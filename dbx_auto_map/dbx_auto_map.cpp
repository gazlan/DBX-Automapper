/* ******************************************************************** **
** @@ DBX Auto mapper
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Note   :
** ******************************************************************** */

/* ******************************************************************** **
**                uses pre-compiled headers
** ******************************************************************** */

#include "stdafx.h"

#include <stdio.h>
#include <limits.h>
#include <time.h>

#include "..\shared\xlat_tables.h"
#include "..\shared\xlat.h"
#include "..\shared\text.h"
#include "..\shared\file.h"
#include "..\shared\file_walker.h"
#include "..\shared\mmf.h"
#include "..\shared\timestamp.h"
#include "..\shared\vector.h"
#include "..\shared\vector_sorted.h"
#include "..\shared\db_dbx.h"
#include "..\shared\hash_murmur3.h"
#include "..\shared\map_bppt_jannink.h"

#ifdef NDEBUG
#pragma optimize("gsy",on)
#pragma comment(linker,"/FILEALIGN:512 /MERGE:.rdata=.text /MERGE:.data=.text /SECTION:.text,EWR /IGNORE:4078")
#endif

#ifdef _DEBUG
#define new DEBUG_NEW
#undef THIS_FILE
static char THIS_FILE[] = __FILE__;
#endif

/* ******************************************************************** **
** @@                   internal defines
** ******************************************************************** */

#ifndef QWORD
typedef unsigned __int64   QWORD;
#endif

#define MAX_RECORD_SIZE                         (128)
#define MAPPER_MARKER                           "***"

static CString    _sFileIndex07        = _T("");
static CString    _sFileIndex10        = _T("");

static CString    _sTable07_RU         = _T("");
static CString    _sTable07_RU_DBF     = _T("");
static CString    _sTable07_RU_DBV     = _T("");

static CString    _sTable10_RU         = _T("");
static CString    _sTable10_RU_DBF     = _T("");
static CString    _sTable10_RU_DBV     = _T("");

static CString    _sTable10_RU_NEW     = _T("");
static CString    _sTable10_RU_NEW_DBF = _T("");
static CString    _sTable10_RU_NEW_DBV = _T("");

static CString    _sMapper10_RU        = _T("");
static CString    _sMapper10_RU_DBF    = _T("");

enum DBV_FLAGS
{
   DBV_FLAG_NONE       = 0,
   DBV_FLAG_TRANLATED  = 0x01,
   DBV_FLAG_VERIFIED   = 0x02,
   DBV_FLAG_MARKED     = 0x04,
   DBV_FLAG_COMMENTED  = 0x08,
   DBV_FLAG_CHANGED    = 0x10,
   DBV_FLAG_DUPLICATED = 0x20
};
 
struct DBV_RECORD
{
   DWORD       _dwIndexFrom;
   DWORD       _dwIndexTo;
   DWORD       _dwText;
   char*       _pszText;
   DWORD       _dwTextSize;
   char*       _pszComment;
   DWORD       _dwCommentSize;
   DWORD*      _pArray;
   DWORD       _dwArraySize;
};

#pragma pack(push,1)
struct DBF_MAPPER_RECORD
{
   BYTE        _byErased;
   DWORD       _dwIndexTo;
   DWORD       _dwIndexFrom;
   DWORD       _dwRecNum;
};
#pragma pack(pop)

/* ******************************************************************** **
** @@                   internal prototypes
** ******************************************************************** */

/* ******************************************************************** **
** @@                   external global variables
** ******************************************************************** */

extern DWORD   dwKeepError = 0;

/* ******************************************************************** **
** @@                   static global variables
** ******************************************************************** */

static DWORD         _dwSizeOrg = 0;
static DWORD         _pHashOrg[4];

static DWORD         _dwGranulation = 3; // 2 Power: 0, 2, 3, 4

static char          _pRecord[MAX_RECORD_SIZE];

static DBX_TABLE_INFO      _InfoSrc;
static DBX_TABLE_INFO      _InfoDst;
static DBX_TABLE_INFO      _InfoDst2;
static DBX_TABLE_INFO      _InfoDst3;

static BPPTreeIndex        _Index;
static BPPTreeIndex        _Index2;

static SortedVector*       _pVect07 = NULL;  
static SortedVector*       _pVect10 = NULL;  

#define VECTOR_INITIAL_SIZE      (8192) 
#define VECTOR_DELTA             (1024) 

static BYTE          _pDummy[MAX_PATH];

static FILE*         _pLog = NULL;

/* ******************************************************************** **
** @@                   real code
** ******************************************************************** */

/* ******************************************************************** **
** @@ IsRussian()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

inline bool IsRussian(const BYTE* const pBuf,DWORD dwSize)
{
   for (DWORD ii = 0; ii < dwSize; ++ii)
   {
      if (pBuf[ii] > 0x7F)
      {
         return true;
      }
   }

   return false;
}


/* ******************************************************************** **
** @@ CMP_Hash()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  : Hash128 compare function
** ******************************************************************** */

inline int CMP_Hash(const void* const pKey1,const void* const pKey2)
{
   DWORD*  p1 = (DWORD*)pKey1;
   DWORD*  p2 = (DWORD*)pKey2;

   if (p1[0] > p2[0])
   {
      return 1;
   }
   else if (p1[0] < p2[0])
   {
      return -1;
   }
   else
   {
      if (p1[1] > p2[1])
      {
         return 1;
      }
      else if (p1[1] < p2[1])
      {
         return -1;
      }
      else
      {
         if (p1[2] > p2[2])
         {
            return 1;
         }
         else if (p1[2] < p2[2])
         {
            return -1;
         }
         else
         {
            if (p1[3] > p2[3])
            {
               return 1;
            }
            else if (p1[3] < p2[3])
            {
               return -1;
            }
            else
            {
               return 0;
            }
         }
      }
   }
}

/* ******************************************************************** **
** @@ CMP_Index()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

inline int CMP_Index(const void** const pKey1,const void** const pKey2)
{
   DBV_RECORD*    p1 = *(DBV_RECORD**)pKey1;
   DBV_RECORD*    p2 = *(DBV_RECORD**)pKey2;

   if (p1->_dwIndexFrom > p2->_dwIndexFrom)
   {
      return 1;
   }
   else if (p1->_dwIndexFrom < p2->_dwIndexFrom)
   {
      return -1;
   }
   else
   {
      return 0;
   }
}

/* ******************************************************************** **
** @@ CMP_Mapper()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

int __cdecl CMP_Mapper(const void* pKey1,const void* pKey2)
{
   DBF_MAPPER_RECORD*   p1 = (DBF_MAPPER_RECORD*)pKey1;
   DBF_MAPPER_RECORD*   p2 = (DBF_MAPPER_RECORD*)pKey2;

   if (p1->_dwIndexTo > p2->_dwIndexTo)
   {
      return 1;
   }
   else if (p1->_dwIndexTo < p2->_dwIndexTo)
   {
      return -1;
   }
   else
   {
      return 0;
   }
}

/* ******************************************************************** **
** @@ Load()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Load()
{
   DBX*     pDBX = new DBX;

   DBX_TABLE*     pSrc = pDBX->OpenTable
   (
      (LPCTSTR)_sTable07_RU,
      (LPCTSTR)_sTable07_RU_DBF,
      (LPCTSTR)_sTable07_RU_DBV,
      DBX_OM_READ_ONLY,
      DBX_OM_READ_ONLY,
      DBX_FM_FLUSH_NEVER,
      DBX_FM_FLUSH_NEVER
   );
   
   if (!pSrc)
   {
      // Error !
      ASSERT(0);
      return;
   }

   DWORD ii = 0;

   DWORD    dwRecCnt07 = pSrc->GetRecCnt();

   ASSERT(dwRecCnt07);

   MMF      _mmf07;

   _mmf07.OpenReadOnly((LPCTSTR)_sTable07_RU_DBV);

   BYTE*    pBuf07 = _mmf07.Buffer();

   ASSERT(pBuf07);

   _pVect07 = new SortedVector;

   _pVect07->Resize(VECTOR_INITIAL_SIZE);  
   _pVect07->Delta(VECTOR_DELTA);  
   _pVect07->SetSorter(CMP_Index);  

   for (ii = 1; ii <= dwRecCnt07; ++ii)
   {
      DBV_RECORD*    p07 = new DBV_RECORD;

      memset(p07,0,sizeof(DBV_RECORD));

      const BYTE* const    pRecord = pSrc->Go(ii);

      ASSERT(pRecord);

      DBX_COLUMN*    pIndex = pSrc->GetColumn("INDEX");
      DBX_COLUMN*    pText  = pSrc->GetColumn("TEXT");

      ASSERT(pIndex);
      ASSERT(pText);

      DWORD    dwIndex = *(DWORD*)pIndex->Get(pRecord);
      DWORD    dwText  = *(DWORD*)pText-> Get(pRecord);

      ASSERT(dwText);
      ASSERT(!(dwText & 0x07));

      p07->_dwIndexFrom = dwIndex;
      p07->_dwText      = dwText;
      p07->_dwTextSize  = *(DWORD*)(pBuf07 + p07->_dwText);

      p07->_pszText = new char[p07->_dwTextSize];

      memcpy(p07->_pszText,pBuf07 + p07->_dwText + sizeof(DWORD),p07->_dwTextSize);

      if (_pVect07->Insert(p07) == -1)
      {
         // Error !
         ASSERT(0);
         delete p07;
         p07 = NULL;
      }
   }

   pDBX->CloseTable(pSrc);

   DBX_TABLE*     pDst = pDBX->OpenTable
   (
      (LPCTSTR)_sTable10_RU,
      (LPCTSTR)_sTable10_RU_DBF,
      (LPCTSTR)_sTable10_RU_DBV,
      DBX_OM_READ_ONLY,
      DBX_OM_READ_ONLY,
      DBX_FM_FLUSH_NEVER,
      DBX_FM_FLUSH_NEVER
   );
   
   if (!pDst)
   {
      // Error !
      ASSERT(0);
      pDBX->CloseTable(pDst);
      return;
   }

   DWORD    dwRecCnt10 = pDst->GetRecCnt();

   ASSERT(dwRecCnt10);

   MMF      _mmf10;

   _mmf10.OpenReadOnly((LPCTSTR)_sTable10_RU_DBV);

   BYTE*    pBuf10 = _mmf10.Buffer();

   ASSERT(pBuf10);

   _pVect10 = new SortedVector;

   _pVect10->Resize(VECTOR_INITIAL_SIZE);  
   _pVect10->Delta(VECTOR_DELTA);  
   _pVect10->SetSorter(CMP_Index);  

   for (ii = 1; ii <= dwRecCnt10; ++ii)
   {
      DBV_RECORD*    p10 = new DBV_RECORD;

      memset(p10,0,sizeof(DBV_RECORD));

      const BYTE* const    pRecord = pDst->Go(ii);

      ASSERT(pRecord);

      DBX_COLUMN*    pIndex = pDst->GetColumn("INDEX FROM");
      DBX_COLUMN*    pText  = pDst->GetColumn("TEXT");

      ASSERT(pIndex);
      ASSERT(pText);

      DWORD    dwIndex = *(DWORD*)pIndex->Get(pRecord);
      DWORD    dwText  = *(DWORD*)pText-> Get(pRecord);

      ASSERT(dwText);
      ASSERT(!(dwText & 0x07));

      p10->_dwIndexFrom = dwIndex;
      p10->_dwText      = dwText;
      p10->_dwTextSize  = *(DWORD*)(pBuf10 + p10->_dwText);

      p10->_pszText = new char[p10->_dwTextSize];

      memcpy(p10->_pszText,pBuf10 + p10->_dwText + sizeof(DWORD),p10->_dwTextSize);

      if (_pVect10->Insert(p10) == -1)
      {
         // Error !
         ASSERT(0);
         delete p10;
         p10 = NULL;
      }
   }

   pDBX->CloseTable(pDst);

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ Cleanup()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Cleanup()
{
   int ii = 0;

   int   iCnt07 = _pVect07->Count();

   // Should be int !
   for (ii = (iCnt07 - 1); ii >= 0; --ii)
   {
      DBV_RECORD*    p07 = (DBV_RECORD*)_pVect07->At(ii);

      if (p07)
      {
         if (p07->_pszText)
         {
            delete[] p07->_pszText;
            p07->_pszText = NULL; 
         }

         delete p07;
         p07 = NULL;
      }
   }

   int   iCnt10 = _pVect10->Count();

   // Should be int !
   for (ii = (iCnt10 - 1); ii >= 0; --ii)
   {
      DBV_RECORD*    p10 = (DBV_RECORD*)_pVect10->At(ii);

      if (p10)
      {
         if (p10->_pszText)
         {
            delete[] p10->_pszText;
            p10->_pszText = NULL; 
         }

         if (p10->_pszComment)
         {
            delete[] p10->_pszComment;
            p10->_pszComment = NULL;
         }

         if (p10->_pArray)
         {
            delete[] p10->_pArray;
            p10->_pArray = NULL;
         }

         delete p10;
         p10 = NULL;
      }
   }

   if (_pVect07)
   {
      delete _pVect07;
      _pVect07 = NULL;
   }

   if (_pVect10)
   {
      delete _pVect10;
      _pVect10 = NULL;
   }
}

/* ******************************************************************** **
** @@ AppendFix2()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void AppendFix2
(
   DBX_TABLE*        pTable,
   DWORD             dwIndex,
   DWORD             dwTextPos,
   DWORD             dwCmntPos,
   DWORD             dwArrayPos
)
{
   BYTE     _Record[MAX_PATH];

   memset(&_Record,0x20,MAX_PATH);

   DBX_COLUMN*    pIndexFrom = pTable->GetColumn("INDEX FROM");
   DBX_COLUMN*    pIndexTo   = pTable->GetColumn("INDEX TO");
   DBX_COLUMN*    pText      = pTable->GetColumn("TEXT");
   DBX_COLUMN*    pCmnt      = pTable->GetColumn("COMMENT");
   DBX_COLUMN*    pArray     = pTable->GetColumn("ARRAY");
   DBX_COLUMN*    pFlags     = pTable->GetColumn("FLAGS");

   ASSERT(pIndexFrom);
   ASSERT(pIndexTo);
   ASSERT(pText);
   ASSERT(pCmnt);
   ASSERT(pArray);
   ASSERT(pFlags);

   DWORD    dwFlags = dwCmntPos  ?  DBV_FLAG_COMMENTED  :  DBV_FLAG_NONE;

   dwFlags |= dwArrayPos  ?  DBV_FLAG_DUPLICATED  :  DBV_FLAG_NONE;

   pIndexFrom->Set(&_Record,&dwIndex);
   pIndexTo->  Set(&_Record,&dwIndex);
   pText->     Set(&_Record,&dwTextPos);
   pCmnt->     Set(&_Record,&dwCmntPos);
   pArray->    Set(&_Record,&dwArrayPos);
   pFlags->    Set(&_Record,&dwFlags);

   pTable->InsertRecord((BYTE*)&_Record);
}

/* ******************************************************************** **
** @@ AppendFix3()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void AppendFix3
(
   DBX_TABLE*        pTable,
   DWORD             dwRecNum,
   DWORD             dwIndex
)
{
   BYTE     _Record[MAX_PATH];

   memset(&_Record,0x20,MAX_PATH);

   DBX_COLUMN*    pIndexTo   = pTable->GetColumn("INDEX TO");
   DBX_COLUMN*    pIndexFrom = pTable->GetColumn("INDEX FROM");
   DBX_COLUMN*    pRecNum    = pTable->GetColumn("RECORD NUM");

   ASSERT(pIndexTo);
   ASSERT(pIndexFrom);
   ASSERT(pRecNum);

   pIndexTo->  Set(&_Record,&dwIndex);
   pIndexFrom->Set(&_Record,&dwIndex);
   pRecNum->   Set(&_Record,&dwRecNum);

   pTable->InsertRecord((BYTE*)&_Record);
}

/* ******************************************************************** **
** @@ AppendVar2()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static DWORD AppendVar2
(
   DBX_TABLE*           pTable,
   const BYTE* const    pData,
   DWORD                dwSize
)
{
   if (!pData || !dwSize)
   {
      // Nothing to do !
      return 0;
   }

   ASSERT(pTable->_hVarFile != INVALID_HANDLE_VALUE);

   DWORD    dwFileSize = GetFileSize(pTable->_hVarFile,NULL);

   DWORD    dwBound = 0;

   if (_dwGranulation)
   {
      dwBound = ((dwFileSize + ((1 << _dwGranulation) - 1)) >> _dwGranulation) << _dwGranulation;
   }
   else
   {
      dwBound = dwFileSize;
   }

   DWORD    dwDelta = dwBound - dwFileSize;

   ASSERT(dwDelta < (WORD)(1 << _dwGranulation));

   if (dwDelta)
   {
      WriteBuffer(pTable->_hVarFile,_pDummy,dwDelta);
   }

   WriteBuffer(pTable->_hVarFile,&dwSize,sizeof(DWORD));
   WriteBuffer(pTable->_hVarFile,(void*)pData,dwSize);

   return dwBound;
}

/* ******************************************************************** **
** @@ Append2()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Append2
(
   BYTE*                pText,
   DWORD                dwTextSize,
   DBX_TABLE*           pTable,
   DWORD                dwIndex,
   BYTE*                pComment,
   DWORD                dwCommentSize,
   BYTE*                pArray,
   DWORD                dwArraySize
)
{
   ASSERT(pText);
   ASSERT(dwTextSize);
   ASSERT(pTable);
//   ASSERT(dwIndex);

   DWORD    dwTextPos  = AppendVar2(pTable,pText,   dwTextSize);
   DWORD    dwCmntPos  = AppendVar2(pTable,pComment,dwCommentSize);
   DWORD    dwArrayPos = AppendVar2(pTable,pArray,  dwArraySize);

   AppendFix2(pTable,dwIndex,dwTextPos,dwCmntPos,dwArrayPos);
}

/* ******************************************************************** **
** @@ Append3()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Append3
(
   DBX_TABLE*     pTable,
   DWORD          dwRecNum,
   DWORD          dwIndex
)
{
   ASSERT(pTable);
   ASSERT(dwRecNum);

   AppendFix3(pTable,dwRecNum,dwIndex);
}

/* ******************************************************************** **
** @@ Updater()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Updater()
{
   DBX*     pDBX = new DBX;

   DBX_TABLE*     pDst2 = pDBX->OpenTable
   (
      (LPCTSTR)_sTable10_RU_NEW,
      (LPCTSTR)_sTable10_RU_NEW_DBF,
      (LPCTSTR)_sTable10_RU_NEW_DBV,
      DBX_OM_READ_WRITE,
      DBX_OM_READ_WRITE,
      DBX_FM_FLUSH_ON_CLOSE,
      DBX_FM_FLUSH_ON_CLOSE
   );
   
   if (!pDst2)
   {
      // Error !
      ASSERT(0);
      return;
   }

   DBX_TABLE*     pDst3 = pDBX->OpenTable
   (
      (LPCTSTR)_sMapper10_RU,
      (LPCTSTR)_sMapper10_RU_DBF,
      NULL,
      DBX_OM_READ_WRITE,
      DBX_OM_NONE,
      DBX_FM_FLUSH_ON_CLOSE,
      DBX_FM_FLUSH_NEVER
   );
   
   if (!pDst3)
   {
      // Error !
      ASSERT(0);
      return;
   }

   DWORD    dwRecCnt = _pVect10->Count();

   ASSERT(dwRecCnt);

   for (DWORD ii = 0; ii < dwRecCnt; ++ii)
   {
      DBV_RECORD*       pRec = (DBV_RECORD*)_pVect10->At(ii);

      ASSERT(pRec);

      if (pRec)
      {
         char*    pText         = pRec->_pszText;
         DWORD    dwTextSize    = pRec->_dwTextSize;
         DWORD    dwIndex       = pRec->_dwIndexFrom;
         char*    pComment      = pRec->_pszComment;
         DWORD    dwCommentSize = pRec->_dwCommentSize;
         DWORD*   pArray        = pRec->_pArray;
         DWORD    dwArraySize   = pRec->_dwArraySize;

         Append2((BYTE*)pText,dwTextSize,pDst2,dwIndex,(BYTE*)pComment,dwCommentSize,(BYTE*)pArray,dwArraySize);
         Append3(pDst3,ii + 1,dwIndex);
      }
   }

   pDBX->CloseTable(pDst2);

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ AppendArray()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void AppendArray(DBV_RECORD* pRec10,const DWORD* const pArr,DWORD dwCnt)
{
   if (!pRec10 || !pArr || !dwCnt)
   {
      // Error !
      ASSERT(0);
      return;
   }

   if (pRec10->_pArray)
   {
      delete[] pRec10->_pArray;
      pRec10->_pArray = NULL;
   }

   pRec10->_pArray = new DWORD[dwCnt];

   memcpy(pRec10->_pArray,pArr,sizeof(DWORD) * dwCnt);

   pRec10->_dwArraySize = sizeof(DWORD) * dwCnt;
} 

/* ******************************************************************** **
** @@ Mapper()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Mapper
(
   const char* const    pszEnName,
   const char* const    pszRuName
)
{
   ASSERT(pszEnName);
   ASSERT(pszRuName);
   
   char     pszIdxName [_MAX_PATH];
   char     pszIdx2Name[_MAX_PATH];
   char     pszDrive   [_MAX_DRIVE];
   char     pszDir     [_MAX_DIR];
   char     pszFName   [_MAX_FNAME];
   char     pszExt     [_MAX_EXT];

   _splitpath(pszEnName,  pszDrive,pszDir,pszFName,pszExt);
   _makepath( pszIdxName, pszDrive,pszDir,pszFName,"dbi");
   _makepath( pszIdx2Name,pszDrive,pszDir,pszFName,"dbi2");

   BPPT_INDEX_INFO      Info;

   memset(&Info,0,sizeof(Info));

   strcpy(Info._pszIndexName,(LPCTSTR)_sFileIndex07);

   Info._pCompare = CMP_Hash;

   Info._bDuplicate   = false;
   Info._bInitialized = true;  
                                    
   Info._iKeySize    = 16;          // 128 bits Murmur Hash 
   Info._iSectorSize = (1 << 16);   // 64 K

   BPPT_INDEX_INFO       Info2;

   memset(&Info2,0,sizeof(Info2));

   strcpy(Info2._pszIndexName,(LPCTSTR)_sFileIndex10);

   Info2._pCompare = CMP_Hash;

   Info2._bDuplicate   = true;
   Info2._bInitialized = true;  
                                    
   Info2._iKeySize    = 16;          // 128 bits Murmur Hash 
   Info2._iSectorSize = (1 << 16);   // 64 K

   if (!_Index.Open(Info))
   {
      // Error !
      ASSERT(0);
      _Index.Close();
      return;
   }

   if (!_Index2.Open(Info2))
   {
      // Error !
      ASSERT(0);
      _Index.Close();
      return;
   }

   DWORD    pKey07[4];
   DWORD    dwValue07 = 0; 

   DWORD    pKey10[4];
   DWORD    dwValue10 = 0; 

   memset(pKey07,0,sizeof(DWORD) * 4);
   memset(pKey10,0,sizeof(DWORD) * 4);

   const DWORD    MAX_DUP_CNT = 1024; // !!

   DWORD    pArr[MAX_DUP_CNT];

   DWORD    dwDupCnt    = 0;
   DWORD    dwMaxDupCnt = 0;

   fprintf(_pLog,"##### [START] ###########################################################################\n");
   
   if (!_Index.FindFirst((char*)pKey07,&dwValue07))
   {
      // Error !
      ASSERT(0);
   }
   else
   {
      // Reset Array
      dwDupCnt    = 0;
      dwMaxDupCnt = 0;

      DBV_RECORD*    pCurrent = NULL;

      memset(pArr,0,sizeof(DWORD) * MAX_DUP_CNT);

      DBV_RECORD     _Test07;

      memset(&_Test07,0,sizeof(DBV_RECORD));

      _Test07._dwIndexFrom = dwValue07;

      DBV_RECORD*    pTest07 = (DBV_RECORD*)_pVect07->Search(&_Test07);

      fprintf(_pLog,"--------------------------------------------------------------------------------\n");
      fprintf(_pLog,"Found First:  %08X\n",dwValue07);
      fprintf(_pLog,"--------------------------------------------------------------------------------\n");

      if (pTest07 && IsRussian((BYTE*)pTest07->_pszText,pTest07->_dwTextSize))
      {
         // Found First
//         printf("%08X:  ",dwValue07);
         if (_Index2.Find((char*)pKey07,&dwValue10))
         {
//            printf("%08X:  ",dwValue10);
            fprintf(_pLog,"*** First: %08X\n",dwValue10);

            // Update First
            DBV_RECORD     _Pattern07;
            DBV_RECORD     _Pattern10;

            memset(&_Pattern07,0,sizeof(DBV_RECORD));
            memset(&_Pattern10,0,sizeof(DBV_RECORD));

            _Pattern07._dwIndexFrom = dwValue07;
            _Pattern10._dwIndexFrom = dwValue10;

            DBV_RECORD*    pRec07 = (DBV_RECORD*)_pVect07->Search(&_Pattern07);
            DBV_RECORD*    pRec10 = (DBV_RECORD*)_pVect10->Search(&_Pattern10);

            pCurrent = pRec10;

            if (pRec07 && pRec10)
            {
               if (pRec10->_pszText)         
               {
                  fprintf(_pLog,"[ORIGINAL]\n%s\n",pRec10->_pszText);

                  delete[] pRec10->_pszText;
                  pRec10->_pszText = NULL;
               }

               pRec10->_dwTextSize = pRec07->_dwTextSize;
               pRec10->_pszText    = new char[pRec07->_dwTextSize];

               memcpy(pRec10->_pszText,pRec07->_pszText,pRec10->_dwTextSize);

               fprintf(_pLog,"[NEW]\n%s\n",pRec10->_pszText);
               fprintf(_pLog,"--------------------------------------------------------------------------------\n");

               pRec10->_dwCommentSize = sizeof(MAPPER_MARKER);
               pRec10->_pszComment    = new char[pRec10->_dwCommentSize];

               memcpy(pRec10->_pszComment,MAPPER_MARKER,pRec10->_dwCommentSize);

               pArr[dwDupCnt++] = dwValue10;

               dwMaxDupCnt = max(dwMaxDupCnt,dwDupCnt);
            }

            do 
            {
               if (_Index2.FindNext((char*)pKey10,&dwValue10))
               {
                  if (!memcmp(pKey07,pKey10,sizeof(DWORD) * 4))
                  {
                     // Found Next in the Dup Set
//                     printf("%08X  ",dwValue10);
                     fprintf(_pLog,"*** First -> Next: %s\n",pRec10->_pszText);

                     // Update Next
                     DBV_RECORD     _Pattern10;

                     memset(&_Pattern10,0,sizeof(DBV_RECORD));

                     _Pattern10._dwIndexFrom = dwValue10;

                     DBV_RECORD*    pRec10 = (DBV_RECORD*)_pVect10->Search(&_Pattern10);

                     pCurrent = pRec10;

                     if (pRec07 && pRec10)
                     {
                        if (pRec10->_pszText)         
                        {
                           fprintf(_pLog,"[ORIGINAL]\n%s\n",pRec10->_pszText);

                           delete[] pRec10->_pszText;
                           pRec10->_pszText = NULL;
                        }

                        pRec10->_dwTextSize = pRec07->_dwTextSize;
                        pRec10->_pszText    = new char[pRec07->_dwTextSize];

                        memcpy(pRec10->_pszText,pRec07->_pszText,pRec10->_dwTextSize);

                        fprintf(_pLog,"[NEW]\n%s\n",pRec10->_pszText);
                        fprintf(_pLog,"--------------------------------------------------------------------------------\n");

                        pRec10->_dwCommentSize = sizeof(MAPPER_MARKER);
                        pRec10->_pszComment    = new char[pRec10->_dwCommentSize];

                        memcpy(pRec10->_pszComment,MAPPER_MARKER,pRec10->_dwCommentSize);

                        pArr[dwDupCnt++] = dwValue10;

                        dwMaxDupCnt = max(dwMaxDupCnt,dwDupCnt);
                     }
                  }
               }
            }
            while (!memcmp(pKey07,pKey10,sizeof(DWORD) * 4));
         }
      }  

      fprintf(_pLog,"--------------------------------------------------------------------------------\n");

      if (dwDupCnt > 1)
      {
         fprintf(_pLog,"** Array First [IndexFrom: %08X]  ",pCurrent->_dwIndexFrom);

         for (DWORD kk = 0; kk < dwDupCnt; ++kk)
         {
               fprintf(_pLog,"%08X  ",pArr[kk]);
         }

         fprintf(_pLog,"\n** Max Dups [IndexFrom: %08X] %08X\n",pCurrent->_dwIndexFrom,dwMaxDupCnt);
         fprintf(_pLog,"--------------------------------------------------------------------------------\n");
      }

      if (dwMaxDupCnt > 1)
      {
         AppendArray(pCurrent,pArr,dwDupCnt); 
      }
   }

   do 
   {
      if (!_Index.FindNext((char*)pKey07,&dwValue07))
      {
         // Finished
         break;
      }
      else
      {
         // Reset Array
         dwDupCnt    = 0;
         dwMaxDupCnt = 0;

         DBV_RECORD*    pCurrent = NULL;

         memset(pArr,0,sizeof(DWORD) * MAX_DUP_CNT);

         DBV_RECORD     _Test07;

         memset(&_Test07,0,sizeof(DBV_RECORD));

         _Test07._dwIndexFrom = dwValue07;

         DBV_RECORD*    pTest07 = (DBV_RECORD*)_pVect07->Search(&_Test07);

         fprintf(_pLog,"--------------------------------------------------------------------------------\n");
         fprintf(_pLog,"Found Next:  %08X\n",dwValue07);
         fprintf(_pLog,"--------------------------------------------------------------------------------\n");

         if (pTest07 && IsRussian((BYTE*)pTest07->_pszText,pTest07->_dwTextSize))
         {
            // Found Next
//            printf("%08X:  ",dwValue07);
            if (_Index2.Find((char*)pKey07,&dwValue10))
            {
               // Found First
//                printf("%08X:  ",dwValue10);
               fprintf(_pLog,"*** Next -> First: %08X\n",dwValue10);
               
               // Update First
               DBV_RECORD     _Pattern07;
               DBV_RECORD     _Pattern10;

               memset(&_Pattern07,0,sizeof(DBV_RECORD));
               memset(&_Pattern10,0,sizeof(DBV_RECORD));

               _Pattern07._dwIndexFrom = dwValue07;
               _Pattern10._dwIndexFrom = dwValue10;

               DBV_RECORD*    pRec07 = (DBV_RECORD*)_pVect07->Search(&_Pattern07);
               DBV_RECORD*    pRec10 = (DBV_RECORD*)_pVect10->Search(&_Pattern10);

               pCurrent = pRec10;

               if (pRec07 && pRec10)
               {
                  if (pRec10->_pszText)         
                  {
                     fprintf(_pLog,"[ORIGINAL]\n%s\n",pRec10->_pszText);

                     delete[] pRec10->_pszText;
                     pRec10->_pszText = NULL;
                  }

                  if (pRec10->_pszComment)         
                  {
                     delete[] pRec10->_pszComment;
                     pRec10->_pszComment = NULL;
                  }

                  pRec10->_dwTextSize = pRec07->_dwTextSize;
                  pRec10->_pszText    = new char[pRec07->_dwTextSize];

                  memcpy(pRec10->_pszText,pRec07->_pszText,pRec10->_dwTextSize);

                  fprintf(_pLog,"[NEW]\n%s\n",pRec10->_pszText);
                  fprintf(_pLog,"--------------------------------------------------------------------------------\n");

                  pRec10->_dwCommentSize = sizeof(MAPPER_MARKER);
                  pRec10->_pszComment    = new char[pRec10->_dwCommentSize];

                  memcpy(pRec10->_pszComment,MAPPER_MARKER,pRec10->_dwCommentSize);

                  pArr[dwDupCnt++] = dwValue10;

                  dwMaxDupCnt = max(dwMaxDupCnt,dwDupCnt);
               }

               do 
               {
                  if (_Index2.FindNext((char*)pKey10,&dwValue10))
                  {
                     if (!memcmp(pKey07,pKey10,sizeof(DWORD) * 4))
                     {
                        // Found Next in the Dup Set
//                      printf("%08X  ",dwValue10);
                        fprintf(_pLog,"*** Next -> Next: %08X\n",dwValue10);

                        // Update Next
                        DBV_RECORD     _Pattern10;

                        memset(&_Pattern10,0,sizeof(DBV_RECORD));

                        _Pattern10._dwIndexFrom = dwValue10;

                        DBV_RECORD*    pRec10 = (DBV_RECORD*)_pVect10->Search(&_Pattern10);

                        pCurrent = pRec10;

                        if (pRec07 && pRec10)
                        {
                           if (pRec10->_pszText)         
                           {
                              fprintf(_pLog,"[ORIGINAL]\n%s\n",pRec10->_pszText);

                              delete[] pRec10->_pszText;
                              pRec10->_pszText = NULL;
                           }

                           if (pRec10->_pszComment)         
                           {
                              delete[] pRec10->_pszComment;
                              pRec10->_pszComment = NULL;
                           }

                           pRec10->_dwTextSize = pRec07->_dwTextSize;
                           pRec10->_pszText    = new char[pRec07->_dwTextSize];

                           memcpy(pRec10->_pszText,pRec07->_pszText,pRec10->_dwTextSize);

                           fprintf(_pLog,"[NEW]\n%s\n",pRec10->_pszText);
                           fprintf(_pLog,"--------------------------------------------------------------------------------\n");

                           pRec10->_dwCommentSize = sizeof(MAPPER_MARKER);
                           pRec10->_pszComment    = new char[pRec10->_dwCommentSize];

                           memcpy(pRec10->_pszComment,MAPPER_MARKER,pRec10->_dwCommentSize);

                           pArr[dwDupCnt++] = dwValue10;

                           dwMaxDupCnt = max(dwMaxDupCnt,dwDupCnt);
                        }
                     }
                  }
               }
               while (!memcmp(pKey07,pKey10,sizeof(DWORD) * 4));
            }

            fprintf(_pLog,"##### [END] ###########################################################################\n");
         }

         fprintf(_pLog,"--------------------------------------------------------------------------------\n");

         if (dwDupCnt > 1)
         {
            fprintf(_pLog,"** Array Next [IndexFrom: %08X]  ",pCurrent->_dwIndexFrom);

            for (DWORD kk = 0; kk < dwDupCnt; ++kk)
            {
                  fprintf(_pLog,"%08X  ",pArr[kk]);
            }
            
            fprintf(_pLog,"\n** Max Dups [IndexFrom: %08X]  %08X\n",pCurrent->_dwIndexFrom,dwMaxDupCnt);
            fprintf(_pLog,"--------------------------------------------------------------------------------\n");
         }

         if (dwMaxDupCnt > 1)
         {
            AppendArray(pCurrent,pArr,dwDupCnt); 
         }
      }
   } 
   while (true);

   _Index.Close();
   _Index2.Close();
}

/* ******************************************************************** **
** @@ Creator2()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Creator2(const DBX_TABLE_INFO& rInfo)
{
   DBX*     pDBX = new DBX;

   if (!pDBX->CreateEmptyTable(&rInfo))
   {
      // Error !
      ASSERT(0);
      return;
   }

   if (!pDBX->CreateEmptyMemo((LPCTSTR)_sTable10_RU_NEW_DBV,_dwGranulation))
   {
      // Error !
      ASSERT(0);
      return;
   }

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ Creator3()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Creator3(const DBX_TABLE_INFO& rInfo)
{
   DBX*     pDBX = new DBX;

   if (!pDBX->CreateEmptyTable(&rInfo))
   {
      // Error !
      ASSERT(0);
      return;
   }

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ Sorter()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Sorter()
{
   DBX*     pDBX = new DBX;

   DBX_TABLE*     pMapper = pDBX->OpenTable
   (
      (LPCTSTR)_sMapper10_RU,
      (LPCTSTR)_sMapper10_RU_DBF,
      NULL,
      DBX_OM_READ_ONLY,
      DBX_OM_NONE,
      DBX_FM_FLUSH_NEVER,
      DBX_FM_FLUSH_NEVER
   );
   
   if (!pMapper)
   {
      // Error !
      ASSERT(0);
      return;
   }

   BYTE*    pStart = pMapper->_pMemBufFix + pMapper->_FixHeader._wDataStart;
   int      iCnt   = pMapper->_FixHeader._dwRecCnt;
   int      iWidth = pMapper->_FixHeader._wRecSize;

   delete pDBX;
   pDBX = NULL;

   MMF*     pMF = new MMF;

   pMF->OpenReadWrite((LPCTSTR)_sMapper10_RU_DBF);

   qsort(pStart,iCnt,iWidth,CMP_Mapper);

   pMF->Close();

   delete pMF;
   pMF = NULL;
}

/* ******************************************************************** **
** @@ ForEach()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void ForEach(const char* const pszFilename)
{
   CString     sFile = pszFilename;

   sFile.MakeUpper();

   if (!sFile.Replace("ENGLISH","Russian"))
   {
      // Error !
      // No Language file
      return;
   }
   
   char     pszEnName [_MAX_PATH];
   char     pszRuName [_MAX_PATH];
   char     pszDBFName[_MAX_PATH];
   char     pszDrive  [_MAX_DRIVE];
   char     pszDir    [_MAX_DIR];
   char     pszFName  [_MAX_FNAME];
   char     pszExt    [_MAX_EXT];

   _splitpath(pszFilename,pszDrive,pszDir,pszFName,pszExt);
   _makepath( pszEnName, pszDrive,pszDir,pszFName,"");

   _splitpath((LPCTSTR)sFile,pszDrive,pszDir,pszFName,pszExt);
   _makepath( pszRuName,     pszDrive,pszDir,pszFName,"");

   switch (*pszFName)
   {
      case 'm':
      case 'M':
      {
         _sFileIndex07        = "M_English_07.dbi";
         _sFileIndex10        = "M_English_10.dbi2";
         _sTable07_RU         = "M_Russian_07";
         _sTable07_RU_DBF     = "M_Russian_07.dbf";
         _sTable07_RU_DBV     = "M_Russian_07.dbv";
         _sTable10_RU         = "M_Russian_10";
         _sTable10_RU_DBF     = "M_Russian_10.dbf";
         _sTable10_RU_DBV     = "M_Russian_10.dbv";
         _sTable10_RU_NEW     = "M_Russian_10_";
         _sTable10_RU_NEW_DBF = "M_Russian_10_.dbf";
         _sTable10_RU_NEW_DBV = "M_Russian_10_.dbv";
         _sMapper10_RU        = "M_Mapper_10";
         _sMapper10_RU_DBF    = "M_Mapper_10.dbf";
         break;
      }
      case 'u':
      case 'U':
      {
         _sFileIndex07        = "U_English_07.dbi";
         _sFileIndex10        = "U_English_10.dbi2";
         _sTable07_RU         = "U_Russian_07";
         _sTable07_RU_DBF     = "U_Russian_07.dbf";
         _sTable07_RU_DBV     = "U_Russian_07.dbv";
         _sTable10_RU         = "U_Russian_10";
         _sTable10_RU_DBF     = "U_Russian_10.dbf";
         _sTable10_RU_DBV     = "U_Russian_10.dbv";
         _sTable10_RU_NEW     = "U_Russian_10_";
         _sTable10_RU_NEW_DBF = "U_Russian_10_.dbf";
         _sTable10_RU_NEW_DBV = "U_Russian_10_.dbv";
         _sMapper10_RU        = "U_Mapper_10";
         _sMapper10_RU_DBF    = "U_Mapper_10.dbf";
         break;
      }
      case 'v':
      case 'V':
      {
         _sFileIndex07        = "V_English_07.dbi";
         _sFileIndex10        = "V_English_10.dbi2";
         _sTable07_RU         = "V_Russian_07";
         _sTable07_RU_DBF     = "V_Russian_07.dbf";
         _sTable07_RU_DBV     = "V_Russian_07.dbv";
         _sTable10_RU         = "V_Russian_10";
         _sTable10_RU_DBF     = "V_Russian_10.dbf";
         _sTable10_RU_DBV     = "V_Russian_10.dbv";
         _sTable10_RU_NEW     = "V_Russian_10_";
         _sTable10_RU_NEW_DBF = "V_Russian_10_.dbf";
         _sTable10_RU_NEW_DBV = "V_Russian_10_.dbv";
         _sMapper10_RU        = "V_Mapper_10";
         _sMapper10_RU_DBF    = "V_Mapper_10.dbf";
         break;
      }
      default:
      {
         // Error !
         ASSERT(0);
         return;
      }
   }

   const int      FIELD_CNT = 5;

   DBX_COLUMN_DESCRIPTOR    pFieldArr[FIELD_CNT];

   memset(pFieldArr,0,sizeof(DBX_COLUMN_DESCRIPTOR) * FIELD_CNT);

   // 1. IDX
   DefineField(pFieldArr, 0,"INDEX",  DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 2. TEXT
   DefineField(pFieldArr, 1,"TEXT",   DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 3. COMMENT
   DefineField(pFieldArr, 2,"COMMENT",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 3. ARRAY
   DefineField(pFieldArr, 3,"ARRAY",  DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 5. FLAGS
   DefineField(pFieldArr, 5,"FLAGS",  DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(BYTE));

   _InfoDst._FileType  = DBX_FT_FOX_BASE_PLUS_NO_MEMO;
   _InfoDst._iCnt      = FIELD_CNT;
   _InfoDst._pFieldArr = pFieldArr;

   _splitpath(pszRuName,pszDrive,pszDir,pszFName,pszExt);
   _makepath( pszDBFName,pszDrive,pszDir,pszFName,"dbf");

   strcpy((char*)&_InfoDst._pszName,(LPCTSTR)_sTable10_RU_DBF);

   Load();

   Mapper(pszEnName,pszRuName);

   const int      FIELD_CNT2 = 6;

   DBX_COLUMN_DESCRIPTOR    pFieldArr2[FIELD_CNT];

   memset(pFieldArr2,0,sizeof(DBX_COLUMN_DESCRIPTOR) * FIELD_CNT2);

   // 1. IDX FROM
   DefineField(pFieldArr2, 0,"INDEX FROM",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 2. IDX TO
   DefineField(pFieldArr2, 1,"INDEX TO",  DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 3. TEXT
   DefineField(pFieldArr2, 2,"TEXT",      DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 4. COMMENT
   DefineField(pFieldArr2, 3,"COMMENT",   DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 5. ARRAY
   DefineField(pFieldArr2, 4,"ARRAY",     DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 6. FLAGS
   DefineField(pFieldArr2, 5,"FLAGS",     DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(BYTE));

   _InfoDst2._FileType  = DBX_FT_FOX_BASE_PLUS_NO_MEMO;
   _InfoDst2._iCnt      = FIELD_CNT2;
   _InfoDst2._pFieldArr = pFieldArr2;

   strcpy((char*)&_InfoDst2._pszName,(LPCTSTR)_sTable10_RU_NEW_DBF);

   Creator2(_InfoDst2);

   const int      FIELD_CNT3 = 3;

   DBX_COLUMN_DESCRIPTOR    pFieldArr3[FIELD_CNT];

   memset(pFieldArr3,0,sizeof(DBX_COLUMN_DESCRIPTOR) * FIELD_CNT3);

   // 1. INDEX TO
   DefineField(pFieldArr3, 0,"INDEX TO",  DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 2. INDEX FROM
   DefineField(pFieldArr3, 1,"INDEX FROM",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 3. RECORD NUM
   DefineField(pFieldArr3, 2,"RECORD NUM",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));

   _InfoDst3._FileType  = DBX_FT_FOX_BASE_PLUS_NO_MEMO;
   _InfoDst3._iCnt      = FIELD_CNT3;
   _InfoDst3._pFieldArr = pFieldArr3;

   strcpy((char*)&_InfoDst3._pszName,(LPCTSTR)_sMapper10_RU_DBF);

   Creator3(_InfoDst3);

   Updater();

   Sorter();

   Cleanup();
}

/* ******************************************************************** **
** @@ ShowHelp()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void ShowHelp()
{
   const char  pszCopyright[] = "-*-   DBX Auto mapper  1.0   *   Copyright (c) Gazlan, 2015   -*-";
   const char  pszDescript [] = "DBX Auto mapper";
   const char  pszE_Mail   [] = "complains_n_suggestions direct to gazlan@yandex.ru";

   printf("%s\n\n",pszCopyright);
   printf("%s\n\n",pszDescript);
   printf("Usage: dbx_auto_map.com wildcards\n\n");
   printf("%s\n",pszE_Mail);
}

/* ******************************************************************** **
** @@ main()
** @ Copyrt:
** @ Author:
** @ Modify:
** @ Update:
** @ Notes :
** ******************************************************************** */

int main(int argc,char** argv)
{
   if (argc != 2)
   {
      ShowHelp();
      return 0;
   }

   if (argc == 2 && ((!strcmp(argv[1],"?")) || (!strcmp(argv[1],"/?")) || (!strcmp(argv[1],"-?")) || (!stricmp(argv[1],"/h")) || (!stricmp(argv[1],"-h"))))
   {
      ShowHelp();
      return 0;
   }

   char     pszMask[MAX_PATH + 1];
   
   memset(pszMask,0,sizeof(pszMask));
   
   strncpy(pszMask,argv[1],MAX_PATH);
   pszMask[MAX_PATH] = 0; // Ensure ASCIIZ
   
   char     pszDrive[_MAX_DRIVE];
   char     pszDir  [_MAX_DIR];
   char     pszFName[_MAX_FNAME];
   char     pszExt  [_MAX_EXT];
   
   _splitpath(pszMask,pszDrive,pszDir,pszFName,pszExt);
   
   char     pszSrchMask[MAX_PATH + 1];
   char     pszSrchPath[MAX_PATH + 1];
   
   strcpy(pszSrchMask,pszFName);
   strcat(pszSrchMask,pszExt);
   
   Walker      Visitor;

   Visitor.Init(ForEach,pszSrchMask,false);

   strcpy(pszSrchPath,pszDrive);
   strcat(pszSrchPath,pszDir);

   _pLog = fopen("00_log.txt","wt");

   if (_pLog)
   {
      Visitor.Run(*pszSrchPath  ?  pszSrchPath  :  ".");

      fclose(_pLog);
      _pLog = NULL;
   }

   return 0;
}

/* ******************************************************************** **
**                That's All
** ******************************************************************** */
