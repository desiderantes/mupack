#include "../stdafx.h"
#include <winnt.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <imagehlp.h>//#include <Dbghelp.h>
#include "pack_x86.h"
#include "patternfind.h"
#include "../logger.h"
#include "Types.h"
#include "fr_pack/frpacker.hpp"
PE pe;
//Internal dll calls
const char *dlls [] = {"kernel32.dll"};
const char *thunks[] = { "VirtualAlloc", "VirtualFree", "VirtualProtect", "GetProcAddress", "GetModuleHandleA", "" };


#define Test86MSByte(b) ((b) == 0 || (b) == 0xFF)
SizeT x86_Convert(Byte *data, SizeT size)
{
	UInt32 state = 0;
	UInt32 ip = 0;
	int encoding = 1;
	const Byte kMaskToAllowedStatus[8] = { 1, 1, 1, 0, 1, 0, 0, 0 };
	const Byte kMaskToBitNumber[8] = { 0, 1, 2, 2, 3, 3, 3, 3 };
	SizeT bufferPos = 0, prevPosT;
	UInt32 prevMask = state & 0x7;
	if (size < 5)
		return 0;
	ip += 5;
	prevPosT = (SizeT)0 - 1;

	for (;;)
	{
		Byte *p = data + bufferPos;
		Byte *limit = data + size - 4;
		for (; p < limit; p++)
			if ((*p & 0xFE) == 0xE8)
				break;
		bufferPos = (SizeT)(p - data);
		if (p >= limit)
			break;
		prevPosT = bufferPos - prevPosT;
		if (prevPosT > 3)
			prevMask = 0;
		else
		{
			prevMask = (prevMask << ((int)prevPosT - 1)) & 0x7;
			if (prevMask != 0)
			{
				Byte b = p[4 - kMaskToBitNumber[prevMask]];
				if (!kMaskToAllowedStatus[prevMask] || Test86MSByte(b))
				{
					prevPosT = bufferPos;
					prevMask = ((prevMask << 1) & 0x7) | 1;
					bufferPos++;
					continue;
				}
			}
		}
		prevPosT = bufferPos;

		if (Test86MSByte(p[4]))
		{
			UInt32 src = ((UInt32)p[4] << 24) | ((UInt32)p[3] << 16) | ((UInt32)p[2] << 8) | ((UInt32)p[1]);
			UInt32 dest;
			for (;;)
			{
				Byte b;
				int index;
				if (encoding)
					dest = (ip + (UInt32)bufferPos) + src;
				else
					dest = src - (ip + (UInt32)bufferPos);
				if (prevMask == 0)
					break;
				index = kMaskToBitNumber[prevMask] * 8;
				b = (Byte)(dest >> (24 - index));
				if (!Test86MSByte(b))
					break;
				src = dest ^ ((1 << (32 - index)) - 1);
			}
			p[4] = (Byte)(~(((dest >> 24) & 1) - 1));
			p[3] = (Byte)(dest >> 16);
			p[2] = (Byte)(dest >> 8);
			p[1] = (Byte)dest;
			bufferPos += 5;
		}
		else
		{
			prevMask = ((prevMask << 1) & 0x7) | 1;
			bufferPos++;
		}
	}
	prevPosT = bufferPos - prevPosT;
	state = ((prevPosT > 3) ? 0 : ((prevMask << ((int)prevPosT - 1)) & 0x7));
	return bufferPos;
}


const int MOD_ADLER = 65521;

DWORD adler32(unsigned char *data, size_t len) /* where data is the location of the data in physical memory and
											   len is the length of the data in bytes */
{
	DWORD a = 1, b = 0;
	size_t index;
	/* Process each byte of the data in order */
	for (index = 0; index < len; ++index)
	{
		a = (a + data[index]) % MOD_ADLER;
		b = (b + a) % MOD_ADLER;
	}
	return (b << 16) | a;
}

int wsstrcpy(char *dest, const char *src)
{
	strcpy(dest,src);
	return strlen(dest);
}

void PrepareNewResourceEntry(PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntry, PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntryOut, DWORD resourceBase, DWORD resourceType, DWORD level);

void PrepareNewResourceDirectory(PIMAGE_RESOURCE_DIRECTORY resDir, DWORD resourceBase, DWORD level, DWORD resourceType)
{
	PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntry, _resDirEntry;
    UINT i;

	DWORD new_resource_section_size = pe.new_resource_section_size;
	new_resource_section_size += sizeof( IMAGE_RESOURCE_DIRECTORY );
	new_resource_section_size += sizeof( IMAGE_RESOURCE_DIRECTORY_ENTRY ) * ( resDir->NumberOfNamedEntries + resDir->NumberOfIdEntries );

	DWORD offset_to_names = new_resource_section_size;

    resDirEntry = (PIMAGE_RESOURCE_DIRECTORY_ENTRY)(resDir+1);
    
	for ( i=0; i < resDir->NumberOfNamedEntries; i++, resDirEntry++ )
	{
		wchar_t * name = ( wchar_t * ) ( resourceBase + ( resDirEntry->Name & 0x7fffffff ) );
		new_resource_section_size += ( *name + 1 ) * sizeof( *name );
		new_resource_section_size = ( new_resource_section_size + 3 ) & ~3;
	}

	// reallocating it causes it to move around, so allocate it only once before entering this
	//pe.new_resource_section = ( unsigned char * ) realloc( pe.new_resource_section, new_resource_section_size );

	PIMAGE_RESOURCE_DIRECTORY _resDir = ( PIMAGE_RESOURCE_DIRECTORY ) ( pe.new_resource_section + pe.new_resource_section_size );
	pe.new_resource_section_size = new_resource_section_size;

	memcpy( _resDir, resDir, sizeof(*resDir) );

    resDirEntry = (PIMAGE_RESOURCE_DIRECTORY_ENTRY)(resDir+1);
    
	_resDirEntry = (PIMAGE_RESOURCE_DIRECTORY_ENTRY)(_resDir+1);

	for ( i=0; i < _resDir->NumberOfNamedEntries; i++, resDirEntry++, _resDirEntry++ )
	{
		wchar_t * name = ( wchar_t * ) ( resourceBase + ( resDirEntry->Name & 0x7fffffff ) );
		wchar_t * name_target = ( wchar_t * ) ( pe.new_resource_section + offset_to_names );
	//	memcpy( name_target, name, ( *name + 1 ) * sizeof( *name ) );
		memcpy(name_target, name, (*name + 1) * 2);
		_resDirEntry->Name = 0x80000000 + offset_to_names;
		//offset_to_names += ( *name + 1 ) * sizeof( *name );
		offset_to_names += (*name + 1) * 2;
		DWORD offset_padded = ( offset_to_names + 3 ) & ~3;
		memset( name_target + *name + 1, 0, offset_padded - offset_to_names );
		offset_to_names = offset_padded;
	}

	for ( i=0; i < _resDir->NumberOfIdEntries; i++, resDirEntry++, _resDirEntry++ )
	{
		_resDirEntry->Name = resDirEntry->Name;
	}

    resDirEntry = (PIMAGE_RESOURCE_DIRECTORY_ENTRY)(resDir+1);
    
	_resDirEntry = (PIMAGE_RESOURCE_DIRECTORY_ENTRY)(_resDir+1);

    for ( i=0; i < resDir->NumberOfNamedEntries; i++, resDirEntry++, _resDirEntry++ )
        PrepareNewResourceEntry(resDirEntry, _resDirEntry, resourceBase, resourceType, level+1);

    for ( i=0; i < resDir->NumberOfIdEntries; i++, resDirEntry++, _resDirEntry++ )
        PrepareNewResourceEntry(resDirEntry, _resDirEntry, resourceBase, resourceType, level+1);
}

void PrepareNewResourceEntry(PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntry, PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntryOut, DWORD resourceBase, DWORD resourceType, DWORD level)
{
	UINT i;
    PIMAGE_RESOURCE_DATA_ENTRY pResDataEntry, _pResDataEntry;
    
    if ( resDirEntry->OffsetToData & IMAGE_RESOURCE_DATA_IS_DIRECTORY )
    {
		resDirEntryOut->OffsetToData = 0x80000000 + pe.new_resource_section_size;
        PrepareNewResourceDirectory( (PIMAGE_RESOURCE_DIRECTORY)
            ((resDirEntry->OffsetToData & 0x7FFFFFFF) + resourceBase),
            resourceBase, level, level == 1 ? resDirEntry->Name : resourceType);
		return;
    }

	DWORD new_resource_section_size = pe.new_resource_section_size;
	new_resource_section_size += sizeof( IMAGE_RESOURCE_DATA_ENTRY );

	//pe.new_resource_section = ( unsigned char * ) realloc( pe.new_resource_section, new_resource_section_size );

	resDirEntryOut->OffsetToData = pe.new_resource_section_size;
	_pResDataEntry = ( PIMAGE_RESOURCE_DATA_ENTRY ) ( pe.new_resource_section + pe.new_resource_section_size );
	pe.new_resource_section_size = new_resource_section_size;

	pResDataEntry = (PIMAGE_RESOURCE_DATA_ENTRY)
                    (resourceBase + resDirEntry->OffsetToData);

	_pResDataEntry->Size = pResDataEntry->Size;
	_pResDataEntry->CodePage = pResDataEntry->CodePage;
	_pResDataEntry->Reserved = pResDataEntry->Reserved;

	if(resourceType == (DWORD)RT_ICON||resourceType == (DWORD)RT_VERSION||
       resourceType == (DWORD)RT_GROUP_ICON|| resourceType == (DWORD)RT_MANIFEST)
	{
		_pResDataEntry->OffsetToData = pe.new_resource_data_size;
		pe.new_resource_data_size += ( pResDataEntry->Size + 3 ) & ~3;
	}
	else
	{
		_pResDataEntry->OffsetToData = 0x80000000 + pe.new_resource_cdata_size;
		pe.new_resource_cdata_size += ( pResDataEntry->Size + 3 ) & ~3;
	}
}

void ProcessResourceEntry(PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntry, DWORD resourceBase, PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntryOut, DWORD resourceBaseOut, DWORD resourceType, DWORD level);

void ProcessResourceDirectory(PIMAGE_RESOURCE_DIRECTORY resDir,
							   DWORD resourceBase,
							   PIMAGE_RESOURCE_DIRECTORY resDirOut,
							   DWORD resourceBaseOut,
							   DWORD level,
							   DWORD resourceType)
{
	PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntry, resDirEntryOut;
    UINT i;

    resDirEntry = (PIMAGE_RESOURCE_DIRECTORY_ENTRY)(resDir+1);
	resDirEntryOut = (PIMAGE_RESOURCE_DIRECTORY_ENTRY)(resDirOut+1);
    
    for ( i=0; i < resDir->NumberOfNamedEntries; i++, resDirEntry++, resDirEntryOut++ )
        ProcessResourceEntry(resDirEntry, resourceBase, resDirEntryOut, resourceBaseOut, resourceType, level+1);

    for ( i=0; i < resDir->NumberOfIdEntries; i++, resDirEntry++, resDirEntryOut++ )
        ProcessResourceEntry(resDirEntry, resourceBase, resDirEntryOut, resourceBaseOut, resourceType, level+1);
}

void ProcessResourceEntry(PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntry, DWORD resourceBase, PIMAGE_RESOURCE_DIRECTORY_ENTRY resDirEntryOut, DWORD resourceBaseOut, DWORD resourceType, DWORD level)
{
	UINT i;
    PIMAGE_RESOURCE_DATA_ENTRY pResDataEntry, _pResDataEntry;
    
    if ( resDirEntry->OffsetToData & IMAGE_RESOURCE_DATA_IS_DIRECTORY )
    {
        return ProcessResourceDirectory( (PIMAGE_RESOURCE_DIRECTORY)
            ((resDirEntry->OffsetToData & 0x7FFFFFFF) + resourceBase),
			resourceBase,
			(PIMAGE_RESOURCE_DIRECTORY)
			((resDirEntryOut->OffsetToData & 0x7FFFFFFF) + resourceBaseOut),
            resourceBaseOut, level, level == 1 ? resDirEntry->Name : resourceType);
    }

    pResDataEntry = (PIMAGE_RESOURCE_DATA_ENTRY)
                    (resourceBase + resDirEntry->OffsetToData);

	_pResDataEntry = (PIMAGE_RESOURCE_DATA_ENTRY)
                    (resourceBaseOut + resDirEntryOut->OffsetToData);

	if ( _pResDataEntry->OffsetToData & 0x80000000 )
	{
		_pResDataEntry->OffsetToData = pe.resource_section_virtual_address
			+ pe.new_resource_section_size
			+ pe.new_resource_data_size
			+ ( _pResDataEntry->OffsetToData & 0x7FFFFFFF );
	}
	else
	{
		_pResDataEntry->OffsetToData = pe.resource_section_virtual_address
			+ pe.new_resource_section_size
			+ _pResDataEntry->OffsetToData;
	}

	unsigned char * src_data = ( unsigned char * ) rvatoffset( pResDataEntry->OffsetToData );
	unsigned char * dest_data = ( unsigned char * )( resourceBaseOut ) + _pResDataEntry->OffsetToData - pe.resource_section_virtual_address;

	memcpy( dest_data, src_data, pResDataEntry->Size );

	DWORD alignment = 4 - (pResDataEntry->Size & 3);
	if ( alignment & 3 ) memset( dest_data + pResDataEntry->Size, 0, alignment );
}

int compress_file(char* argv)
{
	LogMessage* message = LogMessage::GetSingleton();
	compress_data_ compress_data;
	compress_functions_ compress_functions;
    WIN32_FILE_ATTRIBUTE_DATA  wfad;
	GetFileAttributesEx(argv, GetFileExInfoStandard, &wfad);
	int filesize = wfad.nFileSizeLow;
	if (filesize < 500000)
	{
		compress_data = &compress_fr;
		compress_functions = &functions_fr;
	}
	else
	{
		compress_data = &compress_lzma;
		compress_functions = &functions_lzma;
	}
	ZeroMemory(&pe,sizeof(PE));
	message->DoLogMessage("File packed successfully!", ERR_SUCCESS);
	return 0;
}