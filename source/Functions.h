#include "main.h"
#include "SQModule.h"
#pragma once

extern HSQUIRRELVM v;

#ifdef __cplusplus
extern "C"
{
#endif

	void				    RegisterSquirrelFunc				( HSQUIRRELVM v, SQFUNCTION f, const SQChar* fname, unsigned char uiParams, const SQChar* szParams );
	void					RegisterFuncs						( HSQUIRRELVM v );

#ifdef __cplusplus
}
#endif

#define _SQUIRRELDEF( x ) SQInteger x( HSQUIRRELVM v )
