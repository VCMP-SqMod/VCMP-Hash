#include "Functions.h"
#include "squirrel.h"
#include "crc32.h"
#include "keccak.h"
#include "md5.h"
#include "sha1.h"
#include "sha256.h"
#include "sha3.h"
#include "b64.h"
#include "whirlpool.h"

#include <string>

#define SQMD_SUCCESS 0
#define SQMD_FAILURE 1

extern HSQAPI sq;

/* ------------------------------------------------------------------------------------------------
 * Helper structure for retrieving a value from the stack as a string or a formatted string.
*/
struct StackStrF
{
    const SQChar *  mPtr; ///< Pointer to the C string that was retrieved.
    SQInteger       mLen; ///< The string length if it could be retrieved.
    SQRESULT        mRes; ///< The result of the retrieval attempts.
    HSQOBJECT       mObj; ///< Strong reference to the string object.
    HSQUIRRELVM     mVM; ///< The associated virtual machine.

    /* --------------------------------------------------------------------------------------------
     * Default constructor.
    */
    StackStrF()
        : mPtr(_SC(""))
        , mLen(0)
        , mRes(SQ_OK)
        , mObj()
        , mVM(v)
    {
        // Reset the converted value object
        sq->resetobject(&mObj);
    }

    /* --------------------------------------------------------------------------------------------
     * Compile time string constructor.
    */
    template < size_t N > StackStrF(const SQChar(&str)[N])
        : mPtr(str)
        , mLen(N)
        , mRes(SQ_OK)
        , mObj()
        , mVM(v)
    {
        // Reset the converted value object
        sq->resetobject(&mObj);
    }

    /* --------------------------------------------------------------------------------------------
     * Base constructor.
    */
    StackStrF(HSQUIRRELVM vm, SQInteger idx, bool fmt = false, bool dummy = false)
        : mPtr(nullptr)
        , mLen(-1)
        , mRes(SQ_OK)
        , mObj()
        , mVM(vm)
    {
        // Reset the converted value object
        sq->resetobject(&mObj);
        // is this a dummy request?
        if (dummy)
        {
            // Since this is a dummy then avoid making it look like a failure
            mPtr = _SC("");
            mLen = 0;
            // We're not supposed to proceed with this!
            return;
        }
        // Grab the top of the stack
        const SQInteger top = sq->gettop(vm);
        // Was the string or value specified?
        if (top <= (idx - 1))
        {
            mRes = sq->throwerror(vm, "Missing string or value");
        }
        // Do we have enough values to call the format function and are we allowed to?
        else if (fmt && (top - 1) >= idx)
        {
            mRes = sq->throwerror(vm, "Function `sqstd_format` is not exported in official plugin");
        }
        // Is the value on the stack an actual string?
        else if (sq->gettype(vm, idx) == OT_STRING)
        {
            // Obtain a reference to the string object
            mRes = sq->getstackobj(vm, idx, &mObj);
            // Could we retrieve the object from the stack?
            if (SQ_SUCCEEDED(mRes))
            {
                // Keep a strong reference to the object
                sq->addref(vm, &mObj);
                // Attempt to retrieve the string value from the stack
                mRes = sq->getstring(vm, idx, &mPtr);
                // If we could get the string then we can get the size as well
                if (SQ_SUCCEEDED(mRes))
                {
                    mLen = sq->getsize(vm, idx);
                }
            }
            // Did the retrieval succeeded but ended up with a null string pointer?
            if (SQ_SUCCEEDED(mRes) && !mPtr)
            {
                mRes = sq->throwerror(vm, "Unable to retrieve the string");
            }
        }
        // We have to try and convert it to string
        else
        {
            // Attempt to convert the value from the stack to a string
            mRes = sq->tostring(vm, idx);
            // Could we convert the specified value to string?
            if (SQ_SUCCEEDED(mRes))
            {
                // Obtain a reference to the resulted object
                mRes = sq->getstackobj(vm, -1, &mObj);
                // Could we retrieve the object from the stack?
                if (SQ_SUCCEEDED(mRes))
                {
                    // Keep a strong reference to the object
                    sq->addref(vm, &mObj);
                    // Attempt to obtain the string pointer
                    mRes = sq->getstring(vm, -1, &mPtr);
                    // If we could get the string then we can get the size as well
                    if (SQ_SUCCEEDED(mRes))
                    {
                        mLen = sq->getsize(vm, -1);
                    }
                }
            }
            // Pop a value from the stack regardless of the result
            sq->pop(vm, 1);
            // Did the retrieval succeeded but ended up with a null string pointer?
            if (SQ_SUCCEEDED(mRes) && !mPtr)
            {
                mRes = sq->throwerror(vm, "Unable to retrieve the value");
            }
        }
    }

    /* --------------------------------------------------------------------------------------------
     * Copy constructor. (disabled)
    */
    StackStrF(const StackStrF & o) = delete;

    /* --------------------------------------------------------------------------------------------
     * Move constructor.
    */
    StackStrF(StackStrF && o)
        : mPtr(o.mPtr)
        , mLen(o.mLen)
        , mRes(o.mRes)
        , mObj(o.mObj)
        , mVM(o.mVM)
    {
        o.mPtr = nullptr;
        o.mLen = 0;
        o.mRes = SQ_OK;
        o.mVM = nullptr;
        sq->resetobject(&o.mObj);
    }

    /* --------------------------------------------------------------------------------------------
     * Destructor.
    */
    ~StackStrF()
    {
        if (mVM && !sq_isnull(mObj))
        {
            sq->release(mVM, &mObj);
        }
    }

    /* --------------------------------------------------------------------------------------------
     * Copy assignment operator. (disabled)
    */
    StackStrF & operator = (const StackStrF & o) = delete;

    /* --------------------------------------------------------------------------------------------
     * Move assignment operator. (disabled)
    */
    StackStrF & operator = (StackStrF && o) = delete;
};

// ------------------------------------------------------------------------------------------------
using String = std::basic_string<SQChar>;

/* ------------------------------------------------------------------------------------------------
 * Utility to avoid creating encoder instances for each call.
*/
template < class T > struct BaseHash
{
    static T Algo;
};

// ------------------------------------------------------------------------------------------------
template < class T > T BaseHash< T >::Algo;

/* ------------------------------------------------------------------------------------------------
 * Hash the specified value or the result of a formatted string.
*/
template < class T > static SQInteger HashF(HSQUIRRELVM vm)
{
    // Attempt to retrieve the value from the stack as a string
    StackStrF val(vm, 2, true);
    // Have we failed to retrieve the string?
    if (SQ_FAILED(val.mRes))
    {
        return val.mRes; // Propagate the error!
    }
    // Forward the call to the actual implementation and store the string
    String str(BaseHash< T >::Algo(val.mPtr, static_cast< size_t >(val.mLen)));
    // Push the string on the stack
    sq->pushstring(vm, str.data(), str.size());
    // At this point we have a valid string on the stack
    return 1;
}

/* ------------------------------------------------------------------------------------------------
 * Hash the specified value or the result of a formatted string with whirlpool algorithm.
*/
static SQInteger WhirlpoolF(HSQUIRRELVM vm)
{
    // Attempt to retrieve the value from the stack as a string
    StackStrF val(vm, 2, true);
    // Have we failed to retrieve the string?
    if (SQ_FAILED(val.mRes))
    {
        return val.mRes; // Propagate the error!
    }
    // Prepare a whirlpool hashing context
    whirlpool_ctx ctx;
    // Initialize the hashing context
    rhash_whirlpool_init(&ctx);
    // Update the context with the given string
    rhash_whirlpool_update(&ctx, reinterpret_cast< const unsigned char * >(val.mPtr),
                                    val.mLen < 0 ? 0 : static_cast< size_t >(val.mLen));
    // Reserve space for the result in binary form
    unsigned char raw_hash[whirlpool_block_size];
    // Finalize hashing and obtain the result
    rhash_whirlpool_final(&ctx, raw_hash);
    // Reserve space for the hexadecimal string
    char hex_hash[whirlpool_block_size * 2];
    // Convert from binary form to hex string
    for (int i = 0, p = 0; i < whirlpool_block_size; ++i)
    {
        static const char dec2hex[16+1] = "0123456789abcdef";
        hex_hash[p++] = dec2hex[(raw_hash[i] >> 4) & 15];
        hex_hash[p++] = dec2hex[ raw_hash[i]       & 15];
    }
    // Push the string on the stack
    sq->pushstring(vm, hex_hash, whirlpool_block_size * 2);
    // At this point we have a valid string on the stack
    return 1;
}

/* ------------------------------------------------------------------------------------------------
 * Encode the specified value or the result of a formatted string with base64 algorithm.
*/
static SQInteger EncodeBase64F(HSQUIRRELVM vm)
{
    // Attempt to retrieve the value from the stack as a string
    StackStrF val(vm, 2, true);
    // Have we failed to retrieve the string?
    if (SQ_FAILED(val.mRes))
    {
        return val.mRes; // Propagate the error!
    }
    // Size of the encoded string
    size_t enclen = 0;
    // Attempt to encode the resulted string
    char * result = b64_encode_ex(reinterpret_cast< const unsigned char * >(val.mPtr),
                                val.mLen < 0 ? 0 : static_cast< size_t >(val.mLen), &enclen);
    // Did we fail to allocate memory for it?
    if (!result)
    {
        return sq->throwerror(vm, _SC("Unable to allocate memory for output"));
    }
    // Push the string on the stack
    sq->pushstring(vm, result, static_cast< SQInteger >(enclen));
    // At this point we have a valid string on the stack
    return 1;
}

/* ------------------------------------------------------------------------------------------------
 * Decode the specified value or the result of a formatted string with base64 algorithm.
*/
static SQInteger DecodeBase64F(HSQUIRRELVM vm)
{
    // Attempt to retrieve the value from the stack as a string
    StackStrF val(vm, 2, true);
    // Have we failed to retrieve the string?
    if (SQ_FAILED(val.mRes))
    {
        return val.mRes; // Propagate the error!
    }
    // Size of the decoded string
    size_t declen = 0;
    // Attempt to decode the resulted string
    unsigned char * result = b64_decode_ex(val.mPtr, val.mLen < 0 ? 0 : static_cast< size_t >(val.mLen), &declen);
    // Did we fail to allocate memory for it?
    if (!result)
    {
        return sq->throwerror(vm, _SC("Unable to allocate memory for output"));
    }
    // Push the string on the stack
    sq->pushstring(vm, reinterpret_cast< const SQChar * >(result), static_cast< SQInteger >(declen));
    // At this point we have a valid string on the stack
    return 1;
}

// Function used to register native functions into the squirrel virtual machine
void RegisterSquirrelFunc(HSQUIRRELVM vm, SQFUNCTION pointer, const SQChar * name, unsigned char params, const SQChar * mask)
{
    // Push the root table to specify in which table we register the function
    sq->pushroottable(vm);
    // Push the name of the function
    sq->pushstring(vm, name, -1);
    // Push the function pointer
    sq->newclosure(vm, pointer, 0);
    // Create the function
    sq->setnativeclosurename(vm, -1, name);
    sq->newslot(vm, -3, SQFalse);
    // Pop the root table
    sq->pop(vm, 1);
}

void RegisterFuncs(HSQUIRRELVM vm)
{
    RegisterSquirrelFunc(vm, EncodeBase64F, "base64_encode", 0, NULL);
    RegisterSquirrelFunc(vm, DecodeBase64F, "base64_decode", 0, NULL);

    RegisterSquirrelFunc(vm, HashF< CRC32 >, _SC("CRC32"), 0, NULL);
    RegisterSquirrelFunc(vm, HashF< Keccak >, _SC("KECCAK"), 0, NULL);
    RegisterSquirrelFunc(vm, HashF< MD5 >, _SC("MD5"), 0, NULL);
    RegisterSquirrelFunc(vm, HashF< SHA1 >, _SC("SHA1"), 0, NULL);
    RegisterSquirrelFunc(vm, HashF< SHA256 >, _SC("SHA256"), 0, NULL);
    RegisterSquirrelFunc(vm, HashF< SHA3 >, _SC("SHA3"), 0, NULL);
    RegisterSquirrelFunc(vm, WhirlpoolF, _SC("WHIRLPOOL"), 0, NULL);
}
