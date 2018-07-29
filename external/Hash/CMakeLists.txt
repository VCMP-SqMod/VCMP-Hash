add_library(Hash STATIC endian.h crc32.cpp crc32.h digest.cpp hash.h hmac.h keccak.cpp keccak.h md5.cpp md5.h sha1.cpp sha1.h sha256.cpp sha256.h sha3.cpp sha3.h)

target_include_directories(Hash PUBLIC ${CMAKE_CURRENT_LIST_DIR})

if(FORCE_32BIT_BIN)
	set_target_properties(Hash PROPERTIES COMPILE_FLAGS "-m32" LINK_FLAGS "-m32")
endif()
