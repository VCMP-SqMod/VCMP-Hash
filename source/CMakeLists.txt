add_library(HashMod MODULE main.cpp Functions.cpp)

if(FORCE_32BIT_BIN)
	set_target_properties(HashMod PROPERTIES COMPILE_FLAGS "-m32" LINK_FLAGS "-m32")
endif()

if(CMAKE_SIZEOF_VOID_P EQUAL 8)
	target_compile_definitions(HashMod PRIVATE _SQ64)
endif()

set_target_properties(HashMod PROPERTIES PREFIX "")

if(WIN32)
	if(CMAKE_SIZEOF_VOID_P EQUAL 8 AND NOT FORCE_32BIT_BIN)
		set_target_properties(HashMod PROPERTIES OUTPUT_NAME "hash-win64")
	else()
		set_target_properties(HashMod PROPERTIES OUTPUT_NAME "hash-win32")
	endif()
else()
	if(CMAKE_SIZEOF_VOID_P EQUAL 8 AND NOT FORCE_32BIT_BIN)
		set_target_properties(HashMod PROPERTIES OUTPUT_NAME "hash-linux64")
	else()
		set_target_properties(HashMod PROPERTIES OUTPUT_NAME "hash-linux32")
	endif()
endif(WIN32)

target_include_directories(HashMod PRIVATE ${CMAKE_CURRENT_LIST_DIR})

target_link_libraries(HashMod Base64 Hash Whirlpool)
