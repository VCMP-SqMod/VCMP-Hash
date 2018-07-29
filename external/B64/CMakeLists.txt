add_library(Base64 STATIC b64.h encode.c decode.c)

target_include_directories(Base64 PUBLIC ${CMAKE_CURRENT_LIST_DIR})

if(FORCE_32BIT_BIN)
	set_target_properties(Base64 PROPERTIES COMPILE_FLAGS "-m32" LINK_FLAGS "-m32")
endif()
