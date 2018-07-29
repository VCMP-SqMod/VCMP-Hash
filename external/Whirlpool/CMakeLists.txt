add_library(Whirlpool STATIC ustd.h byte_order.h byte_order.c whirlpool.h whirlpool.c whirlpool_sbox.c)

target_include_directories(Whirlpool PUBLIC ${CMAKE_CURRENT_LIST_DIR})

if(FORCE_32BIT_BIN)
	set_target_properties(Whirlpool PROPERTIES COMPILE_FLAGS "-m32" LINK_FLAGS "-m32")
endif()
