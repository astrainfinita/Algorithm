#include <lean/lean.h>

extern "C" LEAN_EXPORT b_lean_obj_res lean_Mutable_set(b_lean_obj_arg ref, lean_obj_arg a, b_lean_obj_arg b) {
    lean_st_ref_set(ref, a);
    return b;
}
