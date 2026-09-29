import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# `axisTSlices`: the flat index formula for one axis of a lexicographic array

`axisT r t B sgn a` transforms along the middle axis of a flat array of shape `A × t × B`
(the axis index runs with stride `B`); `dftN r t sgn` is the one-dimensional transform of a
*list* of positions.  Reading `axisT` at a flat position `idx` gives the transform of the slice
through `idx`, i.e. the `dftN` of the map `u ↦ a ((idx / (t*B) * t + u) * B + idx % B)`, evaluated
at the slice index `idx / B % t`.

The only content is arithmetic: the "source" index of the axis stage,
`idx - (idx / B % t) * B + u * B`, must coincide with the slice-based index
`(idx / (t*B) * t + u) * B + idx % B`.  Both are `t*B * (idx / (t*B)) + u*B + idx % B`.
-/

set_option autoImplicit false

namespace Work.SynFFT

/-- The flat index of element `u` of the slice through `idx`, in the two forms used by
`axisT` (source position of the butterfly) and by `dftN` (slice through `idx`). -/
lemma axisT_arg (t B idx u : ℕ) :
    idx - (idx / B % t) * B + u * B = (idx / (t * B) * t + u) * B + idx % B := by
  -- `idx % (t*B) = (idx/B % t) * B + idx % B`
  have hmod : idx % (t * B) = (idx / B % t) * B + idx % B := by
    conv_lhs => rw [← Nat.div_add_mod' (idx % (t * B)) B]
    rw [Nat.mod_mul_left_div_self idx B t, Nat.mod_mul_left_mod idx t B]
  have hX : idx = (t * B) * (idx / (t * B)) + ((idx / B % t) * B + idx % B) := by
    rw [← hmod]
    exact (Nat.div_add_mod idx (t * B)).symm
  -- hence `idx - (idx/B % t) * B = (t*B) * (idx/(t*B)) + idx % B`
  have hsub : idx - (idx / B % t) * B = (t * B) * (idx / (t * B)) + idx % B := by
    set X := (t * B) * (idx / (t * B)) with hXdef
    set cB := (idx / B % t) * B with hcBdef
    have hidx : idx = X + (cB + idx % B) := by
      rw [hXdef, hcBdef]
      exact hX
    omega
  rw [hsub]
  ring

theorem axisTSlices : Work.SynFFT.AxisTSlicesProp := by
  intro r A t B sgn a idx hidx ht hB
  funext c
  simp only [axisT, dftN]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [axisT_arg t B idx u]

end Work.SynFFT
