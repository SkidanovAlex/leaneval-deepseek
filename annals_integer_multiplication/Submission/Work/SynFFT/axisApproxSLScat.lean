import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.axisTSlices
import Submission.Work.SynFFT.axisScatterGetD

/-!
# `axisApproxSLScat`: the scatter of an approximate slice list

This file proves the mathematical (list-and-arithmetic) half of the `HasAxis` assembly: an
`ApproxSL` bound for the `A*B` slices of a flat array of shape `A × t × B`, read block by block
through the *scattered* index map

`i ↦ (i / (t*B) * B + i % B) * t + i / B % t`

(this is the permutation that `axisScatterGetD` inverts), transfers to the transformed array
`axisT r t B sgn u` along that axis.

Writing `q < A*t*B` for a flat position of the scattered list, `q = (α*t + j)*B + β` with
`α = q/(t*B) < A`, `j = q/B % t < t`, `β = q % B < B`, the source position of `q` in `W` is
`s*t + j` with `s = α*B + β < A*B`, and the slice through `q` is read by the same `dftN` that
`hu` bounds: this is `AxisTSlicesProp` (`Work.SynFFT.axisTSlices`) plus `s/B = α`, `s%B = β`.
The rest is `Nat`-arithmetic and `getD_map_range`.
-/

set_option maxHeartbeats 800000

namespace Work.SynFFT

/-! ## The index arithmetic of the scattered read -/

/-- For a flat position `q` of the scattered list, `B` is positive (otherwise `q < A*t*B` is
impossible). -/
theorem axisScatBpos (A t B q : ℕ) (hq : q < A * t * B) : 0 < B := by
  by_contra h
  have h0 : B = 0 := Nat.eq_zero_of_not_pos h
  subst h0
  simp at hq

/-- For a flat position `q` of the scattered list, `t` is positive. -/
theorem axisScatTpos (A t B q : ℕ) (hq : q < A * t * B) : 0 < t := by
  by_contra h
  have h0 : t = 0 := Nat.eq_zero_of_not_pos h
  subst h0
  simp at hq

/-- The outer block index `q / (t*B)` of a flat position `q < A*t*B` is `< A`. -/
theorem axisScatDivLtA (A t B q : ℕ) (hq : q < A * t * B) : q / (t * B) < A := by
  have hB : 0 < B := axisScatBpos A t B q hq
  have ht : 0 < t := axisScatTpos A t B q hq
  have hS : 0 < t * B := Nat.mul_pos ht hB
  rw [Nat.div_lt_iff_lt_mul hS]
  exact lt_of_lt_of_le hq (le_of_eq (Nat.mul_assoc A t B))

/-- The slice index `s = q/(t*B)*B + q%B` of a flat position `q < A*t*B` is `< A*B`. -/
theorem axisScatSliceLt (A t B q : ℕ) (hq : q < A * t * B) :
    q / (t * B) * B + q % B < A * B := by
  have hB : 0 < B := axisScatBpos A t B q hq
  have hdiv : q / (t * B) < A := axisScatDivLtA A t B q hq
  have hmod : q % B < B := Nat.mod_lt _ hB
  calc q / (t * B) * B + q % B < q / (t * B) * B + B := Nat.add_lt_add_left hmod _
    _ = (q / (t * B) + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right B (by omega)

/-- The slice loop index `q / B % t` of a flat position `q < A*t*B` is `< t`. -/
theorem axisScatJlt (A t B q : ℕ) (hq : q < A * t * B) : q / B % t < t := by
  have ht : 0 < t := axisScatTpos A t B q hq
  exact Nat.mod_lt _ ht

/-- `s / B = q / (t*B)` for the slice index `s = q/(t*B)*B + q%B`. -/
theorem axisScatDivB (A t B q : ℕ) (hq : q < A * t * B) :
    (q / (t * B) * B + q % B) / B = q / (t * B) := by
  have hB : 0 < B := axisScatBpos A t B q hq
  have hmod : q % B < B := Nat.mod_lt _ hB
  rw [Nat.add_comm (q / (t * B) * B) (q % B), Nat.add_mul_div_right (q % B) (q / (t * B)) hB,
    Nat.div_eq_of_lt hmod, Nat.zero_add]

/-- `s % B = q % B` for the slice index `s = q/(t*B)*B + q%B`. -/
theorem axisScatModB (A t B q : ℕ) (hq : q < A * t * B) :
    (q / (t * B) * B + q % B) % B = q % B := by
  have hB : 0 < B := axisScatBpos A t B q hq
  have hmod : q % B < B := Nat.mod_lt _ hB
  rw [Nat.mul_comm (q / (t * B)) B, Nat.mul_add_mod, Nat.mod_eq_of_lt hmod]

/-! ## The scattered `ApproxSL` transfer -/

theorem axisApproxSLScat (p r A t B : ℕ) (sgn : ℤ) (u : Work.SynFFT.Arr r) (E : ℝ)
    (W W' : List (List (ℤ × ℤ))) (h : W.length = A * B * t)
    (hW' : W' = (List.range (A * t * B)).map
        (fun i => W.getD ((i / (t * B) * B + i % B) * t + i / B % t) []))
    (hu : ∀ s, s < A * B → ∀ j, j < t → ∀ c : Fin r,
      (2 : ℝ) ^ p * ‖HvdH.fxC p ((W.getD (s * t + j) []).getD (c : ℕ) (0, 0)) -
        Work.SynFFT.dftN r t sgn (fun j' c' => u ((s / B * t + j') * B + s % B) c') j c‖ ≤ E) :
    Work.SynFFT.ApproxSL p r (A * t * B) W' (Work.SynFFT.axisT r t B sgn u) E := by
  subst hW'
  unfold ApproxSL
  constructor
  · simp
  · intro q hq c
    -- read the scattered list at `q`
    have hget : ((List.range (A * t * B)).map
        (fun i => W.getD ((i / (t * B) * B + i % B) * t + i / B % t) [])).getD q [] =
        W.getD ((q / (t * B) * B + q % B) * t + q / B % t) [] :=
      getD_map_range _ [] hq
    rw [hget]
    -- the axis transform at `q` is the `dftN` of the slice through `q`
    have hTS := axisTSlices r A t B sgn u q hq (axisScatTpos A t B q hq)
      (axisScatBpos A t B q hq)
    rw [hTS]
    -- ... and that `dftN` is the one `hu` bounds, with `s = q/(t*B)*B + q%B`
    have hFG : (fun u' : ℕ => u ((q / (t * B) * t + u') * B + q % B)) =
        (fun j' c' => u (((q / (t * B) * B + q % B) / B * t + j') * B +
          (q / (t * B) * B + q % B) % B) c') := by
      funext j' c'
      rw [axisScatDivB A t B q hq, axisScatModB A t B q hq]
    rw [hFG]
    exact hu (q / (t * B) * B + q % B) (axisScatSliceLt A t B q hq) (q / B % t)
      (axisScatJlt A t B q hq) c

end Work.SynFFT
