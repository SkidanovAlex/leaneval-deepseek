import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.H2.T1Q.SliceIntQ
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.EllPkgClsVop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The `θ`-derivative of `PhiTil`**: it splits unconditionally (the only `θ`-dependence of the
correction is the explicit factor `sin 2θ`). -/
theorem pth_PhiTil_eq {α : ℝ} {F Ψ : Fn} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    Work.Spaces.pth (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pth Ψ z θ
        - deriv (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z) θ := by
  have hfun : (fun θ' => Work.Construction.PhiTil α F Ψ z θ')
      = fun θ' => Ψ z θ' - (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  have hd2 : DifferentiableAt ℝ
      (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z) θ := by
    fun_prop
  simp only [Work.Spaces.pth]
  rw [hfun]
  rw [show (fun θ' => Ψ z θ' - (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z)
      = (fun θ' => Ψ z θ')
        - (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z) from rfl,
    deriv_sub (differentiableAt_tslice hΨ hz h0 h1) hd2]

/-- **The `z`-derivative of `PhiTil`**: it splits as soon as the `L₁₂`-part is differentiable. -/
theorem pz_PhiTil_eq {α : ℝ} {F Ψ : Fn} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ}
    (hu : DifferentiableAt ℝ (fun z' => (1 / (4 * α)) * Work.Construction.L12 F z') z)
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    Work.Spaces.pz (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Spaces.pz Ψ z θ
        - deriv (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
            * Work.Construction.L12 F z') z := by
  have hfun : (fun z' => Work.Construction.PhiTil α F Ψ z' θ)
      = fun z' => Ψ z' θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z' := by
    funext z'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  have hd2 : DifferentiableAt ℝ
      (fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z') z := by
    refine (hu.const_mul (Real.sin (2 * θ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun z' => ?_))
    ring
  simp only [Work.Spaces.pz]
  rw [hfun]
  rw [show (fun z' => Ψ z' θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z')
      = (fun z' => Ψ z' θ)
        - (fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z') from rfl,
    deriv_sub (differentiableAt_zslice hΨ hz h0 h1) hd2]

/-- **The `V`-slot identifies the `L₁₂`-part of `PhiTil`.**  On the open quadrant,

  `Vop (PhiTil α F Ψ) = Vop Ψ + (1/(4α)) (tan θ · sin 2θ - 2 cos 2θ) · L₁₂(F)`.

Only the *values* of `∂_θ` occur, so this identity is unconditionally valid. -/
theorem Vop_PhiTil_eq {α : ℝ} {F Ψ : Fn} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z θ
      = Work.Construction.Vop Ψ z θ
        + (1 / (4 * α)) * (Real.tan θ * Real.sin (2 * θ) - 2 * Real.cos (2 * θ))
            * Work.Construction.L12 F z := by
  have hpth := pth_PhiTil_eq (α := α) (F := F) (Ψ := Ψ) hΨ hz h0 h1
  have hval : Work.Construction.PhiTil α F Ψ z θ
      = Ψ z θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z := by
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  simp only [Work.Construction.Vop]
  rw [hpth, hval, deriv_const_sin_two_mul]
  ring

/-- **The `θ = π/4` identification of `L₁₂`.**  On `z > 0`,

  `L₁₂(F)(z) = 4α (Vop (PhiTil α F Ψ) z (π/4) - Vop Ψ z (π/4))`. -/
theorem L12_eq_of_Vop {α : ℝ} (hα : α ≠ 0) {F Ψ : Fn}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {z : ℝ} (hz : 0 < z) :
    Work.Construction.L12 F z
      = (Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z (π / 4)
          - Work.Construction.Vop Ψ z (π / 4)) * (4 * α) := by
  have h := Vop_PhiTil_eq (α := α) (F := F) (Ψ := Ψ) hΨ (z := z) (θ := π / 4) hz
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsin : Real.sin (2 * (π / 4)) = 1 := by
    rw [show 2 * (π / 4) = π / 2 from by ring, Real.sin_pi_div_two]
  have hcos : Real.cos (2 * (π / 4)) = 0 := by
    rw [show 2 * (π / 4) = π / 2 from by ring, Real.cos_pi_div_two]
  rw [Real.tan_pi_div_four, hsin, hcos] at h
  norm_num at h
  have hcoef : α⁻¹ * (1 / 4) = 1 / (4 * α) := by ring
  rw [hcoef] at h
  have h4 : (4 * α : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hα
  have hmul : (1 / (4 * α)) * (4 * α) = 1 := by
    rw [one_div, inv_mul_cancel₀ h4]
  have hkey : (1 / (4 * α)) * Work.Construction.L12 F z
      = Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z (π / 4)
        - Work.Construction.Vop Ψ z (π / 4) := by linarith [h]
  calc Work.Construction.L12 F z
      = ((1 / (4 * α)) * (4 * α)) * Work.Construction.L12 F z := by rw [hmul, one_mul]
    _ = ((1 / (4 * α)) * Work.Construction.L12 F z) * (4 * α) := by ring
    _ = (Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z (π / 4)
          - Work.Construction.Vop Ψ z (π / 4)) * (4 * α) := by rw [hkey]

/-- **`z ↦ L₁₂(F)(z)` is differentiable on `(0,∞)`** for the source `F` of a pair whose
`V`-slot is smooth on the open quadrant and whose stream function is `SmoothOpen`. -/
theorem differentiableAt_L12_of_Vop {α : ℝ} (hα : α ≠ 0) {F Ψ : Fn}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.Construction.PhiTil α F Ψ)))
    {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 F z') z := by
  have hs1 : ContDiffOn ℝ 1
      (fun z' => Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z' (π / 4))
      (Set.Ioi 0) := contDiffOn_slice_pi_div_four (n := 1) (hV.forall 1)
  have hs2 : ContDiffOn ℝ 1 (fun z' => Work.Construction.Vop Ψ z' (π / 4)) (Set.Ioi 0) :=
    contDiffOn_slice_pi_div_four (n := 1) ((smoothOpen_Vop hΨ).forall 1)
  have hd : DifferentiableAt ℝ (fun z' =>
      Work.Construction.Vop (Work.Construction.PhiTil α F Ψ) z' (π / 4)
        - Work.Construction.Vop Ψ z' (π / 4)) z :=
    ((hs1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).sub
      ((hs2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz))
  refine (hd.mul_const (4 * α)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact L12_eq_of_Vop hα (F := F) (Ψ := Ψ) hΨ hz'



end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXA1w.Helpers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Slice and slot lemmas for the `C⁴` mixed calculus

* `contDiffOn_uncurry_mixed_shift`, `contDiffOn_uncurry_mixed_Q0`, `contDiffOn_slice_mixed`:
  the finite-order `D`-calculus on the open quadrant and its `θ`-slices;
* `mixed_slot_sq_w_le_HkIntegrand`: a mixed slot with the radial weight `w` is dominated by
  `sin(2θ)^γ · HkIntegrand α 4 f`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

/-- `D_z^j D_θ^i` lowers the differentiability order by `i + j` on an open set. -/
theorem contDiffOn_uncurry_mixed_shift {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (j i n : ℕ) (h : ContDiffOn ℝ (n + i + j) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed j i G)) V := by
  have heq : ((n : WithTop ℕ∞) + i + j) = ((n : WithTop ℕ∞) + j + i) := by abel
  have h1 : ContDiffOn ℝ (n + j + i) (Function.uncurry G) V := by
    rw [← heq]; exact h
  have h2 : ContDiffOn ℝ (n + j) (Function.uncurry (Work.Spaces.DthIter i G)) V :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift hV i (n + j) h1
  exact Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift hV j n h2

/-- The mixed slot `D_z^jD_θ^if` is `C^n` on the open quadrant, for `n + i + j ≤ 4`. -/
theorem contDiffOn_uncurry_mixed_Q0 {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (j i n : ℕ) (h : n + i + j ≤ 4) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed j i f)) Work.FTS.EllipticEst.Q0 :=
  contDiffOn_uncurry_mixed_shift Work.FTS.EllipticEst.isOpen_Q0 j i n
    (h4.of_le (Nat.cast_le.mpr h))

/-- The `θ`-slice of a mixed slot is `C^n` on `(0,π/2)`. -/
theorem contDiffOn_slice_mixed {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (j i n : ℕ) (h : n + i + j ≤ 4) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ n (fun θ => Work.Spaces.mixed j i f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.StrongEps.EComparison.contDiffOn_slice_t hz (contDiffOn_uncurry_mixed_Q0 h4 j i n h)

/-- **A mixed slot with weight `w` is dominated by the `ℋ⁴`-integrand.**

For an interior angle `θ` where `sin(2θ) > 0`, `(D_z^jD_θ^if · w)²` is at most
`sin(2θ)^γ · HkIntegrand α 4 f`, because the slot occurs in `HkIntegrand` with the full
weight `W = w sin(2θ)^{-γ/2}`. -/
theorem mixed_slot_sq_w_le_HkIntegrand {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (j i : ℕ)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hsin : 0 < Real.sin (2 * θ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hθ
  have hi5 : i < 5 := by omega
  have hj5 : j < 5 := by omega
  have hterm : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
    have hinner : ∀ i' ∈ Finset.range 5,
        (if 1 ≤ i' ∧ i' + j ≤ 4 then (Work.Spaces.mixed j i' f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
          ≤ ∑ j' ∈ Finset.range 5,
              (if 1 ≤ i' ∧ i' + j' ≤ 4
                then (Work.Spaces.mixed j' i' f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      intro i' _
      refine Finset.single_le_sum
        (f := fun j' => if 1 ≤ i' ∧ i' + j' ≤ 4
          then (Work.Spaces.mixed j' i' f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        (fun j' _ => ?_) (Finset.mem_range.mpr hj5)
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
    have houter : ∀ i' ∈ Finset.range 5,
        0 ≤ ∑ j' ∈ Finset.range 5,
              (if 1 ≤ i' ∧ i' + j' ≤ 4
                then (Work.Spaces.mixed j' i' f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      intro i' _
      refine Finset.sum_nonneg fun j' _ => ?_
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
    rw [Work.Spaces.HkIntegrand]
    refine le_trans ?_ (le_add_of_nonneg_left
      (Finset.sum_nonneg fun i' _ => sq_nonneg _))
    calc (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (if 1 ≤ i ∧ i + j ≤ 4
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          rw [if_pos ⟨hi, hij⟩]
      _ ≤ ∑ j' ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j' ≤ 4
                then (Work.Spaces.mixed j' i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
          hinner i (Finset.mem_range.mpr hi5)
      _ ≤ ∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5,
              (if 1 ≤ i' ∧ i' + j' ≤ 4
                then (Work.Spaces.mixed j' i' f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
          Finset.single_le_sum houter (Finset.mem_range.mpr hi5)
  have hwedge : (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) := by
    rw [show Work.Spaces.Wt α z θ
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) from rfl]
    rw [show (Work.Spaces.mixed j i f z θ
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
        = (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 from by ring]
    rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by
      rw [sq, ← Real.rpow_add hsin]; congr 1; ring]
    rw [mul_assoc, ← Real.rpow_add hsin,
      show -(Work.Spaces.gam α) + Work.Spaces.gam α = 0 by ring, Real.rpow_zero, mul_one]
  calc (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) := hwedge
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) :=
        mul_le_mul_of_nonneg_right hterm (Real.rpow_nonneg hsin.le _)
    _ = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) * Work.Spaces.HkIntegrand α 4 f z θ := by
        ring

end Work.FTS_RegExport.RXA1w
end
end
