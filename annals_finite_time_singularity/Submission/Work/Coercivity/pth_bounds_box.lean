/-
# Bounds for `∂_θ f`, `∂_z f`, `∂_z ∂_θ f`, `∂_θ² f` on the box `(0,R) × Iθ`

The lemma `pth_bounds_box` collects the four elementary bounds on the box for a function
`f` which is smooth on a neighbourhood of the closed quadrant and satisfies

  `f(0,θ) = 0`,  `∂_z f(0,θ) = 0`   for all `θ ∈ Iθ`,

namely, for `0 < z < R` and `θ ∈ [0,π/2]`,

  `|∂_θ f z θ| ≤ C z²`,  `|∂_z f z θ| ≤ C z`,  `|∂_z ∂_θ f z θ| ≤ C z`,  `|∂_θ² f z θ| ≤ C`.

All four are instances of the fundamental theorem of calculus on the radial slice
`z' ↦ ∂_z^j ∂_θ^i f z' θ`, whose base value at `z = 0` vanishes and whose `z`-derivative
is bounded on the box `[0,R] × Iθ` by a supremum of a continuous function on a compact
set.  The only point requiring care is the base value `∂_z ∂_θ f (0,θ) = 0`: it is the
`θ`-derivative of `∂_z f(0,·)`, which vanishes on `Iθ`; at the two endpoints `θ = 0`,
`θ = π/2` the vanishing of a differentiable function on a one-sided neighbourhood of the
point forces the two-sided derivative to vanish (`deriv_zero_on_Itheta`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.SmoothNbhd_pth_slice
import Submission.Work.Coercivity.Dz_alg
import Submission.Work.Coercivity.deriv_zero_on_Itheta
import Submission.Work.Coercivity.slice_abs_le_sq_ftc
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.dth_bd0_of_IBP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem pth_bounds_box (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) (R : ℝ) (hR : 0 < R)
    (h0 : ∀ θ ∈ Spaces.Iθ, f 0 θ = 0 ∧ Spaces.pz f 0 θ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.pth f z θ| ≤ C * z ^ 2
      ∧ |Spaces.pz f z θ| ≤ C * z
      ∧ |Spaces.pz (Spaces.pth f) z θ| ≤ C * z
      ∧ |Spaces.pth (Spaces.pth f) z θ| ≤ C := by
  -- ## Smoothness of the partial derivatives
  have hsm_pz : Spaces.SmoothNbhd (Spaces.pz f) :=
    Spaces.contDiffOn_uncurry_pz Spaces.isOpen_U hsm
  have hsm_pth : Spaces.SmoothNbhd (Spaces.pth f) :=
    Spaces.contDiffOn_uncurry_pth Spaces.isOpen_U hsm
  have hsm_pzpz : Spaces.SmoothNbhd (Spaces.pz (Spaces.pz f)) :=
    Spaces.contDiffOn_uncurry_pz Spaces.isOpen_U hsm_pz
  have hsm_pzpth : Spaces.SmoothNbhd (Spaces.pz (Spaces.pth f)) :=
    Spaces.contDiffOn_uncurry_pz Spaces.isOpen_U hsm_pth
  have hsm_pzpzpth : Spaces.SmoothNbhd (Spaces.pz (Spaces.pz (Spaces.pth f))) :=
    Spaces.contDiffOn_uncurry_pz Spaces.isOpen_U hsm_pzpth
  have hsm_pthpth : Spaces.SmoothNbhd (Spaces.pth (Spaces.pth f)) :=
    Spaces.contDiffOn_uncurry_pth Spaces.isOpen_U hsm_pth
  -- ## The four suprema on the box
  set M2 : ℝ := Spaces.boxSup R (Spaces.pz (Spaces.pz f)) with hM2def
  set M3 : ℝ := Spaces.boxSup R (Spaces.pz (Spaces.pz (Spaces.pth f))) with hM3def
  set M4 : ℝ := Spaces.boxSup R (Spaces.pth (Spaces.pth f)) with hM4def
  have hb2 : BddAbove (Spaces.boxSet R (Spaces.pz (Spaces.pz f))) :=
    Spaces.bddAbove_boxSup_of_continuousOn
      (Spaces.continuousOn_box_of_contDiffOn (Spaces.contDiffOn_uncurry_pz Spaces.isOpen_U hsm_pz))
  have hb3 : BddAbove (Spaces.boxSet R (Spaces.pz (Spaces.pz (Spaces.pth f)))) :=
    Spaces.bddAbove_boxSup_of_continuousOn
      (Spaces.continuousOn_box_of_contDiffOn (Spaces.contDiffOn_uncurry_pz Spaces.isOpen_U hsm_pzpth))
  have hb4 : BddAbove (Spaces.boxSet R (Spaces.pth (Spaces.pth f))) :=
    Spaces.bddAbove_boxSup_of_continuousOn
      (Spaces.continuousOn_box_of_contDiffOn (Spaces.contDiffOn_uncurry_pth Spaces.isOpen_U hsm_pth))
  have hbnd2 : ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.pz (Spaces.pz f) z θ| ≤ M2 := by
    intro z hz θ hθ
    rw [hM2def]
    exact Spaces.le_boxSup hb2 hz hθ
  have hbnd3 : ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.pz (Spaces.pz (Spaces.pth f)) z θ| ≤ M3 := by
    intro z hz θ hθ
    rw [hM3def]
    exact Spaces.le_boxSup hb3 hz hθ
  have hbnd4 : ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.pth (Spaces.pth f) z θ| ≤ M4 := by
    intro z hz θ hθ
    rw [hM4def]
    exact Spaces.le_boxSup hb4 hz hθ
  have hM2nn : 0 ≤ M2 := by rw [hM2def]; exact Spaces.boxSup_nonneg hR.le hb2
  have hM3nn : 0 ≤ M3 := by rw [hM3def]; exact Spaces.boxSup_nonneg hR.le hb3
  have hM4nn : 0 ≤ M4 := by rw [hM4def]; exact Spaces.boxSup_nonneg hR.le hb4
  -- ## The three vanishing boundary values at `z = 0`
  have hpz0 : ∀ θ ∈ Spaces.Iθ, Spaces.pz f 0 θ = 0 := fun θ hθ => (h0 θ hθ).2
  have hpth0 : ∀ θ ∈ Spaces.Iθ, Spaces.pth f 0 θ = 0 := by
    intro θ hθ
    have hd : DifferentiableAt ℝ (fun θ' => f 0 θ') θ :=
      ((SmoothNbhd_pth_slice f hsm 0 (le_refl 0)).1 θ hθ).differentiableAt
    exact deriv_zero_on_Itheta hθ hd (fun θ' hθ' => (h0 θ' hθ').1)
  have hpthpz0 : ∀ θ ∈ Spaces.Iθ, Spaces.pth (Spaces.pz f) 0 θ = 0 := by
    intro θ hθ
    have hd : DifferentiableAt ℝ (fun θ' => Spaces.pz f 0 θ') θ :=
      ((SmoothNbhd_pth_slice (Spaces.pz f) hsm_pz 0 (le_refl 0)).1 θ hθ).differentiableAt
    exact deriv_zero_on_Itheta hθ hd (fun θ' hθ' => (h0 θ' hθ').2)
  have hApz0 : ∀ θ ∈ Spaces.Iθ, Spaces.pz (Spaces.pth f) 0 θ = 0 := by
    intro θ hθ
    have hmem : ((0 : ℝ), θ) ∈ Spaces.U := Spaces.mem_U_of_dom Spaces.zero_mem_Iz hθ
    have hcd : ContDiffAt ℝ 2 (Function.uncurry f) (0, θ) :=
      (hsm.contDiffAt (Spaces.isOpen_U.mem_nhds hmem)).of_le le_top
    rw [Spaces.pz_pth_comm hcd]
    exact hpthpz0 θ hθ
  -- ## The four bounds on `(0,R) × Iθ`
  have hii : ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ, |Spaces.pz f z θ| ≤ M2 * z := by
    intro z hz θ hθ
    have hb := slice_sub_zero_bound (Spaces.pz f) hsm_pz hθ (le_of_lt hz.1)
      (fun u hu => hbnd2 u ⟨hu.1, le_trans hu.2 (le_of_lt hz.2)⟩ θ hθ)
    rw [hpz0 θ hθ, sub_zero] at hb
    rwa [hM2def]
  have hiii : ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.pz (Spaces.pth f) z θ| ≤ M3 * z := by
    intro z hz θ hθ
    have hb := slice_sub_zero_bound (Spaces.pz (Spaces.pth f)) hsm_pzpth hθ (le_of_lt hz.1)
      (fun u hu => hbnd3 u ⟨hu.1, le_trans hu.2 (le_of_lt hz.2)⟩ θ hθ)
    rw [hApz0 θ hθ, sub_zero] at hb
    rwa [hM3def]
  have hi : ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.pth f z θ| ≤ M3 * z ^ 2 / 2 := by
    intro z hz θ hθ
    have hb : |Spaces.pth f z θ| ≤
        Spaces.boxSup R (Spaces.pz (Spaces.pz (Spaces.pth f))) * z ^ 2 / 2 :=
      slice_abs_le_sq_ftc (K := Spaces.boxSup R (Spaces.pz (Spaces.pz (Spaces.pth f))))
        hsm_pth hθ (le_of_lt hz.1) (hpth0 θ hθ) (fun s hs => ?_)
    · rwa [hM3def]
    · rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h, hApz0 θ hθ, abs_zero]
        simp
      · exact hiii s ⟨h, lt_of_le_of_lt hs.2 hz.2⟩ θ hθ
  have hiv : ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.pth (Spaces.pth f) z θ| ≤ M4 :=
    fun z hz θ hθ => hbnd4 z ⟨le_of_lt hz.1, le_of_lt hz.2⟩ θ hθ
  -- ## Assembly
  set C : ℝ := max 1 (max M3 (max M2 M4)) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC3 : M3 ≤ C := by rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hC2 : M2 ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left M2 M4) (le_trans (le_max_right M3 (max M2 M4)) (le_max_right 1 _))
  have hC4 : M4 ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right M2 M4) (le_trans (le_max_right M3 (max M2 M4)) (le_max_right 1 _))
  refine ⟨C, hCpos, ?_⟩
  intro z hz θ hθ
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc |Spaces.pth f z θ| ≤ M3 * z ^ 2 / 2 := hi z hz θ hθ
      _ ≤ M3 * z ^ 2 := by nlinarith [hM3nn, sq_nonneg z]
      _ ≤ C * z ^ 2 := mul_le_mul_of_nonneg_right hC3 (sq_nonneg z)
  · calc |Spaces.pz f z θ| ≤ M2 * z := hii z hz θ hθ
      _ ≤ C * z := mul_le_mul_of_nonneg_right hC2 (le_of_lt hz.1)
  · calc |Spaces.pz (Spaces.pth f) z θ| ≤ M3 * z := hiii z hz θ hθ
      _ ≤ C * z := mul_le_mul_of_nonneg_right hC3 (le_of_lt hz.1)
  · calc |Spaces.pth (Spaces.pth f) z θ| ≤ M4 := hiv z hz θ hθ
      _ ≤ C := hC4

end Work.Coercivity
