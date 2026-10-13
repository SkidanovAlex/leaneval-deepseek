import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.GCompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

set_option maxHeartbeats 1000000

/-- **Differentiability of the `z`-slice.** If `g` is `C²` on the open rectangle
`(-1,∞) × (-1, π/2+1)` then for `(x,θ)` in that rectangle the slice `y ↦ g y θ` is
differentiable at `x`. -/
theorem differentiableAt_slice_z {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    {x θ : ℝ} (hx : -1 < x) (hθ : -1 < θ) (hθ2 : θ < Real.pi / 2 + 1) :
    DifferentiableAt ℝ (fun y => g y θ) x := by
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hmem : (x, θ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    ⟨hx, hθ, hθ2⟩
  have hd : DifferentiableAt ℝ (Function.uncurry g) (x, θ) :=
    (hsm.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hmem)
  have hlin : DifferentiableAt ℝ (fun y : ℝ => (y, θ)) x := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hd.comp x hlin

/-- **Differentiability of the `θ`-slice.** -/
theorem differentiableAt_slice_theta {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    {z x : ℝ} (hz : -1 < z) (hx : -1 < x) (hx2 : x < Real.pi / 2 + 1) :
    DifferentiableAt ℝ (fun s => g z s) x := by
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hmem : (z, x) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    ⟨hz, hx, hx2⟩
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, x) :=
    (hsm.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hmem)
  have hlin : DifferentiableAt ℝ (fun s : ℝ => (z, s)) x := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hd.comp x hlin

/-- **Mean-value inequality in the `z`-direction, uniform in `θ`.**  For `0 ≤ a ≤ b ≤ 2` and
`θ ∈ [0,π/2]`, `|g b θ - g a θ| ≤ K b (b-a)`. -/
theorem slice_z_mvt {g : ℝ → ℝ → ℝ} {K : ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hz : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz g z θ| ≤ K * z)
    (hK : 0 ≤ K) {a b θ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |g b θ - g a θ| ≤ K * b * (b - a) := by
  have hθ1 : -1 < θ := by linarith [hθ.1]
  have hθ2 : θ < Real.pi / 2 + 1 := by linarith [hθ.2]
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun y => g y θ) (Work.Spaces.pz g x θ) (Set.Icc a b) x := by
    intro x hx
    have hx0 : -1 < x := by linarith [ha, hx.1]
    have hd : DifferentiableAt ℝ (fun y => g y θ) x := differentiableAt_slice_z hsm hx0 hθ1 hθ2
    have h1 : HasDerivAt (fun y => g y θ) (deriv (fun y => g y θ) x) x := hd.hasDerivAt
    simpa [Work.Spaces.pz] using h1.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico a b, ‖Work.Spaces.pz g x θ‖ ≤ K * b := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans ha hx.1
    have hx2 : x ≤ 2 := le_trans hx.2.le hb
    have hle : |Work.Spaces.pz g x θ| ≤ K * x := hz x θ hx0 hx2 hθ
    have hxb : x ≤ b := hx.2.le
    rw [Real.norm_eq_abs]
    exact le_trans hle (mul_le_mul_of_nonneg_left hxb hK)
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => g y θ) (f' := fun x => Work.Spaces.pz g x θ)
      (a := a) (b := b) (C := K * b) hderiv hbound
  have hfin := hMVT b ⟨hab, le_rfl⟩
  rwa [Real.norm_eq_abs] at hfin

/-- **Mean-value inequality in the `θ`-direction.**  For `0 ≤ z ≤ 2` and
`θ ≤ θ'` in `[0,π/2]`, `|g z θ' - g z θ| ≤ K z (θ' - θ)`. -/
theorem slice_theta_mvt {g : ℝ → ℝ → ℝ} {K : ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hth : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pth g z θ| ≤ K * z)
    {z θ θ' : ℝ} (hz0 : 0 ≤ z) (hz2 : z ≤ 2)
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) (h : θ ≤ θ') :
    |g z θ' - g z θ| ≤ K * z * (θ' - θ) := by
  have hz1 : -1 < z := by linarith
  have hderiv : ∀ x ∈ Set.Icc θ θ',
      HasDerivWithinAt (fun s => g z s) (Work.Spaces.pth g z x) (Set.Icc θ θ') x := by
    intro x hx
    have hx1 : -1 < x := by linarith [hθ.1, hx.1]
    have hx2 : x < Real.pi / 2 + 1 := by linarith [hθ'.2, hx.2]
    have hd : DifferentiableAt ℝ (fun s => g z s) x :=
      differentiableAt_slice_theta hsm hz1 hx1 hx2
    have h1 : HasDerivAt (fun s => g z s) (deriv (fun s => g z s) x) x := hd.hasDerivAt
    simpa [Work.Spaces.pth] using h1.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico θ θ', ‖Work.Spaces.pth g z x‖ ≤ K * z := by
    intro x hx
    have hxI : x ∈ Work.Spaces.Iθ := ⟨le_trans hθ.1 hx.1, le_trans hx.2.le hθ'.2⟩
    rw [Real.norm_eq_abs]
    exact hth z x hz0 hz2 hxI
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => g z s) (f' := fun x => Work.Spaces.pth g z x)
      (a := θ) (b := θ') (C := K * z) hderiv hbound
  have hfin := hMVT θ' ⟨h, le_rfl⟩
  rwa [Real.norm_eq_abs] at hfin

theorem g_slice_lipschitz {g : ℝ → ℝ → ℝ} {K : ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hz : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz g z θ| ≤ K * z)
    (hth : ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pth g z θ| ≤ K * z) :
    (∀ z z' θ : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 → θ ∈ Work.Spaces.Iθ →
        |g z θ - g z' θ| ≤ K * max z z' * |z - z'|) ∧
      (∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
        |g z θ - g z θ'| ≤ K * z * |θ - θ'|) := by
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hK : 0 ≤ K := by
    have h := hz 1 0 (by norm_num) (by norm_num) h0I
    have hnn := abs_nonneg (Work.Spaces.pz g 1 0)
    linarith
  constructor
  · intro z z' θ hz0 hz2 hz'0 hz'2 hθ
    rcases le_total z z' with hzz | hzz
    · have h := slice_z_mvt hsm hz hK hz0 hzz hz'2 hθ
      rw [max_eq_right hzz, abs_sub_comm, abs_of_nonpos (sub_nonpos.mpr hzz), neg_sub]
      exact h
    · have h := slice_z_mvt hsm hz hK hz'0 hzz hz2 hθ
      rw [max_eq_left hzz, abs_of_nonneg (sub_nonneg.mpr hzz)]
      exact h
  · intro z θ θ' hz0 hz2 hθ hθ'
    rcases le_total θ θ' with h | h
    · have hh := slice_theta_mvt hsm hth hz0 hz2 hθ hθ' h
      rw [abs_sub_comm, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
      exact hh
    · have hh := slice_theta_mvt hsm hth hz0 hz2 hθ' hθ h
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      exact hh

end Work.ConstructionInstance
