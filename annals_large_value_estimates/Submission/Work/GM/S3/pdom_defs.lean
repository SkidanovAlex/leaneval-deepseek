import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop71_main

/-!
# The true `v`-domain of GM Prop 7.1

`Work.GM.S3.pbox = [1/2,2]²` is the region where the `u₃`-weight
`w2v v u = u² w(u)² w(v₁u)² w(v₂u)²` can be non-zero.  But that weight also forces
`v₂/v₁ = (v₂u)/(v₁u) ∈ [1/2,2]` whenever it is non-zero (both `v₁u` and `v₂u` must lie in
`[1,2]`).  Hence the inner integral `innerInt N m v` vanishes unless
`v ∈ pdom := pbox ∩ {v | v₂/v₁ ∈ [1/2,2]}`; this file collects the corresponding support
lemmas.
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun Separated Iterm hhat hfun)

/-- The true `v`-domain of GM Prop 7.1: `v ∈ [1/2,2]²` **and** `v₂/v₁ ∈ [1/2,2]`.  The corner
"triangles" of `pbox` (where `v₂/v₁ ∉ [1/2,2]`) carry zero `u₃`-weight. -/
def pdom : Set (ℝ × ℝ) :=
  pbox ∩ {v : ℝ × ℝ | v.2 / v.1 ∈ Set.Icc (1 / 2 : ℝ) 2}

private theorem volume_prod_eq :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.volume.prod MeasureTheory.volume := rfl

theorem pdom_subset_pbox : pdom ⊆ pbox := Set.inter_subset_left

theorem measurableSet_pdom : MeasurableSet pdom := by
  rw [pdom]
  refine measurableSet_pbox.inter ?_
  have h : Measurable (fun v : ℝ × ℝ => v.2 / v.1) := by fun_prop
  exact measurableSet_Icc.preimage h

/-- For `a, b ∈ [1,2]`, the quotient `a/b` lies in `[1/2,2]`. -/
theorem div_mem_Icc_half_two {a b : ℝ} (ha : a ∈ Set.Icc (1 : ℝ) 2)
    (hb : b ∈ Set.Icc (1 : ℝ) 2) : a / b ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hbpos : 0 < b := by linarith
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hbpos]; linarith
  · rw [div_le_iff₀ hbpos]; linarith

/-- If `w₂(·,v)` is non-zero at `u` then `v₁u, v₂u, u ∈ [1,2]`; since `v₂/v₁ = (v₂u)/(v₁u)`,
this forces `v₂/v₁ ∈ [1/2,2]`.  Hence `w₂(·,v)` vanishes identically when `v₂/v₁ ∉ [1/2,2]`. -/
theorem w2v_eq_zero_of_ratio_not_mem {v : ℝ × ℝ}
    (hv : v.2 / v.1 ∉ Set.Icc (1 / 2 : ℝ) 2) (u : ℝ) : w2v v u = 0 := by
  by_contra h
  rw [w2v] at h
  obtain ⟨h12, h4⟩ := mul_ne_zero_iff.mp h
  obtain ⟨h123, h3⟩ := mul_ne_zero_iff.mp h12
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h123
  have hu : u ≠ 0 := by
    rintro rfl
    exact h1 (by simp)
  have h1I : v.1 * u ∈ Set.Icc (1 : ℝ) 2 := mem_Icc_of_w2C_ne_zero h3
  have h2I : v.2 * u ∈ Set.Icc (1 : ℝ) 2 := mem_Icc_of_w2C_ne_zero h4
  have hr : (v.2 * u) / (v.1 * u) = v.2 / v.1 := mul_div_mul_right v.2 v.1 hu
  exact hv (hr ▸ div_mem_Icc_half_two h2I h1I)

/-- Strengthened support of the inner integral: it vanishes off `pdom`. -/
theorem innerInt_eq_zero_of_not_mem_pdom {N : ℕ} {m : ℤ × ℤ × ℤ} {v : ℝ × ℝ}
    (hv : v ∉ pdom) : innerInt N m v = 0 := by
  rw [pdom, Set.mem_inter_iff, not_and_or] at hv
  rcases hv with hv | hv
  · exact prop71_inner_support N m v hv
  · unfold innerInt
    have hzero : (fun u : ℝ =>
        Complex.exp (-(2 * Real.pi * Complex.I * ((N : ℝ) * phas m v) * u)) * w2v v u)
        = fun _ => (0 : ℂ) := by
      funext u
      rw [w2v_eq_zero_of_ratio_not_mem hv u, mul_zero]
    rw [hzero]
    simp

/-- `vol(pdom) ≥ 1`: `pdom` contains the unit square `[1,2] × [1,2]`. -/
theorem pdom_volume_ge_one :
    1 ≤ ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pdom).toReal := by
  have hsub : Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (1 : ℝ) 2 ⊆ pdom := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    refine ⟨⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
      ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩, div_mem_Icc_half_two hy hx⟩
  have hvol : ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      (Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (1 : ℝ) 2)).toReal = 1 := by
    rw [volume_prod_eq, MeasureTheory.Measure.prod_prod, Real.volume_Icc, ENNReal.toReal_mul]
    norm_num
  have hle : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pdom ≤
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pbox :=
    MeasureTheory.measure_mono pdom_subset_pbox
  have hne : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pdom ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hle prop71_box_isCompact_pbox.measure_lt_top)
  calc (1 : ℝ) = _ := hvol.symm
    _ ≤ ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pdom).toReal :=
        ENNReal.toReal_mono hne (MeasureTheory.measure_mono hsub)

end Work.GM.S3
