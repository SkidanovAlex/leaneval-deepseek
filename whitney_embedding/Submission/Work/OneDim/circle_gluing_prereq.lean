import Mathlib
import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.CirclePt
import Submission.Work.OneDim.CirclePtFacts
import Submission.Work.OneDim.SeamTools

/-!
# Prerequisites for the gluing of `ℝ` into a circle

This file collects the three analytic/topological ingredients used in
`Work.OneDim.circle_gluing`:

* `Work.OneDim.spherePt_stereographic`: the stereographic parametrisations `spherePt`, `spherePt'`
  of the circle are injective, local diffeomorphisms, cover the circle minus one point, and are
  related by `spherePt (1/t) = spherePt' t`;
* `Work.OneDim.exists_diffeomorph_tails`: two parametrisations of the two ends of `ℝ` can be glued
  into a single diffeomorphism of `ℝ`;
* `Work.OneDim.seam_chart_data`: the seam data extracted from an injective local diffeomorphism
  `φ : ℝ → C` onto the complement of a point.
-/

open scoped Manifold ContDiff
open Topology Set Function Filter

namespace Work.OneDim

noncomputable section

/-! ## The stereographic parametrisations of the circle -/

theorem spherePt'_ne_Q (t : ℝ) : spherePt' t ≠ Q := by
  intro h
  have h2 : ((spherePt' t : Circle) : ℂ) = 1 := by rw [h, Q_coe]
  rw [spherePt'_coe] at h2
  have him : (2 * t) / (1 + t ^ 2) = 0 := by
    have h := congrArg Complex.im h2
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add, Complex.one_im] using h
  have hre : (t ^ 2 - 1) / (1 + t ^ 2) = 1 := by
    have h := congrArg Complex.re h2
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, sub_zero, Complex.one_re] using h
  have hpos : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have ht : t = 0 := by
    have h1 : 2 * t = 0 := by
      rw [div_eq_zero_iff] at him
      rcases him with h | h
      · exact h
      · exact absurd h hpos
    linarith
  rw [ht] at hre
  norm_num at hre

theorem spherePt_sphereCoord (z : Circle) (hz : z ≠ Qm) :
    spherePt (sphereCoord (z : ℂ)) = z := by
  have hz' : (z : ℂ) ≠ -1 := fun h => hz (Subtype.ext (by rw [h, Qm_coe]))
  have h1a : 1 + (z : ℂ).re ≠ 0 := circle_one_add_re_ne_zero z hz'
  have hsq : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := circle_re_sq_add_im_sq z
  refine circle_ext' ?_ ?_
  · rw [spherePt_coe, sphereCoord]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    field_simp
    nlinarith [hsq]
  · rw [spherePt_coe, sphereCoord]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
    field_simp
    linear_combination (-(z : ℂ).im) * hsq

theorem spherePt'_sphereCoord' (z : Circle) (hz : z ≠ Q) :
    spherePt' (sphereCoord' (z : ℂ)) = z := by
  have hz' : (z : ℂ) ≠ 1 := fun h => hz (Subtype.ext (by rw [h, Q_coe]))
  have h1a : 1 - (z : ℂ).re ≠ 0 := circle_one_sub_re_ne_zero z hz'
  have hsq : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := circle_re_sq_add_im_sq z
  refine circle_ext' ?_ ?_
  · rw [spherePt'_coe, sphereCoord']
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    field_simp
    nlinarith [hsq]
  · rw [spherePt'_coe, sphereCoord']
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
    field_simp
    linear_combination (-(z : ℂ).im) * hsq

theorem spherePt'_injective : Function.Injective spherePt' := by
  intro a b h
  have := congrArg (fun z : Circle => sphereCoord' (z : ℂ)) h
  rwa [sphereCoord'_spherePt', sphereCoord'_spherePt'] at this

theorem range_spherePt : Set.range spherePt = ({Qm} : Set Circle)ᶜ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simpa using spherePt_ne_Qm t
  · intro hz
    exact ⟨sphereCoord (z : ℂ), spherePt_sphereCoord z (by simpa using hz)⟩

theorem range_spherePt' : Set.range spherePt' = ({Q} : Set Circle)ᶜ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simpa using spherePt'_ne_Q t
  · intro hz
    exact ⟨sphereCoord' (z : ℂ), spherePt'_sphereCoord' z (by simpa using hz)⟩

theorem contMDiff_spherePt : ContMDiff (modelWithCornersSelf ℝ ℝ) I1 sm spherePt := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have hnum : ContDiff ℝ sm (fun t : ℝ => (1 - t ^ 2 : ℝ) / (1 + t ^ 2)) :=
    ContDiff.div (by fun_prop) (by fun_prop) (fun t => by positivity)
  have hnum2 : ContDiff ℝ sm (fun t : ℝ => (2 * t : ℝ) / (1 + t ^ 2)) :=
    ContDiff.div (by fun_prop) (by fun_prop) (fun t => by positivity)
  have hI : ContDiff ℝ sm (fun _ : ℝ => Complex.I) := contDiff_const
  have hlift : ContDiff ℝ sm (fun t : ℝ => (((1 - t ^ 2 : ℝ) / (1 + t ^ 2 : ℝ) : ℝ) : ℂ)
      + (((2 * t : ℝ) / (1 + t ^ 2 : ℝ) : ℝ) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp hnum).add
      ((Complex.ofRealCLM.contDiff.comp hnum2).mul hI)
  have heq : (fun t : ℝ => ((spherePt t : Circle) : ℂ)) = fun t : ℝ =>
      (((1 - t ^ 2 : ℝ) / (1 + t ^ 2 : ℝ) : ℝ) : ℂ)
        + (((2 * t : ℝ) / (1 + t ^ 2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    funext t
    rw [spherePt_coe]
  have htot : ContDiff ℝ sm (fun t : ℝ => ((spherePt t : Circle) : ℂ)) := by
    rw [heq]; exact hlift
  have hmem : ∀ t : ℝ, ((spherePt t : Circle) : ℂ) ∈ Metric.sphere (0 : ℂ) 1 :=
    fun t => (spherePt t).2
  have hcod : ContMDiff (modelWithCornersSelf ℝ ℝ) I1 sm
      (Set.codRestrict (fun t : ℝ => ((spherePt t : Circle) : ℂ)) (Metric.sphere (0 : ℂ) 1)
        hmem) :=
    htot.contMDiff.codRestrict_sphere hmem
  have hfun : (Set.codRestrict (fun t : ℝ => ((spherePt t : Circle) : ℂ))
      (Metric.sphere (0 : ℂ) 1) hmem) = spherePt := by
    funext t
    exact Subtype.ext rfl
  rwa [hfun] at hcod

theorem contMDiff_spherePt' : ContMDiff (modelWithCornersSelf ℝ ℝ) I1 sm spherePt' := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have hnum : ContDiff ℝ sm (fun t : ℝ => (t ^ 2 - 1 : ℝ) / (1 + t ^ 2)) :=
    ContDiff.div (by fun_prop) (by fun_prop) (fun t => by positivity)
  have hnum2 : ContDiff ℝ sm (fun t : ℝ => (2 * t : ℝ) / (1 + t ^ 2)) :=
    ContDiff.div (by fun_prop) (by fun_prop) (fun t => by positivity)
  have hI : ContDiff ℝ sm (fun _ : ℝ => Complex.I) := contDiff_const
  have hlift : ContDiff ℝ sm (fun t : ℝ => (((t ^ 2 - 1 : ℝ) / (1 + t ^ 2 : ℝ) : ℝ) : ℂ)
      + (((2 * t : ℝ) / (1 + t ^ 2 : ℝ) : ℝ) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp hnum).add
      ((Complex.ofRealCLM.contDiff.comp hnum2).mul hI)
  have heq : (fun t : ℝ => ((spherePt' t : Circle) : ℂ)) = fun t : ℝ =>
      (((t ^ 2 - 1 : ℝ) / (1 + t ^ 2 : ℝ) : ℝ) : ℂ)
        + (((2 * t : ℝ) / (1 + t ^ 2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    funext t
    rw [spherePt'_coe]
  have htot : ContDiff ℝ sm (fun t : ℝ => ((spherePt' t : Circle) : ℂ)) := by
    rw [heq]; exact hlift
  have hmem : ∀ t : ℝ, ((spherePt' t : Circle) : ℂ) ∈ Metric.sphere (0 : ℂ) 1 :=
    fun t => (spherePt' t).2
  have hcod : ContMDiff (modelWithCornersSelf ℝ ℝ) I1 sm
      (Set.codRestrict (fun t : ℝ => ((spherePt' t : Circle) : ℂ)) (Metric.sphere (0 : ℂ) 1)
        hmem) :=
    htot.contMDiff.codRestrict_sphere hmem
  have hfun : (Set.codRestrict (fun t : ℝ => ((spherePt' t : Circle) : ℂ))
      (Metric.sphere (0 : ℂ) 1) hmem) = spherePt' := by
    funext t
    exact Subtype.ext rfl
  rwa [hfun] at hcod

theorem contMDiffOn_sphereCoord :
    ContMDiffOn I1 (modelWithCornersSelf ℝ ℝ) sm (fun z : Circle => sphereCoord (z : ℂ))
      ({Qm} : Set Circle)ᶜ := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have hcoe : ContMDiffOn I1 (modelWithCornersSelf ℝ ℂ) sm (fun z : Circle => (z : ℂ))
      ({Qm} : Set Circle)ᶜ := contMDiff_coe_sphere.contMDiffOn
  have him : ContMDiffOn I1 (modelWithCornersSelf ℝ ℝ) sm
      (fun z : Circle => ((z : ℂ)).im) ({Qm} : Set Circle)ᶜ :=
    Complex.imCLM.contMDiff.comp_contMDiffOn hcoe
  have hden : ContMDiffOn I1 (modelWithCornersSelf ℝ ℝ) sm
      (fun z : Circle => 1 + ((z : ℂ)).re) ({Qm} : Set Circle)ᶜ :=
    contMDiffOn_const.add (Complex.reCLM.contMDiff.comp_contMDiffOn hcoe)
  have hne : ∀ z ∈ ({Qm} : Set Circle)ᶜ, 1 + ((z : ℂ)).re ≠ 0 := fun z hz =>
    circle_one_add_re_ne_zero z (fun h => hz (Subtype.ext (by rw [h, Qm_coe])))
  have h : ContMDiffOn I1 (modelWithCornersSelf ℝ ℝ) sm
      (fun z : Circle => ((z : ℂ).im) / (1 + (z : ℂ).re)) ({Qm} : Set Circle)ᶜ :=
    him.div₀ hden hne
  simpa only [sphereCoord] using h

theorem contMDiffOn_sphereCoord' :
    ContMDiffOn I1 (modelWithCornersSelf ℝ ℝ) sm (fun z : Circle => sphereCoord' (z : ℂ))
      ({Q} : Set Circle)ᶜ := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  have hcoe : ContMDiffOn I1 (modelWithCornersSelf ℝ ℂ) sm (fun z : Circle => (z : ℂ))
      ({Q} : Set Circle)ᶜ := contMDiff_coe_sphere.contMDiffOn
  have him : ContMDiffOn I1 (modelWithCornersSelf ℝ ℝ) sm
      (fun z : Circle => ((z : ℂ)).im) ({Q} : Set Circle)ᶜ :=
    Complex.imCLM.contMDiff.comp_contMDiffOn hcoe
  have hden : ContMDiffOn I1 (modelWithCornersSelf ℝ ℝ) sm
      (fun z : Circle => 1 - ((z : ℂ)).re) ({Q} : Set Circle)ᶜ :=
    contMDiffOn_const.sub (Complex.reCLM.contMDiff.comp_contMDiffOn hcoe)
  have hne : ∀ z ∈ ({Q} : Set Circle)ᶜ, 1 - ((z : ℂ).re) ≠ 0 := fun z hz =>
    circle_one_sub_re_ne_zero z (fun h => hz (Subtype.ext (by rw [h, Q_coe])))
  have h : ContMDiffOn I1 (modelWithCornersSelf ℝ ℝ) sm
      (fun z : Circle => ((z : ℂ).im) / (1 - (z : ℂ).re)) ({Q} : Set Circle)ᶜ :=
    him.div₀ hden hne
  simpa only [sphereCoord'] using h

/-- The circle parametrised stereographically by `ℝ`: a partial diffeomorphism from `ℝ` onto
the circle minus the point `Qm`. -/
def spherePtPD : PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 ℝ Circle sm where
  toPartialEquiv :=
    { toFun := spherePt
      invFun := fun z : Circle => sphereCoord (z : ℂ)
      source := Set.univ
      target := ({Qm} : Set Circle)ᶜ
      map_source' := fun t _ => spherePt_ne_Qm t
      map_target' := fun z _ => Set.mem_univ _
      left_inv' := fun t _ => sphereCoord_spherePt t
      right_inv' := fun z hz => spherePt_sphereCoord z (by simpa using hz) }
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton (x := Qm)
  contMDiffOn_toFun := contMDiff_spherePt.contMDiffOn
  contMDiffOn_invFun := contMDiffOn_sphereCoord

/-- The circle parametrised stereographically by `ℝ`, with the other pole. -/
def spherePtPD' : PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 ℝ Circle sm where
  toPartialEquiv :=
    { toFun := spherePt'
      invFun := fun z : Circle => sphereCoord' (z : ℂ)
      source := Set.univ
      target := ({Q} : Set Circle)ᶜ
      map_source' := fun t _ => spherePt'_ne_Q t
      map_target' := fun z _ => Set.mem_univ _
      left_inv' := fun t _ => sphereCoord'_spherePt' t
      right_inv' := fun z hz => spherePt'_sphereCoord' z (by simpa using hz) }
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton (x := Q)
  contMDiffOn_toFun := contMDiff_spherePt'.contMDiffOn
  contMDiffOn_invFun := contMDiffOn_sphereCoord'

@[simp] theorem spherePtPD_source : spherePtPD.source = Set.univ := rfl
@[simp] theorem spherePtPD_apply (t : ℝ) : spherePtPD t = spherePt t := rfl
@[simp] theorem spherePtPD'_source : spherePtPD'.source = Set.univ := rfl
@[simp] theorem spherePtPD'_apply (t : ℝ) : spherePtPD' t = spherePt' t := rfl

theorem isLocalDiffeomorph_spherePt :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm spherePt := by
  intro t
  refine ⟨spherePtPD, by simp, ?_⟩
  intro y _
  simp

theorem isLocalDiffeomorph_spherePt' :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm spherePt' := by
  intro t
  refine ⟨spherePtPD', by simp, ?_⟩
  intro y _
  simp

theorem spherePt_stereographic :
    Function.Injective spherePt ∧ Function.Injective spherePt' ∧
    (∀ t : ℝ, t ≠ 0 → spherePt (1 / t) = spherePt' t) ∧
    Set.range spherePt = ({Qm} : Set Circle)ᶜ ∧
    Set.range spherePt' = ({Q} : Set Circle)ᶜ ∧
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm spherePt ∧
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm spherePt' :=
  ⟨spherePt_injective, spherePt'_injective, fun t ht => (spherePt'_eq_spherePt_inv t ht).symm,
    range_spherePt, range_spherePt', isLocalDiffeomorph_spherePt, isLocalDiffeomorph_spherePt'⟩

end

end Work.OneDim
