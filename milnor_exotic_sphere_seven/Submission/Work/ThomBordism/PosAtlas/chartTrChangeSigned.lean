import Mathlib
import Submission.Work.ThomBordism.PosAtlas.eucFam_linear_action
import Submission.Work.ThomBordism.PosAtlas.chartTr_transHomeomorph
import Submission.Work.ThomBordism.PosAtlas.Defs
import Submission.Work.ThomBordism.PosAtlas.reflLin_det
import Submission.Work.PTGeometric.HOFChart
import Submission.Work.Thom.Orientation.Reflection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The signed chart-transfer change of the Euclidean local generator

For two `ℝ⁹`-charts `e`, `f` of a `T₁` space `W` at a common point `w`, whose transition
`f ∘ e.symm` is differentiable at `e w` with invertible derivative `A`, the chart transfers of the
Euclidean local generator differ by the orientation character `sign (det A)`:

  `chartTr e w (eucFam 9 (e w)) = (if 0 < det A then 1 else -1) • chartTr f w (eucFam 9 (f w))`.

The positive-determinant case is `Work.PTGeometric.HOF.chartTr_change`.  The negative case is
obtained by post-composing one of the charts with the reflection `flipH` of the model (negating the
first coordinate, `det = -1`): the transfer of the reflected chart is the *negative* of the transfer
of the original one (`chartTr_flip`, from `chartTr_transHomeomorph` and `eucFam_linear_action`),
while the transition of the reflected chart to the other one has positive determinant
(`q ↦ flip (f (e.symm q))` has derivative `flip ∘ A`, and `(-1)(-1) = 1`), so
`Work.PTGeometric.HOF.chartTr_change` applies to it.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.ThomBordism.PosAtlas

noncomputable section

open Work.Thom.Orientation
open Work.PTGeometric.HOF
open CategoryTheory

/-! ## The reflection as a topological homeomorphism of the model -/

/-- **The reflection of the model `ℝ⁹` negating the coordinate `0`**, as a homeomorphism.  It is
its own inverse. -/
def flipH : E9 ≃ₜ E9 where
  toFun := flipFst 9
  invFun := flipFst 9
  left_inv := flipFst_involutive 9
  right_inv := flipFst_involutive 9
  continuous_toFun := (flipFst 9).continuous
  continuous_invFun := (flipFst 9).continuous

/-- The reflection as a morphism of `TopCat`. -/
abbrev flipM : TopCat.of E9 ⟶ TopCat.of E9 :=
  TopCat.ofHom ⟨fun z => flipFst 9 z, (flipFst 9).continuous⟩

theorem flipH_apply (z : E9) : flipH z = flipFst 9 z := rfl

theorem flipH_symm_apply (z : E9) : flipH.symm z = flipFst 9 z := rfl

theorem flipM_apply (z : E9) : flipM z = flipFst 9 z := rfl

theorem flipFst_bijective : Function.Bijective (flipFst 9) :=
  ⟨flipFst_injective 9, fun y => ⟨flipFst 9 y, flipFst_involutive 9 y⟩⟩

theorem flipM_comp_self : flipM ≫ flipM = 𝟙 (TopCat.of E9) := by
  apply TopCat.ext
  intro z
  show flipFst 9 (flipFst 9 z) = z
  rw [flipFst_involutive]

/-! ## The inverse action of the reflection on the local generator

`eucFam_linear_action` computes the action of the reflection in the *forward* direction; functoriality
of `RelHmapOf` (with `flipM ≫ flipM = 𝟙`) converts it into the inverse direction, which is the form
needed by `chartTr_transHomeomorph`. -/

theorem flipPair₁ (a : E9) :
    ∀ z : E9, z ∉ ({a} : Set E9) → flipM z ∉ ({flipFst 9 a} : Set E9) := by
  intro z hz
  simp only [Set.mem_singleton_iff] at hz ⊢
  intro h
  change flipFst 9 z = flipFst 9 a at h
  exact hz (flipFst_injective 9 h)

theorem flipPair₂ (a : E9) :
    ∀ z : E9, z ∉ ({flipFst 9 a} : Set E9) → flipM z ∉ ({a} : Set E9) := by
  intro z hz h
  simp only [Set.mem_singleton_iff] at hz h
  refine hz ?_
  change flipFst 9 z = a at h
  have h3 := congrArg (flipFst 9) h
  rwa [flipFst_involutive] at h3

theorem flipPair₃ (a : E9) :
    ∀ z : E9, z ∉ ({a} : Set E9) → (flipM ≫ flipM) z ∉ ({a} : Set E9) := by
  intro z hz
  have h : (flipM ≫ flipM) z = z := by
    change flipFst 9 (flipFst 9 z) = z
    rw [flipFst_involutive]
  rw [h]
  exact hz

/-- **The inverse action of the reflection on the local generator**: it is multiplication by `-1`. -/
theorem eucFam_flipM_inv (a : E9) :
    RelHmapOf 9 flipM ({flipFst 9 a} : Set E9) ({a} : Set E9) (flipPair₂ a)
      (eucFam 9 (by norm_num) (flipFst 9 a)) = - eucFam 9 (by norm_num) a := by
  have hlin := eucFam_linear_action (flipFst 9) flipFst_bijective a
  have hsign : (if 0 < LinearMap.det (flipFst 9).toLinearMap then (1 : ℤ) else -1) = -1 := by
    rw [if_neg (not_lt.mpr (le_of_lt (flipFst_det 9 (by norm_num))))]
  rw [hsign, neg_one_zsmul] at hlin
  have hfwd : RelHmapOf 9 flipM ({a} : Set E9) ({flipFst 9 a} : Set E9) (flipPair₁ a)
      (eucFam 9 (by norm_num) a) = - eucFam 9 (by norm_num) (flipFst 9 a) := hlin
  have hcomp := RelHmapOf_comp (n := 9) (f := flipM) (g := flipM)
    (K := ({a} : Set E9)) (K' := ({flipFst 9 a} : Set E9)) (K'' := ({a} : Set E9))
    (flipPair₁ a) (flipPair₂ a) (flipPair₃ a)
  have hid0 := RelHmapOf_congr (n := 9) (X := TopCat.of E9) (Y := TopCat.of E9)
    (K := ({a} : Set E9)) (K' := ({a} : Set E9))
    flipM_comp_self (flipPair₃ a) (fun x hx => hx)
  have hid1 : RelHmapOf 9 (𝟙 (TopCat.of E9)) ({a} : Set E9) ({a} : Set E9) (fun x hx => hx)
      = LinearMap.id := RelHmapOf_id (n := 9) (X := TopCat.of E9) (K := ({a} : Set E9))
  have hid : RelHmapOf 9 (flipM ≫ flipM) ({a} : Set E9) ({a} : Set E9) (flipPair₃ a)
      = LinearMap.id := hid0.trans hid1
  have key : (RelHmapOf 9 flipM ({flipFst 9 a} : Set E9) ({a} : Set E9) (flipPair₂ a))
      ((RelHmapOf 9 flipM ({a} : Set E9) ({flipFst 9 a} : Set E9) (flipPair₁ a))
        (eucFam 9 (by norm_num) a)) = eucFam 9 (by norm_num) a := by
    have h1 := LinearMap.congr_fun hcomp (eucFam 9 (by norm_num) a)
    rw [LinearMap.comp_apply] at h1
    rw [h1, hid, LinearMap.id_apply]
  have key2 : - (RelHmapOf 9 flipM ({flipFst 9 a} : Set E9) ({a} : Set E9) (flipPair₂ a))
      (eucFam 9 (by norm_num) (flipFst 9 a)) = eucFam 9 (by norm_num) a := by
    rw [← key, hfwd, map_neg]
  exact neg_eq_iff_eq_neg.mp key2

/-! ## The transfer of a reflected chart -/

/-- **The chart transfer of a reflected chart is the negative of the transfer of the chart**:  the
reflection of the model reverses the orientation. -/
theorem chartTr_flip {W : TopCat} [T1Space W]
    (e : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin 9))) (w : W) (he : w ∈ e.source) :
    Work.PTGeometric.HOF.chartTr (e.transHomeomorph flipH) w he
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (flipH (e w)))
      = - Work.PTGeometric.HOF.chartTr e w he
            (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (e w)) := by
  have hinner : RelHmapOf 9 (TopCat.ofHom ⟨fun z => flipH.symm z, flipH.continuous_invFun⟩)
      ({flipH (e w)} : Set (EuclideanSpace ℝ (Fin 9))) ({e w} : Set (EuclideanSpace ℝ (Fin 9)))
      (fun z hz => by
        simp only [Set.mem_singleton_iff] at hz ⊢
        intro hh
        exact hz (by rw [← hh]; exact (flipH.apply_symm_apply z).symm))
      (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (flipH (e w)))
      = - Work.PTGeometric.HOF.eucFam 9 (by norm_num) (e w) :=
    eucFam_flipM_inv (e w)
  rw [Work.ThomBordism.PosAtlas.chartTr_transHomeomorph e flipH w he
    (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (flipH (e w))), hinner, map_neg]

/-! ## The main statement -/

theorem chartTrChangeSigned {W : TopCat} [T1Space W]
    (e f : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin 9))) (w : W)
    (he : w ∈ e.source) (hf : w ∈ f.source)
    (A : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 9))
    (hA : Function.Bijective A)
    (hd : HasFDerivAt (fun z => f (e.symm z)) A (e w)) :
    Work.PTGeometric.HOF.chartTr e w he
        (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (e w))
      = (if 0 < LinearMap.det A.toLinearMap then (1 : ℤ) else -1)
        • Work.PTGeometric.HOF.chartTr f w hf
            (Work.PTGeometric.HOF.eucFam 9 (by norm_num) (f w)) := by
  by_cases hdet : 0 < LinearMap.det A.toLinearMap
  · rw [if_pos hdet, one_smul]
    exact Work.PTGeometric.HOF.chartTr_change 9 (by norm_num) e f w he hf A hd hdet
  · rw [if_neg hdet, neg_one_zsmul]
    -- the bijectivity makes the determinant nonzero, hence negative here
    have hAne : LinearMap.det A.toLinearMap ≠ 0 := by
      intro h0
      have hker : A.toLinearMap.ker ≠ ⊥ := (LinearMap.det_eq_zero_iff_ker_ne_bot).mp h0
      apply hker
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hx' : A x = 0 := hx
      exact hA.1 (by rw [hx', map_zero])
    have hAneg : LinearMap.det A.toLinearMap < 0 :=
      lt_of_le_of_ne (le_of_not_gt hdet) hAne
    have hFneg : LinearMap.det (flipFst 9).toLinearMap < 0 := flipFst_det 9 (by norm_num)
    have hdet' : 0 < LinearMap.det ((flipFst 9).comp A).toLinearMap := by
      rw [show ((flipFst 9).comp A).toLinearMap = (flipFst 9).toLinearMap.comp A.toLinearMap
        from rfl, LinearMap.det_comp]
      exact mul_pos_of_neg_of_neg hFneg hAneg
    -- the transition of the reflected chart is `flip ∘ (f ∘ e.symm)`, of derivative `flip ∘ A`
    have hd' : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin 9) => (f.transHomeomorph flipH) (e.symm z))
        ((flipFst 9).comp A) (e w) := by
      have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 9) => flipFst 9 y) (flipFst 9)
          (f (e.symm (e w))) := (flipFst 9).hasFDerivAt
      have h2 := h1.comp (e w) hd
      change HasFDerivAt ((fun y : EuclideanSpace ℝ (Fin 9) => flipFst 9 y) ∘
        fun z => f (e.symm z)) ((flipFst 9).comp A) (e w)
      exact h2
    have h1 := Work.PTGeometric.HOF.chartTr_change 9 (by norm_num) e (f.transHomeomorph flipH)
      w he hf ((flipFst 9).comp A) hd' hdet'
    have h2 := chartTr_flip f w hf
    exact h1.trans h2

end

end Work.ThomBordism.PosAtlas
