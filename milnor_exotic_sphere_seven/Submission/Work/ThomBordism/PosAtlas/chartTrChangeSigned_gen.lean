/-
# The signed chart-transfer change of the Euclidean local generator (general dimension)

For two `ℝⁿ`-charts `e`, `f` of a `T₁` space `W` at a common point `w` (`n ≥ 1`), whose transition
`f ∘ e.symm` is differentiable at `e w` with invertible derivative `A`, the chart transfers of the
Euclidean local generator differ by the orientation character `sign (det A)`:

  `chartTr e w (eucFam n hn (e w)) = (if 0 < det A then 1 else -1) • chartTr f w (eucFam n hn (f w))`.

The positive-determinant case is `Work.PTGeometric.HOF.chartTr_change`.  The negative case is
obtained by post-composing one of the charts with the reflection `flipHn n` of the model (negating
the first coordinate, `det = -1`): the transfer of the reflected chart is the *negative* of the
transfer of the original one (`chartTr_flip_gen`, from `chartTr_transHomeomorph` and
`eucFam_linear_action_gen`), while the transition of the reflected chart to the other one has
positive determinant (`q ↦ flip (f (e.symm q))` has derivative `flip ∘ A`, and `(-1)(-1) = 1`), so
`Work.PTGeometric.HOF.chartTr_change` applies to it.

This is the general-`n` version of `Work.ThomBordism.PosAtlas.chartTrChangeSigned` (the case
`n = 9`); the helpers below are named with the suffix `_gen`/`…n` to avoid clashing with the
`n = 9` file, which lives in the same namespace.
-/
import Mathlib
import Submission.Work.ThomBordism.PosAtlas.eucFam_linear_action_gen
import Submission.Work.ThomBordism.PosAtlas.chartTr_transHomeomorph
import Submission.Work.PTGeometric.HOFChart
import Submission.Work.Thom.Orientation.Reflection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.ThomBordism.PosAtlas

noncomputable section

open Work.Thom.Orientation
open Work.PTGeometric.HOF
open CategoryTheory

/-! ## The reflection of the model `ℝⁿ` -/

/-- **The reflection of the model `ℝⁿ` negating the coordinate `0`**, as a homeomorphism.  It is
its own inverse. -/
def flipHn (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) where
  toFun := flipFst n
  invFun := flipFst n
  left_inv := flipFst_involutive n
  right_inv := flipFst_involutive n
  continuous_toFun := (flipFst n).continuous
  continuous_invFun := (flipFst n).continuous

/-- The reflection as a morphism of `TopCat`. -/
abbrev flipMn (n : ℕ) :
    TopCat.of (EuclideanSpace ℝ (Fin n)) ⟶ TopCat.of (EuclideanSpace ℝ (Fin n)) :=
  TopCat.ofHom ⟨fun z => flipFst n z, (flipFst n).continuous⟩

theorem flipHn_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : flipHn n z = flipFst n z := rfl

theorem flipHn_symm_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    (flipHn n).symm z = flipFst n z := rfl

theorem flipMn_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : flipMn n z = flipFst n z := rfl

theorem flipFst_bijective_gen (n : ℕ) : Function.Bijective (flipFst n) :=
  ⟨flipFst_injective n, fun y => ⟨flipFst n y, flipFst_involutive n y⟩⟩

theorem flipMn_comp_self (n : ℕ) :
    flipMn n ≫ flipMn n = 𝟙 (TopCat.of (EuclideanSpace ℝ (Fin n))) := by
  apply TopCat.ext
  intro z
  show flipFst n (flipFst n z) = z
  rw [flipFst_involutive]

/-! ## The inverse action of the reflection on the local generator

`eucFam_linear_action_gen` computes the action of the reflection in the *forward* direction;
functoriality of `RelHmapOf` (with `flipMn n ≫ flipMn n = 𝟙`) converts it into the inverse
direction, which is the form needed by `chartTr_transHomeomorph`. -/

theorem flipPair₁_gen (n : ℕ) (a : EuclideanSpace ℝ (Fin n)) :
    ∀ z : EuclideanSpace ℝ (Fin n), z ∉ ({a} : Set (EuclideanSpace ℝ (Fin n))) →
      flipMn n z ∉ ({flipFst n a} : Set (EuclideanSpace ℝ (Fin n))) := by
  intro z hz
  simp only [Set.mem_singleton_iff] at hz ⊢
  intro h
  change flipFst n z = flipFst n a at h
  exact hz (flipFst_injective n h)

theorem flipPair₂_gen (n : ℕ) (a : EuclideanSpace ℝ (Fin n)) :
    ∀ z : EuclideanSpace ℝ (Fin n), z ∉ ({flipFst n a} : Set (EuclideanSpace ℝ (Fin n))) →
      flipMn n z ∉ ({a} : Set (EuclideanSpace ℝ (Fin n))) := by
  intro z hz h
  simp only [Set.mem_singleton_iff] at hz h
  refine hz ?_
  change flipFst n z = a at h
  have h3 := congrArg (flipFst n) h
  rwa [flipFst_involutive] at h3

theorem flipPair₃_gen (n : ℕ) (a : EuclideanSpace ℝ (Fin n)) :
    ∀ z : EuclideanSpace ℝ (Fin n), z ∉ ({a} : Set (EuclideanSpace ℝ (Fin n))) →
      (flipMn n ≫ flipMn n) z ∉ ({a} : Set (EuclideanSpace ℝ (Fin n))) := by
  intro z hz
  have h : (flipMn n ≫ flipMn n) z = z := by
    change flipFst n (flipFst n z) = z
    rw [flipFst_involutive]
  rw [h]
  exact hz

/-- **The inverse action of the reflection on the local generator**: it is multiplication by `-1`. -/
theorem eucFam_flipM_inv_gen (n : ℕ) (hn : 1 ≤ n) (a : EuclideanSpace ℝ (Fin n)) :
    RelHmapOf n (flipMn n) ({flipFst n a} : Set (EuclideanSpace ℝ (Fin n)))
      ({a} : Set (EuclideanSpace ℝ (Fin n))) (flipPair₂_gen n a)
      (eucFam n hn (flipFst n a)) = - eucFam n hn a := by
  have hlin := eucFam_linear_action_gen n hn (flipFst n) (flipFst_bijective_gen n) a
  have hsign : (if 0 < LinearMap.det (flipFst n).toLinearMap then (1 : ℤ) else -1) = -1 := by
    rw [if_neg (not_lt.mpr (le_of_lt (flipFst_det n (by omega))))]
  rw [hsign, neg_one_zsmul] at hlin
  have hfwd : RelHmapOf n (flipMn n) ({a} : Set (EuclideanSpace ℝ (Fin n)))
      ({flipFst n a} : Set (EuclideanSpace ℝ (Fin n))) (flipPair₁_gen n a)
      (eucFam n hn a) = - eucFam n hn (flipFst n a) := hlin
  have hcomp := RelHmapOf_comp (n := n) (f := flipMn n) (g := flipMn n)
    (K := ({a} : Set (EuclideanSpace ℝ (Fin n))))
    (K' := ({flipFst n a} : Set (EuclideanSpace ℝ (Fin n))))
    (K'' := ({a} : Set (EuclideanSpace ℝ (Fin n))))
    (flipPair₁_gen n a) (flipPair₂_gen n a) (flipPair₃_gen n a)
  have hid0 := RelHmapOf_congr (n := n) (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (K := ({a} : Set (EuclideanSpace ℝ (Fin n))))
    (K' := ({a} : Set (EuclideanSpace ℝ (Fin n))))
    (flipMn_comp_self n) (flipPair₃_gen n a) (fun x hx => hx)
  have hid1 : RelHmapOf n (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin n))))
      ({a} : Set (EuclideanSpace ℝ (Fin n))) ({a} : Set (EuclideanSpace ℝ (Fin n)))
      (fun x hx => hx) = LinearMap.id :=
    RelHmapOf_id (n := n) (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
      (K := ({a} : Set (EuclideanSpace ℝ (Fin n))))
  have hid : RelHmapOf n (flipMn n ≫ flipMn n) ({a} : Set (EuclideanSpace ℝ (Fin n)))
      ({a} : Set (EuclideanSpace ℝ (Fin n))) (flipPair₃_gen n a) = LinearMap.id :=
    hid0.trans hid1
  have key : (RelHmapOf n (flipMn n) ({flipFst n a} : Set (EuclideanSpace ℝ (Fin n)))
      ({a} : Set (EuclideanSpace ℝ (Fin n))) (flipPair₂_gen n a))
      ((RelHmapOf n (flipMn n) ({a} : Set (EuclideanSpace ℝ (Fin n)))
        ({flipFst n a} : Set (EuclideanSpace ℝ (Fin n))) (flipPair₁_gen n a))
        (eucFam n hn a)) = eucFam n hn a := by
    have h1 := LinearMap.congr_fun hcomp (eucFam n hn a)
    rw [LinearMap.comp_apply] at h1
    rw [h1, hid, LinearMap.id_apply]
  have key2 : - (RelHmapOf n (flipMn n) ({flipFst n a} : Set (EuclideanSpace ℝ (Fin n)))
      ({a} : Set (EuclideanSpace ℝ (Fin n))) (flipPair₂_gen n a))
      (eucFam n hn (flipFst n a)) = eucFam n hn a := by
    rw [← key, hfwd, map_neg]
  exact neg_eq_iff_eq_neg.mp key2

/-! ## The transfer of a reflected chart -/

/-- **The chart transfer of a reflected chart is the negative of the transfer of the chart**:  the
reflection of the model reverses the orientation. -/
theorem chartTr_flip_gen (n : ℕ) (hn : 1 ≤ n) {W : TopCat} [T1Space W]
    (e : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin n))) (w : W) (he : w ∈ e.source) :
    Work.PTGeometric.HOF.chartTr (e.transHomeomorph (flipHn n)) w he
        (Work.PTGeometric.HOF.eucFam n hn (flipHn n (e w)))
      = - Work.PTGeometric.HOF.chartTr e w he
            (Work.PTGeometric.HOF.eucFam n hn (e w)) := by
  have hinner : RelHmapOf n
      (TopCat.ofHom ⟨fun z => (flipHn n).symm z, (flipHn n).continuous_invFun⟩)
      ({flipHn n (e w)} : Set (EuclideanSpace ℝ (Fin n)))
      ({e w} : Set (EuclideanSpace ℝ (Fin n)))
      (fun z hz => by
        simp only [Set.mem_singleton_iff] at hz ⊢
        intro hh
        exact hz (by rw [← hh]; exact ((flipHn n).apply_symm_apply z).symm))
      (Work.PTGeometric.HOF.eucFam n hn (flipHn n (e w)))
      = - Work.PTGeometric.HOF.eucFam n hn (e w) :=
    eucFam_flipM_inv_gen n hn (e w)
  rw [Work.ThomBordism.PosAtlas.chartTr_transHomeomorph e (flipHn n) w he
    (Work.PTGeometric.HOF.eucFam n hn (flipHn n (e w))), hinner, map_neg]

/-! ## The main statement -/

theorem chartTrChangeSigned_gen (n : ℕ) (hn : 1 ≤ n) {W : TopCat} [T1Space W]
    (e f : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin n))) (w : W)
    (he : w ∈ e.source) (hf : w ∈ f.source)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Function.Bijective A)
    (hd : HasFDerivAt (fun z => f (e.symm z)) A (e w)) :
    Work.PTGeometric.HOF.chartTr e w he (Work.PTGeometric.HOF.eucFam n hn (e w))
      = (if 0 < LinearMap.det A.toLinearMap then (1 : ℤ) else -1)
        • Work.PTGeometric.HOF.chartTr f w hf (Work.PTGeometric.HOF.eucFam n hn (f w)) := by
  by_cases hdet : 0 < LinearMap.det A.toLinearMap
  · rw [if_pos hdet, one_smul]
    exact Work.PTGeometric.HOF.chartTr_change n hn e f w he hf A hd hdet
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
    have hFneg : LinearMap.det (flipFst n).toLinearMap < 0 := flipFst_det n (by omega)
    have hdet' : 0 < LinearMap.det ((flipFst n).comp A).toLinearMap := by
      rw [show ((flipFst n).comp A).toLinearMap
            = (flipFst n).toLinearMap.comp A.toLinearMap from rfl, LinearMap.det_comp]
      exact mul_pos_of_neg_of_neg hFneg hAneg
    -- the transition of the reflected chart is `flip ∘ (f ∘ e.symm)`, of derivative `flip ∘ A`
    have hd' : HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) => (f.transHomeomorph (flipHn n)) (e.symm z))
        ((flipFst n).comp A) (e w) := by
      have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => flipFst n y) (flipFst n)
          (f (e.symm (e w))) := (flipFst n).hasFDerivAt
      have h2 := h1.comp (e w) hd
      change HasFDerivAt ((fun y : EuclideanSpace ℝ (Fin n) => flipFst n y) ∘
        fun z => f (e.symm z)) ((flipFst n).comp A) (e w)
      exact h2
    have h1 := Work.PTGeometric.HOF.chartTr_change n hn e (f.transHomeomorph (flipHn n))
      w he hf ((flipFst n).comp A) hd' hdet'
    have h2 := chartTr_flip_gen n hn f w hf
    exact h1.trans h2

end

end Work.ThomBordism.PosAtlas
