import Submission.Work.Core.Std
import Submission.Work.Cases.const

open LeanEval.Geometry.NewlanderNirenberg
open Set
open scoped ContDiff

namespace Submission

variable {n : ℕ}

/-- Derivative of `y ↦ J₀ (V y)` for a constant linear `J₀`. -/
lemma fderiv_const_comp (J₀ : E n →L[ℝ] E n) (V : E n → E n) (x : E n)
    (hV : DifferentiableAt ℝ V x) :
    fderiv ℝ (fun y => J₀ (V y)) x = J₀.comp (fderiv ℝ V x) :=
  ((J₀.hasFDerivAt.comp x hV.hasFDerivAt)).fderiv

/-- **The Nijenhuis tensor of a constant field of endomorphisms vanishes.**  For a constant `J₀`
with `J₀² = -1` the four terms of `N(V,W)` cancel. -/
lemma nijenhuis_const (J₀ : E n →L[ℝ] E n) (hJ₀ : ∀ v, J₀ (J₀ v) = -v)
    (V W : E n → E n) (x : E n) (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    nijenhuis (fun _ => J₀) V W x = 0 := by
  have hJV : fderiv ℝ (fun y => J₀ (V y)) x = J₀.comp (fderiv ℝ V x) :=
    fderiv_const_comp J₀ V x hV
  have hJW : fderiv ℝ (fun y => J₀ (W y)) x = J₀.comp (fderiv ℝ W x) :=
    fderiv_const_comp J₀ W x hW
  simp only [nijenhuis, VectorField.lieBracket, hJV, hJW, ContinuousLinearMap.comp_apply,
    sub_apply, map_sub, hJ₀]
  abel

lemma nijenhuisVanishesOn_const (J₀ : E n →L[ℝ] E n) (hJ₀ : ∀ v, J₀ (J₀ v) = -v)
    (U : Set (E n)) : NijenhuisVanishesOn (fun _ : E n => J₀) U :=
  fun V W hV hW x _ =>
    nijenhuis_const J₀ hJ₀ V W x (hV.contDiffAt.differentiableAt (by simp))
      (hW.contDiffAt.differentiableAt (by simp))

lemma isAlmostComplexOn_const (J₀ : E n →L[ℝ] E n) (hJ₀ : ∀ v, J₀ (J₀ v) = -v)
    (U : Set (E n)) : IsAlmostComplexOn (fun _ : E n => J₀) U :=
  ⟨contDiffOn_const, fun _ _ v => hJ₀ v⟩

/-- **The challenge statement for a constant almost complex structure.**  A constant field `J₀`
with `J₀² = -1` is an almost complex structure with vanishing Nijenhuis tensor on every open set,
and the conclusion of `newlander_nirenberg` holds for it. -/
theorem of_const {U : Set (E n)} (hU : IsOpen U) (J₀ : E n →L[ℝ] E n)
    (hJ₀ : ∀ v, J₀ (J₀ v) = -v) {x : E n} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (F n),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → F n) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : F n → E n) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E n,
        fderiv ℝ (φ : E n → F n) y (J₀ v) = Complex.I • fderiv ℝ (φ : E n → F n) y v :=
  Work.Cases.const hU J₀ hJ₀ hx

/-- The hypotheses of the challenge statement hold for the transported standard structure. -/
lemma isAlmostComplexOn_stdOf' (T : E n ≃L[ℝ] F n) (U : Set (E n)) :
    IsAlmostComplexOn (stdOf T) U :=
  isAlmostComplexOn_stdOf T U

lemma nijenhuisVanishesOn_stdOf (T : E n ≃L[ℝ] F n) (U : Set (E n)) :
    NijenhuisVanishesOn (stdOf T) U := by
  have hconst : (fun _ : E n => stdOf T 0) = stdOf T := rfl
  rw [← hconst]
  exact nijenhuisVanishesOn_const (stdOf T 0) (fun v => stdOf_sq T 0 v) U

/-- **The challenge statement for the standard structure `stdOf T`.** -/
theorem of_std {U : Set (E n)} (hU : IsOpen U) (T : E n ≃L[ℝ] F n) {x : E n} (hx : x ∈ U) :
    ∃ φ : OpenPartialHomeomorph (E n) (F n),
      x ∈ φ.source ∧ φ.source ⊆ U ∧
      ContDiffOn ℝ ∞ (φ : E n → F n) φ.source ∧
      ContDiffOn ℝ ∞ (φ.symm : F n → E n) φ.target ∧
      ∀ y ∈ φ.source, ∀ v : E n,
        fderiv ℝ (φ : E n → F n) y (stdOf T y v)
          = Complex.I • fderiv ℝ (φ : E n → F n) y v :=
  newlander_nirenberg_std hU T hx

end Submission
