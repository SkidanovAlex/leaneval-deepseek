import Submission.Work.Induction.isVChar_indFun
import Submission.Work.Induction.isVChar_resFun
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.cfInner_indFun_eq_of_TI
import Submission.Work.Coherence.Defs
import Submission.Work.CharCore.mem_Irr_iff_fdrep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Induction.Bridge`: vocabulary bridges to `Work.Coherence`

Area A6 states its character-ring results in the vocabulary of area A5
(`Work.CharCore.IsClassFun / cfInner / Irr / IsChar / IsVChar`).  The project lead asked
CharCore to unify the character-theory vocabulary with the one delivered by area A11
(`Work.Coherence.IsClassFun / cfInner / Irr / IsChar / IsVChar`); A6 follows CharCore, so the
results below are deliberately phrased in `Work.CharCore`'s vocabulary.

This file records that the two vocabularies agree and restates the main restriction/induction
closure results in `Work.Coherence`'s vocabulary, so that a caller using either one can use
A6's results directly.  (The canonical bridge is area A5's; this is a convenience copy inside
A6.)
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Induction

variable {G : Type*} [Group G] [Fintype G]

/-- `Work.CharCore.Irr` and `Work.Coherence.Irr` are the same set of characters: both are the
characters of the simple finite-dimensional complex representations
(`Work.CharCore.mem_Irr_iff_fdrep`, `Work.Coherence.mem_Irr`). -/
theorem irr_eq_coherence :
    ((Work.CharCore.Irr G : Finset (G → ℂ)) : Set (G → ℂ)) = Work.Coherence.Irr G := by
  ext χ
  exact (Work.CharCore.mem_Irr_iff_fdrep χ).trans (Work.Coherence.mem_Irr).symm

theorem isChar_iff_coherence (f : G → ℂ) :
    Work.CharCore.IsChar f ↔ Work.Coherence.IsChar f := by
  rw [Work.CharCore.IsChar, Work.Coherence.IsChar, irr_eq_coherence]

theorem isVChar_iff_coherence (f : G → ℂ) :
    Work.CharCore.IsVChar f ↔ Work.Coherence.IsVChar f := by
  rw [Work.CharCore.IsVChar, Work.Coherence.IsVChar, irr_eq_coherence]

theorem cfInner_eq_coherence (f g : G → ℂ) :
    Work.CharCore.cfInner f g = Work.Coherence.cfInner f g := rfl

theorem isClassFun_iff_coherence (f : G → ℂ) :
    Work.CharCore.IsClassFun f ↔ Work.Coherence.IsClassFun f := Iff.rfl

section RestrictionInduction

variable {H : Subgroup G}

/-- Frobenius reciprocity in `Work.Coherence`'s vocabulary. -/
theorem coherence_frobenius_reciprocity (φ : H → ℂ) (ψ : G → ℂ)
    (hψ : Work.Coherence.IsClassFun ψ) :
    Work.Coherence.cfInner (indFun H φ) ψ = Work.Coherence.cfInner φ (resFun H ψ) := by
  rw [← cfInner_eq_coherence]
  exact frobenius_reciprocity H φ ψ ((isClassFun_iff_coherence ψ).mpr hψ)

/-- Restriction of a character, in `Work.Coherence`'s vocabulary. -/
theorem coherence_isChar_resFun {φ : G → ℂ} (hφ : Work.Coherence.IsChar φ) :
    Work.Coherence.IsChar (resFun H φ) :=
  (isChar_iff_coherence _).mp <|
    isChar_resFun ((isChar_iff_coherence (G := G) φ).mpr hφ)

/-- Induction of a character, in `Work.Coherence`'s vocabulary. -/
theorem coherence_isChar_indFun {φ : H → ℂ} (hφ : Work.Coherence.IsChar φ) :
    Work.Coherence.IsChar (indFun H φ) :=
  (isChar_iff_coherence _).mp <|
    isChar_indFun ((isChar_iff_coherence (G := H) φ).mpr hφ)

/-- Restriction of a virtual character, in `Work.Coherence`'s vocabulary. -/
theorem coherence_isVChar_resFun {φ : G → ℂ} (hφ : Work.Coherence.IsVChar φ) :
    Work.Coherence.IsVChar (resFun H φ) :=
  (isVChar_iff_coherence _).mp <|
    isVChar_resFun ((isVChar_iff_coherence (G := G) φ).mpr hφ)

/-- Induction of a virtual character, in `Work.Coherence`'s vocabulary. -/
theorem coherence_isVChar_indFun {φ : H → ℂ} (hφ : Work.Coherence.IsVChar φ) :
    Work.Coherence.IsVChar (indFun H φ) :=
  (isVChar_iff_coherence _).mp <|
    isVChar_indFun ((isVChar_iff_coherence (G := H) φ).mpr hφ)

/-- The Brauer–Suzuki isometry, in `Work.Coherence`'s vocabulary. -/
theorem coherence_cfInner_indFun_eq_of_TI (hTI : IsTI H) (hN : normalizer H = H)
    (φ ψ : H → ℂ) (hφ : Work.Coherence.IsClassFun φ) (hψ : Work.Coherence.IsClassFun ψ)
    (hφ1 : φ 1 = 0) (hψ1 : ψ 1 = 0) :
    Work.Coherence.cfInner (indFun H φ) (indFun H ψ) = Work.Coherence.cfInner φ ψ := by
  rw [← cfInner_eq_coherence]
  exact cfInner_indFun_eq_of_TI H hTI hN φ ψ ((isClassFun_iff_coherence φ).mpr hφ)
    ((isClassFun_iff_coherence ψ).mpr hψ) hφ1 hψ1

end RestrictionInduction

end Work.Induction
