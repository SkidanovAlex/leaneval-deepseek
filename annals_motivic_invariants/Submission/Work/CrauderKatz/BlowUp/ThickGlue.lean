/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.ThickDefs
import Submission.Work.CrauderKatz.BlowUp.transHom_exists_alg

/-!
# `Work.CrauderKatz.BlowUp.ThickGlue` — gluing the two charts of the thickened blow-up

`thickBlowUp 𝕜` is the colimit of the locally directed diagram of two affine charts
`Spec (thickRing 𝕜)` glued along the overlap `Spec (ovRing 𝕜) = Spec R[1/t]`:
the first chart by the canonical localization `R → R[1/t]`, the second by the transition
`x ↦ s·y = X0·X1`, `t ↦ s⁻¹ = X1⁻¹`, `ε ↦ η = X2`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- The transition ring hom `R → R[1/t]` of the gluing, `x ↦ X0·X1`, `t ↦ X1⁻¹`, `ε ↦ X2`. -/
noncomputable def trans : thickRing 𝕜 →+* ovRing 𝕜 := (transHom_exists_alg 𝕜).choose

lemma trans_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom (trans 𝕜))) :=
  (transHom_exists_alg 𝕜).choose_spec.1

lemma trans_thickX : trans 𝕜 (thickX 𝕜) =
    algebraMap _ (ovRing 𝕜) (thickX 𝕜) * algebraMap _ (ovRing 𝕜) (thickT 𝕜) :=
  (transHom_exists_alg 𝕜).choose_spec.2.1

lemma trans_thickT : trans 𝕜 (thickT 𝕜) = IsLocalization.Away.invSelf (thickT 𝕜) :=
  (transHom_exists_alg 𝕜).choose_spec.2.2.1

lemma trans_thickE : trans 𝕜 (thickE 𝕜) = algebraMap _ (ovRing 𝕜) (thickE 𝕜) :=
  (transHom_exists_alg 𝕜).choose_spec.2.2.2.1

/-- The transition ring hom is `𝕜`-linear. -/
lemma trans_algMap (c : 𝕜) :
    trans 𝕜 (algebraMap 𝕜 (thickRing 𝕜) c) = algebraMap 𝕜 (ovRing 𝕜) c :=
  (transHom_exists_alg 𝕜).choose_spec.2.2.2.2 c

/-- The canonical localization `R → R[1/t]`, viewed as a morphism of the overlap into the first
chart. -/
def ovToChart₁ : ovS 𝕜 ⟶ chartS 𝕜 :=
  Spec.map (CommRingCat.ofHom (algebraMap (thickRing 𝕜) (ovRing 𝕜)))

/-- The transition morphism of the overlap into the second chart. -/
def ovToChart₂ : ovS 𝕜 ⟶ chartS 𝕜 :=
  Spec.map (CommRingCat.ofHom (trans 𝕜))

instance instIsOpenImmersionOv₁ : IsOpenImmersion (ovToChart₁ 𝕜) := inferInstanceAs
  (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (thickRing 𝕜) (ovRing 𝕜)))))

instance instIsOpenImmersionOv₂ : IsOpenImmersion (ovToChart₂ 𝕜) := trans_isOpenImmersion 𝕜

/-- The gluing diagram of the thickened blow-up: the two charts glued along `Spec R[1/t]`. -/
def diag : WidePushoutShape (Fin 2) ⥤ Scheme.{0} :=
  WidePushoutShape.wideSpan (ovS 𝕜) (fun _ => chartS 𝕜)
    (fun j => if j = 0 then ovToChart₁ 𝕜 else ovToChart₂ 𝕜)

lemma arrow_isOpenImmersion (j : Fin 2) : IsOpenImmersion ((diag 𝕜).map (.init j)) := by
  have h : (diag 𝕜).map (.init j) =
      (if j = 0 then ovToChart₁ 𝕜 else ovToChart₂ 𝕜) := by
    simp only [diag, WidePushoutShape.wideSpan_map]
  rw [h]
  by_cases hj : j = 0
  · rw [if_pos hj]
    exact inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (thickRing 𝕜) (ovRing 𝕜)))))
  · rw [if_neg hj]
    exact trans_isOpenImmersion 𝕜

lemma diag_map_isOpenImmersion {i j : WidePushoutShape (Fin 2)} (f : i ⟶ j) :
    IsOpenImmersion ((diag 𝕜).map f) := by
  rcases f with _ | j
  · exact inferInstanceAs (IsOpenImmersion (𝟙 (diag 𝕜).obj _))
  · exact arrow_isOpenImmersion 𝕜 j

attribute [instance] diag_map_isOpenImmersion

/-- **The thickened blow-up of the affine plane at the origin.** -/
abbrev thickBlowUp : Scheme.{0} := colimit (diag 𝕜)

/-- The first chart inside the thickened blow-up. -/
def chart₁ : chartS 𝕜 ⟶ thickBlowUp 𝕜 := colimit.ι (diag 𝕜) (some 0)

/-- The second chart inside the thickened blow-up. -/
def chart₂ : chartS 𝕜 ⟶ thickBlowUp 𝕜 := colimit.ι (diag 𝕜) (some 1)

instance : IsOpenImmersion (chart₁ 𝕜) := inferInstanceAs
  (IsOpenImmersion (colimit.ι (diag 𝕜) (some 0)))

instance : IsOpenImmersion (chart₂ 𝕜) := inferInstanceAs
  (IsOpenImmersion (colimit.ι (diag 𝕜) (some 1)))

end

end Work.CrauderKatz.BlowUp

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- The structure morphism of a chart to `Spec 𝕜`. -/
def chartToSpecK : chartS 𝕜 ⟶ Spec (CommRingCat.of 𝕜) :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (thickRing 𝕜)))

/-- The structure morphism of the overlap to `Spec 𝕜`. -/
def ovToSpecK : ovS 𝕜 ⟶ Spec (CommRingCat.of 𝕜) :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (ovRing 𝕜)))

lemma ovToChart₁_comp :
    ovToChart₁ 𝕜 ≫ chartToSpecK 𝕜 = ovToSpecK 𝕜 := by
  simp only [ovToChart₁, chartToSpecK, ovToSpecK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The composite `algebraMap 𝕜 R → R[1/t]` is the `𝕜`-structure map of the overlap. -/
lemma trans_comp_algMap : (trans 𝕜).comp (algebraMap 𝕜 (thickRing 𝕜)) = algebraMap 𝕜 (ovRing 𝕜) :=
  RingHom.ext fun c => trans_algMap 𝕜 c

lemma ovToChart₂_comp :
    ovToChart₂ 𝕜 ≫ chartToSpecK 𝕜 = ovToSpecK 𝕜 := by
  simp only [ovToChart₂, chartToSpecK, ovToSpecK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [trans_comp_algMap 𝕜]

/-- The cocone on the gluing diagram `diag 𝕜` with point `Spec 𝕜`. -/
def toSpecKCocone : Cocone (diag 𝕜) :=
  WidePushoutShape.mkCocone (ovToSpecK 𝕜) (fun _ => chartToSpecK 𝕜) (fun j => by
    fin_cases j
    · exact ovToChart₁_comp 𝕜
    · exact ovToChart₂_comp 𝕜)

/-- The structure morphism of the thickened blow-up to `Spec 𝕜`. -/
def toBeSpecK : thickBlowUp 𝕜 ⟶ Spec (CommRingCat.of 𝕜) :=
  colimit.desc (diag 𝕜) (toSpecKCocone 𝕜)

instance instOverThickBlowUp : (thickBlowUp 𝕜).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨toBeSpecK 𝕜⟩

lemma overlap_toBeSpecK : colimit.ι (diag 𝕜) none ≫ toBeSpecK 𝕜 = ovToSpecK 𝕜 :=
  colimit.ι_desc (toSpecKCocone 𝕜) none

lemma chart₁_toBeSpecK : chart₁ 𝕜 ≫ toBeSpecK 𝕜 = chartToSpecK 𝕜 :=
  colimit.ι_desc (toSpecKCocone 𝕜) (some 0)

lemma chart₂_toBeSpecK : chart₂ 𝕜 ≫ toBeSpecK 𝕜 = chartToSpecK 𝕜 :=
  colimit.ι_desc (toSpecKCocone 𝕜) (some 1)

end

end Work.CrauderKatz.BlowUp
