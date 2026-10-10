/-
Copyright (c) 2026 the annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.LineDefs
import Submission.Work.CrauderKatz.BlowUp.lineTransHom_exists

/-!
# `Work.CrauderKatz.BlowUp.LineGlue` — gluing the two charts of the thickened blow-up of `𝔸³`

`lineBlowUp 𝕜` is the colimit of the locally directed diagram of two affine charts
`Spec (lineRing 𝕜)` glued along the overlap `Spec (lineOvRing 𝕜) = Spec R[1/t]`:
the first chart by the canonical localization `R → R[1/t]`, the second by the transition
`x ↦ x·t`, `t ↦ t⁻¹`, `z ↦ z`, `ε ↦ ε`.

This is the exact analogue of `Submission/Work/CrauderKatz/BlowUp/ThickGlue.lean` one dimension up.

The transition map is obtained from `Submission.Work.CrauderKatz.BlowUp.lineTransHom_exists`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- The transition ring hom `R → R[1/t]` of the gluing, `x ↦ X0·X1`, `t ↦ X1⁻¹`, `z ↦ X2`,
`ε ↦ X3`. -/
noncomputable def lineTrans : lineRing 𝕜 →+* lineOvRing 𝕜 := (lineTransHom_exists 𝕜).choose

lemma lineTrans_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom (lineTrans 𝕜))) :=
  (lineTransHom_exists 𝕜).choose_spec.1

lemma lineTrans_lineX : lineTrans 𝕜 (lineX 𝕜) =
    algebraMap _ (lineOvRing 𝕜) (lineX 𝕜) * algebraMap _ (lineOvRing 𝕜) (lineT 𝕜) :=
  (lineTransHom_exists 𝕜).choose_spec.2.1

lemma lineTrans_lineT : lineTrans 𝕜 (lineT 𝕜) = IsLocalization.Away.invSelf (lineT 𝕜) :=
  (lineTransHom_exists 𝕜).choose_spec.2.2.1

lemma lineTrans_lineZ : lineTrans 𝕜 (lineZ 𝕜) = algebraMap _ (lineOvRing 𝕜) (lineZ 𝕜) :=
  (lineTransHom_exists 𝕜).choose_spec.2.2.2.1

lemma lineTrans_lineE : lineTrans 𝕜 (lineE 𝕜) = algebraMap _ (lineOvRing 𝕜) (lineE 𝕜) :=
  (lineTransHom_exists 𝕜).choose_spec.2.2.2.2.1

/-- The transition ring hom is `𝕜`-linear. -/
lemma lineTrans_algMap (c : 𝕜) :
    lineTrans 𝕜 (algebraMap 𝕜 (lineRing 𝕜) c) = algebraMap 𝕜 (lineOvRing 𝕜) c :=
  (lineTransHom_exists 𝕜).choose_spec.2.2.2.2.2 c

/-- The canonical localization `R → R[1/t]`, viewed as a morphism of the overlap into the first
chart. -/
def lineOvToChart₁ : lineOvS 𝕜 ⟶ lineChartS 𝕜 :=
  Spec.map (CommRingCat.ofHom (algebraMap (lineRing 𝕜) (lineOvRing 𝕜)))

/-- The transition morphism of the overlap into the second chart. -/
def lineOvToChart₂ : lineOvS 𝕜 ⟶ lineChartS 𝕜 :=
  Spec.map (CommRingCat.ofHom (lineTrans 𝕜))

instance instIsOpenImmersionLineOv₁ : IsOpenImmersion (lineOvToChart₁ 𝕜) := inferInstanceAs
  (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (lineRing 𝕜) (lineOvRing 𝕜)))))

instance instIsOpenImmersionLineOv₂ : IsOpenImmersion (lineOvToChart₂ 𝕜) :=
  lineTrans_isOpenImmersion 𝕜

/-- The gluing diagram of the thickened blow-up of `𝔸³` along a line: the two charts glued along
`Spec R[1/t]`. -/
def lineDiag : WidePushoutShape (Fin 2) ⥤ Scheme.{0} :=
  WidePushoutShape.wideSpan (lineOvS 𝕜) (fun _ => lineChartS 𝕜)
    (fun j => if j = 0 then lineOvToChart₁ 𝕜 else lineOvToChart₂ 𝕜)

lemma lineArrow_isOpenImmersion (j : Fin 2) : IsOpenImmersion ((lineDiag 𝕜).map (.init j)) := by
  have h : (lineDiag 𝕜).map (.init j) =
      (if j = 0 then lineOvToChart₁ 𝕜 else lineOvToChart₂ 𝕜) := by
    simp only [lineDiag, WidePushoutShape.wideSpan_map]
  rw [h]
  by_cases hj : j = 0
  · rw [if_pos hj]
    exact inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (lineRing 𝕜) (lineOvRing 𝕜)))))
  · rw [if_neg hj]
    exact lineTrans_isOpenImmersion 𝕜

lemma lineDiag_map_isOpenImmersion {i j : WidePushoutShape (Fin 2)} (f : i ⟶ j) :
    IsOpenImmersion ((lineDiag 𝕜).map f) := by
  rcases f with _ | j
  · exact inferInstanceAs (IsOpenImmersion (𝟙 (lineDiag 𝕜).obj _))
  · exact lineArrow_isOpenImmersion 𝕜 j

attribute [instance] lineDiag_map_isOpenImmersion

/-- **The thickened blow-up of `𝔸³` along a coordinate line.** -/
abbrev lineBlowUp : Scheme.{0} := colimit (lineDiag 𝕜)

/-- The first chart inside the thickened blow-up. -/
def lineChart₁ : lineChartS 𝕜 ⟶ lineBlowUp 𝕜 := colimit.ι (lineDiag 𝕜) (some 0)

/-- The second chart inside the thickened blow-up. -/
def lineChart₂ : lineChartS 𝕜 ⟶ lineBlowUp 𝕜 := colimit.ι (lineDiag 𝕜) (some 1)

instance : IsOpenImmersion (lineChart₁ 𝕜) := inferInstanceAs
  (IsOpenImmersion (colimit.ι (lineDiag 𝕜) (some 0)))

instance : IsOpenImmersion (lineChart₂ 𝕜) := inferInstanceAs
  (IsOpenImmersion (colimit.ι (lineDiag 𝕜) (some 1)))

end

end Work.CrauderKatz.BlowUp

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- The structure morphism of a chart to `Spec 𝕜`. -/
def lineChartToSpecK : lineChartS 𝕜 ⟶ Spec (CommRingCat.of 𝕜) :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (lineRing 𝕜)))

/-- The structure morphism of the overlap to `Spec 𝕜`. -/
def lineOvToSpecK : lineOvS 𝕜 ⟶ Spec (CommRingCat.of 𝕜) :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (lineOvRing 𝕜)))

/-- The chart is a scheme over `Spec 𝕜`. -/
instance instOverLineChartS : (lineChartS 𝕜).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨lineChartToSpecK 𝕜⟩

/-- The overlap is a scheme over `Spec 𝕜`. -/
instance instOverLineOvS : (lineOvS 𝕜).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨lineOvToSpecK 𝕜⟩

lemma lineOvToChart₁_comp :
    lineOvToChart₁ 𝕜 ≫ lineChartToSpecK 𝕜 = lineOvToSpecK 𝕜 := by
  simp only [lineOvToChart₁, lineChartToSpecK, lineOvToSpecK, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]

/-- The composite `algebraMap 𝕜 R → R[1/t]` is the `𝕜`-structure map of the overlap. -/
lemma lineTrans_comp_algMap : (lineTrans 𝕜).comp (algebraMap 𝕜 (lineRing 𝕜)) =
    algebraMap 𝕜 (lineOvRing 𝕜) :=
  RingHom.ext fun c => lineTrans_algMap 𝕜 c

lemma lineOvToChart₂_comp :
    lineOvToChart₂ 𝕜 ≫ lineChartToSpecK 𝕜 = lineOvToSpecK 𝕜 := by
  simp only [lineOvToChart₂, lineChartToSpecK, lineOvToSpecK, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [lineTrans_comp_algMap 𝕜]

/-- The cocone on the gluing diagram `lineDiag 𝕜` with point `Spec 𝕜`. -/
def lineToSpecKCocone : Cocone (lineDiag 𝕜) :=
  WidePushoutShape.mkCocone (lineOvToSpecK 𝕜) (fun _ => lineChartToSpecK 𝕜) (fun j => by
    fin_cases j
    · exact lineOvToChart₁_comp 𝕜
    · exact lineOvToChart₂_comp 𝕜)

/-- The structure morphism of the thickened blow-up to `Spec 𝕜`. -/
def lineToBeSpecK : lineBlowUp 𝕜 ⟶ Spec (CommRingCat.of 𝕜) :=
  colimit.desc (lineDiag 𝕜) (lineToSpecKCocone 𝕜)

instance instOverLineBlowUp : (lineBlowUp 𝕜).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨lineToBeSpecK 𝕜⟩

lemma lineOverlap_toBeSpecK : colimit.ι (lineDiag 𝕜) none ≫ lineToBeSpecK 𝕜 = lineOvToSpecK 𝕜 :=
  colimit.ι_desc (lineToSpecKCocone 𝕜) none

lemma lineChart₁_toBeSpecK : lineChart₁ 𝕜 ≫ lineToBeSpecK 𝕜 = lineChartToSpecK 𝕜 :=
  colimit.ι_desc (lineToSpecKCocone 𝕜) (some 0)

lemma lineChart₂_toBeSpecK : lineChart₂ 𝕜 ≫ lineToBeSpecK 𝕜 = lineChartToSpecK 𝕜 :=
  colimit.ι_desc (lineToSpecKCocone 𝕜) (some 1)

end

end Work.CrauderKatz.BlowUp

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- Both open immersions of the overlap `lineOvS 𝕜` into the colimit agree: a point `y` of the
overlap maps to the same point of `lineBlowUp 𝕜` through the first and through the second
chart.  This is the cocone condition of the colimit along the two arrows `lineOvToChart₁`,
`lineOvToChart₂`. -/
theorem lineChart₁_ovToChart₁_eq_lineChart₂_ovToChart₂ (y : lineOvS 𝕜) :
    lineChart₁ 𝕜 (lineOvToChart₁ 𝕜 y) = lineChart₂ 𝕜 (lineOvToChart₂ 𝕜 y) := by
  have hw1 : (lineDiag 𝕜).map (WidePushoutShape.Hom.init (0 : Fin 2)) = lineOvToChart₁ 𝕜 := by
    simp only [lineDiag, WidePushoutShape.wideSpan_map]
    simp
  have hw2 : (lineDiag 𝕜).map (WidePushoutShape.Hom.init (1 : Fin 2)) = lineOvToChart₂ 𝕜 := by
    simp only [lineDiag, WidePushoutShape.wideSpan_map]
    simp
  have h1 : lineOvToChart₁ 𝕜 ≫ lineChart₁ 𝕜 = colimit.ι (lineDiag 𝕜) none := by
    rw [← colimit.w (lineDiag 𝕜) (WidePushoutShape.Hom.init (0 : Fin 2)), hw1]
    rfl
  have h2 : lineOvToChart₂ 𝕜 ≫ lineChart₂ 𝕜 = colimit.ι (lineDiag 𝕜) none := by
    rw [← colimit.w (lineDiag 𝕜) (WidePushoutShape.Hom.init (1 : Fin 2)), hw2]
    rfl
  have e1 : lineChart₁ 𝕜 (lineOvToChart₁ 𝕜 y) = colimit.ι (lineDiag 𝕜) none y := by
    rw [← h1]; rfl
  have e2 : colimit.ι (lineDiag 𝕜) none y = lineChart₂ 𝕜 (lineOvToChart₂ 𝕜 y) := by
    rw [← h2]; rfl
  exact e1.trans e2

/-- The two charts of `lineBlowUp 𝕜` cover it: the open subschemes `lineChart₁.opensRange` and
`lineChart₂.opensRange` have join `⊤`. -/
theorem opensRange_lineChart₁_sup_opensRange_lineChart₂ :
    (lineChart₁ 𝕜).opensRange ⊔ (lineChart₂ 𝕜).opensRange = ⊤ := by
  rw [eq_top_iff]
  intro x hx
  obtain ⟨i, xi, hxi⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (lineDiag 𝕜) x
  rcases i with _ | j
  · have hmap : (lineDiag 𝕜).map (WidePushoutShape.Hom.init (0 : Fin 2)) = lineOvToChart₁ 𝕜 := by
      simp only [lineDiag, WidePushoutShape.wideSpan_map]
      simp
    have h0 : colimit.ι (lineDiag 𝕜) none = lineOvToChart₁ 𝕜 ≫ lineChart₁ 𝕜 := by
      rw [← colimit.w (lineDiag 𝕜) (WidePushoutShape.Hom.init (0 : Fin 2)), hmap]
      rfl
    have hxU : x ∈ (lineChart₁ 𝕜).opensRange := by
      refine Scheme.Hom.mem_opensRange.mpr ⟨lineOvToChart₁ 𝕜 xi, ?_⟩
      rw [← hxi, h0]
      rfl
    exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hxU)
  · fin_cases j
    · have hxU : x ∈ (lineChart₁ 𝕜).opensRange := Scheme.Hom.mem_opensRange.mpr ⟨xi, hxi⟩
      exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hxU)
    · have hxU : x ∈ (lineChart₂ 𝕜).opensRange := Scheme.Hom.mem_opensRange.mpr ⟨xi, hxi⟩
      exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr hxU)

/-- The two charts cover the thickened blow-up. -/
theorem lineChart_cover (x : lineBlowUp 𝕜) :
    x ∈ Set.range (lineChart₁ 𝕜) ∪ Set.range (lineChart₂ 𝕜) := by
  have h := opensRange_lineChart₁_sup_opensRange_lineChart₂ 𝕜
  have hx : x ∈ (lineChart₁ 𝕜).opensRange ⊔ (lineChart₂ 𝕜).opensRange := by rw [h]; trivial
  rw [TopologicalSpace.Opens.mem_sup] at hx
  rcases hx with h1 | h2
  · exact Or.inl (by rw [← Hom.coe_opensRange]; exact h1)
  · exact Or.inr (by rw [← Hom.coe_opensRange]; exact h2)

end

end Work.CrauderKatz.BlowUp
