/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.LineDefs
import Submission.Work.CrauderKatz.BlowUp.LineGlue
import Submission.Work.CrauderKatz.BlowUp.Defs
import Submission.Work.CrauderKatz.BlowUp.lineK_isPrime
import Submission.Work.CrauderKatz.BlowUp.lineK_height
import Submission.Work.CrauderKatz.BlowUp.isIrreducibleSpace_lineBlowUp
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.BlowUp.LineMap` — the blow-up morphism of the thickened blow-up of `𝔸³`

`lineBlowUp 𝕜` is the colimit of two copies of `Spec R`, `R = 𝕜[x,t,z,ε]/(ε², x·ε)`, glued along
`D(t)`.  Here we build the contraction morphism

`lineSigma 𝕜 : lineBlowUp 𝕜 ⟶ 𝔸³ = 𝔸(Fin 3; Spec 𝕜)`

whose restriction to the first chart is `(x,t,z) ↦ (x, x·t, z)` and to the second chart is
`(y,s,z) ↦ (s·y, y, z)`.  This is the analogue of `Submission/Work/CrauderKatz/BlowUp/ThickMap.lean`
one dimension up; the third coordinate `z` is inert, and the contraction only moves along the first
two coordinates.

The irreducibility of `lineBlowUp 𝕜` (needed for the density of the two prongs' sources) is
`Submission.Work.CrauderKatz.BlowUp.isIrreducibleSpace_lineBlowUp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

instance instIrreducibleSpaceLineBlowUp : IrreducibleSpace (lineBlowUp 𝕜) :=
  isIrreducibleSpace_lineBlowUp 𝕜

/-- The affine three-space over `𝕜`, as the spectrum of `𝕜[X,Y,Z]`. -/
abbrev A3 : Scheme.{0} := Spec (CommRingCat.of (MvPolynomial (Fin 3) 𝕜))

/-- The transition map as a `𝕜`-algebra homomorphism. -/
def lineTransAlg : lineRing 𝕜 →ₐ[𝕜] lineOvRing 𝕜 :=
  { lineTrans 𝕜 with commutes' := fun c => lineTrans_algMap 𝕜 c }

/-- The first chart of the blow-up as a ring map: `X ↦ x`, `Y ↦ x·t`, `Z ↦ z`. -/
def linePsi1 : MvPolynomial (Fin 3) 𝕜 →ₐ[𝕜] lineRing 𝕜 :=
  MvPolynomial.aeval (R := 𝕜) ![lineX 𝕜, lineX 𝕜 * lineT 𝕜, lineZ 𝕜]

/-- The second chart of the blow-up as a ring map: `X ↦ s·y`, `Y ↦ y`, `Z ↦ z` (where `y = lineX`,
`s = lineT` in the second chart). -/
def linePsi2 : MvPolynomial (Fin 3) 𝕜 →ₐ[𝕜] lineRing 𝕜 :=
  MvPolynomial.aeval (R := 𝕜) ![lineX 𝕜 * lineT 𝕜, lineX 𝕜, lineZ 𝕜]

@[simp] lemma linePsi1_X0 : linePsi1 𝕜 (MvPolynomial.X 0) = lineX 𝕜 := by
  simp [linePsi1]

@[simp] lemma linePsi1_X1 : linePsi1 𝕜 (MvPolynomial.X 1) = lineX 𝕜 * lineT 𝕜 := by
  simp [linePsi1]

@[simp] lemma linePsi1_X2 : linePsi1 𝕜 (MvPolynomial.X 2) = lineZ 𝕜 := by
  simp [linePsi1]

@[simp] lemma linePsi2_X0 : linePsi2 𝕜 (MvPolynomial.X 0) = lineX 𝕜 * lineT 𝕜 := by
  simp [linePsi2]

@[simp] lemma linePsi2_X1 : linePsi2 𝕜 (MvPolynomial.X 1) = lineX 𝕜 := by
  simp [linePsi2]

@[simp] lemma linePsi2_X2 : linePsi2 𝕜 (MvPolynomial.X 2) = lineZ 𝕜 := by
  simp [linePsi2]

/-- The first chart morphism `Spec R ⟶ Spec 𝕜[X,Y,Z]`, `(x,t,z) ↦ (x, x·t, z)`. -/
def toA3₁ : lineChartS 𝕜 ⟶ A3 𝕜 :=
  Spec.map (CommRingCat.ofHom (linePsi1 𝕜).toRingHom)

/-- The second chart morphism `Spec R ⟶ Spec 𝕜[X,Y,Z]`, `(y,s,z) ↦ (s·y, y, z)`. -/
def toA3₂ : lineChartS 𝕜 ⟶ A3 𝕜 :=
  Spec.map (CommRingCat.ofHom (linePsi2 𝕜).toRingHom)

/-- The two chart morphisms agree on the overlap (ring-level statement). -/
lemma linePsi_agree :
    (algebraMap (lineRing 𝕜) (lineOvRing 𝕜)).comp (linePsi1 𝕜).toRingHom =
      (lineTrans 𝕜).comp (linePsi2 𝕜).toRingHom := by
  refine RingHom.ext fun f => ?_
  have h : (IsScalarTower.toAlgHom 𝕜 (lineRing 𝕜) (lineOvRing 𝕜)).comp (linePsi1 𝕜) =
      (lineTransAlg 𝕜).comp (linePsi2 𝕜) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [AlgHom.comp_apply, linePsi1, linePsi2, MvPolynomial.aeval_X, lineTransAlg,
        IsScalarTower.toAlgHom_apply, lineTrans_lineX, lineTrans_lineT, lineTrans_lineZ,
        IsLocalization.Away.mul_invSelf, mul_assoc]
  have h2 := AlgHom.congr_fun h f
  simpa [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, lineTransAlg] using h2

/-- The two chart morphisms agree on the overlap. -/
lemma toA3_agree : lineOvToChart₁ 𝕜 ≫ toA3₁ 𝕜 = lineOvToChart₂ 𝕜 ≫ toA3₂ 𝕜 := by
  simp only [lineOvToChart₁, lineOvToChart₂, toA3₁, toA3₂, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [linePsi_agree 𝕜]

/-- The standard identification of the affine three-space with the spectrum of `𝕜[X,Y,Z]`. -/
def lineIso3 : Affine3 𝕜 ≅ A3 𝕜 := AffineSpace.SpecIso (Fin 3) (CommRingCat.of 𝕜)

/-- The first chart of the blow-up inside `𝔸³`. -/
def lineSig1 : lineChartS 𝕜 ⟶ Affine3 𝕜 := toA3₁ 𝕜 ≫ (lineIso3 𝕜).inv

/-- The second chart of the blow-up inside `𝔸³`. -/
def lineSig2 : lineChartS 𝕜 ⟶ Affine3 𝕜 := toA3₂ 𝕜 ≫ (lineIso3 𝕜).inv

/-- The overlap leg of the gluing: the two charts agree on `D(t)` in `𝔸³`. -/
lemma lineSig_agree : lineOvToChart₂ 𝕜 ≫ lineSig2 𝕜 = lineOvToChart₁ 𝕜 ≫ lineSig1 𝕜 := by
  rw [lineSig1, lineSig2, ← Category.assoc, ← Category.assoc, toA3_agree 𝕜]

/-- The cocone giving the contraction morphism `lineBlowUp 𝕜 ⟶ 𝔸³`. -/
def lineSigmaCocone : Cocone (lineDiag 𝕜) :=
  WidePushoutShape.mkCocone (lineOvToChart₁ 𝕜 ≫ lineSig1 𝕜)
    (fun j => if j = 0 then lineSig1 𝕜 else lineSig2 𝕜) (fun j => by
      have h : (lineDiag 𝕜).map (WidePushoutShape.Hom.init j) =
          (if j = 0 then lineOvToChart₁ 𝕜 else lineOvToChart₂ 𝕜) := by
        simp only [lineDiag, WidePushoutShape.wideSpan_map]
      refine (congrArg (fun m => m ≫ (if j = 0 then lineSig1 𝕜 else lineSig2 𝕜)) h).trans ?_
      split_ifs with hj
      · rfl
      · exact lineSig_agree 𝕜)

/-- **The contraction morphism of the thickened blow-up of `𝔸³` along a line.** -/
def lineSigma : lineBlowUp 𝕜 ⟶ Affine3 𝕜 :=
  colimit.desc (lineDiag 𝕜) (lineSigmaCocone 𝕜)

lemma lineChart₁_lineSigma : lineChart₁ 𝕜 ≫ lineSigma 𝕜 = lineSig1 𝕜 := by
  rw [lineChart₁, lineSigma]
  exact colimit.ι_desc (lineSigmaCocone 𝕜) (some 0)

lemma lineChart₂_lineSigma : lineChart₂ 𝕜 ≫ lineSigma 𝕜 = lineSig2 𝕜 := by
  rw [lineChart₂, lineSigma]
  exact colimit.ι_desc (lineSigmaCocone 𝕜) (some 1)

lemma linePsi1_algMap (c : 𝕜) : linePsi1 𝕜 (algebraMap 𝕜 (MvPolynomial (Fin 3) 𝕜) c) =
    algebraMap 𝕜 (lineRing 𝕜) c := (linePsi1 𝕜).commutes c

lemma linePsi2_algMap (c : 𝕜) : linePsi2 𝕜 (algebraMap 𝕜 (MvPolynomial (Fin 3) 𝕜) c) =
    algebraMap 𝕜 (lineRing 𝕜) c := (linePsi2 𝕜).commutes c

lemma algMap_comp_linePsi1 :
    (linePsi1 𝕜).toRingHom.comp (algebraMap 𝕜 (MvPolynomial (Fin 3) 𝕜)) =
      algebraMap 𝕜 (lineRing 𝕜) :=
  RingHom.ext (linePsi1_algMap 𝕜)

lemma algMap_comp_linePsi2 :
    (linePsi2 𝕜).toRingHom.comp (algebraMap 𝕜 (MvPolynomial (Fin 3) 𝕜)) =
      algebraMap 𝕜 (lineRing 𝕜) :=
  RingHom.ext (linePsi2_algMap 𝕜)

lemma A3_structure : (A3 𝕜 ↘ Spec (CommRingCat.of 𝕜)) =
    Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin 3) 𝕜))) := rfl

lemma toA3₁_structure : toA3₁ 𝕜 ≫ (A3 𝕜 ↘ Spec (CommRingCat.of 𝕜)) = lineChartToSpecK 𝕜 := by
  rw [A3_structure 𝕜, toA3₁, lineChartToSpecK, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    algMap_comp_linePsi1 𝕜]

lemma toA3₂_structure : toA3₂ 𝕜 ≫ (A3 𝕜 ↘ Spec (CommRingCat.of 𝕜)) = lineChartToSpecK 𝕜 := by
  rw [A3_structure 𝕜, toA3₂, lineChartToSpecK, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    algMap_comp_linePsi2 𝕜]

lemma lineIso3_inv_structure :
    (lineIso3 𝕜).inv ≫ (Affine3 𝕜 ↘ Spec (CommRingCat.of 𝕜)) =
      (A3 𝕜 ↘ Spec (CommRingCat.of 𝕜)) :=
  AffineSpace.SpecIso_inv_over (CommRingCat.of 𝕜)

lemma lineSig1_structure : lineSig1 𝕜 ≫ (Affine3 𝕜 ↘ Spec (CommRingCat.of 𝕜)) =
    lineChartToSpecK 𝕜 := by
  rw [lineSig1, Category.assoc, lineIso3_inv_structure 𝕜, toA3₁_structure 𝕜]

lemma lineSig2_structure : lineSig2 𝕜 ≫ (Affine3 𝕜 ↘ Spec (CommRingCat.of 𝕜)) =
    lineChartToSpecK 𝕜 := by
  rw [lineSig2, Category.assoc, lineIso3_inv_structure 𝕜, toA3₂_structure 𝕜]

set_option backward.isDefEq.respectTransparency false in
lemma lineColimit_ι_sigma_none :
    colimit.ι (lineDiag 𝕜) none ≫ lineSigma 𝕜 = lineOvToChart₁ 𝕜 ≫ lineSig1 𝕜 := by
  rw [lineSigma]
  exact colimit.ι_desc (lineSigmaCocone 𝕜) none

lemma lineColimit_ι_sigma_some (i : Fin 2) :
    colimit.ι (lineDiag 𝕜) (some i) ≫ lineSigma 𝕜 =
      (if i = 0 then lineSig1 𝕜 else lineSig2 𝕜) := by
  rw [lineSigma]
  exact colimit.ι_desc (lineSigmaCocone 𝕜) (some i)

lemma lineColimit_ι_specK (i : Fin 2) :
    colimit.ι (lineDiag 𝕜) (some i) ≫ lineToBeSpecK 𝕜 = lineChartToSpecK 𝕜 :=
  colimit.ι_desc (lineToSpecKCocone 𝕜) (some i)

set_option backward.isDefEq.respectTransparency false in
/-- **The contraction morphism is over `Spec 𝕜`.** -/
lemma lineSigma_isOver :
    lineSigma 𝕜 ≫ (Affine3 𝕜 ↘ Spec (CommRingCat.of 𝕜)) = lineToBeSpecK 𝕜 := by
  apply colimit.hom_ext
  intro j
  cases j with
  | none =>
    rw [← Category.assoc, lineColimit_ι_sigma_none 𝕜, Category.assoc, lineSig1_structure 𝕜,
      lineOvToChart₁_comp 𝕜, lineOverlap_toBeSpecK 𝕜]
  | some i =>
    rw [← Category.assoc, lineColimit_ι_sigma_some 𝕜 i]
    split_ifs with hi
    · rw [lineSig1_structure 𝕜, lineColimit_ι_specK 𝕜 i]
    · rw [lineSig2_structure 𝕜, lineColimit_ι_specK 𝕜 i]


/-! ## The two prongs of the thickened blow-up of `𝔸³` -/

/-- The ring homomorphism `𝕜[X₀,X₁,X₂,X₃] →+* 𝕜` with `X₀ ↦ 1`, `X₁ ↦ 1`, `X₂ ↦ 1`, `X₃ ↦ 0`. -/
private def lineAuxEval : MvPolynomial (Fin 4) 𝕜 →+* 𝕜 :=
  MvPolynomial.eval fun i : Fin 4 => if i = 0 then 1 else if i = 1 then 1 else if i = 2 then 1 else 0

private lemma lineAuxEval_X0 : lineAuxEval 𝕜 (MvPolynomial.X 0) = 1 := by simp [lineAuxEval]

private lemma lineAuxEval_X3 : lineAuxEval 𝕜 (MvPolynomial.X 3) = 0 := by simp [lineAuxEval]

private lemma lineAuxEval_of_mem {a : MvPolynomial (Fin 4) 𝕜} (ha : a ∈ lineI 𝕜) :
    lineAuxEval 𝕜 a = 0 := by
  rw [lineI, Ideal.mem_span_pair] at ha
  obtain ⟨A, B, hAB⟩ := ha
  rw [← hAB]
  simp only [map_add, map_mul, map_pow, lineAuxEval_X0, lineAuxEval_X3]
  first | refl_ring1 | ring

/-- The ring homomorphism `R = 𝕜[x,t,z,ε]/(ε², x·ε) →+* 𝕜` with `x ↦ 1`, `t ↦ 1`, `z ↦ 1`,
`ε ↦ 0`. -/
private def lineAuxPsi : lineRing 𝕜 →+* 𝕜 :=
  Ideal.Quotient.lift (lineI 𝕜) (lineAuxEval 𝕜) (fun _ ha => lineAuxEval_of_mem 𝕜 ha)

private lemma lineAuxPsi_lineX : lineAuxPsi 𝕜 (lineX 𝕜) = 1 := by
  rw [lineAuxPsi, lineX, Ideal.Quotient.lift_mk]
  exact lineAuxEval_X0 𝕜

/-- The exceptional coordinate `x` is not nilpotent in the chart ring `𝕜[x,t,z,ε]/(ε², x·ε)`. -/
lemma lineNot_isNilpotent_lineX : ¬ IsNilpotent (lineX 𝕜) := by
  intro h
  have h' : IsNilpotent (lineAuxPsi 𝕜 (lineX 𝕜)) := h.map (lineAuxPsi 𝕜)
  rw [lineAuxPsi_lineX] at h'
  exact one_ne_zero h'.eq_zero

/-- The open subscheme `D(x)` of the chart: the complement of the exceptional surface. -/
abbrev lineChartOpen : (lineChartS 𝕜).Opens := PrimeSpectrum.basicOpen (lineX 𝕜)

/-- The open subscheme `D(X i)` of `Spec 𝕜[X,Y,Z]`. -/
abbrev lineA3open (i : Fin 3) : (A3 𝕜).Opens :=
  PrimeSpectrum.basicOpen (MvPolynomial.X i : MvPolynomial (Fin 3) 𝕜)

lemma lineChartOpen_ne_bot : (lineChartOpen 𝕜 : Set (lineChartS 𝕜)).Nonempty := by
  refine Set.nonempty_iff_ne_empty.mpr fun h => lineNot_isNilpotent_lineX 𝕜 ?_
  rw [← PrimeSpectrum.basicOpen_eq_bot_iff (lineX 𝕜)]
  exact TopologicalSpace.Opens.ext h

lemma lineA3open_ne_bot (i : Fin 3) : (lineA3open 𝕜 i : Set (A3 𝕜)).Nonempty :=
  ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (MvPolynomial (Fin 3) 𝕜)), by
    exact (PrimeSpectrum.mem_basicOpen (MvPolynomial.X i) _).mpr
      (fun h => MvPolynomial.X_ne_zero i (Ideal.mem_bot.mp h))⟩

lemma dense_lineA3open (i : Fin 3) : Dense (lineA3open 𝕜 i : Set (A3 𝕜)) :=
  IsOpen.dense (lineA3open 𝕜 i).2 (lineA3open_ne_bot 𝕜 i)

/-- The overlap coordinate `t` does not lie in the generic point `lineK 𝕜 = (x, ε)` of the
exceptional surface, so `lineK 𝕜` is a point of the open overlap `D(t)`.  Computed with the
surjection `killEZBar : lineRing 𝕜 ↠ 𝕜[X,Y,Z]`, `ε ↦ 0`, under which `lineK` is the preimage of
`(X)`. -/
lemma lineT_not_mem_lineK : lineT 𝕜 ∉ lineK 𝕜 := by
  intro h
  rw [lineK_eq_comap 𝕜, Ideal.mem_comap] at h
  have hT : killEZBar 𝕜 (lineT 𝕜) = MvPolynomial.X 1 := by
    show killEZBar 𝕜 (Ideal.Quotient.mk (lineI 𝕜) (MvPolynomial.X 1)) = MvPolynomial.X 1
    rw [killEZBar_mk, killEZ_X1]
  rw [hT] at h
  have hker : (Ideal.span ({MvPolynomial.X 0} : Set (MvPolynomial (Fin 3) 𝕜))) ≤
      RingHom.ker (MvPolynomial.eval (fun i : Fin 3 => if i = 1 then 1 else 0)) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simp [MvPolynomial.eval_X]
  have h0 := hker h
  simp [MvPolynomial.eval_X] at h0

/-- The generic point of the exceptional surface: the point of the first chart defined by the
prime `(x, ε) = lineK`.  (The name avoids the ring element `lineE 𝕜 = ε` of the chart ring.) -/
abbrev lineBlowUpE : lineBlowUp 𝕜 := lineChart₁ 𝕜 ⟨lineK 𝕜, lineK_isPrime 𝕜⟩

variable {𝕜}

/-- The first prong: the first chart minus the exceptional surface, identified with `D(X) ⊂ 𝔸³`. -/
def lineProng1
    (θ : Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin 3) 𝕜) ≃ₐ[𝕜]
      Localization.Away (lineX 𝕜)) : (lineBlowUp 𝕜).PartialIso (Affine3 𝕜) where
  source := lineChart₁ 𝕜 ''ᵁ lineChartOpen 𝕜
  dense_source := by
    haveI := instIrreducibleSpaceLineBlowUp 𝕜
    refine IsOpen.dense (lineChart₁ 𝕜 ''ᵁ lineChartOpen 𝕜).2 ?_
    obtain ⟨p, hp⟩ := lineChartOpen_ne_bot 𝕜
    exact ⟨lineChart₁ 𝕜 p, by rw [Scheme.Hom.coe_image]; exact Set.mem_image_of_mem _ hp⟩
  target := (lineIso3 𝕜).inv ''ᵁ lineA3open 𝕜 0
  dense_target := by
    rw [Scheme.Hom.coe_image]
    exact (Function.Surjective.denseRange fun y =>
      ⟨(lineIso3 𝕜).hom y, by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩).dense_image
      (lineIso3 𝕜).inv.continuous (dense_lineA3open 𝕜 0)
  iso := ((lineChart₁ 𝕜).isoImage (lineChartOpen 𝕜)).symm ≪≫
    (basicOpenIsoSpecAway (R := CommRingCat.of (lineRing 𝕜)) (lineX 𝕜)) ≪≫
    Scheme.Spec.mapIso (θ.toRingEquiv.toCommRingCatIso.op) ≪≫
    (basicOpenIsoSpecAway (R := CommRingCat.of (MvPolynomial (Fin 3) 𝕜))
      (MvPolynomial.X 0)).symm ≪≫
    ((lineIso3 𝕜).inv.isoImage (lineA3open 𝕜 0))

/-- The second prong: the second chart minus the exceptional surface, identified with `D(Y) ⊂ 𝔸³`. -/
def lineProng2
    (θ : Localization.Away (MvPolynomial.X 1 : MvPolynomial (Fin 3) 𝕜) ≃ₐ[𝕜]
      Localization.Away (lineX 𝕜)) : (lineBlowUp 𝕜).PartialIso (Affine3 𝕜) where
  source := lineChart₂ 𝕜 ''ᵁ lineChartOpen 𝕜
  dense_source := by
    haveI := instIrreducibleSpaceLineBlowUp 𝕜
    refine IsOpen.dense (lineChart₂ 𝕜 ''ᵁ lineChartOpen 𝕜).2 ?_
    obtain ⟨p, hp⟩ := lineChartOpen_ne_bot 𝕜
    exact ⟨lineChart₂ 𝕜 p, by rw [Scheme.Hom.coe_image]; exact Set.mem_image_of_mem _ hp⟩
  target := (lineIso3 𝕜).inv ''ᵁ lineA3open 𝕜 1
  dense_target := by
    rw [Scheme.Hom.coe_image]
    exact (Function.Surjective.denseRange fun y =>
      ⟨(lineIso3 𝕜).hom y, by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩).dense_image
      (lineIso3 𝕜).inv.continuous (dense_lineA3open 𝕜 1)
  iso := ((lineChart₂ 𝕜).isoImage (lineChartOpen 𝕜)).symm ≪≫
    (basicOpenIsoSpecAway (R := CommRingCat.of (lineRing 𝕜)) (lineX 𝕜)) ≪≫
    Scheme.Spec.mapIso (θ.toRingEquiv.toCommRingCatIso.op) ≪≫
    (basicOpenIsoSpecAway (R := CommRingCat.of (MvPolynomial (Fin 3) 𝕜))
      (MvPolynomial.X 1)).symm ≪≫
    ((lineIso3 𝕜).inv.isoImage (lineA3open 𝕜 1))

end

end Work.CrauderKatz.BlowUp
