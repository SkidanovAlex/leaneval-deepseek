import Mathlib
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationPos
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationNeg
import Submission.Work.Thom.relCohHomeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The model action of a linear isomorphism of `ℝ⁸` on `H⁸(ℝ⁸, ℝ⁸∖0; ℤ)`

The target of this file is `Work.ThomBordism.FrameSigns.linearModelAction`: a linear isomorphism
`A` of `ℝ⁸` acts on the top relative cohomology of the pair `(ℝ⁸, ℝ⁸∖0)` by the sign of its
determinant.

The mathematical content is entirely contained in the two "gauge orientation" statements of the
Thom chapter, `Work.ThomBordism.FrameSigns.gaugeOrientationPos` and
`Work.ThomBordism.FrameSigns.gaugeOrientationNeg`: a gauge automorphism `(y,v) ↦ (y, D y v)` of the
trivial bundle `Y × ℝⁿ → Y` whose determinant is positive (resp. negative) everywhere acts as the
identity (resp. by `-1`) on `H^n(Y × ℝⁿ, Y × (ℝⁿ∖0); ℤ)`.  The only thing left to do here is to
realise the *linear* isomorphism `A` of `ℝ⁸` as the conjugate of the constant gauge it defines over
the one-point base `Y = PUnit`, along the homeomorphism of pairs

`ℝ⁸ ≅ PUnit × ℝ⁸,  v ↦ ((), v)`

(the inverse being the projection onto the second factor).  Concretely, with
`incl : C(ℝ⁸, PUnit × ℝ⁸)` the above inclusion and `proj` the projection, one has
`A = proj ∘ gaugeEnd D ∘ incl` with `D : PUnit → Gauge 8` the constant family `D _ = A`, and hence,
by functoriality of the pullback of relative cohomology (`Work.Thom.relCohMap_comp'`),

`relCohMap A = relCohMap proj ≫ relCohMap (gaugeEnd D) ≫ relCohMap incl`.

Since `relCohMap proj ≫ relCohMap incl = relCohMap (proj ∘ incl) = 𝟙` (the two maps being inverse to
each other), the action of `A` on a class `ξ` is the action of the gauge on `relCohMap proj ξ`,
transported back:

`(relCohMap A).hom ξ = (relCohMap incl).hom ((relCohMap (gaugeEnd D)).hom ((relCohMap proj).hom ξ))`.
-/

namespace Work.ThomBordism.FrameSigns

open CategoryTheory

noncomputable section

/-- The identification of the model space `ℝ⁸` with the total space of the trivial rank-`8` bundle
over the one-point space, as a continuous map of pairs
`(ℝ⁸, ℝ⁸∖0) → (PUnit × ℝ⁸, PUnit × (ℝ⁸∖0))`. -/
def lmaIncl : C(EuclideanSpace ℝ (Fin 8), PUnit × EuclideanSpace ℝ (Fin 8)) :=
  ⟨fun v => (PUnit.unit, v), continuous_const.prodMk continuous_id⟩

/-- The projection of the total space of the trivial rank-`8` bundle over the one-point space onto
its fibre, as a continuous map of pairs `(PUnit × ℝ⁸, PUnit × (ℝ⁸∖0)) → (ℝ⁸, ℝ⁸∖0)` inverse to
`lmaIncl`. -/
def lmaProj : C(PUnit × EuclideanSpace ℝ (Fin 8), EuclideanSpace ℝ (Fin 8)) :=
  ⟨Prod.snd, continuous_snd⟩

/-- `lmaProj` is a left inverse of `lmaIncl` (as a map of pairs). -/
@[simp] theorem lmaProj_comp_lmaIncl :
    lmaProj.comp lmaIncl = ContinuousMap.id (EuclideanSpace ℝ (Fin 8)) := by
  apply ContinuousMap.ext; intro v; rfl

/-- `lmaIncl` is a left inverse of `lmaProj` (as a map of pairs). -/
theorem lmaIncl_comp_lmaProj :
    lmaIncl.comp lmaProj = ContinuousMap.id (PUnit × EuclideanSpace ℝ (Fin 8)) := by
  apply ContinuousMap.ext; intro p
  exact Prod.ext (Subsingleton.elim (PUnit.unit) p.1) rfl

/-- **Conjugation lemma.**  Let `D : PUnit → Gauge 8` be a gauge over the one-point base (i.e. a
single invertible endomorphism of `ℝ⁸`), acting on the punctured relative cohomology
`H⁸(PUnit × ℝ⁸, PUnit × (ℝ⁸∖0); ℤ)` by the integer `c`, and suppose that the continuous map `A`
of `ℝ⁸` is the conjugate `proj ∘ gaugeEnd D ∘ incl` of that gauge by the homeomorphism of pairs
`ℝ⁸ ≅ PUnit × ℝ⁸`.  Then `A` acts on `H⁸(ℝ⁸, ℝ⁸∖0; ℤ)` by `c` as well.

This is the passage from the "gauge over a point" statement to the statement about a single linear
isomorphism of `ℝ⁸`. -/
theorem lmaConj (A : C(EuclideanSpace ℝ (Fin 8), EuclideanSpace ℝ (Fin 8)))
    (hA : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}),
      A x ∈ ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}))
    (D : PUnit → Work.Thom.Gauge 8) (hD : Continuous D)
    (hmem : ∀ p ∈ Work.Thom.Punct PUnit 8, Work.Thom.gaugeEnd D hD p ∈ Work.Thom.Punct PUnit 8)
    (hAeq : A = lmaProj.comp ((Work.Thom.gaugeEnd D hD).comp lmaIncl))
    (c : ℤ)
    (hchar : ∀ ξ : Work.Thom.RelCoh ℤ 8 (PUnit × EuclideanSpace ℝ (Fin 8)) (Work.Thom.Punct PUnit 8),
      (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct PUnit 8) (Work.Thom.Punct PUnit 8)
        hmem ℤ 8).hom ξ = c • ξ) :
    ∀ ξ : Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}),
      (Work.Thom.relCohMap A ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0})
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) hA ℤ 8).hom ξ = c • ξ := by
  intro ξ
  -- The inclusion and the projection carry the punctured part to the punctured part.
  have hI : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}), lmaIncl x ∈ Work.Thom.Punct PUnit 8 :=
    fun x hx => hx
  have hp : ∀ y ∈ Work.Thom.Punct PUnit 8, lmaProj y ∈ ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) :=
    fun y hy => hy
  have hGincl : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}),
      (Work.Thom.gaugeEnd D hD) (lmaIncl x) ∈ Work.Thom.Punct PUnit 8 :=
    fun x hx => hmem (lmaIncl x) (hI x hx)
  have hgi : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}),
      lmaProj ((Work.Thom.gaugeEnd D hD) (lmaIncl x)) ∈ ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) :=
    fun x hx => hp _ (hGincl x hx)
  -- The three pullbacks of the factorisation `A = proj ∘ gaugeEnd D ∘ incl`.
  let Λ : Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) ⟶
      Work.Thom.RelCoh ℤ 8 (PUnit × EuclideanSpace ℝ (Fin 8)) (Work.Thom.Punct PUnit 8) :=
    Work.Thom.relCohMap lmaProj (Work.Thom.Punct PUnit 8) ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) hp ℤ 8
  let Φ : Work.Thom.RelCoh ℤ 8 (PUnit × EuclideanSpace ℝ (Fin 8)) (Work.Thom.Punct PUnit 8) ⟶
      Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) :=
    Work.Thom.relCohMap lmaIncl ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) (Work.Thom.Punct PUnit 8) hI ℤ 8
  let Γ : Work.Thom.RelCoh ℤ 8 (PUnit × EuclideanSpace ℝ (Fin 8)) (Work.Thom.Punct PUnit 8) ⟶
      Work.Thom.RelCoh ℤ 8 (PUnit × EuclideanSpace ℝ (Fin 8)) (Work.Thom.Punct PUnit 8) :=
    Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct PUnit 8) (Work.Thom.Punct PUnit 8) hmem ℤ 8
  -- `proj` and `incl` are inverse to each other, so `Λ ≫ Φ = 𝟙`.
  have h1 : (ModuleCat.Hom.hom Φ) ((ModuleCat.Hom.hom Λ) ξ) = ξ := by
    have hLP : Λ ≫ Φ = 𝟙 (Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8))
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0})) := by
      have hc := Work.Thom.relCohMap_comp' (X := EuclideanSpace ℝ (Fin 8))
        (Y := PUnit × EuclideanSpace ℝ (Fin 8)) (Z := EuclideanSpace ℝ (Fin 8))
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) (Work.Thom.Punct PUnit 8)
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) lmaIncl lmaProj hI hp
        (fun x hx => hp (lmaIncl x) (hI x hx)) ℤ 8
      dsimp only [Λ, Φ]
      rw [hc]
      rw [Work.Thom.relCohMap_congr' (f := lmaProj.comp lmaIncl)
        (f' := ContinuousMap.id (EuclideanSpace ℝ (Fin 8)))
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0})
        lmaProj_comp_lmaIncl (fun x hx => hp (lmaIncl x) (hI x hx)) (fun x hx => hx) ℤ 8]
      rw [Work.Thom.relCohMap_id' ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) ℤ 8]
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using congrArg (fun φ => φ.hom ξ) hLP
  -- The gauge acts by `c`.
  have h2 : (ModuleCat.Hom.hom Γ) ((ModuleCat.Hom.hom Λ) ξ) = c • ((ModuleCat.Hom.hom Λ) ξ) :=
    hchar ((ModuleCat.Hom.hom Λ) ξ)
  -- The factorisation of `relCohMap A`.
  have h3 : (ModuleCat.Hom.hom (Work.Thom.relCohMap A ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0})
      ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) hA ℤ 8)) ξ
      = (ModuleCat.Hom.hom Φ) ((ModuleCat.Hom.hom Γ) ((ModuleCat.Hom.hom Λ) ξ)) := by
    have hfac : Work.Thom.relCohMap A ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0})
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) hA ℤ 8 = Λ ≫ (Γ ≫ Φ) := by
      rw [Work.Thom.relCohMap_congr' (f := A)
        (f' := lmaProj.comp ((Work.Thom.gaugeEnd D hD).comp lmaIncl))
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0})
        hAeq hA hgi ℤ 8]
      rw [← Work.Thom.relCohMap_comp' (X := EuclideanSpace ℝ (Fin 8))
        (Y := PUnit × EuclideanSpace ℝ (Fin 8)) (Z := EuclideanSpace ℝ (Fin 8))
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) (Work.Thom.Punct PUnit 8)
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) ((Work.Thom.gaugeEnd D hD).comp lmaIncl) lmaProj
        hGincl hp hgi ℤ 8]
      rw [← Work.Thom.relCohMap_comp' (X := EuclideanSpace ℝ (Fin 8))
        (Y := PUnit × EuclideanSpace ℝ (Fin 8)) (Z := PUnit × EuclideanSpace ℝ (Fin 8))
        ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}) (Work.Thom.Punct PUnit 8) (Work.Thom.Punct PUnit 8)
        lmaIncl (Work.Thom.gaugeEnd D hD) hI hmem hGincl ℤ 8]
    rw [hfac, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [h3, h2, map_zsmul, h1]

/-- **The model action of a linear isomorphism of `ℝ⁸` on `H⁸(ℝ⁸, ℝ⁸∖0; ℤ)`**, with the
"punctured" membership hypothesis left as an explicit argument.

A linear isomorphism `A` of `ℝ⁸` acts on `H⁸(ℝ⁸, ℝ⁸∖0; ℤ)` by the sign of its determinant. -/
theorem linearModelActionGen (A : EuclideanSpace ℝ (Fin 8) ≃L[ℝ] EuclideanSpace ℝ (Fin 8))
    (hdet : LinearMap.det (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 8)).toLinearMap ≠ 0)
    (hA : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}),
      (A : C(EuclideanSpace ℝ (Fin 8), EuclideanSpace ℝ (Fin 8))) x
        ∈ ({v : EuclideanSpace ℝ (Fin 8) | v ≠ 0})) :
    ∀ ξ : Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) {v : EuclideanSpace ℝ (Fin 8) | v ≠ 0},
      (Work.Thom.relCohMap (A : C(EuclideanSpace ℝ (Fin 8), EuclideanSpace ℝ (Fin 8)))
        {v : EuclideanSpace ℝ (Fin 8) | v ≠ 0} {v : EuclideanSpace ℝ (Fin 8) | v ≠ 0} hA ℤ 8).hom ξ
        = (if 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 8)).toLinearMap then (1 : ℤ) else -1) • ξ := by
  intro ξ
  -- `A` as the constant gauge over the one-point base.
  let D : PUnit → Work.Thom.Gauge 8 := fun _ =>
    (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 8))
  have hD : Continuous D := continuous_const
  have hAeq : (A : C(EuclideanSpace ℝ (Fin 8), EuclideanSpace ℝ (Fin 8))) =
      lmaProj.comp ((Work.Thom.gaugeEnd D hD).comp lmaIncl) := by
    apply ContinuousMap.ext; intro v; rfl
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- negative determinant: the gauge acts by `-1`
    have hmem : ∀ p ∈ Work.Thom.Punct PUnit 8,
        Work.Thom.gaugeEnd D hD p ∈ Work.Thom.Punct PUnit 8 :=
      Work.Thom.gaugeEnd_mem D hD
        (fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_lt hneg))
    have h := lmaConj (A : C(EuclideanSpace ℝ (Fin 8), EuclideanSpace ℝ (Fin 8))) hA D hD hmem hAeq (-1)
      (fun ξ' => by
        simpa using Work.ThomBordism.FrameSigns.gaugeOrientationNeg (n := 8) (by norm_num) D hD
          (fun _ => hneg) ξ') ξ
    rw [h, if_neg (not_lt.mpr hneg.le)]
  · -- positive determinant: the gauge acts by `1`
    have hmem : ∀ p ∈ Work.Thom.Punct PUnit 8,
        Work.Thom.gaugeEnd D hD p ∈ Work.Thom.Punct PUnit 8 :=
      Work.Thom.gaugeEnd_mem D hD
        (fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_gt hpos))
    have h := lmaConj (A : C(EuclideanSpace ℝ (Fin 8), EuclideanSpace ℝ (Fin 8))) hA D hD hmem hAeq 1
      (fun ξ' => by
        simpa using Work.ThomBordism.FrameSigns.gaugeOrientationPos (n := 8) (by norm_num) D hD
          (fun _ => hpos) ξ') ξ
    rw [h, if_pos hpos]

theorem linearModelAction (A : EuclideanSpace ℝ (Fin 8) ≃L[ℝ] EuclideanSpace ℝ (Fin 8))
    (hdet : LinearMap.det (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 8)).toLinearMap ≠ 0) :
    ∀ ξ : Work.Thom.RelCoh ℤ 8 (EuclideanSpace ℝ (Fin 8)) {v : EuclideanSpace ℝ (Fin 8) | v ≠ 0},
      (Work.Thom.relCohMap (A : C(EuclideanSpace ℝ (Fin 8), EuclideanSpace ℝ (Fin 8)))
        {v : EuclideanSpace ℝ (Fin 8) | v ≠ 0} {v : EuclideanSpace ℝ (Fin 8) | v ≠ 0}
        (fun z hz => by
          simp only [Set.mem_setOf_eq] at hz ⊢
          exact fun h => hz ((A.map_eq_zero_iff).mp h)) ℤ 8).hom ξ
        = (if 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 8)).toLinearMap then (1 : ℤ) else -1) • ξ := by
  intro ξ
  exact linearModelActionGen A hdet _ ξ

end

end Work.ThomBordism.FrameSigns
