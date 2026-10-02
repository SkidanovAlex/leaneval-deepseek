import Mathlib
import Submission.Work.ThomBordism.FrameSigns.linearModelAction
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationPos
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationNeg
import Submission.Work.ThomBordism.coorientationRef

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The model action of a linear isomorphism of `ℝⁿ` on `Hⁿ(ℝⁿ, ℝⁿ∖0; ℤ)`

The chapter `Submission/Work/ThomBordism/FrameSigns/linearModelAction.lean` proves, for the single
dimension `n = 8`, that a linear isomorphism `A` of `ℝ⁸` acts on `H⁸(ℝ⁸, ℝ⁸∖0; ℤ)` by the sign of
`det A`.  The TEL route for the key local statement (`Submission/Work/ThomBordism/keyLocal.lean`,
plan (v)) needs the same statement in the *ambient* dimension `8 + k` — and, for the normal part, in
the fibre dimension `k`.  This file records the general-dimension version
`Work.ThomBordism.FrameSigns.linearModelActionN`, by the same proof (the gauge statement
`Work.ThomBordism.FrameSigns.gaugeOrientationPos`/`Neg` is already general in `n`).

Consequence (also recorded here): a change of frame by a *positive*-determinant linear isomorphism
does not change the pullback of any class, in particular of the standard model generator
`Work.ThomBordism.stdModelGen`; this is exactly the step "the determinant sign of the frame
comparison is `pairSign …`, hence the two frames give the same reading of the model class" that the
TEL route uses.
-/

namespace Work.ThomBordism.FrameSigns

open CategoryTheory

noncomputable section

variable {n : ℕ}

/-- The identification of the model space `ℝⁿ` with the total space of the trivial rank-`n` bundle
over the one-point space, as a continuous map of pairs
`(ℝⁿ, ℝⁿ∖0) → (PUnit × ℝⁿ, PUnit × (ℝⁿ∖0))`. -/
def lmaInclN : C(EuclideanSpace ℝ (Fin n), PUnit × EuclideanSpace ℝ (Fin n)) :=
  ⟨fun v => (PUnit.unit, v), continuous_const.prodMk continuous_id⟩

/-- The projection of the total space of the trivial rank-`n` bundle over the one-point space onto
its fibre, as a continuous map of pairs `(PUnit × ℝⁿ, PUnit × (ℝⁿ∖0)) → (ℝⁿ, ℝⁿ∖0)`. -/
def lmaProjN : C(PUnit × EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
  ⟨Prod.snd, continuous_snd⟩

@[simp] theorem lmaProjN_comp_lmaInclN :
    lmaProjN.comp lmaInclN = ContinuousMap.id (EuclideanSpace ℝ (Fin n)) := by
  apply ContinuousMap.ext; intro v; rfl

theorem lmaInclN_comp_lmaProjN :
    lmaInclN.comp lmaProjN = ContinuousMap.id (PUnit × EuclideanSpace ℝ (Fin n)) := by
  apply ContinuousMap.ext; intro p
  exact Prod.ext (Subsingleton.elim (PUnit.unit) p.1) rfl

/-- **Conjugation lemma** (dimension `n`): a single invertible endomorphism `A` of `ℝⁿ` which is the
conjugate `proj ∘ gaugeEnd D ∘ incl` of a gauge over the one-point base acts on
`Hⁿ(ℝⁿ, ℝⁿ∖0; ℤ)` by the same integer `c` as the gauge. -/
theorem lmaConjN (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
    (hA : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      A x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}))
    (D : PUnit → Work.Thom.Gauge n) (hD : Continuous D)
    (hmem : ∀ p ∈ Work.Thom.Punct PUnit n, Work.Thom.gaugeEnd D hD p ∈ Work.Thom.Punct PUnit n)
    (hAeq : A = lmaProjN.comp ((Work.Thom.gaugeEnd D hD).comp lmaInclN))
    (c : ℤ)
    (hchar : ∀ ξ : Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n))
      (Work.Thom.Punct PUnit n),
      (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct PUnit n)
        (Work.Thom.Punct PUnit n) hmem ℤ n).hom ξ = c • ξ) :
    ∀ ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (Work.Thom.relCohMap A ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hA ℤ n).hom ξ = c • ξ := by
  intro ξ
  have hI : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      lmaInclN x ∈ Work.Thom.Punct PUnit n := fun x hx => hx
  have hp : ∀ y ∈ Work.Thom.Punct PUnit n,
      lmaProjN y ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) := fun y hy => hy
  have hGincl : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (Work.Thom.gaugeEnd D hD) (lmaInclN x) ∈ Work.Thom.Punct PUnit n :=
    fun x hx => hmem (lmaInclN x) (hI x hx)
  have hgi : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      lmaProjN ((Work.Thom.gaugeEnd D hD) (lmaInclN x)) ∈
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) :=
    fun x hx => hp _ (hGincl x hx)
  let Λ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ⟶
      Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct PUnit n) :=
    Work.Thom.relCohMap lmaProjN (Work.Thom.Punct PUnit n)
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hp ℤ n
  let Φ : Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct PUnit n) ⟶
      Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) :=
    Work.Thom.relCohMap lmaInclN ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
      (Work.Thom.Punct PUnit n) hI ℤ n
  let Γ : Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct PUnit n) ⟶
      Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct PUnit n) :=
    Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct PUnit n)
      (Work.Thom.Punct PUnit n) hmem ℤ n
  have h1 : (ModuleCat.Hom.hom Φ) ((ModuleCat.Hom.hom Λ) ξ) = ξ := by
    have hLP : Λ ≫ Φ = 𝟙 (Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})) := by
      have hc := Work.Thom.relCohMap_comp' (X := EuclideanSpace ℝ (Fin n))
        (Y := PUnit × EuclideanSpace ℝ (Fin n)) (Z := EuclideanSpace ℝ (Fin n))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) (Work.Thom.Punct PUnit n)
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) lmaInclN lmaProjN hI hp
        (fun x hx => hp (lmaInclN x) (hI x hx)) ℤ n
      dsimp only [Λ, Φ]
      rw [hc]
      rw [Work.Thom.relCohMap_congr' (f := lmaProjN.comp lmaInclN)
        (f' := ContinuousMap.id (EuclideanSpace ℝ (Fin n)))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        lmaProjN_comp_lmaInclN (fun x hx => hp (lmaInclN x) (hI x hx)) (fun x hx => hx) ℤ n]
      rw [Work.Thom.relCohMap_id' ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ℤ n]
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using congrArg (fun φ => φ.hom ξ) hLP
  have h2 : (ModuleCat.Hom.hom Γ) ((ModuleCat.Hom.hom Λ) ξ) = c • ((ModuleCat.Hom.hom Λ) ξ) :=
    hchar ((ModuleCat.Hom.hom Λ) ξ)
  have h3 : (ModuleCat.Hom.hom (Work.Thom.relCohMap A ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hA ℤ n)) ξ
      = (ModuleCat.Hom.hom Φ) ((ModuleCat.Hom.hom Γ) ((ModuleCat.Hom.hom Λ) ξ)) := by
    have hfac : Work.Thom.relCohMap A ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hA ℤ n = Λ ≫ (Γ ≫ Φ) := by
      rw [Work.Thom.relCohMap_congr' (f := A)
        (f' := lmaProjN.comp ((Work.Thom.gaugeEnd D hD).comp lmaInclN))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        hAeq hA hgi ℤ n]
      rw [← Work.Thom.relCohMap_comp' (X := EuclideanSpace ℝ (Fin n))
        (Y := PUnit × EuclideanSpace ℝ (Fin n)) (Z := EuclideanSpace ℝ (Fin n))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) (Work.Thom.Punct PUnit n)
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ((Work.Thom.gaugeEnd D hD).comp lmaInclN) lmaProjN
        hGincl hp hgi ℤ n]
      rw [← Work.Thom.relCohMap_comp' (X := EuclideanSpace ℝ (Fin n))
        (Y := PUnit × EuclideanSpace ℝ (Fin n)) (Z := PUnit × EuclideanSpace ℝ (Fin n))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) (Work.Thom.Punct PUnit n) (Work.Thom.Punct PUnit n)
        lmaInclN (Work.Thom.gaugeEnd D hD) hI hmem hGincl ℤ n]
    rw [hfac, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [h3, h2, map_zsmul, h1]

/-- **The model action of a linear isomorphism of `ℝⁿ` on `Hⁿ(ℝⁿ, ℝⁿ∖0; ℤ)`**, in the general
dimension `n`.  `A` acts by the sign of its determinant. -/
theorem linearModelActionNGen (hn : 1 ≤ n)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hdet : LinearMap.det (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap ≠ 0)
    (hA : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) x ∈
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})) :
    ∀ ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (Work.Thom.relCohMap (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hA ℤ n).hom ξ
        = (if 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap
            then (1 : ℤ) else -1) • ξ := by
  intro ξ
  let D : PUnit → Work.Thom.Gauge n := fun _ =>
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  have hD : Continuous D := continuous_const
  have hAeq : (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) =
      lmaProjN.comp ((Work.Thom.gaugeEnd D hD).comp lmaInclN) := by
    apply ContinuousMap.ext; intro v; rfl
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · have hmem : ∀ p ∈ Work.Thom.Punct PUnit n,
        Work.Thom.gaugeEnd D hD p ∈ Work.Thom.Punct PUnit n :=
      Work.Thom.gaugeEnd_mem D hD
        (fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_lt hneg))
    have h := lmaConjN (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) hA D hD hmem hAeq (-1)
      (fun ξ' => by
        simpa using Work.ThomBordism.FrameSigns.gaugeOrientationNeg (n := n) hn D hD
          (fun _ => hneg) ξ') ξ
    rw [h, if_neg (not_lt.mpr hneg.le)]
  · have hmem : ∀ p ∈ Work.Thom.Punct PUnit n,
        Work.Thom.gaugeEnd D hD p ∈ Work.Thom.Punct PUnit n :=
      Work.Thom.gaugeEnd_mem D hD
        (fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_gt hpos))
    have h := lmaConjN (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) hA D hD hmem hAeq 1
      (fun ξ' => by
        simpa using Work.ThomBordism.FrameSigns.gaugeOrientationPos (n := n) hn D hD
          (fun _ => hpos) ξ') ξ
    rw [h, if_pos hpos]

/-- **The model action, with the pair condition discharged by the linear isomorphism.** -/
theorem linearModelActionN (hn : 1 ≤ n)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hdet : LinearMap.det (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap ≠ 0) :
    ∀ ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (Work.Thom.relCohMap (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        (fun z hz => by
          simp only [Set.mem_setOf_eq] at hz ⊢
          exact fun h => hz ((A.map_eq_zero_iff).mp h)) ℤ n).hom ξ
        = (if 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap
            then (1 : ℤ) else -1) • ξ := by
  intro ξ
  exact linearModelActionNGen hn A hdet _ ξ

/-- **A positive-determinant change of frame does not change the reading of any class.**

If a frame-reading map `Φ` — a map of pairs `(X, B) → (ℝⁿ, ℝⁿ∖0)` — is post-composed with a linear
isomorphism `A` of positive determinant (equivalently: if the two frames differ by `A`), then the two
readings of a relative class agree.

This is the form in which the TEL route consumes the model action: with
`Work.ThomBordism.sigmaTelescope_gauss` supplying `pairSign (flipTan …) (gframe …) = 1`, i.e.
`det A > 0` for the comparison of the ambient/tube frame with the σ-corrected Gauss frame of the
normal bundle, this is the class-level comparison of the two coorientation conventions of `ν`. -/
theorem relCohMap_comp_linearModelActionNGen {n : ℕ} (hn : 1 ≤ n)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hdet : 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap)
    (hA : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) x ∈
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}))
    {X : Type} [TopologicalSpace X] (B : Set X) (Φ : C(X, EuclideanSpace ℝ (Fin n)))
    (hΦ : ∀ x ∈ B, Φ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}))
    (hAΦ : ∀ x ∈ B, (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) (Φ x) ∈
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}))
    (ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n))
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})) :
    (Work.Thom.relCohMap ((A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))).comp Φ)
        B ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hAΦ ℤ n).hom ξ
      = (Work.Thom.relCohMap Φ B ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hΦ ℤ n).hom ξ := by
  have hcomp := Work.Thom.relCohMap_comp' B ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) Φ
      (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) hΦ hA hAΦ ℤ n
  rw [← hcomp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [linearModelActionNGen hn A (ne_of_gt hdet) hA ξ, if_pos hdet, one_smul]

/-- **A positive-determinant change of frame does not change the reading of the standard model
generator** — the specialisation of `relCohMap_comp_linearModelActionNGen` to
`Work.ThomBordism.stdModelGen`, i.e. the class whose readings are the two coorientation conventions. -/
theorem relCohMap_comp_linearModelActionN_stdModelGen {n : ℕ} (hn : 1 ≤ n)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hdet : 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap)
    (hA : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) x ∈
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}))
    {X : Type} [TopologicalSpace X] (B : Set X) (Φ : C(X, EuclideanSpace ℝ (Fin n)))
    (hΦ : ∀ x ∈ B, Φ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}))
    (hAΦ : ∀ x ∈ B, (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) (Φ x) ∈
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})) :
    (Work.Thom.relCohMap ((A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))).comp Φ)
        B ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hAΦ ℤ n).hom
        (Work.ThomBordism.stdModelGen n)
      = (Work.Thom.relCohMap Φ B ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hΦ ℤ n).hom
        (Work.ThomBordism.stdModelGen n) :=
  relCohMap_comp_linearModelActionNGen hn A hdet hA B Φ hΦ hAΦ
    (Work.ThomBordism.stdModelGen n)

end

end Work.ThomBordism.FrameSigns
