import Mathlib
import Submission.Work.ThomBordism.FrameSigns.linearActionIsl
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationPos
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationNeg

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The action of a linear isomorphism of `ℝⁿ` on `Hⁿ(ℝⁿ, ℝⁿ∖0)`

A bijective continuous linear endomorphism `A` of `ℝⁿ` (`n ≥ 1`) acts on the top relative
cohomology of the pair `(ℝⁿ, ℝⁿ∖0)` by the sign of its determinant.

The mathematical content is the two "gauge orientation" statements
`Work.ThomBordism.FrameSigns.gaugeOrientationPos` / `gaugeOrientationNeg`: a gauge automorphism
`(y,v) ↦ (y, D y v)` of the trivial bundle `Y × ℝⁿ → Y` with pointwise positive (resp. negative)
determinant acts as `+1` (resp. `-1`) on `Hⁿ(Y × ℝⁿ, Y × (ℝⁿ∖0); ℤ)`.  The linear map `A` is the
conjugate of the constant gauge over the one-point base along the homeomorphism of pairs
`ℝⁿ ≅ PUnit × ℝⁿ`, `v ↦ ((), v)`, and pullback is functorial.

This is the general-`n` version of `Work.ThomBordism.FrameSigns.linearModelActionIsl` (which is
stated for `n = 8`); the `n = 8` and `n = 9` cases are its specialisations.
-/

namespace Work.ThomBordism.PosAtlas

open CategoryTheory

noncomputable section

/-- The identification of the model space `ℝⁿ` with the total space of the trivial rank-`n` bundle
over the one-point base, as a continuous map of pairs
`(ℝⁿ, ℝⁿ∖0) → (PUnit × ℝⁿ, PUnit × (ℝⁿ∖0))`. -/
def cohIncl (n : ℕ) : C(EuclideanSpace ℝ (Fin n), PUnit × EuclideanSpace ℝ (Fin n)) :=
  ⟨fun v => (PUnit.unit, v), continuous_const.prodMk continuous_id⟩

/-- The projection of the total space of the trivial rank-`n` bundle over the one-point base onto
its fibre, as a continuous map of pairs `(PUnit × ℝⁿ, PUnit × (ℝⁿ∖0)) → (ℝⁿ, ℝⁿ∖0)` inverse to
`cohIncl`. -/
def cohProj (n : ℕ) : C(PUnit × EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
  ⟨Prod.snd, continuous_snd⟩

/-- `cohProj` is a left inverse of `cohIncl`. -/
@[simp] theorem cohProj_comp_cohIncl (n : ℕ) :
    (cohProj n).comp (cohIncl n) = ContinuousMap.id (EuclideanSpace ℝ (Fin n)) := by
  apply ContinuousMap.ext; intro v; rfl

/-- `cohIncl` is a left inverse of `cohProj`. -/
theorem cohIncl_comp_cohProj (n : ℕ) :
    (cohIncl n).comp (cohProj n) = ContinuousMap.id (PUnit × EuclideanSpace ℝ (Fin n)) := by
  apply ContinuousMap.ext; intro p
  exact Prod.ext (Subsingleton.elim (PUnit.unit) p.1) rfl

/-- **Conjugation lemma.**  Let `D : PUnit → Gauge n` be a gauge over the one-point base (i.e. a
single invertible endomorphism of `ℝⁿ`), acting on the punctured relative cohomology
`Hⁿ(PUnit × ℝⁿ, PUnit × (ℝⁿ∖0); ℤ)` by the integer `c`, and let `A` be the conjugate
`proj ∘ gaugeEnd D ∘ incl` of that gauge by the homeomorphism of pairs `ℝⁿ ≅ PUnit × ℝⁿ`.  Then
`A` acts on `Hⁿ(ℝⁿ, ℝⁿ∖0; ℤ)` by `c` as well. -/
theorem cohConj {n : ℕ}
    (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
    (hA : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      A x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}))
    (D : PUnit → Work.Thom.Gauge n) (hD : Continuous D)
    (hmem : ∀ p ∈ Work.Thom.Punct PUnit n, Work.Thom.gaugeEnd D hD p ∈ Work.Thom.Punct PUnit n)
    (hAeq : A = (cohProj n).comp ((Work.Thom.gaugeEnd D hD).comp (cohIncl n)))
    (c : ℤ)
    (hchar : ∀ ξ : Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n))
        (Work.Thom.Punct PUnit n),
      (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct PUnit n)
        (Work.Thom.Punct PUnit n) hmem ℤ n).hom ξ = c • ξ) :
    ∀ ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (Work.Thom.relCohMap A ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hA ℤ n).hom ξ = c • ξ := by
  intro ξ
  -- The inclusion and the projection carry the punctured part to the punctured part.
  have hI : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      cohIncl n x ∈ Work.Thom.Punct PUnit n := fun x hx => hx
  have hp : ∀ y ∈ Work.Thom.Punct PUnit n,
      cohProj n y ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) := fun y hy => hy
  have hGincl : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (Work.Thom.gaugeEnd D hD) (cohIncl n x) ∈ Work.Thom.Punct PUnit n :=
    fun x hx => hmem (cohIncl n x) (hI x hx)
  have hgi : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      cohProj n ((Work.Thom.gaugeEnd D hD) (cohIncl n x))
        ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) := fun x hx => hp _ (hGincl x hx)
  -- The three pullbacks of the factorisation `A = proj ∘ gaugeEnd D ∘ incl`.
  let Λ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ⟶
      Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct PUnit n) :=
    Work.Thom.relCohMap (cohProj n) (Work.Thom.Punct PUnit n)
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hp ℤ n
  let Φ : Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct PUnit n) ⟶
      Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) :=
    Work.Thom.relCohMap (cohIncl n) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
      (Work.Thom.Punct PUnit n) hI ℤ n
  let Γ : Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct PUnit n) ⟶
      Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct PUnit n) :=
    Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct PUnit n)
      (Work.Thom.Punct PUnit n) hmem ℤ n
  -- `proj` and `incl` are inverse to each other, so `Λ ≫ Φ = 𝟙`.
  have h1 : (ModuleCat.Hom.hom Φ) ((ModuleCat.Hom.hom Λ) ξ) = ξ := by
    have hLP : Λ ≫ Φ = 𝟙 (Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})) := by
      have hc := Work.Thom.relCohMap_compA (X := EuclideanSpace ℝ (Fin n))
        (Y := PUnit × EuclideanSpace ℝ (Fin n)) (Z := EuclideanSpace ℝ (Fin n))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) (Work.Thom.Punct PUnit n)
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) (cohIncl n) (cohProj n) hI hp
        (fun x hx => hp (cohIncl n x) (hI x hx)) ℤ n
      dsimp only [Λ, Φ]
      rw [hc]
      rw [Work.Thom.relCohMap_congrA (f := (cohProj n).comp (cohIncl n))
        (f' := ContinuousMap.id (EuclideanSpace ℝ (Fin n)))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        (cohProj_comp_cohIncl n) (fun x hx => hp (cohIncl n x) (hI x hx)) (fun x hx => hx) ℤ n]
      rw [Work.Thom.relCohMap_idA ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ℤ n]
    simpa [ModuleCat.hom_comp, ModuleCat.hom_id] using congrArg (fun φ => φ.hom ξ) hLP
  -- The gauge acts by `c`.
  have h2 : (ModuleCat.Hom.hom Γ) ((ModuleCat.Hom.hom Λ) ξ) = c • ((ModuleCat.Hom.hom Λ) ξ) :=
    hchar ((ModuleCat.Hom.hom Λ) ξ)
  -- The factorisation of `relCohMap A`.
  have h3 : (ModuleCat.Hom.hom (Work.Thom.relCohMap A ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
      ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hA ℤ n)) ξ
      = (ModuleCat.Hom.hom Φ) ((ModuleCat.Hom.hom Γ) ((ModuleCat.Hom.hom Λ) ξ)) := by
    have hfac : Work.Thom.relCohMap A ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) hA ℤ n = Λ ≫ (Γ ≫ Φ) := by
      rw [Work.Thom.relCohMap_congrA (f := A)
        (f' := (cohProj n).comp ((Work.Thom.gaugeEnd D hD).comp (cohIncl n)))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
        hAeq hA hgi ℤ n]
      rw [← Work.Thom.relCohMap_compA (X := EuclideanSpace ℝ (Fin n))
        (Y := PUnit × EuclideanSpace ℝ (Fin n)) (Z := EuclideanSpace ℝ (Fin n))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) (Work.Thom.Punct PUnit n)
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) ((Work.Thom.gaugeEnd D hD).comp (cohIncl n))
        (cohProj n) hGincl hp hgi ℤ n]
      rw [← Work.Thom.relCohMap_compA (X := EuclideanSpace ℝ (Fin n))
        (Y := PUnit × EuclideanSpace ℝ (Fin n)) (Z := PUnit × EuclideanSpace ℝ (Fin n))
        ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) (Work.Thom.Punct PUnit n)
        (Work.Thom.Punct PUnit n) (cohIncl n) (Work.Thom.gaugeEnd D hD) hI hmem hGincl ℤ n]
    rw [hfac, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [h3, h2, map_zsmul, h1]

/-- **The model action of a linear isomorphism of `ℝⁿ` on `Hⁿ(ℝⁿ, ℝⁿ∖0; ℤ)`**, with the punctured
membership hypothesis left as an explicit argument.

A bijective continuous linear endomorphism `A` of `ℝⁿ` (`n ≥ 1`) acts on
`Hⁿ(ℝⁿ, ℝⁿ∖0; ℤ)` by the sign of its determinant. -/
theorem cohLinearActionGen {n : ℕ} (hn : 1 ≤ n)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Function.Bijective A) :
    ∀ (hP : ∀ x ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
        (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) x
          ∈ ({v : EuclideanSpace ℝ (Fin n) | v ≠ 0}))
      (ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n))
        {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}),
      (Work.Thom.relCohMap (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
        {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}
        hP ℤ n).hom ξ
      = (if 0 < LinearMap.det A.toLinearMap then (1 : ℤ) else -1) • ξ := by
  intro hP ξ
  -- A bijective endomorphism has non-zero determinant.
  have hdet : LinearMap.det A.toLinearMap ≠ 0 := by
    intro h0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0)
      (LinearMap.ker_eq_bot.2 hA.1)
  -- `A` as the constant gauge over the one-point base.
  let D : PUnit → Work.Thom.Gauge n := fun _ => A
  have hD : Continuous D := continuous_const
  have hmem : ∀ p ∈ Work.Thom.Punct PUnit n,
      Work.Thom.gaugeEnd D hD p ∈ Work.Thom.Punct PUnit n :=
    Work.Thom.gaugeEnd_mem D hD (fun _ => hA)
  have hAeq : (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) =
      (cohProj n).comp ((Work.Thom.gaugeEnd D hD).comp (cohIncl n)) := by
    apply ContinuousMap.ext; intro v; rfl
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- negative determinant: the gauge acts by `-1`
    have hchar : ∀ ξ' : Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n))
        (Work.Thom.Punct PUnit n),
        (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct PUnit n)
          (Work.Thom.Punct PUnit n) hmem ℤ n).hom ξ' = (-1 : ℤ) • ξ' := by
      intro ξ'
      simpa using Work.ThomBordism.FrameSigns.gaugeOrientationNeg (n := n) hn D hD
        (fun _ => hneg) ξ'
    have h := cohConj (A := (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))))
      hP D hD hmem hAeq (-1) hchar ξ
    rw [h, if_neg (not_lt.mpr hneg.le)]
  · -- positive determinant: the gauge acts by `1`
    have hchar : ∀ ξ' : Work.Thom.RelCoh ℤ n (PUnit × EuclideanSpace ℝ (Fin n))
        (Work.Thom.Punct PUnit n),
        (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct PUnit n)
          (Work.Thom.Punct PUnit n) hmem ℤ n).hom ξ' = (1 : ℤ) • ξ' := by
      intro ξ'
      simpa using Work.ThomBordism.FrameSigns.gaugeOrientationPos (n := n) hn D hD
        (fun _ => hpos) ξ'
    have h := cohConj (A := (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))))
      hP D hD hmem hAeq 1 hchar ξ
    rw [h, if_pos hpos]

theorem cohLinearAction {n : ℕ} (hn : 1 ≤ n)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Function.Bijective A) :
    ∀ ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n)) {v | v ≠ 0},
      (Work.Thom.relCohMap (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
        {v | v ≠ 0} {v | v ≠ 0}
        (fun x hx => by
          simp only [Set.mem_ofPred_eq] at hx ⊢
          intro h
          exact hx (hA.1 (by simpa using h))) ℤ n).hom ξ
      = (if 0 < LinearMap.det A.toLinearMap then (1 : ℤ) else -1) • ξ := by
  intro ξ
  exact cohLinearActionGen hn A hA (fun x hx => by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      intro h
      exact hx (hA.1 (by simpa using h))) ξ

end

end Work.ThomBordism.PosAtlas
