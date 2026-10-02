import Mathlib
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationPos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism.KeyLocal

noncomputable section

/-- **A fibrewise linear reparametrisation with positive determinant does not change the pullback of
the standard model generator.**

For a topological space `Y`, a continuous family `A : Y → (ℝ^k →L[ℝ] ℝ^k)` of linear maps of
*positive determinant*, a continuous map `B : Y → ℝ^k` and a set `S ⊆ Y` on which the values of `A y`
do not vanish (hypothesis `hC`) and the values of `B` do not vanish (hypothesis `hB`),

  `(y ↦ A y (B y))^*(stdModelGen k) = B^*(stdModelGen k)`   in `H^k(Y, S)`

(relative to the *same* set `S` on both sides).

Proof: write `y ↦ A y (B y)` as `proj₂ ∘ gaugeEnd A ∘ (y ↦ (y, B y))`.  The gauge
`(y, v) ↦ (y, A y v)` acts trivially on `H^k(Y × ℝ^k, Y × (ℝ^k∖0))` — the PROVED
`Work.ThomBordism.FrameSigns.gaugeOrientationPos`, via the model class `Mpun` — and the pullback
along the section `y ↦ (y, B y)` of the product class `(y, v) ↦ v` is the pullback of `stdModelGen k`
along `B`.  **No homotopy of `A` to the identity through invertible maps is used** (and none exists
in general): the gauge statement is an exact algebraic identification of the model classes. -/
theorem varyingMatGauge {k : ℕ} (hk : 1 ≤ k) {Y : Type} [TopologicalSpace Y]
    (A : C(Y, EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
    (hpos : ∀ y, 0 < LinearMap.det (A y).toLinearMap)
    (B : C(Y, EuclideanSpace ℝ (Fin k))) (S : Set Y)
    (hC : ∀ y ∈ S,
      (⟨fun y => A y (B y), A.continuous.clm_apply B.continuous⟩ :
        C(Y, EuclideanSpace ℝ (Fin k))) y ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
    (hB : ∀ y ∈ S, B y ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))) :
    (Work.Thom.relCohMap
        (⟨fun y => A y (B y), A.continuous.clm_apply B.continuous⟩ :
          C(Y, EuclideanSpace ℝ (Fin k)))
        S ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) hC ℤ k).hom
        (Work.ThomBordism.stdModelGen k)
      = (Work.Thom.relCohMap B S ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) hB ℤ k).hom
        (Work.ThomBordism.stdModelGen k) := by
  classical
  set Ec := EuclideanSpace ℝ (Fin k) with hEc
  -- the projection `Y × ℝ^k → ℝ^k`
  set P : C(Y × Ec, Ec) := ⟨Prod.snd, continuous_snd⟩ with hP
  have hPmem : ∀ p ∈ Work.Thom.Punct Y k, P p ∈ ({0}ᶜ : Set Ec) := fun p hp => hp
  set ξ : Work.Thom.RelCoh ℤ k (Y × Ec) (Work.Thom.Punct Y k) :=
    (Work.Thom.relCohMap P (Work.Thom.Punct Y k) ({0}ᶜ : Set Ec) hPmem ℤ k).hom
      (Work.ThomBordism.stdModelGen k) with hξ
  -- the gauge
  set D : Y → Work.Thom.Gauge k := fun y => A y with hD
  have hDc : Continuous D := A.continuous
  have hbij : ∀ y, Function.Bijective (D y) := fun y =>
    Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_gt (hpos y))
  have hGmem : ∀ p ∈ Work.Thom.Punct Y k,
      Work.Thom.gaugeEnd D hDc p ∈ Work.Thom.Punct Y k :=
    Work.Thom.gaugeEnd_mem D hDc hbij
  have hGfix : (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hDc) (Work.Thom.Punct Y k)
      (Work.Thom.Punct Y k) hGmem ℤ k).hom ξ = ξ :=
    Work.ThomBordism.FrameSigns.gaugeOrientationPos hk D hDc hpos ξ
  -- the section
  set Ψ : C(Y, Y × Ec) := ⟨fun y => (y, B y), continuous_id.prodMk B.continuous⟩ with hΨ
  have hΨmem : ∀ y ∈ S, Ψ y ∈ Work.Thom.Punct Y k := fun y hy => hB y hy
  have hCP : ∀ y ∈ S, (Work.Thom.gaugeEnd D hDc) (Ψ y) ∈ Work.Thom.Punct Y k :=
    fun y hy => hGmem (Ψ y) (hΨmem y hy)
  have hcp1 : P.comp Ψ = B := by
    apply ContinuousMap.ext; intro y; rfl
  have hcp3 : P.comp ((Work.Thom.gaugeEnd D hDc).comp Ψ) =
      ⟨fun y => A y (B y), A.continuous.clm_apply B.continuous⟩ := by
    apply ContinuousMap.ext; intro y; rfl
  have hPcomp : ∀ y ∈ S, (P.comp ((Work.Thom.gaugeEnd D hDc).comp Ψ)) y ∈
      ({0}ᶜ : Set Ec) := fun y hy => hC y hy
  -- the left-hand side
  have hL : (Work.Thom.relCohMap
        (⟨fun y => A y (B y), A.continuous.clm_apply B.continuous⟩ : C(Y, Ec))
        S ({0}ᶜ : Set Ec) hC ℤ k).hom (Work.ThomBordism.stdModelGen k)
      = (Work.Thom.relCohMap Ψ S (Work.Thom.Punct Y k) hΨmem ℤ k).hom ξ := by
    rw [show (Work.Thom.relCohMap
          (⟨fun y => A y (B y), A.continuous.clm_apply B.continuous⟩ : C(Y, Ec))
          S ({0}ᶜ : Set Ec) hC ℤ k)
        = (Work.Thom.relCohMap (P.comp ((Work.Thom.gaugeEnd D hDc).comp Ψ)) S
            ({0}ᶜ : Set Ec) hPcomp ℤ k) from
      (Work.Thom.relCohMap_congrA S ({0}ᶜ : Set Ec) hcp3 hC hPcomp ℤ k).symm]
    rw [show (Work.Thom.relCohMap (P.comp ((Work.Thom.gaugeEnd D hDc).comp Ψ)) S
          ({0}ᶜ : Set Ec) hPcomp ℤ k).hom (Work.ThomBordism.stdModelGen k)
        = (Work.Thom.relCohMap ((Work.Thom.gaugeEnd D hDc).comp Ψ) S
            (Work.Thom.Punct Y k) hCP ℤ k).hom ((Work.Thom.relCohMap P
              (Work.Thom.Punct Y k) ({0}ᶜ : Set Ec) hPmem ℤ k).hom
            (Work.ThomBordism.stdModelGen k)) from
      (Work.Thom.relCohMap_compA_apply S (Work.Thom.Punct Y k) ({0}ᶜ : Set Ec)
        ((Work.Thom.gaugeEnd D hDc).comp Ψ) P hCP hPmem hPcomp ℤ k
        (Work.ThomBordism.stdModelGen k)).symm]
    rw [← hξ]
    rw [show (Work.Thom.relCohMap ((Work.Thom.gaugeEnd D hDc).comp Ψ) S
          (Work.Thom.Punct Y k) hCP ℤ k).hom ξ
        = (Work.Thom.relCohMap Ψ S (Work.Thom.Punct Y k) hΨmem ℤ k).hom
          ((Work.Thom.relCohMap (Work.Thom.gaugeEnd D hDc) (Work.Thom.Punct Y k)
            (Work.Thom.Punct Y k) hGmem ℤ k).hom ξ) from
      (Work.Thom.relCohMap_compA_apply S (Work.Thom.Punct Y k) (Work.Thom.Punct Y k)
        Ψ (Work.Thom.gaugeEnd D hDc) hΨmem hGmem hCP ℤ k ξ).symm]
    rw [hGfix]
  -- the right-hand side
  have hR : (Work.Thom.relCohMap B S ({0}ᶜ : Set Ec) hB ℤ k).hom
        (Work.ThomBordism.stdModelGen k)
      = (Work.Thom.relCohMap Ψ S (Work.Thom.Punct Y k) hΨmem ℤ k).hom ξ := by
    rw [show (Work.Thom.relCohMap B S ({0}ᶜ : Set Ec) hB ℤ k)
        = (Work.Thom.relCohMap (P.comp Ψ) S ({0}ᶜ : Set Ec)
            (fun y hy => hPmem (Ψ y) (hΨmem y hy)) ℤ k) from
      (Work.Thom.relCohMap_congrA S ({0}ᶜ : Set Ec) hcp1 hB
        (fun y hy => hPmem (Ψ y) (hΨmem y hy)) ℤ k).symm]
    rw [show (Work.Thom.relCohMap (P.comp Ψ) S ({0}ᶜ : Set Ec)
          (fun y hy => hPmem (Ψ y) (hΨmem y hy)) ℤ k).hom
          (Work.ThomBordism.stdModelGen k)
        = (Work.Thom.relCohMap Ψ S (Work.Thom.Punct Y k) hΨmem ℤ k).hom
          ((Work.Thom.relCohMap P (Work.Thom.Punct Y k) ({0}ᶜ : Set Ec) hPmem ℤ k).hom
            (Work.ThomBordism.stdModelGen k)) from
      (Work.Thom.relCohMap_compA_apply S (Work.Thom.Punct Y k) ({0}ᶜ : Set Ec)
        Ψ P hΨmem hPmem (fun y hy => hPmem (Ψ y) (hΨmem y hy)) ℤ k
        (Work.ThomBordism.stdModelGen k)).symm]
  rw [hL, hR]

end

end Work.ThomBordism.KeyLocal
