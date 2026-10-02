import Mathlib
import Submission.Work.ThomBordism.KeyLocal.chartDefs
import Submission.Work.ThomBordism.KeyLocal.tcmRelCup_stdModelGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.KeyLocal

theorem chartProductFormula {X : Type} [TopologicalSpace X] {k : ℕ}
    (a : C(X, Work.Tubular.Euc 8)) (b : C(X, Work.Tubular.Euc k))
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hAmem : ∀ y ∈ A, a y ∈ ({0}ᶜ : Set (Work.Tubular.Euc 8)))
    (hBmem : ∀ y ∈ B, b y ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)))
    (hAeq : A = (fun y => a y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc 8)))
    (hBeq : B = (fun y => b y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc k)))
    (hmem : ∀ y ∈ A ∪ B, Work.Whitney.tcmSumLin 8 k (a y, b y)
      ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))) :
    Work.Whitney.tcmRelCup A B hA hB 8 k
      ((Work.Thom.relCohMap a A ({0}ᶜ : Set (Work.Tubular.Euc 8)) hAmem ℤ 8).hom
        Work.ThomBordism.FrameSigns.tau)
      ((Work.Thom.relCohMap b B ({0}ᶜ : Set (Work.Tubular.Euc k)) hBmem ℤ k).hom
        (Work.ThomBordism.stdModelGen k))
    = Work.ThomBordism.KeyLocal.tauSign • (Work.Thom.relCohMap
        (⟨fun y => Work.Whitney.tcmSumLin 8 k (a y, b y),
          (Work.Whitney.tcmSumLin 8 k).continuous.comp (a.continuous.prodMk b.continuous)⟩ :
            C(X, Work.Tubular.Euc (8 + k)))
        (A ∪ B) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmem ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)) := by
  subst hAeq
  subst hBeq
  have htau :
      (Work.Thom.relCohMap a ((fun y => a y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc 8)))
          ({0}ᶜ : Set (Work.Tubular.Euc 8)) hAmem ℤ 8).hom Work.ThomBordism.FrameSigns.tau
      = Work.ThomBordism.KeyLocal.tauSign •
        (Work.Thom.relCohMap a ((fun y => a y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc 8)))
          ({0}ᶜ : Set (Work.Tubular.Euc 8)) hAmem ℤ 8).hom
        (Work.ThomBordism.stdModelGen 8) := by
    rw [Work.ThomBordism.KeyLocal.tau_eq_tauSign_smul_stdModelGen, map_zsmul]
  rw [htau]
  have hsmul : ∀ (x : Work.Thom.RelCoh ℤ 8 X
        ((fun y => a y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc 8))))
      (y : Work.Thom.RelCoh ℤ k X ((fun y => b y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc k)))),
      Work.Whitney.tcmRelCup ((fun y => a y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc 8)))
          ((fun y => b y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc k))) hA hB 8 k
          (Work.ThomBordism.KeyLocal.tauSign • x) y
      = Work.ThomBordism.KeyLocal.tauSign •
          (Work.Whitney.tcmRelCup ((fun y => a y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc 8)))
            ((fun y => b y) ⁻¹' ({0}ᶜ : Set (Work.Tubular.Euc k))) hA hB 8 k x y) := by
    intro x y
    conv_lhs => rw [map_zsmul]
    rfl
  rw [hsmul]
  rw [← Work.ThomBordism.KeyLocal.tcmRelCup_stdModelGen a b]

end Work.ThomBordism.KeyLocal
