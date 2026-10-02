import Mathlib
import Submission.Work.Thom.Mpun_natural_map
import Submission.Work.ThomBordism.KeyLocal.tcmRelCup_stdModelGen

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

/-- **The model class `Mpun n ↥W` only depends on the second coordinate.**

For any `P : X → ↥W` and `V : X → ℝⁿ`, the pullback of the natural model class `Mpun n ↥W` along
`x ↦ (P x, V x)` is the pullback of the standard generator `stdModelGen n` along `V`.

Indeed `Mpun n ↥W = (const unit, id)^*(Mpun n PUnit)` by the base naturality `Mpun_natural_map`
(the constant map `↥W → PUnit`), and `stdModelGen n = psiUnit^*(Mpun n PUnit)`. -/
theorem mpunPullbackSnd {n : ℕ} {B : Type} [TopologicalSpace B] {W : Set B}
    {X : Type} [TopologicalSpace X] (P : C(X, ↥W)) (V : C(X, EuclideanSpace ℝ (Fin n))) :
    (Work.Thom.relCohMap
        (⟨fun x => ((P x : ↥W), V x), P.continuous.prodMk V.continuous⟩ :
          C(X, ↥W × EuclideanSpace ℝ (Fin n)))
        (V ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
        (Work.Thom.Punct ↥W n)
        (fun x hx => hx) ℤ n).hom (Work.Thom.Mpun n ↥W)
      = (Work.Thom.relCohMap V (V ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) (fun x hx => hx) ℤ n).hom
        (Work.ThomBordism.stdModelGen n) := by
  classical
  set SS : Set X := V ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) with hSS
  -- the constant base map `↥W → PUnit`
  set cst : C(↥W, PUnit) := ⟨fun _ => PUnit.unit, continuous_const⟩ with hcst
  set bm : C(↥W × EuclideanSpace ℝ (Fin n), PUnit × EuclideanSpace ℝ (Fin n)) :=
    ⟨fun p => (cst p.1, p.2), cst.continuous.comp continuous_fst |>.prodMk continuous_snd⟩ with hbm
  -- `Mpun` over `↥W` is the pullback of `Mpun` over `PUnit`
  have hMpun : Work.Thom.Mpun n ↥W
      = (Work.Thom.relCohMap bm (Work.Thom.Punct ↥W n) (Work.Thom.Punct PUnit n)
          (fun _ hp => hp) ℤ n).hom (Work.Thom.Mpun n PUnit) :=
    (Work.Thom.Mpun_natural_map (n := n) cst).symm
  -- the two maps
  set pv : C(X, ↥W × EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x => (P x, V x), P.continuous.prodMk V.continuous⟩ with hpv
  set wv : C(X, PUnit × EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x => (PUnit.unit, V x), continuous_const.prodMk V.continuous⟩ with hwv
  have hcomp : bm.comp pv = wv := by
    apply ContinuousMap.ext; intro x; rfl
  have hpsi2 : wv = (psiUnit n).comp V := by
    apply ContinuousMap.ext; intro x; rfl
  -- the chain of pullbacks
  rw [show (Work.Thom.relCohMap pv SS (Work.Thom.Punct ↥W n) (fun x hx => hx) ℤ n).hom
        (Work.Thom.Mpun n ↥W)
      = (Work.Thom.relCohMap pv SS (Work.Thom.Punct ↥W n) (fun x hx => hx) ℤ n).hom
        ((Work.Thom.relCohMap bm (Work.Thom.Punct ↥W n) (Work.Thom.Punct PUnit n)
          (fun _ hp => hp) ℤ n).hom (Work.Thom.Mpun n PUnit)) from
    congrArg (fun y => (Work.Thom.relCohMap pv SS (Work.Thom.Punct ↥W n)
      (fun x hx => hx) ℤ n).hom y) hMpun]
  rw [show (Work.Thom.relCohMap pv SS (Work.Thom.Punct ↥W n) (fun x hx => hx) ℤ n).hom
        ((Work.Thom.relCohMap bm (Work.Thom.Punct ↥W n) (Work.Thom.Punct PUnit n)
          (fun _ hp => hp) ℤ n).hom (Work.Thom.Mpun n PUnit))
      = (Work.Thom.relCohMap (bm.comp pv) SS (Work.Thom.Punct PUnit n)
          (fun x hx => hx) ℤ n).hom (Work.Thom.Mpun n PUnit) from
    Work.Thom.relCohMap_compA_apply SS (Work.Thom.Punct ↥W n) (Work.Thom.Punct PUnit n) pv bm
      (fun x hx => hx) (fun _ hp => hp) (fun x hx => hx) ℤ n (Work.Thom.Mpun n PUnit)]
  rw [show (Work.Thom.relCohMap (bm.comp pv) SS (Work.Thom.Punct PUnit n)
        (fun x hx => hx) ℤ n) = Work.Thom.relCohMap wv SS (Work.Thom.Punct PUnit n)
        (fun x hx => hx) ℤ n from
    Work.Thom.relCohMap_congrA SS (Work.Thom.Punct PUnit n) hcomp
      (fun x hx => hx) (fun x hx => hx) ℤ n]
  rw [show (Work.Thom.relCohMap wv SS (Work.Thom.Punct PUnit n) (fun x hx => hx) ℤ n)
      = Work.Thom.relCohMap ((psiUnit n).comp V) SS (Work.Thom.Punct PUnit n)
        (fun x hx => hx) ℤ n from
    Work.Thom.relCohMap_congrA SS (Work.Thom.Punct PUnit n) hpsi2
      (fun x hx => hx) (fun x hx => hx) ℤ n]
  -- the right-hand side
  rw [stdModelGen_eq_pullback n]
  rw [show (Work.Thom.relCohMap V SS ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
        (fun x hx => hx) ℤ n).hom
        ((Work.Thom.relCohMap (psiUnit n) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
          (Work.Thom.Punct PUnit n) (fun v hv => hv) ℤ n).hom (Work.Thom.Mpun n PUnit))
      = (Work.Thom.relCohMap ((psiUnit n).comp V) SS (Work.Thom.Punct PUnit n)
          (fun x hx => hx) ℤ n).hom (Work.Thom.Mpun n PUnit) from
    (Work.Thom.relCohMap_compA_apply SS ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
      (Work.Thom.Punct PUnit n) V (psiUnit n) (fun x hx => hx) (fun v hv => hv)
      (fun x hx => hx) ℤ n (Work.Thom.Mpun n PUnit))]

end

end Work.ThomBordism.KeyLocal
