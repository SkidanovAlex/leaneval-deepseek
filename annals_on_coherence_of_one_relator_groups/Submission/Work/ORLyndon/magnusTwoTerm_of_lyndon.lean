import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.Magnus
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.ORLyndon.MagnusTwoTermDefs
import Submission.Work.ORLyndon.lyndonDelta_range_eq_augIdeal
import Submission.Work.ORLyndon.lyndon_exact_relationModuleMap
import Submission.Work.ORLyndon.relationModuleMap_injective
import Submission.Work.ORLyndon.foxD_pow
import Submission.Work.ORLyndon.relatorVec_t
import Submission.Work.ORLyndon.deltaYY_injective
import Submission.Work.ORLyndon.deltaYY_range
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.ORFP2.augIdeal_freeGroup_injective

namespace Work.ORLyndon

open MonoidAlgebra

noncomputable def magnusTwoTerm_of_lyndon {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (Y : Finset X) (t : X) (ht : t ∉ Y)
    (hY : ∀ x : X, x ∉ Y → x = t) {r u : FreeGroup X} {l : ℕ}
    (hcr : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hnotmem : r ∉ Subgroup.closure (FreeGroup.of '' (Y : Set X)))
    (h : Work.ORLyndon.LyndonIdentity K X r u l) :
    Work.ORLyndon.MagnusTwoTermExact K (Subgroup.closure (PresentedGroup.of '' (Y : Set X)))
      (Work.ORLyndon.presentRho r u) l
      ((Work.ORLyndon.presentAlg K r) (Work.ORLyndon.foxD (K := K) t u)) := by
  classical
  set A : Subgroup (OneRelatorGroup r) :=
    Subgroup.closure (PresentedGroup.of '' (Y : Set X)) with hA
  set β : MonoidAlgebra K (OneRelatorGroup r) :=
    (presentAlg K r) (foxD (K := K) t u) with hβ
  -- Freiheitssatz: `A` is free on the images of `Y`
  have hinj : Function.Injective (Work.OROneRel.presentedGroupMap r (Y : Set X)) :=
    Work.OROneRel.freiheitssatz_at r hcr (Y : Set X) hnotmem
  have hinjYY : Function.Injective (deltaYY (K := K) Y r) :=
    deltaYY_injective Y r hinj
  have hrangeYY : LinearMap.range (deltaYY (K := K) Y r) =
      (augIdealIn K A : Submodule (MonoidAlgebra K (OneRelatorGroup r))
        (MonoidAlgebra K (OneRelatorGroup r))) :=
    deltaYY_range Y r
  have hrel : relatorVec K r t = normElem K l (presentRho r u) * β :=
    relatorVec_t h t
  -- restriction of `X`-indexed families to `Y` is surjective (an embedding followed by it is
  -- the identity)
  have hsd_emb : ∀ c : (Y : Set X) →₀ MonoidAlgebra K (OneRelatorGroup r),
      subtypeDomainLM (K := K) Y r
        (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ c) = c := by
    intro c
    apply Finsupp.ext
    intro y
    rw [subtypeDomainLM_apply]
    exact Finsupp.embDomain_apply_self _ c y
  -- a vector vanishes if its restriction to `Y` does and its `t`-value does
  have hvanishes : ∀ v : X →₀ MonoidAlgebra K (OneRelatorGroup r),
      subtypeDomainLM (K := K) Y r v = 0 → v t = 0 → v = 0 := by
    intro v hv hvt
    apply Finsupp.ext
    intro x
    by_cases hx : x ∈ Y
    · have h := congrArg (fun z : (Y : Set X) →₀ MonoidAlgebra K (OneRelatorGroup r) =>
          z ⟨x, hx⟩) hv
      rwa [subtypeDomainLM_apply] at h
    · rw [hY x hx]; exact hvt
  -- the middle isomorphism `K[G]^X ≃ I^G_A × K[G]`
  have hmem : ∀ v : X →₀ MonoidAlgebra K (OneRelatorGroup r),
      deltaYBar (K := K) Y r v ∈ augIdealIn K A := by
    intro v
    rw [deltaYBar_apply_def, ← hrangeYY]
    exact LinearMap.mem_range_self _ _
  let Ψfun : (X →₀ MonoidAlgebra K (OneRelatorGroup r)) →
      (↥(augIdealIn K A) × MonoidAlgebra K (OneRelatorGroup r)) :=
    fun v => (⟨deltaYBar (K := K) Y r v, hmem v⟩, v t)
  have hΨ_add : ∀ v w, Ψfun (v + w) = Ψfun v + Ψfun w := by
    intro v w
    apply Prod.ext
    · apply Subtype.ext
      simp only [Ψfun, Submodule.coe_add, Submodule.coe_mk, map_add, Prod.fst_add]
    · simp only [Ψfun, Finsupp.add_apply, Prod.snd_add]
  have hΨ_smul : ∀ (c : MonoidAlgebra K (OneRelatorGroup r))
      (v : X →₀ MonoidAlgebra K (OneRelatorGroup r)), Ψfun (c • v) = c • Ψfun v := by
    intro c v
    apply Prod.ext
    · apply Subtype.ext
      simp only [Ψfun, Submodule.coe_smul, Submodule.coe_mk, map_smul, Prod.smul_fst]
    · simp only [Ψfun, Finsupp.smul_apply, Prod.smul_snd]
  let Ψ : (X →₀ MonoidAlgebra K (OneRelatorGroup r)) →ₗ[MonoidAlgebra K (OneRelatorGroup r)]
      (↥(augIdealIn K A) × MonoidAlgebra K (OneRelatorGroup r)) :=
    { toFun := Ψfun
      map_add' := hΨ_add
      map_smul' := hΨ_smul }
  have Psi_fst : ∀ v : X →₀ MonoidAlgebra K (OneRelatorGroup r),
      ((Ψ v).1 : MonoidAlgebra K (OneRelatorGroup r)) = deltaYBar (K := K) Y r v :=
    fun v => rfl
  have Psi_snd : ∀ v : X →₀ MonoidAlgebra K (OneRelatorGroup r), (Ψ v).2 = v t :=
    fun v => rfl
  have hPsi_bij : Function.Bijective Ψ := by
    constructor
    · intro v w hvw
      have h3 : subtypeDomainLM (K := K) Y r v = subtypeDomainLM (K := K) Y r w :=
        hinjYY (by
          change deltaYBar (K := K) Y r v = deltaYBar (K := K) Y r w
          rw [← Psi_fst v, ← Psi_fst w]
          exact congrArg (fun z =>
            ((z.1 : ↥(augIdealIn K A)) : MonoidAlgebra K (OneRelatorGroup r))) hvw)
      have h2 : v t = w t := by
        rw [← Psi_snd v, ← Psi_snd w]
        exact congrArg Prod.snd hvw
      exact sub_eq_zero.mp (hvanishes (v - w) (by rw [map_sub, h3, sub_self]) (by
        rw [Finsupp.sub_apply, h2, sub_self]))
    · rintro ⟨α, b⟩
      have hα : (α : MonoidAlgebra K (OneRelatorGroup r)) ∈
          LinearMap.range (deltaYY (K := K) Y r) := by
        rw [hrangeYY]; exact α.2
      obtain ⟨c, hc⟩ := hα
      refine ⟨Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ c
        + Finsupp.single t (b - (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ c) t),
        ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change deltaYY (K := K) Y r
            (subtypeDomainLM (K := K) Y r
              (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ c
                + Finsupp.single t
                    (b - (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ c) t)))
          = (α : MonoidAlgebra K (OneRelatorGroup r))
        rw [map_add, hsd_emb c, subtypeDomainLM_single_t Y ht r, add_zero, hc]
      · change (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ c
            + Finsupp.single t
                (b - (Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ c) t)) t = b
        rw [Finsupp.add_apply, Finsupp.single_eq_same, add_sub_cancel]
  let Ψe : (X →₀ MonoidAlgebra K (OneRelatorGroup r)) ≃ₗ[MonoidAlgebra K (OneRelatorGroup r)]
      (↥(augIdealIn K A) × MonoidAlgebra K (OneRelatorGroup r)) :=
    LinearEquiv.ofBijective Ψ hPsi_bij
  let γ : relationModule K r u →ₗ[MonoidAlgebra K (OneRelatorGroup r)]
      (↥(augIdealIn K A) × MonoidAlgebra K (OneRelatorGroup r)) :=
    Ψe.toLinearMap.comp (relationModuleMap K r u l h)
  let π : (↥(augIdealIn K A) × MonoidAlgebra K (OneRelatorGroup r)) →ₗ[
      MonoidAlgebra K (OneRelatorGroup r)] ↥(augIdeal K (OneRelatorGroup r)) :=
    ((lyndonDelta (K := K) r).comp
      (Ψe.symm : (↥(augIdealIn K A) × MonoidAlgebra K (OneRelatorGroup r)) →ₗ[
        MonoidAlgebra K (OneRelatorGroup r)] (X →₀ MonoidAlgebra K (OneRelatorGroup r)))).codRestrict
      (augIdeal K (OneRelatorGroup r)) (fun x => by
        rw [← lyndonDelta_range_eq_augIdeal]
        exact LinearMap.mem_range_self _ _)
  have hγ : ∀ m : relationModule K r u, γ m = Ψe (relationModuleMap K r u l h m) :=
    fun m => rfl
  refine ⟨γ, π, ?_, ?_, ?_, ?_⟩
  · -- second component
    intro a
    show (γ (Submodule.Quotient.mk a)).2 = magnusSecond K l (presentRho r u) β a
    show (Ψe (relationModuleMap K r u l h (Submodule.Quotient.mk a))).2 = _
    rw [show relationModuleMap K r u l h (Submodule.Quotient.mk a) =
        lyndonTheta K r a from Submodule.liftQ_apply _ _ a,
      lyndonTheta_apply]
    show (a • relatorVec K r) t = magnusSecond K l (presentRho r u) β a
    rw [Finsupp.smul_apply, smul_eq_mul, hrel, magnusSecond_apply]
  · -- injectivity of `γ`
    intro x y hxy
    exact relationModuleMap_injective h (Ψe.injective hxy)
  · -- surjectivity of `π`
    intro y
    have hy : (y : MonoidAlgebra K (OneRelatorGroup r)) ∈
        LinearMap.range (lyndonDelta (K := K) r) := by
      rw [lyndonDelta_range_eq_augIdeal]; exact y.2
    obtain ⟨v, hv⟩ := hy
    refine ⟨Ψe v, ?_⟩
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact hv
  · -- `ker π = range γ`
    have hker : ∀ x : ↥(augIdealIn K A) × MonoidAlgebra K (OneRelatorGroup r),
        (x ∈ LinearMap.ker π) ↔ (Ψe.symm x ∈ LinearMap.ker (lyndonDelta (K := K) r)) := by
      intro x
      rw [LinearMap.mem_ker, LinearMap.mem_ker]
      constructor
      · intro hx
        have hx' := congrArg (fun z : ↥(augIdeal K (OneRelatorGroup r)) =>
          (z : MonoidAlgebra K (OneRelatorGroup r))) hx
        rwa [LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at hx'
      · intro hx
        apply Subtype.ext
        rw [LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
        exact hx
    have hrange : ∀ x : ↥(augIdealIn K A) × MonoidAlgebra K (OneRelatorGroup r),
        (x ∈ LinearMap.range γ) ↔
          (Ψe.symm x ∈ LinearMap.range (relationModuleMap K r u l h)) := by
      intro x
      rw [LinearMap.mem_range, LinearMap.mem_range]
      constructor
      · rintro ⟨m, rfl⟩
        refine ⟨m, ?_⟩
        change relationModuleMap K r u l h m = Ψe.symm (Ψe (relationModuleMap K r u l h m))
        exact (LinearEquiv.symm_apply_apply _ _).symm
      · rintro ⟨m, hm⟩
        refine ⟨m, ?_⟩
        change Ψe (relationModuleMap K r u l h m) = x
        rw [hm, LinearEquiv.apply_symm_apply]
    ext x
    rw [hker x, hrange x, lyndon_exact_relationModuleMap h]

end Work.ORLyndon
