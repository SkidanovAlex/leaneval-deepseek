import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.relCupH
import Submission.Work.Cohomology.uctDual
import Submission.Work.Cohomology.relChains_free
import Submission.Work.Cohomology.Sd_isSmallChain
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Whitney.relCycleKron
import Submission.Work.Cohomology.vk_relCup_ne_zero_of_relCapPair_ne_zero
import Submission.Work.Cohomology.smallChainSubmodule_eq_sup
import Submission.Work.Whitney.CycleDetect.exists_cycle_of_notMem_range
import Submission.Work.Whitney.CycleDetect.homologyClass_eq_zero_of_d_eq

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Whitney

/-- **The identification `Hom_ℤ(C_n(X,A),ℤ) ≅ C^n(X,A)` commutes with the differentials.**

This is the elementwise form of `Work.Cohomology.relDualIso_comm`: the relative differential of the
cochain corresponding to a functional is the cochain corresponding to the transposed differential
of the functional. -/
private lemma relDualEquiv_d_apply (X : TopCat) (A : Set X) (n : ℕ)
    (f : ↥((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).X n)) :
    (Work.Cohomology.relComplex ℤ X A).d n (n + 1)
        (Work.Cohomology.relDualEquiv X A n
          (show ↥((Work.Cohomology.relChains X A).X n) →ₗ[ℤ] ℤ from f))
      = Work.Cohomology.relDualEquiv X A (n + 1)
          (((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).d n (n + 1)).hom f) := by
  have h := congrArg
    (fun (g : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).X n ⟶
        (Work.Cohomology.relComplex ℤ X A).X (n + 1)) => g.hom f)
    (Work.Cohomology.relDualIso_comm X A n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
  simp only [LinearMap.comp_apply] at h
  exact h

/-- **A nonzero relative cohomology class is detected by a chain whose boundary lies in `A`.**

Let `X` be a topological space, `A ⊆ X`, and suppose `H_{n-1}(X,A) = 0` for some `n ≥ 1` (the
hypothesis killing the `Ext(H_{n-1}(X,A), ℤ)` summand of the universal coefficient theorem).  Then
every nonzero class `α ∈ H^n(X,A;ℤ)` is detected by a chain `B ∈ C_n(X)` whose boundary is carried
by `A`: for *every* relative cocycle `w` representing `α`, the Kronecker pairing `⟨w, B⟩` is
nonzero.

The chain `B` is a lift of a relative `n`-cycle `z` which detects `α` under the (Ext-free)
Kronecker pairing `H^n(X,A) × H_n(X,A) → ℤ`; its boundary is carried by `A` because `z` is a
relative cycle. -/
theorem exists_chain_relClassOf_ne_zero (X : TopCat) (A : Set X) (n : ℕ) (hn : 1 ≤ n)
    (hexact : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains X A).homology (n - 1)))
    (α : Work.Cohomology.relCohomology ℤ X A n) (hα : α ≠ 0) :
    ∃ B : (Work.Cohomology.singularChains ℤ X).X n,
      Work.Cohomology.IsSmallChain A (∅ : Set X)
        (((Work.Cohomology.singularChains ℤ X).d n (n - 1)) B) ∧
      ∀ (w : ↥(Work.Cohomology.relKern ℤ X A n))
        (hw : Work.Cohomology.relDiffLM ℤ X A n w = 0)
        (_hcl : Work.Cohomology.relClassOf ℤ X A w hw = α),
        Work.Cohomology.kronecker ℤ (TopCat.toSSet.obj X) w.1 B ≠ 0 := by
  rcases n with _ | k
  · exact absurd hn (by simp)
  simp only [Nat.succ_sub_one] at hexact ⊢
  -- A representative of `α` and the fact that it is not a coboundary.
  obtain ⟨a, ha, haα⟩ := Work.Cohomology.exists_relClassOf ℤ X A (k + 1) α
  have hclass : Work.Cohomology.relClassOf ℤ X A a ha ≠ 0 := by
    rw [haα]; exact hα
  have hnot2 := Work.Whitney.CycleDetect.notMem_range_relDiffLM_of_relClassOf_ne_zero X A k a ha
    hclass
  -- The cocycle of the dual complex corresponding to `a`.
  let φ : ↥((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).X (k + 1)) :=
    (Work.Cohomology.relDualEquiv X A (k + 1)).symm a
  have hφa : (Work.Cohomology.relDualEquiv X A (k + 1)) φ = a :=
    (Work.Cohomology.relDualEquiv X A (k + 1)).apply_symm_apply a
  -- `φ` is a cocycle.
  have hφd : ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).d
        (k + 1) (k + 1 + 1)).hom φ = 0 := by
    have h2 : (Work.Cohomology.relDualEquiv X A (k + 1 + 1))
        (((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).d
          (k + 1) (k + 1 + 1)).hom φ) = 0 := by
      rw [← relDualEquiv_d_apply X A (k + 1) φ, hφa, Work.Cohomology.relComplex_d]
      exact ha
    have h3 : (Work.Cohomology.relDualEquiv X A (k + 1 + 1))
        (((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).d
          (k + 1) (k + 1 + 1)).hom φ)
        = (Work.Cohomology.relDualEquiv X A (k + 1 + 1)) 0 := by
      rw [map_zero]
      exact h2
    exact (Work.Cohomology.relDualEquiv X A (k + 1 + 1)).injective h3
  -- `φ` is not a coboundary either.
  have hnot : ∀ ψ : ↥((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).X k),
      ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).d k (k + 1)).hom ψ
        ≠ φ := by
    intro ψ hψ
    apply hnot2
    refine ⟨(Work.Cohomology.relDualEquiv X A k) ψ, ?_⟩
    have h2 : (Work.Cohomology.relComplex ℤ X A).d k (k + 1)
        ((Work.Cohomology.relDualEquiv X A k) ψ) = a := by
      rw [relDualEquiv_d_apply X A k ψ, hψ, hφa]
    rw [Work.Cohomology.relComplex_d] at h2
    exact h2
  -- A relative cycle detecting the class
  obtain ⟨z, hzcyc, hzne⟩ :=
    Work.Whitney.CycleDetect.exists_cycle_of_notMem_range (Work.Cohomology.relChains X A) (k + 1)
      (by omega) (fun j => Work.Cohomology.relChains_free X A j) hexact φ hφd hnot
  -- A lift of `z` to a chain of `X`
  obtain ⟨B, hB⟩ := Work.Cohomology.relDualProj_surjective X A (k + 1) z
  -- its boundary is carried by `A`, since `z` is a relative cycle
  have hker : (Work.Cohomology.relDualProj X A k).hom
      (((Work.Cohomology.singularChains ℤ X).d (k + 1) k) B) = 0 := by
    rw [← LinearMap.comp_apply, ← Work.Cohomology.relDualProj_comm_lm X A k,
      LinearMap.comp_apply, hB]
    exact hzcyc
  have hmem : (((Work.Cohomology.singularChains ℤ X).d (k + 1) k) B) ∈
      LinearMap.range ((Work.Cohomology.inclChains X A).f k).hom := by
    rw [← Work.Cohomology.relDualProj_ker X A k, LinearMap.mem_ker]
    exact hker
  have hsmall : (((Work.Cohomology.singularChains ℤ X).d (k + 1) k) B) ∈
      Work.Cohomology.smallChainSubmodule A (∅ : Set X) k := by
    rw [Work.Cohomology.smallChainSubmodule_eq_sup A (∅ : Set X) k]
    exact Submodule.mem_sup_left hmem
  -- The pairing of the chosen representative with `B`
  have hpair : Work.Cohomology.kronecker ℤ (TopCat.toSSet.obj X) a.1 B
      = (Work.Cohomology.dval (Work.Cohomology.relChains X A) (k + 1) φ) z := by
    have h3 := congrArg
      (fun (g : ↥((Work.Cohomology.singularChains ℤ X).X (k + 1)) →ₗ[ℤ] ℤ) => g B)
      (Work.Cohomology.relDualEquiv_symm_comp X A (k + 1) a)
    simp only [LinearMap.comp_apply] at h3
    rw [hB] at h3
    show (show ↥((Work.Cohomology.singularChains ℤ X).X (k + 1)) →ₗ[ℤ] ℤ from a.1) B
      = (show ↥((Work.Cohomology.relChains X A).X (k + 1)) →ₗ[ℤ] ℤ from φ) z
    rw [h3]
    rfl
  refine ⟨B, hsmall, ?_⟩
  intro w hw hcl
  have hBnz : Work.Cohomology.kronecker ℤ (TopCat.toSSet.obj X) a.1 B ≠ 0 := by
    rw [hpair]
    exact hzne
  have ha' : ((Work.Cohomology.relComplex ℤ X A).d (k + 1) (k + 1 + 1)).hom a = 0 := by
    rw [Work.Cohomology.relComplex_d]; exact ha
  have hw' : ((Work.Cohomology.relComplex ℤ X A).d (k + 1) (k + 1 + 1)).hom w = 0 := by
    rw [Work.Cohomology.relComplex_d]; exact hw
  have hEq : (Work.Cohomology.relComplex ℤ X A).homologyπ (k + 1)
        (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℤ X A) (n := k + 1) a ha')
      = (Work.Cohomology.relComplex ℤ X A).homologyπ (k + 1)
        (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex ℤ X A) (n := k + 1) w hw') := by
    rw [← Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℤ X A a ha ha',
      ← Work.Cohomology.relClassOf_eq_homologyπ_cocycleOfK ℤ X A w hw hw', haα, hcl]
  have heq := Work.Cohomology.kronecker_relComplex_eq_of_homology_eq A k a w ha' hw' hEq B hsmall
  rw [← heq]
  exact hBnz

end Work.Whitney
