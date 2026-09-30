import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.free_submodule_of_free_int
import Submission.Work.Cohomology.free_of_chain_retractions
import Submission.Work.Cohomology.singularChains_free
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Kronecker pairing `Hⁿ(X;ℤ) ⟶ Hom(Hₙ(X;ℤ), ℤ)` is bijective (degree-local form)

`Work.Cohomology.kronH_isIso` proves that the Kronecker pairing is bijective when *all* the integral
homology of `X` is free.  The applications in this development (the universal coefficient theorem
for range models, where only the low degrees are controlled) need the *degree-local* statement: in
degree `n` it is enough that `H_k(X;ℤ)` be free for `k < n` — indeed only `H_{n-1}(X;ℤ)` matters,
because the kernel of the pairing is `Ext(H_{n-1}(X;ℤ), ℤ)`.

The proof follows the strategy of `kronH_isIso`: the explicit dual universal coefficient
isomorphism `Work.Cohomology.uctDualEvalEquiv` (which computes the pairing as evaluation of a
cocycle on a cycle, `Work.Cohomology.uctDualEvalEquiv_apply_apply`) is bijective, and it agrees with
`kronH` on the classes of cocycles, hence everywhere.

The point that makes the local version work is that the retractions used to build
`uctDualEvalEquiv` — a retraction of `Cₙ` onto the cycles `Zₙ`, and one of `C_{n-1}` onto the
boundaries `B_{n-1} = im dₙ` — only need the *boundaries* to be projective, and boundaries are
submodules of the free chain modules, hence free (`free_submodule_of_free_int`); the single place
where the freeness of homology is used is `H_{n-1} = Z_{n-1}/B_{n-1}` for the retraction
`Z_{n-1} → B_{n-1}`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.K2Z

noncomputable section

/-- **The Kronecker pairing is bijective in degree `n` as soon as the integral homology below
degree `n` is free.** -/
theorem kronH_bij (X : Type) [TopologicalSpace X] (n : ℕ)
    (hfree : ∀ k : ℕ, k < n → Module.Free ℤ (Work.Pi6.HR ℤ X k)) :
    Function.Bijective (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of X)) n) := by
  classical
  let E := Work.Cohomology.singularChains ℤ (TopCat.of X)
  -- the chain modules of `E` are free, hence so are all submodules of them
  have hEfree : ∀ m : ℕ, Module.Free ℤ ↥(E.X m) := fun m =>
    Work.Cohomology.singularChains_free (TopCat.of X) m
  have hBfree : ∀ m : ℕ, Module.Free ℤ ↥(Work.Cohomology.uctB E m) := by
    intro m
    haveI : Module.Free ℤ ↥(E.X m) := hEfree m
    exact Work.Cohomology.Module.Free.of_module_eq
      (Work.Cohomology.free_submodule_of_free_int (Work.Cohomology.uctB E m))
  have hRfree : ∀ m : ℕ, Module.Free ℤ ↥(Work.Cohomology.uctR E m) := by
    intro m
    haveI : Module.Free ℤ ↥(E.X (m - 1)) := hEfree (m - 1)
    exact Work.Cohomology.Module.Free.of_module_eq
      (Work.Cohomology.free_submodule_of_free_int (Work.Cohomology.uctR E m))
  -- `H_k = Z_k ⧸ B_k` is projective for `k < n`
  have hHproj : ∀ k : ℕ, k < n → Module.Projective ℤ
      (↥(Work.Cohomology.uctZ E k) ⧸ Work.Cohomology.uctH E k) := by
    intro k hk
    obtain ⟨ek⟩ := Work.Cohomology.homology_iso_H E k
    haveI : Module.Free ℤ ↥(E.homology k) := hfree k hk
    exact Module.Projective.of_equiv' (Work.Cohomology.uctIsoToLinearEquiv ek)
  -- `C_n` retracts onto the cycles (only the boundaries `B_{n-1}` must be projective)
  have hZ : ∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(Work.Cohomology.uctZ E n),
      ρ ∘ₗ (Work.Cohomology.uctZ E n).subtype = LinearMap.id := by
    haveI : Module.Free ℤ ↥(Work.Cohomology.uctR E n) := hRfree n
    exact Work.Cohomology.exists_retraction_cycles E n Module.Projective.of_free
  -- `C_{n-1}` retracts onto the boundaries `B_{n-1} = im dₙ` (needs `H_{n-1}` projective)
  have hR : ∃ r : ↥(E.X (n - 1)) →ₗ[ℤ] ↥(Work.Cohomology.uctR E n),
      r ∘ₗ (Work.Cohomology.uctR E n).subtype = LinearMap.id := by
    rcases n with _ | m
    · rw [Work.Cohomology.uctR_zero]
      exact Work.Cohomology.exists_retraction_bot
    · haveI : Module.Free ℤ ↥(Work.Cohomology.uctR E m) := hRfree m
      haveI : Module.Projective ℤ
          (↥(Work.Cohomology.uctZ E m) ⧸ Work.Cohomology.uctH E m) :=
        hHproj m (Nat.lt_succ_self m)
      exact Work.Cohomology.exists_retraction_bounds E m Module.Projective.of_free ‹_›
  -- the explicit dual universal coefficient isomorphism
  let e := Work.Cohomology.uctDualEvalEquiv E n hZ hR
  have he : ∀ (z : ↥((Work.Cohomology.dualComplex ℤ E).cycles n)) (c : ↥(E.cycles n)),
      e (((Work.Cohomology.dualComplex ℤ E).homologyπ n).hom z) ((E.homologyπ n).hom c)
        = Work.Cohomology.dval E n (((Work.Cohomology.dualComplex ℤ E).iCycles n).hom z)
            ((E.iCycles n).hom c) :=
    Work.Cohomology.uctDualEvalEquiv_apply_apply E n hZ hR
  -- `kronH` agrees with `e` on the classes of cocycles, hence on all of `Hⁿ`
  have hkr : ∀ y : ↥((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homology n),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of X)) n y = e y := by
    intro y
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homologyπ n)).mp
        inferInstance y
    apply LinearMap.ext
    intro v
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homologyπ n)).mp
        inferInstance v
    have hα : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj (TopCat.of X)) n w) = 0 := by
      simp only [Work.Cohomology.cochainOfCycle]
      exact Work.Cohomology.cochainDiff_iCycles ℤ (TopCat.toSSet.obj (TopCat.of X)) n w
    have hcyc : Work.Cohomology.cocycleOf ℤ (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj (TopCat.of X)) n w) hα = w := by
      apply Work.Cohomology.iCycles_injective ℤ (TopCat.toSSet.obj (TopCat.of X)) n
      rw [Work.Cohomology.iCycles_cocycleOf]
      simp only [Work.Cohomology.cochainOfCycle]
    have hcls : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homologyπ n w
        = Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X))
            (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj (TopCat.of X)) n w) hα := by
      show (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homologyπ n w
        = (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homologyπ n
            (Work.Cohomology.cocycleOf ℤ (TopCat.toSSet.obj (TopCat.of X))
              (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj (TopCat.of X)) n w) hα)
      rw [hcyc]
    have h1 : (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of X)) n
            ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homologyπ n w))
          ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homologyπ n c)
        = (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj (TopCat.of X)) n w)
            ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of X))).iCycles n c) := by
      rw [hcls, Work.Cohomology.kronH_apply ℤ (TopCat.toSSet.obj (TopCat.of X))
            (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj (TopCat.of X)) n w) hα c]
    have h2 : e ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homologyπ n w)
          ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of X))).homologyπ n c)
        = (Work.Cohomology.cochainOfCycle ℤ (TopCat.toSSet.obj (TopCat.of X)) n w)
            ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of X))).iCycles n c) := he w c
    exact h1.trans h2.symm
  have hbij : Function.Bijective
      (fun α : ↥((Work.Cohomology.cochainC ℤ
          (TopCat.toSSet.obj (TopCat.of X))).homology n) =>
        Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of X)) n α) := by
    rw [funext hkr]
    exact e.bijective
  exact hbij

end

end Work.Pi6.K2Z
