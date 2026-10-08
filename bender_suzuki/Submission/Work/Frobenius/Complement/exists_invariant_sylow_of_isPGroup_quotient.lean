import Mathlib
import Submission.Work.Coprime.glauberman_exists_fixed

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An `A`-invariant Sylow subgroup from an `M`-invariant one

Let `A` be a finite solvable group acting by automorphisms on a finite group `N`, with
`Nat.card A` coprime to `Nat.card N`.  If `M ⊴ A` and `P` is a Sylow `r`-subgroup of `N`
invariant under `M` (and `A ⧸ M` has prime order `q`), then there is a Sylow `r`-subgroup of
`N` invariant under all of `A`.

This is the induction step of the coprime-action theorem (a solvable group of automorphisms of
coprime order leaves a Sylow subgroup invariant).  Rather than reproduce the classical group
theoretic argument we invoke the stronger and already formalised Glauberman fixed point lemma
`Work.Coprime.glauberman_exists_fixed`, applied to the compatible `A`- and `N`-actions on the
set `Sylow r N`: `N` acts by conjugation and acts transitively (Sylow conjugacy), `A` acts
through the given `MulDistribMulAction`, and the two actions are compatible because `A` acts by
automorphisms.  The extra hypothesis that `P` is `M`-invariant is therefore not needed, but the
statement is kept as requested so that the induction in
`Work.Frobenius.Complement.exists_invariant_sylow_of_isSolvable` can consume it verbatim.
-/

open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Frobenius.Complement

theorem exists_invariant_sylow_of_isPGroup_quotient {A N : Type*} [Group A] [Group N] [Finite A] [Finite N]
    [MulDistribMulAction A N] (hsol : Group.IsSolvable A) (hcop : (Nat.card A).Coprime (Nat.card N))
    {r : ℕ} (hr : r.Prime) {M : Subgroup A} [M.Normal]
    {q : ℕ} (hq : q.Prime) (hqcard : Nat.card (A ⧸ M) = q) {P : Sylow r N}
    (hP : ∀ a : M, ∀ x : N, (x ∈ (P : Subgroup N) ↔ (a : A) • x ∈ (P : Subgroup N))) :
    ∃ P' : Sylow r N, ∀ a : A, ∀ x : N, (x ∈ (P' : Subgroup N) ↔ a • x ∈ (P' : Subgroup N)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  -- Glauberman's fixed point lemma on the transitive `N`-set `Sylow r N` with compatible
  -- `A`-action yields an `A`-invariant Sylow `r`-subgroup.
  obtain ⟨P', hP'⟩ := Work.Coprime.glauberman_exists_fixed A N (Sylow r N) hcop (Or.inl hsol)
    (fun a g ω => by
      -- compatibility: `a • (g • ω) = (a • g) • (a • ω)`
      apply Sylow.ext
      simp only [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul]
      ext x
      simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have key : (MulAut.conj g)⁻¹ • a⁻¹ • x = a⁻¹ • (MulAut.conj (a • g))⁻¹ • x := by
        simp only [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, smul_mul', smul_inv',
          inv_smul_smul]
      rw [key])
    (fun ω ω' => MulAction.exists_smul_eq N ω ω')
  refine ⟨P', fun a x => ?_⟩
  -- convert the pointwise invariance `a • P' = P'` into membership form
  have hmem : a • (P' : Subgroup N) = (P' : Subgroup N) := by
    have := congrArg (fun S : Sylow r N => (S : Subgroup N)) (hP' a)
    simpa only [Sylow.pointwise_smul_def] using this
  have hI : ∀ y : N, (y ∈ (P' : Subgroup N)) ↔ (a⁻¹ • y ∈ (P' : Subgroup N)) := by
    intro y
    rw [← Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := a) (S := (P' : Subgroup N)), hmem]
  rw [hI (a • x), inv_smul_smul]

end Work.Frobenius.Complement
