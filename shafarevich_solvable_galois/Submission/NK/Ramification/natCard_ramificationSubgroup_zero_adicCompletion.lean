import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.CommonsBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.Ramification

/-- **The zeroth higher ramification subgroup of a local field extension has order the
ramification index.**

Let `L / K` be a finite Galois extension of number fields, `Q` a height one prime of `𝓞 K` and `q`
a height one prime of `𝓞 L` lying over `Q`.  The `q`-adic completion `L_q` is then a finite Galois
extension of the `Q`-adic completion `K_Q` with Galois group the whole decomposition subgroup of
`q.adicCompletionIntegers L` (the decomposition subgroup of the valuation ring of a finite local
extension is everything, `decompositionSubgroup_adicCompletionIntegers_eq_top`), and the zeroth
higher ramification subgroup `G_0` — the inertia subgroup `I(L_q/K_Q)`, consisting of the elements
acting trivially on the residue field — has order the ramification index `e(q|Q)`.

This is the local statement used in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
Theorem 12.2.1: `|G_0| = e`. -/
theorem natCard_ramificationSubgroup_zero_adicCompletion {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card ↥(NK.Ramification.ramificationSubgroup (K := Q.adicCompletion K)
        (q.adicCompletionIntegers L) 0) =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- The inertia subgroup of the local Galois group, as produced by the local field arithmetic.
  obtain ⟨I, hI, hIcard⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx
      Q q hq
  -- The decomposition subgroup of the valuation ring of the completion is everything, so the
  -- elements of `A.decompositionSubgroup (Q.adicCompletion K)` are exactly the elements of the
  -- local Galois group.
  have htop : (q.adicCompletionIntegers L).decompositionSubgroup (Q.adicCompletion K) = ⊤ :=
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_adicCompletionIntegers_eq_top
      Q q hq
  let ψ : (q.adicCompletionIntegers L).decompositionSubgroup (Q.adicCompletion K) ≃*
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    { toFun := fun σ => σ.1
      invFun := fun g => ⟨g, htop ▸ Subgroup.mem_top g⟩
      left_inv := fun σ => Subtype.ext rfl
      right_inv := fun g => rfl
      map_mul' := fun σ τ => rfl }
  -- The two subgroups are cut out by the same condition: acting trivially modulo the maximal
  -- ideal of the ring of integers, i.e. moving every element of `A` by an element of valuation
  -- `< 1`.
  have key : ∀ σ : (q.adicCompletionIntegers L).decompositionSubgroup (Q.adicCompletion K),
      σ ∈ NK.Ramification.ramificationSubgroup (K := Q.adicCompletion K)
          (q.adicCompletionIntegers L) 0 ↔ ψ σ ∈ I := by
    intro σ
    rw [hI]
    simp only [NK.Ramification.mem_ramificationSubgroup_iff, zero_add, pow_one]
    apply forall_congr'
    intro x
    rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one q]
    rw [show ((σ • x - x : ↥(q.adicCompletionIntegers L)) : q.adicCompletion L) =
        (ψ σ) ↑x - ↑x from by
      change ((σ • x : ↥(q.adicCompletionIntegers L)) : q.adicCompletion L) - ↑x = (ψ σ) ↑x - ↑x
      rw [NK.Ramification.coe_smul]
      rfl]
  have hmap : Subgroup.map ψ.toMonoidHom
      (ramificationSubgroup (K := Q.adicCompletion K) (q.adicCompletionIntegers L) 0) = I := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (key x).mp hx
    · intro hy
      refine ⟨ψ.symm y, ?_, ?_⟩
      · rw [key]
        simpa using hy
      · simp
  calc Nat.card ↥(ramificationSubgroup (K := Q.adicCompletion K)
          (q.adicCompletionIntegers L) 0)
      = Nat.card ↥(Subgroup.map ψ.toMonoidHom
          (ramificationSubgroup (K := Q.adicCompletion K)
            (q.adicCompletionIntegers L) 0)) :=
        Nat.card_congr (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).toEquiv
    _ = Nat.card ↥I := by rw [hmap]
    _ = q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) := hIcard

end NK.Ramification
