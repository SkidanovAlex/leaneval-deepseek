import Mathlib
import Submission.NK.LocalReciprocity.LocalSetup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocity

/-- **Uniqueness of the local Frobenius.**

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` and `q` a
place of `L` above `Q` which is *unramified* over `Q` (`e(q|Q) = 1`).  Then there is at most one
`K_Q`-algebra automorphism `σ` of the local field `L_q = q.adicCompletion L` satisfying the
Frobenius congruence `σ x ≡ x ^ #k_Q (mod 𝔪)` on the ring of integers.

The proof: `σ' σ⁻¹` acts trivially on the residue field of `L_q` (both `σ` and `σ'` act there by
the `#k_Q`-power map), hence lies in the inertia subgroup.  For an unramified extension the
inertia subgroup has order the ramification index `e(q|Q) = 1`
(`Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx`),
so it is trivial and `σ' σ⁻¹ = 1`. -/
theorem isFrobeniusLocal_unique {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    {σ σ' : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L}
    (h : NK.LocalReciprocity.IsFrobeniusLocal Q q σ)
    (h' : NK.LocalReciprocity.IsFrobeniusLocal Q q σ') : σ = σ' := by
  -- the inertia subgroup of `Gal(L_q / K_Q)`, characterised by triviality on the residue field
  obtain ⟨I, hI, hcard⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx
      Q q hq
  have hcard1 : Nat.card I = 1 := by rw [hcard, hunr]
  have hIbot : I = ⊥ := Subgroup.card_eq_one.mp hcard1
  -- `σ' σ⁻¹` acts trivially on the residue field
  have hres : ∀ x : q.adicCompletionIntegers L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        ((σ' * σ⁻¹) (x : q.adicCompletion L) - (x : q.adicCompletion L)) < 1 := by
    intro x
    -- `z = σ⁻¹ x` is again integral
    have hxO : σ⁻¹ (x : q.adicCompletion L) ∈ q.adicCompletionIntegers L :=
      (Commons.NumberTheory.NumberField.Completion.algEquiv_mem_adicCompletionIntegers_iff_adicCompletion
        Q q hq σ⁻¹ (x : q.adicCompletion L)).mpr x.2
    let z : q.adicCompletionIntegers L := ⟨σ⁻¹ (x : q.adicCompletion L), hxO⟩
    have h1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (σ' (z : q.adicCompletion L) -
          (z : q.adicCompletion L) ^ NK.LocalReciprocity.residueCard K Q) < 1 := h' z
    have h2 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (σ (z : q.adicCompletion L) -
          (z : q.adicCompletion L) ^ NK.LocalReciprocity.residueCard K Q) < 1 := h z
    -- both `σ' z` and `σ z` are congruent to `z ^ #k_Q`
    have heq : (σ' * σ⁻¹) (x : q.adicCompletion L) - (x : q.adicCompletion L)
        = (σ' (z : q.adicCompletion L) -
            (z : q.adicCompletion L) ^ NK.LocalReciprocity.residueCard K Q)
          - (σ (z : q.adicCompletion L) -
            (z : q.adicCompletion L) ^ NK.LocalReciprocity.residueCard K Q) := by
      have hz : (z : q.adicCompletion L) = σ⁻¹ (x : q.adicCompletion L) := rfl
      rw [hz, AlgEquiv.mul_apply]
      rw [show σ (σ⁻¹ (x : q.adicCompletion L)) = (x : q.adicCompletion L) by simp]
      ring
    rw [heq]
    exact Valuation.map_sub_lt
      (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))) h1 h2
  have hmem : σ' * σ⁻¹ ∈ I := (hI _).mpr hres
  have hbot : σ' * σ⁻¹ = 1 := Subgroup.mem_bot.mp (hIbot ▸ hmem)
  exact (mul_inv_eq_one.mp hbot).symm

end NK.LocalReciprocity
