import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.Mu2ArithDeps
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Kummer dictionary at the base field (`μ₂`, completions)

`Work.ZDataTwo.kummerChar_eq_zero_iff_isSquare_completion`: for a number field `k`, an algebraic
closure `Ω` of `k`, a finite place `A` of `Ω` lying over the prime `Q` of `k`, a primitive square
root of unity `ζ ∈ k` and a unit `α ∈ kˣ`, the global Kummer character `σ ↦ σ(√α)/√α` of `α`
vanishes on the decomposition group `D_A ≤ G_k` exactly when `α` is a square in the completion
`k_Q`.

This is the "local Kummer dictionary" of the `μ₂` local Tate system
(`Submission/Work/SSGRoute/ZDataTwo/mu2LocalTateSystemWithArch.lean`), in the base-field form the
construction consumes: it identifies the kernel of the Kummer map `kˣ/(kˣ)² → H¹(G_k, μ₂)` on a
decomposition group with the group of local squares, which is what makes the local Hilbert symbol
`⟪α, β⟫_Q` depend only on the Kummer *classes* of `α` and `β`.

## Proof

`Work.SSGRoute.local_kummer_dictionary_two` is the same statement for a *finite* intermediate field
`K : IntermediateField k Ω` with `↥K` a number field; `↥k` is not literally an intermediate field
of `Ω` over `k`, so the argument is carried out directly at `k`.  Let `N := k(√α) ⊆ Ω`
(`NK.LocalAnabelian.kummerField`), a quadratic extension of `k`.  The character of `α` vanishes at
`σ` exactly when `σ` fixes the chosen square root `√α ∈ Ω`
(`Work.SSGRoute.kummerIdx_spec` / `kummerIdx_eq_zero_of_apply_eq`), i.e. exactly when `σ` lies in
`N.fixingSubgroup`.  Hence the left-hand side is `D_A ≤ G_N`, i.e. `A` splits completely in `N`.
Then

* `NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely` turns `D_A ≤ G_N` into
  "`Q` splits completely in `N`", i.e. into the count of primes of `N` above `Q`;
* `NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one` rewrites that as "every prime
  of `N` above `Q` has local degree `e·f = 1`";
* `NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff` identifies this with "`α` is a square in
  `k_Q`".

If `α` is a global square, then `N = ⊥` and both sides hold trivially
(`NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup`).
-/


set_option linter.style.haveILetI false

namespace Work.ZDataTwo

open scoped Pointwise IntermediateField

theorem kummerChar_eq_zero_iff_isSquare_completion {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω] (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    (α : kˣ) :
    ((∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A →
        Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α σ = 0) ↔
      ∃ d : (Q.adicCompletion k)ˣ,
        algebraMap k (Q.adicCompletion k) (α : k) =
          (d : Q.adicCompletion k) * (d : Q.adicCompletion k)) := by
  classical
  have : SSGRoute.IsFinPlace k A := hA
  haveI hsep : IsSepClosure k Ω := ⟨inferInstance, inferInstance⟩
  set N : IntermediateField k Ω := NK.LocalAnabelian.kummerField (K' := Ω) 2 α with hNdef
  haveI hfdN : FiniteDimensional k N :=
    NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (K' := Ω) Nat.prime_two hζ α
  haveI hnfN : NumberField ↥N := inferInstance
  -- the chosen square root of `α` and its defining property
  have hroot : (((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)) ^ 2 =
      algebraMap k Ω (α : k) := by
    simpa [Units.val_pow_eq_pow_val, Units.coe_map] using
      congrArg (fun u : Ωˣ => (u : Ω)) (Work.SSGRoute.kummerSqrt_pow (K := k) (Ω := Ω) α)
  have hNgen : N = k⟮(((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω))⟯ := by
    rw [hNdef]
    exact NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple 2 Nat.prime_two hζ α hroot
  have hmemN : (((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)) ∈ N := by
    rw [hNgen]
    exact IntermediateField.mem_adjoin_simple_self k _
  have hchar : ∀ σ : Ω ≃ₐ[k] Ω,
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α σ = 0 ↔ σ ∈ N.fixingSubgroup := by
    intro σ
    constructor
    · intro hσ
      have hfixα : σ (((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)) =
          ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω) := by
        have h1 := Work.SSGRoute.kummerIdx_spec 2 hζ α
          (Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α)
          (Work.SSGRoute.kummerSqrt_pow (K := k) (Ω := Ω) α) σ
        have h0 : Work.SSGRoute.kummerIdx 2 hζ α
            (Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α)
            (Work.SSGRoute.kummerSqrt_pow (K := k) (Ω := Ω) α) σ = 0 := hσ
        have hz0 : (Work.SSGRoute.zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot (E := Ω) 2 hζ))
            (Multiplicative.ofAdd (0 : ZMod 2)) = 1 := map_one _
        rw [h0, hz0] at h1
        have h1' : Work.Kummer.kummerRatio σ
            (Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α) = 1 := by
          simpa using h1
        have h2 : σ ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω) /
            ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω) = 1 := by
          rw [← Work.Kummer.kummerRatio_coe]
          exact congrArg (fun u : Ωˣ => (u : Ω)) h1'
        rw [div_eq_one_iff_eq (Units.ne_zero _)] at h2
        exact h2
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      rw [hNgen] at hx
      obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k x).mp hx
      rw [map_div₀,
        show σ ((Polynomial.aeval ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)) r) =
          (Polynomial.aeval (σ ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω))) r from
          (Polynomial.aeval_algHom_apply (σ : Ω →ₐ[k] Ω) _ r).symm,
        show σ ((Polynomial.aeval ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)) s) =
          (Polynomial.aeval (σ ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω))) s from
          (Polynomial.aeval_algHom_apply (σ : Ω →ₐ[k] Ω) _ s).symm,
        hfixα]
    · intro hσ
      refine Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq 2 hζ α
        (Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α)
        (Work.SSGRoute.kummerSqrt_pow (K := k) (Ω := Ω) α) σ ?_
      exact (IntermediateField.mem_fixingSubgroup_iff N σ).mp hσ _ hmemN
  rw [show (∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A →
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α σ = 0) ↔
      SSGRoute.IsSplitIn k N A from
    ⟨fun h σ hσ => (hchar σ).mp (h σ hσ), fun h σ hσ => (hchar σ).mpr (h hσ)⟩]
  by_cases ha : α ∈ NK.LocalAnabelian.powSubgroup 2 k
  · -- `α` is a global square: both sides are trivial
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (show α ∈ (powMonoidHom 2 : kˣ →* kˣ).range from ha)
    constructor
    · intro _
      refine ⟨Units.map (algebraMap k (Q.adicCompletion k)).toMonoidHom u, ?_⟩
      rw [show α = u ^ 2 from hu.symm, Units.val_pow_eq_pow_val, Units.coe_map, map_pow,
        pow_two]
      rfl
    · intro _
      have hbot : N = ⊥ := by
        rw [hNdef]
        exact NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) 2
          Nat.prime_two hζ ha
      have htop : N.fixingSubgroup = ⊤ := by
        rw [hbot]
        exact IntermediateField.fixingSubgroup_bot
      intro σ hσ
      rw [htop]
      exact Subgroup.mem_top σ
  · -- the generic case: `N/k` is a genuine quadratic Galois extension
    haveI hNgal : IsGalois k N :=
      (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) 2 Nat.prime_two hζ α ha).1
    haveI hNnorm : Normal k N := inferInstance
    refine (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely (K := k) (K' := Ω)
      (N := N) Q A hQ).trans ?_
    refine (NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one (K := k) (L := ↥N)
      Q).trans ?_
    refine (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff (K := k) (K' := Ω) 2
      Nat.prime_two hζ α N hNdef Q).trans ?_
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, by simpa [pow_two] using hb⟩
    · rintro ⟨d, hd⟩
      exact ⟨d, by simpa [pow_two] using hd⟩

end Work.ZDataTwo
