import Mathlib
import Submission.NK.ChebotarevGeneral.Basic
import Submission.NK.ChebotarevGeneral.summable_zetaWeight_of_inertiaDeg_ge_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ChebotarevGeneral

open NumberField IsDedekindDomain
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-- Only finitely many primes of `M` lie above a fixed prime of `K` (universe-polymorphic form). -/
private theorem finite_setOf_liesOver_aux {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] (𝔭 : NK.Chebotarev.PrimeIdeal K) :
    {𝒬 : NK.Chebotarev.PrimeIdeal M | 𝒬.asIdeal.LiesOver 𝔭.asIdeal}.Finite := by
  have hfin : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers M)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot
  refine Set.Finite.of_finite_image (s := {𝒬 : NK.Chebotarev.PrimeIdeal M |
      𝒬.asIdeal.LiesOver 𝔭.asIdeal}) (f := fun 𝒬 : NK.Chebotarev.PrimeIdeal M => 𝒬.asIdeal)
    ?_ ?_
  · exact hfin.subset (by rintro _ ⟨𝒬, h𝒬, rfl⟩; exact ⟨inferInstance, h𝒬⟩)
  · intro 𝒬 _ 𝒬' _ h
    exact IsDedekindDomain.HeightOneSpectrum.ext h

theorem exists_bound_primeIdealZetaSum_of_inertiaDeg_or_mem_finite {K M : Type*} [Field K]
    [NumberField K] [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M]
    (A : Set (NK.Chebotarev.PrimeIdeal M)) (Bad : Set (NK.Chebotarev.PrimeIdeal K))
    (hBad : Bad.Finite) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → NumberField.Set.primeIdealZetaSum
      {𝒬 : NK.Chebotarev.PrimeIdeal M | 𝒬 ∈ A ∧
        (2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal ∨
          IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬 ∈ Bad)} s ≤ C := by
  classical
  -- the primes of `M` of residue degree at least `2` over `K`
  set T : Set (NK.Chebotarev.PrimeIdeal M) :=
    {𝒬 | 2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal} with hT
  -- the primes of `M` lying above a bad prime of `K`
  set BadM : Set (NK.Chebotarev.PrimeIdeal M) :=
    {𝒬 | IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬 ∈ Bad}
    with hBadM
  -- the latter form a finite set
  have hBadMfin : BadM.Finite := by
    have h' : (⋃ 𝔭 ∈ Bad, {𝒬 : NK.Chebotarev.PrimeIdeal M |
        IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬 = 𝔭}).Finite := by
      refine hBad.biUnion (fun 𝔭 _ => ?_)
      refine (finite_setOf_liesOver_aux (K := K) (M := M) 𝔭).subset ?_
      intro 𝒬 h𝒬
      simp only [Set.mem_ofPred_eq] at h𝒬 ⊢
      rw [Ideal.liesOver_iff, ← h𝒬, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    refine h'.subset ?_
    intro 𝒬 h𝒬
    rw [hBadM] at h𝒬
    exact Set.mem_iUnion₂.mpr ⟨_, h𝒬, rfl⟩
  refine ⟨NumberField.Set.primeIdealZetaSum T 1 + (BadM.ncard : ℝ), ?_⟩
  intro s hs
  -- summability of the residue-degree-`≥ 2` part, at exponent `1` and at exponent `s`
  have hdeg : ∀ 𝒬 : T, 2 ≤ (Ideal.under (NumberField.RingOfIntegers K)
      𝒬.1.asIdeal).inertiaDeg' 𝒬.1.asIdeal := by
    intro 𝒬
    simpa only [hT, Set.mem_ofPred_eq] using 𝒬.2
  have hTs : Summable fun 𝒬 : T => (Ideal.absNorm 𝒬.1.asIdeal : ℝ) ^ (-s) :=
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := M) hs).subtype T
  have hT1 : Summable fun 𝒬 : T => (Ideal.absNorm 𝒬.1.asIdeal : ℝ) ^ (-(1 : ℝ)) := by
    have h := summable_zetaWeight_of_inertiaDeg_ge_two (K := K) (M := M) (s := (1 : ℝ))
      (by norm_num)
    refine (h.subtype T).congr (fun 𝒬 => ?_)
    simp only [Function.comp_apply, hdeg 𝒬, if_true]
  -- the analogous summability for the bad part at exponent `s`
  have hBadTs : Summable fun 𝒬 : Set.diff BadM T =>
      (Ideal.absNorm 𝒬.1.asIdeal : ℝ) ^ (-s) :=
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := M) hs).subtype
      (Set.diff BadM T)
  -- the target set is contained in the union of the two pieces
  have hsub : {𝒬 : NK.Chebotarev.PrimeIdeal M | 𝒬 ∈ A ∧
      (2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal ∨
        IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬 ∈ Bad)}
      ⊆ T ∪ BadM := by
    intro 𝒬 h𝒬
    simp only [Set.mem_ofPred_eq] at h𝒬
    rcases h𝒬 with ⟨_, h | h⟩
    · exact Or.inl (by simpa only [hT, Set.mem_ofPred_eq] using h)
    · exact Or.inr (by simpa only [hBadM, Set.mem_ofPred_eq] using h)
  -- the bound on the residue-degree-`≥ 2` part: compare with the exponent `1`
  have hTbound : NumberField.Set.primeIdealZetaSum T s ≤ NumberField.Set.primeIdealZetaSum T 1 := by
    rw [NumberField.Set.primeIdealZetaSum_def, NumberField.Set.primeIdealZetaSum_def]
    refine Summable.tsum_le_tsum (fun 𝒬 => ?_) hTs hT1
    have h1 : (1 : ℝ) ≤ (Ideal.absNorm 𝒬.1.asIdeal : ℝ) := by
      have hne : Ideal.absNorm 𝒬.1.asIdeal ≠ 0 := fun h0 =>
        𝒬.1.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  -- the bound on the bad part: only finitely many primes
  have hBadbound : NumberField.Set.primeIdealZetaSum (Set.diff BadM T) s ≤ (BadM.ncard : ℝ) := by
    calc NumberField.Set.primeIdealZetaSum (Set.diff BadM T) s
        ≤ NumberField.Set.primeIdealZetaSum BadM s :=
          Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_mono Set.sdiff_subset hs
      _ ≤ (BadM.ncard : ℝ) :=
          NumberField.Set.primeIdealZetaSum_le_card_of_finite hBadMfin
            (le_of_lt (lt_trans zero_lt_one hs))
  -- split the union into its two disjoint pieces
  have hunion : NumberField.Set.primeIdealZetaSum (T ∪ BadM) s =
      NumberField.Set.primeIdealZetaSum T s +
        NumberField.Set.primeIdealZetaSum (Set.diff BadM T) s := by
    rw [← Set.union_sdiff_self (s := T) (t := BadM)]
    exact Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint
      (disjoint_sdiff_self_right (x := T) (y := BadM)) s hTs hBadTs
  have hmono : NumberField.Set.primeIdealZetaSum
      {𝒬 : NK.Chebotarev.PrimeIdeal M | 𝒬 ∈ A ∧
        (2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal ∨
          IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬 ∈ Bad)} s
      ≤ NumberField.Set.primeIdealZetaSum (T ∪ BadM) s :=
    Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_mono hsub hs
  calc NumberField.Set.primeIdealZetaSum
        {𝒬 : NK.Chebotarev.PrimeIdeal M | 𝒬 ∈ A ∧
          (2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal ∨
            IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬 ∈ Bad)} s
      ≤ NumberField.Set.primeIdealZetaSum (T ∪ BadM) s := hmono
    _ = NumberField.Set.primeIdealZetaSum T s +
          NumberField.Set.primeIdealZetaSum (Set.diff BadM T) s := hunion
    _ ≤ NumberField.Set.primeIdealZetaSum T 1 + (BadM.ncard : ℝ) := add_le_add hTbound hBadbound

end

end NK.ChebotarevGeneral
