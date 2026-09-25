import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.Defs


open Filter NumberField
open scoped BigOperators Topology

namespace NK.GlobalCFTdeep.SecondInequality

-- Module `Submission.NK.GlobalCFTdeep.SecondInequality.card_le_finrank_of_bound`, namespace
-- `NK.GlobalCFTdeep.SecondInequality`, importing
-- `Submission.NK.GlobalCFTdeep.SecondInequality.Defs` (which defines `trivialClassSum`,
-- `splitCompletelySet` and proves `hasDirichletDensity_splitCompletelySet`, and brings in
-- `Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely` and
-- `Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_div_log`).
--
-- MATHEMATICS (Milne, Class Field Theory, Chapter VI, Theorem 4.9, the last step of the
-- analytic proof of the second inequality).  `hsub` says: every prime outside `S` that splits
-- completely in `L` has trivial class under `b`.  `hbound` is the analytic estimate
-- `|B| · ∑_{𝔭∉S, b𝔭=1} N𝔭^{-s} ≤ log (1/(s-1)) + C`.
--
-- The completely split primes have Dirichlet density `1/[L:K]`
-- (`hasDirichletDensity_splitCompletelySet`, proved from the shared library), i.e.
-- `∑_{split} N𝔭^{-s} / log (1/(s-1)) → 1/[L:K]`.  Since the split primes outside `S` are among
-- the primes with `b 𝔭 = 1`, and the primes of `S` contribute at most `|S|` (each weight is `≤ 1`),
--   `|B| · ∑_{split} N𝔭^{-s} ≤ |B| · (∑_{b𝔭=1, 𝔭∉S} N𝔭^{-s} + |S|) ≤ log (1/(s-1)) + C + |B|·|S|`.
-- Dividing by `log (1/(s-1))` (positive for `s > 1`) and letting `s → 1⁺`, where
-- `log (1/(s-1)) → +∞`, gives `|B| · 1/[L:K] ≤ 1`, hence `|B| ≤ [L:K]`.
--
-- Useful ingredients: `Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_div_log`
-- (from a density statement to the limit of `∑ / log`),
-- `Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_le_card_of_finite`
-- (`∑_{𝔭∈S} N𝔭^{-s} ≤ |S|` for `s ≥ 0`), `tendsto_log_one_div_sub_one` (i.e.
-- `Real.log (1/(s-1)) → +∞`) and `le_of_tendsto_of_tendsto` / `Filter.Tendsto.le_of_tendsto`.

/-- `Real.log (1 / (s - 1)) → +∞` as `s → 1⁺`.  This is the analytic engine of the "divide and
pass to the limit" step: the additive constants become negligible after division by the
diverging logarithm. -/
lemma tendsto_log_one_div_sub_one_nhdsGT :
    Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  have h1a : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
    ((continuous_id.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).sub_const 1
  have h1b : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by simpa using h1a
  have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h1b, by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs ⊢
      linarith⟩
  have h2 : Tendsto (fun s : ℝ => (s - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun s : ℝ => Real.log ((s - 1)⁻¹)) (𝓝[>] (1 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp h2
  refine h3.congr' ?_
  filter_upwards with s
  rw [one_div]

/-- `Real.log (1 / (s - 1))` is positive for `s` close to `1` from the right (namely for
`1 < s < 2`).  This is what makes the division by `log (1/(s-1))` legitimate in the last step of
the proof of the second inequality. -/
lemma eventually_log_pos_one_div_sub_one :
    ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 0 < Real.log (1 / (s - 1)) := by
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs
  have hpos : 0 < s - 1 := by linarith [hs.1]
  have hlt : s - 1 < 1 := by linarith [hs.2]
  have h1 : 1 < 1 / (s - 1) := by
    rw [one_lt_div hpos]
    exact hlt
  exact Real.log_pos h1

theorem card_le_finrank_of_bound {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {B : Type*} [CommGroup B] [Fintype B] [DecidableEq B] (b : PrimeIdeal K → B)
    (S : Finset (PrimeIdeal K))
    (hsub : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∉ S →
      (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L → b 𝔭 = 1)
    (hbound : ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      (Nat.card B : ℝ) * trivialClassSum b S s ≤ Real.log (1 / (s - 1)) + C) :
    Nat.card B ≤ Module.finrank K L := by
  classical
  set A : Set (PrimeIdeal K) := splitCompletelySet K L with hAdef
  -- `A` is the set of primes splitting completely in `L`; it has Dirichlet density `1/[L:K]`.
  have hdens : NumberField.Set.HasDirichletDensity A (1 / (Module.finrank K L : ℝ)) := by
    rw [hAdef]
    exact hasDirichletDensity_splitCompletelySet
  have hlim : Tendsto (fun s : ℝ => A.primeIdealZetaSum s / Real.log (1 / (s - 1)))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 / (Module.finrank K L : ℝ))) :=
    Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_div_log hdens
  obtain ⟨C, hC⟩ := hbound
  -- The split primes contribute at most the trivial-class primes plus the finite set `S`.
  have hkey : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      A.primeIdealZetaSum s ≤ trivialClassSum b S s + (S.card : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : 1 < s := hs
    have hs0 : (0 : ℝ) ≤ s := by linarith
    have hsum0 : Summable (fun 𝔭 : PrimeIdeal K => primeWeight s 𝔭) := by
      simpa [primeWeight_def] using
        (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs1)
    have hdisj : Disjoint (A ∩ (S : Set (PrimeIdeal K))) (A \ (S : Set (PrimeIdeal K))) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => hx2.2 hx1.2
    have hdecomp : A.primeIdealZetaSum s =
        (A ∩ (S : Set (PrimeIdeal K))).primeIdealZetaSum s +
        (A \ (S : Set (PrimeIdeal K))).primeIdealZetaSum s := by
      have h1 : Summable (fun 𝔭 : ↑(A ∩ (S : Set (PrimeIdeal K))) => primeWeight s 𝔭.1) :=
        hsum0.subtype (fun 𝔭 => 𝔭 ∈ A ∩ (S : Set (PrimeIdeal K)))
      have h2 : Summable (fun 𝔭 : ↑(A \ (S : Set (PrimeIdeal K))) => primeWeight s 𝔭.1) :=
        hsum0.subtype (fun 𝔭 => 𝔭 ∈ A \ (S : Set (PrimeIdeal K)))
      have hunion := Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint
        (K := K) hdisj s (by simpa [primeWeight_def] using h1)
        (by simpa [primeWeight_def] using h2)
      rwa [Set.inter_union_sdiff] at hunion
    -- The primes of `S` contribute at most `|S|`, each weight being `≤ 1`.
    have hcard : (A ∩ (S : Set (PrimeIdeal K))).ncard ≤ S.card := by
      calc (A ∩ (S : Set (PrimeIdeal K))).ncard ≤ ((S : Set (PrimeIdeal K))).ncard :=
            Set.ncard_le_ncard Set.inter_subset_right (Finset.finite_toSet S)
        _ = S.card := Set.ncard_coe_finset S
    have hA1 : (A ∩ (S : Set (PrimeIdeal K))).primeIdealZetaSum s ≤ (S.card : ℝ) := by
      have hfin : (A ∩ (S : Set (PrimeIdeal K))).Finite := (Finset.finite_toSet S).inter_of_right A
      calc (A ∩ (S : Set (PrimeIdeal K))).primeIdealZetaSum s
          ≤ ((A ∩ (S : Set (PrimeIdeal K))).ncard : ℝ) :=
            NumberField.Set.primeIdealZetaSum_le_card_of_finite hfin hs0
        _ ≤ (S.card : ℝ) := by exact_mod_cast hcard
    -- The split primes outside `S` are among the primes of trivial class.
    have hA2 : (A \ (S : Set (PrimeIdeal K))).primeIdealZetaSum s ≤ trivialClassSum b S s := by
      rw [NumberField.Set.primeIdealZetaSum_def, trivialClassSum_def]
      refine Summable.tsum_le_tsum_of_inj
        (f := fun 𝔭 : ↑(A \ (S : Set (PrimeIdeal K))) =>
          (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))
        (g := fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
          if b 𝔭.1 = 1 then primeWeight s 𝔭.1 else 0)
        (fun 𝔭 => (⟨𝔭.1, 𝔭.2.2⟩ : {𝔭 : PrimeIdeal K // 𝔭 ∉ S})) ?_ ?_ ?_ ?_ ?_
      · intro 𝔭 𝔮 h
        have h3 : ((⟨𝔭.1, 𝔭.2.2⟩ : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}) : PrimeIdeal K) =
            ((⟨𝔮.1, 𝔮.2.2⟩ : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}) : PrimeIdeal K) :=
          congrArg (fun x : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => (x : PrimeIdeal K)) h
        have h4 : 𝔭.1 = 𝔮.1 := h3
        exact Subtype.ext h4
      · intro c hc
        split_ifs with h
        · exact primeWeight_nonneg s c.1
        · exact le_rfl
      · intro 𝔭
        have hS' : (𝔭 : PrimeIdeal K) ∉ S := 𝔭.2.2
        have hsplit : (𝔭.1.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard =
            Module.finrank K L := by
          simpa [hAdef, splitCompletelySet] using 𝔭.2.1
        have hb : b 𝔭.1 = 1 := hsub 𝔭.1 hS' hsplit
        simp only [hb, ↓reduceIte, primeWeight_def]
        exact le_rfl
      · exact hsum0.subtype (fun 𝔭 => 𝔭 ∈ A \ (S : Set (PrimeIdeal K)))
      · refine Summable.of_nonneg_of_le (fun c => ?_) (fun c => ?_)
          (hsum0.subtype (fun 𝔭 => 𝔭 ∉ (S : Set (PrimeIdeal K))))
        · split_ifs with h
          · exact primeWeight_nonneg s c.1
          · exact le_rfl
        · split_ifs with h
          · exact le_rfl
          · exact primeWeight_nonneg s c.1
    calc A.primeIdealZetaSum s
        = (A ∩ (S : Set (PrimeIdeal K))).primeIdealZetaSum s +
          (A \ (S : Set (PrimeIdeal K))).primeIdealZetaSum s := hdecomp
      _ ≤ (S.card : ℝ) + trivialClassSum b S s := add_le_add hA1 hA2
      _ = trivialClassSum b S s + (S.card : ℝ) := by ring
  -- Multiply by `|B|`, insert the analytic bound, and divide by the (positive) logarithm.
  have hFG : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      (Nat.card B : ℝ) * (A.primeIdealZetaSum s / Real.log (1 / (s - 1))) ≤
        1 + (C + (Nat.card B : ℝ) * (S.card : ℝ)) * (Real.log (1 / (s - 1)))⁻¹ := by
    filter_upwards [hkey, hC, eventually_log_pos_one_div_sub_one] with s hk hb hl
    have hBC : (0 : ℝ) ≤ (Nat.card B : ℝ) := Nat.cast_nonneg _
    have hmul : (Nat.card B : ℝ) * A.primeIdealZetaSum s ≤
        (Nat.card B : ℝ) * trivialClassSum b S s + (Nat.card B : ℝ) * (S.card : ℝ) := by
      calc (Nat.card B : ℝ) * A.primeIdealZetaSum s
          ≤ (Nat.card B : ℝ) * (trivialClassSum b S s + (S.card : ℝ)) :=
            mul_le_mul_of_nonneg_left hk hBC
        _ = (Nat.card B : ℝ) * trivialClassSum b S s + (Nat.card B : ℝ) * (S.card : ℝ) := by ring
    have htot : (Nat.card B : ℝ) * A.primeIdealZetaSum s ≤
        Real.log (1 / (s - 1)) + (C + (Nat.card B : ℝ) * (S.card : ℝ)) := by
      have := add_le_add_right hb ((Nat.card B : ℝ) * (S.card : ℝ))
      linarith
    have hdiv : (Nat.card B : ℝ) * A.primeIdealZetaSum s / Real.log (1 / (s - 1)) ≤
        (Real.log (1 / (s - 1)) + (C + (Nat.card B : ℝ) * (S.card : ℝ))) /
          Real.log (1 / (s - 1)) :=
      div_le_div_of_nonneg_right htot (le_of_lt hl)
    calc (Nat.card B : ℝ) * (A.primeIdealZetaSum s / Real.log (1 / (s - 1)))
        = (Nat.card B : ℝ) * A.primeIdealZetaSum s / Real.log (1 / (s - 1)) :=
          (mul_div_assoc _ _ _).symm
      _ ≤ (Real.log (1 / (s - 1)) + (C + (Nat.card B : ℝ) * (S.card : ℝ))) /
            Real.log (1 / (s - 1)) := hdiv
      _ = 1 + (C + (Nat.card B : ℝ) * (S.card : ℝ)) * (Real.log (1 / (s - 1)))⁻¹ := by
          rw [add_div, div_self (ne_of_gt hl), div_eq_mul_inv]
  have hFlim : Tendsto (fun s : ℝ => (Nat.card B : ℝ) *
      (A.primeIdealZetaSum s / Real.log (1 / (s - 1)))) (𝓝[>] (1 : ℝ))
      (𝓝 ((Nat.card B : ℝ) * (1 / (Module.finrank K L : ℝ)))) :=
    hlim.const_mul _
  have hGlim : Tendsto (fun s : ℝ => 1 + (C + (Nat.card B : ℝ) * (S.card : ℝ)) *
      (Real.log (1 / (s - 1)))⁻¹) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    have h1 : Tendsto (fun s : ℝ => (Real.log (1 / (s - 1)))⁻¹) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
      tendsto_log_one_div_sub_one_nhdsGT.inv_tendsto_atTop
    have h2 : Tendsto (fun s : ℝ => (C + (Nat.card B : ℝ) * (S.card : ℝ)) *
        (Real.log (1 / (s - 1)))⁻¹) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      simpa using h1.const_mul (C + (Nat.card B : ℝ) * (S.card : ℝ))
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := 𝓝[>] (1 : ℝ))).add h2
  have hle := le_of_tendsto_of_tendsto hFlim hGlim hFG
  -- `|B| · 1/[L:K] ≤ 1` and `[L:K] > 0` give `|B| ≤ [L:K]`.
  have hnpos : (0 : ℝ) < (Module.finrank K L : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L))
  have hle' : (Nat.card B : ℝ) / (Module.finrank K L : ℝ) ≤ 1 := by
    rw [div_eq_mul_one_div]
    exact hle
  have hfin : (Nat.card B : ℝ) ≤ (Module.finrank K L : ℝ) := by
    have := (div_le_iff₀ hnpos).mp hle'
    simpa using this
  exact_mod_cast hfin

end NK.GlobalCFTdeep.SecondInequality
