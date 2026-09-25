import Mathlib
import Submission.Work.Tower.APDensity.Basic

namespace Work.Tower.APDensity.Count

theorem exists_enum_of_sum_bound {ℓ : ℕ} {ε : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (h : ε * (N : ℝ) ≤ Work.Tower.goodPrimeSum N)
    (hℓ : (ℓ : ℝ) ≤ ε * N / Real.log (N : ℝ)) :
    ∃ r : Fin ℓ → ℕ,
      (∀ i, Nat.Prime (r i)) ∧ Function.Injective r ∧ (∀ i, r i % 3 = 1) ∧ (∀ i, r i < N) ∧
      (∑ i : Fin ℓ, Real.log (r i : ℝ)) ≤ ℓ * Real.log (N : ℝ) := by
  -- From `ε * N ≤ goodPrimeSum N ≤ goodPrimeCount N * log N` and `log N > 0`
  -- we obtain `ℓ ≤ goodPrimeCount N`, i.e. there are at least `ℓ` good primes below `N`.
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    have h1N : (1 : ℕ) < N := lt_of_lt_of_le (by norm_num) hN
    exact_mod_cast h1N
  have h1 : ε * (N : ℝ) ≤ (Work.Tower.goodPrimeCount N : ℝ) * Real.log (N : ℝ) :=
    h.trans (Work.Tower.goodPrimeSum_le_card_mul_log N)
  have h2 : ε * (N : ℝ) / Real.log (N : ℝ) ≤ (Work.Tower.goodPrimeCount N : ℝ) :=
    (div_le_iff₀ hlogN).mpr h1
  have h3 : ℓ ≤ Work.Tower.goodPrimeCount N := Nat.cast_le.mp (hℓ.trans h2)
  have h3' : ℓ ≤ ((Finset.range N).filter Work.Tower.IsGoodPrime).card := h3
  -- Enumerate the good primes below `N` in increasing order and take the first `ℓ` of them.
  let e := ((Finset.range N).filter Work.Tower.IsGoodPrime).orderEmbOfFin rfl
  have he : ∀ i, e i ∈ (Finset.range N).filter Work.Tower.IsGoodPrime := fun i =>
    Finset.orderEmbOfFin_mem _ rfl i
  refine ⟨fun i => e (Fin.castLE h3' i), fun i => ?_, ?_, fun i => ?_, fun i => ?_, ?_⟩
  · exact ((Finset.mem_filter.mp (he _)).2).1
  · exact RelEmbedding.injective e |>.comp (Fin.castLE_injective h3')
  · exact ((Finset.mem_filter.mp (he _)).2).2
  · exact Finset.mem_range.mp (Finset.mem_filter.mp (he _)).1
  · -- Each chosen prime is `< N`, so each `log` is at most `log N`.
    show (∑ i : Fin ℓ, Real.log ((e (Fin.castLE h3' i) : ℕ) : ℝ)) ≤ ℓ * Real.log (N : ℝ)
    have hbound : ∀ i : Fin ℓ, Real.log ((e (Fin.castLE h3' i) : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
      intro i
      have hmem := he (Fin.castLE h3' i)
      rw [Finset.mem_filter, Finset.mem_range] at hmem
      exact Real.log_le_log (by exact_mod_cast hmem.2.1.pos) (by exact_mod_cast hmem.1.le)
    calc (∑ i : Fin ℓ, Real.log ((e (Fin.castLE h3' i) : ℕ) : ℝ))
        ≤ ∑ _ : Fin ℓ, Real.log (N : ℝ) := Finset.sum_le_sum fun i _ => hbound i
      _ = ℓ * Real.log (N : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Work.Tower.APDensity.Count
