import Mathlib
import Submission.Work.BMF.liouville.sum_prime_pow_le_rect_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

open Work.BMF.liouville

/-- **Cardinality of proper prime powers up to `M`.** The number of `n ∈ [2,M]` that are prime
powers but not prime is at most `2·√M·log M` (true also for `M ≤ 1`, where it is `0 ≤ 0`).

Route: such an `n` is `p^k` with `p` prime, `k ≥ 2` (`exists_prime_pow_of_isPrimePow_not_prime`
and `powRep`/`powRep_spec` from the imported module). Then `p ≤ √M` and, since `2^k ≤ p^k = n ≤ M`,
`k ≤ Nat.log 2 M`. The map `n ↦ powRep n` is injective, so the count is at most
`#(primes ≤ √M) · #(Icc 2 (Nat.log 2 M)) ≤ ⌊√M⌋ · Nat.log 2 M ≤ √M · Nat.log 2 M`, and
`Nat.log 2 M · log 2 ≤ log M` together with `log 2 ≥ 1/2` gives `Nat.log 2 M ≤ 2 log M`. -/
theorem card_primepow_not_prime_le (M : ℕ) :
    (((Finset.Icc 2 M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)).card : ℝ)
      ≤ 2 * Real.sqrt M * Real.log M := by
  classical
  by_cases hM : M ≤ 1
  · -- `M ≤ 1`: the interval `[2,M]` is empty, so the count is `0`.
    have hI : Finset.Icc 2 M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hI, Finset.filter_empty, Finset.card_empty]
    simp only [Nat.cast_zero]
    have hM0 : M = 0 ∨ M = 1 := by omega
    rcases hM0 with rfl | rfl <;> norm_num
  · -- `2 ≤ M`.
    have hMne : M ≠ 0 := by omega
    set T := (Finset.Icc 2 M).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n) with hTdef
    -- Every element of `T` admits a prime power representation.
    have hmem : ∀ n ∈ T, ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ n = p ^ k := by
      intro n hn
      rw [hTdef, Finset.mem_filter] at hn
      exact exists_prime_pow_of_isPrimePow_not_prime n hn.2.1 hn.2.2
    -- `powRep` is injective on `T`.
    have hinj : Set.InjOn powRep ↑T := by
      intro a ha b hb heq
      have sa := powRep_spec (hmem a ha)
      have sb := powRep_spec (hmem b hb)
      rw [sa.2.2, sb.2.2, heq]
    -- The image of `T` under `powRep` lands in `[2,√M] × [2,log₂M]`.
    have hsub : T.image powRep
        ⊆ (Finset.Icc 2 (Nat.sqrt M)) ×ˢ (Finset.Icc 2 (Nat.log 2 M)) := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨x, hx, rfl⟩ := hq
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      obtain ⟨hxIcc, _⟩ := Finset.mem_filter.mp (hTdef ▸ hx)
      obtain ⟨h2x, hxM⟩ := Finset.mem_Icc.mp hxIcc
      have spec := powRep_spec (hmem x hx)
      have hpkM : (powRep x).1 ^ (powRep x).2 ≤ M := by rw [← spec.2.2]; exact hxM
      have hp2 : (powRep x).1 ^ 2 ≤ M :=
        le_trans (Nat.pow_le_pow_right spec.1.pos (by omega)) hpkM
      have h2k : 2 ^ (powRep x).2 ≤ M :=
        le_trans (Nat.pow_le_pow_left spec.1.two_le (powRep x).2) hpkM
      exact ⟨⟨spec.1.two_le, Nat.le_sqrt'.mpr hp2⟩,
        ⟨spec.2.1, (Nat.le_log_iff_pow_le (by norm_num) hMne).mpr h2k⟩⟩
    have hcard1 :
        T.card ≤ ((Finset.Icc 2 (Nat.sqrt M)) ×ˢ (Finset.Icc 2 (Nat.log 2 M))).card := by
      calc T.card = (T.image powRep).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ _ := Finset.card_le_card hsub
    rw [Finset.card_product] at hcard1
    have hA : (Finset.Icc 2 (Nat.sqrt M)).card ≤ Nat.sqrt M := by rw [Nat.card_Icc]; omega
    have hB : (Finset.Icc 2 (Nat.log 2 M)).card ≤ Nat.log 2 M := by rw [Nat.card_Icc]; omega
    have hcard : T.card ≤ Nat.sqrt M * Nat.log 2 M := le_trans hcard1 (Nat.mul_le_mul hA hB)
    have hcardR : ((T.card : ℕ) : ℝ) ≤ (Nat.sqrt M : ℝ) * (Nat.log 2 M : ℝ) := by
      calc ((T.card : ℕ) : ℝ) ≤ ((Nat.sqrt M * Nat.log 2 M : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (Nat.sqrt M : ℝ) * (Nat.log 2 M : ℝ) := by push_cast; ring
    -- Real inequalities: `⌊√M⌋ ≤ √M` and `log₂ M ≤ 2 log M`.
    have hs : (Nat.sqrt M : ℝ) ≤ Real.sqrt M := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (Nat.sqrt M : ℝ))]
      apply Real.sqrt_le_sqrt
      rw [← Nat.cast_pow]
      exact_mod_cast Nat.sqrt_le' M
    have hl : (Nat.log 2 M : ℝ) ≤ 2 * Real.log M := by
      have h1 : (2:ℝ) ^ Nat.log 2 M ≤ (M:ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 hMne
      have h2 : 0 < (2:ℝ) ^ Nat.log 2 M := by positivity
      have hlog := Real.log_le_log h2 h1
      rw [Real.log_pow] at hlog
      have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hk : (0:ℝ) ≤ (Nat.log 2 M : ℝ) := by positivity
      nlinarith [hlog, hlog2, hk]
    calc (T.card : ℝ) ≤ (Nat.sqrt M : ℝ) * (Nat.log 2 M : ℝ) := hcardR
      _ ≤ Real.sqrt M * (2 * Real.log M) := mul_le_mul hs hl (by positivity) (Real.sqrt_nonneg M)
      _ = 2 * Real.sqrt M * Real.log M := by ring

end Work.BMF.pcsw
