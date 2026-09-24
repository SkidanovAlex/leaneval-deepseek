import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RIMain.abel_pointwise
import Submission.Work.ChenPlan.LinearSieve.RI.T_eq_zero_of_le
import Submission.Work.ChenPlan.LinearSieve.RIMain.base_layer_bound_sharp
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_integral_form
import Submission.Work.ChenPlan.LinearSieve.RI.tail_bound

/-!
# The sharp Rosser–Iwaniec layer bound in the degenerate case `K = 0`

`sharp_layer_bound_K0` is the `K = 0` case of the sharp layer bound
`T_n(D,z) ≤ VfR A z · profC (n-1) (log D / log z)` for the Rosser–Iwaniec layer sums
(`Work.ChenPlan.LinearSieve.T`), under the range-uniform linearity hypothesis
`IsLinearRange A z 0`.

**Observation.**  With `K = 0` the range axiom is *degenerate*: for a prime `p` of the sieve
problem with `p < z`, applying the axiom to the pair `w = max 2 (p - ε)`, `z' = p + ε`
isolates the single prime `p` in the product (the filter `w ≤ q < z'` contains only `p`), so
`(1 - ν p)⁻¹ ≤ log(p+ε)/log(max 2 (p-ε))` for every `ε > 0`; letting `ε → 0⁺` gives
`(1 - ν p)⁻¹ ≤ 1`, i.e. `ν p ≤ 0`, contradicting `BoundingSieve.nu_pos_of_prime`.

Hence `IsLinearRange A z 0` forces the sieve problem to have **no prime below `z`**, so every
layer sum `T_n(D,z)`, `n ≥ 1`, is the empty sum `0`, and the claimed inequality reduces to
`VfR A z · profC (n-1) s ≥ 0`.  (Correctly, a genuine density-one sieve — e.g. `ν p = 1/p` —
satisfies the range axiom only with a positive constant `K`: at `w = p - ε`, `z' = p + ε` the
product is `(1-ν p)⁻¹ = 1 + 1/p + O(1/p²)` while `log z'/log w → 1`.)
-/

open Finset
open scoped BigOperators Topology

namespace Work.ChenPlan.LinearSieve.RIMain.sharp_bound

/-- **The range axiom with `K = 0` is degenerate**: the sieve problem has no prime below the
sift limit `z`. -/
theorem no_prime_below_of_isLinearRange_zero {A : BoundingSieve} {z : ℝ}
    (hlinrange : Submission.ChenPlan.IsLinearRange A z 0) :
    ∀ p ∈ A.prodPrimes.primeFactors, ¬ ((p : ℝ) < z) := by
  intro p hp hpz
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ A.prodPrimes := (Nat.mem_primeFactors.mp hp).2.1
  have hnu_pos : 0 < A.nu p := A.nu_pos_of_prime p hpprime hpdvd
  have hnu_lt1 : A.nu p < 1 := A.nu_lt_one_of_prime p hpprime hpdvd
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.two_le
  have hppos : (0:ℝ) < (p:ℝ) := by linarith
  -- a positive `ε` small enough that `p + ε ≤ z` and that `[p-ε, p+ε)` contains no integer but `p`
  set ε₀ : ℝ := min (1/2) ((z - (p:ℝ))/2) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]; exact lt_min (by norm_num) (by linarith)
  -- the axiom applied to `w = max 2 (p - ε)`, `z' = p + ε`
  have hbound : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (1 - A.nu p)⁻¹ ≤ Real.log ((p:ℝ) + ε) / Real.log (max 2 ((p:ℝ) - ε)) := by
    intro ε hε hεlt
    have hw2 : (2:ℝ) ≤ max 2 ((p:ℝ) - ε) := le_max_left _ _
    have hwlt : max 2 ((p:ℝ) - ε) < (p:ℝ) + ε := by
      refine max_lt ?_ ?_ <;> linarith
    have hz' : (p:ℝ) + ε ≤ z := by
      have h1 : ε < (z - (p:ℝ))/2 := lt_of_lt_of_le hεlt (min_le_right _ _)
      linarith
    have hmain := hlinrange (max 2 ((p:ℝ) - ε)) ((p:ℝ) + ε) hw2 hwlt hz'
    -- `p` belongs to the filtered set, whose product is therefore at least `(1 - ν p)⁻¹`
    have hS : p ∈ A.prodPrimes.primeFactors.filter
        (fun q : ℕ => max 2 ((p:ℝ) - ε) ≤ (q:ℝ) ∧ (q:ℝ) < (p:ℝ) + ε) := by
      rw [Finset.mem_filter]
      exact ⟨hp, max_le hp2 (by linarith), by linarith⟩
    have hprod_ge : (1 - A.nu p)⁻¹ ≤
        ∏ q ∈ A.prodPrimes.primeFactors.filter
          (fun q : ℕ => max 2 ((p:ℝ) - ε) ≤ (q:ℝ) ∧ (q:ℝ) < (p:ℝ) + ε),
          (1 - A.nu q)⁻¹ := by
      rw [← Finset.mul_prod_erase _ (fun q : ℕ => (1 - A.nu q)⁻¹) hS]
      refine le_mul_of_one_le_right (inv_nonneg.mpr (by linarith)) ?_
      have h := Finset.prod_le_prod₀ (s := (A.prodPrimes.primeFactors.filter
            (fun q : ℕ => max 2 ((p:ℝ) - ε) ≤ (q:ℝ) ∧ (q:ℝ) < (p:ℝ) + ε)).erase p)
          (f := fun _ : ℕ => (1:ℝ)) (g := fun q : ℕ => (1 - A.nu q)⁻¹)
          (fun q _ => zero_le_one) (fun q hq => ?_)
      · simpa using h
      · rw [Finset.mem_erase] at hq
        have hqmem : q ∈ A.prodPrimes.primeFactors := (Finset.mem_filter.mp hq.2).1
        have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
        have hqdvd : q ∣ A.prodPrimes := (Nat.mem_primeFactors.mp hqmem).2.1
        have hqpos : 0 < A.nu q := A.nu_pos_of_prime q hqprime hqdvd
        have hq_lt1 : A.nu q < 1 := A.nu_lt_one_of_prime q hqprime hqdvd
        exact le_of_lt (one_lt_inv_iff₀.mpr ⟨by linarith, by linarith⟩)
    calc (1 - A.nu p)⁻¹
        ≤ ∏ q ∈ A.prodPrimes.primeFactors.filter
          (fun q : ℕ => max 2 ((p:ℝ) - ε) ≤ (q:ℝ) ∧ (q:ℝ) < (p:ℝ) + ε),
          (1 - A.nu q)⁻¹ := hprod_ge
      _ ≤ (Real.log ((p:ℝ)+ε)/Real.log (max 2 ((p:ℝ)-ε))) *
            (1 + 0/Real.log (max 2 ((p:ℝ)-ε))) := hmain
      _ = Real.log ((p:ℝ)+ε)/Real.log (max 2 ((p:ℝ)-ε)) := by ring
  -- let `ε → 0⁺`
  have hid : Filter.Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
    Filter.tendsto_id.mono_right nhdsWithin_le_nhds
  have hlim : Filter.Tendsto
      (fun ε : ℝ => Real.log ((p:ℝ) + ε) / Real.log (max 2 ((p:ℝ) - ε)))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hnum : Filter.Tendsto (fun ε : ℝ => Real.log ((p:ℝ) + ε)) (𝓝[>] (0:ℝ))
        (𝓝 (Real.log (p:ℝ))) := by
      refine (Real.continuousAt_log (ne_of_gt hppos)).tendsto.comp ?_
      have h : Filter.Tendsto (fun ε : ℝ => (p:ℝ) + ε) (𝓝[>] (0:ℝ)) (𝓝 ((p:ℝ) + 0)) :=
        tendsto_const_nhds.add hid
      simpa using h
    have hden : Filter.Tendsto (fun ε : ℝ => Real.log (max 2 ((p:ℝ) - ε))) (𝓝[>] (0:ℝ))
        (𝓝 (Real.log (p:ℝ))) := by
      refine (Real.continuousAt_log (ne_of_gt hppos)).tendsto.comp ?_
      have hsub : Filter.Tendsto (fun ε : ℝ => (p:ℝ) - ε) (𝓝[>] (0:ℝ)) (𝓝 ((p:ℝ) - 0)) :=
        tendsto_const_nhds.sub hid
      have hmx : Filter.Tendsto (fun ε : ℝ => max (2:ℝ) ((p:ℝ) - ε)) (𝓝[>] (0:ℝ))
          (𝓝 (max (2:ℝ) ((p:ℝ) - 0))) := tendsto_const_nhds.max hsub
      have hmax2 : max (2:ℝ) ((p:ℝ) - 0) = (p:ℝ) := by
        rw [sub_zero, max_eq_right hp2]
      rw [hmax2] at hmx
      exact hmx
    have hlogp : Real.log (p:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    have h := hnum.div hden hlogp
    rwa [div_self hlogp] at h
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), (1 - A.nu p)⁻¹ ≤
      Real.log ((p:ℝ) + ε) / Real.log (max 2 ((p:ℝ) - ε)) := by
    rw [eventually_nhdsWithin_iff]
    have h0 : ∀ᶠ ε in 𝓝 (0:ℝ), ε < ε₀ := isOpen_Iio.mem_nhds hε₀pos
    exact h0.mono (fun ε hle hεpos => hbound ε hεpos hle)
  have hle1 : (1 - A.nu p)⁻¹ ≤ 1 := ge_of_tendsto hlim hev
  have hc : (1:ℝ) ≤ 1 - A.nu p := by
    have h1 : (1 - A.nu p)⁻¹ ≤ (1:ℝ)⁻¹ := by simpa using hle1
    exact (inv_le_inv₀ (by linarith : (0:ℝ) < 1 - A.nu p) (by norm_num : (0:ℝ) < 1)).mp h1
  linarith

theorem sharp_layer_bound_K0 :
    ∀ {A : BoundingSieve} {D z : ℝ}, 2 ≤ z → 1 ≤ D →
      Submission.ChenPlan.IsLinear A z 0 → Submission.ChenPlan.IsLinearRange A z 0 →
      ∀ n : ℕ, 1 ≤ n →
        (Odd n → 1 ≤ Real.log D / Real.log z) →
        (Even n → 2 ≤ Real.log D / Real.log z) →
      Work.ChenPlan.LinearSieve.T A n D z ≤ Work.ChenPlan.LinearSieve.VfR A z *
        Work.NumberTheory.Chen.APSwitchUpper.profC (n - 1) (Real.log D / Real.log z) := by
  classical
  intro A D z hz hD hlin hlinrange n hn hodd heven
  have hno : ∀ p ∈ A.prodPrimes.primeFactors, ¬ ((p : ℝ) < z) :=
    no_prime_below_of_isLinearRange_zero hlinrange
  -- every layer sum is empty
  have hT : Work.ChenPlan.LinearSieve.T A n D z = 0 := by
    rcases n with _ | m
    · omega
    · rw [Work.ChenPlan.LinearSieve.T.eq_2 A D z m]
      refine Finset.sum_eq_zero (fun p hp => ?_)
      rw [Finset.mem_filter] at hp
      exact absurd hp.2.1 (hno p hp.1)
  rw [hT]
  exact mul_nonneg (Work.ChenPlan.LinearSieve.VfR_nonneg A z)
    (Work.NumberTheory.Chen.APSwitchUpper.profC_nonneg _ _)

end Work.ChenPlan.LinearSieve.RIMain.sharp_bound
