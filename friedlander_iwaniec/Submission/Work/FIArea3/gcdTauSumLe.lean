import Mathlib
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Work.FIArea2.sum_tau_pow_le

namespace Work.FIArea3

open Finset
open scoped BigOperators


noncomputable section

/-- `n ≤ ∑_{d ∣ n} d` for `n ≥ 1` (the divisor `n` itself is a summand). -/
private lemma self_le_sum_divisors (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ≤ ∑ d ∈ n.divisors, (d : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  exact Finset.single_le_sum (fun d _ => Nat.cast_nonneg d) (Nat.mem_divisors_self n hn0)

/-- `gcd(b,e) ≤ ∑_{h ∣ b} [h ∣ e]·h` for `1 ≤ b`: the divisors of `gcd b e` are exactly the
common divisors of `b` and `e`, and `gcd b e` contributes itself. -/
private lemma gcd_le_sum_ite (b e : ℕ) (hb : 1 ≤ b) :
    ((Nat.gcd b e : ℕ) : ℝ) ≤ ∑ h ∈ b.divisors, (if h ∣ e then (h : ℝ) else 0) := by
  have hb0 : b ≠ 0 := by omega
  have hg0 : Nat.gcd b e ≠ 0 := fun h => hb0 (Nat.gcd_eq_zero_iff.mp h).1
  have hsub : (Nat.gcd b e).divisors ⊆ b.divisors.filter (fun h => h ∣ e) := by
    intro h hh
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hh
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdvd.trans (Nat.gcd_dvd_left b e), hb0⟩,
        hdvd.trans (Nat.gcd_dvd_right b e)⟩
  calc ((Nat.gcd b e : ℕ) : ℝ)
      ≤ ∑ d ∈ (Nat.gcd b e).divisors, (d : ℝ) :=
        self_le_sum_divisors _ (Nat.pos_of_ne_zero hg0)
    _ ≤ ∑ h ∈ b.divisors.filter (fun h => h ∣ e), (h : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => Nat.cast_nonneg h)
    _ = ∑ h ∈ b.divisors, (if h ∣ e then (h : ℝ) else 0) := by rw [Finset.sum_filter]

/-- Reindexing the "multiples of `h`" sum: replacing `e` by `h·e'` turns `∑_e [h ∣ e]·h·(τ(e)^k/e)`
into `∑_{e' ≤ Y/h} τ(h·e')^k/e'`. -/
private lemma reindex_sum (k h Y : ℕ) (hh : 1 ≤ h) :
    (∑ e ∈ Finset.Icc 1 Y,
        (if h ∣ e then (h : ℝ) else 0) * ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)))
      = ∑ e' ∈ Finset.Icc 1 (Y / h), ((((h * e').divisors.card : ℕ) : ℝ)) ^ k / (e' : ℝ) := by
  have hstep : (∑ e ∈ Finset.Icc 1 Y,
        (if h ∣ e then (h : ℝ) else 0) * ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)))
      = ∑ e ∈ (Finset.Icc 1 Y).filter (fun e => h ∣ e),
          (h : ℝ) * ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e he => ?_
    by_cases hc : h ∣ e <;> simp [hc]
  rw [hstep, ← Work.FIArea2.image_mul_Icc_eq_filter (d := h) (X := Y) hh]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun e' he' => ?_
    have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
    rw [Nat.cast_mul]
    field_simp
  · intro a _ b _ hab
    exact Nat.mul_left_cancel (by omega : 0 < h) hab

/-- Bound for the inner (multiples of `h`) sum: using sub-multiplicativity of `τ`, the sum over
`e' ≤ Y/h` is at most `τ(h)^k` times the full logarithmic sum, which is bounded by `hC0`. -/
private lemma inner_bound (k : ℕ) (C0 : ℝ)
    (hC0 : ∀ X : ℕ, (∑ n ∈ Finset.Icc 1 X, ((((n.divisors.card : ℕ) : ℝ))) ^ k / (n : ℝ))
        ≤ C0 * (Real.log (X : ℝ) + 2) ^ (2 ^ k))
    (h Y : ℕ) (_hh : 1 ≤ h) :
    (∑ e' ∈ Finset.Icc 1 (Y / h), ((((h * e').divisors.card : ℕ) : ℝ)) ^ k / (e' : ℝ))
      ≤ ((((h.divisors.card : ℕ) : ℝ))) ^ k * (C0 * (Real.log (Y : ℝ) + 2) ^ (2 ^ k)) := by
  have hterm : ∀ e' ∈ Finset.Icc 1 (Y / h),
      ((((h * e').divisors.card : ℕ) : ℝ)) ^ k / (e' : ℝ)
        ≤ ((((h.divisors.card : ℕ) : ℝ))) ^ k *
            (((((e'.divisors.card : ℕ) : ℝ))) ^ k / (e' : ℝ)) := by
    intro e' he'
    have h1 : ((((h * e').divisors.card : ℕ) : ℝ))
        ≤ ((((h.divisors.card : ℕ) : ℝ))) * ((((e'.divisors.card : ℕ) : ℝ))) := by
      have := Work.FIArea2.tauR_mul_le h e'
      simpa [Work.FIArea2.tauR] using this
    have h2 : ((((h * e').divisors.card : ℕ) : ℝ)) ^ k
        ≤ (((((h.divisors.card : ℕ) : ℝ))) * ((((e'.divisors.card : ℕ) : ℝ)))) ^ k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h1 k
    rw [mul_pow] at h2
    have he'pos : (0:ℝ) < (e':ℝ) := by
      have : 1 ≤ e' := (Finset.mem_Icc.mp he').1
      exact_mod_cast this
    calc ((((h * e').divisors.card : ℕ) : ℝ)) ^ k / (e' : ℝ)
        ≤ ((((((h.divisors.card : ℕ) : ℝ))) ^ k * ((((e'.divisors.card : ℕ) : ℝ))) ^ k)) / (e' : ℝ) :=
          div_le_div_of_nonneg_right h2 he'pos.le
      _ = ((((h.divisors.card : ℕ) : ℝ))) ^ k *
            ((((((e'.divisors.card : ℕ) : ℝ))) ^ k) / (e' : ℝ)) := by ring
  calc (∑ e' ∈ Finset.Icc 1 (Y / h), ((((h * e').divisors.card : ℕ) : ℝ)) ^ k / (e' : ℝ))
      ≤ ∑ e' ∈ Finset.Icc 1 (Y / h), ((((h.divisors.card : ℕ) : ℝ))) ^ k *
          (((((e'.divisors.card : ℕ) : ℝ))) ^ k / (e' : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ((((h.divisors.card : ℕ) : ℝ))) ^ k *
          (∑ e' ∈ Finset.Icc 1 (Y / h), (((((e'.divisors.card : ℕ) : ℝ))) ^ k / (e' : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ ((((h.divisors.card : ℕ) : ℝ))) ^ k * (C0 * (Real.log (Y : ℝ) + 2) ^ (2 ^ k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Nat.cast_nonneg _) k)
        refine le_trans ?_ (hC0 Y)
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (Nat.div_le_self Y h)) ?_
        intro n hn _
        exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) k) (Nat.cast_nonneg n)

/-- `∑_{h ∣ b} τ(h)^k ≤ τ(b)^{k+1}`: each `τ(h) ≤ τ(b)` for `h ∣ b`, and there are `τ(b)` terms. -/
private lemma sum_tau_pow_divisors_le (k b : ℕ) (hb : 1 ≤ b) :
    (∑ h ∈ b.divisors, ((((h.divisors.card : ℕ) : ℝ))) ^ k)
      ≤ ((((b.divisors.card : ℕ) : ℝ))) ^ (k + 1) := by
  have hb0 : b ≠ 0 := by omega
  have hle : ∀ h ∈ b.divisors,
      ((((h.divisors.card : ℕ) : ℝ))) ≤ ((((b.divisors.card : ℕ) : ℝ))) := by
    intro h hh
    have hdvd : h ∣ b := (Nat.mem_divisors.mp hh).1
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hb0 hdvd)
  calc (∑ h ∈ b.divisors, ((((h.divisors.card : ℕ) : ℝ))) ^ k)
      ≤ ∑ h ∈ b.divisors, ((((b.divisors.card : ℕ) : ℝ))) ^ k :=
        Finset.sum_le_sum (fun h hh => pow_le_pow_left₀ (Nat.cast_nonneg _) (hle h hh) k)
    _ = ((((b.divisors.card : ℕ) : ℝ))) ^ (k + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, pow_succ]
        ring

/-- `Σ_{e ≤ Y} τ(e)^k·gcd(b,e)/e ≤ C·(log Y+2)^{2^{k+1}}·τ(b)^{k+1}` for `1 ≤ b` (existential `C`
depending only on `k`). Proof: `gcd(b,e) ≤ σ(gcd(b,e)) = Σ_{h ∣ b, h ∣ e} h`, then swap the sums;
the inner sum `Σ_{h∣e} τ(e)^k/e ≤ h^{-1}τ(h)^k·Σ τ(e')^k/e'` is controlled by `sum_tau_pow_div_le`,
and `Σ_{h ∣ b}τ(h)^k ≤ τ(b)^{k+1}`. -/
theorem gcdTauSumLe (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y b : ℕ), 1 ≤ b →
      (∑ e ∈ Finset.Icc 1 Y,
          (((e.divisors.card : ℕ) : ℝ)) ^ k * ((Nat.gcd b e : ℕ) : ℝ) / (e : ℝ))
        ≤ C * (Real.log (Y : ℝ) + 2) ^ (2 ^ (k + 1))
            * (((b.divisors.card : ℕ) : ℝ)) ^ (k + 1) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FIArea2.sum_tau_pow_div_le k
  refine ⟨C0, hC0pos, fun Y b hb => ?_⟩
  have hlog : (0:ℝ) ≤ Real.log (Y:ℝ) := by
    rcases Nat.eq_zero_or_pos Y with h | h
    · subst h; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hbase_nonneg : (0:ℝ) ≤ Real.log (Y:ℝ) + 2 := by linarith
  have hbase_one : (1:ℝ) ≤ Real.log (Y:ℝ) + 2 := by linarith
  have hB : (∑ e ∈ Finset.Icc 1 Y,
        (((e.divisors.card : ℕ) : ℝ)) ^ k * ((Nat.gcd b e : ℕ) : ℝ) / (e : ℝ))
      ≤ ∑ e ∈ Finset.Icc 1 Y, ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)) *
          (∑ h ∈ b.divisors, (if h ∣ e then (h : ℝ) else 0)) := by
    refine Finset.sum_le_sum fun e he => ?_
    calc (((e.divisors.card : ℕ) : ℝ)) ^ k * ((Nat.gcd b e : ℕ) : ℝ) / (e : ℝ)
        = ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)) * ((Nat.gcd b e : ℕ) : ℝ) := by ring
      _ ≤ ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)) *
            (∑ h ∈ b.divisors, (if h ∣ e then (h : ℝ) else 0)) :=
          mul_le_mul_of_nonneg_left (gcd_le_sum_ite b e hb)
            (div_nonneg (pow_nonneg (Nat.cast_nonneg _) k) (Nat.cast_nonneg e))
  have hstep : (∑ e ∈ Finset.Icc 1 Y, ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)) *
          (∑ h ∈ b.divisors, (if h ∣ e then (h : ℝ) else 0)))
      = ∑ h ∈ b.divisors, ∑ e ∈ Finset.Icc 1 Y,
          (if h ∣ e then (h : ℝ) else 0) * ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun e he => by ring
  have hinner : ∀ h ∈ b.divisors,
      (∑ e ∈ Finset.Icc 1 Y, (if h ∣ e then (h : ℝ) else 0) *
          ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)))
        ≤ ((((h.divisors.card : ℕ) : ℝ))) ^ k * (C0 * (Real.log (Y : ℝ) + 2) ^ (2 ^ k)) := by
    intro h hh
    have hh1 : 1 ≤ h := by
      have hdvd : h ∣ b := (Nat.mem_divisors.mp hh).1
      exact Nat.pos_of_dvd_of_pos hdvd (by omega)
    rw [reindex_sum k h Y hh1]
    exact inner_bound k C0 hC0 h Y hh1
  have h2k : 2 ^ k ≤ 2 ^ (k + 1) := by
    calc 2 ^ k ≤ 2 ^ k * 2 := Nat.le_mul_of_pos_right _ (by norm_num)
      _ = 2 ^ (k + 1) := by rw [pow_succ]
  calc (∑ e ∈ Finset.Icc 1 Y,
        (((e.divisors.card : ℕ) : ℝ)) ^ k * ((Nat.gcd b e : ℕ) : ℝ) / (e : ℝ))
      ≤ ∑ e ∈ Finset.Icc 1 Y, ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)) *
          (∑ h ∈ b.divisors, (if h ∣ e then (h : ℝ) else 0)) := hB
    _ = ∑ h ∈ b.divisors, ∑ e ∈ Finset.Icc 1 Y,
          (if h ∣ e then (h : ℝ) else 0) * ((((e.divisors.card : ℕ) : ℝ)) ^ k / (e : ℝ)) := hstep
    _ ≤ ∑ h ∈ b.divisors, ((((h.divisors.card : ℕ) : ℝ))) ^ k *
          (C0 * (Real.log (Y : ℝ) + 2) ^ (2 ^ k)) := Finset.sum_le_sum hinner
    _ = (∑ h ∈ b.divisors, ((((h.divisors.card : ℕ) : ℝ))) ^ k) *
          (C0 * (Real.log (Y : ℝ) + 2) ^ (2 ^ k)) := by rw [Finset.sum_mul]
    _ ≤ ((((b.divisors.card : ℕ) : ℝ))) ^ (k + 1) * (C0 * (Real.log (Y : ℝ) + 2) ^ (2 ^ k)) :=
        mul_le_mul_of_nonneg_right (sum_tau_pow_divisors_le k b hb)
          (mul_nonneg hC0pos.le (pow_nonneg hbase_nonneg _))
    _ = C0 * (Real.log (Y : ℝ) + 2) ^ (2 ^ k) * ((((b.divisors.card : ℕ) : ℝ))) ^ (k + 1) := by ring
    _ ≤ C0 * (Real.log (Y : ℝ) + 2) ^ (2 ^ (k + 1)) * ((((b.divisors.card : ℕ) : ℝ))) ^ (k + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Nat.cast_nonneg _) (k + 1))
        refine mul_le_mul_of_nonneg_left ?_ hC0pos.le
        exact pow_le_pow_right₀ hbase_one h2k

end

end Work.FIArea3

