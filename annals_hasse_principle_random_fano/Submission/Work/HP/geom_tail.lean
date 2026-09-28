import Mathlib

namespace Work.HP

open MeasureTheory
open scoped ENNReal

/-- Termwise identity for the dyadic squares. -/
lemma dyadic_sq_eq (M : ℝ) (ℓ : ℕ) : (M / 2 ^ ℓ) ^ 2 = M ^ 2 * ((1 : ℝ) / 4) ^ ℓ := by
  have h4 : ((2 : ℝ) ^ ℓ) ^ 2 = 4 ^ ℓ := by
    rw [sq, ← pow_add, show ℓ + ℓ = 2 * ℓ by omega, pow_mul]
    norm_num
  rw [div_pow, h4, div_eq_mul_inv, ← inv_pow]
  ring

/-- The summand is summable (dominated by a geometric series with ratio `1/4`). -/
lemma geom_summable (M σ : ℝ) (_hM : 0 < M) :
    Summable (fun ℓ : ℕ => if M / 2 ^ ℓ < σ then (M / 2 ^ ℓ) ^ 2 else 0) := by
  have hgeo : Summable (fun ℓ : ℕ => ((1 : ℝ) / 4) ^ ℓ) := by
    rw [summable_geometric_iff_norm_lt_one]; norm_num
  have hbound : Summable (fun ℓ : ℕ => M ^ 2 * ((1 : ℝ) / 4) ^ ℓ) := hgeo.mul_left (M ^ 2)
  refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hbound
  · split <;> positivity
  · rw [dyadic_sq_eq M ℓ]; split <;> [rfl; positivity]

/-- Real form of the geometric tail bound. -/
lemma geom_tail_real (M σ : ℝ) (hM : 0 < M) (hσ : 0 < σ) :
    (∑' ℓ : ℕ, (if M / 2 ^ ℓ < σ then (M / 2 ^ ℓ) ^ 2 else 0)) ≤ (4 / 3) * σ ^ 2 := by
  -- there always exists an index whose dyadic term drops below `σ`
  have hnex : ∃ ℓ : ℕ, M / 2 ^ ℓ < σ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (M / σ)
    have hNle : (N : ℝ) ≤ (2 : ℝ) ^ N := by
      have := Nat.lt_two_pow_self (n := N)
      exact_mod_cast (le_of_lt this)
    have h2N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have h1 : M / σ < (2 : ℝ) ^ N := lt_of_lt_of_le hN hNle
    have h2 : M < (2 : ℝ) ^ N * σ := by rw [div_lt_iff₀ hσ] at h1; linarith
    exact ⟨N, by rw [div_lt_iff₀ h2N]; linarith⟩
  let n := Nat.find hnex
  have hnspec : M / 2 ^ n < σ := Nat.find_spec hnex
  have hnmin : ∀ m : ℕ, m < n → ¬ (M / 2 ^ m < σ) := fun m hm => Nat.find_min hnex hm
  let f : ℕ → ℝ := fun ℓ => if M / 2 ^ ℓ < σ then (M / 2 ^ ℓ) ^ 2 else 0
  change (∑' ℓ : ℕ, f ℓ) ≤ (4 / 3) * σ ^ 2
  have hg : Summable f := geom_summable M σ hM
  -- the tail beyond `n` is a geometric series with ratio `1/4`
  have hgn : ∀ i : ℕ, f (i + n) = (M / 2 ^ n) ^ 2 * ((1 : ℝ) / 4) ^ i := by
    intro i
    have hcond : M / 2 ^ (i + n) < σ := by
      have hle : M / 2 ^ (i + n) ≤ M / 2 ^ n := by
        apply div_le_div_of_nonneg_left (le_of_lt hM)
        · positivity
        · exact pow_le_pow_right₀ (by norm_num) (by omega)
      exact lt_of_le_of_lt hle hnspec
    simp only [f]
    rw [ite_eq_left hcond, dyadic_sq_eq M (i + n), dyadic_sq_eq M n, pow_add]
    ring
  have hzero : (∑ m ∈ Finset.range n, f m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    simp only [f]
    rw [ite_eq_right (hnmin m hm)]
  have hs := hg.sum_add_tsum_nat_add n
  rw [hzero, zero_add] at hs
  have hEq : (∑' ℓ : ℕ, f ℓ) = ∑' i : ℕ, f (i + n) := hs.symm
  have hsum1 : (∑' i : ℕ, f (i + n)) = ∑' i : ℕ, (M / 2 ^ n) ^ 2 * ((1 : ℝ) / 4) ^ i :=
    tsum_congr (fun i => hgn i)
  have hsum2 : (∑' i : ℕ, (M / 2 ^ n) ^ 2 * ((1 : ℝ) / 4) ^ i) = (M / 2 ^ n) ^ 2 * (4 / 3) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (show ‖((1 : ℝ) / 4)‖ < 1 by norm_num)]
    norm_num
  rw [hEq, hsum1, hsum2]
  have hc : (0 : ℝ) ≤ M / 2 ^ n := by positivity
  nlinarith [hnspec, hσ, hc]

/-- Cardinality of the set of dyadic scales greater than `1`. -/
lemma geom_tail_ncard (M : ℝ) (_hM : 0 < M) :
    (({ℓ : ℕ | 1 < M / 2 ^ ℓ}.ncard : ℝ) ≤ (Nat.ceil M : ℝ) + 1) := by
  have hsub : {ℓ : ℕ | 1 < M / 2 ^ ℓ} ⊆ Set.Iic (Nat.ceil M) := by
    intro ℓ hℓ
    have hℓ' : 1 < M / 2 ^ ℓ := hℓ
    simp only [Set.mem_Iic]
    have hpow : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
    rw [lt_div_iff₀ hpow] at hℓ'
    rw [one_mul] at hℓ'
    have h2 : (ℓ : ℝ) < (2 : ℝ) ^ ℓ := by
      have := Nat.lt_two_pow_self (n := ℓ)
      exact_mod_cast this
    have h3 : (ℓ : ℝ) < M := lt_trans h2 hℓ'
    have h4 : (ℓ : ℝ) < (Nat.ceil M : ℝ) := lt_of_lt_of_le h3 (Nat.le_ceil M)
    have : ℓ < Nat.ceil M := by exact_mod_cast h4
    omega
  have hle : ({ℓ : ℕ | 1 < M / 2 ^ ℓ}).ncard ≤ Nat.ceil M + 1 := by
    have hfin : (Set.Iic (Nat.ceil M)).Finite := Set.finite_Iic _
    have h := Set.ncard_le_ncard hsub hfin
    rwa [Set.ncard_Iic_nat] at h
  exact_mod_cast hle

theorem geom_tail :
    (∀ (M σ : ℝ), 0 < M → 0 < σ →
      (∑' ℓ : ℕ, (if M / 2 ^ ℓ < σ then ENNReal.ofReal ((M / 2 ^ ℓ) ^ 2) else 0))
        ≤ ENNReal.ofReal ((4 / 3) * σ ^ 2)) ∧
    (∀ M : ℝ, 0 < M → (({ℓ : ℕ | 1 < M / 2 ^ ℓ}.ncard : ℝ) ≤ (Nat.ceil M : ℝ) + 1)) := by
  constructor
  · intro M σ hM hσ
    let f : ℕ → ℝ := fun ℓ => if M / 2 ^ ℓ < σ then (M / 2 ^ ℓ) ^ 2 else 0
    have hg : Summable f := geom_summable M σ hM
    have hfnn : ∀ ℓ : ℕ, 0 ≤ f ℓ := by intro ℓ; simp only [f]; split <;> positivity
    have hreal : (∑' ℓ : ℕ, f ℓ) ≤ (4 / 3) * σ ^ 2 := geom_tail_real M σ hM hσ
    have step1 : (∑' ℓ : ℕ, ENNReal.ofReal (f ℓ)) = ENNReal.ofReal (∑' ℓ : ℕ, f ℓ) :=
      (ENNReal.ofReal_tsum_of_nonneg hfnn hg).symm
    have step2 : (∑' ℓ : ℕ, (if M / 2 ^ ℓ < σ then ENNReal.ofReal ((M / 2 ^ ℓ) ^ 2) else 0))
        = ∑' ℓ : ℕ, ENNReal.ofReal (f ℓ) := by
      apply tsum_congr; intro ℓ
      simp only [f]; split <;> simp
    rw [step2, step1]
    exact ENNReal.ofReal_le_ofReal hreal
  · intro M hM
    exact geom_tail_ncard M hM

end Work.HP
