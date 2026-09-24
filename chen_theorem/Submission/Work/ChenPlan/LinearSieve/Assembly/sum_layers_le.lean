import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_le_decay

open Finset
open scoped BigOperators

namespace Work.ChenPlan.LinearSieve.Assembly

open Work.NumberTheory.Chen.APSwitchUpper

/-! ## Parity arithmetic on the layer index -/

lemma two_mul_div_two_of_odd {n : ℕ} (hn : Odd n) : 2 * ((n - 1) / 2) = n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  omega

lemma one_le_of_odd {n : ℕ} (hn : Odd n) : 1 ≤ n := by
  obtain ⟨k, rfl⟩ := hn
  omega

lemma two_mul_div_two_add_one_of_even {n : ℕ} (hn : Even n) (h0 : n ≠ 0) :
    2 * ((n - 1) / 2) + 1 = n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  omega

lemma one_le_of_even_ne {n : ℕ} (hn : Even n) (h0 : n ≠ 0) : 1 ≤ n := by
  obtain ⟨k, rfl⟩ := hn
  omega

/-- `(98/100)^(n-1) ≤ ((98/100)^2)^((n-1)/2)`: since `n - 1 ≥ 2 * ((n-1)/2)` and the
base `98/100` is in `[0,1]`. -/
lemma pow_le_sq_pow_div (n : ℕ) :
    (98/100 : ℝ) ^ (n - 1) ≤ ((98/100 : ℝ) ^ 2) ^ ((n - 1) / 2) := by
  have hle : 2 * ((n - 1) / 2) ≤ n - 1 := by
    rw [mul_comm]; exact Nat.div_mul_le_self (n - 1) 2
  rw [← pow_mul]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hle

/-! ## Summability of the even- and odd-index profile series -/

lemma summable_profC_even {σ : ℝ} (hσ : 1 ≤ σ) :
    Summable (fun j : ℕ => profC (2 * j) σ) := by
  have hr0 : (0:ℝ) ≤ ((97:ℝ)/100)^2 := by norm_num
  have hr1 : ((97:ℝ)/100)^2 < 1 := by norm_num
  refine Summable.of_nonneg_of_le (fun j => profC_nonneg (2*j) σ) (fun j => ?_)
    (Summable.mul_left (20 * errH σ) (summable_geometric_of_lt_one hr0 hr1))
  calc profC (2 * j) σ ≤ 20 * ((97:ℝ)/100)^(2*j) * errH σ := profC_le_decay (2*j) σ hσ
    _ = 20 * errH σ * (((97:ℝ)/100)^2)^j := by rw [pow_mul]; ac_rfl

lemma summable_profC_odd {σ : ℝ} (hσ : 1 ≤ σ) :
    Summable (fun j : ℕ => profC (2 * j + 1) σ) := by
  have hr0 : (0:ℝ) ≤ ((97:ℝ)/100)^2 := by norm_num
  have hr1 : ((97:ℝ)/100)^2 < 1 := by norm_num
  refine Summable.of_nonneg_of_le (fun j => profC_nonneg (2*j+1) σ) (fun j => ?_)
    (Summable.mul_left (20 * errH σ) (summable_geometric_of_lt_one hr0 hr1))
  have hpow : ((97:ℝ)/100)^(2*j+1) = ((97:ℝ)/100) * (((97:ℝ)/100)^2)^j := by
    rw [pow_succ, pow_mul, mul_comm]
  calc profC (2 * j + 1) σ ≤ 20 * ((97:ℝ)/100)^(2*j+1) * errH σ := profC_le_decay (2*j+1) σ hσ
    _ = 20 * errH σ * (((97:ℝ)/100)^2)^j * ((97:ℝ)/100) := by rw [hpow]; ac_rfl
    _ ≤ 20 * errH σ * (((97:ℝ)/100)^2)^j := by
        have hX : (0:ℝ) ≤ 20 * errH σ * (((97:ℝ)/100)^2)^j :=
          mul_nonneg (mul_nonneg (by norm_num) (errH_nonneg σ)) (pow_nonneg hr0 j)
        simpa using mul_le_mul_of_nonneg_left (by norm_num : ((97:ℝ)/100) ≤ 1) hX

/-! ## Reindexing a parity-filtered layer sum by `n ↦ (n-1)/2` -/

lemma sum_filter_div_two_le_tsum {f : ℕ → ℝ} {N : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hinj : ∀ x ∈ (Finset.range N).filter P, ∀ y ∈ (Finset.range N).filter P,
      (x - 1) / 2 = (y - 1) / 2 → x = y)
    (hf : ∀ j, 0 ≤ f j) (hS : Summable f) :
    ∑ n ∈ (Finset.range N).filter P, f ((n - 1) / 2) ≤ ∑' j, f j := by
  rw [← Finset.sum_image (s := (Finset.range N).filter P)
        (g := fun n : ℕ => (n - 1) / 2)
        (by intro x hx y hy h; exact hinj x hx y hy h)]
  exact Summable.sum_le_tsum _ (fun i _ => hf i) hS

lemma injOn_odd_div_two (N : ℕ) :
    ∀ x ∈ (Finset.range N).filter (fun n : ℕ => Odd n),
      ∀ y ∈ (Finset.range N).filter (fun n : ℕ => Odd n),
        (x - 1) / 2 = (y - 1) / 2 → x = y := by
  intro x hx y hy h
  have hx' : 2 * ((x - 1) / 2) = x - 1 := two_mul_div_two_of_odd (Finset.mem_filter.mp hx).2
  have hy' : 2 * ((y - 1) / 2) = y - 1 := two_mul_div_two_of_odd (Finset.mem_filter.mp hy).2
  have h1 : 1 ≤ x := one_le_of_odd (Finset.mem_filter.mp hx).2
  have h2 : 1 ≤ y := one_le_of_odd (Finset.mem_filter.mp hy).2
  have h3 : x - 1 = y - 1 := by rw [← hx', ← hy', h]
  omega

lemma injOn_even_div_two (N : ℕ) :
    ∀ x ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
      ∀ y ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        (x - 1) / 2 = (y - 1) / 2 → x = y := by
  intro x hx y hy h
  obtain ⟨hxe, hx0⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hye, hy0⟩ := (Finset.mem_filter.mp hy).2
  have hx' : 2 * ((x - 1) / 2) + 1 = x - 1 := two_mul_div_two_add_one_of_even hxe hx0
  have hy' : 2 * ((y - 1) / 2) + 1 = y - 1 := two_mul_div_two_add_one_of_even hye hy0
  have h1 : 1 ≤ x := one_le_of_even_ne hxe hx0
  have h2 : 1 ≤ y := one_le_of_even_ne hye hy0
  have h3 : x - 1 = y - 1 := by
    calc x - 1 = 2 * ((x - 1) / 2) + 1 := hx'.symm
      _ = 2 * ((y - 1) / 2) + 1 := by rw [h]
      _ = y - 1 := hy'
  omega

/-! ## The tail of the error profile is dominated by `26000 ε h s` -/

lemma sum_error_le {N : ℕ} {P : ℕ → Prop} [DecidablePred P] {s ε : ℝ} (hε : 0 ≤ ε)
    (hinj : ∀ x ∈ (Finset.range N).filter P, ∀ y ∈ (Finset.range N).filter P,
      (x - 1) / 2 = (y - 1) / 2 → x = y) :
    ∑ n ∈ (Finset.range N).filter P, (1000 * ε * (98/100 : ℝ) ^ (n - 1) * errH s)
      ≤ 26000 * ε * errH s := by
  set c : ℝ := 1000 * ε * errH s with hc
  have hc0 : 0 ≤ c := by
    rw [hc]; exact mul_nonneg (mul_nonneg (by norm_num) hε) (errH_nonneg s)
  have hstep : ∑ n ∈ (Finset.range N).filter P, (1000 * ε * (98/100 : ℝ) ^ (n - 1) * errH s)
      ≤ c * ∑ n ∈ (Finset.range N).filter P, (((98/100 : ℝ) ^ 2) ^ ((n - 1) / 2)) := by
    rw [hc, Finset.mul_sum]
    refine Finset.sum_le_sum (fun n _ => ?_)
    have hp := pow_le_sq_pow_div n
    have ha : (0:ℝ) ≤ 1000 * ε * errH s :=
      mul_nonneg (mul_nonneg (by norm_num) hε) (errH_nonneg s)
    calc 1000 * ε * (98/100 : ℝ) ^ (n - 1) * errH s
        = (1000 * ε * errH s) * (98/100 : ℝ) ^ (n - 1) := by ring
      _ ≤ (1000 * ε * errH s) * (((98/100 : ℝ) ^ 2) ^ ((n - 1) / 2)) :=
          mul_le_mul_of_nonneg_left hp ha
  have hsum : ∑ n ∈ (Finset.range N).filter P, (((98/100 : ℝ) ^ 2) ^ ((n - 1) / 2))
      ≤ ∑' j : ℕ, ((98/100 : ℝ) ^ 2) ^ j :=
    sum_filter_div_two_le_tsum (P := P) (N := N) (f := fun j : ℕ => ((98/100 : ℝ) ^ 2) ^ j)
      hinj (fun j => pow_nonneg (by norm_num) j)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hgeo : (∑' j : ℕ, ((98/100 : ℝ) ^ 2) ^ j) = (1 - (98/100 : ℝ) ^ 2)⁻¹ :=
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)
  have h26 : (1 - (98/100 : ℝ) ^ 2)⁻¹ ≤ 26 := by norm_num
  calc ∑ n ∈ (Finset.range N).filter P, (1000 * ε * (98/100 : ℝ) ^ (n - 1) * errH s)
      ≤ c * ∑ n ∈ (Finset.range N).filter P, (((98/100 : ℝ) ^ 2) ^ ((n - 1) / 2)) := hstep
    _ ≤ c * ∑' j : ℕ, ((98/100 : ℝ) ^ 2) ^ j := mul_le_mul_of_nonneg_left hsum hc0
    _ = c * (1 - (98/100 : ℝ) ^ 2)⁻¹ := by rw [hgeo]
    _ ≤ c * 26 := mul_le_mul_of_nonneg_left h26 hc0
    _ = 26000 * ε * errH s := by rw [hc]; ring

theorem sum_layers_le (N : ℕ) {s ε : ℝ} (hs : 1 ≤ s) (hε : 0 ≤ ε) :
    (∑ n ∈ (Finset.range N).filter (fun n : ℕ => Odd n),
        (Work.NumberTheory.Chen.APSwitchUpper.profC (n - 1) s
          + 1000 * ε * (98/100 : ℝ) ^ (n - 1) * Work.NumberTheory.Chen.APSwitchUpper.errH s)
        ≤ Work.NumberTheory.Chen.APSwitchUpper.riPhi s
          + 26000 * ε * Work.NumberTheory.Chen.APSwitchUpper.errH s) ∧
    (∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        (Work.NumberTheory.Chen.APSwitchUpper.profC (n - 1) s
          + 1000 * ε * (98/100 : ℝ) ^ (n - 1) * Work.NumberTheory.Chen.APSwitchUpper.errH s)
        ≤ Work.NumberTheory.Chen.APSwitchUpper.riPsi s
          + 26000 * ε * Work.NumberTheory.Chen.APSwitchUpper.errH s) := by
  constructor
  · rw [Finset.sum_add_distrib]
    have hA : ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Odd n), profC (n - 1) s ≤ riPhi s := by
      have heq : ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Odd n), profC (n - 1) s
          = ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Odd n),
              (fun j : ℕ => profC (2 * j) s) ((n - 1) / 2) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have ho : Odd n := (Finset.mem_filter.mp hn).2
        show profC (n - 1) s = profC (2 * ((n - 1) / 2)) s
        rw [two_mul_div_two_of_odd ho]
      rw [heq]
      have hb := sum_filter_div_two_le_tsum (f := fun j : ℕ => profC (2 * j) s)
        (P := fun n : ℕ => Odd n) (N := N) (injOn_odd_div_two N)
        (fun j => profC_nonneg (2 * j) s) (summable_profC_even hs)
      have hri : riPhi s = ∑' j : ℕ, profC (2 * j) s := rfl
      rw [hri]; exact hb
    have hB := sum_error_le (P := fun n : ℕ => Odd n) (N := N) (s := s) (ε := ε) hε
      (injOn_odd_div_two N)
    linarith
  · rw [Finset.sum_add_distrib]
    have hA : ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        profC (n - 1) s ≤ riPsi s := by
      have heq : ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0), profC (n - 1) s
          = ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
              (fun j : ℕ => profC (2 * j + 1) s) ((n - 1) / 2) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        obtain ⟨hev, hn0⟩ := (Finset.mem_filter.mp hn).2
        show profC (n - 1) s = profC (2 * ((n - 1) / 2) + 1) s
        rw [two_mul_div_two_add_one_of_even hev hn0]
      rw [heq]
      have hb := sum_filter_div_two_le_tsum (f := fun j : ℕ => profC (2 * j + 1) s)
        (P := fun n : ℕ => Even n ∧ n ≠ 0) (N := N) (injOn_even_div_two N)
        (fun j => profC_nonneg (2 * j + 1) s) (summable_profC_odd hs)
      have hri : riPsi s = ∑' j : ℕ, profC (2 * j + 1) s := rfl
      rw [hri]; exact hb
    have hB := sum_error_le (P := fun n : ℕ => Even n ∧ n ≠ 0) (N := N) (s := s) (ε := ε) hε
      (injOn_even_div_two N)
    linarith

end Work.ChenPlan.LinearSieve.Assembly
