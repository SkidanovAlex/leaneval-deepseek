import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.PrimeCounting

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- The correction term for a prime index `n`:
`log(n/(n-1)) - 1/n`. -/
def corrTerm (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) / ((n : ℝ) - 1)) - (1 : ℝ) / (n : ℝ)

/-- The extension of `corrTerm` by zero to all naturals. -/
def corrExt (n : ℕ) : ℝ := if Nat.Prime n then corrTerm n else 0

lemma corr_log_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) / ((n : ℝ) - 1)) ≤ 1 / ((n : ℝ) - 1) := by
  have hr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hr' : (n : ℝ) - 1 ≠ 0 := ne_of_gt hnm1
  have hx : 0 < (n : ℝ) / ((n : ℝ) - 1) := div_pos hr hnm1
  have hlog := Real.log_le_sub_one_of_pos hx
  calc
    Real.log ((n : ℝ) / ((n : ℝ) - 1)) ≤ (n : ℝ) / ((n : ℝ) - 1) - 1 := hlog
    _ = 1 / ((n : ℝ) - 1) := by
      field_simp [hr']
      ring

lemma corr_log_ge_inv {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / (n : ℝ) ≤ Real.log ((n : ℝ) / ((n : ℝ) - 1)) := by
  have hr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hnm1ne : (n : ℝ) - 1 ≠ 0 := ne_of_gt hnm1
  have hx2 : 0 < ((n : ℝ) - 1) / (n : ℝ) := div_pos hnm1 hr
  have hll := Real.log_le_sub_one_of_pos hx2
  have hstep_eq : ((n : ℝ) - 1) / (n : ℝ) - 1 = -((1 : ℝ) / (n : ℝ)) := by
    field_simp [hr]
    ring
  have hA : Real.log (((n : ℝ) - 1) / (n : ℝ)) ≤ -((1 : ℝ) / (n : ℝ)) := by
    simpa [hstep_eq] using hll
  have hrew : Real.log ((n : ℝ) / ((n : ℝ) - 1)) =
      -Real.log (((n : ℝ) - 1) / (n : ℝ)) := by
    rw [← Real.log_inv (((n : ℝ) - 1) / (n : ℝ))]
    congr 1
    field_simp [hr, hnm1ne]
  rw [hrew]
  exact le_neg_of_le_neg hA

lemma corrTerm_nonneg {n : ℕ} (hp : Nat.Prime n) : 0 ≤ corrTerm n := by
  exact sub_nonneg.mpr (corr_log_ge_inv (Nat.Prime.two_le hp))

lemma corrTerm_le_two_div_sq {n : ℕ} (hn : 2 ≤ n) : corrTerm n ≤ 2 / (n : ℝ) ^ 2 := by
  have hlog := corr_log_le hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnm1pos : 0 < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hr : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hnm1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt hnm1pos
  have hsq : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  have hprod : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hnpos hnm1pos
  have hmain : (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hprod hsq]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have h1 : Real.log ((n : ℝ) / ((n : ℝ) - 1)) - (1 : ℝ) / (n : ℝ) ≤
      (1 : ℝ) / ((n : ℝ) - 1) - (1 : ℝ) / (n : ℝ) := by
    exact sub_le_sub_right hlog _
  have heq : (1 : ℝ) / ((n : ℝ) - 1) - (1 : ℝ) / (n : ℝ) =
      (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp [hr, hnm1]
    ring
  calc
    corrTerm n = Real.log ((n : ℝ) / ((n : ℝ) - 1)) - (1 : ℝ) / (n : ℝ) := by rfl
    _ ≤ (1 : ℝ) / ((n : ℝ) - 1) - (1 : ℝ) / (n : ℝ) := h1
    _ = (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := heq
    _ ≤ 2 / (n : ℝ) ^ 2 := hmain

lemma corrExt_bound (n : ℕ) : ‖corrExt n‖ ≤ (2 : ℝ) / (n : ℝ) ^ 2 := by
  by_cases hp : Nat.Prime n
  · have hle : corrTerm n ≤ (2 : ℝ) / (n : ℝ) ^ 2 :=
      corrTerm_le_two_div_sq (Nat.Prime.two_le hp)
    simpa [corrExt, if_pos hp, Real.norm_eq_abs, abs_of_nonneg (corrTerm_nonneg hp)] using hle
  · simp [corrExt, if_neg hp]
    exact div_nonneg (by norm_num) (sq_nonneg ((n : ℝ)))

lemma summable_corrExt : Summable corrExt := by
  refine Summable.of_norm_bounded ?_ corrExt_bound
  have h₁ : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have h₂ : Summable (fun n : ℕ => (2 : ℝ) * (1 / (n : ℝ) ^ 2)) :=
    Summable.mul_left (2 : ℝ) h₁
  refine Summable.congr h₂ ?_
  intro n
  field_simp

lemma partial_sum_eq_range (m : ℕ) :
    (∑ p ∈ m.primesLE, corrTerm p) = ∑ k ∈ Finset.range (m + 1), corrExt k := by
  have hIcc : (Finset.Icc 0 m : Finset ℕ) = Finset.range (m + 1) := by
    ext k
    simp [Finset.mem_Icc, Nat.lt_succ_iff]
  rw [Nat.primesLE_eq_filter_Icc_zero, hIcc]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro p hp
  simp [corrExt]

lemma tsum_corrExt_eq :
    (∑' p : Nat.Primes, corrTerm p) = ∑' n : ℕ, corrExt n := by
  let b : Nat.Primes → ℝ := fun p => corrTerm p
  have hs : Function.support corrExt ⊆ {n : ℕ | Nat.Prime n} := by
    intro n hn
    by_contra hnp
    have hprime : Nat.Prime n := by
      by_contra h
      simp [corrExt, h] at hn
    exact hnp hprime
  have hiff := (hasSum_subtype_iff_of_support_subset (f := corrExt)
    (a := ∑' n : ℕ, corrExt n) (s := {n : ℕ | Nat.Prime n}) hs)
  have hL : HasSum (fun p : Nat.Primes => corrExt p.1) (∑' n : ℕ, corrExt n) :=
    hiff.2 (Summable.hasSum summable_corrExt)
  have hcong : ∀ p : Nat.Primes, b p = corrExt p.1 := by
    intro p
    simp [b, corrExt, p.2]
  have hbT : HasSum b (∑' n : ℕ, corrExt n) := HasSum.congr_fun hL (fun p => hcong p)
  have hb : (∑' p : Nat.Primes, b p) = ∑' n : ℕ, corrExt n := HasSum.tsum_eq hbT
  simpa [b] using hb

lemma tendsto_partial_range_add_one :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range (m + 1), corrExt k) atTop
      (nhds (∑' n : ℕ, corrExt n)) := by
  have h := Summable.tendsto_sum_tsum_nat summable_corrExt
  exact h.comp (Filter.tendsto_add_atTop_nat 1)

theorem corr_partial_sums_tendsto_tsum :
    Filter.Tendsto (fun x : ℝ =>
      ∑ p ∈ (⌊x⌋₊).primesLE,
        (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - (1 : ℝ) / p))
      Filter.atTop
      (nhds (∑' p : Nat.Primes,
        (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - (1 : ℝ) / p))) := by
  have hNat : Tendsto (fun m : ℕ => ∑ p ∈ m.primesLE, corrTerm p) atTop
      (nhds (∑' n : ℕ, corrExt n)) := by
    simpa [partial_sum_eq_range] using tendsto_partial_range_add_one
  have hFloor : Tendsto (fun x : ℝ => ∑ p ∈ (⌊x⌋₊).primesLE, corrTerm p) atTop
      (nhds (∑' n : ℕ, corrExt n)) := by
    exact hNat.comp (tendsto_nat_floor_atTop (α := ℝ))
  change Filter.Tendsto (fun x : ℝ => ∑ p ∈ (⌊x⌋₊).primesLE, corrTerm p) atTop
      (nhds (∑' p : Nat.Primes, corrTerm p))
  rw [tsum_corrExt_eq]
  exact hFloor

end

end Commons.NumberTheory.Mertens