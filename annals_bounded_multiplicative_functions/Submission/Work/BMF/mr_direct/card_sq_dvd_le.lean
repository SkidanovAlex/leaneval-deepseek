import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Counting `n ∈ [X,2X]` divisible by the square of a prime in `[P,Q]`

We prove `Work.BMF.mr_direct.card_sq_dvd_le`: for `1 ≤ X`, `2 ≤ P ≤ Q`,

`#{n ∈ [X,2X] ∩ ℕ : ∃ p prime, P ≤ p ≤ Q, p² ∣ n} ≤ 4X/P`.

The proof is a union bound over the primes `p ∈ primeSet P Q`: the number of
multiples of `p²` in `[X,2X]` is at most `2X/p²`, and
`∑_{p prime, p ≥ P} 1/p² ≤ 2/P` (a telescoping tail bound for `∑ 1/n²`).
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open Finset

/-- Tail bound: for `2 ≤ m`, `∑_{m ≤ n ≤ N} 1/n² ≤ 2/m`. -/
private lemma sum_Icc_inv_sq_le (m N : ℕ) (hm : 2 ≤ m) :
    ∑ n ∈ Finset.Icc m N, ((n : ℝ) ^ 2)⁻¹ ≤ 2 / (m : ℝ) := by
  by_cases hN : m ≤ N
  · have hterm : ∀ n ∈ Finset.Icc m N,
        ((n : ℝ) ^ 2)⁻¹ ≤ (((n - 1 : ℕ) : ℝ))⁻¹ - ((n : ℝ))⁻¹ := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn2 : 2 ≤ n := le_trans hm hn.1
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [hcast]
      have hn2' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
      have hn' : (0:ℝ) < (n:ℝ) := by linarith
      have h1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
      rw [inv_sub_inv (ne_of_gt h1) (ne_of_gt hn')]
      have h2 : (n:ℝ) - ((n:ℝ) - 1) = 1 := by ring
      rw [h2, inv_eq_one_div]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ)^2)
        (by positivity : (0:ℝ) < ((n:ℝ)-1)*(n:ℝ))]
      nlinarith [sq_nonneg (n:ℝ)]
    have htel' : ∑ n ∈ Finset.Icc m N, (-((n:ℝ))⁻¹ - (-(((n - 1 : ℕ) : ℝ))⁻¹))
        = -((N:ℝ))⁻¹ - (-(((m-1:ℕ):ℝ))⁻¹) := by
      simpa using Finset.sum_Icc_sub hN (fun i : ℕ => -((((i - 1 : ℕ)) : ℝ))⁻¹)
    have htel : ∑ n ∈ Finset.Icc m N, ((((n - 1 : ℕ) : ℝ))⁻¹ - ((n : ℝ))⁻¹)
        = (((m-1:ℕ):ℝ))⁻¹ - ((N:ℝ))⁻¹ := by
      rw [show (∑ n ∈ Finset.Icc m N, ((((n - 1 : ℕ) : ℝ))⁻¹ - ((n : ℝ))⁻¹))
            = ∑ n ∈ Finset.Icc m N, (-((n:ℝ))⁻¹ - (-(((n - 1 : ℕ) : ℝ))⁻¹)) by
            apply Finset.sum_congr rfl; intro n _; ring]
      rw [htel']; ring
    calc ∑ n ∈ Finset.Icc m N, ((n : ℝ) ^ 2)⁻¹
        ≤ ∑ n ∈ Finset.Icc m N, ((((n - 1 : ℕ) : ℝ))⁻¹ - ((n : ℝ))⁻¹) :=
          Finset.sum_le_sum hterm
      _ = (((m - 1 : ℕ) : ℝ))⁻¹ - ((N : ℝ))⁻¹ := htel
      _ ≤ 2 / (m : ℝ) := by
          have hNinv : (0:ℝ) ≤ ((N:ℝ))⁻¹ := by positivity
          have hm1cast : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
          have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
          have h1 : (0:ℝ) < (m:ℝ) - 1 := by linarith
          have h2 : (0:ℝ) < (m:ℝ) := by linarith
          have hle : (((m - 1 : ℕ) : ℝ))⁻¹ ≤ 2 / (m:ℝ) := by
            rw [hm1cast, inv_eq_one_div, div_le_div_iff₀ h1 h2]
            linarith
          linarith
  · push Not at hN
    have hzero : ∑ n ∈ Finset.Icc m N, ((n : ℝ) ^ 2)⁻¹ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [Finset.mem_Icc] at hn
      exfalso; omega
    rw [hzero]
    have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    positivity

/-- The multiples of `q ≥ 1` in `{1, …, N}` number at most `N / q`. -/
lemma card_filter_dvd_le (N q : ℕ) (hq : 0 < q) :
    ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card ≤ N / q := by
  have hinj : Set.InjOn (fun n : ℕ => n / q)
      ↑((Finset.Icc 1 N).filter (fun n => q ∣ n)) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    change a / q = b / q at hab
    calc a = a / q * q := (Nat.div_mul_cancel ha.2).symm
      _ = b / q * q := by rw [hab]
      _ = b := Nat.div_mul_cancel hb.2
  have hsub : ((Finset.Icc 1 N).filter (fun n => q ∣ n)).image (fun n => n / q)
      ⊆ Finset.Icc 1 (N / q) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
    rw [Finset.mem_Icc]
    exact ⟨(Nat.le_div_iff_mul_le hq).mpr (by simpa using Nat.le_of_dvd (by omega : 0 < n) hdvd),
      Nat.div_le_div_right hnN⟩
  calc ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card
      = (((Finset.Icc 1 N).filter (fun n => q ∣ n)).image (fun n => n / q)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (N / q)).card := Finset.card_le_card hsub
    _ = N / q := by simp

/-- At most `2X / p²` elements of `natIcc X (2X)` are divisible by `p²` (`p ≥ 2`). -/
lemma card_filter_sq_dvd_le (X : ℝ) (hX : 1 ≤ X) (p : ℕ) (hp : 2 ≤ p) :
    (((Work.BMF.natIcc X (2 * X)).filter (fun n => p * p ∣ n)).card : ℝ)
      ≤ 2 * X / (p : ℝ) ^ 2 := by
  have hp0 : 0 < p := by omega
  have hq0 : 0 < p * p := Nat.mul_pos hp0 hp0
  have h1ceil : (1:ℕ) ≤ ⌈X⌉₊ := by
    have h : (1:ℝ) ≤ (⌈X⌉₊ : ℝ) := le_trans hX (Nat.le_ceil X)
    exact_mod_cast h
  have hsub : (Work.BMF.natIcc X (2*X)).filter (fun n => p*p ∣ n)
      ⊆ (Finset.Icc 1 ⌊2*X⌋₊).filter (fun n => p*p ∣ n) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    obtain ⟨hnB, hdvd⟩ := hn
    refine ⟨?_, hdvd⟩
    rw [Work.BMF.natIcc, Finset.mem_Icc] at hnB
    rw [Finset.mem_Icc]
    exact ⟨le_trans h1ceil hnB.1, hnB.2⟩
  have hcard := card_filter_dvd_le ⌊2*X⌋₊ (p*p) hq0
  calc (((Work.BMF.natIcc X (2*X)).filter (fun n => p*p ∣ n)).card : ℝ)
      ≤ (((Finset.Icc 1 ⌊2*X⌋₊).filter (fun n => p*p ∣ n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((⌊2*X⌋₊ / (p*p) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ ((⌊2*X⌋₊ : ℝ) / ((p*p : ℕ) : ℝ)) := Nat.cast_div_le
    _ ≤ (2*X) / ((p*p : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)
    _ = 2*X/(p:ℝ)^2 := by push_cast; ring

/-- The primes in `[P,Q]` contribute at most `2/P` to `∑ 1/p²` (for `P ≥ 2`). -/
lemma sum_primeSet_inv_sq_le (P Q : ℝ) (hP : 2 ≤ P) :
    ∑ p ∈ Work.BMF.mrDirect.primeSet P Q, ((p : ℝ) ^ 2)⁻¹ ≤ 2 / P := by
  have hPpos : (0:ℝ) < P := by linarith
  have hsub : Work.BMF.mrDirect.primeSet P Q ⊆ Finset.Icc ⌈P⌉₊ ⌊Q⌋₊ := by
    intro p hp
    rw [Work.BMF.mrDirect.primeSet, Finset.mem_filter] at hp
    exact hp.1
  have hceil : 2 ≤ ⌈P⌉₊ := by
    have h : (2:ℝ) ≤ (⌈P⌉₊ : ℝ) := le_trans hP (Nat.le_ceil P)
    exact_mod_cast h
  calc ∑ p ∈ Work.BMF.mrDirect.primeSet P Q, ((p:ℝ)^2)⁻¹
      ≤ ∑ p ∈ Finset.Icc ⌈P⌉₊ ⌊Q⌋₊, ((p:ℝ)^2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ ≤ 2 / (⌈P⌉₊ : ℝ) := sum_Icc_inv_sq_le ⌈P⌉₊ ⌊Q⌋₊ hceil
    _ ≤ 2 / P := div_le_div_of_nonneg_left (by norm_num) hPpos (Nat.le_ceil P)

lemma card_sq_dvd_le (X P Q : ℝ) (hX : 1 ≤ X) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ((Work.BMF.natIcc X (2 * X)).filter
        (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p * p ∣ n)).card
      ≤ 4 * X / P := by
  classical
  have hQ0 : (0:ℝ) ≤ Q := le_trans (by linarith : (0:ℝ) ≤ P) hPQ
  have hbound : ∀ p ∈ Work.BMF.mrDirect.primeSet P Q,
      (((Work.BMF.natIcc X (2*X)).filter (fun n => p*p ∣ n)).card : ℝ)
        ≤ 2*X/(p:ℝ)^2 := by
    intro p hp
    have hpprime : p.Prime := ((Work.BMF.mrDirect.mem_primeSet hQ0).mp hp).1
    exact card_filter_sq_dvd_le X hX p hpprime.two_le
  have hsub : ((Work.BMF.natIcc X (2*X)).filter
        (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p*p ∣ n))
      ⊆ (Work.BMF.mrDirect.primeSet P Q).biUnion
          (fun p => (Work.BMF.natIcc X (2*X)).filter (fun n => p*p ∣ n)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnB, p, hpσ, hpdvd⟩ := hn
    exact Finset.mem_biUnion.mpr ⟨p, hpσ, Finset.mem_filter.mpr ⟨hnB, hpdvd⟩⟩
  calc (((Work.BMF.natIcc X (2*X)).filter
          (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p*p ∣ n)).card : ℝ)
      ≤ (((Work.BMF.mrDirect.primeSet P Q).biUnion
          (fun p => (Work.BMF.natIcc X (2*X)).filter (fun n => p*p ∣ n))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Work.BMF.mrDirect.primeSet P Q,
          (((Work.BMF.natIcc X (2*X)).filter (fun n => p*p ∣ n)).card : ℝ) := by
        have h := Finset.card_biUnion_le (s := Work.BMF.mrDirect.primeSet P Q)
          (t := fun p => (Work.BMF.natIcc X (2*X)).filter (fun n => p*p ∣ n))
        calc _ ≤ ((∑ p ∈ Work.BMF.mrDirect.primeSet P Q,
              ((Work.BMF.natIcc X (2*X)).filter (fun n => p*p ∣ n)).card : ℕ) : ℝ) := by
              exact_mod_cast h
          _ = ∑ p ∈ Work.BMF.mrDirect.primeSet P Q,
              (((Work.BMF.natIcc X (2*X)).filter (fun n => p*p ∣ n)).card : ℝ) := by
              push_cast; rfl
    _ ≤ ∑ p ∈ Work.BMF.mrDirect.primeSet P Q, 2*X/(p:ℝ)^2 := Finset.sum_le_sum hbound
    _ = 2*X * ∑ p ∈ Work.BMF.mrDirect.primeSet P Q, ((p:ℝ)^2)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [div_eq_mul_inv]
    _ ≤ 2*X * (2/P) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact sum_primeSet_inv_sq_le P Q hP
    _ = 4*X / P := by field_simp; ring

end Work.BMF.mr_direct
