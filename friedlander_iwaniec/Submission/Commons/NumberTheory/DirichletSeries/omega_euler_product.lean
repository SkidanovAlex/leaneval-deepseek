import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Submission.Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow

namespace Commons.NumberTheory.DirichletSeries

open scoped Topology
open Filter

lemma pow_card_primeFactors_le_const_mul_rpow (a eps : ℝ) (ha : 0 < a) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → a ^ n.primeFactors.card ≤ C * (n : ℝ) ^ eps := by
  rcases lt_or_ge (1:ℝ) a with hlt | hle
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, a ≤ (2:ℝ)^k := by
      have h := tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < 2 by norm_num)
      have h2 : ∀ᶠ n : ℕ in Filter.atTop, a ≤ (2:ℝ)^n := h.eventually (eventually_ge_atTop a)
      exact (Filter.eventually_atTop.mp h2).imp (fun n hn => hn n le_rfl)
    have hkne : k ≠ 0 := by
      rintro rfl
      simp only [pow_zero] at hk
      linarith
    have hkR : ((k:ℝ)) ≠ 0 := by exact_mod_cast hkne
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hkne
    obtain ⟨C0, hC0pos, hC0⟩ :=
      Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow (eps/k) (div_pos heps hkpos)
    refine ⟨C0 ^ k, pow_pos hC0pos k, fun n hn => ?_⟩
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have h1 : a ^ n.primeFactors.card ≤ ((2:ℝ)^k) ^ n.primeFactors.card :=
      pow_le_pow_left₀ ha.le hk _
    have h2 : ((2:ℝ)^k) ^ n.primeFactors.card = ((2:ℝ)^n.primeFactors.card)^k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have h3 : ((2:ℝ)^n.primeFactors.card)^k ≤ (C0 * (n:ℝ)^(eps/k))^k :=
      pow_le_pow_left₀ (by positivity) (hC0 n hn) k
    have h4 : (C0 * (n:ℝ)^(eps/k))^k = C0^k * (n:ℝ)^eps := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, div_mul_cancel₀ _ hkR]
    calc a ^ n.primeFactors.card ≤ ((2:ℝ)^k) ^ n.primeFactors.card := h1
      _ = ((2:ℝ)^n.primeFactors.card)^k := h2
      _ ≤ (C0 * (n:ℝ)^(eps/k))^k := h3
      _ = C0^k * (n:ℝ)^eps := h4
  · refine ⟨1, one_pos, fun n hn => ?_⟩
    have h1 : a ^ n.primeFactors.card ≤ 1 := pow_le_one₀ ha.le hle
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ eps := Real.one_le_rpow (by exact_mod_cast hn) (le_of_lt heps)
    calc a ^ n.primeFactors.card ≤ 1 := h1
      _ ≤ 1 * (n : ℝ) ^ eps := by rw [one_mul]; exact h2

lemma summable_norm_omega_cpow (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖(z ^ n.primeFactors.card) * (n : ℂ) ^ (-s)‖) := by
  obtain ⟨C, hCpos, hC⟩ :=
    pow_card_primeFactors_le_const_mul_rpow (‖z‖+1) ((s.re - 1)/2) (by positivity) (by linarith)
  have hσeps : 1 < s.re - (s.re - 1)/2 := by linarith
  have hmaj : Summable (fun n : ℕ => C * (n:ℝ) ^ (-(s.re - (s.re-1)/2))) := by
    have hbase : Summable (fun n : ℕ => (n:ℝ) ^ (-(s.re - (s.re-1)/2))) := by
      have h := (Real.summable_nat_rpow_inv (p := s.re - (s.re-1)/2)).mpr hσeps
      refine h.congr (fun n => ?_)
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
    simpa using hbase.mul_left C
  refine hmaj.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hz : ((0:ℕ):ℂ) ^ (-s) = 0 := by
      rw [Nat.cast_zero]
      exact Complex.zero_cpow (neg_ne_zero.mpr (Complex.ne_zero_of_one_lt_re hs))
    have hr : ((0:ℕ):ℝ) ^ (-(s.re - (s.re-1)/2)) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (ne_of_lt (by linarith : -(s.re-(s.re-1)/2) < 0))
    rw [Nat.primeFactors_zero, Finset.card_empty, pow_zero, one_mul, hz, hr, norm_zero, mul_zero]
  · rw [norm_mul, norm_pow]
    have hn1 : 1 ≤ n := hn
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    have hcp : ‖(n : ℂ) ^ (-s)‖ = (n:ℝ)^(-(s.re)) := by
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hnR]
      simp
    rw [hcp]
    have hb : ‖z‖ ^ n.primeFactors.card ≤ (‖z‖+1) ^ n.primeFactors.card :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
    have hb2 := hC n hn1
    calc ‖z‖ ^ n.primeFactors.card * (n:ℝ)^(-(s.re))
        ≤ (‖z‖+1) ^ n.primeFactors.card * (n:ℝ)^(-(s.re)) :=
          mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ (C * (n:ℝ)^((s.re-1)/2)) * (n:ℝ)^(-(s.re)) :=
          mul_le_mul_of_nonneg_right hb2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = C * (n:ℝ)^(-(s.re - (s.re-1)/2)) := by
          rw [mul_assoc, ← Real.rpow_add hnR]
          congr 2
          ring


private lemma local_factor (z : ℂ) {s : ℂ} (hs : 1 < s.re) (p : ℕ) (hp : p.Prime) :
    (∑' e : ℕ, (z ^ (p ^ e).primeFactors.card) * ((p ^ e : ℕ) : ℂ) ^ (-s)) =
      (1 + (z - 1) * (p : ℂ) ^ (-s)) * (1 - (p : ℂ) ^ (-s))⁻¹ := by
  set q : ℂ := (p : ℂ) ^ (-s) with hqdef
  have hp2 : 2 ≤ p := hp.two_le
  have hsumall : Summable (fun n : ℕ => (z ^ n.primeFactors.card) * (n : ℂ) ^ (-s)) :=
    (summable_norm_omega_cpow z hs).of_norm
  have hsumm : Summable
      (fun e : ℕ => (z ^ (p ^ e).primeFactors.card) * ((p ^ e : ℕ) : ℂ) ^ (-s)) :=
    hsumall.comp_injective (Nat.pow_right_injective hp2)
  have hqnorm : ‖q‖ = (p:ℝ)^(-(s.re)) := by
    rw [hqdef, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.pos)]
    simp
  have hqlt : ‖q‖ < 1 := by
    rw [hqnorm, Real.rpow_neg (Nat.cast_nonneg p)]
    refine inv_lt_one_of_one_lt₀ ?_
    exact Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (lt_trans one_pos hs)
  have hqne : q ≠ 1 := by
    intro h
    rw [h] at hqlt
    simp at hqlt
  have h1q : (1:ℂ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hqne)
  have hgeom : ∑' e : ℕ, q ^ e = (1 - q)⁻¹ := tsum_geometric_of_norm_lt_one hqlt
  have hqsum : Summable (fun e : ℕ => q ^ e) := summable_geometric_of_norm_lt_one hqlt
  have hshift : ∑' e : ℕ, q ^ (e+1) = (1 - q)⁻¹ - 1 := by
    have h := hqsum.tsum_eq_zero_add
    rw [hgeom, pow_zero] at h
    rw [h]; ring
  have hterm : ∀ e : ℕ,
      (z ^ (p ^ (e+1)).primeFactors.card) * ((p ^ (e+1) : ℕ) : ℂ) ^ (-s) = z * q ^ (e+1) := by
    intro e
    have hcard : (p ^ (e+1)).primeFactors.card = 1 := by
      rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero e) hp, Finset.card_singleton]
    rw [hcard, pow_one]
    congr 1
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, mul_comm, Complex.cpow_mul_nat, hqdef]
  have hf1 : (z ^ (p ^ 0).primeFactors.card) * ((p ^ 0 : ℕ) : ℂ) ^ (-s) = 1 := by
    simp
  have hmain : (∑' e : ℕ, (z ^ (p ^ e).primeFactors.card) * ((p ^ e : ℕ) : ℂ) ^ (-s))
      = 1 + z * ((1 - q)⁻¹ - 1) := by
    rw [hsumm.tsum_eq_zero_add, hf1, tsum_congr hterm, tsum_mul_left, hshift]
  rw [hmain]
  field_simp
  ring

theorem omega_euler_product (z : ℂ) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (z ^ n.primeFactors.card) * (n : ℂ) ^ (-s))
      = riemannZeta s * ∏' p : Nat.Primes, (1 + (z - 1) * ((p : ℕ) : ℂ) ^ (-s)) := by
  let f : ℕ → ℂ := fun n => (z ^ n.primeFactors.card) * (n : ℂ) ^ (-s)
  change (∑' n, f n)
      = riemannZeta s * ∏' p : Nat.Primes, (1 + (z - 1) * ((p : ℕ) : ℂ) ^ (-s))
  have hf1 : f 1 = 1 := by simp [f]
  have hf0 : f 0 = 0 := by
    change (z ^ (0:ℕ).primeFactors.card) * ((0:ℕ):ℂ) ^ (-s) = 0
    rw [Nat.primeFactors_zero, Finset.card_empty, pow_zero, one_mul]
    simpa using Complex.zero_cpow (neg_ne_zero.mpr (Complex.ne_zero_of_one_lt_re hs))
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    change (z ^ (m*n).primeFactors.card) * (((m*n:ℕ)) : ℂ) ^ (-s)
      = (z ^ m.primeFactors.card * (m:ℂ)^(-s)) * (z ^ n.primeFactors.card * (n:ℂ)^(-s))
    rw [hmn.primeFactors_mul, Finset.card_union_of_disjoint hmn.disjoint_primeFactors, pow_add,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hsum : Summable (fun n => ‖f n‖) := summable_norm_omega_cpow z hs
  have heuler := EulerProduct.eulerProduct_tprod (f := f) hf1 hmul hsum hf0
  rw [← heuler]
  have hprimes : Summable (fun p : Nat.Primes => ‖((p:ℕ):ℂ)^(-s)‖) := by
    have h := summable_riemannZetaSummand (s := s) hs
    have h2 : Summable (fun n : ℕ => ‖(n:ℂ)^(-s)‖) := by simpa [riemannZetaSummandHom] using h
    exact h2.comp_injective Nat.Primes.coe_nat_injective
  have hAsum : Summable (fun p : Nat.Primes => ‖(z-1) * ((p:ℕ):ℂ)^(-s)‖) := by
    simp_rw [norm_mul]
    exact hprimes.mul_left ‖z-1‖
  have hA : Multipliable (fun p : Nat.Primes => 1 + (z-1) * ((p:ℕ):ℂ)^(-s)) :=
    multipliable_one_add_of_summable hAsum
  have hB : Multipliable (fun p : Nat.Primes => (1 - ((p:ℕ):ℂ)^(-s))⁻¹) :=
    (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hloc : ∀ p : Nat.Primes,
      (∑' e : ℕ, f ((p:ℕ)^e))
        = (1 + (z-1)*((p:ℕ):ℂ)^(-s)) * (1 - ((p:ℕ):ℂ)^(-s))⁻¹ := by
    intro p
    simpa only [f] using local_factor z hs (p:ℕ) p.2
  rw [show (∏' p : Nat.Primes, ∑' e : ℕ, f ((p:ℕ)^e))
        = ∏' p : Nat.Primes, ((1 + (z-1)*((p:ℕ):ℂ)^(-s)) * (1 - ((p:ℕ):ℂ)^(-s))⁻¹)
        from tprod_congr (fun p => hloc p)]
  rw [Multipliable.tprod_mul hA hB, riemannZeta_eulerProduct_tprod hs]
  ring

end Commons.NumberTheory.DirichletSeries