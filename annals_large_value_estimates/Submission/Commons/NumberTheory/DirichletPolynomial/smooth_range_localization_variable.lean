import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.RootsOfUnity.Complex
import Submission.Commons.NumberTheory.DirichletPolynomial.smooth_range_localization

namespace Commons.NumberTheory.DirichletPolynomial

open Finset

set_option maxHeartbeats 1600000

noncomputable section

/-- The (normalised) Dirichlet interval sum `∑_{a≤n≤b} n^{-1/2+iθ}`. -/
def ivSum (a b : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc a b, (n : ℂ) ^ (Complex.I * ((θ : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)


/-! ## Auxiliary analytic tools (roots of unity, geometric sums, harmonic bounds) -/

def zeta (K : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (K : ℂ))

lemma zeta_isPrimitiveRoot (K : ℕ) (hK : 0 < K) : IsPrimitiveRoot (zeta K) K := by
  have := Complex.isPrimitiveRoot_exp K (Nat.pos_iff_ne_zero.mp hK)
  simpa [zeta] using this

-- main orthogonality
theorem zeta_pow_orthogonality (K : ℕ) (hK : 0 < K) (n m : ℕ) (hn : n < K) (hm : m < K) :
    (∑ α ∈ Finset.range K,
        (zeta K ^ n * (zeta K ^ m)⁻¹) ^ α)
      = if n = m then (K : ℂ) else 0 := by
  have hζ := zeta_isPrimitiveRoot K hK
  have hζne : zeta K ≠ 0 := hζ.ne_zero (Nat.pos_iff_ne_zero.mp hK)
  set w : ℂ := zeta K ^ n * (zeta K ^ m)⁻¹ with hw
  have h1p : (zeta K ^ n) ^ K = 1 := by
    rw [← pow_mul, mul_comm n K, pow_mul, hζ.pow_eq_one, one_pow]
  have h2p : (zeta K ^ m) ^ K = 1 := by
    rw [← pow_mul, mul_comm m K, pow_mul, hζ.pow_eq_one, one_pow]
  have hwpow : w ^ K = 1 := by
    rw [hw, mul_pow, inv_pow, h1p, h2p, inv_one, mul_one]
  have hwiff : w = 1 ↔ n = m := by
    constructor
    · intro h1
      have hzpow : w = (zeta K) ^ ((n : ℤ) - (m : ℤ)) := by
        rw [hw, zpow_sub₀ hζne, zpow_natCast, zpow_natCast, div_eq_mul_inv]
      have h2 : (zeta K) ^ ((n : ℤ) - (m : ℤ)) = 1 := by rw [← hzpow]; exact h1
      have h3 : (K : ℤ) ∣ ((n : ℤ) - (m : ℤ)) := (hζ.zpow_eq_one_iff_dvd _).mp h2
      obtain ⟨c, hc⟩ := h3
      have hK' : (0:ℤ) < (K:ℤ) := by exact_mod_cast hK
      have hn' : (n : ℤ) < (K : ℤ) := by exact_mod_cast hn
      have hlt : |((n:ℤ) - (m:ℤ))| < (K:ℤ) := by
        rw [abs_lt]
        constructor
        · have hm0 : (0:ℤ) ≤ (m:ℤ) := Nat.cast_nonneg m
          linarith
        · have hn0 : (0:ℤ) ≤ (n:ℤ) := Nat.cast_nonneg n
          linarith
      have hc0 : c = 0 := by
        by_contra hne
        have h1 : (1:ℤ) ≤ |c| := Int.one_le_abs hne
        have h2 : |(K:ℤ) * c| = (K:ℤ) * |c| := by rw [abs_mul, abs_of_pos hK']
        have : (K:ℤ) ≤ |((n:ℤ)-(m:ℤ))| := by rw [hc, h2]; nlinarith
        linarith
      have : (n:ℤ) = (m:ℤ) := by
        rw [hc0, mul_zero] at hc
        omega
      omega
    · intro h
      subst h
      rw [hw]
      exact mul_inv_cancel₀ (pow_ne_zero _ hζne)
  by_cases h : n = m
  · rw [if_pos h]
    have hw1 : w = 1 := hwiff.mpr h
    rw [hw1]
    simp
  · rw [if_neg h]
    have hwne : w ≠ 1 := fun hh => h (hwiff.mp hh)
    rw [geom_sum_eq hwne K, hwpow]
    simp





lemma mul_sum_Icc_pow (z : ℂ) {lo hi : ℕ} (h : lo ≤ hi) :
    (z - 1) * ∑ n ∈ Finset.Icc lo hi, z ^ n = z ^ (hi + 1) - z ^ lo := by
  rw [Finset.Icc_eq_cons_Ico h, Finset.sum_cons, Finset.sum_Ico_eq_sum_range]
  rw [mul_add]
  have h1 : (z - 1) * ∑ k ∈ Finset.range (hi - lo), z ^ (lo + k) = z ^ hi - z ^ lo := by
    have hstep : ∑ k ∈ Finset.range (hi - lo), z ^ (lo + k)
        = z ^ lo * ∑ k ∈ Finset.range (hi - lo), z ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]
    rw [hstep]
    have h2 : (z - 1) * (z ^ lo * ∑ k ∈ Finset.range (hi - lo), z ^ k)
        = z ^ lo * ((z - 1) * ∑ k ∈ Finset.range (hi - lo), z ^ k) := by ring
    rw [h2, mul_geom_sum]
    have hlt : lo + (hi - lo) = hi := Nat.add_sub_cancel' h
    rw [mul_sub, mul_one, ← pow_add, hlt]
  rw [h1]
  have h3 : (z - 1) * z ^ hi = z ^ (hi+1) - z ^ hi := by rw [sub_mul, one_mul, pow_succ']
  rw [h3]
  ring

lemma norm_sum_Icc_pow_le {z : ℂ} (hz1 : ‖z‖ = 1) (hz : z ≠ 1) {lo hi : ℕ} (h : lo ≤ hi) :
    ‖∑ n ∈ Finset.Icc lo hi, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  have hpos : 0 < ‖z - 1‖ := by
    rcases lt_or_eq_of_le (norm_nonneg (z-1)) with h' | h'
    · exact h'
    · exfalso; apply hz; exact sub_eq_zero.mp (norm_eq_zero.mp h'.symm)
  have hkey := mul_sum_Icc_pow z h
  have hnorm : ‖z - 1‖ * ‖∑ n ∈ Finset.Icc lo hi, z ^ n‖
      = ‖z ^ (hi+1) - z ^ lo‖ := by
    rw [← norm_mul, hkey]
  have hb : ‖z ^ (hi+1) - z ^ lo‖ ≤ 2 := by
    have h1 : ‖z ^ (hi+1)‖ = 1 := by rw [norm_pow, hz1, one_pow]
    have h2 : ‖z ^ lo‖ = 1 := by rw [norm_pow, hz1, one_pow]
    calc ‖z ^ (hi+1) - z ^ lo‖ ≤ ‖z ^ (hi+1)‖ + ‖z ^ lo‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  rw [le_div_iff₀ hpos, mul_comm]
  rw [hnorm]
  exact hb


lemma zeta_eq (K : ℕ) : zeta K = Complex.exp (((2 * Real.pi / K : ℝ) : ℂ) * Complex.I) := by
  rw [zeta]
  congr 1
  push_cast
  ring

lemma zeta_eq' (K : ℕ) : zeta K = Complex.exp (Complex.I * ((2 * Real.pi / K : ℝ) : ℂ)) := by
  rw [zeta_eq, mul_comm]

lemma norm_zeta (K : ℕ) : ‖zeta K‖ = 1 := by
  rw [zeta_eq, Complex.norm_exp_ofReal_mul_I]

lemma zeta_pow_eq (K α : ℕ) : (zeta K)^α = Complex.exp (Complex.I * ((2 * Real.pi * α / K : ℝ) : ℂ)) := by
  rw [zeta_eq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma norm_zeta_pow_sub_one (K : ℕ) (hK : 0 < K) {α : ℕ} (hα : α ≤ K) :
    ‖(zeta K)^α - 1‖ = 2 * Real.sin (Real.pi * α / K) := by
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have h2 : 0 ≤ Real.sin (Real.pi * (α:ℝ) / (K:ℝ)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · apply div_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (Nat.cast_nonneg α)) (le_of_lt hKpos)
    · rw [div_le_iff₀ hKpos]
      have hα' : (α:ℝ) ≤ (K:ℝ) := by exact_mod_cast hα
      nlinarith [Real.pi_pos]
  rw [zeta_pow_eq, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * ↑α / ↑K) / 2 = Real.pi * ↑α / ↑K from by ring]
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h2])]

lemma norm_zeta_pow (K α : ℕ) : ‖(zeta K)^α‖ = 1 := by
  rw [norm_pow, norm_zeta, one_pow]

lemma zeta_pow_ne_one (K : ℕ) (hK : 0 < K) {α : ℕ} (h1 : 1 ≤ α) (h2 : α < K) :
    zeta K ^ α ≠ 1 := by
  intro h
  have hζ := zeta_isPrimitiveRoot K hK
  have hdiv : K ∣ α := (hζ.pow_eq_one_iff_dvd α).mp h
  obtain ⟨c, hc⟩ := hdiv
  have hc0 : c = 0 := by
    by_contra hne
    have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hne
    have hK1 : K * c ≥ K := by
      calc K * c ≥ K * 1 := Nat.mul_le_mul_left K hc1
        _ = K := by ring
    omega
  subst hc0
  omega

lemma norm_sum_Icc_zeta_pow_le (K : ℕ) (hK : 0 < K) {α : ℕ} (h1 : 1 ≤ α) (h2 : α < K)
    {lo hi : ℕ} (h : lo ≤ hi) :
    ‖∑ n ∈ Finset.Icc lo hi, (zeta K ^ α) ^ n‖ ≤ 1 / Real.sin (Real.pi * α / K) := by
  have hbound := norm_sum_Icc_pow_le (norm_zeta_pow K α) (zeta_pow_ne_one K hK h1 h2) h
  have hsub := norm_zeta_pow_sub_one K hK (le_of_lt h2)
  rw [hsub] at hbound
  have hs : 0 < Real.sin (Real.pi * ↑α / ↑K) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · apply div_pos (mul_pos Real.pi_pos (by exact_mod_cast h1)) (by exact_mod_cast hK)
    · rw [div_lt_iff₀ (by exact_mod_cast hK)]
      have hα' : (α:ℝ) < (K:ℝ) := by exact_mod_cast h2
      nlinarith [Real.pi_pos]
  calc ‖∑ n ∈ Finset.Icc lo hi, (zeta K ^ α) ^ n‖ ≤ 2 / (2 * Real.sin (Real.pi * ↑α / ↑K)) := hbound
    _ = 1 / Real.sin (Real.pi * ↑α / ↑K) := by field_simp



lemma card_Icc_le (B a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ B) : (Finset.Icc a b).card ≤ B := by
  rcases lt_or_ge b a with h | h
  · rw [Finset.Icc_eq_empty (not_le.mpr h)]; simp
  · rw [Nat.card_Icc]; omega



lemma Icc_one_eq_Ico (K : ℕ) : Finset.Icc 1 (K-1) = Finset.Ico 1 K := by
  ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

lemma inv_sin_le_two_terms (K : ℕ) (hK : 0 < K) {α : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ K - 1) :
    (1:ℝ) / Real.sin (Real.pi * α / K)
      ≤ (K:ℝ) / (2 * (α:ℝ)) + (K:ℝ) / (2 * ((K:ℝ) - (α:ℝ))) := by
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hαpos : (0:ℝ) < (α:ℝ) := by exact_mod_cast h1
  have hαK : (α:ℝ) < (K:ℝ) := by
    have : α < K := by omega
    exact_mod_cast this
  have hx0 : 0 ≤ Real.pi * (α:ℝ) / (K:ℝ) :=
    div_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (le_of_lt hαpos)) (le_of_lt hKpos)
  have hsecond_nonneg : 0 ≤ (K:ℝ) / (2 * ((K:ℝ) - (α:ℝ))) := by
    apply div_nonneg (le_of_lt hKpos)
    have : (0:ℝ) < (K:ℝ) - (α:ℝ) := by linarith
    linarith
  rcases Nat.lt_or_ge K (2*α) with hcase | hcase
  · have hcase' : (K:ℝ) < 2 * (α:ℝ) := by exact_mod_cast hcase
    have hsub1 : (1:ℝ) ≤ (K:ℝ) - (α:ℝ) := by
      have h : 1 ≤ K - α := by omega
      rw [← Nat.cast_sub (show α ≤ K by omega)]
      exact_mod_cast h
    have hsubpos : (0:ℝ) < (K:ℝ) - (α:ℝ) := by linarith
    have hx : Real.pi * ((K:ℝ) - (α:ℝ)) / (K:ℝ) ≤ Real.pi / 2 := by
      rw [div_le_iff₀ hKpos]; nlinarith [Real.pi_pos]
    have hx0' : 0 ≤ Real.pi * ((K:ℝ) - (α:ℝ)) / (K:ℝ) :=
      div_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (le_of_lt hsubpos)) (le_of_lt hKpos)
    have hs := Real.mul_le_sin hx0' hx
    have hsin : 2 * ((K:ℝ) - (α:ℝ)) / (K:ℝ) ≤ Real.sin (Real.pi * ((K:ℝ) - (α:ℝ)) / (K:ℝ)) := by
      calc 2 * ((K:ℝ) - (α:ℝ)) / (K:ℝ)
          = (2/Real.pi) * (Real.pi * ((K:ℝ) - (α:ℝ)) / (K:ℝ)) := by field_simp
        _ ≤ Real.sin (Real.pi * ((K:ℝ) - (α:ℝ)) / (K:ℝ)) := hs
    have hspos : 0 < Real.sin (Real.pi * ((K:ℝ) - (α:ℝ)) / (K:ℝ)) := lt_of_lt_of_le (by positivity) hsin
    have heqsin : Real.sin (Real.pi * (α:ℝ) / (K:ℝ)) = Real.sin (Real.pi * ((K:ℝ) - (α:ℝ)) / (K:ℝ)) := by
      rw [show Real.pi * ((K:ℝ) - (α:ℝ)) / (K:ℝ) = Real.pi - Real.pi * (α:ℝ) / (K:ℝ) from by
        field_simp]
      rw [Real.sin_pi_sub]
    rw [heqsin]
    have hle := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2*((K:ℝ)-(α:ℝ))/(K:ℝ)) hsin
    have heq : (1:ℝ) / (2 * ((K:ℝ) - (α:ℝ)) / (K:ℝ)) = (K:ℝ)/(2*((K:ℝ)-(α:ℝ))) := by field_simp
    rw [heq] at hle
    have hfirst_nonneg : 0 ≤ (K:ℝ) / (2 * (α:ℝ)) := by positivity
    linarith [hle, hfirst_nonneg]
  · have hcase' : (2:ℝ) * (α:ℝ) ≤ (K:ℝ) := by exact_mod_cast hcase
    have hx : Real.pi * (α:ℝ) / (K:ℝ) ≤ Real.pi / 2 := by
      rw [div_le_iff₀ hKpos]; nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin hx0 hx
    have hsin : 2 * (α:ℝ) / (K:ℝ) ≤ Real.sin (Real.pi * (α:ℝ) / (K:ℝ)) := by
      calc 2 * (α:ℝ) / (K:ℝ) = (2/Real.pi) * (Real.pi * (α:ℝ) / (K:ℝ)) := by field_simp
        _ ≤ Real.sin (Real.pi * (α:ℝ) / (K:ℝ)) := hs
    have hspos : 0 < Real.sin (Real.pi * (α:ℝ) / (K:ℝ)) := lt_of_lt_of_le (by positivity) hsin
    have hle := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2*(α:ℝ)/(K:ℝ)) hsin
    have heq : (1:ℝ) / (2 * (α:ℝ) / (K:ℝ)) = (K:ℝ)/(2*(α:ℝ)) := by field_simp
    rw [heq] at hle
    linarith [hle, hsecond_nonneg]

lemma sum_inv_sin_le (K : ℕ) (hK : 0 < K) :
    ∑ α ∈ Finset.Icc 1 (K-1), (1:ℝ) / Real.sin (Real.pi * α / K)
      ≤ (K:ℝ) * (harmonic (K-1) : ℝ) := by
  rw [Icc_one_eq_Ico]
  have hpoint : ∑ α ∈ Finset.Ico 1 K, (1:ℝ) / Real.sin (Real.pi * α / K)
      ≤ ∑ α ∈ Finset.Ico 1 K, ((K:ℝ)/(2*(α:ℝ)) + (K:ℝ)/(2*((K:ℝ)-(α:ℝ)))) := by
    refine Finset.sum_le_sum fun α hα => ?_
    rw [Finset.mem_Ico] at hα
    exact inv_sin_le_two_terms K hK hα.1 (by omega)
  refine hpoint.trans ?_
  have hharm : ∑ α ∈ Finset.Ico 1 K, (1:ℝ) / (α:ℝ) = (harmonic (K-1) : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [harmonic]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hrefl : ∑ α ∈ Finset.Ico 1 K, (1:ℝ) / ((K:ℝ) - (α:ℝ))
      = ∑ α ∈ Finset.Ico 1 K, (1:ℝ)/(α:ℝ) := by
    have h := Finset.sum_Ico_reflect (fun j : ℕ => (1:ℝ)/(j:ℝ)) 1 (n := K) (m := K) (by omega)
    rw [show K + 1 - K = 1 by omega, show K + 1 - 1 = K by omega] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [Nat.cast_sub (le_of_lt hj.2)]
  have hsplit : ∑ α ∈ Finset.Ico 1 K, ((K:ℝ)/(2*(α:ℝ)) + (K:ℝ)/(2*((K:ℝ)-(α:ℝ))))
      = (K:ℝ)/2 * (∑ α ∈ Finset.Ico 1 K, (1:ℝ)/(α:ℝ))
        + (K:ℝ)/2 * (∑ α ∈ Finset.Ico 1 K, (1:ℝ)/((K:ℝ)-(α:ℝ))) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun α hα => ?_
      rw [Finset.mem_Ico] at hα
      have hαpos : (0:ℝ) < (α:ℝ) := by exact_mod_cast hα.1
      field_simp
    · refine Finset.sum_congr rfl fun α hα => ?_
      rw [Finset.mem_Ico] at hα
      have : (α:ℝ) < (K:ℝ) := by exact_mod_cast hα.2
      have : (0:ℝ) < (K:ℝ) - (α:ℝ) := by linarith
      field_simp
  rw [hsplit, hrefl, hharm]
  exact le_of_eq (by ring)



section FourierExpansion

/-- Finite Fourier expansion: the interval sum is recovered as an average of
"half-range Fourier transforms". -/
lemma fourier_expansion (K : ℕ) (hK : 0 < K) (c : ℕ → ℂ) (lo hi : ℕ) (_hlh : lo ≤ hi)
    (hhi : hi < K) (S : Finset ℕ) (hsub : Finset.Icc lo hi ⊆ S) (hSlt : ∀ n ∈ S, n < K) :
    (∑ α ∈ Finset.range K, (∑ n ∈ Finset.Icc lo hi, ((zeta K) ^ n) ^ α) *
        (∑ m ∈ S, (((zeta K) ^ m)⁻¹) ^ α * c m))
      = (K : ℂ) * ∑ n ∈ Finset.Icc lo hi, c n := by
  have expand : ∀ α : ℕ, (∑ n ∈ Finset.Icc lo hi, ((zeta K) ^ n) ^ α) *
        (∑ m ∈ S, (((zeta K) ^ m)⁻¹) ^ α * c m)
      = ∑ n ∈ Finset.Icc lo hi, ∑ m ∈ S, ((zeta K) ^ n * ((zeta K) ^ m)⁻¹) ^ α * c m := by
    intro α
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  have step1 : ∀ n ∈ Finset.Icc lo hi,
      (∑ α ∈ Finset.range K, ∑ m ∈ S, ((zeta K) ^ n * ((zeta K) ^ m)⁻¹) ^ α * c m)
      = (K : ℂ) * c n := by
    intro n hn
    rw [Finset.sum_comm]
    have hnK : n < K := lt_of_le_of_lt (Finset.mem_Icc.mp hn).2 hhi
    have hinner : ∀ m ∈ S,
        (∑ α ∈ Finset.range K, ((zeta K) ^ n * ((zeta K) ^ m)⁻¹) ^ α * c m)
        = (if n = m then (K : ℂ) else 0) * c m := by
      intro m hm
      rw [← Finset.sum_mul, zeta_pow_orthogonality K hK n m hnK (hSlt m hm)]
    rw [Finset.sum_congr rfl hinner]
    rw [show (∑ m ∈ S, (if n = m then (K : ℂ) else 0) * c m)
        = ∑ m ∈ S, (if n = m then (K : ℂ) * c m else 0) from by
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases h : n = m <;> simp [h]]
    rw [Finset.sum_ite_eq, if_pos (hsub hn)]
  rw [Finset.sum_congr rfl step1]
  rw [Finset.mul_sum]

end FourierExpansion

section CS

/-- Weighted Cauchy–Schwarz. -/
lemma cs_weighted (s : Finset ℕ) (F : ℕ → ℝ) (hF : ∀ α ∈ s, 0 < F α) (P Q : ℕ → ℂ) :
    ‖∑ α ∈ s, P α * Q α‖ ^ 2
      ≤ (∑ α ∈ s, ‖P α‖ ^ 2 / F α) * (∑ α ∈ s, F α * ‖Q α‖ ^ 2) := by
  have h1 : ‖∑ α ∈ s, P α * Q α‖
      ≤ ∑ α ∈ s, (‖P α‖ / Real.sqrt (F α)) * (Real.sqrt (F α) * ‖Q α‖) := by
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [norm_mul]
    have hFp : (0:ℝ) < F α := hF α hα
    have hs : Real.sqrt (F α) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hFp)
    field_simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun α => ‖P α‖ / Real.sqrt (F α)) (fun α => Real.sqrt (F α) * ‖Q α‖)
  have h3 : (∑ α ∈ s, (‖P α‖ / Real.sqrt (F α)) ^ 2) = ∑ α ∈ s, ‖P α‖ ^ 2 / F α := by
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [div_pow, Real.sq_sqrt (le_of_lt (hF α hα))]
  have h4 : (∑ α ∈ s, (Real.sqrt (F α) * ‖Q α‖) ^ 2) = ∑ α ∈ s, F α * ‖Q α‖ ^ 2 := by
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hF α hα))]
  rw [h3, h4] at h2
  have h5 : ‖∑ α ∈ s, P α * Q α‖ ^ 2 ≤ (∑ α ∈ s, (‖P α‖ / Real.sqrt (F α)) *
      (Real.sqrt (F α) * ‖Q α‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  linarith [h2, h5]

end CS

lemma swap_factor (R : ℕ) (t : Fin R → ℝ) (W : ℝ) (K : ℕ) (F : ℕ → ℝ)
    (Z : ℕ → Fin R → Fin R → ℝ) :
    (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then ∑ α ∈ Finset.range K, F α * Z α i j else 0))
      = ∑ α ∈ Finset.range K, F α *
          (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ W then Z α i j else 0)) := by
  have h1 : ∀ i j : Fin R, (if |t i - t j| ≤ W then ∑ α ∈ Finset.range K, F α * Z α i j else 0)
      = ∑ α ∈ Finset.range K, (if |t i - t j| ≤ W then F α * Z α i j else 0) := by
    intro i j
    by_cases h : |t i - t j| ≤ W <;> simp [h]
  simp_rw [h1]
  have h2 : ∀ i : Fin R, (∑ j : Fin R, ∑ α ∈ Finset.range K,
        (if |t i - t j| ≤ W then F α * Z α i j else 0))
      = ∑ α ∈ Finset.range K, ∑ j : Fin R, (if |t i - t j| ≤ W then F α * Z α i j else 0) := by
    intro i
    exact Finset.sum_comm
  simp_rw [h2]
  have h3 : (∑ i : Fin R, ∑ α ∈ Finset.range K, ∑ j : Fin R,
        (if |t i - t j| ≤ W then F α * Z α i j else 0))
      = ∑ α ∈ Finset.range K, ∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then F α * Z α i j else 0) := Finset.sum_comm
  rw [h3]
  refine Finset.sum_congr rfl fun α _ => ?_
  have h4 : ∀ i j : Fin R, (if |t i - t j| ≤ W then F α * Z α i j else 0)
      = F α * (if |t i - t j| ≤ W then Z α i j else 0) := by
    intro i j
    by_cases h : |t i - t j| ≤ W <;> simp [h]
  simp_rw [h4]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]


theorem smooth_range_localization_variable :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℕ), 1 ≤ A → A ≤ B →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) → ∀ (W : ℝ), 1 ≤ W →
    ∀ (a b : Fin R → Fin R → ℕ), (∀ i j, A ≤ a i j ∧ a i j ≤ b i j ∧ b i j ≤ B) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ W then
        ‖∑ n ∈ Finset.Icc (a i j) (b i j),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * (Real.log ((B : ℝ) + 2)) ^ 2 *
      (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          ‖∑ n ∈ Finset.Icc A B,
              (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)) := by
  obtain ⟨C₂, hC₂pos, hmaj⟩ := dirichlet_coefficient_majorant
  refine ⟨36 * C₂, by positivity, ?_⟩
  intro A B hA hAB R t hsep W hW a b hab
  have hB1 : 1 ≤ B := le_trans hA hAB
  set K : ℕ := B + 1 with hKdef
  have hKpos : 0 < K := by omega
  have hBK : B < K := by omega
  have hlog1 : (1:ℝ) ≤ Real.log ((B:ℝ) + 2) := by
    have h3 : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
      exact Real.exp_one_lt_three
    have hB2 : (3:ℝ) ≤ (B:ℝ) + 2 := by
      have : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB1
      linarith
    have := Real.log_le_log (by norm_num : (0:ℝ) < 3) hB2
    linarith
  -- the weight F
  set F : ℕ → ℝ := fun α => if α = 0 then (B:ℝ) else 1 / Real.sin (Real.pi * α / K) with hFdef
  have hFpos : ∀ α ∈ Finset.range K, 0 < F α := by
    intro α hα
    rw [Finset.mem_range] at hα
    simp only [hFdef]
    by_cases h : α = 0
    · rw [if_pos h]
      exact_mod_cast hB1
    · rw [if_neg h]
      refine div_pos one_pos (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
      · apply div_pos (mul_pos Real.pi_pos ?_) (by exact_mod_cast hKpos)
        exact_mod_cast (Nat.pos_of_ne_zero h)
      · rw [div_lt_iff₀ (by exact_mod_cast hKpos)]
        have hαK : (α:ℝ) < (K:ℝ) := by exact_mod_cast hα
        nlinarith [Real.pi_pos]
  have hFsum : ∑ α ∈ Finset.range K, F α ≤ (K:ℝ) * (3 * Real.log ((B:ℝ) + 2)) := by
    have hrange : (∑ α ∈ Finset.range K, F α) = F 0 + ∑ α ∈ Finset.Ico 1 K, F α := by
      have hconsec := Finset.sum_Ico_consecutive F (show 0 ≤ 1 by omega) (show 1 ≤ K by omega)
      rw [Finset.range_eq_Ico, ← hconsec]
      simp
    rw [hrange]
    have hF0 : F 0 = (B:ℝ) := by simp [hFdef]
    rw [hF0]
    have hico : ∑ α ∈ Finset.Ico 1 K, F α = ∑ α ∈ Finset.Ico 1 K, 1 / Real.sin (Real.pi * α / K) := by
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [Finset.mem_Ico] at hα
      simp only [hFdef]
      rw [if_neg (by omega)]
    rw [hico]
    have hsin := sum_inv_sin_le K hKpos
    rw [Icc_one_eq_Ico] at hsin
    have hhar : (harmonic (K-1) : ℝ) ≤ 1 + Real.log (K:ℝ) := by
      have h1 := harmonic_le_one_add_log (K-1)
      have h2 : ((K-1 : ℕ) : ℝ) ≤ (K:ℝ) := by
        have : K - 1 ≤ K := Nat.sub_le K 1
        exact_mod_cast this
      have h3 : (0:ℝ) < ((K-1:ℕ):ℝ) := by
        have : 0 < K - 1 := by omega
        exact_mod_cast this
      have h4 : Real.log (((K-1:ℕ)):ℝ) ≤ Real.log (K:ℝ) := Real.log_le_log h3 h2
      linarith [h1]
    have hle2 : (B:ℝ) + ∑ α ∈ Finset.Ico 1 K, 1 / Real.sin (Real.pi * α / K)
        ≤ (K:ℝ) * (2 + Real.log (K:ℝ)) := by
      have hBK' : (B:ℝ) ≤ (K:ℝ) := by
        have : B ≤ K := by omega
        exact_mod_cast this
      have h1 : ∑ α ∈ Finset.Ico 1 K, 1 / Real.sin (Real.pi * α / K)
          ≤ (K:ℝ) * (1 + Real.log (K:ℝ)) :=
        calc _ ≤ (K:ℝ) * (harmonic (K-1) : ℝ) := hsin
          _ ≤ (K:ℝ) * (1 + Real.log (K:ℝ)) :=
              mul_le_mul_of_nonneg_left hhar (by positivity)
      nlinarith [h1, hBK']
    have hlogK : Real.log (K:ℝ) ≤ Real.log ((B:ℝ)+2) := by
      apply Real.log_le_log
      · exact_mod_cast hKpos
      · have : (K:ℝ) ≤ (B:ℝ)+2 := by
          have : K ≤ B + 2 := by omega
          exact_mod_cast this
        linarith
    nlinarith [hle2, hlogK, hlog1]
  -- the two families of Fourier coefficients
  set P : ℕ → Fin R → Fin R → ℂ := fun α i j =>
      ∑ n ∈ Finset.Icc (a i j) (b i j), ((zeta K) ^ n) ^ α with hPdef
  set Q : ℕ → Fin R → Fin R → ℂ := fun α i j =>
      ∑ n ∈ Finset.Icc A B, (((zeta K) ^ n)⁻¹) ^ α *
        (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ) with hQdef
  -- ===== Step A: the Fourier identity =====
  have hA_id : ∀ i j : Fin R, ivSum (a i j) (b i j) (t i - t j) =
      (1 / (K:ℂ)) * ∑ α ∈ Finset.range K, P α i j * Q α i j := by
    intro i j
    obtain ⟨ha1, ha2, ha3⟩ := hab i j
    have hmem : Finset.Icc (a i j) (b i j) ⊆ Finset.Icc A B :=
      Finset.Icc_subset_Icc ha1 ha3
    have hSlt : ∀ n ∈ Finset.Icc A B, n < K := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      omega
    have h := fourier_expansion K hKpos
      (fun m => (m : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (m : ℝ) : ℂ))
      (a i j) (b i j) ha2 (by omega) (Finset.Icc A B) hmem hSlt
    simp only [hPdef, hQdef]
    simp_rw [mul_div_assoc]
    rw [h, ivSum]
    have hKne : (K:ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    field_simp
  -- ===== Step B: weighted Cauchy-Schwarz, per pair =====
  have hB_cs : ∀ i j : Fin R, ‖ivSum (a i j) (b i j) (t i - t j)‖ ^ 2 ≤
      ((1 / (K:ℝ)) * ∑ α ∈ Finset.range K, ‖P α i j‖ ^ 2 / F α) *
        ((1 / (K:ℝ)) * ∑ α ∈ Finset.range K, F α * ‖Q α i j‖ ^ 2) := by
    intro i j
    rw [hA_id i j]
    have hcs := cs_weighted (Finset.range K) F hFpos (fun α => P α i j) (fun α => Q α i j)
    have hKne : (K:ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hnorm : ‖(1 / (K:ℂ)) * ∑ α ∈ Finset.range K, P α i j * Q α i j‖
        = (1 / (K:ℝ)) * ‖∑ α ∈ Finset.range K, P α i j * Q α i j‖ := by
      rw [norm_mul, norm_div, norm_one, Complex.norm_natCast, one_div]
    rw [hnorm]
    have hKposR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
    have hsq : ((1 / (K:ℝ)) * ‖∑ α ∈ Finset.range K, P α i j * Q α i j‖) ^ 2
        = (1 / (K:ℝ)) ^ 2 * ‖∑ α ∈ Finset.range K, P α i j * Q α i j‖ ^ 2 := by ring
    rw [hsq]
    have hfinal : (1 / (K:ℝ)) ^ 2 * (∑ α ∈ Finset.range K, ‖P α i j‖ ^ 2 / F α)
          * (∑ α ∈ Finset.range K, F α * ‖Q α i j‖ ^ 2)
        = ((1 / (K:ℝ)) * ∑ α ∈ Finset.range K, ‖P α i j‖ ^ 2 / F α) *
          ((1 / (K:ℝ)) * ∑ α ∈ Finset.range K, F α * ‖Q α i j‖ ^ 2) := by ring
    nlinarith [hcs]
  -- ===== Step C: the P-factor is O(log) =====
  have hP_le : ∀ i j : Fin R, ∀ α ∈ Finset.range K, ‖P α i j‖ ≤ F α := by
    intro i j α hα
    rw [Finset.mem_range] at hα
    by_cases h : α = 0
    · subst h
      have hval : P 0 i j = ((Finset.Icc (a i j) (b i j)).card : ℂ) := by
        simp only [hPdef]
        simp
      rw [hval, Complex.norm_natCast]
      simp only [hFdef, if_pos rfl]
      exact_mod_cast (card_Icc_le B (a i j) (b i j) (le_trans hA (hab i j).1) (hab i j).2.2)
    · have hval : P α i j
          = ∑ n ∈ Finset.Icc (a i j) (b i j), ((zeta K) ^ α) ^ n := by
        simp only [hPdef]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← pow_mul, ← pow_mul, mul_comm]
      simp only [hval, hFdef] 
      rw [if_neg h]
      have h1 : 1 ≤ α := Nat.one_le_iff_ne_zero.mpr h
      exact norm_sum_Icc_zeta_pow_le K hKpos h1 hα (hab i j).2.1
  have hC_P : ∀ i j : Fin R, (1 / (K:ℝ)) * ∑ α ∈ Finset.range K, ‖P α i j‖ ^ 2 / F α
      ≤ 3 * Real.log ((B:ℝ) + 2) := by
    intro i j
    have hle : ∑ α ∈ Finset.range K, ‖P α i j‖ ^ 2 / F α ≤ ∑ α ∈ Finset.range K, F α := by
      refine Finset.sum_le_sum fun α hα => ?_
      have hFp : 0 < F α := hFpos α hα
      have hP := hP_le i j α hα
      rw [div_le_iff₀ hFp]
      nlinarith [hP, norm_nonneg (P α i j)]
    have hstep : (1 / (K:ℝ)) * ∑ α ∈ Finset.range K, ‖P α i j‖ ^ 2 / F α
        ≤ (1 / (K:ℝ)) * ((K:ℝ) * (3 * Real.log ((B:ℝ) + 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hle, hFsum]
    have hKposR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
    rw [show (1 / (K:ℝ)) * ((K:ℝ) * (3 * Real.log ((B:ℝ) + 2)))
        = 3 * Real.log ((B:ℝ) + 2) from by field_simp] at hstep
    exact hstep
  -- ===== Step D: fixed α, apply the large sieve majorant =====
  have hD : ∀ α ∈ Finset.range K,
      ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ W then ‖Q α i j‖ ^ 2 else 0)
        ≤ 4 * C₂ * (∑ i : Fin R, ∑ j : Fin R,
            (if |t i - t j| ≤ W then ‖ivSum A B (t i - t j)‖ ^ 2 else 0)) := by
    intro α hα
    have hS1 : ∀ n ∈ Finset.Icc A B, 1 ≤ n := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      omega
    have hm : (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then
            ‖∑ n ∈ Finset.Icc A B, (((zeta K) ^ n)⁻¹) ^ α *
              (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
           else 0))
        ≤ 4 * C₂ * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then
            ‖∑ n ∈ Finset.Icc A B, (1:ℂ) * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))
              / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
           else 0)) := by
      have h := hmaj (1/4) (by norm_num) (by norm_num) W (by linarith) (Finset.Icc A B) hS1
        (fun _ : ℕ => (1:ℝ)) (fun n : ℕ => (((zeta K) ^ n)⁻¹) ^ α)
        (fun n => by rw [norm_pow, norm_inv, norm_pow, norm_zeta]; norm_num) R t hsep
      have h4 : (4:ℝ) * (1/4) * W = W := by ring
      have hC2 : C₂ / (1/4) = 4 * C₂ := by ring
      simp only [h4, hC2] at h
      exact h
    have key1 : (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then ‖Q α i j‖ ^ 2 else 0))
        = (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then
            ‖∑ n ∈ Finset.Icc A B, (((zeta K) ^ n)⁻¹) ^ α *
              (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
           else 0)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases h : |t i - t j| ≤ W
      · simp only [if_pos h, hQdef]
      · simp only [if_neg h]
    have hRHS : 4 * C₂ * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then
            ‖∑ n ∈ Finset.Icc A B, (1:ℂ) * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))
              / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
           else 0))
        = 4 * C₂ * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then ‖ivSum A B (t i - t j)‖ ^ 2 else 0)) := by
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases h : |t i - t j| ≤ W
      · rw [if_pos h, if_pos h]
        simp only [ivSum, one_mul]
      · rw [if_neg h, if_neg h]
    rw [key1]
    rw [← hRHS]
    exact hm
  -- ===== Step E: assembly =====
  have hLnn : (0:ℝ) ≤ 3 * Real.log ((B:ℝ) + 2) := by linarith [hlog1]
  have hUnn : (0:ℝ) ≤ ∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ W then ‖ivSum A B (t i - t j)‖ ^ 2 else 0) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    by_cases h : |t i - t j| ≤ W
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  have hswap : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          (3 * Real.log ((B:ℝ)+2)) *
            ((1 / (K:ℝ)) * ∑ α ∈ Finset.range K, F α * ‖Q α i j‖ ^ 2) else 0))
      = (3 * Real.log ((B:ℝ)+2)) * (1 / (K:ℝ)) *
          (∑ α ∈ Finset.range K, F α *
            (∑ i : Fin R, ∑ j : Fin R,
              (if |t i - t j| ≤ W then ‖Q α i j‖ ^ 2 else 0))) := by
    have h1 : ∀ i j : Fin R, (3 * Real.log ((B:ℝ)+2)) *
            ((1 / (K:ℝ)) * ∑ α ∈ Finset.range K, F α * ‖Q α i j‖ ^ 2)
        = ∑ α ∈ Finset.range K,
            ((3 * Real.log ((B:ℝ)+2)) * (1 / (K:ℝ)) * F α) * ‖Q α i j‖ ^ 2 := by
      intro i j
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      ring
    simp_rw [h1]
    rw [swap_factor R t W K
      (fun α => (3 * Real.log ((B:ℝ)+2)) * (1 / (K:ℝ)) * F α)
      (fun α i j => ‖Q α i j‖ ^ 2)]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  have hDsum : (∑ α ∈ Finset.range K, F α *
        (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then ‖Q α i j‖ ^ 2 else 0)))
      ≤ (∑ α ∈ Finset.range K, F α) *
        (4 * C₂ * (∑ i : Fin R, ∑ j : Fin R,
            (if |t i - t j| ≤ W then ‖ivSum A B (t i - t j)‖ ^ 2 else 0))) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun α hα => ?_
    exact mul_le_mul_of_nonneg_left (hD α hα) (le_of_lt (hFpos α hα))
  have hKposR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
  calc (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ W then
        ‖∑ n ∈ Finset.Icc (a i j) (b i j),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
      = ∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then ‖ivSum (a i j) (b i j) (t i - t j)‖ ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        by_cases h : |t i - t j| ≤ W
        · rw [if_pos h, if_pos h, ivSum]
        · rw [if_neg h, if_neg h]
    _ ≤ ∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then
            (3 * Real.log ((B:ℝ)+2)) *
              ((1 / (K:ℝ)) * ∑ α ∈ Finset.range K, F α * ‖Q α i j‖ ^ 2) else 0) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        by_cases h : |t i - t j| ≤ W
        · rw [if_pos h, if_pos h]
          have h1 := hB_cs i j
          have h2 := hC_P i j
          have h3 : (0:ℝ) ≤ (1 / (K:ℝ)) * ∑ α ∈ Finset.range K, F α * ‖Q α i j‖ ^ 2 := by
            apply mul_nonneg (by positivity)
            exact Finset.sum_nonneg fun α hα => mul_nonneg (le_of_lt (hFpos α hα)) (sq_nonneg _)
          nlinarith [h1, h2, h3]
        · rw [if_neg h, if_neg h]
    _ = (3 * Real.log ((B:ℝ)+2)) * (1 / (K:ℝ)) *
          (∑ α ∈ Finset.range K, F α *
            (∑ i : Fin R, ∑ j : Fin R,
              (if |t i - t j| ≤ W then ‖Q α i j‖ ^ 2 else 0))) := hswap
    _ ≤ (3 * Real.log ((B:ℝ)+2)) * (1 / (K:ℝ)) *
          ((∑ α ∈ Finset.range K, F α) *
            (4 * C₂ * (∑ i : Fin R, ∑ j : Fin R,
              (if |t i - t j| ≤ W then ‖ivSum A B (t i - t j)‖ ^ 2 else 0)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hDsum
    _ ≤ (3 * Real.log ((B:ℝ)+2)) * (1 / (K:ℝ)) *
          (((K:ℝ) * (3 * Real.log ((B:ℝ)+2))) *
            (4 * C₂ * (∑ i : Fin R, ∑ j : Fin R,
              (if |t i - t j| ≤ W then ‖ivSum A B (t i - t j)‖ ^ 2 else 0)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right hFsum
        positivity
    _ = 36 * C₂ * (Real.log ((B:ℝ)+2)) ^ 2 *
          (∑ i : Fin R, ∑ j : Fin R,
            (if |t i - t j| ≤ W then ‖ivSum A B (t i - t j)‖ ^ 2 else 0)) := by
        field_simp
        ring


end

end Commons.NumberTheory.DirichletPolynomial
