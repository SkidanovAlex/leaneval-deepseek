import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Analysis.SumIntegral

open scoped BigOperators
open Finset

/-- Algebraic inequality: for `0 ≤ u ≤ v` and `j : ℕ`,
`((j:ℝ)+1) * u^j * (v-u) ≤ v^(j+1) - u^(j+1)`. -/
private lemma mul_pow_mul_sub_le_pow_sub (j : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ((j : ℝ) + 1) * u ^ j * (v - u) ≤ v ^ (j + 1) - u ^ (j + 1) := by
  have hvu : 0 ≤ v - u := sub_nonneg.mpr huv
  have hgeom : (∑ i ∈ Finset.range (j + 1), v ^ i * u ^ (j + 1 - 1 - i)) * (v - u)
      = v ^ (j + 1) - u ^ (j + 1) := geom_sum₂_mul v u (j + 1)
  rw [← hgeom]
  have hconst : ((j : ℝ) + 1) * u ^ j = ∑ _i ∈ Finset.range (j + 1), u ^ j := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [hconst]
  apply mul_le_mul_of_nonneg_right _ hvu
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_range] at hi
  have hji : j + 1 - 1 - i = j - i := by omega
  rw [hji]
  have hup : u ^ j = u ^ i * u ^ (j - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hup]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu huv i) (pow_nonneg hu (j - i))

/-- `1/(x+1) ≤ log((x+1)/x)` for `1 ≤ x`. -/
private lemma inv_add_one_le_log_ratio (x : ℝ) (hx : 1 ≤ x) :
    1 / (x + 1) ≤ Real.log ((x + 1) / x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le one_pos hx
  have hx1_pos : 0 < x + 1 := by linarith
  have hlog : Real.log (x / (x + 1)) ≤ x / (x + 1) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hx_pos hx1_pos)
  have hval : x / (x + 1) - 1 = -(1 / (x + 1)) := by
    field_simp
    ring
  have hlog' : Real.log (x / (x + 1)) ≤ -(1 / (x + 1)) := by
    rw [hval] at hlog; exact hlog
  have h2 : Real.log ((x + 1) / x) = -Real.log (x / (x + 1)) := by
    have h2' : (x + 1) / x = (x / (x + 1))⁻¹ := (inv_div x (x + 1)).symm
    simp only [h2', Real.log_inv]
  rw [h2]
  linarith

/-- Pointwise telescoping step. -/
private lemma local_step (j n a : ℕ) (ha : 1 ≤ a) (han : a < n) :
    (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ j / (((a + 1 : ℕ) : ℝ)) ≤
      (Real.log ((n : ℝ) / (a : ℝ))) ^ (j + 1) / ((j : ℝ) + 1) -
        (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ (j + 1) / ((j : ℝ) + 1) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have ha_pos : (0 : ℝ) < (a : ℝ) := by
    have : (0 : ℕ) < a := by omega
    exact_mod_cast this
  have ha1_pos : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by
    have : (0 : ℕ) < a + 1 := by omega
    exact_mod_cast this
  have ha1_le_n : a + 1 ≤ n := by omega
  have hcast : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hu_nonneg : 0 ≤ Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    rw [one_le_div ha1_pos]
    exact_mod_cast ha1_le_n
  have huv : Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ)) ≤ Real.log ((n : ℝ) / (a : ℝ)) := by
    apply Real.log_le_log (div_pos hn_pos ha1_pos)
    exact div_le_div_of_nonneg_left hn_pos.le ha_pos (by exact_mod_cast (Nat.le_succ a) : (a : ℝ) ≤ ((a + 1 : ℕ) : ℝ))
  have hvu_eq : Real.log ((n : ℝ) / (a : ℝ)) - Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))
      = Real.log (((a + 1 : ℕ) : ℝ) / (a : ℝ)) := by
    rw [Real.log_div hn_pos.ne' ha_pos.ne', Real.log_div hn_pos.ne' ha1_pos.ne']
    rw [Real.log_div ha1_pos.ne' ha_pos.ne']
    ring
  have hratio : 1 / (((a + 1 : ℕ) : ℝ)) ≤
      Real.log ((n : ℝ) / (a : ℝ)) - Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ)) := by
    rw [hvu_eq, hcast]
    exact inv_add_one_le_log_ratio (a : ℝ) (by exact_mod_cast ha)
  have hmain1 : (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ j *
      (Real.log ((n : ℝ) / (a : ℝ)) - Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ≤
      ((Real.log ((n : ℝ) / (a : ℝ))) ^ (j + 1) -
        (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ (j + 1)) / ((j : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
    rw [show (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ j *
          (Real.log ((n : ℝ) / (a : ℝ)) - Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) *
          ((j : ℝ) + 1)
        = ((j : ℝ) + 1) * (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ j *
          (Real.log ((n : ℝ) / (a : ℝ)) - Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) by ring]
    exact mul_pow_mul_sub_le_pow_sub j hu_nonneg huv
  have hmain2 : (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ j / (((a + 1 : ℕ) : ℝ)) ≤
      (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ j *
        (Real.log ((n : ℝ) / (a : ℝ)) - Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) := by
    have hc : ((((a + 1 : ℕ) : ℝ))⁻¹) ≤
        Real.log ((n : ℝ) / (a : ℝ)) - Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ)) := by
      rw [← one_div]; exact hratio
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hc (pow_nonneg hu_nonneg j)
  calc (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ j / (((a + 1 : ℕ) : ℝ))
      ≤ (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ j *
          (Real.log ((n : ℝ) / (a : ℝ)) - Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) := hmain2
    _ ≤ ((Real.log ((n : ℝ) / (a : ℝ))) ^ (j + 1) -
          (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ (j + 1)) / ((j : ℝ) + 1) := hmain1
    _ = (Real.log ((n : ℝ) / (a : ℝ))) ^ (j + 1) / ((j : ℝ) + 1) -
          (Real.log ((n : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ (j + 1) / ((j : ℝ) + 1) := by ring

theorem monomial_log_sum_le (j n : ℕ) (hn : 1 ≤ n) :
    (∑ a ∈ Finset.Icc 1 n, (Real.log ((n : ℝ) / (a : ℝ))) ^ j / (a : ℝ)) ≤
      (Real.log (n : ℝ)) ^ j + (Real.log (n : ℝ)) ^ (j + 1) / ((j : ℝ) + 1) := by
  let f : ℕ → ℝ := fun m => (Real.log ((n : ℝ) / (m : ℝ))) ^ j / (m : ℝ)
  let phi : ℕ → ℝ := fun m => (Real.log ((n : ℝ) / (m : ℝ))) ^ (j + 1) / ((j : ℝ) + 1)
  have hIcc : (∑ a ∈ Finset.Icc 1 n, f a) = f 1 + ∑ a ∈ Finset.Ico 1 n, f (a + 1) := by
    have h1 : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have h2 : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ico 2 (n + 1)) := by
      ext a; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have h3 : (1 : ℕ) ∉ Finset.Ico 2 (n + 1) := by simp only [Finset.mem_Ico]; omega
    rw [h1, h2, Finset.sum_insert h3, Finset.sum_Ico_add' f 1 n 1]
  have htel : (∑ a ∈ Finset.Ico 1 n, (phi a - phi (a + 1))) = phi 1 - phi n := by
    rw [Finset.sum_Ico_eq_sub (f := fun a => phi a - phi (a + 1)) hn]
    rw [Finset.sum_range_sub' phi n, Finset.sum_range_sub' phi 1]
    ring
  have hlocal : ∀ a ∈ Finset.Ico 1 n, f (a + 1) ≤ phi a - phi (a + 1) := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    exact local_step j n a ha.1 ha.2
  have hf1 : f 1 = (Real.log (n : ℝ)) ^ j := by simp [f]
  have hp1 : phi 1 = (Real.log (n : ℝ)) ^ (j + 1) / ((j : ℝ) + 1) := by simp [phi]
  have hpn : phi n = 0 := by
    have hn_ne : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      linarith
    simp only [phi]
    rw [div_self hn_ne, Real.log_one, zero_pow (by omega : j + 1 ≠ 0), zero_div]
  calc (∑ a ∈ Finset.Icc 1 n, f a)
      = f 1 + ∑ a ∈ Finset.Ico 1 n, f (a + 1) := hIcc
    _ ≤ f 1 + ∑ a ∈ Finset.Ico 1 n, (phi a - phi (a + 1)) := by
        apply add_le_add_right
        exact Finset.sum_le_sum hlocal
    _ = f 1 + (phi 1 - phi n) := by rw [htel]
    _ = (Real.log (n : ℝ)) ^ j + (Real.log (n : ℝ)) ^ (j + 1) / ((j : ℝ) + 1) := by
        rw [hf1, hp1, hpn]; ring

end Commons.Analysis.SumIntegral