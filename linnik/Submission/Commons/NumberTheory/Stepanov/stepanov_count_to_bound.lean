import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Cast.Order.Field

namespace Commons.NumberTheory.Stepanov

set_option maxHeartbeats 2000000

theorem stepanov_count_to_bound (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d) (D : ℕ) (hD : D ≤ d)
    (q T : ℕ) (hq : (4 * e * (d + 1) + 2 * e ^ 3 * (d + 1) + 4) ^ 2 ≤ q)
    (hT : T * Nat.sqrt q ≤ Nat.sqrt q * Nat.sqrt q / (2 * e) + 1 + q * (Nat.sqrt q / e + d + 3)
        + (e - 1) * (((q - 1) / e) * D)) :
    (T : ℝ) ≤ (q : ℝ) / (e : ℝ)
      + (1 / (2 * (e : ℝ)) + (1 + 4 * ((d : ℝ) + 4) + 4 * ((e : ℝ) - 1) * (d : ℝ) / (e : ℝ)) + 1)
        * Real.sqrt (q : ℝ) := by
  set s := Nat.sqrt q with hs
  have hs2 : s * s ≤ q := by rw [hs]; exact Nat.sqrt_le q
  have hM : 4 * e * (d + 1) + 2 * e ^ 3 * (d + 1) + 4 ≤ s := by
    rw [hs]
    exact Nat.le_sqrt.2 (by simpa [pow_two] using hq)
  have hqle : q ≤ s * s + 2 * s := by
    have h := Nat.lt_succ_sqrt q
    rw [← hs] at h
    nlinarith
  have hs1 : 1 ≤ s := by
    have : 1 ≤ 4 * e * (d + 1) := by
      have h2 : 2 ≤ 4 * (d + 1) := by omega
      calc 1 ≤ 2 := by norm_num
        _ ≤ 2 * e := by omega
        _ = e * 2 := by ring
        _ ≤ e * (4 * (d + 1)) := Nat.mul_le_mul_left e h2
        _ = 4 * e * (d + 1) := by ring
    omega
  have heR : (2:ℝ) ≤ (e:ℝ) := by exact_mod_cast he
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hDd : (D:ℝ) ≤ (d:ℝ) := by exact_mod_cast hD
  have hs1R : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs1
  have hs0R : (0:ℝ) < (s:ℝ) := by linarith
  have hs2R : (s:ℝ)*(s:ℝ) ≤ (q:ℝ) := by exact_mod_cast hs2
  have hqleR : (q:ℝ) ≤ (s:ℝ)*(s:ℝ) + 2*(s:ℝ) := by exact_mod_cast hqle
  have hsqrts : (s:ℝ) ≤ Real.sqrt (q:ℝ) := by
    rw [Real.le_sqrt (by linarith) (by positivity)]
    simpa [pow_two] using hs2R
  have hSs : (s:ℝ)*(s:ℝ) ≤ Real.sqrt (q:ℝ) * (s:ℝ) :=
    mul_le_mul_of_nonneg_right hsqrts (le_of_lt hs0R)
  set B : ℕ := s * s / (2 * e) + 1 + q * (s / e + d + 3) + (e - 1) * (((q - 1) / e) * D) with hBdef
  have hT_nat : T * s ≤ B := by rw [hBdef, hs]; exact hT
  have hT' : (T:ℝ)*(s:ℝ) ≤ (B:ℝ) := by exact_mod_cast hT_nat
  have hcast : (B:ℝ) = ((s * s / (2 * e) : ℕ) : ℝ) + 1 + (q:ℝ) * (((s / e : ℕ) : ℝ) + (d:ℝ) + 3)
      + ((e - 1 : ℕ) : ℝ) * ((((q - 1) / e : ℕ) : ℝ) * (D:ℝ)) := by
    rw [hBdef]; push_cast; ring
  have h1 : ((s * s / (2 * e) : ℕ) : ℝ) ≤ (q:ℝ)/(2*(e:ℝ)) := by
    calc ((s * s / (2 * e) : ℕ) : ℝ) ≤ ((s * s : ℕ) : ℝ) / ((2 * e : ℕ) : ℝ) := Nat.cast_div_le
      _ = (s:ℝ)*(s:ℝ)/(2*(e:ℝ)) := by push_cast; ring
      _ ≤ (q:ℝ)/(2*(e:ℝ)) := by
          have h2e : (0:ℝ) < 2*(e:ℝ) := by linarith [heR]
          gcongr
  have hse : ((s / e : ℕ) : ℝ) ≤ (s:ℝ)/(e:ℝ) := Nat.cast_div_le
  have h2 : (q:ℝ) * (((s / e : ℕ) : ℝ) + (d:ℝ) + 3) ≤ (q:ℝ) * ((s:ℝ)/(e:ℝ) + (d:ℝ) + 3) := by
    have hqnn : (0:ℝ) ≤ (q:ℝ) := by positivity
    nlinarith [hse]
  have hqe : ((((q - 1) / e : ℕ)) : ℝ) ≤ (q:ℝ)/(e:ℝ) := by
    calc (((q-1)/e : ℕ) : ℝ) ≤ ((q-1 : ℕ) : ℝ)/((e:ℝ)) := Nat.cast_div_le
      _ ≤ (q:ℝ)/(e:ℝ) := by
          have hq1 : ((q-1:ℕ):ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.sub_le q 1
          have hep : (0:ℝ) < (e:ℝ) := by linarith [heR]
          gcongr
  have h3 : ((e - 1 : ℕ) : ℝ) * ((((q - 1) / e : ℕ) : ℝ) * (D:ℝ))
      ≤ ((e:ℝ)-1)*((d:ℝ)/(e:ℝ))*(q:ℝ) := by
    have he1 : ((e-1:ℕ):ℝ) = (e:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ e)]; norm_num
    rw [he1]
    have hqnn : (0:ℝ) ≤ (q:ℝ)/(e:ℝ) := by positivity
    have hDnn : (0:ℝ) ≤ (D:ℝ) := by positivity
    have hstep : ((((q-1)/e : ℕ) : ℝ) * (D:ℝ)) ≤ ((q:ℝ)/(e:ℝ)) * (d:ℝ) :=
      mul_le_mul hqe hDd hDnn hqnn
    have he1nn : (0:ℝ) ≤ (e:ℝ)-1 := by linarith [heR]
    calc ((e:ℝ)-1) * ((((q-1)/e : ℕ) : ℝ) * (D:ℝ))
        ≤ ((e:ℝ)-1) * (((q:ℝ)/(e:ℝ)) * (d:ℝ)) := mul_le_mul_of_nonneg_left hstep he1nn
      _ = ((e:ℝ)-1) * ((d:ℝ)/(e:ℝ)) * (q:ℝ) := by ring
  have hBu : (B:ℝ) ≤ (q:ℝ)/(2*(e:ℝ)) + 1 + (q:ℝ)*((s:ℝ)/(e:ℝ) + (d:ℝ) + 3)
      + ((e:ℝ)-1)*((d:ℝ)/(e:ℝ))*(q:ℝ) := by
    rw [hcast]
    linarith [h1, h2, h3]
  have hpoly : (s:ℝ) * (4*(e:ℝ)*(d:ℝ) + 6*(e:ℝ)) + (e:ℝ)
      ≤ (15*(e:ℝ) + 6*(e:ℝ)*(d:ℝ) - 3*(d:ℝ)) * (s:ℝ)^2 := by
    have hc : (e:ℝ) ≤ 2*(e:ℝ)*(d:ℝ)+9*(e:ℝ)-3*(d:ℝ) := by nlinarith [heR, hdR]
    have hcoef2 : (0:ℝ) ≤ 2*(e:ℝ)*(d:ℝ)+9*(e:ℝ)-3*(d:ℝ) := by linarith [hc, heR]
    have hscoef : 2*(e:ℝ)*(d:ℝ)+9*(e:ℝ)-3*(d:ℝ)
        ≤ (s:ℝ)*(2*(e:ℝ)*(d:ℝ)+9*(e:ℝ)-3*(d:ℝ)) := le_mul_of_one_le_left hcoef2 hs1R
    have hmid : (e:ℝ) ≤ (s:ℝ)*(2*(e:ℝ)*(d:ℝ)+9*(e:ℝ)-3*(d:ℝ)) := le_trans hc hscoef
    have hcoef_nonneg : (0:ℝ) ≤ 15*(e:ℝ) + 6*(e:ℝ)*(d:ℝ) - 3*(d:ℝ) := by nlinarith [heR, hdR]
    have hsq_ge : (s:ℝ) ≤ (s:ℝ)^2 := by nlinarith [hs1R]
    have h1' : (s:ℝ)*(4*(e:ℝ)*(d:ℝ)+6*(e:ℝ)) + (e:ℝ)
        ≤ (s:ℝ)*(4*(e:ℝ)*(d:ℝ)+6*(e:ℝ)) + (s:ℝ)*(2*(e:ℝ)*(d:ℝ)+9*(e:ℝ)-3*(d:ℝ)) := by linarith [hmid]
    have h2' : (s:ℝ)*(4*(e:ℝ)*(d:ℝ)+6*(e:ℝ)) + (s:ℝ)*(2*(e:ℝ)*(d:ℝ)+9*(e:ℝ)-3*(d:ℝ))
        = (s:ℝ)*(15*(e:ℝ)+6*(e:ℝ)*(d:ℝ)-3*(d:ℝ)) := by ring
    have h3' : (s:ℝ)*(15*(e:ℝ)+6*(e:ℝ)*(d:ℝ)-3*(d:ℝ))
        ≤ (15*(e:ℝ)+6*(e:ℝ)*(d:ℝ)-3*(d:ℝ))*(s:ℝ)^2 := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hsq_ge hcoef_nonneg
    linarith [h1', h2', h3']
  have hcore : (q:ℝ)/(2*(e:ℝ)) + 1 + (q:ℝ)*((d:ℝ)+3) + ((e:ℝ)-1)*((d:ℝ)/(e:ℝ))*(q:ℝ)
      ≤ (1/(2*(e:ℝ)) + (1 + 4*((d:ℝ)+4) + 4*((e:ℝ)-1)*(d:ℝ)/(e:ℝ)) + 1) * Real.sqrt (q:ℝ) * (s:ℝ) := by
    have heR_pos : (0:ℝ) < (e:ℝ) := by linarith [heR]
    refine le_of_mul_le_mul_left ?_ heR_pos
    have h1e : (e:ℝ)*((q:ℝ)/(2*(e:ℝ)) + 1 + (q:ℝ)*((d:ℝ)+3) + ((e:ℝ)-1)*((d:ℝ)/(e:ℝ))*(q:ℝ))
        = (q:ℝ)*(1/2 + 2*(e:ℝ)*(d:ℝ) + 3*(e:ℝ) - (d:ℝ)) + (e:ℝ) := by
      field_simp; ring
    have h2e : (e:ℝ)*((1/(2*(e:ℝ)) + (1 + 4*((d:ℝ)+4) + 4*((e:ℝ)-1)*(d:ℝ)/(e:ℝ)) + 1) * Real.sqrt (q:ℝ) * (s:ℝ))
        = (1/2 + 18*(e:ℝ) + 8*(e:ℝ)*(d:ℝ) - 4*(d:ℝ)) * Real.sqrt (q:ℝ) * (s:ℝ) := by
      field_simp; ring
    rw [h1e, h2e]
    have hKnn : (0:ℝ) ≤ 1/2 + 2*(e:ℝ)*(d:ℝ) + 3*(e:ℝ) - (d:ℝ) := by nlinarith [heR, hdR]
    have hqK := mul_le_mul_of_nonneg_right hqleR hKnn
    have hrest : ((s:ℝ)^2 + 2*(s:ℝ))*(1/2+2*(e:ℝ)*(d:ℝ)+3*(e:ℝ)-(d:ℝ)) + (e:ℝ)
        ≤ (1/2+18*(e:ℝ)+8*(e:ℝ)*(d:ℝ)-4*(d:ℝ))*(s:ℝ)^2 := by
      have hsle : (s:ℝ)*(1+4*(e:ℝ)*(d:ℝ)+6*(e:ℝ)-2*(d:ℝ)) ≤ (s:ℝ)*(4*(e:ℝ)*(d:ℝ)+6*(e:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hs0R)
        nlinarith [hdR]
      nlinarith [hpoly, hsle]
    have hLnn : (0:ℝ) ≤ 1/2+18*(e:ℝ)+8*(e:ℝ)*(d:ℝ)-4*(d:ℝ) := by nlinarith [heR, hdR]
    have hfs : (1/2+18*(e:ℝ)+8*(e:ℝ)*(d:ℝ)-4*(d:ℝ))*(s:ℝ)^2
        ≤ (1/2+18*(e:ℝ)+8*(e:ℝ)*(d:ℝ)-4*(d:ℝ))*(Real.sqrt (q:ℝ)*(s:ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa [pow_two] using hSs) hLnn
    linarith [hqK, hrest, hfs]
  have key : (B:ℝ) ≤ ((q:ℝ)/(e:ℝ)
      + (1/(2*(e:ℝ)) + (1 + 4*((d:ℝ)+4) + 4*((e:ℝ)-1)*(d:ℝ)/(e:ℝ)) + 1) * Real.sqrt (q:ℝ)) * (s:ℝ) := by
    have hqse : (q:ℝ)*((s:ℝ)/(e:ℝ)) = (q:ℝ)/(e:ℝ)*(s:ℝ) := by ring
    have hexp : (q:ℝ)*((s:ℝ)/(e:ℝ) + (d:ℝ) + 3) = (q:ℝ)*((s:ℝ)/(e:ℝ)) + (q:ℝ)*((d:ℝ)+3) := by ring
    have hgoal : (q:ℝ)/(e:ℝ)*(s:ℝ)
        + (1/(2*(e:ℝ)) + (1 + 4*((d:ℝ)+4) + 4*((e:ℝ)-1)*(d:ℝ)/(e:ℝ)) + 1) * Real.sqrt (q:ℝ) * (s:ℝ)
        = ((q:ℝ)/(e:ℝ) + (1/(2*(e:ℝ)) + (1 + 4*((d:ℝ)+4) + 4*((e:ℝ)-1)*(d:ℝ)/(e:ℝ)) + 1) * Real.sqrt (q:ℝ)) * (s:ℝ) := by ring
    linarith [hBu, hcore, hqse, hexp, hgoal]
  have hfinal : (T:ℝ)*(s:ℝ) ≤ ((q:ℝ)/(e:ℝ)
      + (1/(2*(e:ℝ)) + (1 + 4*((d:ℝ)+4) + 4*((e:ℝ)-1)*(d:ℝ)/(e:ℝ)) + 1) * Real.sqrt (q:ℝ)) * (s:ℝ) :=
    le_trans hT' key
  exact (mul_le_mul_iff_left₀ hs0R).mp hfinal

end Commons.NumberTheory.Stepanov