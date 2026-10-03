import Mathlib
import Submission.Work.KMTAreas.A4Z.SivLocal

namespace Work.KMTAreas.A4Z

theorem sqrt_kappa_le (K C : ℝ) (hK : 0 < K) (hC : 0 < C) (d : ℕ) (hd : 2 ≤ d)
    (D : ℤ) (hD : 0 ≤ D) (c₀ c : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀) (hcc : c ≤ c₀) (hc1 : c ≤ 1) :
    ∃ C'' : ℝ, 0 < C'' ∧ ∀ l : ℕ,
      Real.sqrt ((C * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2 * (2 * (D : ℝ) + 1)
          + ((C * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2
              + K * (max ((l : ℝ)) 1) ^ 2 * (2 : ℝ) ^ (-(16 * (d : ℝ) * (l : ℝ))))
            * Work.KMTAreas.A4Z.kern8Mass)
        ≤ C'' * (2 : ℝ) ^ (-(c * (l : ℝ))) := by
  have hM0 : 0 ≤ kern8Mass := tsum_nonneg fun m => Real.rpow_nonneg (by positivity) _
  have hD0 : (0:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  set X : ℝ := C^2 * ((2*(D:ℝ) + 1) + kern8Mass) + K * kern8Mass with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]
    have hC2 : 0 < C^2 := pow_pos hC 2
    have hbr : 0 < (2*(D:ℝ)+1) + kern8Mass := by
      have h1 : (0:ℝ) < 2*(D:ℝ)+1 := by linarith
      linarith
    have hp : 0 < C^2 * ((2*(D:ℝ)+1) + kern8Mass) := mul_pos hC2 hbr
    have hKM : 0 ≤ K * kern8Mass := mul_nonneg hK.le hM0
    linarith
  refine ⟨Real.sqrt X, Real.sqrt_pos.mpr hXpos, ?_⟩
  intro l
  set u : ℝ := (2:ℝ) ^ (-(c*(l:ℝ))) with hu
  set v : ℝ := (2:ℝ) ^ (-(c₀*(l:ℝ))) with hv
  set w : ℝ := (2:ℝ) ^ (-(8*(d:ℝ)*(l:ℝ))) with hw
  set z : ℝ := (2:ℝ) ^ (-(16*(d:ℝ)*(l:ℝ))) with hz
  have hu0 : 0 ≤ u := Real.rpow_nonneg (by norm_num) _
  have hv0 : 0 < v := Real.rpow_pos_of_pos (by norm_num) _
  have hw0 : 0 < w := Real.rpow_pos_of_pos (by norm_num) _
  have hmaxNat : max l 1 ≤ 2^l := by
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp
    · exact max_le (le_of_lt Nat.lt_two_pow_self) Nat.one_le_two_pow
  have hmaxR : max (l:ℝ) 1 ≤ (2:ℝ)^(l:ℝ) := by
    calc max (l:ℝ) 1 = ((max l 1 : ℕ) : ℝ) := by rw [Nat.cast_max, Nat.cast_one]
      _ ≤ ((2^l : ℕ) : ℝ) := by exact_mod_cast hmaxNat
      _ = (2:ℝ)^(l:ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  have hvu : v ≤ u := by
    rw [hv, hu]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h1 : c * (l:ℝ) ≤ c₀ * (l:ℝ) := mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg l)
    linarith
  have h8d : c ≤ 8*(d:ℝ) - 1 := by
    have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    linarith
  have hexp : (l:ℝ) + -(8*(d:ℝ)*(l:ℝ)) ≤ -(c*(l:ℝ)) := by
    have h1 : c * (l:ℝ) ≤ (8*(d:ℝ) - 1) * (l:ℝ) :=
      mul_le_mul_of_nonneg_right h8d (Nat.cast_nonneg l)
    nlinarith
  have hmaxw : max (l:ℝ) 1 * w ≤ u := by
    calc max (l:ℝ) 1 * w ≤ (2:ℝ)^(l:ℝ) * w :=
          mul_le_mul_of_nonneg_right hmaxR (le_of_lt hw0)
      _ = (2:ℝ)^((l:ℝ) + -(8*(d:ℝ)*(l:ℝ))) := by
          rw [hw]
          exact (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
      _ ≤ u := by
          rw [hu]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hz_eq : z = w * w := by
    rw [hz, hw, ← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
    congr 1
    ring
  have hmax2z : (max (l:ℝ) 1)^2 * z ≤ u^2 := by
    have hmw0 : 0 ≤ max (l:ℝ) 1 * w :=
      mul_nonneg (le_trans (Nat.cast_nonneg l) (le_max_left _ _)) (le_of_lt hw0)
    calc (max (l:ℝ) 1)^2 * z = (max (l:ℝ) 1 * w)^2 := by rw [hz_eq]; ring
      _ ≤ u^2 := pow_le_pow_left₀ hmw0 hmaxw 2
  have hbr : 0 ≤ (2*(D:ℝ)+1) + kern8Mass := by
    have h1 : (0:ℝ) ≤ 2*(D:ℝ)+1 := by linarith
    linarith
  have hC2 : 0 ≤ C^2 := sq_nonneg C
  have h1 : (C*v)^2 * ((2*(D:ℝ)+1) + kern8Mass)
      ≤ C^2*((2*(D:ℝ)+1)+kern8Mass)*u^2 := by
    have hv2 : v^2 ≤ u^2 := pow_le_pow_left₀ (le_of_lt hv0) hvu 2
    calc (C*v)^2 * ((2*(D:ℝ)+1) + kern8Mass)
        = C^2 * v^2 * ((2*(D:ℝ)+1)+kern8Mass) := by rw [mul_pow]
      _ ≤ C^2 * u^2 * ((2*(D:ℝ)+1)+kern8Mass) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv2 hC2) hbr
      _ = C^2 * ((2*(D:ℝ)+1)+kern8Mass) * u^2 := by ring
  have h2 : K * (max (l:ℝ) 1)^2 * z * kern8Mass ≤ K * kern8Mass * u^2 := by
    have hKM : 0 ≤ K * kern8Mass := mul_nonneg hK.le hM0
    calc K * (max (l:ℝ) 1)^2 * z * kern8Mass
        = (K * kern8Mass) * ((max (l:ℝ) 1)^2 * z) := by ring
      _ ≤ (K * kern8Mass) * u^2 := mul_le_mul_of_nonneg_left hmax2z hKM
      _ = K * kern8Mass * u^2 := by ring
  have hinner : (C*v)^2 * (2*(D:ℝ)+1) + ((C*v)^2 + K * (max (l:ℝ) 1)^2 * z) * kern8Mass
      ≤ X * u^2 := by
    have hexp1 : (C*v)^2 * (2*(D:ℝ)+1) + ((C*v)^2 + K*(max (l:ℝ) 1)^2*z) * kern8Mass
        = (C*v)^2 * ((2*(D:ℝ)+1) + kern8Mass)
          + K*(max (l:ℝ) 1)^2*z*kern8Mass := by ring
    have hexp2 : X * u^2
        = C^2*((2*(D:ℝ)+1)+kern8Mass)*u^2 + K*kern8Mass*u^2 := by
      rw [hXdef]; ring
    rw [hexp1, hexp2]
    exact add_le_add h1 h2
  have hs : Real.sqrt ((C*v)^2 * (2*(D:ℝ)+1) + ((C*v)^2 + K * (max (l:ℝ) 1)^2 * z) * kern8Mass)
      ≤ Real.sqrt X * u := by
    have h := Real.sqrt_le_sqrt hinner
    rwa [Real.sqrt_mul hXpos.le, Real.sqrt_sq hu0] at h
  exact hs

end Work.KMTAreas.A4Z
