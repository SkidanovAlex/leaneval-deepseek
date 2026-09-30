import Mathlib
import Submission.Work.BW.num_T
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.num_kum
import Submission.Work.BW.est16_half_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- From `e^x · 2 ≤ e^y` deduce `x < y` (used to strip the exponentials in the BW (14)/(15)
comparison). -/
private lemma lt_of_exp_mul_two_le_exp {x y : ℝ} (h : Real.exp x * 2 ≤ Real.exp y) : x < y := by
  have hp : 0 < Real.exp x := Real.exp_pos x
  have hlt : Real.exp x < Real.exp y := by linarith
  exact (Real.exp_lt_exp).1 hlt

/-- BW (14) vs (15), the quantitative side of the `g ≠ 0 ⟹ f ≠ 0` bridge: the `(15)`-exponent
`A = ln(p) − (logHeight p + (1−1/d)(dhT* + 0.204SD) + 1.007(|s|/2^J)D + kum_J)` strictly exceeds the
`(14)`-exponent `B = ln(p) + hT* + (0.205/d + 1.01(|s|/2^J)/S − 9·2^r)SD`, for `T* ≤ T`,
`J ≤ I = ⌊50log(2rd)⌋` and `|s|/2^J ≤ 4S`. Indeed
`A − B = (9·2^r − 0.204 − 0.001/d)SD − logHeight p − dhT* − kum_J − (1.007 + 1.01/S)(|s|/2^J)D` and
one bounds `logHeight p ≤ 0.85SD` (12), `dhT* ≤ 0.735SD` (with `T* ≤ T = acT`), `kum_J ≤ 2.2SD`
(from `J ≤ I`), and `(1.007 + 1.01/S)(|s|/2^J)D ≤ 1.007·4S·D + 1.01·(|s|/2^J)D ≤ 4.028SD + 4.04SD`,
giving `A − B ≥ (9·2^r − 12.06)SD ≥ 23.9 SD > 0`. -/
theorem est1415_gap {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (hJ : J ≤ pI r (dK K)) (Tst : ℝ)
    (hTst : Tst ≤ acT K σ) (s : ℤ)
    (hs : ((|s| : ℤ) : ℝ) / 2 ^ J ≤ 4 * acS K r b v) :
    lnp φ p + (acH K b v : ℝ) * Tst +
        (0.205 * (1 / (dK K : ℝ)) + 1.01 * (((|s| : ℤ) : ℝ) / 2 ^ J) / acS K r b v - 9 * 2 ^ r) *
          acS K r b v * acD K σ
      < lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) *
          ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
          1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J) := by
  refine lt_of_exp_mul_two_le_exp ?_
  -- non-degeneracy of the parameters
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := by
    have hpos : 0 < dK K := Module.finrank_pos (R := ℚ) (M := K)
    omega
  have hdR : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd
  have hh19 : 19 ≤ acH K b v := (acH_lower H).1
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hlog : 0 < Real.log (2 * r * (dK K : ℝ)) := log_2rd_pos hr hd
  have hDpos : 0 < acD K σ := pD_pos hr hd σ hσ
  have hSpos : 0 < acS K r b v := by
    have h1 : 0 < pS r (dK K) (acH K b v) := by
      rw [pS]
      have : 0 < acH K b v := by omega
      positivity
    exact_mod_cast h1
  have hss0 : (0 : ℝ) ≤ ((|s| : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ |s| := abs_nonneg s
    exact_mod_cast this
  have h2r4 : (4 : ℝ) ≤ (2 : ℝ) ^ r := by
    have h : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
    norm_num at h
    exact h
  -- `Tst ≤ T`, so `dhT* ≤ 0.735 SD` (`num_T`)
  have hTs : (dK K : ℝ) * (acH K b v : ℝ) * Tst ≤ 0.735 * acS K r b v * acD K σ := by
    have h1 := (num_T hr hd hh19 σ hσ).2.2.1
    have h2 : Tst ≤ (pT r (dK K) σ : ℝ) := hTst
    have h3 : (0 : ℝ) ≤ (dK K : ℝ) * (acH K b v : ℝ) := by positivity
    calc (dK K : ℝ) * (acH K b v : ℝ) * Tst
        ≤ (dK K : ℝ) * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ ≤ 0.735 * acS K r b v * acD K σ := h1
  have hHp : Height.logHeight p ≤ 0.85 * acS K r b v * acD K σ := H.hp12
  have hSD : Real.log 2 ≤ 0.001 * acS K r b v * acD K σ := (num_kum hr hd hh19 σ hσ J).2.2
  -- the Kummer contribution stays below `2·2 SD` (BW p. 58: `0·044 J ≤ 2·2 log(2rd)`)
  have hkum : kumJ K b v σ J ≤ 2.2 * acS K r b v * acD K σ := by
    rw [kumJ]
    have hJle : (J : ℝ) ≤ 50 * Real.log (2 * r * (dK K : ℝ)) := by
      have h1 : (pI r (dK K) : ℝ) ≤ 50 * Real.log (2 * r * (dK K : ℝ)) := by
        simpa only [pI] using
          Nat.floor_le (show (0 : ℝ) ≤ 50 * Real.log (2 * r * (dK K : ℝ)) by positivity)
      exact le_trans (by exact_mod_cast hJ) h1
    have hSDnn : 0 ≤ acS K r b v * acD K σ := le_of_lt (mul_pos hSpos hDpos)
    calc 0.044 * (J : ℝ) / Real.log (2 * r * (dK K : ℝ)) * acS K r b v * acD K σ
        = (0.044 * (J : ℝ) / Real.log (2 * r * (dK K : ℝ))) *
            (acS K r b v * acD K σ) := by ring
      _ ≤ 2.2 * (acS K r b v * acD K σ) := by
          apply mul_le_mul_of_nonneg_right _ hSDnn
          rw [div_le_iff₀ hlog]
          nlinarith [hJle]
      _ = 2.2 * acS K r b v * acD K σ := by ring
  -- the order bound `|s|/2^J ≤ 4S ≤ 2^r S`
  have hss : ((|s| : ℤ) : ℝ) / 2 ^ J ≤ 2 ^ r * acS K r b v := by
    have h4S : (4 : ℝ) * acS K r b v ≤ 2 ^ r * acS K r b v :=
      mul_le_mul_of_nonneg_right h2r4 (le_of_lt hSpos)
    linarith [hs, h4S]
  exact est16_half_arith (A := lnp φ p) (d := (dK K : ℝ)) (h := (acH K b v : ℝ))
    (S := acS K r b v) (D := acD K σ) (Tst := Tst) (Hp := Height.logHeight p)
    (kumJ := kumJ K b v σ J) (ss := ((|s| : ℤ) : ℝ)) (r := r) (J := J)
    hr hdR hSpos (le_of_lt hDpos) hss0 hTs hHp hss hkum hSD

end Work.BW
