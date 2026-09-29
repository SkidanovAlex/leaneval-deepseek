import Mathlib
import Submission.Work.Cert.ACBall.LuneChain
import Submission.Work.Cert.ACBall.luneR_taylor_pieces
import Submission.Work.Cert.ACBall.lR_centre_bounds
import Submission.Work.Cert.ACBall.lRpD_num

/-! # Disc bounds for the lune radicand `R = luneR (36/5)`

`R z = (1+c²)²(1+z)² - 16c² z` (`c = 36/5`) is a quadratic polynomial, so it is *exactly*
determined by its value and its derivative at one point:

`R z - R z₀ = R'(z₀)(z - z₀) + (1+c²)² (z - z₀)²`,  `R' z - R' z₀ = 2(1+c²)² (z - z₀)`.

The ball chain `lR st ∋ R(-c)`, `lRp st ∋ R'(-c)` (`ACBall.LuneChain`) together with the witnesses
`w.RU`, `w.RL`, `w.rpU` of `lokM` therefore bound `R` on the whole input disc `‖z + c‖ ≤ ρ/S`:

* `|R z| ≤ (w.RU + (lR st).r)/S + sup|R'|·ρ/S` with `sup|R'| ≤ lRpD/S`,
  where `lRpD = w.rpU + (lRp st).r + ⌈ρ·2(1+c²)²/S⌉ + 1` and the `⌈·⌉` term absorbs both the
  factor `ρ/S` in the sup bound and the second-order term `(1+c²)²(ρ/S)²`;
* symmetrically `|R z| ≥ (w.RL - (lR st).r)/S - sup|R'|·ρ/S`;
* `|R' z| ≤ lRpD/S` directly.

The two roundings `⌈ρ·lRpD/S⌉/S` and `(w.rpU + (lRp st).r)/S + (lRpp/S)(ρ/S)` are the content of
`lRpD_num`; the purely analytic part is `luneR_taylor_pieces` and the point enclosures are
`lR_centre_bounds`. -/

namespace Work.Cert.ACBall
open Work.Cert

/-- The `lokM` flag of the lune checker, split into its ten conjuncts. -/
lemma lokM_spec (st : St) (w : LuneW) (h : lokM st w = true) :
    0 ≤ w.D ∧ (lvp st w).x * (lvp st w).x + (lvp st w).y * (lvp st w).y ≤ w.D * w.D ∧
    0 ≤ w.zU ∧ st.cr * st.cr + st.ci * st.ci ≤ w.zU * w.zU ∧
    0 ≤ w.RU ∧ (lR st).x * (lR st).x + (lR st).y * (lR st).y ≤ w.RU * w.RU ∧
    0 ≤ w.RL ∧ w.RL * w.RL ≤ (lR st).x * (lR st).x + (lR st).y * (lR st).y ∧
    0 ≤ w.rpU ∧ (lRp st).x * (lRp st).x + (lRp st).y * (lRp st).y ≤ w.rpU * w.rpU := by
  simp only [lokM, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> tauto

/-- `(lRpp : ℝ)/S = 2(1+(36/5)²)²`, the modulus of the second derivative of `luneR (36/5)`. -/
lemma lRpp_mS : ((lRpp : ℤ) : ℝ) / (S : ℝ) = 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 := by
  simpa only [lRpp, mS] using mS_twoLB2

theorem luneR_disc_bounds (st : St) (w : LuneW) (hokM : lokM st w = true) (hrho : 0 ≤ st.rho)
    {z : ℂ} (hz : ‖z - (-(cIn st))‖ ≤ (st.rho : ℝ) / S) :
    ‖Work.APsi.luneR (36 / 5) z‖ ≤ (lRhi st w : ℝ) / S ∧
    ‖deriv (Work.APsi.luneR (36 / 5)) z‖ ≤ (lRpD st w : ℝ) / S ∧
    (lRlo st w : ℝ) / S ≤ ‖Work.APsi.luneR (36 / 5) z‖ := by
  obtain ⟨hD0, hvpD, hzU0, hcU, hRU0, hRUsq, hRL0, hRLsq, hrpU0, hrpUsq⟩ := lokM_spec st w hokM
  obtain ⟨hRc_hi, hRc_lo, hRp_hi⟩ := lR_centre_bounds st w hRU0 hRUsq hRL0 hRLsq hrpU0 hrpUsq
  obtain ⟨hTay1, hTay2⟩ := luneR_taylor_pieces z (-(cIn st))
  obtain ⟨hnum1, hnum2⟩ := lRpD_num st w hrho
  have hSpos : (0 : ℝ) < (S : ℝ) := S_posR
  have hrhoR : (0 : ℝ) ≤ (st.rho : ℝ) := by exact_mod_cast hrho
  have hd0 : (0 : ℝ) ≤ ‖z - (-(cIn st))‖ := norm_nonneg _
  have hd : ‖z - (-(cIn st))‖ ≤ (st.rho : ℝ) / (S : ℝ) := hz
  have hCpp : ((lRpp : ℤ) : ℝ) / (S : ℝ) = 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 := lRpp_mS
  have hA20 : (0 : ℝ) ≤ (1 + (36 / 5 : ℝ) ^ 2) ^ 2 := by positivity
  have hCache : (1 + (36 / 5 : ℝ) ^ 2) ^ 2 ≤ ((lRpp : ℤ) : ℝ) / (S : ℝ) := by
    rw [hCpp]; linarith
  have hCache2 : 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 ≤ ((lRpp : ℤ) : ℝ) / (S : ℝ) := by rw [hCpp]
  have hCnn : (0 : ℝ) ≤ ((lRpp : ℤ) : ℝ) / (S : ℝ) := by rw [hCpp]; positivity
  have hRpU0 : (0 : ℝ) ≤ ((w.rpU + (lRp st).r : ℤ) : ℝ) / (S : ℝ) := by
    apply div_nonneg _ (le_of_lt hSpos)
    have hr : (0 : ℝ) ≤ ((lRp st).r : ℝ) := by
      exact_mod_cast (nonneg_radius (ballMem_lRp st) : (0 : ℤ) ≤ (lRp st).r)
    have h1 : (0 : ℝ) ≤ (w.rpU : ℝ) := by exact_mod_cast hrpU0
    push_cast
    linarith
  have hA : ‖deriv (Work.APsi.luneR (36 / 5)) (-(cIn st))‖ * ‖z - (-(cIn st))‖
      ≤ (((w.rpU + (lRp st).r : ℤ) : ℝ) / (S : ℝ)) * ((st.rho : ℝ) / (S : ℝ)) :=
    mul_le_mul hRp_hi hd hd0 hRpU0
  have hB : (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * ‖z - (-(cIn st))‖ ^ 2
      ≤ (((lRpp : ℤ) : ℝ) / (S : ℝ)) * ((st.rho : ℝ) / (S : ℝ)) ^ 2 :=
    mul_le_mul hCache (pow_le_pow_left₀ hd0 hd 2) (sq_nonneg _) hCnn
  have htri1 : ‖Work.APsi.luneR (36 / 5) z‖
      ≤ ‖Work.APsi.luneR (36 / 5) (-(cIn st))‖
        + ‖Work.APsi.luneR (36 / 5) z - Work.APsi.luneR (36 / 5) (-(cIn st))‖ := by
    have h := norm_add_le (Work.APsi.luneR (36 / 5) (-(cIn st)))
      (Work.APsi.luneR (36 / 5) z - Work.APsi.luneR (36 / 5) (-(cIn st)))
    have he : Work.APsi.luneR (36 / 5) (-(cIn st))
        + (Work.APsi.luneR (36 / 5) z - Work.APsi.luneR (36 / 5) (-(cIn st)))
        = Work.APsi.luneR (36 / 5) z := by ring
    rw [he] at h
    exact h
  have hh1 : ‖Work.APsi.luneR (36 / 5) z - Work.APsi.luneR (36 / 5) (-(cIn st))‖
      ≤ ‖deriv (Work.APsi.luneR (36 / 5)) (-(cIn st))‖ * ‖z - (-(cIn st))‖
        + (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * ‖z - (-(cIn st))‖ ^ 2 := hTay1
  have hpart1 : ‖Work.APsi.luneR (36 / 5) z‖ ≤ (lRhi st w : ℝ) / S := by
    have hhi : ((w.RU + (lR st).r : ℤ) : ℝ) / (S : ℝ)
        + ((mu st.rho (lRpD st w) : ℤ) : ℝ) / (S : ℝ) ≤ (lRhi st w : ℝ) / S := by
      have he : ((lRhi st w : ℤ) : ℝ) / (S : ℝ)
          = ((w.RU + (lR st).r : ℤ) : ℝ) / (S : ℝ)
            + ((mu st.rho (lRpD st w) : ℤ) : ℝ) / (S : ℝ) + 1 / (S : ℝ) := by
        rw [lRhi]; push_cast; ring
      rw [he]
      have hpos : (0 : ℝ) < 1 / (S : ℝ) := one_div_pos.mpr hSpos
      linarith
    linarith [htri1, hh1, hA, hB, hnum1, hRc_hi, hhi]
  have hpart2 : ‖deriv (Work.APsi.luneR (36 / 5)) z‖ ≤ (lRpD st w : ℝ) / S := by
    have h2a : ‖deriv (Work.APsi.luneR (36 / 5)) z‖
        ≤ ‖deriv (Work.APsi.luneR (36 / 5)) (-(cIn st))‖
          + ‖deriv (Work.APsi.luneR (36 / 5)) z
              - deriv (Work.APsi.luneR (36 / 5)) (-(cIn st))‖ := by
      have h := norm_add_le (deriv (Work.APsi.luneR (36 / 5)) (-(cIn st)))
        (deriv (Work.APsi.luneR (36 / 5)) z - deriv (Work.APsi.luneR (36 / 5)) (-(cIn st)))
      have he : deriv (Work.APsi.luneR (36 / 5)) (-(cIn st))
          + (deriv (Work.APsi.luneR (36 / 5)) z - deriv (Work.APsi.luneR (36 / 5)) (-(cIn st)))
          = deriv (Work.APsi.luneR (36 / 5)) z := by ring
      rw [he] at h
      exact h
    have h2b : ‖deriv (Work.APsi.luneR (36 / 5)) z
          - deriv (Work.APsi.luneR (36 / 5)) (-(cIn st))‖
        ≤ 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * ‖z - (-(cIn st))‖ := hTay2
    have h2c : 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * ‖z - (-(cIn st))‖
        ≤ (((lRpp : ℤ) : ℝ) / (S : ℝ)) * ((st.rho : ℝ) / (S : ℝ)) :=
      mul_le_mul hCache2 hd hd0 hCnn
    linarith [h2a, h2b, h2c, hRp_hi, hnum2]
  have hpart3 : (lRlo st w : ℝ) / S ≤ ‖Work.APsi.luneR (36 / 5) z‖ := by
    have h3b : ‖Work.APsi.luneR (36 / 5) (-(cIn st))‖
        ≤ ‖Work.APsi.luneR (36 / 5) z‖
          + ‖Work.APsi.luneR (36 / 5) z - Work.APsi.luneR (36 / 5) (-(cIn st))‖ := by
      have h := norm_add_le (Work.APsi.luneR (36 / 5) z)
        (Work.APsi.luneR (36 / 5) (-(cIn st)) - Work.APsi.luneR (36 / 5) z)
      have he : Work.APsi.luneR (36 / 5) z
          + (Work.APsi.luneR (36 / 5) (-(cIn st)) - Work.APsi.luneR (36 / 5) z)
          = Work.APsi.luneR (36 / 5) (-(cIn st)) := by ring
      rw [he] at h
      rw [norm_sub_rev] at h
      exact h
    have hlo : (lRlo st w : ℝ) / S
        = ((w.RL - (lR st).r : ℤ) : ℝ) / (S : ℝ)
          - ((mu st.rho (lRpD st w) : ℤ) : ℝ) / (S : ℝ) - 1 / (S : ℝ) := by
      rw [lRlo]; push_cast; ring
    rw [hlo]
    linarith [h3b, hh1, hA, hB, hnum1, hRc_lo, one_div_pos.mpr hSpos]
  exact ⟨hpart1, hpart2, hpart3⟩

end Work.Cert.ACBall
