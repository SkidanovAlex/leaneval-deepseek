import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num_13
import Submission.Work.BW.est14_thetaopt
import Submission.Work.BW.est_Theta_yu
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The third conjunct of `num_13`, isolated: the `Θ`-arithmetic.  Sorry-free. -/
lemma est21_dpbB_num13_third {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 19 ≤ h)
    (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (x : ℝ) (hx : 0 ≤ x) :
    ((Real.log (57 * r * d) + 2 / (57 * r * d)) * h + x / (57 * r * d)) * (pD0 r d σ + 1) ≤
      (0.108 * (pS r d h : ℝ) + 0.007 * x) * pD r d σ / d := by
  push_cast
  have hpart := num13_hpart hr hd σ hσ
  have xpart := num13_xpart hr hd σ hσ
  have hh0 : (0:ℝ) ≤ (h:ℝ) := by positivity
  have hr0 : (0:ℝ) < (r:ℝ) := by
    have : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hS : (pS r d h : ℝ) = 16 * (r:ℝ) * (d:ℝ) * (h:ℝ) := by
    simp only [pS]; push_cast; ring
  have h1 : (Real.log (57 * (r:ℝ) * (d:ℝ)) + 2 / (57 * (r:ℝ) * (d:ℝ))) * (h:ℝ)
        * ((pD0 r d σ : ℝ) + 1)
      ≤ 1.728 * (r:ℝ) * pD r d σ * (h:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hpart hh0
    linarith [h]
  have h2 : x / (57 * (r:ℝ) * (d:ℝ)) * ((pD0 r d σ : ℝ) + 1)
      ≤ 0.007 * x * pD r d σ / (d:ℝ) := by
    have hstep : x / (57 * (r:ℝ) * (d:ℝ)) * ((pD0 r d σ : ℝ) + 1)
        ≤ x / (57 * (r:ℝ) * (d:ℝ)) * (0.399 * ((r:ℝ) * pD r d σ)) :=
      mul_le_mul_of_nonneg_left xpart (by positivity)
    have hxe : x / (57 * (r:ℝ) * (d:ℝ)) * (0.399 * ((r:ℝ) * pD r d σ))
        = 0.007 * x * pD r d σ / (d:ℝ) := by
      field_simp
      ring
    rw [hxe] at hstep
    exact hstep
  rw [add_mul]
  have hS3 : (0.108:ℝ) * (pS r d h : ℝ) * pD r d σ / (d:ℝ)
      = 1.728 * (r:ℝ) * pD r d σ * (h:ℝ) := by
    rw [hS]; field_simp; ring
  have hRHS : (0.108 * (pS r d h : ℝ) + 0.007 * x) * pD r d σ / (d:ℝ)
      = 0.108 * (pS r d h : ℝ) * pD r d σ / (d:ℝ) + 0.007 * x * pD r d σ / (d:ℝ) := by
    ring
  rw [hRHS, hS3]
  linarith [h1, h2]

/-- Port of `Work.BW.est21_dpb_aeval_le` — the `Θ`-evaluation bound of the BW p. 49 `0.255` estimate.  The original lives in `Submission/Work/BW/est21_dpb_clean.lean` (line 86) and its proof should be copied; that file imports `Submission.Work.BW.est13`, which does NOT compile, so nothing there is importable — you must import the sorry-free `Submission.Work.BW.est13_clean` if you need anything from `est13` (this statement does not).  The proof needs the local helper `est21_dpb_num13_third` (line 61 of `est21_dpb_clean.lean`), a sorry-free variant of the third conjunct of `num_13` built on `num13_hpart`/`num13_xpart`; port it too.  ANY extra declaration you make must have a name starting with `est21_dpbB_` and be public, so that this module can be imported together with the other `est21_dpb*` ports. -/
lemma est21_dpbB_aeval_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (t0 : ℕ) (z : ℂ)
    (ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ))
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ‖Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
        (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))‖ ≤
      Real.exp ((0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) *
        acD K σ / (dK K : ℝ)) := by
  have hHn : 0 < acH K b v := by have h := (acH_lower H).1; omega
  have hHpos : (0:ℝ) < (acH K b v : ℝ) := by exact_mod_cast hHn
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hr2' : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast H.hr
  have hdr : (0:ℝ) < (dK K : ℝ) := by
    have : (0:ℕ) < dK K := Module.finrank_pos (R := ℚ) (M := K)
    exact_mod_cast this
  have hmu : (0:ℝ) < 57 * (r : ℝ) * (dK K : ℝ) := by nlinarith [hr2', hdr]
  set w : ℂ := (((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ) with hwdef
  have hw : ‖w‖ ≤ ‖z‖ / 2 ^ J + (acH K b v : ℝ) := by
    have h1 : ‖(((2 : ℂ) ^ J)⁻¹) * z‖ = ‖z‖ / 2 ^ J := by
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_two, div_eq_mul_inv]
      ring
    have h2n : (lm.1 : ℕ) ≤ acH K b v := le_of_lt lm.1.isLt
    have h2 : ((lm.1 : ℕ) : ℝ) ≤ (acH K b v : ℝ) := by exact_mod_cast h2n
    calc ‖w‖ = ‖(((2 : ℂ) ^ J)⁻¹) * z + (((lm.1 : ℕ)) : ℂ)‖ := rfl
      _ ≤ ‖(((2 : ℂ) ^ J)⁻¹) * z‖ + ‖(((lm.1 : ℕ)) : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ / 2 ^ J + ((lm.1 : ℕ) : ℝ) := by rw [h1, Complex.norm_natCast]
      _ ≤ ‖z‖ / 2 ^ J + (acH K b v : ℝ) := by linarith
  have hbase1 : (1:ℝ) ≤ Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ)) := by
    have ha : (0:ℝ) ≤ ‖w‖ / (acH K b v : ℝ) := div_nonneg (norm_nonneg w) hHpos.le
    have hb : (1:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have hc : (1:ℝ) ≤ 1 + ‖w‖ / (acH K b v : ℝ) := by linarith
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ)) :=
          mul_le_mul hb hc (by norm_num) (Real.exp_pos 1).le
  have hlog : Real.log ((Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^
        ((acH K b v) * (pD0 r (dK K) σ + 1))) ≤
      ((pD0 r (dK K) σ : ℝ) + 1) *
        ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
          + (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ))) := by
    have hpos1 : (0:ℝ) < 1 + ‖w‖ / (acH K b v : ℝ) := by
      have ha : (0:ℝ) ≤ ‖w‖ / (acH K b v : ℝ) := div_nonneg (norm_nonneg w) hHpos.le
      linarith
    have hb : Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ)) =
        Real.exp (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ))) := by
      rw [Real.exp_add, Real.exp_log hpos1]
    rw [hb, Real.log_pow, Real.log_exp]
    have hcast : ((↑((acH K b v) * (pD0 r (dK K) σ + 1)) : ℝ)) =
        (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have hopt := est14_thetaopt (mu := 57 * (r : ℝ) * (dK K : ℝ)) (h := (acH K b v : ℝ))
      (x := ‖w‖) hmu hHpos (norm_nonneg w)
    have hopt' : (acH K b v : ℝ) * (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ))) ≤
        (Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
          + ‖w‖ / (57 * (r : ℝ) * (dK K : ℝ)) := by linarith [hopt]
    have hstep : (acH K b v : ℝ) * (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ))) ≤
        (Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
          + (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ)) := by
      have h1 : ‖w‖ / (57 * (r : ℝ) * (dK K : ℝ)) ≤
          (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ)) :=
        div_le_div_of_nonneg_right hw hmu.le
      linarith [hopt']
    calc (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1) *
            (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ)))
        = ((pD0 r (dK K) σ : ℝ) + 1) *
            ((acH K b v : ℝ) * (1 + Real.log (1 + ‖w‖ / (acH K b v : ℝ)))) := by ring
      _ ≤ ((pD0 r (dK K) σ : ℝ) + 1) *
            ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
              + (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  have hnum : ((pD0 r (dK K) σ : ℝ) + 1) *
        ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 2 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ)
          + (‖z‖ / 2 ^ J + (acH K b v : ℝ)) / (57 * (r : ℝ) * (dK K : ℝ))) ≤
      (0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) * acD K σ / (dK K : ℝ) := by
    have h := est21_dpbB_num13_third H.hr (by
        have : (0:ℕ) < dK K := Module.finrank_pos (R := ℚ) (M := K); omega)
      (acH_lower H).1 σ hσ (‖z‖ / 2 ^ J + (acH K b v : ℝ)) (by positivity)
    simpa only [acS, acD, mul_comm, mul_left_comm, mul_assoc] using h
  have hTheta : ‖Theta w (acH K b v) ((lm.2.1 : ℕ) + 1) t0‖ ≤
      (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1)) :=
    est_Theta_yu w (acH K b v) ((lm.2.1 : ℕ) + 1) t0 (by have h := (acH_lower H).1; omega)
  have hpow : (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1))
      ≤ (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * (pD0 r (dK K) σ + 1)) :=
    pow_le_pow_right₀ hbase1
      (Nat.mul_le_mul_left (acH K b v) (Nat.succ_le_succ (Nat.lt_succ_iff.mp lm.2.1.isLt)))
  calc ‖Polynomial.aeval w (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))‖
      = ‖Theta w (acH K b v) ((lm.2.1 : ℕ) + 1) t0‖ := rfl
    _ ≤ (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1)) := hTheta
    _ ≤ (Real.exp 1 * (1 + ‖w‖ / (acH K b v : ℝ))) ^ ((acH K b v) * (pD0 r (dK K) σ + 1)) := hpow
    _ ≤ Real.exp ((0.108 * acS K r b v + 0.007 * (‖z‖ / 2 ^ J + (acH K b v : ℝ))) *
          acD K σ / (dK K : ℝ)) := Real.le_exp_of_log_le (le_trans hlog hnum)

end Work.BW
