import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est13_clean
import Submission.Work.BW.est_Pi
import Submission.Work.BW.est14_phibound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `(u(h))^{t₀} ≤ exp(h t₀ + 0·1 h T)`, from the sorry-free `hanson_ulcm_log_le`. -/
lemma est21_dpbA_ulcm_bound {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) {t0 : ℕ}
    (ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ)) :
    ‖((ulcm (acH K b v) : ℂ) ^ t0)‖ ≤
      Real.exp ((acH K b v : ℝ) * (t0 : ℝ) + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
  have hlog := hanson_ulcm_log_le (acH K b v)
  have hh0 : (0:ℝ) ≤ (acH K b v : ℝ) := by positivity
  have ht0nn : (0:ℝ) ≤ (t0 : ℝ) := Nat.cast_nonneg t0
  rw [norm_pow, Complex.norm_natCast]
  refine Real.le_exp_of_log_le ?_
  rw [Real.log_pow]
  nlinarith [hlog, ht0, hh0, ht0nn]

/-- Port of `Work.BW.est21_dpb_coeff_le` — the coefficient bound of the BW p. 49 `0.255` estimate.  The original lives in `Submission/Work/BW/est21_dpb_clean.lean` (line 192) and its proof should be copied; that file imports `Submission.Work.BW.est13`, which does NOT compile (its `two_pow_le_syl` clashes with `log_ulcm_le`'s declaration of the same public name), so import `Submission.Work.BW.est13_clean` instead, which has the same statements (in particular `hanson_ulcm_log_le`).

The only local helper the original proof needs is `est21_dpb_ulcm_bound` (`‖(ulcm h)^t0‖ ≤ exp(h·t0 + 0.1·h·T)`); port it too.  ANY extra declaration you make must have a name starting with `est21_dpbA_` and must be public lemma/theorem (never shadow another module's name), so that this module can be imported together with the other `est21_dpb*` ports. -/
lemma est21_dpbA_coeff_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) {t0 : ℕ} {t : Fin (r - 1) → ℕ}
    (ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ)) (htT : ((∑ m, t m : ℕ) : ℝ) ≤ acT K σ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ‖φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) *
        (ulcm (acH K b v) : ℂ) ^ t0‖ ≤
      Real.exp (lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
        + (pT r (dK K) σ : ℝ) * Real.log 1.7 + (acH K b v : ℝ) * (t0 : ℝ)
        + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
  have hlm : ∀ j, (fun i => (lm.2.2 i : ℕ)) j ≤ pDj r (dK K) σ j :=
    fun j => Nat.lt_succ_iff.mp (lm.2.2 j).isLt
  have hpi := est_Pi H (fun i => (lm.2.2 i : ℕ)) hlm t htT
  have hphi := est14_phibound φ p H.hp0 lm
  have hul := est21_dpbA_ulcm_bound H ht0
  have hexp17 : (1.7:ℝ) ^ (pT r (dK K) σ) =
      Real.exp ((pT r (dK K) σ : ℝ) * Real.log 1.7) := by
    conv_lhs => rw [← Real.exp_log (by norm_num : (0:ℝ) < 1.7)]
    rw [← Real.exp_nat_mul]
  rw [norm_mul, norm_mul]
  calc ‖φ (p lm)‖ * ‖∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)‖ *
        ‖(ulcm (acH K b v) : ℂ) ^ t0‖
      ≤ Real.exp (lnp φ p)
          * (Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)) * (1.7:ℝ) ^ (pT r (dK K) σ))
          * Real.exp ((acH K b v : ℝ) * (t0 : ℝ) + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
        exact mul_le_mul (mul_le_mul hphi hpi (norm_nonneg _) (Real.exp_pos _).le) hul
          (norm_nonneg _) (by positivity)
    _ = Real.exp (lnp φ p + (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
          + (pT r (dK K) σ : ℝ) * Real.log 1.7 + (acH K b v : ℝ) * (t0 : ℝ)
          + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
        rw [hexp17, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        ring_nf

end Work.BW
