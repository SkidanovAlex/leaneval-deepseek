import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est13p
import Submission.Work.BW.est_Pi
import Submission.Work.BW.est_Theta_yu
import Submission.Work.BW.num_13
import Submission.Work.BW.num_T
import Submission.Work.BW.ulcm_le_three_pow
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.log_ulcm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

set_option maxHeartbeats 4000000 in
/-- The complex-norm bound for the rational factor of the `est17` expansion at descent level `J`:
the product `∏_m Δ(γ_{ι m}(λ);t_m) · u(h)^{t₀} · Θ(2^{-J}(s/2)+λ₋₁; h, λ₀+1, t₀)` has complex
absolute value at most `exp(hT* + 0.1hT + (log 1.7)T + Θe)` with
`Θe = ((log(57rd) + 3/(57rd))h + z/(57rd))(D₀+1)`, `z = |s|/2^{J+1}`, `T = acT K σl`,
`λ = lm : AuxIdx r h D₀ D_j`, `λ₋₁ < h`, `λ₀ ≤ D₀`. Uses `est_Pi` for the `Δ`-product,
`Theta_bound` (sibling `est13`) for `Θ`, `ulcm_le_three_pow` + `num_13` for the `u(h)^{t₀}`
excess, and the elementary `log(3+z/h) ≤ log M + (3+z/h)/M - 1` (`M = 57rd`) to move the
`z`-dependence into the `z(D₀+1)/M` slot. -/
theorem est17_arch_rat_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {Lm : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σl : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) → K}
    (H : ACHyp φ α b k c v Lm α' σl ι p) (J : ℕ) (Tst : ℝ) (hTst : Tst ≤ acT K σl)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) :
    ‖(∏ m, Delta (gam b k Lm (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
        * (ulcm (acH K b v) : ℂ) ^ t0
        * Theta (((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ))
            (acH K b v) ((lm.2.1 : ℕ) + 1) t0‖
      ≤ Real.exp ((acH K b v : ℝ) * Tst
          + 0.1 * (acH K b v : ℝ) * acT K σl
          + Real.log 1.7 * acT K σl
          + ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 3 / (57 * (r : ℝ) * (dK K : ℝ)))
                * (acH K b v : ℝ)
              + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / (57 * (r : ℝ) * (dK K : ℝ)))
              * ((pD0 r (dK K) σl : ℝ) + 1)) := by
  classical
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := by
    have hpos : 0 < dK K := by
      haveI : Nontrivial K := inferInstance
      exact Module.finrank_pos (R := ℚ) (M := K)
    omega
  have hh : 19 ≤ acH K b v := (acH_lower H).1
  have hh1 : 1 ≤ acH K b v := le_trans (by norm_num) hh
  have hhR : (0 : ℝ) < (acH K b v : ℝ) := by
    exact_mod_cast (show (0 : ℕ) < acH K b v by omega)
  have hTst' : Tst ≤ (pT r (dK K) σl : ℝ) := hTst
  have hcast : ((t0 + ∑ m, t m : ℕ) : ℝ) = (t0 : ℝ) + ((∑ m, t m : ℕ) : ℝ) := by
    push_cast
    ring
  have ht0T : (t0 : ℝ) ≤ (pT r (dK K) σl : ℝ) := by
    have h1 : (t0 : ℝ) ≤ ((t0 + ∑ m, t m : ℕ) : ℝ) := by
      rw [hcast]
      exact le_add_of_nonneg_right (by positivity)
    exact le_trans h1 (le_trans ht hTst')
  have hsumT : ((∑ m, t m : ℕ) : ℝ) ≤ (pT r (dK K) σl : ℝ) := by
    have h1 : ((∑ m, t m : ℕ) : ℝ) ≤ ((t0 + ∑ m, t m : ℕ) : ℝ) := by
      rw [hcast]
      exact le_add_of_nonneg_left (by positivity)
    exact le_trans h1 (le_trans ht hTst')
  set z : ℝ := ((|s| : ℤ) : ℝ) / 2 / 2 ^ J with hzdef
  have hznn : (0 : ℝ) ≤ z := by rw [hzdef]; positivity
  set M : ℝ := 57 * (r : ℝ) * (dK K : ℝ) with hMdef
  have hMpos : (0 : ℝ) < M := by rw [hMdef]; positivity
  set Θe : ℝ := ((Real.log M + 3 / M) * (acH K b v : ℝ) + z / M)
      * ((pD0 r (dK K) σl : ℝ) + 1) with hΘedef
  -- (1) the `Δ`-product, by `est_Pi`
  have hP : ‖∏ m, Delta (gam b k Lm (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)‖
      ≤ Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)) * 1.7 ^ pT r (dK K) σl := by
    refine est_Pi H (fun i => (lm.2.2 i : ℕ)) (fun i => ?_) t ?_
    · exact Nat.lt_succ_iff.mp (lm.2.2 i).isLt
    · exact hsumT
  -- (2) the `u(h)^{t₀}` factor
  have hU : ‖((ulcm (acH K b v) : ℂ)) ^ t0‖
      ≤ Real.exp (Real.log (ulcm (acH K b v)) * (t0 : ℝ)) := by
    have hu : (0 : ℝ) < (ulcm (acH K b v) : ℝ) := by
      have h := ulcm_pos (acH K b v)
      exact_mod_cast h
    rw [norm_pow, Complex.norm_natCast,
      ← Real.rpow_natCast (ulcm (acH K b v) : ℝ) t0, Real.rpow_def_of_pos hu]
  -- (3) the `Θ` factor
  have hTheta : ‖Theta (((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ))
        (acH K b v) ((lm.2.1 : ℕ) + 1) t0‖ ≤ Real.exp Θe := by
    have hzn : ‖((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2)‖ = z := by
      have h2J : ‖((2 : ℂ) ^ J)⁻¹‖ = ((2 : ℝ) ^ J)⁻¹ := by
        rw [norm_inv, norm_pow]
        norm_num
      have hs2 : ‖((s : ℂ) / 2)‖ = ((|s| : ℤ) : ℝ) / 2 := by
        rw [Complex.norm_div, Complex.norm_intCast]
        norm_num
      rw [norm_mul, h2J, hs2, hzdef]
      ring
    have hwnorm : ‖((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ)‖
        ≤ z + (acH K b v : ℝ) := by
      calc ‖((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ)‖
          ≤ ‖((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2)‖ + ‖(((lm.1 : ℕ) : ℂ))‖ := norm_add_le _ _
        _ = z + ((lm.1 : ℕ) : ℝ) := by rw [hzn, Complex.norm_natCast]
        _ ≤ z + (acH K b v : ℝ) := by
            have hlt : ((lm.1 : ℕ) : ℝ) ≤ (acH K b v : ℝ) := by
              exact_mod_cast (le_of_lt lm.1.isLt : (lm.1 : ℕ) ≤ acH K b v)
            linarith
    have hbase : Real.exp 1
          * (2 + ‖((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ)‖ / (acH K b v : ℝ))
        ≤ Real.exp 1 * (3 + z / (acH K b v : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      have h2 : ‖((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ)‖ / (acH K b v : ℝ)
          ≤ (z + (acH K b v : ℝ)) / (acH K b v : ℝ) :=
        div_le_div_of_nonneg_right hwnorm hhR.le
      have h3 : 2 + (z + (acH K b v : ℝ)) / (acH K b v : ℝ) = 3 + z / (acH K b v : ℝ) := by
        field_simp
        ring
      linarith
    have hexp : (acH K b v) * ((lm.2.1 : ℕ) + 1) ≤ (acH K b v) * ((pD0 r (dK K) σl) + 1) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr (lm.2.1).isLt)
    have h4a := Theta_bound (((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ))
      (acH K b v) ((lm.2.1 : ℕ) + 1) t0 hh1
    have h4b : (Real.exp 1 * (2 + ‖((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ)‖
            / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1))
        ≤ (Real.exp 1 * (3 + z / (acH K b v : ℝ)))
            ^ ((acH K b v) * ((pD0 r (dK K) σl) + 1)) := by
      have hbase1 : (1 : ℝ) ≤ Real.exp 1 * (3 + z / (acH K b v : ℝ)) := by
        have h1 : (1 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp 1
          linarith
        have h2 : (1 : ℝ) ≤ 3 + z / (acH K b v : ℝ) := by
          have h3 : (0 : ℝ) ≤ z / (acH K b v : ℝ) := by positivity
          linarith
        nlinarith [h1, h2]
      calc (Real.exp 1 * (2 + ‖((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ)‖
              / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1))
          ≤ (Real.exp 1 * (3 + z / (acH K b v : ℝ))) ^ ((acH K b v) * ((lm.2.1 : ℕ) + 1)) :=
            pow_le_pow_left₀ (by positivity) hbase _
        _ ≤ (Real.exp 1 * (3 + z / (acH K b v : ℝ)))
              ^ ((acH K b v) * ((pD0 r (dK K) σl) + 1)) :=
            pow_le_pow_right₀ hbase1 hexp
    have h4c : (Real.exp 1 * (3 + z / (acH K b v : ℝ)))
          ^ ((acH K b v) * ((pD0 r (dK K) σl) + 1))
        = Real.exp ((((acH K b v) * ((pD0 r (dK K) σl) + 1) : ℕ) : ℝ)
            * (1 + Real.log (3 + z / (acH K b v : ℝ)))) := by
      rw [← Real.rpow_natCast (Real.exp 1 * (3 + z / (acH K b v : ℝ)))
          ((acH K b v) * ((pD0 r (dK K) σl) + 1)),
        Real.rpow_def_of_pos (by positivity),
        Real.log_mul (ne_of_gt (Real.exp_pos 1))
          (ne_of_gt (by positivity : (0 : ℝ) < 3 + z / (acH K b v : ℝ))),
        Real.log_exp]
      congr 1
      ring
    have h4d : Real.log (3 + z / (acH K b v : ℝ))
        ≤ Real.log M + (3 + z / (acH K b v : ℝ)) / M - 1 := by
      have h1 : (0 : ℝ) < (3 + z / (acH K b v : ℝ)) / M := by positivity
      have h2 := Real.log_le_sub_one_of_pos h1
      rw [Real.log_div (ne_of_gt (by positivity : (0 : ℝ) < 3 + z / (acH K b v : ℝ)))
        (ne_of_gt hMpos)] at h2
      linarith
    have h4e : Real.exp ((((acH K b v) * ((pD0 r (dK K) σl) + 1) : ℕ) : ℝ)
          * (1 + Real.log (3 + z / (acH K b v : ℝ)))) ≤ Real.exp Θe := by
      apply Real.exp_le_exp.mpr
      rw [hΘedef]
      have heq : (((acH K b v) * ((pD0 r (dK K) σl) + 1) : ℕ) : ℝ)
          = (acH K b v : ℝ) * (((pD0 r (dK K) σl : ℕ) : ℝ) + 1) := by
        push_cast
        ring
      rw [heq]
      have h1 : 1 + Real.log (3 + z / (acH K b v : ℝ))
          ≤ Real.log M + 3 / M + z / ((acH K b v : ℝ) * M) := by
        have h := h4d
        have hsplit : (3 + z / (acH K b v : ℝ)) / M = 3 / M + z / ((acH K b v : ℝ) * M) := by
          field_simp
        linarith [h, hsplit.le]
      have h2 := mul_le_mul_of_nonneg_left h1
        (by positivity : (0 : ℝ) ≤ (acH K b v : ℝ) * (((pD0 r (dK K) σl : ℕ) : ℝ) + 1))
      have h3 : (acH K b v : ℝ) * (((pD0 r (dK K) σl : ℕ) : ℝ) + 1)
            * (Real.log M + 3 / M + z / ((acH K b v : ℝ) * M))
          = ((Real.log M + 3 / M) * (acH K b v : ℝ) + z / M)
            * (((pD0 r (dK K) σl : ℕ) : ℝ) + 1) := by
        field_simp
      linarith [h2, h3.le]
    exact le_trans h4a (le_trans h4b (le_trans (le_of_eq h4c) h4e))
  -- (4) assemble
  have h17 : (1.7 : ℝ) ^ pT r (dK K) σl
      = Real.exp (Real.log 1.7 * (pT r (dK K) σl : ℝ)) := by
    rw [← Real.rpow_natCast (1.7 : ℝ) (pT r (dK K) σl),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1.7)]
  have hcombine : ‖(∏ m, Delta (gam b k Lm (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
        * (ulcm (acH K b v) : ℂ) ^ t0
        * Theta (((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ))
            (acH K b v) ((lm.2.1 : ℕ) + 1) t0‖
      ≤ Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
          + Real.log (ulcm (acH K b v)) * (t0 : ℝ)
          + Real.log 1.7 * (pT r (dK K) σl : ℝ) + Θe) := by
    rw [norm_mul, norm_mul]
    calc ‖∏ m, Delta (gam b k Lm (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)‖
            * ‖((ulcm (acH K b v) : ℂ)) ^ t0‖
            * ‖Theta (((2 : ℂ) ^ J)⁻¹ * ((s : ℂ) / 2) + ((lm.1 : ℕ) : ℂ))
                (acH K b v) ((lm.2.1 : ℕ) + 1) t0‖
        ≤ (Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)) * 1.7 ^ pT r (dK K) σl)
            * Real.exp (Real.log (ulcm (acH K b v)) * (t0 : ℝ)) * Real.exp Θe := by
          gcongr
      _ = Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
            + Real.log (ulcm (acH K b v)) * (t0 : ℝ)
            + Real.log 1.7 * (pT r (dK K) σl : ℝ) + Θe) := by
          rw [h17, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  have hfin : Real.exp ((acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ)
        + Real.log (ulcm (acH K b v)) * (t0 : ℝ)
        + Real.log 1.7 * (pT r (dK K) σl : ℝ) + Θe)
      ≤ Real.exp ((acH K b v : ℝ) * Tst + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σl : ℝ)
          + Real.log 1.7 * (pT r (dK K) σl : ℝ) + Θe) := by
    apply Real.exp_le_exp.mpr
    have hlu : Real.log (ulcm (acH K b v)) ≤ 1.1 * (acH K b v : ℝ) := log_ulcm_le _ hh
    have ht0nn : (0 : ℝ) ≤ (t0 : ℝ) := Nat.cast_nonneg _
    have h1 : (acH K b v : ℝ) * ((∑ m, t m : ℕ) : ℝ) + (acH K b v : ℝ) * (t0 : ℝ)
        ≤ (acH K b v : ℝ) * Tst := by
      have h2 : ((∑ m, t m : ℕ) : ℝ) + (t0 : ℝ) ≤ Tst := by
        have h3 : ((∑ m, t m : ℕ) : ℝ) + (t0 : ℝ) = ((t0 + ∑ m, t m : ℕ) : ℝ) := by
          rw [hcast]; ring
        rw [h3]; exact ht
      nlinarith [h2, hhR.le]
    have h3 : Real.log (ulcm (acH K b v)) * (t0 : ℝ)
        ≤ (acH K b v : ℝ) * (t0 : ℝ) + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σl : ℝ) := by
      have h4 : Real.log (ulcm (acH K b v)) * (t0 : ℝ)
          ≤ (1.1 * (acH K b v : ℝ)) * (t0 : ℝ) :=
        mul_le_mul_of_nonneg_right hlu ht0nn
      have h5 : (1.1 * (acH K b v : ℝ)) * (t0 : ℝ)
          ≤ (acH K b v : ℝ) * (t0 : ℝ) + 0.1 * (acH K b v : ℝ) * (pT r (dK K) σl : ℝ) := by
        nlinarith [ht0T, hhR.le]
      linarith
    linarith
  exact le_trans hcombine hfin

end Work.BW
