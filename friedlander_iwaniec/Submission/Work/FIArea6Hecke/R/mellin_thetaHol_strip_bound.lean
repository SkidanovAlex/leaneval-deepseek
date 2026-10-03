import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea5.S16Hecke.thetaHol_bound_of_summable
import Submission.Work.FIArea5.S16Hecke.thetaHol_exp_decay

namespace Work.FIArea6Hecke.R

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

open Work.FIArea5.S16Hecke

/-! ## A generic two-piece Mellin bound on the strip `-1/2 ≤ re z ≤ 3/2` -/

theorem mellin_strip_bound_two_piece_aux {f : ℝ → ℂ} {a q B1 B2 : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hq : 1 / 2 < q) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (h1 : ∀ u : ℝ, 0 < u → u ≤ a → ‖f u‖ ≤ B1 * u ^ q)
    (h2 : ∀ u : ℝ, a ≤ u → ‖f u‖ ≤ B2 * Real.exp (-Real.pi * (u - a))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → ‖mellin f z‖ ≤ M := by
  set g : ℝ → ℝ := fun u =>
      B1 * Real.exp (Real.pi * a) * (u ^ (q - 3 / 2) * Real.exp (-Real.pi * u))
      + B2 * Real.exp (Real.pi * a) * a ^ (-(3 / 2 : ℝ)) * Real.exp (-Real.pi * u)
      + B2 * Real.exp (Real.pi * a) * (u ^ ((1 : ℝ) / 2) * Real.exp (-Real.pi * u))
    with hg
  have hA : IntegrableOn (fun u : ℝ => u ^ (q - 3 / 2) * Real.exp (-Real.pi * u)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (s := q - 3 / 2) (p := 1)
      (b := Real.pi) (by linarith) (by norm_num) Real.pi_pos
  have hB : IntegrableOn (fun u : ℝ => Real.exp (-Real.pi * u)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 Real.pi_pos
  have hC : IntegrableOn (fun u : ℝ => u ^ ((1 : ℝ) / 2) * Real.exp (-Real.pi * u)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ) / 2) (p := 1)
      (b := Real.pi) (by norm_num) (by norm_num) Real.pi_pos
  have hg_int : IntegrableOn g (Ioi 0) := by
    rw [hg]
    exact ((hA.const_mul (B1 * Real.exp (Real.pi * a))).add
      (hB.const_mul (B2 * Real.exp (Real.pi * a) * a ^ (-(3 / 2 : ℝ))))).add
      (hC.const_mul (B2 * Real.exp (Real.pi * a)))
  refine ⟨∫ u in Ioi 0, g u, ?_, ?_⟩
  · refine setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have e1 : 0 ≤ B1 * Real.exp (Real.pi * a) * (u ^ (q - 3 / 2) * Real.exp (-Real.pi * u)) :=
      mul_nonneg (mul_nonneg hB1 (Real.exp_pos _).le)
        (mul_nonneg (Real.rpow_nonneg hu0 _) (Real.exp_pos _).le)
    have e2 : 0 ≤ B2 * Real.exp (Real.pi * a) * a ^ (-(3 / 2 : ℝ)) * Real.exp (-Real.pi * u) :=
      mul_nonneg (mul_nonneg (mul_nonneg hB2 (Real.exp_pos _).le) (Real.rpow_nonneg ha.le _))
        (Real.exp_pos _).le
    have e3 : 0 ≤ B2 * Real.exp (Real.pi * a) * (u ^ ((1 : ℝ) / 2) * Real.exp (-Real.pi * u)) :=
      mul_nonneg (mul_nonneg hB2 (Real.exp_pos _).le)
        (mul_nonneg (Real.rpow_nonneg hu0 _) (Real.exp_pos _).le)
    rw [hg]
    linarith
  · intro z hz1 hz2
    show ‖mellin f z‖ ≤ ∫ u in Ioi 0, g u
    refine MeasureTheory.norm_integral_le_of_norm_le hg_int ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    have hnorm : ‖(u : ℂ) ^ (z - 1) • f u‖ = u ^ (z.re - 1) * ‖f u‖ := by
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re, Complex.one_re]
    have e1 : 0 ≤ B1 * Real.exp (Real.pi * a) * (u ^ (q - 3 / 2) * Real.exp (-Real.pi * u)) :=
      mul_nonneg (mul_nonneg hB1 (Real.exp_pos _).le)
        (mul_nonneg (Real.rpow_nonneg hu0.le _) (Real.exp_pos _).le)
    have e2 : 0 ≤ B2 * Real.exp (Real.pi * a) * a ^ (-(3 / 2 : ℝ)) * Real.exp (-Real.pi * u) :=
      mul_nonneg (mul_nonneg (mul_nonneg hB2 (Real.exp_pos _).le) (Real.rpow_nonneg ha.le _))
        (Real.exp_pos _).le
    have e3 : 0 ≤ B2 * Real.exp (Real.pi * a) * (u ^ ((1 : ℝ) / 2) * Real.exp (-Real.pi * u)) :=
      mul_nonneg (mul_nonneg hB2 (Real.exp_pos _).le)
        (mul_nonneg (Real.rpow_nonneg hu0.le _) (Real.exp_pos _).le)
    rw [hnorm, hg]
    rcases le_total u a with hua | hua
    · have hf : ‖f u‖ ≤ B1 * u ^ q := h1 u hu0 hua
      have hu1 : u ≤ 1 := le_trans hua ha1
      have hpow : u ^ (z.re - 1) ≤ u ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by linarith)
      have hsq : u ^ (-(3 / 2 : ℝ)) * u ^ q = u ^ (q - 3 / 2) := by
        rw [← Real.rpow_add hu0]
        congr 1
        ring
      have hstep : u ^ (z.re - 1) * ‖f u‖ ≤ B1 * u ^ (q - 3 / 2) :=
        calc u ^ (z.re - 1) * ‖f u‖
            ≤ u ^ (-(3 / 2 : ℝ)) * (B1 * u ^ q) :=
              mul_le_mul hpow hf (norm_nonneg _) (Real.rpow_nonneg hu0.le _)
          _ = B1 * u ^ (q - 3 / 2) := by
              calc u ^ (-(3 / 2 : ℝ)) * (B1 * u ^ q)
                  = B1 * (u ^ (-(3 / 2 : ℝ)) * u ^ q) := by ring
                _ = B1 * u ^ (q - 3 / 2) := by rw [hsq]
      have hexp1 : 1 ≤ Real.exp (Real.pi * a) * Real.exp (-Real.pi * u) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have hkey : B1 * u ^ (q - 3 / 2) ≤
          B1 * Real.exp (Real.pi * a) * (u ^ (q - 3 / 2) * Real.exp (-Real.pi * u)) := by
        have hr : 0 ≤ u ^ (q - 3 / 2) := Real.rpow_nonneg hu0.le _
        have h0' : 0 ≤ B1 * u ^ (q - 3 / 2) := mul_nonneg hB1 hr
        calc B1 * u ^ (q - 3 / 2)
            = (B1 * u ^ (q - 3 / 2)) * 1 := by ring
          _ ≤ (B1 * u ^ (q - 3 / 2)) * (Real.exp (Real.pi * a) * Real.exp (-Real.pi * u)) :=
              mul_le_mul_of_nonneg_left hexp1 h0'
          _ = B1 * Real.exp (Real.pi * a) * (u ^ (q - 3 / 2) * Real.exp (-Real.pi * u)) := by
              ring
      linarith
    · have hf : ‖f u‖ ≤ B2 * Real.exp (-Real.pi * (u - a)) := h2 u hua
      have hpow : u ^ (z.re - 1) ≤ a ^ (-(3 / 2 : ℝ)) + u ^ ((1 : ℝ) / 2) := by
        rcases le_total u 1 with hu1 | hu1
        · have hp1 : u ^ (z.re - 1) ≤ u ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by linarith)
          have hp2 : u ^ (-(3 / 2 : ℝ)) ≤ a ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos ha hua (by norm_num)
          linarith [Real.rpow_nonneg hu0.le ((1 : ℝ) / 2)]
        · have hp1 : u ^ (z.re - 1) ≤ u ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
          linarith [Real.rpow_nonneg ha.le (-(3 / 2 : ℝ))]
      have hstep : u ^ (z.re - 1) * ‖f u‖ ≤
          (a ^ (-(3 / 2 : ℝ)) + u ^ ((1 : ℝ) / 2)) * (B2 * Real.exp (-Real.pi * (u - a))) :=
        mul_le_mul hpow hf (norm_nonneg _)
          (add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hu0.le _))
      have hexp : Real.exp (-Real.pi * (u - a))
          = Real.exp (Real.pi * a) * Real.exp (-Real.pi * u) := by
        rw [show -Real.pi * (u - a) = Real.pi * a + -Real.pi * u by ring, Real.exp_add]
      have hkey : (a ^ (-(3 / 2 : ℝ)) + u ^ ((1 : ℝ) / 2)) * (B2 * Real.exp (-Real.pi * (u - a)))
          ≤ B1 * Real.exp (Real.pi * a) * (u ^ (q - 3 / 2) * Real.exp (-Real.pi * u))
            + B2 * Real.exp (Real.pi * a) * a ^ (-(3 / 2 : ℝ)) * Real.exp (-Real.pi * u)
            + B2 * Real.exp (Real.pi * a) * (u ^ ((1 : ℝ) / 2) * Real.exp (-Real.pi * u)) := by
        have heq : (a ^ (-(3 / 2 : ℝ)) + u ^ ((1 : ℝ) / 2))
              * (B2 * Real.exp (-Real.pi * (u - a)))
            = B2 * Real.exp (Real.pi * a) * a ^ (-(3 / 2 : ℝ)) * Real.exp (-Real.pi * u)
              + B2 * Real.exp (Real.pi * a) * (u ^ ((1 : ℝ) / 2) * Real.exp (-Real.pi * u)) := by
          rw [hexp]
          ring
        linarith
      linarith

lemma thetaHol_zero_poly_small (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) (hU : unitSum chi 0 ≠ 0)
    (h0 : gaussSum d chi 0 = 0) :
    ∃ B1 : ℝ, 0 ≤ B1 ∧ ∀ u : ℝ, 0 < u → u ≤ 1 / ((4 * (d : ℝ)) ^ 2) →
      ‖thetaHol chi 0 u‖ ≤ B1 * u ^ 2 := by
  obtain ⟨C, δ, hCpos, hδpos, hdec⟩ := hci_thetaOdd_decay_small d hd chi 0 hchi (Or.inl h0)
  refine ⟨‖(unitSum chi 0)⁻¹‖ * C * (2 / δ ^ 2), ?_, ?_⟩
  · have h2 : 0 < 2 / δ ^ 2 := div_pos (by norm_num) (by positivity)
    positivity
  · intro u hu hua
    have hbdd : ‖thetaOdd chi 0 u‖ ≤ C * Real.exp (-δ / u) := hdec u hu hua
    have hexp_le : Real.exp (-δ / u) ≤ 2 / δ ^ 2 * u ^ 2 := by
      have hxu : 0 < δ / u := div_pos hδpos hu
      have h2 : (δ / u) ^ 2 / 2 ≤ Real.exp (δ / u) := by
        have h := Real.pow_div_factorial_le_exp (δ / u) hxu.le 2
        simpa using h
      have hmul : (δ / u) ^ 2 * Real.exp (-(δ / u)) ≤ 2 := by
        have h := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(δ / u))).le
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
        linarith
      have hle : Real.exp (-(δ / u)) ≤ 2 / (δ / u) ^ 2 := by
        rw [le_div_iff₀ (pow_pos hxu 2), mul_comm]
        exact hmul
      have hEq : 2 / (δ / u) ^ 2 = 2 / δ ^ 2 * u ^ 2 := by
        have hδne : δ ≠ 0 := ne_of_gt hδpos
        have hune : u ≠ 0 := ne_of_gt hu
        field_simp
      rw [show -δ / u = -(δ / u) by ring, ← hEq]
      exact hle
    calc ‖thetaHol chi 0 u‖
        = ‖(unitSum chi 0)⁻¹ * thetaOdd chi 0 u‖ := by
          rw [hci_thetaHol_eq_inv_unitSum_mul chi 0 hchi.1.2.1 hU u]
      _ = ‖(unitSum chi 0)⁻¹‖ * ‖thetaOdd chi 0 u‖ := norm_mul _ _
      _ ≤ ‖(unitSum chi 0)⁻¹‖ * (C * Real.exp (-δ / u)) :=
          mul_le_mul_of_nonneg_left hbdd (norm_nonneg _)
      _ ≤ ‖(unitSum chi 0)⁻¹‖ * (C * (2 / δ ^ 2 * u ^ 2)) := by
          have h1 : C * Real.exp (-δ / u) ≤ C * (2 / δ ^ 2 * u ^ 2) :=
            mul_le_mul_of_nonneg_left hexp_le hCpos.le
          exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖(unitSum chi 0)⁻¹‖ * C * (2 / δ ^ 2) * u ^ 2 := by ring

/-- **`mellin (thetaHol χ 0)` is bounded on the closed strip `-1/2 ≤ re z ≤ 3/2`.** -/
theorem mellin_thetaHol_strip_bound (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hU : Work.FIArea5.S16Hecke.unitSum chi 0 ≠ 0)
    (h0 : Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 →
      ‖mellin (Work.FIArea5.S16Hecke.thetaHol chi 0) z‖ ≤ M := by
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  set a : ℝ := 1 / ((4 * (d : ℝ)) ^ 2) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h4d : (1 : ℝ) ≤ 4 * (d : ℝ) := by linarith
    have h4d0 : (0 : ℝ) ≤ 4 * (d : ℝ) := le_trans zero_le_one h4d
    have hmul : (1 : ℝ) * 1 ≤ (4 * (d : ℝ)) * (4 * (d : ℝ)) :=
      mul_le_mul h4d h4d (by norm_num) h4d0
    nlinarith [hmul]
  obtain ⟨B1, hB1nn, hB1⟩ := thetaHol_zero_poly_small d hd chi hchi hU h0
  obtain ⟨B2, hB2nn, hB2⟩ :=
    thetaHol_bound_of_summable chi 0 hapos (summable_thetaSummand hapos chi 0 hb)
  obtain ⟨M, hM0, hM⟩ :=
    mellin_strip_bound_two_piece_aux (f := thetaHol chi 0) (a := a) (q := 2) (B1 := B1) (B2 := B2)
      hapos ha1 (by norm_num) hB1nn hB2nn
      (fun u hu hua => by rw [ha] at hua; rw [Real.rpow_two]; exact hB1 u hu hua)
      (fun u hua => by rw [ha] at hua; exact hB2 u hua)
  exact ⟨M, hM0, hM⟩

end

end Work.FIArea6Hecke.R
