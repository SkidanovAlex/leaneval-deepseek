import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4
import Submission.Commons.NumberTheory.DirichletCharacter.estermann_positivity
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.S16Hecke.hecke_prod_coeff_nonneg
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.estermann_defs
import Submission.Work.FIArea6Hecke.R.estermann_conv_facts
import Submission.Work.FIArea6Hecke.R.estermannF_analyticOnNhd
import Submission.Commons.NumberTheory.Zeta.riemannZeta_bound_sphere_two

namespace Work.FIArea6Hecke.R

open scoped BigOperators

lemma estermannF_ball_bound_aux {d₁ d₂ : ℕ} {Lam₁ Lam₂ F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbnd₁ : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s‖ ≤ C * (d₁ : ℝ) ^ (10 : ℕ))
    (hbnd₂ : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s‖ ≤ C * (d₂ : ℝ) ^ (10 : ℕ))
    (hbndF : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖F s‖ ≤ C * ((d₁ * d₂ : ℕ) : ℝ) ^ (10 : ℕ))
    (hL4 : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s‖ ≤ C)
    (h2s : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖1 - (2 : ℂ) ^ (-s)‖ ≤ C) :
    ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖estermannF d₁ d₂ Lam₁ Lam₂ F s‖ ≤ C ^ (5 : ℕ) * (((d₁ * d₂ : ℕ) : ℝ) ^ (20 : ℕ)) := by
  intro s hs
  have h1 := hbnd₁ s hs
  have h2 := hbnd₂ s hs
  have h3 := hbndF s hs
  have h4 := hL4 s hs
  have h5 := h2s s hs
  unfold estermannF
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hnorm1 : (0:ℝ) ≤ ‖(1:ℂ) - 2 ^ (-s)‖ := norm_nonneg _
  have hnorm2 : (0:ℝ) ≤ ‖DirichletCharacter.LFunction chi4C s‖ := norm_nonneg _
  have hnorm3 : (0:ℝ) ≤ ‖Lval d₁ 0 Lam₁ s‖ := norm_nonneg _
  have hnorm4 : (0:ℝ) ≤ ‖Lval d₂ 0 Lam₂ s‖ := norm_nonneg _
  have hnorm5 : (0:ℝ) ≤ ‖F s‖ := norm_nonneg _
  have hCp : (0:ℝ) ≤ C := hC
  calc ‖(1:ℂ) - 2 ^ (-s)‖ * ‖DirichletCharacter.LFunction chi4C s‖ *
        ‖Lval d₁ 0 Lam₁ s‖ * ‖Lval d₂ 0 Lam₂ s‖ * ‖F s‖
      ≤ C * C * (C * (d₁:ℝ)^10) * (C * (d₂:ℝ)^10) * (C * (((d₁ * d₂ : ℕ) : ℝ) ^ 10)) := by
        have hp1 : (0:ℝ) ≤ (d₁:ℝ)^10 := by positivity
        have hp2 : (0:ℝ) ≤ (d₂:ℝ)^10 := by positivity
        have hp3 : (0:ℝ) ≤ (((d₁ * d₂ : ℕ) : ℝ))^10 := by positivity
        have hC1 : 0 ≤ C := hC
        have hCC : (0:ℝ) ≤ C * C := by positivity
        have hCC1 : (0:ℝ) ≤ C * C * (C * (d₁:ℝ)^10) := by positivity
        have hCC2 : (0:ℝ) ≤ C * C * (C * (d₁:ℝ)^10) * (C * (d₂:ℝ)^10) := by positivity
        exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h5 h4 hnorm2 hC1) h1 hnorm3 hCC)
          h2 hnorm4 hCC1) h3 hnorm5 hCC2
    _ = C ^ 5 * (((d₁*d₂:ℕ):ℝ) ^ 20) := by
        push_cast
        ring

lemma estermann_scaled_arith_aux {C β₁ K A x D m : ℝ}
    (hC : 1 ≤ C) (hβ₁lo : 19 / 20 ≤ β₁) (hβ₁hi : β₁ < 1)
    (hK : 1 ≤ K) (hA : 0 ≤ A) (hx : 0 ≤ x) (hD : 1 ≤ D) (hm : 1 ≤ m) (hDm : D ≤ m ^ 2)
    (hmain : (1 / 4) * (1 - β₁) * (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) ≤ A * K * x) :
    (1 / 4) * C ^ (-(15 : ℝ)) / (A + 1) * (1 - β₁) * K ^ (-(200 : ℝ)) * m ^ (-(200 * (1 - β₁))) ≤ x := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have ht0 : 0 ≤ 1 - β₁ := by linarith
  have ht1 : 1 - β₁ ≤ 1 := by linarith
  have hMpos : 0 < C ^ 5 * D ^ 20 := by positivity
  have hTpos : 0 < (1 / 4) * (1 - β₁) * (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) := by
    have h2 : 0 < (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) := Real.rpow_pos_of_pos hMpos _
    positivity
  have hAKx : 0 < A * K * x := lt_of_lt_of_le hTpos hmain
  have hApos : 0 < A := pos_of_mul_pos_left (pos_of_mul_pos_left hAKx hx) hKpos.le
  have hAKpos : 0 < A * K := mul_pos hApos hKpos
  have hxge : (1 / 4) * (1 - β₁) * (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) / (A * K) ≤ x := by
    rw [div_le_iff₀ hAKpos]
    exact hmain.trans (le_of_eq (mul_comm (A * K) x))
  refine le_trans ?_ hxge
  rw [le_div_iff₀ hAKpos]
  have hstepA : (1 / 4) * C ^ (-(15 : ℝ)) / (A + 1) * A ≤ (1 / 4) * C ^ (-(15 : ℝ)) := by
    have hAd : A / (A + 1) ≤ 1 :=
      (div_le_one (by linarith : (0:ℝ) < A + 1)).mpr (by linarith)
    have hfac : (0:ℝ) ≤ (1 / 4) * C ^ (-(15 : ℝ)) := by
      have := Real.rpow_pos_of_pos hCpos (-(15:ℝ))
      positivity
    calc (1 / 4) * C ^ (-(15 : ℝ)) / (A + 1) * A
        = (1 / 4) * C ^ (-(15 : ℝ)) * (A / (A + 1)) := by ring
      _ ≤ (1 / 4) * C ^ (-(15 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hAd hfac
      _ = (1 / 4) * C ^ (-(15 : ℝ)) := by ring
  have hstepB : K ^ (-(200 : ℝ)) * K ≤ 1 := by
    rw [show K ^ (-(200:ℝ)) * K = K ^ (-(200:ℝ)) * K ^ (1:ℝ) by rw [Real.rpow_one],
        ← Real.rpow_add hKpos]
    rw [show -(200:ℝ) + 1 = -(199:ℝ) by norm_num]
    exact Real.rpow_le_one_of_one_le_of_nonpos hK (by norm_num)
  have hCexp : C ^ (-(15 : ℝ)) ≤ C ^ (-(15 * (1 - β₁))) :=
    Real.rpow_le_rpow_of_exponent_le hC (by nlinarith)
  have hmexp : m ^ (-(200 * (1 - β₁))) ≤ m ^ (-(120 * (1 - β₁))) :=
    Real.rpow_le_rpow_of_exponent_le hm (by nlinarith)
  have hDexp : m ^ (-(120 * (1 - β₁))) ≤ D ^ (-(60 * (1 - β₁))) := by
    have h1 : (m^2) ^ (-(60 * (1 - β₁))) ≤ D ^ (-(60 * (1 - β₁))) :=
      Real.rpow_le_rpow_of_nonpos hDpos hDm (by nlinarith)
    have h2 : (m^2) ^ (-(60 * (1 - β₁))) = m ^ (-(120 * (1 - β₁))) := by
      rw [← Real.rpow_natCast m 2, ← Real.rpow_mul hmpos.le]
      congr 1; ring
    rwa [h2] at h1
  have hMeq : C ^ (-(15 * (1 - β₁))) * D ^ (-(60 * (1 - β₁)))
      = (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast C 5, ← Real.rpow_natCast D 20,
        ← Real.rpow_mul hCpos.le, ← Real.rpow_mul hDpos.le]
    congr 1 <;> ring
  have hkey : C ^ (-(15:ℝ)) * m ^ (-(200 * (1 - β₁))) ≤ (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) := by
    calc C ^ (-(15:ℝ)) * m ^ (-(200 * (1 - β₁)))
        ≤ C ^ (-(15 * (1 - β₁))) * D ^ (-(60 * (1 - β₁))) :=
          mul_le_mul hCexp (le_trans hmexp hDexp)
            (Real.rpow_nonneg hmpos.le _) (Real.rpow_nonneg hCpos.le _)
      _ = (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) := hMeq
  have hfinal : (1 / 4) * C ^ (-(15:ℝ)) * (1 - β₁) * m ^ (-(200 * (1 - β₁)))
      ≤ (1 / 4) * (1 - β₁) * (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) := by
    have h14 : (0:ℝ) ≤ (1 / 4) * (1 - β₁) := by linarith
    calc (1 / 4) * C ^ (-(15:ℝ)) * (1 - β₁) * m ^ (-(200 * (1 - β₁)))
        = ((1 / 4) * (1 - β₁)) * (C ^ (-(15:ℝ)) * m ^ (-(200 * (1 - β₁)))) := by ring
      _ ≤ ((1 / 4) * (1 - β₁)) * (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) :=
          mul_le_mul_of_nonneg_left hkey h14
      _ = (1 / 4) * (1 - β₁) * (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) := by ring
  calc ((1 / 4) * C ^ (-(15 : ℝ)) / (A + 1) * (1 - β₁) * K ^ (-(200 : ℝ)) *
          m ^ (-(200 * (1 - β₁)))) * (A * K)
      = ((1 / 4) * C ^ (-(15 : ℝ)) / (A + 1) * A) * ((1 - β₁) * (K ^ (-(200 : ℝ)) * K)) *
          m ^ (-(200 * (1 - β₁))) := by ring
    _ ≤ ((1 / 4) * C ^ (-(15 : ℝ))) * ((1 - β₁) * 1) * m ^ (-(200 * (1 - β₁))) := by
        have h15 : (0:ℝ) ≤ (1 / 4) * C ^ (-(15 : ℝ)) := by
          have := Real.rpow_pos_of_pos hCpos (-(15:ℝ))
          positivity
        have hmm : (0:ℝ) ≤ m ^ (-(200 * (1 - β₁))) := Real.rpow_nonneg hmpos.le _
        have hb2 : (0:ℝ) ≤ (1 - β₁) * (K ^ (-(200 : ℝ)) * K) := by positivity
        exact mul_le_mul (mul_le_mul hstepA (mul_le_mul_of_nonneg_left hstepB ht0) hb2 h15)
          (le_refl _) hmm (by positivity)
    _ = (1 / 4) * C ^ (-(15 : ℝ)) * (1 - β₁) * m ^ (-(200 * (1 - β₁))) := by ring
    _ ≤ (1 / 4) * (1 - β₁) * (C ^ 5 * D ^ 20) ^ (-(3 * (1 - β₁))) := hfinal




/-- **The Goldfeld/Estermann step of *FI* Lemma 16.1, with the modulus exponent proportional to
`1-β₁`.**  This is the shape the final `d^{-ε}` form needs: the exceptional zero satisfies
`1-β₁ < ε₁` for the case-2 threshold `ε₁` of the caller, hence
`(max d₁ d₂)^{-(200·(1-β₁))} ≥ (max d₁ d₂)^{-200ε₁}`, an exponent of size `ε₁` which is then
absorbed by rescaling `ε₁` against the target's `ε`.  An exponent that is a FIXED power of `d`
(e.g. `-200`) would NOT suffice, since a fixed power is much smaller than `d^{-ε}` for `ε < 200`.
(The exponent `200(1-β₁)` is conservative: the argument yields `120(1-β₁)`.)

The exceptional datum `(d₁,χ₁,Lam₁,β₁)` and the bound `C` are FIXED before the `∃ c`; the variable
data `(d₂,χ₂,Lam₂,F)` and the value bound `K` come after it, and the conclusion involves them only
through `K^{-200}` and `(max d₁ d₂)^{-(200(1-β₁))}`, so `c` is uniform in `d₂`.

`f(s) := (1-2^{-s})·L(χ₄,s)·(Lam₁/heckeArch d₁)(s)·(Lam₂/heckeArch d₂)(s)·F(s)` is entire; with
`a` from `hecke_prod_coeff_nonneg chi₁ chi₂` and `hζK`, one gets `ζ(s)f(s) = Σ a_n n^{-s}` on
`re s > 1` with `a_1 = 1`, `a_n ≥ 0`, so Estermann's positivity at `σ = β₁` (where `f(β₁) = 0`)
gives `(1/4)(1-β₁)M^{-3(1-β₁)} ≤ Re f(1)`, whence

  `‖Lval d₂ 0 Lam₂ 1‖ ≥ (1/4)(1-β₁)M^{-3(1-β₁)}/(|L(χ₄,1)|·‖Lval d₁ 0 Lam₁ 1‖·K)`,

and `M ≤ C⁵(d₁d₂)^{20}` (from `hbnd₁,hbnd₂,hbndF,hL4,h2s`) gives
`M^{-3(1-β₁)} ≥ C^{-15}(max d₁ d₂)^{-120(1-β₁)}`, an exponent proportional to `1-β₁` as required.
Degenerate cases (`Lval d₁ 0 Lam₁ 1 = 0`, `F 1 = 0`) force `f(1) = 0`, contradicting the positivity
bound, from which the conclusion follows. -/
theorem estermann_L_one_lower_scaled
    {d₁ : ℕ} (h₁ : 1 ≤ d₁) {chi₁ : GaussianInt → ℂ}
    (h1₁ : chi₁ 1 = 1)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z * w) = chi₁ z * chi₁ w)
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1)
    {Lam₁ : ℂ → ℂ} (hAn₁ : AnalyticOn ℂ Lam₁ Set.univ)
    (hAgr₁ : ∀ s : ℂ, 1 < s.re →
      Lam₁ s = Work.FITop4.Bridge.heckeArch d₁ 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s)
    (hζK : ∀ s : ℂ, 1 < s.re →
      Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1 : ℂ)) 0 s
        = riemannZeta s * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s
            * (1 - (2 : ℂ) ^ (-s)))
    {β₁ : ℝ} (hβ₁lo : 19 / 20 ≤ β₁) (hβ₁hi : β₁ < 1) (hzero : Lam₁ (β₁ : ℂ) = 0)
    {C : ℝ} (hC : 1 ≤ C)
    (hbnd₁ : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s‖ ≤ C * (d₁ : ℝ) ^ (10 : ℕ))
    (hL4 : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s‖ ≤ C)
    (h2s : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
      ‖1 - (2 : ℂ) ^ (-s)‖ ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d₂ : ℕ), 1 ≤ d₂ → ∀ (chi₂ : GaussianInt → ℂ),
        (chi₂ 1 = 1) →
        (∀ z : GaussianInt, chi₂ z = star (chi₂ z)) →
        (∀ z w : GaussianInt, chi₂ (z * w) = chi₂ z * chi₂ w) →
        (∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1) →
        ∀ (Lam₂ : ℂ → ℂ), AnalyticOn ℂ Lam₂ Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam₂ s = Work.FITop4.Bridge.heckeArch d₂ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s) →
        ∀ (F : ℂ → ℂ), AnalyticOn ℂ F Set.univ →
        (∀ s : ℂ, 1 < s.re →
          F s = Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s) →
        ∀ (K : ℝ), 1 ≤ K → ‖F 1‖ ≤ K →
        (∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
          ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s‖ ≤ C * (d₂ : ℝ) ^ (10 : ℕ)) →
        (∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
          ‖F s‖ ≤ C * ((d₁ * d₂ : ℕ) : ℝ) ^ (10 : ℕ)) →
        c * (1 - β₁) * K ^ (-(200 : ℝ))
            * (max (d₁ : ℝ) (d₂ : ℝ)) ^ (-(200 * (1 - β₁)))
          ≤ ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by
  classical
  set A : ℝ := (1 / 2) * ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C 1‖ *
      ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1‖ with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hcpos : 0 < (1 / 4) * C ^ (-(15 : ℝ)) / (A + 1) := by
    have h1 : 0 < C ^ (-(15 : ℝ)) := Real.rpow_pos_of_pos hCpos _
    have h2 : 0 < A + 1 := by linarith
    positivity
  refine ⟨(1 / 4) * C ^ (-(15 : ℝ)) / (A + 1), hcpos, ?_⟩
  intro d₂ h₂ chi₂ h1₂ hre₂ hmul₂ hb₂ Lam₂ hAn₂ hAgr₂ F hFan hFagr K hK hF1 hbnd₂ hbndF
  obtain ⟨Kz, hKzpos, hKzbd⟩ := Commons.NumberTheory.Zeta.riemannZeta_bound_sphere_two
  obtain ⟨hc1, hcnonneg, hcabs, hcid⟩ :=
    estermann_conv_facts h1₁ h1₂ hre₁ hre₂ hmul₁ hmul₂ hb₁ hb₂
  have hFser : ∀ s : ℂ, 1 < s.re →
      riemannZeta s * estermannF d₁ d₂ Lam₁ Lam₂ F s
        = ∑' n : ℕ, (((Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
    intro s hs
    have hs0 : 0 < s.re := by linarith
    have harch₁ : Work.FITop4.Bridge.heckeArch d₁ 0 s ≠ 0 := (heckeArch_facts h₁).1 s hs0
    have hL₁ : Work.FIArea6Hecke.Lval d₁ 0 Lam₁ s
        = Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s := by
      rw [Work.FIArea6Hecke.Lval, hAgr₁ s hs]
      exact mul_div_cancel_left₀ _ harch₁
    have harch₂ : Work.FITop4.Bridge.heckeArch d₂ 0 s ≠ 0 := (heckeArch_facts h₂).1 s hs0
    have hL₂ : Work.FIArea6Hecke.Lval d₂ 0 Lam₂ s
        = Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s := by
      rw [Work.FIArea6Hecke.Lval, hAgr₂ s hs]
      exact mul_div_cancel_left₀ _ harch₂
    have hkey : riemannZeta s *
          ((1 - (2:ℂ) ^ (-s)) * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s)
        = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1:ℂ)) 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s := by
      calc riemannZeta s *
            ((1 - (2:ℂ) ^ (-s)) * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s)
          = (riemannZeta s * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s *
              (1 - (2:ℂ) ^ (-s))) *
            (Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s) := by ring
        _ = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1:ℂ)) 0 s *
            (Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s) := by
              rw [← hζK s hs]
        _ = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1:ℂ)) 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s := by ring
    calc riemannZeta s * estermannF d₁ d₂ Lam₁ Lam₂ F s
        = riemannZeta s *
            ((1 - (2:ℂ) ^ (-s)) * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s) := by
          simp only [estermannF]
          rw [hL₁, hL₂, hFagr s hs]
      _ = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1:ℂ)) 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s := hkey
      _ = ∑' n : ℕ, (((Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re : ℝ) : ℂ) * (n : ℂ) ^ (-s) :=
          (hcid s hs).symm
  have hfa := estermannF_analyticOnNhd h₁ h₂ hAn₁ hAn₂ hFan
  have hfnb := estermannF_ball_bound_aux (le_trans zero_le_one hC) hbnd₁ hbnd₂ hbndF hL4 h2s
  have hD1 : (1:ℝ) ≤ ((d₁ * d₂ : ℕ) : ℝ) := by
    have h12 : (1:ℕ) ≤ d₁ * d₂ := by
      have := Nat.mul_le_mul h₁ h₂
      simpa using this
    exact_mod_cast h12
  have h5p : (1:ℝ) ≤ C ^ 5 := one_le_pow₀ hC
  have h20p : (1:ℝ) ≤ (((d₁ * d₂ : ℕ) : ℝ)) ^ (20:ℕ) := one_le_pow₀ hD1
  have hM1 : (1:ℝ) ≤ C ^ 5 * (((d₁ * d₂ : ℕ) : ℝ)) ^ (20:ℕ) := by
    simpa using (mul_le_mul h5p h20p (zero_le_one) (le_trans zero_le_one h5p))
  have hzetaσ : ∃ c : ℝ, c < 0 ∧ riemannZeta (β₁ : ℂ) = (c : ℂ) :=
    Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one (by linarith) hβ₁hi
  have hfσ : (0:ℝ) ≤ (estermannF d₁ d₂ Lam₁ Lam₂ F (β₁ : ℂ)).re := by
    have hz : estermannF d₁ d₂ Lam₁ Lam₂ F (β₁ : ℂ) = 0 := by
      simp [estermannF, Work.FIArea6Hecke.Lval, hzero]
    rw [hz]; simp
  have hr0 : ∀ n : ℕ, 0 ≤ (Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : Work.FIArea5.S16Hecke.Conv chi₁ chi₂ 0 = 0 := by
        simp [Work.FIArea5.S16Hecke.Conv, LSeries.convolution_def]
      rw [h0]; simp
    · exact hcnonneg n hn
  have hc1r : (Work.FIArea5.S16Hecke.Conv chi₁ chi₂ 1).re = 1 := by rw [hc1]; simp
  have hpos := Commons.NumberTheory.DirichletCharacter.estermann_positivity
    (f := estermannF d₁ d₂ Lam₁ Lam₂ F)
    (r := fun n => (Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re)
    (M := C ^ 5 * (((d₁ * d₂ : ℕ) : ℝ)) ^ (20:ℕ)) (σ := β₁) (K := Kz)
    hKzpos hM1 hβ₁lo hβ₁hi hfa hfnb (fun z hz => hKzbd z hz) hzetaσ hr0 hc1r hcabs hFser hfσ
  have h1val : ‖(1:ℂ) - (2:ℂ) ^ (-(1:ℂ))‖ = 1/2 := by
    rw [show (-(1:ℂ)) = ((-1:ℤ):ℂ) by simp, Complex.cpow_intCast]
    norm_num
  have hnorm1 : ‖estermannF d₁ d₂ Lam₁ Lam₂ F 1‖
      = A * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * ‖F 1‖ := by
    rw [hAdef]
    show ‖(1 - (2:ℂ) ^ (-(1:ℂ))) * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C 1 *
        Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1 * Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1 * F 1‖
      = 1 / 2 * ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C 1‖ *
        ‖Work.FIArea6Hecke.Lval d₁ 0 Lam₁ 1‖ * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * ‖F 1‖
    simp only [norm_mul, h1val]
  have hf1le : (estermannF d₁ d₂ Lam₁ Lam₂ F 1).re
      ≤ A * K * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by
    have hstep1 : (estermannF d₁ d₂ Lam₁ Lam₂ F 1).re
        ≤ ‖estermannF d₁ d₂ Lam₁ Lam₂ F 1‖ := Complex.re_le_norm _
    rw [hnorm1] at hstep1
    refine le_trans hstep1 ?_
    have hx0 : (0:ℝ) ≤ ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := norm_nonneg _
    have hAA : (0:ℝ) ≤ A * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by positivity
    calc A * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * ‖F 1‖
        ≤ A * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ * K := mul_le_mul_of_nonneg_left hF1 hAA
      _ = A * K * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := by ring
  have hmain : (1 / 4) * (1 - β₁) * (C ^ 5 * (((d₁ * d₂ : ℕ) : ℝ)) ^ (20:ℕ)) ^ (-(3 * (1 - β₁)))
      ≤ A * K * ‖Work.FIArea6Hecke.Lval d₂ 0 Lam₂ 1‖ := le_trans hpos hf1le
  have hm1 : (1:ℝ) ≤ max (d₁ : ℝ) (d₂ : ℝ) :=
    le_trans (by exact_mod_cast h₂) (le_max_right _ _)
  have hDm : (((d₁ * d₂ : ℕ) : ℝ)) ≤ (max (d₁ : ℝ) (d₂ : ℝ)) ^ 2 := by
    have hle1 : (d₁:ℝ) ≤ max (d₁:ℝ) (d₂:ℝ) := le_max_left _ _
    have hle2 : (d₂:ℝ) ≤ max (d₁:ℝ) (d₂:ℝ) := le_max_right _ _
    have h1' : (0:ℝ) ≤ (d₁:ℝ) := by positivity
    have h2' : (0:ℝ) ≤ (d₂:ℝ) := by positivity
    have hm0 : (0:ℝ) ≤ max (d₁:ℝ) (d₂:ℝ) := le_trans h1' hle1
    calc (((d₁ * d₂ : ℕ) : ℝ)) = (d₁:ℝ) * (d₂:ℝ) := by push_cast; ring
      _ ≤ max (d₁:ℝ) (d₂:ℝ) * max (d₁:ℝ) (d₂:ℝ) := mul_le_mul hle1 hle2 h2' hm0
      _ = (max (d₁ : ℝ) (d₂ : ℝ)) ^ 2 := by ring
  exact estermann_scaled_arith_aux hC hβ₁lo hβ₁hi hK hA0 (norm_nonneg _) hD1 hm1 hDm hmain



end Work.FIArea6Hecke.R
