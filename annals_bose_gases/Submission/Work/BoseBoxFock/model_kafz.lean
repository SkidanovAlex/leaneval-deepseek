import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.Kafz_lower_bound_moments
import Submission.Work.BoseBoxFock.envFacts_uniform
import Submission.Work.BoseBoxFock.errKafz_dominates_uniform
import Submission.Work.BoseBoxFock.honestEnvBessel
import Submission.Work.BoseBoxFock.symC_floor_honest2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {m : ℕ} [NeZero m]

/-! ## 0. The scaling of the error `errKafz` in its constant

`errKafz v R μ C = C · (positive monomials)` is *linear* in `C`; the assembly uses this
to trade the `√(48/π)`-factor of the `χ̂²`(`g`)-row (which the honest Bessel row forces)
for a factor `4` in the error constant. -/
lemma errKafz_mul_four (v : ℝ³ → ℝ) {R μ C : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    Work.BoseFixR.errKafz v R μ (4 * C) = 4 * Work.BoseFixR.errKafz v R μ C := by
  have h1 := Work.BoseFixR.errKafz_eq_errAbs (v := v) (μ := μ) (R := R) (C := 4 * C) hμ hav
  have h2 := Work.BoseFixR.errKafz_eq_errAbs (v := v) (μ := μ) (R := R) (C := C) hμ hav
  rw [h1, h2]
  simp only [Work.BoseFixR.errAbs]
  ring

theorem model_kafz (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ HM : ∀ μ : ℝ, HonestModes v μ, ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ), (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        ∀ Ψ : Work.BoseB4.RealFock (HM μ).m, Ψ ≠ 0 →
          ExcWindow (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
            (BoseGases.a v) μ) n Ψ →
          ((⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFS ρ.1)
              - Work.BoseFixR.errKafz v R μ C) * Work.BoseB4.bomb (HM μ).m Ψ Ψ
            ≤ Work.BoseB4.bomb (HM μ).m Ψ (H2ndHon v h fc fu HM μ Ψ) := by
  classical
  obtain ⟨ε₀, C₀, hε₀, hC₀, hEnv⟩ := envFacts_uniform v h hv hv1 hvrad hR hv_supp hav fc fu
  obtain ⟨C₁, hC₁, hArith⟩ :=
    errKafz_dominates_uniform v h hv hv1 hvrad hR hv_supp hav fc fu ε₀ C₀ hε₀ hC₀ hEnv
  refine ⟨ε₀, 4 * C₁, hε₀, by positivity, ?_⟩
  intro HM μ hAdm n hn Ψ hΨ hWin
  have hμ : 0 < μ := hAdm.1
  have hav0 : (0 : ℝ) ≤ BoseGases.a v := le_of_lt hav
  obtain ⟨henvEll0, henvEll, henvMu, henvBox, henvLin, henvMle, henvW1, henvW1ω, henvWω0,
    henvWω0le, henvOm0, henvC, henvP1, henvP2, henvP3, henvP4⟩ := hEnv HM μ hAdm
  have hn' : (n : ℝ) ≤ 2 * μ * (HonestBoxFam v h fc fu HM μ).E.ell ^ 3 := by
    rw [henvEll]; exact hn
  obtain ⟨hbigM0, h48M0, hB20, hB1s0, hAr5⟩ := hArith HM μ hAdm n hn'
  obtain ⟨hχ21, hχ2b48, hBes48⟩ := honestEnvBesselCorrected v h fc fu HM μ
  -- ## the pointwise floor (FS `thm:Kafz` at the honest model)
  have hfloor := symC_floor_honest2 v h hv hvrad hR hv_supp hav fc fu HM μ C₀
    (C₀ * BoseGases.a v) hμ hC₀ (mul_nonneg hC₀ hav0) hbigM0 (hEnv HM μ hAdm)
    henvW1ω hχ2b48 hχ21 hBes48 n hn' Ψ hWin
  -- ## the two Gaussian moments
  obtain ⟨hm2, hm1⟩ := gauss_moments_le Ψ n hWin.2
  rw [Work.BoseB4.bomb_self_eq_norm_split Ψ] at hm2 hm1
  -- ## the arithmetic
  have hS : Real.sqrt (48 / Real.pi) ≤ 4 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hroot : (0 : ℝ) ≤ (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ)) :=
    Real.rpow_nonneg henvEll0.le _
  have hB1 : 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
        * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
            * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
          + (HonestBoxFam v h fc fu HM μ).E.W1omega0
            * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)))
      ≤ 4 * (4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
        * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
            * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
          + (HonestBoxFam v h fc fu HM μ).E.W1omega0
            * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM))) := by
    have hA : |(HonestBoxFam v h fc fu HM μ).E.W1 0|
          * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
        ≤ 4 * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
          * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))) := by
      nlinarith [abs_nonneg ((HonestBoxFam v h fc fu HM μ).E.W1 0),
        Real.sqrt_nonneg ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)),
        mul_nonneg (abs_nonneg ((HonestBoxFam v h fc fu HM μ).E.W1 0))
          (Real.sqrt_nonneg ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)))]
    have hB0' : (HonestBoxFam v h fc fu HM μ).E.W1omega0
          * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
        ≤ 4 * ((HonestBoxFam v h fc fu HM μ).E.W1omega0
          * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM)) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 48 / Real.pi)
        ((HonestBoxFam v h fc fu HM μ).E.bigM)]
      have h1 : Real.sqrt (48 / Real.pi)
            * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM)
          ≤ 4 * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM) :=
        mul_le_mul_of_nonneg_right hS
          (Real.sqrt_nonneg ((HonestBoxFam v h fc fu HM μ).E.bigM))
      calc (HonestBoxFam v h fc fu HM μ).E.W1omega0
            * (Real.sqrt (48 / Real.pi)
              * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM))
          ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega0
            * (4 * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM)) := mul_le_mul_of_nonneg_left h1 henvWω0
        _ = 4 * ((HonestBoxFam v h fc fu HM μ).E.W1omega0
            * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM)) := by ring
    have hsum : |(HonestBoxFam v h fc fu HM μ).E.W1 0|
          * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
        + (HonestBoxFam v h fc fu HM μ).E.W1omega0
          * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
        ≤ 4 * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
            * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
          + (HonestBoxFam v h fc fu HM μ).E.W1omega0
            * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM)) := by
      calc |(HonestBoxFam v h fc fu HM μ).E.W1 0|
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
            + (HonestBoxFam v h fc fu HM μ).E.W1omega0
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
          ≤ 4 * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)))
            + 4 * ((HonestBoxFam v h fc fu HM μ).E.W1omega0
              * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM)) :=
            add_le_add hA hB0'
        _ = 4 * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
            + (HonestBoxFam v h fc fu HM μ).E.W1omega0
              * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM)) := by ring
    have hmul := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hroot)
    calc 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
          * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
            + (HonestBoxFam v h fc fu HM μ).E.W1omega0
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)))
        ≤ 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
          * (4 * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
            + (HonestBoxFam v h fc fu HM μ).E.W1omega0
              * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM))) := hmul
      _ = 4 * (4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
          * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
            + (HonestBoxFam v h fc fu HM μ).E.W1omega0
              * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM))) := by ring
  have hB00 : (0 : ℝ) ≤ |2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
        + μ * (8 * Real.pi * BoseGases.a v)|
      + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
        * (2 * C₀ * BoseGases.a v
            + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
        * ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)) := by
    have h2c : (0 : ℝ) ≤ 2 * C₀ * BoseGases.a v
        + |(HonestBoxFam v h fc fu HM μ).E.W1 0
            + (HonestBoxFam v h fc fu HM μ).E.W1omega0| := by
      nlinarith [abs_nonneg ((HonestBoxFam v h fc fu HM μ).E.W1 0
          + (HonestBoxFam v h fc fu HM μ).E.W1omega0),
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hC₀ hav0)]
    have h2 : (0 : ℝ) ≤ (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
        * (2 * C₀ * BoseGases.a v
            + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
        * ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)) :=
      mul_nonneg (mul_nonneg hroot h2c) (by positivity)
    linarith [abs_nonneg (2 * cHCF (HonestBoxFam v h fc fu HM μ).E
      (8 * Real.pi * BoseGases.a v) + μ * (8 * Real.pi * BoseGases.a v)), h2]
  have hb1pos : (0 : ℝ) ≤ 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
        * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
            * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
          + (HonestBoxFam v h fc fu HM μ).E.W1omega0
            * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))) := by
    have h2c : (0 : ℝ) ≤ |(HonestBoxFam v h fc fu HM μ).E.W1 0|
          * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
        + (HonestBoxFam v h fc fu HM μ).E.W1omega0
          * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)) :=
      add_nonneg
        (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
        (mul_nonneg henvWω0 (Real.sqrt_nonneg _))
    exact mul_nonneg (by positivity) h2c
  have herr : 4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
        * ((n : ℝ) + 1)
      + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
          * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
            + (HonestBoxFam v h fc fu HM μ).E.W1omega0
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)))
          * Real.sqrt ((n : ℝ) + 1)
      + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
              + μ * (8 * Real.pi * BoseGases.a v)|
          + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
            * (2 * C₀ * BoseGases.a v
                + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                    + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
            * ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)))
      ≤ Work.BoseFixR.errKafz v R μ (4 * C₁) := by
    rw [errKafz_mul_four v hμ hav]
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hsqn : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
    have hm1' : 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
          * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
            + (HonestBoxFam v h fc fu HM μ).E.W1omega0
              * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)))
          * Real.sqrt ((n : ℝ) + 1)
        ≤ (4 * (4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
            * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
              + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                * Real.sqrt ((HonestBoxFam v h fc fu HM μ).E.bigM))))
          * Real.sqrt ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hB1 hsqn
    have h2 : 4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
          * ((n : ℝ) + 1)
        ≤ 4 * (4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
          * ((n : ℝ) + 1)) := by
      nlinarith [hB20, hn1, mul_nonneg hB20 hn1]
    have h4 : |2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
            + μ * (8 * Real.pi * BoseGases.a v)|
          + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
            * (2 * C₀ * BoseGases.a v
                + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                    + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
            * ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
        ≤ 4 * (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
              + μ * (8 * Real.pi * BoseGases.a v)|
            + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (2 * C₀ * BoseGases.a v
                  + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                      + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
              * ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))) := by
      nlinarith [hB00]
    have hstep := hAr5
    linarith [hm1', h2, h4, hstep]
  -- ## the integrated bound
  have hmain := Kafz_lower_bound_moments (E := cfock (Excited (HM μ).m))
    (s := Finset.range 25) pvecF qvecF (KvecHon v h fc fu HM μ)
    ((⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}), (HonestBoxFam v h fc fu HM μ).valFS ρ.1))
    (4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v))
    (4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
      * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
          * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))
        + (HonestBoxFam v h fc fu HM μ).E.W1omega0
          * Real.sqrt ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM))))
    (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
        + μ * (8 * Real.pi * BoseGases.a v)|
      + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
        * (2 * C₀ * BoseGases.a v
            + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
        * ((48 / Real.pi) * ((HonestBoxFam v h fc fu HM μ).E.bigM)))
    ((n : ℝ) + 1) (Real.sqrt ((n : ℝ) + 1)) (Work.BoseFixR.errKafz v R μ (4 * C₁))
    hB20 hb1pos (split Ψ) hfloor hm2 hm1 herr
  rw [← Work.BoseB4.bomb_self_eq_norm_split Ψ] at hmain
  have hW := hW_H2ndHon v h fc fu HM μ Ψ
  rw [LinearMap.sum_apply] at hW
  rw [← hW] at hmain
  have hR : (inner ℂ (Work.BoseB4.Embed (cfock (Excited (HM μ).m)) (Work.BoseB4.split Ψ))
        (Work.BoseB4.Embed (cfock (Excited (HM μ).m))
          (Work.BoseB4.split (H2ndHon v h fc fu HM μ Ψ)))).re
      = Work.BoseB4.bomb (HM μ).m Ψ (H2ndHon v h fc fu HM μ Ψ) := by
    show (Work.BoseB4.coreInner (Work.BoseB4.split Ψ)
      (Work.BoseB4.split (H2ndHon v h fc fu HM μ Ψ))).re
        = Work.BoseB4.bomb (HM μ).m Ψ (H2ndHon v h fc fu HM μ Ψ)
    rw [Work.BoseB4.Split_inner (m := (HM μ).m) Ψ (H2ndHon v h fc fu HM μ Ψ)]
    simp
  rw [hR] at hmain
  exact hmain

end Work.BoseBoxFock
