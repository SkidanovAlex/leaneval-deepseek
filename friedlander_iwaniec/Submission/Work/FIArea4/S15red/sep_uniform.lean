import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.separation_ineq_nearCut
import Submission.Work.FIArea4.Vflip.separation_ineq
import Submission.Work.FIArea4.Vflip.sepG_decay
import Submission.Work.FIArea4.Vflip.sepG_mellin

/-!
# `sep_uniform`: the near-cut separation inequality for a general bump

This is the Friedlander–Iwaniec separation inequality (12.13)–(12.14) for an **arbitrary**
smooth `ψ` supported in `[1/2, 5/2]` (in particular the paper's majorant `bump`), uniform in
`a, b` up to the factor `(log (2 + b/a) + 1)^2`.  It is the general form of
`Work.FIArea4.Vflip.Vfd.separation_ineq_nearCut`, whose proof only ever uses the smoothness and
the support of the weight, so it goes through verbatim for `ψ`.
-/

open MeasureTheory
open scoped FourierTransform

namespace Work.FIArea4.S15red

open Work.FIArea4.Vflip Work.FIArea4.Vflip.Vfd

theorem sep_uniform {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψsup : ∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
      (ι : Type) [Fintype ι] (x y : ι → ℝ) (c : ι → ℂ) (M : ℝ),
      (∀ i, 0 < y i) →
      (∀ u t : ℝ, ‖∑ i, c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
            (y i : ℂ) ^ (Complex.I * t)‖ ≤ M) →
      ‖∑ i, c i * ((ψ (|x i| * y i) * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ)‖
        ≤ C * (Real.log (2 + b / a) + 1) ^ 2 * M := by
  classical
  obtain ⟨KG, hKGpos, hKGdec⟩ := sepG_decay hψ hψsup
  have hGmellin := sepG_mellin hψ hψsup
  have hIntG : Integrable (sepG ψ) :=
    integrable_sepG _ hψ hψsup
  obtain ⟨KC, hKCpos, hKCl1⟩ := chat_fourier_l1
  -- ## the majorant
  set Maj : ℝ → ℝ := fun t => (KC * (1 + |2 * Real.pi * t|) ^ 2) * ‖sepG ψ t‖
    with hMajdef
  have hMajint : Integrable Maj := by
    have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (-(2 : ℝ))) := by
      have h := integrable_one_add_norm (μ := volume) (E := ℝ) (r := 2)
        (by rw [Module.finrank_self]; norm_num)
      simpa [Real.norm_eq_abs] using h
    have hbdd : ∀ t : ℝ, Maj t ≤ (KG * KC * (1 + 2 * Real.pi) ^ 2) * (1 + |t|) ^ (-(2 : ℝ)) := by
      intro t
      have hpow : (1 + |2 * Real.pi * t|) ^ 2 ≤ (1 + 2 * Real.pi) ^ 2 * (1 + |t|) ^ 2 := by
        have h3 : |2 * Real.pi * t| = 2 * Real.pi * |t| := by
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos,
            abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have h2 : 1 + |2 * Real.pi * t| ≤ (1 + 2 * Real.pi) * (1 + |t|) := by
          rw [h3]; nlinarith [abs_nonneg t, Real.pi_pos]
        calc (1 + |2 * Real.pi * t|) ^ 2 ≤ ((1 + 2 * Real.pi) * (1 + |t|)) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h2 2
          _ = (1 + 2 * Real.pi) ^ 2 * (1 + |t|) ^ 2 := by ring
      have hrpow : (1 + |t|) ^ 2 * (1 + |t|) ^ (-(4 : ℝ)) = (1 + |t|) ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_natCast (1 + |t|) 2,
          ← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |t|)]
        norm_num
      rw [hMajdef]
      calc (KC * (1 + |2 * Real.pi * t|) ^ 2) * ‖sepG ψ t‖
          ≤ (KC * ((1 + 2 * Real.pi) ^ 2 * (1 + |t|) ^ 2)) *
              (KG * (1 + |t|) ^ (-(4 : ℝ))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hpow hKCpos.le) (hKGdec t) (norm_nonneg _)
              (by positivity)
        _ = (KG * KC * (1 + 2 * Real.pi) ^ 2) * (1 + |t|) ^ (-(2 : ℝ)) := by
            rw [show (KC * ((1 + 2 * Real.pi) ^ 2 * (1 + |t|) ^ 2)) *
                  (KG * (1 + |t|) ^ (-(4 : ℝ)))
                = (KC * (1 + 2 * Real.pi) ^ 2 * KG) *
                  ((1 + |t|) ^ 2 * (1 + |t|) ^ (-(4 : ℝ))) by ring]
            rw [hrpow]; ring
    refine Integrable.mono' (hbase.const_mul (KG * KC * (1 + 2 * Real.pi) ^ 2)) ?_ ?_
    · rw [hMajdef]
      exact ((by fun_prop : Continuous fun t : ℝ =>
        KC * (1 + |2 * Real.pi * t|) ^ 2)).aestronglyMeasurable.mul
          hIntG.aestronglyMeasurable.norm
    · filter_upwards with t
      rw [Real.norm_of_nonneg (by rw [hMajdef]; positivity)]
      exact hbdd t
  have hMajnn : ∀ t : ℝ, 0 ≤ Maj t := by intro t; rw [hMajdef]; positivity
  refine ⟨(∫ t : ℝ, Maj t) + 1, by positivity, ?_⟩
  intro a b ha hab ι _ x y c M hy hM
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 0)
  have hIntW : ∀ t : ℝ, Integrable (𝓕 (chat a b (2 * Real.pi * t))) :=
    fun t => integrable_fourier_chat a b (2 * Real.pi * t) ha hab
  -- ## the two explicit local functions
  set Tc : ι → ℝ → ℂ := fun i t => (Work.FIArea4.Vflip.nearCut a b (x i) : ℂ) *
      (((|x i| : ℝ) : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) *
      ((y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) with hTc
  set Sf : ℝ → ℝ → ℂ := fun u t => ∑ i, c i *
      Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
      (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) with hSf
  have hSfbd : ∀ u t : ℝ, ‖Sf u t‖ ≤ M := by
    intro u t
    rw [hSf]
    exact hM u (2 * Real.pi * t)
  -- ## 0. continuity of the local factor `Tc i`
  have hcontTc : ∀ i, Continuous (Tc i) := by
    intro i
    by_cases hi : x i = 0
    · have hnc : Work.FIArea4.Vflip.nearCut a b (x i) = 0 := by rw [hi]; exact nearCut_zero a b ha
      have hfun : Tc i = fun _ : ℝ => 0 := by
        funext t; rw [hTc]; simp only [hnc, Complex.ofReal_zero, zero_mul]
      rw [hfun]; exact continuous_const
    · rw [hTc]
      have hxi : 0 < |x i| := abs_pos.mpr hi
      have h1 : Continuous (fun t : ℝ =>
          ((|x i| : ℝ) : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) :=
        continuous_cpow_ofReal |x i| hxi
      have h2 : Continuous (fun t : ℝ =>
          (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) :=
        continuous_cpow_ofReal (y i) (hy i)
      exact (continuous_const.mul h1).mul h2
  -- ## 1. the per-index Mellin identity
  have hper : ∀ i, ((ψ (|x i| * y i)
        * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ) =
      ∫ t : ℝ, sepG ψ t * Tc i t := by
    intro i
    by_cases hi : x i = 0
    · have hnc : Work.FIArea4.Vflip.nearCut a b (x i) = 0 := by rw [hi]; exact nearCut_zero a b ha
      have hTc0 : Tc i = fun _ : ℝ => 0 := by
        funext t; rw [hTc]; simp only [hnc, Complex.ofReal_zero, zero_mul]
      simp [hnc, hTc0]
    · have hpos : 0 < |x i| * y i := mul_pos (abs_pos.mpr hi) (hy i)
      rw [Complex.ofReal_mul, hGmellin (|x i| * y i) hpos]
      rw [← MeasureTheory.integral_mul_const
        (((Work.FIArea4.Vflip.nearCut a b (x i) : ℝ)) : ℂ)
        (fun t : ℝ => sepG ψ t *
          Complex.exp (2 * Real.pi * Complex.I * (t * Real.log (|x i| * y i))))]
      apply integral_congr_ae
      filter_upwards with t
      rw [hTc]
      have h1 : Complex.exp (2 * Real.pi * Complex.I * (t * Real.log (|x i| * y i))) =
          ((|x i| * y i : ℝ) : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
        rw [cpow_ofReal_eq_exp (|x i| * y i) hpos (2 * Real.pi * t)]
        congr 1; push_cast; ring
      rw [h1, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (abs_nonneg (x i)) (hy i).le]
      ring
  -- ## 2. integrability of the summands of the outer integral
  have hIntTc : ∀ i, AEStronglyMeasurable (Tc i) := fun i => (hcontTc i).aestronglyMeasurable
  have hIntSummand : ∀ i, Integrable (fun t : ℝ =>
      c i * (sepG ψ t * Tc i t)) := by
    intro i
    have hb : Integrable (fun t : ℝ => sepG ψ t * Tc i t) :=
      Integrable.mul_of_norm_le hIntG 1 (fun t => by
        rw [hTc, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |Work.FIArea4.Vflip.nearCut a b (x i)| *
              ‖((|x i| : ℝ) : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))‖ *
                ‖(y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))‖
            ≤ 1 * 1 * 1 := by
              refine mul_le_mul (mul_le_mul ?_
                (norm_cpow_imag_nonneg |x i| (abs_nonneg _) _) (norm_nonneg _) (by norm_num))
                (norm_cpow_imag_nonneg (y i) (hy i).le _) (norm_nonneg _) (by norm_num)
              rw [abs_of_nonneg (Work.FIArea4.Vflip.nearCut_nonneg a b (x i))]
              exact Work.FIArea4.Vflip.nearCut_le_one a b (x i)
          _ = 1 := by norm_num) (hIntTc i)
    exact hb.const_mul (c i)
  -- ## 3. the outer identity
  have houter : (∑ i, c i * ((ψ (|x i| * y i)
        * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ)) =
      ∫ t : ℝ, sepG ψ t * (∑ i, c i * Tc i t) := by
    have h1 : (∑ i, c i * ((ψ (|x i| * y i)
          * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ)) =
        ∑ i, c i * ∫ t : ℝ, sepG ψ t * Tc i t :=
      Finset.sum_congr rfl (fun i _ => by rw [hper i])
    rw [h1]
    have h2 : (∑ i, c i * ∫ t : ℝ, sepG ψ t * Tc i t) =
        ∑ i, ∫ t : ℝ, c i * (sepG ψ t * Tc i t) :=
      Finset.sum_congr rfl (fun i _ => by rw [MeasureTheory.integral_const_mul])
    rw [h2, ← MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ => hIntSummand i)]
    apply integral_congr_ae
    filter_upwards with t
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- ## 4. the inner (chirp) expansion at fixed `t`
  have hinner : ∀ t : ℝ, (∑ i, c i * Tc i t) =
      ∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t := by
    intro t
    have hterm : ∀ i : ι, ∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u *
          (c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
            (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) = c i * Tc i t := by
      intro i
      have hA := (chat_fourier_inversion a b (2 * Real.pi * t) ha hab).2.2 (x i)
      have hre : (fun u : ℝ => 𝓕 (chat a b (2 * Real.pi * t)) u *
            (c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
              (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)))) =
          fun u : ℝ => (c i * (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) *
              (𝓕 (chat a b (2 * Real.pi * t)) u *
                Complex.exp (2 * Real.pi * Complex.I * (u * x i))) := by
        funext u; ring
      rw [hre, MeasureTheory.integral_const_mul, hA, hTc]
      simp only [chat]
      ring
    rw [hSf]
    have h1 : (fun u : ℝ => 𝓕 (chat a b (2 * Real.pi * t)) u *
          ((fun u t => ∑ i, c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
              (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) u t)) =
        fun u : ℝ => ∑ i, 𝓕 (chat a b (2 * Real.pi * t)) u *
            (c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
              (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ))) := by
      funext u
      simp only
      rw [Finset.mul_sum]
    rw [h1, MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ => (hterm i).symm)
    · intro i _
      refine Integrable.mul_of_norm_le (hIntW t) ‖c i‖ (fun u => ?_) ?_
      · have hnormexp :
            ‖Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (x i : ℂ)))‖ = 1 := by
          rw [show 2 * ↑Real.pi * Complex.I * ((u : ℂ) * (x i : ℂ))
              = ((2 * Real.pi * (u * x i) : ℝ) : ℂ) * Complex.I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        rw [norm_mul, norm_mul, hnormexp, norm_cpow_imag _ (hy i) _]
        simp
      · exact ((by fun_prop : Continuous fun u : ℝ =>
            c i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
              (y i : ℂ) ^ (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)))).aestronglyMeasurable
  -- ## 5. the bound
  have hEq : (∑ i, c i * ((ψ (|x i| * y i)
        * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ)) =
      ∫ t : ℝ, sepG ψ t *
        (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t) := by
    rw [houter]
    apply integral_congr_ae
    filter_upwards with t
    rw [hinner t]
  have hL1 : (1 : ℝ) ≤ Real.log (2 + b / a) + 1 := by
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have : (0 : ℝ) ≤ Real.log (2 + b / a) :=
      Real.log_nonneg (by have hd : 0 ≤ b / a := (div_pos hb ha).le; linarith)
    linarith
  have hbound : ‖∫ t : ℝ, sepG ψ t *
        (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t)‖
      ≤ M * (Real.log (2 + b / a) + 1) * ∫ t : ℝ, Maj t := by
    calc ‖∫ t : ℝ, sepG ψ t *
          (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t)‖
        ≤ ∫ t : ℝ, ‖sepG ψ t *
            (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, M * (Real.log (2 + b / a) + 1) * Maj t := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (hMajint.const_mul (M * (Real.log (2 + b / a) + 1)))
            (Filter.Eventually.of_forall fun t => ?_)
          dsimp only
          rw [norm_mul]
          have hZ : ‖∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t‖ ≤
              M * ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u‖ := by
            calc ‖∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t‖
                ≤ ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t‖ :=
                  norm_integral_le_integral_norm _
              _ ≤ ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u‖ * M := by
                  refine integral_mono_of_nonneg
                    (Filter.Eventually.of_forall fun u => norm_nonneg _)
                    ((hIntW t).norm.mul_const M) (Filter.Eventually.of_forall fun u => ?_)
                  dsimp only
                  rw [norm_mul]
                  exact mul_le_mul_of_nonneg_left (hSfbd u t) (norm_nonneg _)
              _ = M * ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u‖ := by
                  rw [MeasureTheory.integral_mul_const, mul_comm]
          have hKC := hKCl1 a b ha hab (2 * Real.pi * t)
          rw [hMajdef]
          calc ‖sepG ψ t‖ *
                ‖∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t‖
              ≤ ‖sepG ψ t‖ *
                (M * ∫ u : ℝ, ‖𝓕 (chat a b (2 * Real.pi * t)) u‖) :=
                mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
            _ ≤ ‖sepG ψ t‖ *
                (M * (KC * (1 + |2 * Real.pi * t|) ^ 2 * (Real.log (2 + b / a) + 1))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hKC hMnn) (norm_nonneg _)
            _ = M * (Real.log (2 + b / a) + 1) *
                  ((KC * (1 + |2 * Real.pi * t|) ^ 2) * ‖sepG ψ t‖) := by
                ring
      _ = M * (Real.log (2 + b / a) + 1) * ∫ t : ℝ, Maj t := by
          rw [MeasureTheory.integral_const_mul]
  -- ## 6. conclusion
  rw [hEq]
  have hlog : (1 : ℝ) ≤ (Real.log (2 + b / a) + 1) ^ 2 := one_le_pow₀ hL1
  have hDnn : (0 : ℝ) ≤ ∫ t : ℝ, Maj t := integral_nonneg hMajnn
  have hstep1 : M * (Real.log (2 + b / a) + 1) * ∫ t : ℝ, Maj t
      ≤ M * (Real.log (2 + b / a) + 1) ^ 2 * ∫ t : ℝ, Maj t :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by nlinarith [hL1]) hMnn) hDnn
  have hstep2 : M * (Real.log (2 + b / a) + 1) ^ 2 * ∫ t : ℝ, Maj t
      ≤ ((∫ t : ℝ, Maj t) + 1) * (Real.log (2 + b / a) + 1) ^ 2 * M := by
    nlinarith [hDnn, hMnn, sq_nonneg (Real.log (2 + b / a) + 1),
      mul_nonneg hMnn (sq_nonneg (Real.log (2 + b / a) + 1))]
  calc ‖∫ t : ℝ, sepG ψ t *
        (∫ u : ℝ, 𝓕 (chat a b (2 * Real.pi * t)) u * Sf u t)‖
      ≤ M * (Real.log (2 + b / a) + 1) * ∫ t : ℝ, Maj t := hbound
    _ ≤ M * (Real.log (2 + b / a) + 1) ^ 2 * ∫ t : ℝ, Maj t := hstep1
    _ ≤ ((∫ t : ℝ, Maj t) + 1) * (Real.log (2 + b / a) + 1) ^ 2 * M := hstep2
end Work.FIArea4.S15red
