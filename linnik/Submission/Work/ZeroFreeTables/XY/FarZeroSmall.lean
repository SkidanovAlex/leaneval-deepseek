import Mathlib
import Submission.Work.ZeroFreeTables.XY.LaplaceFarReal

namespace Work.ZeroFreeTables.XY

open MeasureTheory

theorem FarZeroSmall (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q → ∀ {s u : ℂ},
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) →
        |((s - u) * ((Real.log (q:ℝ) : ℝ) : ℂ)).re| ≤ 1 →
        δ < ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ →
        (∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((s - u) * ((Real.log (q:ℝ) : ℝ) : ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ)).re
          ≤ f 0 * ε / 40 := by
  intro f hcont hsupp hf2 hBnd hf0 ε δ hε hδ0
  set C₀ : ℝ := ‖derivWithin (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.Ioi 0) 0‖ with hC₀def
  set C₁ : ℝ := (2 * C₀ + 2 * B * x₀) * Real.exp (x₀ * 1) with hC₁def
  have hC₁nn : 0 ≤ C₁ := by rw [hC₁def]; positivity
  set D : ℝ := δ / 2 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; linarith
  set N : ℝ := max (max (80 / (D * ε)) (Real.sqrt (80 * C₁ / (f 0 * ε)) / D))
      (max (16 / δ ^ 2) (max 16 (4 / δ))) with hNdef
  have hN1 : 80 / (D * ε) ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN2 : Real.sqrt (80 * C₁ / (f 0 * ε)) / D ≤ N :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hN3 : 16 / δ ^ 2 ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hN4 : (16 : ℝ) ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hN5 : 4 / δ ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN4
  refine ⟨⌈Real.exp N⌉₊ + 2, ?_⟩
  intro q hqne hq s u hsre hre hwin
  haveI : NeZero q := hqne
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqN : Real.exp N ≤ (q : ℝ) := by
    have h1 : Real.exp N ≤ (⌈Real.exp N⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp N⌉₊ : ℝ) ≤ (q : ℝ) := by
      have h3 : ⌈Real.exp N⌉₊ ≤ q := by omega
      exact_mod_cast h3
    linarith
  have hLN : N ≤ L := by
    rw [hLdef]
    calc N = Real.log (Real.exp N) := (Real.log_exp N).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos N) hqN
  have hLpos : 0 < L := lt_of_lt_of_le hNpos hLN
  have hL1 : 1 ≤ L := le_trans (by norm_num : (1:ℝ) ≤ 16) (le_trans hN4 hLN)
  -- ## the two comparisons of the real parts
  have hsub_re : ((s - u) * ((L : ℝ) : ℂ)).re = (s.re - u.re) * L := by
    simp [Complex.mul_re, Complex.sub_re]
  have hreL : |(s.re - u.re) * L| ≤ 1 := by
    rwa [hsub_re] at hre
  have hu2 : |s.re - u.re| ≤ 1 / L := by
    rw [abs_mul, abs_of_pos hLpos] at hreL
    rw [le_div_iff₀ hLpos]
    exact hreL
  have hu1 : |1 - s.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    rw [abs_sub_comm]; exact hsre
  have hu3 : |1 - u.re| ≤ (Real.sqrt (Real.log (Real.log (q : ℝ))) + 1) / L := by
    have hdec : 1 - u.re = (s.re - u.re) + (1 - s.re) := by ring
    calc |1 - u.re| = |(s.re - u.re) + (1 - s.re)| := by rw [hdec]
      _ ≤ |s.re - u.re| + |1 - s.re| := abs_add_le _ _
      _ ≤ 1 / L + Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
          add_le_add hu2 hu1
      _ = (Real.sqrt (Real.log (Real.log (q : ℝ))) + 1) / L := by ring
  -- ## the geometric bound `√(log log q) + 1 ≤ (δ/2) L`
  have hδ4pos : 0 < δ / 4 := by linarith
  have hsq : (4 / δ) ^ 2 ≤ L := by
    have h : (4 / δ) ^ 2 = 16 / δ ^ 2 := by ring
    rw [h]; exact le_trans hN3 hLN
  have h4 : 4 / δ ≤ Real.sqrt L := by
    have h1 : Real.sqrt ((4 / δ) ^ 2) ≤ Real.sqrt L := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ 4 / δ)] at h1
  have hsqrtL_le : Real.sqrt L ≤ δ / 4 * L := by
    have h1 : (1:ℝ) ≤ δ / 4 * Real.sqrt L := by
      have h2 := mul_le_mul_of_nonneg_left h4 hδ4pos.le
      have h3 : δ / 4 * (4 / δ) = 1 := by field_simp
      linarith [h2, h3]
    calc Real.sqrt L = 1 * Real.sqrt L := by ring
      _ ≤ (δ / 4 * Real.sqrt L) * Real.sqrt L :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg L)
      _ = δ / 4 * L := by rw [mul_assoc, Real.mul_self_sqrt hLpos.le]
  have hone_le : (1:ℝ) ≤ δ / 4 * L := by
    have h2 := mul_le_mul_of_nonneg_left (le_trans hN5 hLN) hδ4pos.le
    have h3 : δ / 4 * (4 / δ) = 1 := by field_simp
    linarith [h2, h3]
  have hu4 : (Real.sqrt (Real.log (Real.log (q : ℝ))) + 1) / L ≤ D := by
    rw [div_le_iff₀ hLpos, hDdef]
    have hsq2 : Real.sqrt (Real.log L) ≤ Real.sqrt L :=
      Real.sqrt_le_sqrt (by have := Real.log_le_sub_one_of_pos hLpos; linarith)
    linarith [hsq2, hsqrtL_le, hone_le]
  have hwu : |1 - u.re| ≤ D := le_trans hu3 hu4
  -- ## the imaginary part at the window centre
  have hwre : ((1:ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
  have hwim : ((1:ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
  have hIm_gt : D < |s.im - u.im| := by
    have htri := Complex.norm_le_abs_re_add_abs_im ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    rw [hwre, hwim] at htri
    rw [hDdef] at *
    linarith [htri, hwin]
  have hsub_im : ((s - u) * ((L : ℝ) : ℂ)).im = (s.im - u.im) * L := by
    simp [Complex.mul_im, Complex.sub_im]
  have hη : δ / 2 * L ≤ |((s - u) * ((L : ℝ) : ℂ)).im| := by
    rw [hsub_im, abs_mul, abs_of_pos hLpos]
    have h2 : δ / 2 < |s.im - u.im| := by rw [← hDdef]; exact hIm_gt
    nlinarith [h2, hLpos]
  have ha : |((s - u) * ((L : ℝ) : ℂ)).re| ≤ 1 := by
    rw [hsub_re]; exact hreL
  -- ## the analytic decay bound
  have hmain := LaplaceFarReal hx₀ hB hδ0 hLpos hcont hsupp hf2 hBnd
    (a := ((s - u) * ((L : ℝ) : ℂ)).re) (η := ((s - u) * ((L : ℝ) : ℂ)).im) (M := 1) ha hη
  rw [show ((↑(((s - u) * ((L : ℝ) : ℂ)).re) : ℂ) + (↑(((s - u) * ((L : ℝ) : ℂ)).im) : ℂ) * Complex.I)
        = (s - u) * ((L : ℝ) : ℂ) from Complex.re_add_im _] at hmain
  -- ## the two threshold bounds
  have h80 : 80 / ε ≤ D * L := by
    have h1 : 80 / ε ≤ D * N := by
      have h2 := mul_le_mul_of_nonneg_left hN1 hDpos.le
      have h3 : D * (80 / (D * ε)) = 80 / ε := by field_simp
      linarith [h2, h3]
    have h4 : D * N ≤ D * L := mul_le_mul_of_nonneg_left hLN hDpos.le
    linarith
  have hA : ‖f 0‖ / (δ / 2 * L) ≤ f 0 * ε / 80 := by
    have hf0norm : ‖f 0‖ = f 0 := by rw [Real.norm_eq_abs, abs_of_pos hf0]
    rw [hf0norm, ← hDdef]
    have hpos : 0 < 80 / ε := by positivity
    have hle : f 0 / (80 / ε) = f 0 * ε / 80 := by field_simp
    calc f 0 / (D * L) ≤ f 0 / (80 / ε) := div_le_div_of_nonneg_left hf0.le hpos h80
      _ = f 0 * ε / 80 := hle
  have hsq80 : 80 * C₁ / (f 0 * ε) ≤ (D * L) ^ 2 := by
    have h1 : Real.sqrt (80 * C₁ / (f 0 * ε)) ≤ D * N := by
      have h2 := mul_le_mul_of_nonneg_left hN2 hDpos.le
      have h3 : D * (Real.sqrt (80 * C₁ / (f 0 * ε)) / D) = Real.sqrt (80 * C₁ / (f 0 * ε)) := by
        field_simp
      linarith [h2, h3]
    have h4 : D * N ≤ D * L := mul_le_mul_of_nonneg_left hLN hDpos.le
    have h5 : Real.sqrt (80 * C₁ / (f 0 * ε)) ≤ D * L := le_trans h1 h4
    calc 80 * C₁ / (f 0 * ε) = Real.sqrt (80 * C₁ / (f 0 * ε)) ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]
      _ ≤ (D * L) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h5 2
  have hB2 : (2 * C₀ + 2 * B * x₀) * Real.exp (x₀ * 1) / (δ / 2 * L) ^ 2 ≤ f 0 * ε / 80 := by
    rw [← hC₁def, ← hDdef,
      div_le_div_iff₀ (by positivity : (0:ℝ) < (D * L) ^ 2) (by norm_num : (0:ℝ) < 80)]
    have hf0ε : 0 < f 0 * ε := mul_pos hf0 hε
    have h1 := mul_le_mul_of_nonneg_left hsq80 hf0ε.le
    have h2 : f 0 * ε * (80 * C₁ / (f 0 * ε)) = 80 * C₁ := by
      field_simp
    rw [h2] at h1
    linarith [h1]
  -- ## conclude
  have h1 : (∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - u) * ((L : ℝ) : ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ)).re
      ≤ ‖∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - u) * ((L : ℝ) : ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ)‖ :=
    Complex.re_le_norm _
  have h2 : ‖∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((s - u) * ((L : ℝ) : ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ)‖ ≤ f 0 * ε / 40 := by
    refine le_trans hmain ?_
    linarith [hA, hB2]
  linarith [h1, h2]

end Work.ZeroFreeTables.XY
