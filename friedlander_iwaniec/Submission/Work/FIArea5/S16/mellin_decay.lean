import Mathlib
import Submission.Work.FIArea5.S16.mellin_ibp
import Submission.Work.FIArea5.S16.p_endpoint_zero

/-!
# Mellin decay of a smooth bump on `(N, (1+θ)N]`  (*FI* (16.28))

For a `C²` function `p` with `0 ≤ p ≤ 1`, supported in `(N, (1+θ)N]`, and with second
derivative bounded by `2^20 (θN)^{-2}`, the Mellin integral
`∫_N^{(1+θ)N} p(u) u^{s-1} du` (`s = σ + it`, `1/2 ≤ σ ≤ 2`) is
`≪ θ N^σ (1 + θ²t²)^{-1}`.

The proof has three ingredients:

* **Endpoint vanishing** (`p_endpoint_zero`): the support condition forces `p ≡ 0` on
  `(-∞, N]` and on `((1+θ)N, ∞)`, so by continuity `p` vanishes at `N` and at `(1+θ)N`, and
  because `p ≥ 0` both are global minima, whence `p'(N) = p'((1+θ)N) = 0`.
* **Two integrations by parts** (`mellin_ibp`), in which *all* boundary terms vanish, giving
  `∫ p u^{w} = ((w+1)(w+2))^{-1} ∫ p'' u^{w+2}`.  Since the exponent `w = s - 1` has
  imaginary part `t ≠ 0`, the factor `(w+1)(w+2) = s(s+1)` has modulus at least `t²`.
* **The two elementary bounds**: `‖∫ p u^{s-1}‖ ≤ ∫ u^{σ-1} = ((1+θ)^σ - 1)N^σ/σ ≤ 6θN^σ`
  and, from the identity, `‖∫ p u^{s-1}‖ ≤ 2^20 (θN)^{-2} (∫ u^{σ+1})/t² ≤ 2^23 N^σ/(θt²)`.
  Taking the smaller of the two according as `(θt)² ≤ 100` or not finishes the proof.
-/

namespace Work.FIArea5.S16

open MeasureTheory intervalIntegral
open scoped Topology

/-- `u ↦ u^w` (complex power, positive real base) is continuous on `[N,B]` when `N,B > 0`. -/
private lemma md_continuousOn_cpow (w : ℂ) {N B : ℝ} (hN : 0 < N) (hB : 0 < B) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ w) (Set.uIcc N B) := by
  intro u hu
  have hmin : min N B ≤ u := by
    rcases Set.mem_uIcc.mp hu with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans (min_le_right _ _) h1
  have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le (lt_min hN hB) hmin)
  exact (Complex.continuousAt_ofReal_cpow_const u w (Or.inr hu0)).continuousWithinAt

/-- `u ↦ u^r` (real power) is continuous on `[N,B]` when `N,B > 0`. -/
private lemma md_continuousOn_rpow (r : ℝ) {N B : ℝ} (hN : 0 < N) (hB : 0 < B) :
    ContinuousOn (fun u : ℝ => u ^ r) (Set.uIcc N B) := by
  intro u hu
  have hmin : min N B ≤ u := by
    rcases Set.mem_uIcc.mp hu with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans (min_le_right _ _) h1
  have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le (lt_min hN hB) hmin)
  exact (Real.continuousAt_rpow_const u r (Or.inl hu0)).continuousWithinAt

private lemma md_intervalIntegrable_rpow (r : ℝ) {N B : ℝ} (hN : 0 < N) (hB : 0 < B) :
    IntervalIntegrable (fun u : ℝ => u ^ r) volume N B :=
  (md_continuousOn_rpow r hN hB).intervalIntegrable

private lemma md_intervalIntegrable_mul_rpow (f : ℝ → ℝ) (r : ℝ) {N B : ℝ} (hN : 0 < N)
    (hB : 0 < B) (hf : Continuous f) :
    IntervalIntegrable (fun u : ℝ => f u * u ^ r) volume N B :=
  (hf.continuousOn.mul (md_continuousOn_rpow r hN hB)).intervalIntegrable

/-- Elementary bound `((1+θ)^σ - 1)/σ ≤ 6θ` for `0 < θ ≤ 1`, `1/2 ≤ σ ≤ 2`. -/
private lemma md_num_triv (θ σ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hσ : 1 / 2 ≤ σ)
    (hσ2 : σ ≤ 2) : ((1 + θ) ^ σ - 1) / σ ≤ 6 * θ := by
  have h1 : (1:ℝ) ≤ 1 + θ := by linarith
  have h2 : (1 + θ) ^ σ ≤ (1 + θ) ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hσ2
  have h2' : (1 + θ) ^ (2:ℝ) = (1 + θ) ^ 2 := Real.rpow_two (1+θ)
  have h3 : (1 + θ) ^ 2 - 1 ≤ 3 * θ := by nlinarith [sq_nonneg θ, hθ, hθ1]
  have h4 : 0 < σ := by linarith
  have h34 : (1 + θ) ^ σ - 1 ≤ 3 * θ := by rw [h2'] at h2; linarith
  have h5 : ((1+θ)^σ - 1)/σ ≤ (3*θ)/σ := div_le_div_of_nonneg_right h34 h4.le
  have h6 : (3*θ)/σ ≤ 6*θ := by rw [div_le_iff₀ h4]; nlinarith
  linarith

/-- Elementary bound `(1+θ)^(σ+2) - 1 ≤ 6θ(σ+2)`. -/
private lemma md_num_sec (θ σ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hσ : 1 / 2 ≤ σ)
    (hσ2 : σ ≤ 2) : (1 + θ) ^ (σ + 2) - 1 ≤ 6 * θ * (σ + 2) := by
  have h1 : (1:ℝ) ≤ 1 + θ := by linarith
  have h2 : (1 + θ) ^ (σ + 2) ≤ (1 + θ) ^ (4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have h2' : (1 + θ) ^ (4:ℝ) = (1 + θ) ^ 4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hθ2 : θ^2 ≤ θ := by nlinarith
  have hθ3 : θ^3 ≤ θ := by nlinarith [hθ2, hθ.le]
  have hθ4 : θ^4 ≤ θ := by nlinarith [hθ3, hθ.le]
  have h3 : (1 + θ) ^ 4 - 1 ≤ 15 * θ := by nlinarith [hθ2, hθ3, hθ4, hθ.le]
  have h4 : (15:ℝ) ≤ 6 * (σ + 2) := by linarith
  have h5 : (15:ℝ) * θ ≤ 6 * θ * (σ + 2) := by nlinarith [h4, hθ]
  calc (1 + θ) ^ (σ + 2) - 1 ≤ (1 + θ) ^ (4:ℝ) - 1 := by linarith
    _ = (1 + θ)^4 - 1 := by rw [h2']
    _ ≤ 15 * θ := h3
    _ ≤ 6 * θ * (σ + 2) := h5

/-- Trivial bound on the Mellin integral. -/
private lemma md_triv_bound_num (N θ σ : ℝ) (hN : 0 < N) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hσ : 1/2 ≤ σ) (hσ2 : σ ≤ 2) :
    ((1+θ)^σ - 1) * N^σ / σ ≤ 6 * θ * N^σ := by
  have h := md_num_triv θ σ hθ hθ1 hσ hσ2
  have hNr : (0:ℝ) ≤ N^σ := Real.rpow_nonneg hN.le σ
  have key : ((1+θ)^σ - 1) * N^σ / σ = N^σ * (((1+θ)^σ - 1)/σ) := by ring
  rw [key]
  calc N^σ * (((1+θ)^σ - 1)/σ) ≤ N^σ * (6*θ) := mul_le_mul_of_nonneg_left h hNr
    _ = 6 * θ * N^σ := by ring

/-- Bound obtained from the two integrations by parts. -/
private lemma md_sec_bound_num (N θ σ : ℝ) (hN : 0 < N) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hσ : 1/2 ≤ σ) (hσ2 : σ ≤ 2) :
    (1048576 / (θ * N)^2) * (((1+θ)^(σ+2) - 1) * N^(σ+2) / (σ+2)) ≤ 6291456 * N^σ / θ := by
  have hσ2pos : (0:ℝ) < σ + 2 := by linarith
  have hX : ((1+θ)^(σ+2) - 1) / (σ+2) ≤ 6*θ := by
    rw [div_le_iff₀ hσ2pos]; exact md_num_sec θ σ hθ hθ1 hσ hσ2
  have hNrpow : (0:ℝ) ≤ N^(σ+2) := Real.rpow_nonneg hN.le _
  have key : ((1+θ)^(σ+2) - 1) * N^(σ+2) / (σ+2) = (((1+θ)^(σ+2) - 1)/(σ+2)) * N^(σ+2) := by
    ring
  rw [key]
  have hstep : (((1+θ)^(σ+2) - 1)/(σ+2)) * N^(σ+2) ≤ (6*θ) * N^(σ+2) :=
    mul_le_mul_of_nonneg_right hX hNrpow
  have hconst : (0:ℝ) ≤ 1048576 / (θ * N)^2 := by positivity
  calc (1048576 / (θ * N)^2) * ((((1+θ)^(σ+2) - 1)/(σ+2)) * N^(σ+2))
      ≤ (1048576 / (θ * N)^2) * ((6*θ) * N^(σ+2)) := mul_le_mul_of_nonneg_left hstep hconst
    _ = 6291456 * N^σ / θ := by
        rw [show N^(σ+2) = N^σ * N^2 by rw [Real.rpow_add hN, Real.rpow_two]]
        field_simp
        ring

/-- In the regime `(θt)² ≥ 100` the trivial bound `6θN^σ` is below the target. -/
private lemma md_small_num (N θ σ t : ℝ) (hN : 0 < N) (hθ : 0 < θ) (hcase : (θ*t)^2 ≤ 100) :
    6 * θ * N^σ ≤ 10000000 * θ * N^σ * (1 + (θ*t)^2)⁻¹ := by
  have h1 : (0:ℝ) < 1 + (θ*t)^2 := by positivity
  have h2 : 1 + (θ*t)^2 ≤ 101 := by linarith
  have hinv : (1:ℝ)/101 ≤ (1 + (θ*t)^2)⁻¹ := by
    rw [one_div]
    exact (inv_le_inv₀ (by norm_num) h1).mpr h2
  have h3 : (6:ℝ) ≤ 10000000 * (1 + (θ*t)^2)⁻¹ := by
    calc (6:ℝ) ≤ 10000000 * (1/101) := by norm_num
      _ ≤ 10000000 * (1 + (θ*t)^2)⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
  have hNσ : (0:ℝ) ≤ N^σ := Real.rpow_nonneg hN.le σ
  calc 6 * θ * N^σ = 6 * (θ * N^σ) := by ring
    _ ≤ (10000000 * (1 + (θ*t)^2)⁻¹) * (θ * N^σ) :=
        mul_le_mul_of_nonneg_right h3 (mul_nonneg hθ.le hNσ)
    _ = 10000000 * θ * N^σ * (1 + (θ*t)^2)⁻¹ := by ring

/-- In the regime `(θt)² > 100` the two-integration-by-parts bound is below the target. -/
private lemma md_large_num (N θ σ t : ℝ) (hN : 0 < N) (hθ : 0 < θ) (ht : t ≠ 0)
    (hcase : 100 < (θ*t)^2) :
    6291456 * N ^ σ / (θ * t ^ 2) ≤ 10000000 * θ * N ^ σ * (1 + (θ * t) ^ 2)⁻¹ := by
  have h1 : (0:ℝ) < 1 + (θ*t)^2 := by linarith
  have hle : (1:ℝ) + (θ*t)^2 ≤ (101/100) * (θ*t)^2 := by nlinarith [hcase]
  have hinv : ((101/100) * (θ*t)^2)⁻¹ ≤ (1 + (θ*t)^2)⁻¹ :=
    (inv_le_inv₀ (by positivity) h1).mpr hle
  have hNσ : (0:ℝ) ≤ N^σ := Real.rpow_nonneg hN.le σ
  have hkey : 10000000 * θ * N^σ * ((101/100) * (θ*t)^2)⁻¹
      = (1000000000/101) * (N^σ / (θ * t^2)) := by
    field_simp
    ring
  have h2 : (6291456:ℝ) ≤ 1000000000/101 := by norm_num
  have h3 : 6291456 * N^σ / (θ*t^2) ≤ (1000000000/101) * (N^σ / (θ*t^2)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hNσ) (by positivity)
  calc 6291456 * N^σ / (θ*t^2) ≤ (1000000000/101) * (N^σ/(θ*t^2)) := h3
    _ = 10000000 * θ * N^σ * ((101/100)*(θ*t)^2)⁻¹ := hkey.symm
    _ ≤ 10000000 * θ * N^σ * (1 + (θ*t)^2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)

/-- **(16.28)**: Mellin decay of the radial mollifier. -/
theorem mellin_decay (p : ℝ → ℝ) (N θ : ℝ) (hN : 0 < N) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N)
    (hd2 : ∀ u, |iteratedDeriv 2 p u| ≤ 1048576 / (θ * N) ^ 2)
    (σ t : ℝ) (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (ht : t ≠ 0) :
    ‖∫ u in N..(1 + θ) * N, (p u : ℂ) * (u : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I - 1)‖
      ≤ 10000000 * θ * N ^ σ * (1 + (θ * t) ^ 2)⁻¹ := by
  set B : ℝ := (1 + θ) * N with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hNB : N ≤ B := by rw [hBdef]; nlinarith
  obtain ⟨hpN, hpB, hdpN, hdpB⟩ := p_endpoint_zero p N θ hN hpC hp0 hsupp
  set w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I - 1 with hwdef
  have hwre : w.re = σ - 1 := by rw [hwdef]; simp
  have hwre2 : (w + 2).re = σ + 1 := by rw [hwdef]; simp; ring
  have hwim1 : (w + 1).im = t := by rw [hwdef]; simp
  have hwim2 : (w + 2).im = t := by rw [hwdef]; simp
  have hw1 : w + 1 ≠ 0 := by
    intro h
    have h' : (w + 1).im = 0 := by rw [h]; simp
    rw [hwim1] at h'; exact ht h'
  have hw2 : w + 2 ≠ 0 := by
    intro h
    have h' : (w + 2).im = 0 := by rw [h]; simp
    rw [hwim2] at h'; exact ht h'
  have hu_pos : ∀ u ∈ Set.uIcc N B, 0 < u := by
    intro u hu
    have hmin : min N B ≤ u := by
      rcases Set.mem_uIcc.mp hu with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact le_trans (min_le_left _ _) h1
      · exact le_trans (min_le_right _ _) h1
    exact lt_of_lt_of_le (lt_min hN hBpos) hmin
  -- the modulus of `(w+1)(w+2) = s(s+1)` is at least `t²`
  have hden : t ^ 2 ≤ ‖(w + 1) * (w + 2)‖ := by
    have h1 : |t| ≤ ‖w + 1‖ := by simpa [hwim1] using Complex.abs_im_le_norm (w + 1)
    have h2 : |t| ≤ ‖w + 2‖ := by simpa [hwim2] using Complex.abs_im_le_norm (w + 2)
    have h3 : |t| * |t| ≤ ‖w + 1‖ * ‖w + 2‖ :=
      mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg _)
    have h4 : |t| * |t| = t^2 := by rw [← sq, sq_abs]
    rw [h4] at h3
    rwa [norm_mul]
  have ht2pos : 0 < t ^ 2 := by positivity
  -- the two integrations by parts
  have hibp := mellin_ibp p N B w hN hBpos hpC hpN hpB hdpN hdpB hw1 hw2
  have hI_eq : (∫ u in N..B, (p u : ℂ) * (u : ℂ) ^ w)
      = (∫ u in N..B, ((iteratedDeriv 2 p u : ℝ) : ℂ) * (u : ℂ) ^ (w + 2))
          / ((w + 1) * (w + 2)) := by
    rw [eq_div_iff (mul_ne_zero hw1 hw2)]
    exact hibp
  -- bound 1: the trivial (L¹) bound
  have htriv : ‖∫ u in N..B, (p u : ℂ) * (u : ℂ) ^ w‖ ≤ 6 * θ * N ^ σ := by
    calc ‖∫ u in N..B, (p u : ℂ) * (u : ℂ) ^ w‖
        ≤ ∫ u in N..B, ‖(p u : ℂ) * (u : ℂ) ^ w‖ :=
          intervalIntegral.norm_integral_le_integral_norm hNB
      _ = ∫ u in N..B, p u * u ^ (σ - 1) := by
          apply intervalIntegral.integral_congr
          intro u hu
          change ‖(p u : ℂ) * (u : ℂ) ^ w‖ = p u * u ^ (σ - 1)
          have hu0 : 0 < u := hu_pos u hu
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 u),
              Complex.norm_cpow_eq_rpow_re_of_pos hu0, hwre]
      _ ≤ ∫ u in N..B, u ^ (σ - 1) := by
          apply intervalIntegral.integral_mono_on hNB
            (md_intervalIntegrable_mul_rpow p (σ - 1) hN hBpos hpC.continuous)
            (md_intervalIntegrable_rpow (σ - 1) hN hBpos)
          intro u hu
          exact mul_le_of_le_one_left (Real.rpow_nonneg (le_trans hN.le hu.1) _) (hp1 u)
      _ = (B ^ σ - N ^ σ) / σ := by
          rw [integral_rpow (Or.inl (by linarith))]
          rw [show (σ - 1) + 1 = σ by ring]
      _ = ((1 + θ) ^ σ - 1) * N ^ σ / σ := by
          rw [hBdef, Real.mul_rpow (by positivity) hN.le]
          ring
      _ ≤ 6 * θ * N ^ σ := md_triv_bound_num N θ σ hN hθ hθ1 hσ hσ2
  -- bound 2: the two-integration-by-parts bound
  have hsec : ‖∫ u in N..B, (p u : ℂ) * (u : ℂ) ^ w‖ ≤ 6291456 * N ^ σ / (θ * t ^ 2) := by
    rw [hI_eq, norm_div]
    have hcont' : Continuous (fun u : ℝ => |iteratedDeriv 2 p u|) :=
      (hpC.continuous_iteratedDeriv' 2).abs
    have hconstcont : Continuous (fun _ : ℝ => 1048576 / (θ * N) ^ 2) := continuous_const
    have hY : ‖∫ u in N..B, ((iteratedDeriv 2 p u : ℝ) : ℂ) * (u : ℂ) ^ (w + 2)‖
        ≤ 1048576 / (θ * N) ^ 2 * (((1 + θ) ^ (σ + 2) - 1) * N ^ (σ + 2) / (σ + 2)) := by
      calc ‖∫ u in N..B, ((iteratedDeriv 2 p u : ℝ) : ℂ) * (u : ℂ) ^ (w + 2)‖
          ≤ ∫ u in N..B, ‖((iteratedDeriv 2 p u : ℝ) : ℂ) * (u : ℂ) ^ (w + 2)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hNB
        _ = ∫ u in N..B, |iteratedDeriv 2 p u| * u ^ (σ + 1) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change ‖((iteratedDeriv 2 p u : ℝ) : ℂ) * (u : ℂ) ^ (w + 2)‖
              = |iteratedDeriv 2 p u| * u ^ (σ + 1)
            have hu0 : 0 < u := hu_pos u hu
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                Complex.norm_cpow_eq_rpow_re_of_pos hu0, hwre2]
        _ ≤ ∫ u in N..B, (1048576 / (θ * N) ^ 2) * u ^ (σ + 1) := by
            apply intervalIntegral.integral_mono_on hNB
              (md_intervalIntegrable_mul_rpow (fun u => |iteratedDeriv 2 p u|) (σ + 1) hN hBpos
                hcont')
              (md_intervalIntegrable_mul_rpow (fun _ : ℝ => 1048576 / (θ * N) ^ 2) (σ + 1) hN
                hBpos hconstcont)
            intro u hu
            exact mul_le_mul_of_nonneg_right (hd2 u) (Real.rpow_nonneg (le_trans hN.le hu.1) _)
        _ = (1048576 / (θ * N) ^ 2) * ∫ u in N..B, u ^ (σ + 1) := by
            rw [intervalIntegral.integral_const_mul]
        _ = (1048576 / (θ * N) ^ 2) * ((B ^ (σ + 2) - N ^ (σ + 2)) / (σ + 2)) := by
            rw [integral_rpow (Or.inl (by linarith))]
            rw [show σ + 1 + 1 = σ + 2 by ring]
        _ = 1048576 / (θ * N) ^ 2 * (((1 + θ) ^ (σ + 2) - 1) * N ^ (σ + 2) / (σ + 2)) := by
            rw [hBdef, Real.mul_rpow (by positivity) hN.le]
            ring
    have hY' := le_trans hY (md_sec_bound_num N θ σ hN hθ hθ1 hσ hσ2)
    calc ‖∫ u in N..B, ((iteratedDeriv 2 p u : ℝ) : ℂ) * (u : ℂ) ^ (w + 2)‖
            / ‖(w + 1) * (w + 2)‖
        ≤ ‖∫ u in N..B, ((iteratedDeriv 2 p u : ℝ) : ℂ) * (u : ℂ) ^ (w + 2)‖ / t ^ 2 :=
          div_le_div_of_nonneg_left (norm_nonneg _) ht2pos hden
      _ ≤ (6291456 * N ^ σ / θ) / t ^ 2 := div_le_div_of_nonneg_right hY' ht2pos.le
      _ = 6291456 * N ^ σ / (θ * t ^ 2) := by ring
  by_cases hcase : (θ * t) ^ 2 ≤ 100
  · exact le_trans htriv (md_small_num N θ σ t hN hθ hcase)
  · exact le_trans hsec (md_large_num N θ σ t hN hθ ht (not_le.mp hcase))

end Work.FIArea5.S16
