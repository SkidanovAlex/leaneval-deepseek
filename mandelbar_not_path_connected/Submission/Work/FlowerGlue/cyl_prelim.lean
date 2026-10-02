import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue

open Complex Filter Function
open scoped Real Topology

noncomputable section

/-- The exponential coordinate `e z = exp (2 π i z)` on the cylinder `ℂ / ℤ`. -/
noncomputable def e (z : ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)

theorem e_eq_qParam (z : ℂ) : e z = Function.Periodic.qParam (1 : ℝ) z := by
  simp only [e, Function.Periodic.qParam]
  norm_num

theorem e_add (a z : ℂ) : e (a + z) = e a * e z := by
  simp only [e, ← Complex.exp_add]
  congr 1
  ring

theorem e_ne_zero (z : ℂ) : e z ≠ 0 := by
  simp [e]

theorem e_one : e 1 = 1 := by
  simp only [e]
  simpa using Complex.exp_two_pi_mul_I

theorem e_periodic : Function.Periodic e 1 := by
  intro z
  rw [e_add, e_one, mul_one]

/-- **C1** (see `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §1.1): if `T` is entire, injective
and 1-equivariant, then at the upper end of the cylinder `T` omits a whole `ℤ`-tube around `T 0`. -/
theorem cyl_omit {T : ℂ → ℂ} (hT : Differentiable ℂ T) (hinj : Function.Injective T)
    (hper : ∀ ζ : ℂ, T (ζ + 1) = T ζ + 1) :
    ∃ a : ℂ, ∃ ε > 0, ∀ ζ : ℂ, 1 < ζ.im → ∀ n : ℤ, ε ≤ ‖T ζ - a - (n : ℂ)‖ := by
  refine ⟨T 0, ?_⟩
  have hnc : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), T z = T 0 := by
    intro h
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp h
    have hmem : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      have : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < r / 2)]
      rw [this]; linarith
    have hne : ((r / 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ofReal_ne_zero]
      linarith
    exact hne (hinj (hsub hmem))
  have hopen : 𝓝 (T 0) ≤ Filter.map T (𝓝 0) := by
    rcases (hT.analyticAt 0).eventually_constant_or_nhds_le_map_nhds with h' | h'
    · exact absurd h' hnc
    · exact h'
  have hTimg : T '' Metric.ball (0 : ℂ) (1 / 2) ∈ 𝓝 (T 0) := by
    apply hopen
    rw [Filter.mem_map]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) (by norm_num))
      (fun z hz => ⟨z, hz, rfl⟩)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hTimg
  refine ⟨ε, hε, ?_⟩
  intro ζ hζ n
  by_contra hcon
  rw [not_le] at hcon
  have hperZ : ∀ (w : ℂ) (m : ℤ), T (w + (m : ℂ)) = T w + (m : ℂ) := by
    intro w m
    have hp : Function.Periodic (fun w => T w - w) 1 := by
      intro w
      show T (w + 1) - (w + 1) = T w - w
      rw [hper w]
      ring
    have hthis := hp.int_mul m w
    rw [mul_one] at hthis
    calc T (w + (m : ℂ)) = (T (w + (m : ℂ)) - (w + (m : ℂ))) + (w + (m : ℂ)) := by ring
      _ = (T w - w) + (w + (m : ℂ)) := by rw [hthis]
      _ = T w + (m : ℂ) := by ring
  have hmem2 : T ζ - (n : ℂ) ∈ T '' Metric.ball (0 : ℂ) (1 / 2) := by
    apply hεsub
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show T ζ - (n : ℂ) - T 0 = T ζ - T 0 - (n : ℂ) from by ring]
    exact hcon
  obtain ⟨v, hv, hveq⟩ := hmem2
  have hζv : ζ = v + (n : ℂ) := by
    apply hinj
    rw [hperZ v n, hveq]
    ring
  have hvlt : ‖v‖ < 1 / 2 := by
    rw [Metric.mem_ball, dist_zero_right] at hv
    exact hv
  have him : ζ.im = v.im := by
    rw [hζv, Complex.add_im, ← Complex.ofReal_intCast n, Complex.ofReal_im, add_zero]
  have hvim : v.im ≤ ‖v‖ := Complex.im_le_norm v
  linarith

/-- **C2** (see `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §1.1): the exponential coordinate
separates the `ℤ`-tubes. -/
theorem exp_sep (a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, (∀ n : ℤ, ε ≤ ‖z - a - (n : ℂ)‖) → δ ≤ ‖e z - e a‖ := by
  refine ⟨‖e a‖ * min (1 / 2) (ε / 4), ?_, ?_⟩
  · have hmin : (0 : ℝ) < min (1 / 2) (ε / 4) := lt_min (by norm_num) (by linarith)
    exact mul_pos (norm_pos_iff.mpr (e_ne_zero a)) hmin
  · intro z hz
    by_contra hcon
    rw [not_le] at hcon
    have hea : e a ≠ 0 := e_ne_zero a
    have hna : 0 < ‖e a‖ := norm_pos_iff.mpr hea
    have hz_eq : e z = e a * e (z - a) := by
      have h := e_add a (z - a)
      rw [show a + (z - a) = z from by ring] at h
      exact h
    have hfac : e z - e a = e a * (e (z - a) - 1) := by rw [hz_eq]; ring
    have ht : ‖e (z - a) - 1‖ < min (1 / 2) (ε / 4) := by
      have h1 : ‖e a‖ * ‖e (z - a) - 1‖ < ‖e a‖ * min (1 / 2) (ε / 4) := by
        rw [hfac, norm_mul] at hcon
        exact hcon
      nlinarith [h1, hna]
    have htpos : ‖e (z - a) - 1‖ < 1 / 2 := lt_of_lt_of_le ht (min_le_left _ _)
    have htε : ‖e (z - a) - 1‖ < ε / 4 := lt_of_lt_of_le ht (min_le_right _ _)
    set t : ℂ := e (z - a) - 1 with ht_def
    have h1t : (1 : ℂ) + t = e (z - a) := by rw [ht_def]; ring
    have hexp : Complex.exp (Complex.log (1 + t))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z - a)) := by
      rw [h1t, Complex.exp_log (e_ne_zero _)]
      rfl
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    -- hk : log (1+t) = 2πi(z-a) + k*(2πi)
    have hz_k : z - a - ((-k : ℤ) : ℂ) = Complex.log (1 + t) / (2 * (Real.pi : ℂ) * Complex.I) := by
      have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Complex.I_ne_zero, Real.pi_ne_zero]
      rw [hk, Int.cast_neg]
      field_simp
      ring
    have hnorm : ‖z - a - ((-k : ℤ) : ℂ)‖ = ‖Complex.log (1 + t)‖ / (2 * Real.pi) := by
      have hden : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one]; simp
      rw [hz_k, norm_div, hden]
    have hlog2 : ‖Complex.log (1 + t)‖ < 2 * Real.pi * ε := by
      have h1 : ‖t‖ < 1 / 2 := htpos
      have h2 : ‖t‖ < ε / 4 := htε
      have hnn : 0 ≤ ‖t‖ := norm_nonneg t
      have hle := Complex.norm_log_one_add_le (show ‖t‖ < 1 by linarith)
      have h3 : (1 - ‖t‖)⁻¹ < 2 := by
        rw [inv_lt_comm₀ (by linarith) (by norm_num)]; linarith
      have h4 : ‖t‖ ^ 2 * (1 - ‖t‖)⁻¹ / 2 ≤ ‖t‖ / 2 := by
        have hP : ‖t‖ ^ 2 * (1 - ‖t‖)⁻¹ ≤ ‖t‖ ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left h3.le (sq_nonneg ‖t‖)
        have hB : ‖t‖ ^ 2 ≤ ‖t‖ / 2 := by
          nlinarith [mul_le_mul_of_nonneg_left (le_of_lt h1) hnn, sq_nonneg ‖t‖]
        linarith
      have h5 : ‖t‖ ^ 2 * (1 - ‖t‖)⁻¹ / 2 + ‖t‖ ≤ 3 * ‖t‖ / 2 := by linarith
      have h6 : 2 * ‖t‖ < 2 * Real.pi * ε := by nlinarith [Real.pi_gt_three, h2, hnn]
      have h7 : ‖Complex.log (1 + t)‖ ≤ 2 * ‖t‖ := by linarith
      linarith
    have hfin : ‖z - a - ((-k : ℤ) : ℂ)‖ < ε := by
      rw [hnorm, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [hlog2]
    exact absurd hfin (not_lt.mpr (hz (-k)))

end

end Work.FlowerGlue
