import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

/-- The real part of the lifted coordinate `log z / (2πi)` is a principal argument over `2π`,
hence lands in `(-1/2, 1/2]`. -/
lemma lift_re_abs_le (z : ℂ) : |(Complex.log z / (2 * Real.pi * I)).re| ≤ 1 / 2 := by
  have hcalc : (Complex.log z / (2 * Real.pi * I)).re = Complex.arg z / (2 * Real.pi) := by
    rw [Complex.div_re, Complex.log_re, Complex.log_im]
    have h1 : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
    have h2 : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by simp
    have h3 : Complex.normSq (2 * (Real.pi : ℂ) * Complex.I) = (2 * Real.pi) ^ 2 := by
      rw [Complex.normSq_apply, h1, h2]; ring
    rw [h1, h2, h3]
    field_simp
    ring
  rw [hcalc, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have h := Complex.abs_arg_le_pi z
  nlinarith [Real.pi_pos]

/-- A point whose real part is bounded by `1/2` and whose imaginary part is bounded by `y` has
modulus at most `sqrt(1/4 + y²)`. -/
lemma lift_norm_le (w : ℂ) (y : ℝ) (hre : |w.re| ≤ 1 / 2) (him : |w.im| ≤ y) :
    ‖w‖ ≤ Real.sqrt (1 / 4 + y ^ 2) := by
  have h2 : ‖w‖ ^ 2 ≤ 1 / 4 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [abs_le.mp hre, abs_le.mp him]
  calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
    _ ≤ Real.sqrt (1 / 4 + y ^ 2) := Real.sqrt_le_sqrt h2

theorem lift_cover {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (hd : HornData d)
    (s : ℂ) (hs : s ≠ 0) (L : Set ℂ) (hLc : IsCompact L)
    (hL : ∀ ζ ∈ L, ζ ≠ 0 → ζ / s ∈ piExp '' (hd.Bu ∪ hd.Bl)) (y : ℝ) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ d.DE ∧
      ∀ ζ ∈ L, ζ ≠ 0 → Complex.log (ζ / s) / (2 * Real.pi * I) ∈ K ∨
        y ≤ |(Complex.log (ζ / s) / (2 * Real.pi * I)).im| := by
  have hcont : Continuous piExp := by unfold piExp; fun_prop
  set Ls : Set ℂ := (fun ζ : ℂ => ζ / s) '' L with hLs
  have hLs_c : IsCompact Ls := hLc.image (by fun_prop)
  refine ⟨closedBall 0 (Real.sqrt (1 / 4 + y ^ 2) + 1) ∩ piExp ⁻¹' Ls, ?_, ?_, ?_⟩
  · exact (isCompact_closedBall 0 _).inter_right (hLs_c.isClosed.preimage hcont)
  · -- every point whose `π`-image lies in `L/s` is in `DE`, by `T`-invariance of `Bu`, `Bl`
    intro w hw
    rw [Set.mem_inter_iff] at hw
    obtain ⟨-, hwp⟩ := hw
    rw [Set.mem_preimage, hLs] at hwp
    obtain ⟨ζ, hζL, hζeq⟩ := hwp
    change ζ / s = piExp w at hζeq
    have hζne : ζ ≠ 0 := by
      intro h
      have : piExp w = 0 := by rw [← hζeq, h]; simp
      exact Work.Horn.MandelDim.piExp_ne_zero w this
    obtain ⟨u, hu, hueq⟩ := hL ζ hζL hζne
    have huw : piExp u = piExp w := by rw [hueq, hζeq]
    obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp huw
    have hw_eq : w = u + ((-k : ℤ) : ℂ) := by
      rw [hk]; push_cast; ring
    rcases hu with hu | hu
    · rw [hw_eq]
      exact hd.sub (Or.inl (Work.Horn.MandelDim.IsTInvariant.add_int hd.Bu_T hu (-k)))
    · rw [hw_eq]
      exact hd.sub (Or.inr (Work.Horn.MandelDim.IsTInvariant.add_int hd.Bl_T hu (-k)))
  · intro ζ hζL hζne
    have hz_ne : ζ / s ≠ 0 := div_ne_zero hζne hs
    have hpi : piExp (Complex.log (ζ / s) / (2 * Real.pi * I)) = ζ / s :=
      Work.Horn.MandelDim.piExp_log_div (ζ / s) hz_ne
    by_cases hy : |(Complex.log (ζ / s) / (2 * Real.pi * I)).im| ≤ y
    · left
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_trans (lift_norm_le _ y (lift_re_abs_le (ζ / s)) hy)
          (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
      · rw [Set.mem_preimage, hpi, hLs]
        exact ⟨ζ, hζL, rfl⟩
    · right
      exact (not_le.mp hy).le

end Work.Repel
