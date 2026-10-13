import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Series.Deleg.psiCmodeAux.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

/-! ## Bounds on `ψ` and on `Γ̄` near the endpoints -/

/-- `ψ` is bounded on the closed angular interval. -/
theorem psi_abs_bound {α : ℝ} {ψ : ℝ → ℝ} (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |ψ θ| ≤ M := by
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hψ.cont
  refine ⟨M, le_trans (norm_nonneg _) (hM 0 ⟨le_refl 0, by linarith [Real.pi_pos]⟩), ?_⟩
  intro θ hθ
  simpa [Real.norm_eq_abs] using hM θ hθ

/-- `|Γ̄| ≤ 45/4` on the closed angular interval for `0 < α ≤ 1`. -/
theorem GamBar_abs_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |Work.FTS.VocabO.GamBar α θ| ≤ B := by
  refine ⟨45 / 4, by norm_num, fun θ hθ => ?_⟩
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have ht0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs0 (by positivity)
  have ht1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hc1 : Real.cos θ ^ 2 ≤ 1 := by
      have h := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ); simpa using h
    have hc0 : (0:ℝ) ≤ Real.cos θ ^ 2 := by positivity
    simpa using mul_le_mul hs1 hc1 hc0 (by norm_num : (0:ℝ) ≤ 1)
  have hα3 : 0 ≤ α / 3 := by linarith
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := by
    rw [Work.Spaces.Gam]; exact Real.rpow_nonneg ht0 _
  have hGam1 : Work.Spaces.Gam α θ ≤ 1 := by
    rw [Work.Spaces.Gam]; exact Real.rpow_le_one ht0 ht1 hα3
  have hdiv : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hGam1, hc]
  have hdiv0 : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hGam0 hcpos.le
  have hsin : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  rw [Work.FTS.VocabO.GamBar]
  calc |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)|
      ≤ |Work.Spaces.Gam α θ / Work.Spaces.c α| + |5 / 4 * Real.sin (2 * θ)| := abs_sub _ _
    _ ≤ 10 + 5 / 4 := by
        rw [abs_of_nonneg hdiv0, abs_mul]
        have h54 : |(5:ℝ) / 4| = 5 / 4 := by norm_num
        rw [h54]
        linarith [mul_le_of_le_one_right (by norm_num : (0:ℝ) ≤ 5 / 4) hsin]
    _ ≤ 45 / 4 := by norm_num

/-- `|tan θ| ≤ 1` on `(0, π/4)`. -/
theorem abs_tan_le_one {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    |Real.tan θ| ≤ 1 := by
  have hθ0 : 0 < θ := hθ.1
  have hθ4 : θ < Real.pi / 4 := hθ.2
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos0 : 0 < Real.cos θ := by
    have hmem : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ0, hpi], by linarith [hθ4, hpi]⟩
    exact Real.cos_pos_of_mem_Ioo hmem
  have h1 : Real.sin θ ≤ Real.sin (Real.pi / 4) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hpi]) (by linarith [hpi]) hθ4.le
  have h2 : Real.cos (Real.pi / 4) ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hθ0.le (by linarith [hθ4, hpi]) hθ4.le
  rw [Real.sin_pi_div_four] at h1
  rw [Real.cos_pi_div_four] at h2
  have hsinle : Real.sin θ ≤ Real.cos θ := le_trans h1 h2
  have htan_nn : 0 ≤ Real.tan θ :=
    le_of_lt (Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 (by linarith [hθ4, hpi]))
  rw [abs_of_nonneg htan_nn, Real.tan_eq_sin_div_cos]
  rw [div_le_one hcos0]
  exact hsinle

/-- `|θ ψ'(θ)| ≤ C θ` for `θ ∈ (0, π/4)`. -/
theorem theta_deriv_psi_bound {α : ℝ} {ψ : ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), |θ * deriv ψ θ| ≤ C * θ := by
  obtain ⟨M, hMnn, hM⟩ := psi_abs_bound hψ
  obtain ⟨B, hBnn, hB⟩ := GamBar_abs_bound hα hα1
  refine ⟨M + (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
      + 6 * (M * (Real.pi / 4)) + B * (Real.pi / 4)), ?_, fun θ hθ => ?_⟩
  · have hpi4 : (0:ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
    have h1 : 0 ≤ |deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)| := abs_nonneg _
    have h2 : 0 ≤ M * (Real.pi / 4) := mul_nonneg hMnn hpi4.le
    have h3 : 0 ≤ B * (Real.pi / 4) := mul_nonneg hBnn hpi4.le
    linarith
  · have h4 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
    have hθmem : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
    have hform := psi_deriv_tan_form_le (ψ := ψ) hψ hθ.1 hθ.2.le h4
    rw [Real.tan_pi_div_four, one_mul] at hform
    have hpi4pos : (0:ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
    have hI1 : |∫ s in θ..(Real.pi / 4), ψ s| ≤ M * (Real.pi / 4) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := ψ) (a := θ)
        (b := Real.pi / 4) (C := M) (fun x hx => by
          rw [Set.uIoc_of_le hθ.2.le] at hx
          rw [Real.norm_eq_abs]
          exact hM x ⟨le_trans hθ.1.le hx.1.le, by linarith [hx.2, hθ.2]⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ.2.le)] at h
      nlinarith [h, hMnn, hθ.1]
    have hI2 : |∫ s in θ..(Real.pi / 4), Work.FTS.VocabO.GamBar α s| ≤ B * (Real.pi / 4) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := Work.FTS.VocabO.GamBar α) (a := θ) (b := Real.pi / 4) (C := B) (fun x hx => by
          rw [Set.uIoc_of_le hθ.2.le] at hx
          rw [Real.norm_eq_abs]
          exact hB x ⟨le_trans hθ.1.le hx.1.le, by linarith [hx.2, hθ.2]⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ.2.le)] at h
      nlinarith [h, hBnn, hθ.1]
    have hkey : deriv ψ θ = Real.tan θ * ψ θ + (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
        + 6 * (∫ s in θ..(Real.pi / 4), ψ s)
        + ∫ s in θ..(Real.pi / 4), Work.FTS.VocabO.GamBar α s) := by linarith [hform]
    have htan : |Real.tan θ| ≤ 1 := abs_tan_le_one hθ
    have hpt : |deriv ψ θ| ≤ M + (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
        + 6 * (M * (Real.pi / 4)) + B * (Real.pi / 4)) := by
      rw [hkey]
      have h1 : |Real.tan θ * ψ θ| ≤ M := by
        rw [abs_mul]
        exact le_trans (mul_le_of_le_one_left (abs_nonneg _) htan) (hM θ hθmem)
      have h2 : |deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
          + 6 * (∫ s in θ..(Real.pi / 4), ψ s)
          + ∫ s in θ..(Real.pi / 4), Work.FTS.VocabO.GamBar α s|
          ≤ |deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)| + 6 * (M * (Real.pi / 4))
            + B * (Real.pi / 4) := by
        have h0 := abs_add_le (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
            + 6 * (∫ s in θ..(Real.pi / 4), ψ s))
          (∫ s in θ..(Real.pi / 4), Work.FTS.VocabO.GamBar α s)
        have h3 := abs_add_le (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4))
          (6 * (∫ s in θ..(Real.pi / 4), ψ s))
        have h4' : |6 * (∫ s in θ..(Real.pi / 4), ψ s)| ≤ 6 * (M * (Real.pi / 4)) := by
          rw [abs_mul]
          have : |(6:ℝ)| = 6 := by norm_num
          rw [this]
          exact mul_le_mul_of_nonneg_left hI1 (by norm_num)
        linarith [h0, h3, h4']
      calc |Real.tan θ * ψ θ + (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
            + 6 * (∫ s in θ..(Real.pi / 4), ψ s)
            + ∫ s in θ..(Real.pi / 4), Work.FTS.VocabO.GamBar α s)|
          ≤ |Real.tan θ * ψ θ| + |deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
            + 6 * (∫ s in θ..(Real.pi / 4), ψ s)
            + ∫ s in θ..(Real.pi / 4), Work.FTS.VocabO.GamBar α s| := abs_add_le _ _
        _ ≤ M + (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)| + 6 * (M * (Real.pi / 4))
            + B * (Real.pi / 4)) := add_le_add h1 h2
    rw [abs_mul, abs_of_pos hθ.1]
    calc θ * |deriv ψ θ|
        ≤ θ * (M + (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
            + 6 * (M * (Real.pi / 4)) + B * (Real.pi / 4))) :=
          mul_le_mul_of_nonneg_left hpt hθ.1.le
      _ = (M + (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
            + 6 * (M * (Real.pi / 4)) + B * (Real.pi / 4))) * θ := by ring

/-- `|ψ(θ)| ≤ C θ` for `θ ∈ (0, π/4)`: the fundamental theorem of calculus applied to
`ψ θ - ψ 0 = ∫_0^θ ψ'` together with the boundedness of `ψ'` near `0`. -/
theorem psi_linear_bound {α : ℝ} {ψ : ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), |ψ θ| ≤ C * θ := by
  obtain ⟨C, hCnn, hC⟩ := theta_deriv_psi_bound hα hα1 hψ
  refine ⟨C, hCnn, fun θ hθ => ?_⟩
  have hsubIcc : Set.Icc (0:ℝ) θ ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, hθ.2, Real.pi_pos]⟩
  have hsubIoo : Set.Ioo (0:ℝ) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, hθ.2, Real.pi_pos]⟩
  have hsm : ContDiffOn ℝ 2 ψ (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hψ.smooth.of_le (by simp [Work.Stability.smoothOrder])
  have hcont : ContinuousOn ψ (Set.Icc 0 θ) := hψ.cont.mono hsubIcc
  have hder : ∀ x ∈ Set.Ioo (0:ℝ) θ, HasDerivAt ψ (deriv ψ x) x := by
    intro x hx
    have hm : Set.Ioo (0:ℝ) (Real.pi / 2) ∈ 𝓝 x :=
      isOpen_Ioo.mem_nhds (hsubIoo hx)
    exact (((hsm.contDiffAt hm).differentiableAt (by norm_num))).hasDerivAt
  have hbd : ∀ x ∈ Set.Ioc (0:ℝ) θ, |deriv ψ x| ≤ C := by
    intro x hx
    have hx1 := hC x ⟨hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    rw [abs_mul, abs_of_pos hx.1] at hx1
    have hx1' : x * |deriv ψ x| ≤ x * C := by
      rw [mul_comm C x] at hx1
      exact hx1
    exact le_of_mul_le_mul_left hx1' hx.1
  have hd1 : ContDiffOn ℝ 1 (deriv ψ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo
      (by norm_num : ((1:ℕ∞) : WithTop ℕ∞) + 1 ≤ ((2:ℕ∞) : WithTop ℕ∞))
  have hint : IntervalIntegrable (deriv ψ) volume 0 θ :=
    Work.Elliptic.intervalIntegrable_of_continuousOn_Ioo_of_bound hθ.1.le
      (hd1.continuousOn.mono hsubIoo) C (fun x hx => hbd x ⟨hx.1, hx.2.le⟩)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1.le hcont hder hint
  rw [hψ.bdry0, sub_zero] at hFTC
  rw [← hFTC]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := deriv ψ) (a := 0)
    (b := θ) (C := C) (fun x hx => by
      rw [Set.uIoc_of_le hθ.1.le] at hx
      rw [Real.norm_eq_abs]
      exact hbd x hx)
  rwa [Real.norm_eq_abs, sub_zero, abs_of_pos hθ.1] at h

/-- `|cos²θ ψ'(θ)| ≤ C |cos θ|` for `θ ∈ (π/4, π/2)`. -/
theorem cos_sq_deriv_psi_bound {α : ℝ} {ψ : ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |Real.cos θ ^ 2 * deriv ψ θ| ≤ C * |Real.cos θ| := by
  obtain ⟨M, hMnn, hM⟩ := psi_abs_bound hψ
  obtain ⟨B, hBnn, hB⟩ := GamBar_abs_bound hα hα1
  refine ⟨M + (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
      + 6 * (M * (Real.pi / 2)) + B * (Real.pi / 2)), ?_, fun θ hθ => ?_⟩
  · have h1 : 0 ≤ M * (Real.pi / 2) := mul_nonneg hMnn (by linarith [Real.pi_pos])
    have h2 : 0 ≤ B * (Real.pi / 2) := mul_nonneg hBnn (by linarith [Real.pi_pos])
    linarith [abs_nonneg (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4))]
  · have h4 : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
    have hform := psi_deriv_tan_form (ψ := ψ) hψ h4 (by linarith [Real.pi_pos])
      (by linarith [hθ.1, Real.pi_pos]) hθ.2
    rw [Real.tan_pi_div_four, one_mul] at hform
    have hI1 : |∫ s in (Real.pi / 4)..θ, ψ s| ≤ M * (Real.pi / 2) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := ψ) (a := Real.pi / 4)
        (b := θ) (C := M) (fun x hx => by
          rw [Set.uIoc_of_le hθ.1.le] at hx
          rw [Real.norm_eq_abs]
          exact hM x ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ.1.le)] at h
      nlinarith [h, hMnn, hθ.2]
    have hI2 : |∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s| ≤ B * (Real.pi / 2) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := Work.FTS.VocabO.GamBar α) (a := Real.pi / 4) (b := θ) (C := B) (fun x hx => by
          rw [Set.uIoc_of_le hθ.1.le] at hx
          rw [Real.norm_eq_abs]
          exact hB x ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ.1.le)] at h
      nlinarith [h, hBnn, hθ.2]
    have hkey : deriv ψ θ = Real.tan θ * ψ θ + (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
        - 6 * (∫ s in (Real.pi / 4)..θ, ψ s)
        - ∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s) := by linarith [hform]
    have hcos0 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hψb : |ψ θ| ≤ M := hM θ ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
    have hc2 : Real.cos θ ^ 2 ≤ |Real.cos θ| := by
      rw [abs_of_pos hcos0]; nlinarith [hcos0, Real.cos_le_one θ]
    have hstep : Real.cos θ ^ 2 * deriv ψ θ
        = Real.sin θ * Real.cos θ * ψ θ
          + Real.cos θ ^ 2 * (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
            - 6 * (∫ s in (Real.pi / 4)..θ, ψ s)
            - ∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s) := by
      have htan' : Real.cos θ ^ 2 * (Real.tan θ * ψ θ) = Real.sin θ * Real.cos θ * ψ θ := by
        rw [Real.tan_eq_sin_div_cos]; field_simp
      calc Real.cos θ ^ 2 * deriv ψ θ
          = Real.cos θ ^ 2 * (Real.tan θ * ψ θ
              + (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
                - 6 * (∫ s in (Real.pi / 4)..θ, ψ s)
                - ∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s)) := by rw [hkey]
        _ = Real.cos θ ^ 2 * (Real.tan θ * ψ θ)
              + Real.cos θ ^ 2 * (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
                - 6 * (∫ s in (Real.pi / 4)..θ, ψ s)
                - ∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s) := by ring
        _ = Real.sin θ * Real.cos θ * ψ θ
              + Real.cos θ ^ 2 * (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
                - 6 * (∫ s in (Real.pi / 4)..θ, ψ s)
                - ∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s) := by rw [htan']
    have h2 : |deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
        - 6 * (∫ s in (Real.pi / 4)..θ, ψ s)
        - ∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s|
        ≤ |deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)| + 6 * (M * (Real.pi / 2))
          + B * (Real.pi / 2) := by
      have h0 := abs_sub (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
          - 6 * (∫ s in (Real.pi / 4)..θ, ψ s))
        (∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s)
      have h3 := abs_sub (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4))
        (6 * (∫ s in (Real.pi / 4)..θ, ψ s))
      have h4' : |6 * (∫ s in (Real.pi / 4)..θ, ψ s)| ≤ 6 * (M * (Real.pi / 2)) := by
        rw [abs_mul]
        have : |(6:ℝ)| = 6 := by norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_left hI1 (by norm_num)
      linarith [h0, h3, h4']
    have hRnn : 0 ≤ |deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
        + 6 * (M * (Real.pi / 2)) + B * (Real.pi / 2) := by
      have h1 : 0 ≤ M * (Real.pi / 2) := mul_nonneg hMnn (by linarith [Real.pi_pos])
      have h2' : 0 ≤ B * (Real.pi / 2) := mul_nonneg hBnn (by linarith [Real.pi_pos])
      linarith [abs_nonneg (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4))]
    have hfinal : |Real.cos θ ^ 2 * deriv ψ θ| ≤ (M + (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
        + 6 * (M * (Real.pi / 2)) + B * (Real.pi / 2))) * |Real.cos θ| := by
      rw [hstep]
      calc |Real.sin θ * Real.cos θ * ψ θ
            + Real.cos θ ^ 2 * (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
              - 6 * (∫ s in (Real.pi / 4)..θ, ψ s)
              - ∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s)|
          ≤ |Real.sin θ * Real.cos θ * ψ θ|
            + |Real.cos θ ^ 2 * (deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
              - 6 * (∫ s in (Real.pi / 4)..θ, ψ s)
              - ∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s)| := abs_add_le _ _
        _ ≤ M * |Real.cos θ| + (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
              + 6 * (M * (Real.pi / 2)) + B * (Real.pi / 2)) * |Real.cos θ| := by
            apply add_le_add
            · rw [abs_mul, abs_mul]
              have hs1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
              have h1 : |Real.sin θ| * |Real.cos θ| ≤ |Real.cos θ| :=
                mul_le_of_le_one_left (abs_nonneg _) hs1
              calc |Real.sin θ| * |Real.cos θ| * |ψ θ|
                  ≤ |Real.cos θ| * M := mul_le_mul h1 hψb (abs_nonneg _) (abs_nonneg _)
                _ = M * |Real.cos θ| := by ring
            · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
              calc Real.cos θ ^ 2 * |deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)
                    - 6 * (∫ s in (Real.pi / 4)..θ, ψ s)
                    - ∫ s in (Real.pi / 4)..θ, Work.FTS.VocabO.GamBar α s|
                  ≤ |Real.cos θ| * (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
                    + 6 * (M * (Real.pi / 2)) + B * (Real.pi / 2)) :=
                    mul_le_mul hc2 h2 (abs_nonneg _) (abs_nonneg (Real.cos θ))
                _ = (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
                    + 6 * (M * (Real.pi / 2)) + B * (Real.pi / 2)) * |Real.cos θ| := by ring
        _ = (M + (|deriv ψ (Real.pi / 4) - ψ (Real.pi / 4)|
              + 6 * (M * (Real.pi / 2)) + B * (Real.pi / 2))) * |Real.cos θ| := by ring
    exact hfinal


end Work.FTS.PhiStar.Series.Deleg
