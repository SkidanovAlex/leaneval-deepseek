import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.sliceIBPLight
import Submission.Work.FTS.EllipticEst.TT.SliceIbpLightAux
import Submission.Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

/-! ## Helpers: the within-derivatives on `Iθ` and their continuity on the open interval -/

private lemma uniqueDiffOn_Iθ' : UniqueDiffOn ℝ Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact uniqueDiffOn_Icc (by positivity : (0 : ℝ) < Real.pi / 2)

private lemma Iθ_mem_nhds' {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.Iθ ∈ 𝓝 θ := by
  rw [Work.Spaces.Iθ]
  exact Icc_mem_nhds hθ.1 hθ.2

/-- For `f` of class `C²` on the closed interval, `deriv f` and `deriv (deriv f)` are
continuous on the *open* interval (they agree there with the corresponding within
derivatives, which are continuous on `Iθ`). -/
private lemma continuousOn_deriv_Ioo' {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f Work.Spaces.Iθ) :
    ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
      ContinuousOn (deriv (deriv f)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h1 : ContinuousOn (derivWithin f Work.Spaces.Iθ) Work.Spaces.Iθ :=
    hf.continuousOn_derivWithin uniqueDiffOn_Iθ' (by norm_num)
  have h2 : ContDiffOn ℝ 1 (derivWithin f Work.Spaces.Iθ) Work.Spaces.Iθ :=
    hf.derivWithin uniqueDiffOn_Iθ' (by norm_num)
  have h3 : ContinuousOn (derivWithin (derivWithin f Work.Spaces.Iθ) Work.Spaces.Iθ)
      Work.Spaces.Iθ :=
    h2.continuousOn_derivWithin uniqueDiffOn_Iθ' (by norm_num)
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact Ioo_subset_Icc_self
  refine ⟨?_, ?_⟩
  · refine (h1.mono hsub).congr (fun θ hθ => ?_)
    exact (derivWithin_of_mem_nhds (Iθ_mem_nhds' hθ)).symm
  · refine (h3.mono hsub).congr (fun θ hθ => ?_)
    have hcongr : (fun x : ℝ => deriv f x) =ᶠ[𝓝 θ]
        (fun x : ℝ => derivWithin f Work.Spaces.Iθ x) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hθ] with x hx
      exact (derivWithin_of_mem_nhds (Iθ_mem_nhds' hx)).symm
    exact (hcongr.deriv_eq).trans (derivWithin_of_mem_nhds (Iθ_mem_nhds' hθ)).symm

/-- On the open angular interval, `|sin(2θ)^a| ≤ 1` for `a > 0`. -/
private lemma abs_sigR_le_one {a θ : ℝ} (ha0 : 0 < a)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : |sigR a θ| ≤ 1 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [sigR_apply, abs_of_nonneg (Real.rpow_nonneg hs0 a)]
  exact Real.rpow_le_one hs0 (Real.sin_le_one _) ha0.le

/-- The fact that `θ ↦ sin(2θ)` is continuous on the open angular interval. -/
private lemma continuousOn_sin_two :
    ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  Real.continuous_sin.comp_continuousOn
    ((continuous_const : Continuous fun _ : ℝ => (2 : ℝ)).mul continuous_id).continuousOn

/-! ## The analytic side conditions of `slice_ibp_light`:

integrability of the five integrands and vanishing of the two boundary products. -/

/-- **Integrability of the five integrands.**  For `f` of class `C²` on `Iθ` vanishing at
both endpoints and `0 < a < 1`, the five integrands of `slice_ibp_light` are integrable on
`Iθ`.  (Each is continuous on the open interval and bounded there, with bounds provided by
`slice_a_priori_bounds` and Jordan's inequality.) -/
theorem slice_ibp_light_integrable (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f Work.Spaces.Iθ) (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    MeasureTheory.IntegrableOn (fun θ => deriv f θ ^ 2 * sigR a θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => f θ * deriv (deriv f) θ * sigR a θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => f θ * deriv f θ * sigDR a θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * sigR a θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (a - 2)) Work.Spaces.Iθ := by
  obtain ⟨C, hC0, hd1, hd2, hff1, hff2⟩ :=
    Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds f hf h0 h1
  obtain ⟨hcont1, hcont2⟩ := continuousOn_deriv_Ioo' hf
  have hfcont : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine hf.continuousOn.mono ?_
    rw [Work.Spaces.Iθ]; exact Ioo_subset_Icc_self
  have hsIoo : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_sin_two
  have hcosIoo : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_cos.comp_continuousOn
      ((continuous_const : Continuous fun _ : ℝ => (2 : ℝ)).mul continuous_id).continuousOn
  have hsin_pos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsin_nonneg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => (hsin_pos θ hθ).le
  have hsigR_cont : ContinuousOn (fun θ : ℝ => sigR a θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simpa only [sigR_apply] using
      hsIoo.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hsigDR_cont : ContinuousOn (fun θ : ℝ => sigDR a θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hp : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (a - 1))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hsIoo.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
    refine ContinuousOn.congr ((hcosIoo.const_mul (2 * a)).mul hp) (fun θ _ => ?_)
    simp only [Pi.mul_apply, sigDR_apply]
  have hsinpow_cont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (a - 2))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsIoo.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  -- the five pointwise bounds
  have hb1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv f θ ^ 2 * sigR a θ| ≤ C ^ 2 := by
    intro θ hθ
    have h1 : |deriv f θ| ≤ C := hd1 θ hθ
    have h2 : |sigR a θ| ≤ 1 := abs_sigR_le_one ha0 hθ
    have hsq : deriv f θ ^ 2 ≤ C ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (deriv f θ)) h1 2
      rwa [sq_abs] at h
    have habs : |deriv f θ ^ 2 * sigR a θ| = deriv f θ ^ 2 * |sigR a θ| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ))]
    rw [habs]
    calc deriv f θ ^ 2 * |sigR a θ| ≤ C ^ 2 * 1 :=
          mul_le_mul hsq h2 (abs_nonneg _) (sq_nonneg C)
      _ = C ^ 2 := by ring
  have hb2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ * deriv (deriv f) θ * sigR a θ| ≤ C ^ 2 * (Real.pi / 2) := by
    intro θ hθ
    have hmem : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hfB : |f θ| ≤ C * (Real.pi / 2) :=
      le_trans (hff2 θ hmem) (mul_le_mul_of_nonneg_left (by linarith [hθ.1]) hC0)
    have h1 : |deriv (deriv f) θ| ≤ C := hd2 θ hθ
    have h2 : |sigR a θ| ≤ 1 := abs_sigR_le_one ha0 hθ
    have habs : |f θ * deriv (deriv f) θ * sigR a θ|
        = |f θ| * |deriv (deriv f) θ| * |sigR a θ| := by rw [abs_mul, abs_mul]
    rw [habs]
    calc |f θ| * |deriv (deriv f) θ| * |sigR a θ| ≤ (C * (Real.pi / 2)) * C * 1 := by
          have h12 : |f θ| * |deriv (deriv f) θ| ≤ (C * (Real.pi / 2)) * C :=
            mul_le_mul hfB h1 (abs_nonneg _) (by positivity)
          exact mul_le_mul h12 h2 (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (Real.pi / 2) := by ring
  have hb3 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ * deriv f θ * sigDR a θ|
        ≤ 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1) * (Real.pi / 2) ^ a := by
    intro θ hθ
    set m := min θ (Real.pi / 2 - θ) with hm
    have hmpos : 0 < m := by rw [hm]; exact lt_min hθ.1 (by linarith [hθ.2])
    have hmle : m ≤ Real.pi / 2 := by
      rw [hm]; exact le_trans (min_le_right _ _) (by linarith [hθ.1])
    have hfm : |f θ| ≤ C * m := by
      rw [hm]
      rcases le_total θ (Real.pi / 2 - θ) with h | h
      · rw [min_eq_left h]; exact hff1 θ ⟨hθ.1.le, hθ.2.le⟩
      · rw [min_eq_right h]; exact hff2 θ ⟨hθ.1.le, hθ.2.le⟩
    have hd : |deriv f θ| ≤ C := hd1 θ hθ
    have h4pos : (0 : ℝ) < 4 / Real.pi := by positivity
    have hjord : (4 / Real.pi) * m ≤ Real.sin (2 * θ) := by
      rw [hm]; exact four_div_pi_mul_min_le_sin_two ⟨hθ.1.le, hθ.2.le⟩
    have hes : (Real.sin (2 * θ)) ^ (a - 1) ≤ ((4 / Real.pi) * m) ^ (a - 1) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos h4pos hmpos) hjord (by linarith)
    have hsplit : ((4 / Real.pi) * m) ^ (a - 1)
        = (4 / Real.pi) ^ (a - 1) * m ^ (a - 1) := Real.mul_rpow h4pos.le hmpos.le
    have hmma : m * m ^ (a - 1) = m ^ a := by
      have h1 : m ^ a = m ^ (1 + (a - 1)) := by congr 1; ring
      rw [h1, Real.rpow_add hmpos, Real.rpow_one]
    have hosp : 0 ≤ (Real.sin (2 * θ)) ^ (a - 1) :=
      Real.rpow_nonneg (hsin_nonneg θ hθ) _
    have hsDR : |sigDR a θ| ≤ 2 * a * ((4 / Real.pi) * m) ^ (a - 1) := by
      rw [sigDR_apply, abs_mul, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 * a by positivity),
        abs_of_nonneg (Real.rpow_nonneg (hsin_nonneg θ hθ) _)]
      have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
      have h1 : 2 * a * |Real.cos (2 * θ)| ≤ 2 * a * 1 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
      calc 2 * a * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (a - 1)
          ≤ 2 * a * 1 * ((4 / Real.pi) * m) ^ (a - 1) :=
            mul_le_mul h1 hes hosp (by positivity)
        _ = 2 * a * ((4 / Real.pi) * m) ^ (a - 1) := by ring
    have habs : |f θ * deriv f θ * sigDR a θ| = |f θ| * |deriv f θ| * |sigDR a θ| := by
      rw [abs_mul, abs_mul]
    rw [habs]
    calc |f θ| * |deriv f θ| * |sigDR a θ|
        ≤ (C * m) * C * (2 * a * ((4 / Real.pi) * m) ^ (a - 1)) :=
          mul_le_mul (mul_le_mul hfm hd (abs_nonneg _) (by positivity)) hsDR
            (abs_nonneg _) (by positivity)
      _ = 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1) * (m * m ^ (a - 1)) := by
          rw [hsplit]; ring
      _ = 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1) * m ^ a := by rw [hmma]
      _ ≤ 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1) * (Real.pi / 2) ^ a :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hmpos.le hmle ha0.le)
            (by positivity)
  have hb4 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ ^ 2 * sigR a θ| ≤ C ^ 2 * (Real.pi / 2) ^ 2 := by
    intro θ hθ
    have hmem : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hfB : |f θ| ≤ C * (Real.pi / 2) :=
      le_trans (hff2 θ hmem) (mul_le_mul_of_nonneg_left (by linarith [hθ.1]) hC0)
    have hsq : f θ ^ 2 ≤ (C * (Real.pi / 2)) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (f θ)) hfB 2
      rwa [sq_abs] at h
    have h2 : |sigR a θ| ≤ 1 := abs_sigR_le_one ha0 hθ
    have habs : |f θ ^ 2 * sigR a θ| = f θ ^ 2 * |sigR a θ| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ))]
    rw [habs]
    calc f θ ^ 2 * |sigR a θ| ≤ (C * (Real.pi / 2)) ^ 2 * 1 :=
          mul_le_mul hsq h2 (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (Real.pi / 2) ^ 2 := by ring
  have hb5 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2)|
        ≤ C ^ 2 * (4 / Real.pi) ^ (a - 2) * (Real.pi / 2) ^ a := by
    intro θ hθ
    set m := min θ (Real.pi / 2 - θ) with hm
    have hmpos : 0 < m := by rw [hm]; exact lt_min hθ.1 (by linarith [hθ.2])
    have hmle : m ≤ Real.pi / 2 := by
      rw [hm]; exact le_trans (min_le_right _ _) (by linarith [hθ.1])
    have hfm : |f θ| ≤ C * m := by
      rw [hm]
      rcases le_total θ (Real.pi / 2 - θ) with h | h
      · rw [min_eq_left h]; exact hff1 θ ⟨hθ.1.le, hθ.2.le⟩
      · rw [min_eq_right h]; exact hff2 θ ⟨hθ.1.le, hθ.2.le⟩
    have h4pos : (0 : ℝ) < 4 / Real.pi := by positivity
    have hjord : (4 / Real.pi) * m ≤ Real.sin (2 * θ) := by
      rw [hm]; exact four_div_pi_mul_min_le_sin_two ⟨hθ.1.le, hθ.2.le⟩
    have hes : (Real.sin (2 * θ)) ^ (a - 2) ≤ ((4 / Real.pi) * m) ^ (a - 2) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos h4pos hmpos) hjord (by linarith)
    have hsplit : ((4 / Real.pi) * m) ^ (a - 2)
        = (4 / Real.pi) ^ (a - 2) * m ^ (a - 2) := Real.mul_rpow h4pos.le hmpos.le
    have hmm2 : m ^ 2 * m ^ (a - 2) = m ^ a := by
      rw [← Real.rpow_natCast m 2, ← Real.rpow_add hmpos]
      congr 1
      ring
    have hsq : f θ ^ 2 ≤ (C * m) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (f θ)) hfm 2
      rwa [sq_abs] at h
    have hcos2 : Real.cos (2 * θ) ^ 2 ≤ 1 := by
      have h := pow_le_one₀ (n := 2) (abs_nonneg (Real.cos (2 * θ))) (Real.abs_cos_le_one _)
      rwa [sq_abs] at h
    have habs : |f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2)|
        = f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
        abs_of_nonneg (sq_nonneg (Real.cos (2 * θ))),
        abs_of_nonneg (Real.rpow_nonneg (hsin_nonneg θ hθ) _)]
    rw [habs]
    have h3 : (Real.sin (2 * θ)) ^ (a - 2) ≤ (4 / Real.pi) ^ (a - 2) * m ^ (a - 2) := by
      rw [← hsplit]; exact hes
    calc f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2)
        ≤ (C * m) ^ 2 * 1 * ((4 / Real.pi) ^ (a - 2) * m ^ (a - 2)) :=
          mul_le_mul (mul_le_mul hsq hcos2 (by positivity) (by positivity)) h3
            (Real.rpow_nonneg (hsin_nonneg θ hθ) _) (by positivity)
      _ = C ^ 2 * (4 / Real.pi) ^ (a - 2) * (m ^ 2 * m ^ (a - 2)) := by ring
      _ = C ^ 2 * (4 / Real.pi) ^ (a - 2) * m ^ a := by rw [hmm2]
      _ ≤ C ^ 2 * (4 / Real.pi) ^ (a - 2) * (Real.pi / 2) ^ a :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hmpos.le hmle ha0.le)
            (by positivity)
  exact ⟨integrableOn_Iθ_of_continuousOn_Ioo_of_abs_le (K := C ^ 2)
      ((hcont1.pow 2).mul hsigR_cont) hb1,
    integrableOn_Iθ_of_continuousOn_Ioo_of_abs_le (K := C ^ 2 * (Real.pi / 2))
      ((hfcont.mul hcont2).mul hsigR_cont) hb2,
    integrableOn_Iθ_of_continuousOn_Ioo_of_abs_le
      (K := 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1) * (Real.pi / 2) ^ a)
      ((hfcont.mul hcont1).mul hsigDR_cont) hb3,
    integrableOn_Iθ_of_continuousOn_Ioo_of_abs_le (K := C ^ 2 * (Real.pi / 2) ^ 2)
      ((hfcont.pow 2).mul hsigR_cont) hb4,
    integrableOn_Iθ_of_continuousOn_Ioo_of_abs_le
      (K := C ^ 2 * (4 / Real.pi) ^ (a - 2) * (Real.pi / 2) ^ a)
      (((hfcont.pow 2).mul (hcosIoo.pow 2)).mul hsinpow_cont) hb5⟩

/-- **Vanishing of the two boundary products.**  For `f` of class `C²` on `Iθ` vanishing at
both endpoints, the products `f f' σ` and `f² σ'` tend to `0` at `0⁺` and at `(π/2)⁻`. -/
theorem slice_ibp_light_boundary_aux (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f Work.Spaces.Iθ) (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    Filter.Tendsto (fun t : ℝ => f t * deriv f t * sigR a t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun t : ℝ => f t * deriv f t * sigR a t)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
    Filter.Tendsto (fun t : ℝ => f t ^ 2 * sigDR a t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun t : ℝ => f t ^ 2 * sigDR a t)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨C, hC0, hd1, _, hff1, hff2⟩ :=
    Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds f hf h0 h1
  have h4pos : (0 : ℝ) < 4 / Real.pi := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine tendsto_zero_of_abs_le_mul_rpow_left (K := C ^ 2) (r := 1) (by norm_num) ?_
    intro θ hθ
    have hθ2 : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hfθ : |f θ| ≤ C * θ := hff1 θ ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
    have hdθ : |deriv f θ| ≤ C := hd1 θ hθ2
    have hs : |sigR a θ| ≤ 1 := abs_sigR_le_one ha0 hθ2
    have habs : |f θ * deriv f θ * sigR a θ| = |f θ| * |deriv f θ| * |sigR a θ| := by
      rw [abs_mul, abs_mul]
    rw [habs, Real.rpow_one]
    calc |f θ| * |deriv f θ| * |sigR a θ| ≤ (C * θ) * C * 1 := by
          have h12 : |f θ| * |deriv f θ| ≤ (C * θ) * C :=
            mul_le_mul hfθ hdθ (abs_nonneg _) (mul_nonneg hC0 hθ.1.le)
          exact mul_le_mul h12 hs (abs_nonneg _) (mul_nonneg (mul_nonneg hC0 hθ.1.le) hC0)
      _ = C ^ 2 * θ := by ring
  · refine tendsto_zero_of_abs_le_mul_sub_rpow_right (K := C ^ 2) (r := 1) (by norm_num) ?_
    intro θ hθ
    set δ := Real.pi / 2 - θ with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith [hθ.2]
    have hθpos : 0 < θ := by linarith [hθ.1, Real.pi_pos]
    have hθ2 : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθpos, hθ.2⟩
    have hfθ : |f θ| ≤ C * δ := by rw [hδ]; exact hff2 θ ⟨hθpos.le, hθ.2.le⟩
    have hdθ : |deriv f θ| ≤ C := hd1 θ hθ2
    have hs : |sigR a θ| ≤ 1 := abs_sigR_le_one ha0 hθ2
    have habs : |f θ * deriv f θ * sigR a θ| = |f θ| * |deriv f θ| * |sigR a θ| := by
      rw [abs_mul, abs_mul]
    rw [habs, Real.rpow_one]
    calc |f θ| * |deriv f θ| * |sigR a θ| ≤ (C * δ) * C * 1 := by
          have h12 : |f θ| * |deriv f θ| ≤ (C * δ) * C :=
            mul_le_mul hfθ hdθ (abs_nonneg _) (mul_nonneg hC0 hδpos.le)
          exact mul_le_mul h12 hs (abs_nonneg _) (mul_nonneg (mul_nonneg hC0 hδpos.le) hC0)
      _ = C ^ 2 * δ := by ring
  · refine tendsto_zero_of_abs_le_mul_rpow_left (K := 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1))
      (r := a + 1) (by linarith) ?_
    intro θ hθ
    have hθ2 : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hsinθ_nn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hfθ : |f θ| ≤ C * θ := hff1 θ ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
    have hj : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) :=
      four_div_pi_mul_le_sin_two hθ.1.le hθ.2.le
    have hes : (Real.sin (2 * θ)) ^ (a - 1) ≤ ((4 / Real.pi) * θ) ^ (a - 1) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos h4pos hθ.1) hj (by linarith)
    have hsinp : 0 ≤ (Real.sin (2 * θ)) ^ (a - 1) := Real.rpow_nonneg hsinθ_nn _
    have hsDR : |sigDR a θ| ≤ 2 * a * ((4 / Real.pi) * θ) ^ (a - 1) := by
      rw [sigDR_apply, abs_mul, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 * a by positivity),
        abs_of_nonneg (Real.rpow_nonneg hsinθ_nn _)]
      have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
      have h1 : 2 * a * |Real.cos (2 * θ)| ≤ 2 * a * 1 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
      calc 2 * a * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (a - 1)
          ≤ 2 * a * 1 * ((4 / Real.pi) * θ) ^ (a - 1) :=
            mul_le_mul h1 hes hsinp (by positivity)
        _ = 2 * a * ((4 / Real.pi) * θ) ^ (a - 1) := by ring
    have habs : |f θ ^ 2 * sigDR a θ| = f θ ^ 2 * |sigDR a θ| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ))]
    rw [habs]
    have hsq : f θ ^ 2 ≤ (C * θ) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (f θ)) hfθ 2
      rwa [sq_abs] at h
    have hpow : θ ^ 2 * θ ^ (a - 1) = θ ^ (a + 1) := by
      rw [← Real.rpow_natCast θ 2, ← Real.rpow_add hθ.1]
      congr 1
      ring
    calc f θ ^ 2 * |sigDR a θ|
        ≤ (C * θ) ^ 2 * (2 * a * ((4 / Real.pi) * θ) ^ (a - 1)) :=
          mul_le_mul hsq hsDR (abs_nonneg _) (by positivity)
      _ = 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1) * (θ ^ 2 * θ ^ (a - 1)) := by
          rw [Real.mul_rpow h4pos.le hθ.1.le]; ring
      _ = 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1) * θ ^ (a + 1) := by rw [hpow]
  · refine tendsto_zero_of_abs_le_mul_sub_rpow_right
      (K := 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1)) (r := a + 1) (by linarith) ?_
    intro θ hθ
    set δ := Real.pi / 2 - θ with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith [hθ.2]
    have hδle : δ ≤ Real.pi / 4 := by rw [hδ]; linarith [hθ.1]
    have hθpos : 0 < θ := by linarith [hθ.1, Real.pi_pos]
    have hθ2 : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθpos, hθ.2⟩
    have hsinθ_nn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hsin : Real.sin (2 * θ) = Real.sin (2 * δ) := by
      rw [hδ]; exact sin_two_eq_sin_two_sub θ
    have hfθ : |f θ| ≤ C * δ := by rw [hδ]; exact hff2 θ ⟨hθpos.le, hθ.2.le⟩
    have hj : (4 / Real.pi) * δ ≤ Real.sin (2 * θ) := by
      rw [hsin]; exact four_div_pi_mul_le_sin_two hδpos.le hδle
    have hes : (Real.sin (2 * θ)) ^ (a - 1) ≤ ((4 / Real.pi) * δ) ^ (a - 1) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos h4pos hδpos) hj (by linarith)
    have hsinp : 0 ≤ (Real.sin (2 * θ)) ^ (a - 1) := Real.rpow_nonneg hsinθ_nn _
    have hsDR : |sigDR a θ| ≤ 2 * a * ((4 / Real.pi) * δ) ^ (a - 1) := by
      rw [sigDR_apply, abs_mul, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 * a by positivity),
        abs_of_nonneg (Real.rpow_nonneg hsinθ_nn _)]
      have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
      have h1 : 2 * a * |Real.cos (2 * θ)| ≤ 2 * a * 1 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
      calc 2 * a * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (a - 1)
          ≤ 2 * a * 1 * ((4 / Real.pi) * δ) ^ (a - 1) :=
            mul_le_mul h1 hes hsinp (by positivity)
        _ = 2 * a * ((4 / Real.pi) * δ) ^ (a - 1) := by ring
    have habs : |f θ ^ 2 * sigDR a θ| = f θ ^ 2 * |sigDR a θ| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ))]
    rw [habs]
    have hsq : f θ ^ 2 ≤ (C * δ) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (f θ)) hfθ 2
      rwa [sq_abs] at h
    have hpow : δ ^ 2 * δ ^ (a - 1) = δ ^ (a + 1) := by
      rw [← Real.rpow_natCast δ 2, ← Real.rpow_add hδpos]
      congr 1
      ring
    calc f θ ^ 2 * |sigDR a θ|
        ≤ (C * δ) ^ 2 * (2 * a * ((4 / Real.pi) * δ) ^ (a - 1)) :=
          mul_le_mul hsq hsDR (abs_nonneg _) (by positivity)
      _ = 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1) * (δ ^ 2 * δ ^ (a - 1)) := by
          rw [Real.mul_rpow h4pos.le hδpos.le]; ring
      _ = 2 * a * C ^ 2 * (4 / Real.pi) ^ (a - 1) * δ ^ (a + 1) := by rw [hpow]

theorem slice_ibp_light_closed (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) (Real.pi / 2))) (h0 : f 0 = 0)
    (h1 : f (Real.pi / 2) = 0) :
    (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * Work.FTS.EllipticEst.TT.sigR a θ)
      = - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ
            * Work.FTS.EllipticEst.TT.sigR a θ)
        - 2 * a * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Work.FTS.EllipticEst.TT.sigR a θ)
        - 2 * a * (1 - a) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (a - 2)) := by
  have hf' : ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.mono (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)
  obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := slice_ibp_light_integrable a ha0 ha1 hf h0 h1
  obtain ⟨hb1, hb2, hb3, hb4⟩ := slice_ibp_light_boundary_aux a ha0 ha1 hf h0 h1
  exact slice_ibp_light a ha0 ha1 hf' hi1 hi2 hi3 hi4 hi5 hb1 hb2 hb3 hb4

end Work.FTS.EllipticEst.TT
