import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_RegExport.THL.integral_sin_two_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# **A1a** — Hölder modulus from a `sin(2x)^{p-1}` derivative bound

`Work.FTS_RegExport.THL.holder_of_deriv_sin_bound`: if `h` has derivative bounded by
`C · sin(2x)^{p-1}` on `(0, π/2)` (with `0 < p ≤ 1`), then `h` is `p`-Hölder there with
constant `2 (π/4)^{1-p} C / p`.

The proof is the fundamental theorem of calculus:

* `h b - h a = ∫_a^b h'` for `a ≤ b` in the interval; the integrability of `h'` follows by
  domination from the bound, since `h'` agrees with the (measurable) derivative `deriv h` on
  the interval;
* `|∫_a^b h'| ≤ ∫_a^b |h'| ≤ C ∫_a^b sin(2σ)^{p-1}`, and the last integral is bounded by
  `2 (π/4)^{1-p} (b - a)^p / p` — this is the sibling leaf **A1b**
  `Work.FTS_RegExport.THL.integral_sin_two_rpow_le`, imported here.
-/

namespace Work.FTS_RegExport.THL

open MeasureTheory Set intervalIntegral

theorem holder_of_deriv_sin_bound {p C : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hC : 0 ≤ C)
    {h h' : ℝ → ℝ} (hd : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2), HasDerivAt h (h' x) x)
    (hb : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2), |h' x| ≤ C * Real.sin (2 * x) ^ (p - 1)) :
    ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |h θ - h θ'| ≤ 2 * (Real.pi / 4) ^ (1 - p) / p * C * |θ - θ'| ^ p := by
  -- the estimate for an ordered pair `a ≤ b`
  have key : ∀ a b : ℝ, a ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0:ℝ) (Real.pi / 2) → a ≤ b →
      |h b - h a| ≤ 2 * (Real.pi / 4) ^ (1 - p) / p * C * (b - a) ^ p := by
    intro a b ha hbmem hab
    have hsub : Set.uIoc a b ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha.1 hx.1.le, lt_of_le_of_lt hx.2 hbmem.2⟩
    have hsubIcc : Set.uIcc a b ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hbmem.2⟩
    -- the dominating function `C · sin(2σ)^{p-1}` is continuous on the interval
    have hsin : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ)) (Set.uIcc a b) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hne : ∀ σ ∈ Set.uIcc a b, Real.sin (2 * σ) ≠ 0 := by
      intro σ hσ
      have hσ' := hsubIcc hσ
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ'.1]) (by linarith [hσ'.2]))
    have hcontg : ContinuousOn (fun σ : ℝ => C * Real.sin (2 * σ) ^ (p - 1)) (Set.uIcc a b) :=
      continuousOn_const.mul (hsin.rpow_const (fun σ hσ => Or.inl (hne σ hσ)))
    have hg : IntervalIntegrable (fun σ : ℝ => C * Real.sin (2 * σ) ^ (p - 1)) volume a b :=
      hcontg.intervalIntegrable
    -- `h'` agrees with `deriv h` on the interval, hence is a.e. strongly measurable
    have hfm : AEStronglyMeasurable h' (volume.restrict (Set.uIoc a b)) :=
      ((measurable_deriv h).aestronglyMeasurable).congr
        (Set.EqOn.aeEq_restrict (fun x hx => (hd x (hsub hx)).deriv) measurableSet_uIoc)
    have hbnd : (fun x => ‖h' x‖) ≤ᵐ[volume.restrict (Set.uIoc a b)]
        (fun σ => C * Real.sin (2 * σ) ^ (p - 1)) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
        (fun x hx => by simpa only [Real.norm_eq_abs] using hb x (hsub hx))
    have hint : IntervalIntegrable h' volume a b := IntervalIntegrable.mono_fun' hg hfm hbnd
    -- fundamental theorem of calculus
    have hFTC : ∫ σ in a..b, h' σ = h b - h a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsubIcc hx)) hint
    have hstep : |h b - h a| ≤ ∫ σ in a..b, C * Real.sin (2 * σ) ^ (p - 1) := by
      have hmain : ‖∫ σ in a..b, h' σ‖ ≤ ∫ σ in a..b, C * Real.sin (2 * σ) ^ (p - 1) :=
        intervalIntegral.norm_integral_le_of_norm_le (f := h') hab
          (Filter.Eventually.of_forall (fun σ hσ => by
            have hσ' : σ ∈ Set.uIoc a b := by rw [Set.uIoc_of_le hab]; exact hσ
            simpa only [Real.norm_eq_abs] using hb σ (hsub hσ'))) hg
      rw [← hFTC]
      simpa only [Real.norm_eq_abs] using hmain
    have hIntB := integral_sin_two_rpow_le hp hp1 ha.1 hab hbmem.2
    have hcm : ∫ σ in a..b, C * Real.sin (2 * σ) ^ (p - 1)
        = C * ∫ σ in a..b, Real.sin (2 * σ) ^ (p - 1) :=
      intervalIntegral.integral_const_mul C _
    calc |h b - h a| ≤ ∫ σ in a..b, C * Real.sin (2 * σ) ^ (p - 1) := hstep
      _ = C * ∫ σ in a..b, Real.sin (2 * σ) ^ (p - 1) := hcm
      _ ≤ C * (2 * (Real.pi / 4) ^ (1 - p) / p * (b - a) ^ p) :=
          mul_le_mul_of_nonneg_left hIntB hC
      _ = 2 * (Real.pi / 4) ^ (1 - p) / p * C * (b - a) ^ p := by ring
  intro θ hθ θ' hθ'
  rcases le_total θ θ' with hle | hle
  · have hk := key θ θ' hθ hθ' hle
    rw [abs_sub_comm (h θ) (h θ'), abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    exact hk
  · have hk := key θ' θ hθ' hθ hle
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact hk

end Work.FTS_RegExport.THL
