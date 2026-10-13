import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.abs_sub_le_integral_abs
import Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.not_integrableOn_Ioo_div
import Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.not_integrableOn_Ioo_div_sub
import Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.tendsto_intervalIntegral_abs_left
import Submission.Work.FTS.StrongPersist.H6Aux.EndLimits.tendsto_intervalIntegral_abs_right

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Vanishing of a `sin(2θ)u`-profile at the endpoints of `Iθ`

Let `u : ℝ → ℝ` be integrable on `Iθ = [0, π/2]` and let
`F θ = sin (2θ) · u θ` have an integrable derivative `v'` on `(0, π/2)`.  Then `F` vanishes at both
endpoints:

`sin (2θ) u θ → 0` as `θ → 0⁺` and as `θ → (π/2)⁻`.

The point is that `F` has finite total variation, so it cannot oscillate near an endpoint, while a
non-vanishing limit at an endpoint forces `|u θ| ≳ dist (θ, endpoint)⁻¹`, which is not integrable
(logarithmic divergence) — contradicting the integrability of `u`.  Concretely: if `F` did not tend
to `0`, there would be `ε > 0` and points `θ₀` arbitrarily close to the endpoint with
`|F θ₀| ≥ ε`; a shrinking-interval integral bound `∫ |v'| < ε/2` (absolute continuity of the
integral) then gives `|F θ| ≥ ε/2` on a whole one-sided neighbourhood of the endpoint, whence
`|u θ| ≥ (ε/4)/θ` (respectively `≥ (ε/4)/(π/2 - θ)`), which is not integrable.

The auxiliary facts (shrinking integral → 0, the oscillation bound, and the non-integrability of
`c/θ` and `c/(L-θ)`) are the lemmas in `Submission.Work.FTS.StrongPersist.H6Aux.EndLimits`.
-/

namespace Work.FTS.StrongPersist.H6Aux

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.StrongPersist.H6Aux.EndLimits

theorem tendsto_sin_mul_zero_of_integrable {u v' : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn u Work.Spaces.Iθ)
    (hu0 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), 0 ≤ u θ)
    (hv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      HasDerivAt (fun θ' => Real.sin (2*θ') * u θ') (v' θ) θ)
    (hv' : MeasureTheory.IntegrableOn v' Work.Spaces.Iθ) :
    Filter.Tendsto (fun θ => Real.sin (2*θ) * u θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Real.sin (2*θ) * u θ) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
  set F : ℝ → ℝ := fun θ => Real.sin (2*θ) * u θ with hF
  have hpi2 : (0:ℝ) < Real.pi/2 := by linarith [Real.pi_pos]
  have hderiv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt F (v' θ) θ := hv
  have hint' : IntegrableOn v' (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hv'.mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  have huint' : IntegrableOn u (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hu.mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  constructor
  · -- ### the left endpoint `0⁺`
    have hA : Tendsto (fun r : ℝ => ∫ x in (0:ℝ)..r, |v' x|)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
      tendsto_intervalIntegral_abs_left hpi2 hint'
    by_contra hcon
    rw [Metric.tendsto_nhds] at hcon
    push Not at hcon
    obtain ⟨ε, hε, hfreq⟩ := hcon
    simp only [Real.dist_eq, sub_zero] at hfreq
    obtain ⟨δ, _hδ, hδsub⟩ := (nhdsGT_basis (0:ℝ)).mem_iff.1
      (hA.eventually (Metric.ball_mem_nhds (0:ℝ) (by linarith : (0:ℝ) < ε / 2)))
    set r : ℝ := min (δ/2) (Real.pi/4) with hrdef
    have hrpos : 0 < r := by
      rw [hrdef]; exact lt_min (by linarith) (by linarith [Real.pi_pos])
    have hrδ : r < δ := by
      rw [hrdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hrpi : r < Real.pi/2 := by
      rw [hrdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
    have hAr : (∫ x in (0:ℝ)..r, |v' x|) < ε/2 := by
      have h := hδsub ⟨hrpos, hrδ⟩
      simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at h
      linarith [le_abs_self (∫ x in (0:ℝ)..r, |v' x|)]
    have hmem : Set.Ioo (0:ℝ) r ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      (nhdsGT_basis (0:ℝ)).mem_iff.2 ⟨r, hrpos, subset_rfl⟩
    obtain ⟨θ₀, hθ₀big, hθ₀mem⟩ := (hfreq.and_eventually hmem).exists
    have hIntOn : IntegrableOn v' (Set.Ioc (0:ℝ) r) :=
      hint'.mono_set (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hrpi⟩)
    have hIntAbs : IntervalIntegrable v' volume (0:ℝ) r :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hrpos.le).2 hIntOn
    have hderivr : ∀ θ ∈ Set.Ioo (0:ℝ) r, HasDerivAt F (v' θ) θ :=
      fun θ hθ => hderiv θ ⟨hθ.1, lt_trans hθ.2 hrpi⟩
    have hkey : ∀ θ, 0 < θ → θ < r → ε / 2 ≤ |F θ| := by
      intro θ hθ hθr
      have hdiff : |F θ - F θ₀| ≤ ∫ x in (0:ℝ)..r, |v' x| := by
        rcases le_total θ θ₀ with hle | hle
        · rw [abs_sub_comm]
          exact abs_sub_le_integral_abs (a := (0:ℝ)) (b := r) (θ₁ := θ) (θ₂ := θ₀)
            hderivr hIntAbs hθ hle hθ₀mem.2
        · exact abs_sub_le_integral_abs (a := (0:ℝ)) (b := r) (θ₁ := θ₀) (θ₂ := θ)
            hderivr hIntAbs hθ₀mem.1 hle hθr
      have h1 : |F θ₀| ≤ |F θ| + |F θ - F θ₀| := by
        calc |F θ₀| = |F θ + (F θ₀ - F θ)| := by congr 1; ring
          _ ≤ |F θ| + |F θ₀ - F θ| := abs_add_le _ _
          _ = |F θ| + |F θ - F θ₀| := by rw [abs_sub_comm]
      linarith [hAr, hdiff, hθ₀big, h1]
    have hle : ∀ θ ∈ Set.Ioo (0:ℝ) r, ε / 4 / θ ≤ |u θ| := by
      intro θ hθ
      have hFθ : ε / 2 ≤ |F θ| := hkey θ hθ.1 hθ.2
      have hs : 0 < Real.sin (2*θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, hrpi, Real.pi_pos])
      have hFval : F θ = Real.sin (2*θ) * u θ := by rw [hF]
      have habs : |F θ| = Real.sin (2*θ) * |u θ| := by
        rw [hFval, abs_mul, abs_of_pos hs]
      have hsinle : Real.sin (2*θ) ≤ 2*θ := Real.sin_le (by linarith [hθ.1])
      have h1 : ε / 4 / θ ≤ (ε/2)/Real.sin (2*θ) := by
        rw [div_le_div_iff₀ hθ.1 hs]
        have hmul : (ε/4) * Real.sin (2*θ) ≤ (ε/4) * (2*θ) :=
          mul_le_mul_of_nonneg_left hsinle (by linarith [hε] : (0:ℝ) ≤ ε/4)
        have hmul2 : (ε/4) * (2*θ) = (ε/2) * θ := by ring
        linarith [hmul, hmul2]
      have h4 : (ε/2)/Real.sin (2*θ) ≤ |u θ| := by
        have hmul : |u θ| * Real.sin (2*θ) = |F θ| := by rw [habs, mul_comm]
        rw [div_le_iff₀ hs, hmul]
        exact hFθ
      exact le_trans h1 h4
    have huAbsOn : IntegrableOn (fun θ => |u θ|) (Set.Ioo (0:ℝ) r) :=
      Integrable.abs (huint'.mono_set (fun x hx => ⟨hx.1, lt_trans hx.2 hrpi⟩))
    refine (not_integrableOn_Ioo_div (c := ε/4) (r := r) (by linarith) hrpos) ?_
    refine Integrable.mono' huAbsOn ?_ ?_
    · exact (measurable_const.div measurable_id).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith [hε]) hθ.1.le)]
      exact hle θ hθ
  · -- ### the right endpoint `(π/2)⁻`
    have hA2 : Tendsto (fun t : ℝ => ∫ x in t..Real.pi/2, |v' x|)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) :=
      tendsto_intervalIntegral_abs_right hpi2 hint'
    by_contra hcon
    rw [Metric.tendsto_nhds] at hcon
    push Not at hcon
    obtain ⟨ε, hε, hfreq⟩ := hcon
    simp only [Real.dist_eq, sub_zero] at hfreq
    obtain ⟨t₀, ht₀lt, ht₀sub⟩ := (nhdsLT_basis (Real.pi/2)).mem_iff.1
      (hA2.eventually (Metric.ball_mem_nhds (0:ℝ) (by linarith : (0:ℝ) < ε / 2)))
    set t : ℝ := (max t₀ 0 + Real.pi/2)/2 with htdef
    have htpos : 0 < t := by
      rw [htdef]
      have := le_max_right t₀ (0:ℝ)
      linarith [Real.pi_pos]
    have htt : t₀ < t := by
      rw [htdef]
      have := le_max_left t₀ (0:ℝ)
      linarith
    have htlt : t < Real.pi/2 := by
      rw [htdef]
      have := max_lt ht₀lt hpi2
      linarith
    have hAt : (∫ x in t..Real.pi/2, |v' x|) < ε/2 := by
      have h := ht₀sub ⟨htt, htlt⟩
      simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at h
      linarith [le_abs_self (∫ x in t..Real.pi/2, |v' x|)]
    have hmem : Set.Ioo t (Real.pi/2) ∈ nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2)) :=
      (nhdsLT_basis (Real.pi/2)).mem_iff.2 ⟨t, htlt, subset_rfl⟩
    obtain ⟨θ₀, hθ₀big, hθ₀mem⟩ := (hfreq.and_eventually hmem).exists
    have hIntOn : IntegrableOn v' (Set.Ioo t (Real.pi/2)) :=
      hint'.mono_set (fun x hx => ⟨lt_trans htpos hx.1, hx.2⟩)
    have hIntAbs : IntervalIntegrable v' volume t (Real.pi/2) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le htlt.le).2 hIntOn
    have hderivt : ∀ θ ∈ Set.Ioo t (Real.pi/2), HasDerivAt F (v' θ) θ :=
      fun θ hθ => hderiv θ ⟨lt_trans htpos hθ.1, hθ.2⟩
    have hkey : ∀ θ, t < θ → θ < Real.pi/2 → ε / 2 ≤ |F θ| := by
      intro θ hθt hθpi
      have hdiff : |F θ - F θ₀| ≤ ∫ x in t..Real.pi/2, |v' x| := by
        rcases le_total θ θ₀ with hle | hle
        · rw [abs_sub_comm]
          exact abs_sub_le_integral_abs (a := t) (b := Real.pi/2) (θ₁ := θ) (θ₂ := θ₀)
            hderivt hIntAbs hθt hle hθ₀mem.2
        · exact abs_sub_le_integral_abs (a := t) (b := Real.pi/2) (θ₁ := θ₀) (θ₂ := θ)
            hderivt hIntAbs hθ₀mem.1 hle hθpi
      have h1 : |F θ₀| ≤ |F θ| + |F θ - F θ₀| := by
        calc |F θ₀| = |F θ + (F θ₀ - F θ)| := by congr 1; ring
          _ ≤ |F θ| + |F θ₀ - F θ| := abs_add_le _ _
          _ = |F θ| + |F θ - F θ₀| := by rw [abs_sub_comm]
      linarith [hAt, hdiff, hθ₀big, h1]
    have hle : ∀ θ ∈ Set.Ioo t (Real.pi/2), ε / 4 / (Real.pi/2 - θ) ≤ |u θ| := by
      intro θ hθ
      have hFθ : ε / 2 ≤ |F θ| := hkey θ hθ.1 hθ.2
      have hpos : 0 < Real.pi/2 - θ := by linarith [hθ.2]
      have hs : 0 < Real.sin (2*θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, htpos]) (by linarith [hθ.2])
      have hFval : F θ = Real.sin (2*θ) * u θ := by rw [hF]
      have habs : |F θ| = Real.sin (2*θ) * |u θ| := by
        rw [hFval, abs_mul, abs_of_pos hs]
      have hsinle : Real.sin (2*θ) ≤ 2*(Real.pi/2 - θ) := by
        have hπ : Real.pi - 2*θ = 2*(Real.pi/2 - θ) := by ring
        calc Real.sin (2*θ) = Real.sin (Real.pi - 2*θ) := (Real.sin_pi_sub (2*θ)).symm
          _ = Real.sin (2*(Real.pi/2 - θ)) := by rw [hπ]
          _ ≤ 2*(Real.pi/2 - θ) := Real.sin_le (by linarith)
      have h1 : ε / 4 / (Real.pi/2 - θ) ≤ (ε/2)/Real.sin (2*θ) := by
        rw [div_le_div_iff₀ hpos hs]
        have hmul : (ε/4) * Real.sin (2*θ) ≤ (ε/4) * (2*(Real.pi/2 - θ)) :=
          mul_le_mul_of_nonneg_left hsinle (by linarith [hε] : (0:ℝ) ≤ ε/4)
        have hmul2 : (ε/4) * (2*(Real.pi/2 - θ)) = (ε/2) * (Real.pi/2 - θ) := by ring
        linarith [hmul, hmul2]
      have h4 : (ε/2)/Real.sin (2*θ) ≤ |u θ| := by
        have hmul : |u θ| * Real.sin (2*θ) = |F θ| := by rw [habs, mul_comm]
        rw [div_le_iff₀ hs, hmul]
        exact hFθ
      exact le_trans h1 h4
    have huAbsOn : IntegrableOn (fun θ => |u θ|) (Set.Ioo t (Real.pi/2)) :=
      Integrable.abs (huint'.mono_set (fun x hx => ⟨lt_trans htpos hx.1, hx.2⟩))
    refine (not_integrableOn_Ioo_div_sub (c := ε/4) (L := Real.pi/2) (t := t)
      (by linarith) htlt) ?_
    refine Integrable.mono' huAbsOn ?_ ?_
    · exact (measurable_const.div (measurable_const.sub measurable_id)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith [hε]) (by linarith [hθ.2]))]
      exact hle θ hθ

end Work.FTS.StrongPersist.H6Aux
