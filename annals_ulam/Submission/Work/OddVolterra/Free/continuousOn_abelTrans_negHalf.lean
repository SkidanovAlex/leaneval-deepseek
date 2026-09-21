import Mathlib
import Submission.Work.OddRadon.Abel
import Submission.Work.OddRadon.abelTrans_radonInverse_eq_abelDatum

/-!
# Continuity of the classical Abel transform `T_{-1/2}` of a continuous profile vanishing at `0`

`Work.OddRadon.abelTrans α γ c = ∫_0^c γ s (c²-s²)^α ds`.  At the critical exponent
`α = -1/2` the kernel is singular enough that continuity at `c = 0` needs a genuine hypothesis:
for `c → 0⁺` the integral tends to `γ 0 · π/2`, so the transform is continuous at `0` **iff**
`γ 0 = 0` (for instance `γ ≡ 1` gives the constant `π/2` on `(0,a]` and `0` at `0`).
The companion lemma `Work.OddRadon.continuousOn_abelTrans` covers the exponents `α > -1/2`, where
the vanishing factor `c^{2α+1}` supplies continuity at `0` for free; here that factor is `c⁰ = 1`
and the hypothesis `γ 0 = 0` replaces it.

## The proof

The substitution `s = c t` (`AbelDirect.abelTrans_eq_integral_comp_mul`) turns the transform into
the *parameter integral with a fixed integrable kernel*

  `abelTrans (-1/2) γ c = ∫_0^1 γ (c t) (1-t²)^{-1/2} dt   (c > 0)`,

and at `c = 0` both sides vanish because `γ 0 = 0`.  Continuity of that parameter integral on
`[0,a]` is a dominated-convergence statement (`continuousOn_kernelIntegral`): the kernel
`(1-t²)^{-1/2}` is integrable on `(0,1)` and dominates `γ (c t) (1-t²)^{-1/2}` uniformly in
`c ∈ [0,a]` through the sup norm `M` of `γ` on the compact interval `[0,a]`.

## Main results

* `continuousOn_kernelIntegral` — continuity of `c ↦ ∫_0^1 G (c t) (1-t²)^ρ dt` on `[0,A]`
  for `ρ > -1` and `G` continuous on `[0,A]` (no vanishing hypothesis needed: the kernel is
  fixed and integrable);
* `Work.OddVolterra.Free.continuousOn_abelTrans_negHalf` — the requested lemma.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace Work.OddVolterra.Free

/-- **Continuity of the normalised Abel kernel integral.**  For `ρ > -1` the weight
`(1-t²)^ρ` is integrable on `(0,1)`, so for `G` continuous on the compact interval `[0,A]`
(with `A > 0`) the parameter integral `c ↦ ∫_0^1 G (c t) (1-t²)^ρ dt` is continuous on `[0,A]`
by dominated convergence.  (This is `Work.OddRadon.continuousOn_abelKernel` with the interval
`[0,1]` of parameters replaced by `[0,A]`, which is what the local formulation needs.) -/
lemma continuousOn_kernelIntegral {A ρ : ℝ} (hA : 0 < A) (hρ : -1 < ρ) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Set.Icc 0 A)) :
    ContinuousOn (fun c : ℝ => ∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^ρ) (Set.Icc 0 A) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  intro c₀ hc₀
  have hmaps : ∀ (c t : ℝ), c ∈ Set.Icc (0:ℝ) A → t ∈ Set.Ioo (0:ℝ) 1 →
      c * t ∈ Set.Icc (0:ℝ) A := by
    intro c t hc ht
    refine ⟨mul_nonneg hc.1 ht.1.le, ?_⟩
    have h := mul_le_mul hc.2 ht.2.le ht.1.le (le_of_lt hA)
    simpa using h
  have hbound_int : Integrable (fun t : ℝ => M * (1-t^2)^ρ)
      (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
    have h := Work.OddRadon.AbelDirect.intervalIntegrable_one_sub_sq_rpow hρ
    exact (h.1.mono_set Set.Ioo_subset_Ioc_self).const_mul M
  have hmeas : ∀ᶠ c in nhdsWithin c₀ (Set.Icc (0:ℝ) A),
      AEStronglyMeasurable (fun t : ℝ => G (c*t) * (1-t^2)^ρ)
        (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    have h1 : ContinuousOn (fun t : ℝ => (1 - t^2)^ρ) (Set.Ioo (0:ℝ) 1) :=
      ContinuousOn.rpow (continuousOn_const.sub (continuousOn_id.pow 2)) continuousOn_const
        (fun t ht => Or.inl (by nlinarith [ht.1, ht.2]))
    have h2 : ContinuousOn (fun t : ℝ => G (c*t)) (Set.Ioo (0:ℝ) 1) :=
      hG.comp ((continuous_const.mul continuous_id).continuousOn) (fun t ht => hmaps c t hc ht)
    exact h2.mul h1
  have hboundae : ∀ᶠ c in nhdsWithin c₀ (Set.Icc (0:ℝ) A),
      ∀ᵐ t ∂(volume.restrict (Set.Ioo (0:ℝ) 1)),
        ‖G (c*t) * (1-t^2)^ρ‖ ≤ M * (1-t^2)^ρ := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hct : c*t ∈ Set.Icc (0:ℝ) A := hmaps c t hc ht
    have hpos : 0 < (1-t^2)^ρ := Real.rpow_pos_of_pos (by nlinarith [ht.1, ht.2]) ρ
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right (hM _ hct) hpos.le
  have hlim : ∀ᵐ t ∂(volume.restrict (Set.Ioo (0:ℝ) 1)),
      Tendsto (fun c : ℝ => G (c*t) * (1-t^2)^ρ) (nhdsWithin c₀ (Set.Icc (0:ℝ) A))
        (nhds (G (c₀*t) * (1-t^2)^ρ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hmaps' : MapsTo (fun c : ℝ => c*t) (Set.Icc (0:ℝ) A) (Set.Icc (0:ℝ) A) :=
      fun c hc => hmaps c t hc ht
    have h1 : ContinuousWithinAt (fun c : ℝ => G (c*t)) (Set.Icc (0:ℝ) A) c₀ := by
      have hh := (ContinuousOn.comp (f := fun c : ℝ => c*t) (g := G) (t := Set.Icc (0:ℝ) A)
        hG (by
          have hφ : Continuous (fun c : ℝ => c*t) := by
            have h2 : Continuous (id * fun _ : ℝ => t) := continuous_id.mul continuous_const
            exact (show Continuous (fun c : ℝ => c*t) from h2)
          exact hφ.continuousOn) hmaps') c₀ hc₀
      simpa only [Function.comp_def] using hh
    exact h1.mul_const _
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Set.Ioo (0:ℝ) 1))
      (l := nhdsWithin c₀ (Set.Icc (0:ℝ) A))
      (F := fun c t => G (c*t) * (1-t^2)^ρ) (f := fun t => G (c₀*t) * (1-t^2)^ρ)
      (fun t => M * (1-t^2)^ρ) hmeas hboundae hbound_int hlim
  have hK : ∀ c : ℝ, (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^ρ)
      = ∫ t, G (c*t) * (1-t^2)^ρ ∂(volume.restrict (Set.Ioo (0:ℝ) 1)) := by
    intro c
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := 1)).symm
  show Tendsto (fun c : ℝ => ∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^ρ)
      (nhdsWithin c₀ (Set.Icc (0:ℝ) A)) (nhds (∫ t in (0:ℝ)..1, G (c₀*t) * (1-t^2)^ρ))
  rw [hK c₀]
  exact Tendsto.congr' (Eventually.of_forall (fun c => (hK c).symm)) hmain

/-- **Continuity of the classical Abel transform** `T_{-1/2} γ c = ∫_0^c γ s / √(c²-s²) ds`
on `[0,a]`, for `γ` continuous on `[0,a]` with `γ 0 = 0`.

The substitution `s = c t` writes `T_{-1/2} γ c = ∫_0^1 γ (c t) (1-t²)^{-1/2} dt` for `c > 0`
(where `c^{2α+1} = c⁰ = 1`), and at `c = 0` the same identity holds because both sides are `0`:
the left side is `abelTrans_zero` and the right side is `γ 0 · ∫_0^1 (1-t²)^{-1/2} dt = 0` by the
hypothesis `γ 0 = 0`.  The continuity of the substituted form is
`continuousOn_kernelIntegral`. -/
theorem continuousOn_abelTrans_negHalf {a : ℝ} (ha : 0 < a) {γ : ℝ → ℝ}
    (hγ : ContinuousOn γ (Set.Icc 0 a)) (h0 : γ 0 = 0) :
    ContinuousOn (fun c : ℝ => Work.OddRadon.abelTrans (-(1 / 2)) γ c) (Set.Icc 0 a) := by
  have hK : ContinuousOn (fun c : ℝ => ∫ t in (0:ℝ)..1, γ (c*t) * (1-t^2)^(-(1/2:ℝ)))
      (Set.Icc 0 a) := by
    have h := continuousOn_kernelIntegral (A := a) (ρ := -(1/2:ℝ)) ha (by norm_num) hγ
    simpa using h
  refine hK.congr ?_
  intro c hc
  change Work.OddRadon.abelTrans (-(1/2:ℝ)) γ c
      = ∫ t in (0:ℝ)..1, γ (c*t) * (1-t^2)^(-(1/2:ℝ))
  rcases eq_or_lt_of_le hc.1 with h | h
  · subst h
    simp [h0]
  · rw [Work.OddRadon.AbelDirect.abelTrans_eq_integral_comp_mul (-(1/2:ℝ)) γ h]
    have hexp : (2:ℝ) * (-(1/2)) + 1 = 0 := by norm_num
    rw [hexp, Real.rpow_zero, one_mul]

end Work.OddVolterra.Free
