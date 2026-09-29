import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.circleAverage_log_norm_tendsto

/-!
# `Work.Holonomy3.radius_reduction`

If the fine holonomy inequality `A + C·log r ≤ rearrInt w (φ ∘ (r·))` holds for every radius
`r ∈ (0,1)`, then it holds at the boundary:

  `A ≤ rearrInt w φ`.

The content is the one-sided continuity `rearrInt w (φ ∘ (r·)) → rearrInt w φ` as `r → 1⁻`.
Each `φ k` is continuous on the closed unit disc and non-vanishing on the unit circle, hence
non-vanishing (and `log ‖φ k‖` continuous) on a closed annulus `[a k, 1]`; on that annulus the
integrands are jointly continuous, so each iterated interval integral — and hence the finite sum
`rearrInt` — is continuous in the radius.  The same argument applies to `r ↦ A + C·log r`
(`log r → 0`), and `A + C·log r ≤ …` for all `r ∈ (0,1)` passes to the limit.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped Topology BigOperators

/-- The unit-circle parametrisation `s ↦ exp(2πis)`. -/
private noncomputable def Cexp (s : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ))

private lemma continuous_Cexp : Continuous Cexp := by
  change Continuous (fun s : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)))
  fun_prop

private lemma norm_Cexp (s : ℝ) : ‖Cexp s‖ = 1 := by
  change ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ))‖ = 1
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- `rearrInt`, unfolded into the finite sum of iterated integrals, with the map `φ k` replaced by
`z ↦ φ k (r z)` written using the circle parametrisation `Cexp`.  Holds by definition. -/
private lemma rearrInt_unfold {l : ℕ} (w : Fin (l + 1) → ℝ) (φ : Fin (l + 1) → ℂ → ℂ) (r : ℝ) :
    Submission.CDTPlan.rearrInt w (fun k z => φ k (r * z)) =
      ∑ k, ∑ k', w k * w k' *
        (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
          max (Real.log ‖φ k ((r : ℂ) * Cexp s)‖) (Real.log ‖φ k' ((r : ℂ) * Cexp t)‖)) :=
  rfl

/-- Joint continuity of a parameter-dependent iterated interval integral of `max`. -/
private theorem continuous_doubleIntegral_max {X : Type*} [TopologicalSpace X]
    {A B : X → ℝ → ℝ} (hA : Continuous (Function.uncurry A)) (hB : Continuous (Function.uncurry B)) :
    Continuous (fun x : X => ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, max (A x s) (B x t)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

/-- `(r, θ) ↦ log ‖φ (r·e^{2πiθ})‖` is continuous on `[a,1] × ℝ` when `0 < a` and `φ` does
not vanish on the annulus `a ≤ ‖z‖ ≤ 1`. -/
private theorem continuous_logNorm_annulus {φ : ℂ → ℂ} {a : ℝ} (ha : 0 < a)
    (hcont : ContinuousOn φ (Metric.closedBall 0 1))
    (hnz : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ 1 → φ z ≠ 0) :
    Continuous (fun p : Set.Icc a 1 × ℝ => Real.log ‖φ (((p.1 : ℝ) : ℂ) * Cexp (p.2 : ℝ))‖) := by
  have hG_cont : Continuous (fun p : Set.Icc a 1 × ℝ => ((p.1 : ℝ) : ℂ) * Cexp (p.2 : ℝ)) :=
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_Cexp.comp continuous_snd)
  have hG_norm : ∀ p : Set.Icc a 1 × ℝ, ‖((p.1 : ℝ) : ℂ) * Cexp (p.2 : ℝ)‖ = (p.1 : ℝ) := by
    intro p
    rw [norm_mul, norm_Cexp, mul_one]
    simp [abs_of_nonneg (le_trans ha.le p.1.2.1)]
  have hcomp : Continuous (φ ∘ fun p : Set.Icc a 1 × ℝ => ((p.1 : ℝ) : ℂ) * Cexp (p.2 : ℝ)) := by
    rw [← continuousOn_univ]
    exact hcont.comp hG_cont.continuousOn (by
      intro p _
      rw [Metric.mem_closedBall, dist_zero_right, hG_norm p]
      exact p.1.2.2)
  refine hcomp.norm.log (fun p => ?_)
  rw [norm_ne_zero_iff]
  refine hnz _ ?_ ?_
  · rw [hG_norm p]; exact p.1.2.1
  · rw [hG_norm p]; exact p.1.2.2

theorem radius_reduction {l : ℕ} (w : Fin (l + 1) → ℝ) (φ : Fin (l + 1) → ℂ → ℂ) (A C : ℝ)
    (hcont : ∀ k, ContinuousOn (φ k) (Metric.closedBall 0 1))
    (hnz : ∀ (k : Fin (l + 1)) (z : ℂ), ‖z‖ = 1 → φ k z ≠ 0)
    (hineq : ∀ r : ℝ, 0 < r → r < 1 → (∀ k z, ‖z‖ = 1 → φ k (r * z) ≠ 0) →
      A + C * Real.log r ≤ Submission.CDTPlan.rearrInt w (fun k z => φ k (r * z))) :
    A ≤ Submission.CDTPlan.rearrInt w φ := by
  -- a common zero-free annulus `[a,1]` for all the `φ k` at once, obtained from the product
  have hg_cont : ContinuousOn (fun z : ℂ => ∏ k : Fin (l + 1), φ k z)
      (Metric.closedBall 0 1) := by
    have h := continuousOn_finsetProd (s := (Finset.univ : Finset (Fin (l + 1))))
      (f := fun k z => φ k z) (fun k _ => hcont k)
    simpa using h
  have hg_ne : ∀ z : ℂ, ‖z‖ = 1 → (∏ k : Fin (l + 1), φ k z) ≠ 0 := by
    intro z hz
    simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
    exact fun k => hnz k z hz
  obtain ⟨a, ha0, ha1, hann⟩ :=
    exists_annulus_ne_zero (fun z : ℂ => ∏ k : Fin (l + 1), φ k z) hg_cont hg_ne
  have hann' : ∀ (k : Fin (l + 1)) z, a ≤ ‖z‖ → ‖z‖ ≤ 1 → φ k z ≠ 0 := by
    intro k z h1 h2
    exact Finset.prod_ne_zero_iff.mp (hann z h1 h2) k (Finset.mem_univ k)
  -- continuity of each double integral in the radius, near `1` from below
  have hJ : ∀ k k' : Fin (l + 1),
      Filter.Tendsto (fun r : ℝ => ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        max (Real.log ‖φ k ((r : ℂ) * Cexp s)‖) (Real.log ‖φ k' ((r : ℂ) * Cexp t)‖))
      (𝓝[Set.Iio (1:ℝ)] 1)
      (𝓝 (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        max (Real.log ‖φ k ((1 : ℂ) * Cexp s)‖) (Real.log ‖φ k' ((1 : ℂ) * Cexp t)‖))) := by
    intro k k'
    have hbk : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ 1 → φ k z ≠ 0 := fun z h1 h2 => hann' k z h1 h2
    have hbk' : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ 1 → φ k' z ≠ 0 := fun z h1 h2 => hann' k' z h1 h2
    have hA : Continuous (Function.uncurry (fun (x : Set.Icc a 1) (s : ℝ) =>
        Real.log ‖φ k (((x : ℝ) : ℂ) * Cexp s)‖)) :=
      continuous_logNorm_annulus ha0 (hcont k) hbk
    have hB : Continuous (Function.uncurry (fun (x : Set.Icc a 1) (t : ℝ) =>
        Real.log ‖φ k' (((x : ℝ) : ℂ) * Cexp t)‖)) :=
      continuous_logNorm_annulus ha0 (hcont k') hbk'
    have hcont2 : Continuous (fun x : Set.Icc a 1 => ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        max (Real.log ‖φ k (((x : ℝ) : ℂ) * Cexp s)‖)
            (Real.log ‖φ k' (((x : ℝ) : ℂ) * Cexp t)‖)) :=
      continuous_doubleIntegral_max hA hB
    have hCO : ContinuousOn (fun r : ℝ => ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        max (Real.log ‖φ k ((r : ℂ) * Cexp s)‖) (Real.log ‖φ k' ((r : ℂ) * Cexp t)‖))
        (Set.Icc a 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hcont2
    have hCWA : ContinuousWithinAt (fun r : ℝ => ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        max (Real.log ‖φ k ((r : ℂ) * Cexp s)‖) (Real.log ‖φ k' ((r : ℂ) * Cexp t)‖))
        (Set.Icc a 1) 1 :=
      hCO.continuousWithinAt (Set.mem_Icc.mpr ⟨le_of_lt ha1, le_refl 1⟩)
    have hle : 𝓝[Set.Iio (1:ℝ)] 1 ≤ 𝓝[Set.Icc a 1] 1 := by
      rw [nhdsWithin_le_iff]
      have h1 : Set.Ioi a ∈ 𝓝[Set.Iio (1:ℝ)] 1 := nhdsWithin_le_nhds (Ioi_mem_nhds ha1)
      have h2 := self_mem_nhdsWithin (s := Set.Ioi a ∩ Set.Iio (1:ℝ)) (a := (1:ℝ))
      rw [nhdsWithin_inter_of_mem h1] at h2
      exact Filter.mem_of_superset h2 (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    exact Filter.Tendsto.mono_left hCWA hle
  -- assemble the finite sum
  have hsum : Filter.Tendsto (fun r : ℝ => ∑ k, ∑ k', w k * w k' *
        (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
          max (Real.log ‖φ k ((r : ℂ) * Cexp s)‖) (Real.log ‖φ k' ((r : ℂ) * Cexp t)‖)))
      (𝓝[Set.Iio (1:ℝ)] 1)
      (𝓝 (∑ k, ∑ k', w k * w k' *
        (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
          max (Real.log ‖φ k ((1 : ℂ) * Cexp s)‖) (Real.log ‖φ k' ((1 : ℂ) * Cexp t)‖)))) := by
    refine tendsto_finsetSum Finset.univ (fun k _ => ?_)
    refine tendsto_finsetSum Finset.univ (fun k' _ => ?_)
    exact (hJ k k').const_mul (w k * w k')
  -- identify `rearrInt` with the finite sum
  have hfun : (fun r : ℝ => Submission.CDTPlan.rearrInt w (fun k z => φ k (r * z)))
      = fun r : ℝ => ∑ k, ∑ k', w k * w k' *
        (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
          max (Real.log ‖φ k ((r : ℂ) * Cexp s)‖) (Real.log ‖φ k' ((r : ℂ) * Cexp t)‖)) :=
    funext fun r => rearrInt_unfold w φ r
  have hval : Submission.CDTPlan.rearrInt w φ = ∑ k, ∑ k', w k * w k' *
        (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
          max (Real.log ‖φ k ((1 : ℂ) * Cexp s)‖) (Real.log ‖φ k' ((1 : ℂ) * Cexp t)‖)) := by
    rw [show Submission.CDTPlan.rearrInt w φ = ∑ k, ∑ k', w k * w k' *
        (∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
          max (Real.log ‖φ k (Cexp s)‖) (Real.log ‖φ k' (Cexp t)‖)) from rfl]
    simp only [one_mul]
  have hlim : Filter.Tendsto (fun r : ℝ => Submission.CDTPlan.rearrInt w (fun k z => φ k (r * z)))
      (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 (Submission.CDTPlan.rearrInt w φ)) := by
    rw [hval, hfun]
    exact hsum
  -- the linear part tends to `A`
  have hlin : Filter.Tendsto (fun r : ℝ => A + C * Real.log r) (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 A) := by
    have hlog : Filter.Tendsto (fun r : ℝ => Real.log r) (𝓝[Set.Iio (1:ℝ)] 1) (𝓝 0) := by
      have h := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto
      rw [Real.log_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 := hlog.const_mul C
    rw [mul_zero] at h2
    have h3 := h2.const_add A
    rwa [add_zero] at h3
  -- the hypothesis holds eventually along `r → 1⁻`
  have hev : ∀ᶠ r in 𝓝[Set.Iio (1:ℝ)] 1, A + C * Real.log r ≤
      Submission.CDTPlan.rearrInt w (fun k z => φ k (r * z)) := by
    have hmem : Set.Ioo a 1 ∈ 𝓝[Set.Iio (1:ℝ)] 1 := by
      have h1 : Set.Ioi a ∈ 𝓝[Set.Iio (1:ℝ)] 1 :=
        nhdsWithin_le_nhds (Ioi_mem_nhds ha1)
      have h2 := self_mem_nhdsWithin (s := Set.Ioi a ∩ Set.Iio (1:ℝ)) (a := (1:ℝ))
      rw [nhdsWithin_inter_of_mem h1] at h2
      exact h2
    filter_upwards [hmem] with r hr
    have hr0 : 0 < r := lt_of_lt_of_le ha0 hr.1.le
    refine hineq r hr0 hr.2 (fun k z hz => ?_)
    have hnorm : ‖r * z‖ = r := by
      rw [norm_mul, hz, mul_one]
      exact (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_pos hr0)
    exact hann' k (r * z) (by rw [hnorm]; exact le_of_lt hr.1) (by rw [hnorm]; exact hr.2.le)
  exact le_of_tendsto_of_tendsto hlin hlim hev

end Work.Holonomy3
