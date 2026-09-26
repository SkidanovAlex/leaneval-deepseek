import Mathlib
import Submission.Work.Drive.CleanDiscsDefs
import Submission.Work.Drive.TubeSign

/-!
# The innermost sign data, for a trace strictly inside the model disc

`Work.Drive.InnermostSignData` demands, besides the innermost trace and its planar
Jordan–Schoenflies datum, the *one-sidedness* of the level `levP ∘ D.e - 1` on the outward tube of
that trace: the sign of the level is constant there.

This file proves that the datum exists whenever the innermost trace is *strictly inside* the
model disc (`hint : ∀ i t, ‖(D.kappa i).γ t‖ < 1`).  In that case the outward tube of radius
below the gap between the trace and the unit circle is a genuine annulus around the trace, hence
preconnected (`Work.Drive.TubeOutsidePreconnectedSmall`), and the sign of the level is constant on
every preconnected set avoiding the torus (`Work.Drive.levP_sign_const`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Metric

namespace Work.Drive

open Work.CoreTopology

noncomputable section

/-- The radial retraction of `ℂ` onto the closed unit disc, as a map into the model disc. -/
def retrDisc (z : ℂ) : Work.InnermostDisk.Disc :=
  ⟨(max 1 ‖z‖)⁻¹ • z, by
    rw [Metric.mem_closedBall, dist_zero_right]
    rcases eq_or_ne z 0 with h | h
    · rw [h]; simp
    · have h1 : (0:ℝ) < max 1 ‖z‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
      calc ‖(max 1 ‖z‖)⁻¹ • z‖ = (max 1 ‖z‖)⁻¹ * ‖z‖ := by
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt h1))]
        _ ≤ 1 := by
            rw [inv_mul_le_iff₀ h1]
            simpa using le_max_right (1:ℝ) ‖z‖⟩

theorem retrDisc_coe {z : ℂ} (hz : ‖z‖ ≤ 1) : ((retrDisc z : Work.InnermostDisk.Disc) : ℂ) = z := by
  have h1 : max 1 ‖z‖ = 1 := max_eq_left hz
  simp only [retrDisc, h1, inv_one, one_smul]

theorem continuous_retrDisc : Continuous retrDisc := by
  refine Continuous.subtype_mk ?_ _
  have hcont : Continuous fun z : ℂ => (max 1 ‖z‖)⁻¹ • z :=
    ((continuous_const.max continuous_norm).inv₀
      (fun z => ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _)))).smul continuous_id
  simpa only [retrDisc] using hcont

/-- **The sign data of the innermost trace, when the trace is strictly inside the model disc.** -/
theorem exists_innermostSignData_of_strict (ψ : R3 ≃ₜ R3) (PD : PushData ψ) (D : WeakDatum ψ)
    (h : 0 < Fintype.card D.ι) (hint : ∀ i t, ‖(D.kappa i).γ t‖ < 1) :
    Nonempty (InnermostSignData ψ PD D) := by
  classical
  have hneι : Nonempty D.ι := Fintype.card_pos_iff.mp h
  -- the innermost trace and its planar Schoenflies datum
  obtain ⟨i₀, hsch, houtside, -⟩ := InnermostPlaneCurve D.kappa D.kappa_simple D.kappa_disj
    (fun i z hz => by obtain ⟨t, rfl⟩ := hz; exact le_of_lt (hint i t))
  -- the trace lies in a strictly smaller closed disc
  obtain ⟨ρ, hρlt, hρ⟩ := exists_norm_bound (D.kappa i₀).isCompact_trace
    ⟨(D.kappa i₀).γ 0, ⟨0, rfl⟩⟩ (fun z hz => by obtain ⟨t, rfl⟩ := hz; exact hint i₀ t)
  -- the radius of the outward tube
  obtain ⟨r₀, hr₀pos, hr₀⟩ := TubeOutsidePreconnectedSmall (D.kappa i₀) hsch
  obtain ⟨r₁, hr₁pos, hr₁⟩ := exists_pos_sep_compact_family
    (show IsCompact (Set.range (D.kappa i₀).γ) from (D.kappa i₀).isCompact_trace)
    ⟨(D.kappa i₀).γ 0, ⟨0, rfl⟩⟩ (fun j : {j : D.ι // j ≠ i₀} => Set.range (D.kappa j.1).γ)
    (fun j => show IsCompact (Set.range (D.kappa j.1).γ) from (D.kappa j.1).isCompact_trace)
    (fun j => D.kappa_disj (Ne.symm j.2))
  set r : ℝ := min r₀ (min r₁ ((1 - ρ)/2)) with hrdef
  have hrpos : 0 < r := lt_min hr₀pos (lt_min hr₁pos (by linarith))
  have hrle₀ : r ≤ r₀ := min_le_left _ _
  have hrρ : r ≤ (1 - ρ)/2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hrler₁ : r ≤ r₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  -- the outward tube
  have hTpre : IsPreconnected (tubeOutside (D.kappa i₀) hsch r) := hr₀ r hrpos hrle₀
  have hTball : tubeOutside (D.kappa i₀) hsch r ⊆ Metric.ball (0:ℂ) 1 :=
    tubeOutside_subset_ball hsch (fun t => by
      have := hρ ⟨t, rfl⟩; rwa [mem_closedBall, dist_zero_right] at this)
      (show r < 1 - ρ from by linarith)
  have hTmem : ∀ z ∈ tubeOutside (D.kappa i₀) hsch r, ‖z‖ < 1 := fun z hz => by
    have := hTball hz; rwa [Metric.mem_ball, dist_zero_right] at this
  -- on the tube, the level of `D.e` is never `1`
  have hne : ∀ z ∈ tubeOutside (D.kappa i₀) hsch r,
      PD.levP (D.e (retrDisc z)) - 1 ≠ 0 := by
    intro z hz h0
    have hzlt : ‖z‖ < 1 := hTmem z hz
    have hzcb : z ∈ Metric.closedBall (0:ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hzlt
    have hsub : (retrDisc z : Work.InnermostDisk.Disc) = ⟨z, hzcb⟩ :=
      Subtype.ext (retrDisc_coe (z := z) (le_of_lt hzlt))
    have hlev1 : PD.levP (D.e (retrDisc z)) = 1 := by linarith
    rw [hsub] at hlev1
    obtain ⟨j, t, ht⟩ := D.covers ⟨z, hzcb⟩ hzlt ((PD.hlev _).mp hlev1)
    rw [mem_tubeOutside] at hz
    by_cases hj : j = i₀
    · have hzmem : z ∈ Set.range (D.kappa i₀).γ := by
        rw [← hj]; exact ⟨t, ht⟩
      exact hz.2 (trace_subset_closure_V hsch hzmem)
    · exact hr₁ ⟨j, hj⟩ z (lt_of_lt_of_le hz.1 hrler₁) ⟨t, ht⟩
  have hcont : Continuous fun z : ℂ => PD.levP (D.e (retrDisc z)) - 1 :=
    (PD.hcont_lev.comp (D.e.continuous.comp continuous_retrDisc)).sub continuous_const
  -- the one-sidedness of the level on the tube
  have hsign := sign_const_of_preconnected hTpre (fun z : ℂ => PD.levP (D.e (retrDisc z)) - 1)
    hcont hne
  have hkey : ∀ z : ℂ, (hz : z ∈ Metric.closedBall (0:ℂ) 1) → ‖z‖ < 1 →
      (retrDisc z : Work.InnermostDisk.Disc) = ⟨z, hz⟩ := fun z hz hzlt =>
    Subtype.ext (retrDisc_coe (z := z) (le_of_lt hzlt))
  rcases hsign with hpos | hneg
  · refine ⟨i₀, hsch, houtside, r, hrpos, (1:ℝ), Or.inl rfl, ?_, ?_⟩
    · intro j hj z hz
      exact hr₁ ⟨j, hj⟩ z (lt_of_lt_of_le hz hrler₁)
    · intro z hz hzlt hnear hout
      have h1 : 0 < PD.levP (D.e (retrDisc z)) - 1 := hpos z ⟨hnear, hout⟩
      rw [show D.e ⟨z, hz⟩ = D.e (retrDisc z) from by rw [hkey z hz hzlt]]
      linarith
  · refine ⟨i₀, hsch, houtside, r, hrpos, (-1:ℝ), Or.inr rfl, ?_, ?_⟩
    · intro j hj z hz
      exact hr₁ ⟨j, hj⟩ z (lt_of_lt_of_le hz hrler₁)
    · intro z hz hzlt hnear hout
      have h1 : PD.levP (D.e (retrDisc z)) - 1 < 0 := hneg z ⟨hnear, hout⟩
      rw [show D.e ⟨z, hz⟩ = D.e (retrDisc z) from by rw [hkey z hz hzlt]]
      linarith

end

end Work.Drive
