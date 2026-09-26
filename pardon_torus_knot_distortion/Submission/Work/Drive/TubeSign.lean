import Mathlib
import Submission.Work.Drive.PushSide
import Submission.Work.Drive.TubeOutsidePreconnectedSmall

/-!
# The sign of the level on the outward tube

Elementary metric facts used to choose the radius of the outward tube of an innermost trace, and
to see that the tube lies in the open model disc when the trace is strictly inside it:

* `exists_pos_sep_compact` — disjoint compact sets are at positive distance, in the form needed
  for the `avoids` clause of `InnermostSignData`;
* `exists_norm_bound` — a compact set of the open disc is contained in a smaller closed disc;
* `tubeOutside_subset_ball` — the outward tube of radius below the gap between the trace and the
  unit circle lies in the open model disc.

Together with `Work.Drive.levP_sign_const` (the sign of the level is constant on connected sets
avoiding the torus) and the preconnectedness of the outward tube, these give the one-sidedness
clause of `InnermostSignData` whenever the innermost trace is *strictly inside* the model disc.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Metric

namespace Work.Drive

noncomputable section

/-- **Disjoint compact sets are at positive distance**, in the form needed for the `avoids`
clause: there is `r > 0` such that nothing at distance `< r` from `A` lies in `B`. -/
theorem exists_pos_sep_compact {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hne : A.Nonempty) (hd : Disjoint A B) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, infDist z A < r → z ∉ B := by
  rcases eq_empty_or_nonempty B with hB0 | hBne
  · exact ⟨1, one_pos, fun z _ hz => by rw [hB0] at hz; exact hz⟩
  obtain ⟨p, hp, hmin⟩ := (hA.prod hB).exists_isMinOn (hne.prod hBne)
    (by fun_prop : ContinuousOn (fun q : ℂ × ℂ => dist q.1 q.2) (A ×ˢ B))
  have hpA : p.1 ∈ A := hp.1
  have hpB : p.2 ∈ B := hp.2
  have hpos : 0 < dist p.1 p.2 := by
    rcases eq_or_ne p.1 p.2 with h | h
    · exact absurd (h ▸ hpB) (Set.disjoint_left.mp hd hpA)
    · exact dist_pos.mpr h
  refine ⟨dist p.1 p.2, hpos, ?_⟩
  intro z hz hzB
  have hle : dist p.1 p.2 ≤ infDist z A := by
    rw [le_infDist hne]
    intro a ha
    have hv : (a, z) ∈ A ×ˢ B := ⟨ha, hzB⟩
    have h2 := hmin hv
    simpa only [Set.mem_ofPred_eq, Prod.fst, Prod.snd, dist_comm] using h2
  linarith

/-- **Disjoint compact sets are at positive distance, uniformly over a finite family.** -/
theorem exists_pos_sep_compact_family {A : Set ℂ} (hA : IsCompact A) (hne : A.Nonempty)
    {ι : Type} [Fintype ι] (B : ι → Set ℂ) (hB : ∀ i, IsCompact (B i))
    (hd : ∀ i, Disjoint A (B i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ (i : ι) (z : ℂ), infDist z A < r → z ∉ B i := by
  classical
  have hone : ∀ i, ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, infDist z A < r → z ∉ B i :=
    fun i => exists_pos_sep_compact hA (hB i) hne (hd i)
  choose r hr_pos hr_sep using hone
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (hι.elim i)⟩
  · obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset ι) r Finset.univ_nonempty
    refine ⟨r i₀, hr_pos i₀, fun i z hz => hr_sep i z (lt_of_lt_of_le hz ?_)⟩
    exact hmin i (Finset.mem_univ i)

/-- **A compact set of the open unit disc lies in a strictly smaller closed disc.** -/
theorem exists_norm_bound {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (h : ∀ z ∈ K, ‖z‖ < 1) :
    ∃ ρ : ℝ, ρ < 1 ∧ K ⊆ closedBall (0 : ℂ) ρ := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (by fun_prop : ContinuousOn (fun z : ℂ => ‖z‖) K)
  refine ⟨‖x‖, h x hx, fun z hz => ?_⟩
  rw [mem_closedBall, dist_zero_right]
  exact hmax hz

/-- The outward tube of a plane curve, of radius below the gap between the trace and the unit
circle, is contained in the open model disc. -/
theorem tubeOutside_subset_ball {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies c) {ρ r : ℝ}
    (hρ : ∀ t : ℝ, ‖c.γ t‖ ≤ ρ) (hr : r < 1 - ρ) :
    tubeOutside c S r ⊆ Metric.ball (0 : ℂ) 1 := by
  intro z hz
  rw [mem_tubeOutside] at hz
  obtain ⟨y, hy, hd⟩ := (infDist_lt_iff (s := Set.range c.γ) ⟨c.γ 0, ⟨0, rfl⟩⟩).mp hz.1
  obtain ⟨t, rfl⟩ := hy
  rw [Metric.mem_ball, dist_zero_right]
  have h2 : ‖z‖ ≤ ‖z - c.γ t‖ + ‖c.γ t‖ := by
    have hz' : z = (z - c.γ t) + c.γ t := by ring
    simpa only [← hz'] using norm_add_le (z - c.γ t) (c.γ t)
  have h3 : ‖z - c.γ t‖ = dist z (c.γ t) := by rw [dist_eq_norm]
  rw [h3] at h2
  have h4 := hρ t
  linarith

end

end Work.Drive
