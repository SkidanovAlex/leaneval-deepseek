import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.anyDentData_exists
import Submission.Work.Drive.Final.dent_annulus_defs

/-!
# A dent at every event with a depth controlled by an arbitrary positive function of `r` and `κ`

(`NOTES_LEAD_L4b.md` §1 A.)  `Work.Drive.Final.anyDentData_exists` produces, at every event `p` of a
good tilted sweep and for every prescribed `a₀ > 0`, a datum with `D.a' ≤ a₀`.  The consumer
`Work.Drive.Final.exists_dentSurface` instead needs

* the cutoff `χ` of the datum to be `C^∞` (`ContDiff ℝ (⊤ : ℕ∞)`) and to equal `1` on the whole
  closed interval `[-1/2, 1/2]` — the *core* of the dent on which the deformation is an exact
  translation, used in the margin analysis of `dent_annulus_regular`;
* the depth `D.a'` to be bounded by an *arbitrary* positive quantity `A D.r D.κ` depending on the
  radius `D.r` and the Lipschitz constant `D.κ` — the order `r` first, then `A`, then `a'` matters,
  and the radius is part of the datum only once it has been chosen.

The construction is the one of `Work.Drive.Final.anyDentData_exists`, with two changes: the cutoff is
the `ContDiffBump (0 : ℝ) = ⟨1/2, 1, …⟩` (`C^∞`, and `= 1` on the closed ball of radius `1/2`), and
the depth is `a' := min Ab (min (A r κ) (ρ/4))`, chosen *after* `r` and `κ` are fixed.
-/

open LeanEval.KnotTheory.PardonDistortion
open scoped Topology

namespace Work.Drive.Final

open Set

noncomputable section

/-! ## The `C^∞` cutoff, equal to `1` on `[-1/2, 1/2]` -/

/-- **A `C^∞` cutoff of a dent, equal to `1` on the closed interval `[-1/2, 1/2]`.**  This is
`Work.Drive.Final.exists_dent_cutoff_nonneg` with the two extra conclusions required by
`Work.Drive.Final.exists_dentSurface`: the cutoff is `C^∞` (`ContDiff ℝ (⊤ : ℕ∞)`) and it is `1` on
the whole core `|t| ≤ 1/2`. -/
theorem exists_dent_cutoff_smooth :
    ∃ (χ : ℝ → ℝ) (κ : ℝ), Continuous χ ∧ χ 0 = 1 ∧ (∀ t : ℝ, 1 ≤ t → χ t = 0) ∧
      (∀ t : ℝ, |χ t| ≤ 1) ∧ (∀ t : ℝ, 0 ≤ χ t) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → χ t = 1) ∧
      Differentiable ℝ χ ∧ 0 < κ ∧ (∀ t : ℝ, |deriv χ t| ≤ κ) ∧
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ t : ℝ, |t| ≤ 1 / 2 → χ t = 1) := by
  let F : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
  have hFdiff : Differentiable ℝ (F : ℝ → ℝ) := (F.contDiff (n := 1)).differentiable (by simp)
  have hFcont : Continuous (deriv (F : ℝ → ℝ)) := (F.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨t₀, -, hmax⟩ := (isCompact_closedBall (0:ℝ) 1).exists_isMaxOn ⟨0, by simp⟩
    hFcont.abs.continuousOn
  refine ⟨F, |deriv (F : ℝ → ℝ) t₀| + 1, F.continuous, ?_, ?_, ?_, ?_, ?_, hFdiff, by positivity,
    ?_, ?_, ?_⟩
  · simpa using F.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num : (0:ℝ) ≤ 1/2))
  · intro t ht
    refine F.zero_of_le_dist ?_
    show (1:ℝ) ≤ dist t (0:ℝ)
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ t)]
    exact ht
  · intro t
    rw [abs_of_nonneg F.nonneg]
    exact F.le_one
  · intro t
    exact F.nonneg
  · refine ⟨1/2, by norm_num, fun t ht => ?_⟩
    refine F.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    exact ht
  · intro t
    by_cases ht : t ∈ Metric.closedBall (0:ℝ) 1
    · have hle : |deriv (↑F) t| ≤ |deriv (↑F) t₀| := hmax ht
      linarith
    · have h1 : 1 < |t| := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs] at ht
        push Not at ht
        exact ht
      have hev : (F : ℝ → ℝ) =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds h1] with s hs
        refine F.zero_of_le_dist ?_
        show (1:ℝ) ≤ dist s (0:ℝ)
        rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
        linarith [hs]
      rw [hev.deriv_eq]
      simp only [deriv_const, abs_zero]
      linarith [abs_nonneg (deriv (↑F) t₀)]
  · exact F.contDiff (n := ⊤)
  · intro t ht
    refine F.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    exact ht

/-! ## The datum from a push direction, with the depth controlled by `A r κ` -/

/-- **The datum exists as soon as the direction and the slack are given, with the depth bounded by
`A r κ`.**  Same as `Work.Drive.Final.anyDentDatum_of_direction`, except that the depth is chosen
after the radius `r` and the Lipschitz constant `κ` and is bounded by the prescribed positive
`A r κ`, and the cutoff is `C^∞` and equal to `1` on `[-1/2, 1/2]`. -/
theorem anyDentDatum_of_direction_depth {ψ : Submission.Diffeo} {K : Knot} {s R : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (hoffK : ∀ p : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p →
      ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p)
    {p : ℝ × ℝ} (hp : IsAnyEvent ψ s c σ u v h ℓ p)
    (hU : U ∈ nhds (Work.BoxShrink.Pinch.par ψ p))
    {A : ℝ → ℝ → ℝ} (hA : ∀ r κ : ℝ, 0 < r → 0 < κ → 0 < A r κ)
    {d : R3} (hdn : ‖d‖ = 1) (hdv : inner ℝ v d = 0) (hdpos : 0 < ℓ d)
    (hslack : ∀ i : Fin 3, d (σ i) = 0 ∨
      |Work.BoxShrink.Pinch.par ψ p (σ i) - c (σ i)| < Submission.boxSide i * s) :
    ∃ D : AnyDentDatum ψ K s c σ u v h R ℓ U, D.p = p ∧ D.a' ≤ A D.r D.κ ∧
      ContDiff ℝ (⊤ : ℕ∞) D.χ ∧ ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1 := by
  obtain ⟨rb, hrb, Ab, hAb, hboxpres⟩ :=
    box_pres_of_slack (centre := Work.BoxShrink.Pinch.par ψ p) hdn hslack
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r₀, hr₀, havoids₀⟩ :=
    knotAvoids_radius_exists K (Work.BoxShrink.Pinch.par ψ p) (hoffK p hp)
  obtain ⟨χ, κ, hχcont, hχ0, hχout, hχle, hχnn, hχε, hχdiff, hκpos, hκbd, hχsm, hχhalf⟩ :=
    exists_dent_cutoff_smooth
  set r : ℝ := min rb (min (ρ / 4) r₀) with hrdef
  set a' : ℝ := min Ab (min (A r κ) (ρ / 4)) with hadef
  have hrpos : 0 < r := lt_min hrb (lt_min (by linarith) hr₀)
  have hArκ : 0 < A r κ := hA r κ hrpos hκpos
  have hapos : 0 < a' := lt_min hAb (lt_min hArκ (by linarith))
  have hrle : r ≤ rb := min_le_left _ _
  have hrleρ : r ≤ ρ / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrler₀ : r ≤ r₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hale : a' ≤ Ab := min_le_left _ _
  have haleA : a' ≤ A r κ := le_trans (min_le_right _ _) (min_le_left _ _)
  have haleρ : a' ≤ ρ / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨{ χ := χ, χ_cont := hχcont, χ_zero_apply := hχ0, χ_eq_zero := hχout, χ_le_one := hχle,
            χ_nonneg := hχnn, χ_eq_one_near := hχε, χ_diff := hχdiff, κ := κ, κ_pos := hκpos,
            χ_deriv_bound := hκbd, p := p, isEvent := hp,
            centre := Work.BoxShrink.Pinch.par ψ p, centre_eq := rfl, d := d, d_norm := hdn,
            d_orth_v := hdv, push_pos := hdpos, r := r, r_pos := hrpos, a' := a', a'_pos := hapos,
            δ := a', δ_pos := hapos, a'_le_δ := le_rfl, ball_sub := ?_, box_pres := ?_,
            knotAvoids := ?_ }, rfl, haleA, hχsm, hχhalf⟩
  · -- the ball of radius `r + a'` about the centre lies in `U`
    intro z hz
    apply hρsub
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  · -- the deformation preserves the open box on the ball of radius `r`
    intro z hz
    have hz' : ‖z - Work.BoxShrink.Pinch.par ψ p‖ ≤ rb := le_trans hz hrle
    have ht0 : 0 ≤ a' * χ (‖z - Work.BoxShrink.Pinch.par ψ p‖ / r) :=
      mul_nonneg (le_of_lt hapos) (hχnn _)
    have htA : a' * χ (‖z - Work.BoxShrink.Pinch.par ψ p‖ / r) ≤ Ab := by
      have h1 : χ (‖z - Work.BoxShrink.Pinch.par ψ p‖ / r) ≤ 1 :=
        le_trans (le_abs_self _) (hχle _)
      have h2 : a' * χ (‖z - Work.BoxShrink.Pinch.par ψ p‖ / r) ≤ a' * 1 :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hapos)
      linarith
    exact hboxpres z hz' _ ht0 htA
  · -- the radius misses the knot
    intro t
    exact le_trans hrler₀ (havoids₀ t)

/-! ## The producer, with the depth bounded by `A r κ` -/

theorem anyDentData_exists_depthFn {ψ : Submission.Diffeo} {K : Knot} {s R : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {U : Set R3}
    (hG : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1) {p : ℝ × ℝ}
    (hp : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p)
    (hU : U ∈ nhds (Work.BoxShrink.Pinch.par ψ p))
    (A : ℝ → ℝ → ℝ) (hA : ∀ r κ : ℝ, 0 < r → 0 < κ → 0 < A r κ) :
    ∃ D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U, D.p = p ∧ D.a' ≤ A D.r D.κ ∧
      ContDiff ℝ (⊤ : ℕ∞) D.χ ∧ ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1 := by
  obtain ⟨hGS2, hEF, hbelt, -, -, -, hcross, hoffK, -, -⟩ := hG
  obtain ⟨hGS, -, -, -, -, -⟩ := hGS2
  obtain ⟨hTilt, -, -, -, -⟩ := hGS
  obtain ⟨-, hv1, hℓne, hℓv, -, -, -, -, -, -, -⟩ := hTilt
  rcases hp with hp1 | hp2 | hp3
  · -- an interior event: the centre lies in the open box
    obtain ⟨d, h1, h2, h3⟩ := exists_dent_direction hv1 hℓv hℓne
    exact anyDentDatum_of_direction_depth hoffK (Or.inl hp1) hU hA h1 h2 h3
      (fun i => Or.inr (Submission.mem_PBox.mp hp1.1 i))
  · -- a face event: the centre lies in the open box as well
    obtain ⟨d, h1, h2, h3⟩ := exists_dent_direction hv1 hℓv hℓne
    exact anyDentDatum_of_direction_depth hoffK (Or.inr (Or.inl hp2)) hU hA h1 h2 h3
      (fun i => Or.inr (Submission.mem_PBox.mp hp2.1 i))
  · -- a corner event: the centre lies on the boundary of the box
    obtain ⟨hclos, hbn, hslab⟩ := hp3
    obtain ⟨i₀, hi₀2, -, hlt⟩ :=
      corner_extremal_unique hEF hbelt (Work.BoxShrink.Pinch.par_mem_carrier ψ p) hclos hbn hslab
    obtain ⟨d, h1, h2, h3, h4⟩ :=
      exists_unit_of_crossDir (v := v) (ℓ := ℓ) (k := σ i₀) (hcross i₀ hi₀2)
    refine anyDentDatum_of_direction_depth hoffK (Or.inr (Or.inr ⟨hclos, hbn, hslab⟩)) hU hA
      h1 h2 h3 ?_
    intro i
    by_cases hii : i = i₀
    · left; rw [hii]; exact h4
    · exact Or.inr (hlt i hii)

end

end Work.Drive.Final
