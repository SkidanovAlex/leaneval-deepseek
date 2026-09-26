import Mathlib
import ChallengeDeps

/-!
# The sign split at a corner of the sweep loop (item (0) of the fold analysis)

At the *head* corner `B = r (tb σ)` of the chamfered sweep loop the two branches meet with
velocities along

* `T := velocity r (tb σ)` (the retained arc, incoming), and
* `-d` with `d := r (tb σ) - r (ta σ)` (the closing chord, outgoing).

Two cases, and they need *different* tools:

* **transversal** — `d` is not a positive multiple of `T`: then `T` and `-d` lie in a common open
  half-plane, i.e. there is a single direction `n` with `⟪n,T⟫ > 0` and `⟪n,-d⟫ > 0`.  Since the
  loop's branches are small perturbations of these two directions, one fixed `n` separates the whole
  box: no `havoid` input is needed here (this file).
* **fold** — `d = m • T`, `m > 0`: the two directions are antiparallel and no single direction
  exists; one needs the transverse separation supplied by `havoid`
  (`Work.Drive.sweepArc_tail_off_chordLine`, `Work.Drive.knot_foldTail_separation`).

`Work.Drive.exists_wedge_direction_of_not_antiparallel` is the abstract half-plane statement;
`Work.Drive.velocity_wedge_of_corner` upgrades it to a *neighbourhood* statement about the knot's
own velocity, which is the form in which the fixed-direction (CORE) argument of the sweep consumes
it.  Both are `sorry`-free.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The wedge at a non-fold corner (abstract form).**  If `d ≠ 0` is not a *positive* multiple of
`T ≠ 0`, then `T` and `-d` lie in a common open half-plane: there is `n ≠ 0` with `⟪n,T⟫ > 0` and
`⟪n,-d⟫ > 0`.

(If `⟪T,d⟫ ≤ 0` one may take `n = T - d`; otherwise the orthogonal part `b` of `d` off `T` is
nonzero and `n = T - (2⟪T,d⟫/‖b‖²) • b` works, since `⟪b,T⟫ = 0` and `⟪b,d⟫ = ‖b‖²`.) -/
theorem exists_wedge_direction_of_not_antiparallel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {T d : E} (hT : T ≠ 0) (hd : d ≠ 0)
    (h : ¬ ∃ m : ℝ, 0 < m ∧ d = m • T) :
    ∃ n : E, n ≠ 0 ∧ 0 < inner ℝ n T ∧ 0 < inner ℝ n (-d) := by
  have hT2 : 0 < ‖T‖ ^ 2 := pow_pos (norm_pos_iff.mpr hT) 2
  have hd2 : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.mpr hd) 2
  have hc : inner ℝ d T = inner ℝ T d := by rw [real_inner_comm]
  by_cases hle : inner ℝ T d ≤ 0
  · -- `d` has a nonpositive `T`-component: `n = T - d` works
    have hposT : 0 < inner ℝ (T - d) T := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
      nlinarith [hT2, hle, hc]
    have hne : T - d ≠ 0 := fun h0 => by
      rw [h0, inner_zero_left] at hposT
      exact lt_irrefl 0 hposT
    have hposd : 0 < inner ℝ (T - d) (-d) := by
      rw [inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq]
      nlinarith [hd2, hle, hc]
    exact ⟨T - d, hne, hposT, hposd⟩
  · -- `d` has a positive `T`-component; it is then not parallel to `T`, so the
    -- orthogonal part `b` of `d` off `T` is nonzero and `n = T - (2⟪T,d⟫/‖b‖²) • b` works
    have hlt : 0 < inner ℝ T d := lt_of_not_ge hle
    set b : E := d - (inner ℝ T d / ‖T‖ ^ 2) • T with hbdef
    have hbT : inner ℝ b T = 0 := by
      have h1 : inner ℝ (d - (inner ℝ T d / ‖T‖ ^ 2) • T) T
          = inner ℝ d T - (inner ℝ T d / ‖T‖ ^ 2) * inner ℝ T T := by
        rw [inner_sub_left, real_inner_smul_left]
      rw [hbdef, h1, real_inner_self_eq_norm_sq, hc]
      field_simp
      ring
    have hbne : b ≠ 0 := by
      intro hb0
      have h2 : d - (inner ℝ T d / ‖T‖ ^ 2) • T = 0 := by rw [← hbdef]; exact hb0
      refine h ⟨inner ℝ T d / ‖T‖ ^ 2, by positivity, ?_⟩
      exact sub_eq_zero.mp h2
    have hb2 : 0 < ‖b‖ ^ 2 := pow_pos (norm_pos_iff.mpr hbne) 2
    have hbd : inner ℝ b d = ‖b‖ ^ 2 := by
      have hsplit : d = b + (inner ℝ T d / ‖T‖ ^ 2) • T := by rw [hbdef]; abel
      rw [hsplit, inner_add_right, real_inner_smul_right, hbT, mul_zero, add_zero,
        real_inner_self_eq_norm_sq]
    have hposT : 0 < inner ℝ (T - (2 * inner ℝ T d / ‖b‖ ^ 2) • b) T := by
      rw [inner_sub_left, real_inner_smul_left, hbT, mul_zero, sub_zero,
        real_inner_self_eq_norm_sq]
      exact hT2
    have hne : T - (2 * inner ℝ T d / ‖b‖ ^ 2) • b ≠ 0 := fun h0 => by
      rw [h0, inner_zero_left] at hposT
      exact lt_irrefl 0 hposT
    have hposd : 0 < inner ℝ (T - (2 * inner ℝ T d / ‖b‖ ^ 2) • b) (-d) := by
      rw [inner_neg_right, inner_sub_left, real_inner_smul_left, hbd]
      have h1 : 2 * inner ℝ T d / ‖b‖ ^ 2 * ‖b‖ ^ 2 = 2 * inner ℝ T d := by
        field_simp
      rw [h1]
      linarith
    exact ⟨T - (2 * inner ℝ T d / ‖b‖ ^ 2) • b, hne, hposT, hposd⟩

/-- **The wedge at a non-fold corner, in knot language.**  If the chord `r tb - r ta` is not a
positive multiple of `velocity r tb`, then one fixed direction `n` is positive on the chord's
outgoing direction `-(r tb - r ta)` *and* on the knot's velocity on a whole one-sided neighbourhood
`(tb-ρ, tb]` of the corner.  This is exactly the hypothesis of the "CORE" fixed-direction argument
for boxes meeting a transversal corner. -/
theorem velocity_wedge_of_corner {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {ta tb : ℝ}
    (hT : velocity r tb ≠ 0) (hd : r tb - r ta ≠ 0)
    (h : ¬ ∃ m : ℝ, 0 < m ∧ r tb - r ta = m • velocity r tb) :
    ∃ n : Space, n ≠ 0 ∧ 0 < inner ℝ n (-(r tb - r ta)) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : ℝ, tb - ρ < θ → θ ≤ tb → 0 < inner ℝ n (velocity r θ) := by
  obtain ⟨n, hn, hposT, hposd⟩ :=
    exists_wedge_direction_of_not_antiparallel (E := Space) hT hd h
  have hv : Continuous (fun θ : ℝ => inner ℝ n (velocity r θ)) := by
    have hcont : Continuous (fun θ : ℝ => velocity r θ) := by
      simpa only [velocity] using hr.continuous_deriv (by simp)
    exact continuous_const.inner hcont
  have hc0 : ContinuousAt (fun θ : ℝ => inner ℝ n (velocity r θ)) tb := hv.continuousAt
  rw [Metric.continuousAt_iff] at hc0
  obtain ⟨δ, hδ, hδ'⟩ := hc0 (inner ℝ n (velocity r tb)) hposT
  refine ⟨n, hn, hposd, min δ 1, lt_min hδ one_pos, ?_⟩
  intro θ hθ1 hθ2
  have hd1 : dist θ tb < δ := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith : θ - tb ≤ 0)]
    have := min_le_left δ 1
    linarith
  have h1 := hδ' hd1
  rw [Real.dist_eq] at h1
  have h2 := abs_lt.mp h1
  linarith [h2.1]

end Work.Drive
