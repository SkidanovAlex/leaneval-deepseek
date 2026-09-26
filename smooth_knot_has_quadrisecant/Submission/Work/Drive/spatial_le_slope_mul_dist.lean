import Mathlib
import Submission.Work.Drive.Prelude

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# A uniform Lipschitz bound on the parameter circle

For a smooth knot `r` there is a `C¹`-neighbourhood of `r` and a constant `M`
such that *every* smooth knot `r'` in that neighbourhood satisfies the
Lipschitz estimate

  `‖knotMap r' a - knotMap r' b‖ ≤ M * dist a b`   (`a b : AddCircle period`).

The geometric content is the mean value theorem: `M` is a uniform bound for the
speed `‖velocity r'‖`, which is inherited from the (bounded, periodic) speed of
`r` plus the `C¹`-closeness.  The point of the statement is that the constant
`M` is *independent of `r'`*.

The proof is assembled from the following elementary pieces:

* `knotMap_coe_of_periodic` — for a `period`-periodic `r`, the circle map
  `knotMap r` agrees with `r` at the class of any real number (not only on the
  defining half-open period);
* `exists_zsmul_add_mem_Ico` — every real is congruent mod `period` to a point
  of `Ico 0 period`;
* `le_bound_of_periodic` / `exists_velocity_bound` — the speed of a smooth knot
  is bounded;
* `norm_sub_le_of_velocity_bound_mul` — the mean value theorem in the form needed.
-/

/-- For a `period`-periodic curve `r`, the induced map `knotMap r` on the
parameter circle agrees with `r` at the class of *any* real number. -/
lemma knotMap_coe_of_periodic {r : ℝ → Space} (hper : Function.Periodic r period) (t : ℝ) :
    knotMap r (t : AddCircle period) = r t := by
  set τ : ℝ := (AddCircle.equivIco period 0 (t : AddCircle period)).1 with hτ
  have hτmem : τ ∈ Set.Ico 0 period := by
    have h := (AddCircle.equivIco period 0 (t : AddCircle period)).2
    rw [hτ]; simpa using h
  have hclass : (τ : AddCircle period) = (t : AddCircle period) := by
    rw [hτ]; exact AddCircle.coe_equivIco
  have hmod : t ≡ τ [PMOD period] :=
    (AddCommGroup.modEq_iff_eq_mod_zmultiples).2 hclass.symm
  obtain ⟨m, hm⟩ := (AddCommGroup.modEq_iff_zsmul).1 hmod
  have hrt : r τ = r t := by
    have h1 : τ = t + m • period := by
      rw [zsmul_eq_mul] at hm ⊢
      linarith
    rw [h1]; exact (hper.zsmul m) t
  have hmap : knotMap r (τ : AddCircle period) = r τ := by
    unfold knotMap
    exact AddCircle.liftIco_zero_coe_apply hτmem
  rw [← hclass, hmap, hrt]

/-- Every real number is congruent modulo `period` to an element of
`Ico 0 period` (i.e. of the defining half-open period). -/
lemma exists_zsmul_add_mem_Ico (t : ℝ) : ∃ n : ℤ, t + n • period ∈ Set.Ico 0 period := by
  set τ : ℝ := (AddCircle.equivIco period 0 (t : AddCircle period)).1 with hτ
  have hτmem : τ ∈ Set.Ico 0 period := by
    have h := (AddCircle.equivIco period 0 (t : AddCircle period)).2
    rw [hτ]; simpa using h
  have hclass : (τ : AddCircle period) = (t : AddCircle period) := by
    rw [hτ]; exact AddCircle.coe_equivIco
  have hmod : t ≡ τ [PMOD period] :=
    (AddCommGroup.modEq_iff_eq_mod_zmultiples).2 hclass.symm
  obtain ⟨m, hm⟩ := (AddCommGroup.modEq_iff_zsmul).1 hmod
  refine ⟨m, ?_⟩
  have h1 : t + m • period = τ := by
    rw [zsmul_eq_mul] at hm
    rw [zsmul_eq_mul]
    linarith
  rw [h1]
  exact hτmem

/-- A bound on one period of a `period`-periodic function bounds it everywhere. -/
lemma le_bound_of_periodic {f : ℝ → Space} (hper : Function.Periodic f period)
    {B : ℝ} (hB : ∀ t ∈ Set.Icc 0 period, ‖f t‖ ≤ B) (t : ℝ) : ‖f t‖ ≤ B := by
  obtain ⟨n, hn⟩ := exists_zsmul_add_mem_Ico t
  have h1 : f t = f (t + n • period) := ((hper.zsmul n) t).symm
  rw [h1]
  exact hB _ ⟨hn.1, le_of_lt hn.2⟩

/-- The speed of a smooth knot is bounded away from infinity. -/
lemma exists_velocity_bound {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, ‖velocity r t‖ ≤ M := by
  have hcont : Continuous (fun t : ℝ => ‖velocity r t‖) := by
    simpa [velocity] using (hr.smooth.continuous_deriv (by simp)).norm
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (f := fun t : ℝ => ‖velocity r t‖) ⟨0, le_rfl, period_pos.le⟩ hcont.continuousOn
  refine ⟨‖velocity r t0‖ + 1, by positivity, fun t => ?_⟩
  have hB : ∀ t ∈ Set.Icc (0:ℝ) period, ‖velocity r t‖ ≤ ‖velocity r t0‖ :=
    fun t ht => hmax ht
  have hper : Function.Periodic (velocity r) period := fun x => hr.velocity_periodic x
  have := le_bound_of_periodic hper hB t
  linarith

/-- The mean value theorem in the form used here: a speed bound gives a
Lipschitz bound on the whole line. -/
lemma norm_sub_le_of_velocity_bound_mul {f : ℝ → Space} (hdiff : Differentiable ℝ f)
    {M : ℝ} (hM : ∀ t, ‖velocity f t‖ ≤ M) (s t : ℝ) :
    ‖f s - f t‖ ≤ M * |s - t| := by
  rcases le_or_gt s t with hst | hts
  · have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := fun x => deriv f x)
        (C := M) (a := s) (b := t)
        (fun x hx => (hdiff x).hasDerivAt.hasDerivWithinAt)
        (fun x hx => by simpa [velocity] using hM x)
        t ⟨hst, le_rfl⟩
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst), norm_sub_rev]
    exact h
  · have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := fun x => deriv f x)
        (C := M) (a := t) (b := s)
        (fun x hx => (hdiff x).hasDerivAt.hasDerivWithinAt)
        (fun x hx => by simpa [velocity] using hM x)
        s ⟨hts.le, le_rfl⟩
    rw [abs_of_pos (sub_pos.mpr hts)]
    exact h

/-- **Uniform Lipschitz bound.** For a smooth knot `r` there are `ε > 0` and
`M > 0` such that every smooth knot `r'` whose values and velocities are
pointwise `ε`-close to those of `r` satisfies
`‖knotMap r' a - knotMap r' b‖ ≤ M * dist a b` for all points `a`, `b` of the
parameter circle. -/
theorem spatial_le_slope_mul_dist {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, 0 < M ∧
      ∀ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
        LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε ∧
          ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
            LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < ε) →
        ∀ a b : AddCircle LeanEval.KnotTheory.Quadrisecant.period,
          ‖LeanEval.KnotTheory.Quadrisecant.knotMap r' a -
            LeanEval.KnotTheory.Quadrisecant.knotMap r' b‖ ≤ M * dist a b := by
  obtain ⟨B, hBpos, hB⟩ := exists_velocity_bound hr
  refine ⟨1, one_pos, B + 1, by linarith, fun r' hr' hclose a b => ?_⟩
  -- Speed bound for the perturbed knot, uniform in `r'`.
  have hvel : ∀ t : ℝ, ‖velocity r' t‖ ≤ B + 1 := by
    intro t
    have h1 := (hclose t).2
    have h2 := hB t
    have h3 : ‖velocity r' t‖ ≤ ‖velocity r t‖ + ‖velocity r' t - velocity r t‖ := by
      calc ‖velocity r' t‖ = ‖(velocity r' t - velocity r t) + velocity r t‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖velocity r' t - velocity r t‖ + ‖velocity r t‖ := norm_add_le _ _
        _ = ‖velocity r t‖ + ‖velocity r' t - velocity r t‖ := by rw [add_comm]
    linarith
  have hdiff : Differentiable ℝ r' := hr'.smooth.differentiable (by simp)
  -- Real representatives of `b` and of `a - b` (the latter chosen of minimal
  -- absolute value in its class).
  set β : ℝ := (AddCircle.equivIco period 0 b).1 with hβ
  set w : ℝ := (AddCircle.equivIco period 0 (a - b)).1 with hw
  set u : ℝ := w - ((round (period⁻¹ * w) : ℤ) : ℝ) * period with hu
  have hβclass : (β : AddCircle period) = b := by
    rw [hβ]; exact AddCircle.coe_equivIco
  have hwclass : (w : AddCircle period) = a - b := by
    rw [hw]; exact AddCircle.coe_equivIco
  have hzero : ((((round (period⁻¹ * w) : ℤ) : ℝ) * period : ℝ) : AddCircle period) = 0 := by
    rw [← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
  have huclass : (u : AddCircle period) = a - b := by
    rw [hu, AddCircle.coe_sub, hzero, sub_zero, hwclass]
  -- `u` is the (smallest) representative of `a - b`, so `|u| = dist a b`.
  have hnormw : ‖(w : AddCircle period)‖ = |u| := by
    rw [hu, ← AddCircle.norm_eq period (x := w)]
  have hule : |u| ≤ period / 2 := by
    have h2 : ‖(w : AddCircle period)‖ ≤ |period| / 2 :=
      AddCircle.norm_le_half_period period period_ne_zero
    have h3 : |period| = period := abs_of_pos period_pos
    linarith [hnormw]
  have huabs : ‖(u : AddCircle period)‖ = |u| :=
    (AddCircle.norm_coe_eq_abs_iff period period_ne_zero).2 (by
      rw [abs_of_pos period_pos]; exact hule)
  have hdistab : dist a b = |u| := by
    rw [dist_eq_norm, ← huclass, huabs]
  -- `a` is the class of `β + u`.
  have hab : a = ((β + u : ℝ) : AddCircle period) := by
    rw [AddCircle.coe_add, hβclass, huclass]
    abel
  have hknota : knotMap r' a = r' (β + u) := by
    rw [hab]
    exact knotMap_coe_of_periodic hr'.periodic (β + u)
  have hknotb : knotMap r' b = r' β := by
    rw [← hβclass]
    exact knotMap_coe_of_periodic hr'.periodic β
  rw [hknota, hknotb, hdistab]
  have hmvt := norm_sub_le_of_velocity_bound_mul hdiff hvel (β + u) β
  simpa using hmvt

end Work.Drive
