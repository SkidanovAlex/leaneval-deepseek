import Mathlib

namespace Work.Drive.Mono

/-- A set of reals, every point of which is isolated in it, is countable.

The proof goes through the rationals: at an isolated point `t` of `S` we choose a rational open
interval `(q, r)` around `t` meeting `S` only in `t`; the assignment `t ↦ (q, r)` is injective on
`S` into `ℚ × ℚ`. -/
theorem countable_of_isolated_reals {S : Set ℝ}
    (h : ∀ t ∈ S, ∃ ε > 0, ∀ t' ∈ S, |t' - t| < ε → t' = t) : S.Countable := by
  classical
  have key : ∀ t : ℝ, ∃ p : ℚ × ℚ, t ∈ S → ((p.1 : ℝ) < t ∧ t < (p.2 : ℝ) ∧
      ∀ t' ∈ S, (p.1 : ℝ) < t' → t' < (p.2 : ℝ) → t' = t) := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨ε, hε, hiso⟩ := h t ht
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t - ε < t by linarith)
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show t < t + ε by linarith)
      refine ⟨(q, r), fun _ => ⟨hq2, hr1, fun t' ht' h1 h2 => hiso t' ht' ?_⟩⟩
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    · exact ⟨(0, 0), fun hcon => absurd hcon ht⟩
  set p : ℝ → ℚ × ℚ := fun t => Classical.choose (key t) with hp
  have hspec : ∀ t (ht : t ∈ S), (p t).1 < t ∧ t < (p t).2 ∧
      ∀ t' ∈ S, (p t).1 < t' → t' < (p t).2 → t' = t :=
    fun t ht => Classical.choose_spec (key t) ht
  refine Set.MapsTo.countable_of_injOn (f := p) (s := S) (t := (Set.univ : Set (ℚ × ℚ)))
    (fun x _ => Set.mem_univ _) ?_ (Set.countable_univ)
  intro t ht t' ht' heq
  have h1 : (p t).1 = (p t').1 := by rw [heq]
  have h2 : (p t).2 = (p t').2 := by rw [heq]
  have hlt1 : (p t).1 < t' := by rw [h1]; exact (hspec t' ht').1
  have hlt2 : t' < (p t).2 := by rw [h2]; exact (hspec t' ht').2.1
  exact ((hspec t ht).2.2 t' ht' hlt1 hlt2).symm

/-- **The zeros of a smooth function at which its derivative is non-zero form a countable set.**

At such a point `t` the function is locally strictly monotone (the derivative is non-zero and, by
smoothness, non-zero on a whole neighbourhood), so every zero of `f` with `f' ≠ 0` is *isolated* in
the zero set of `f`; a set of isolated points of a second-countable space is countable.

This is the counting step of the `offK` route (`Submission/Work/Drive/Mono/NOTES_s3_offK_route.md`):
the parameters at which a smooth knot crosses a smooth surface transversally are countable, so the
failure set of the `offK` clause is a countable union of vertical rays. -/
theorem countable_of_deriv_ne_zero (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    {t : ℝ | f t = 0 ∧ deriv f t ≠ 0}.Countable := by
  classical
  set S : Set ℝ := {t : ℝ | f t = 0 ∧ deriv f t ≠ 0} with hS
  have hcont : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hfcont : Continuous f := hf.continuous
  have hfdiff : DifferentiableOn ℝ f (Set.univ) :=
    (hf.differentiable (by norm_num)).differentiableOn
  -- Every point of `S` is isolated in `S`.
  have hisol : ∀ t ∈ S, ∃ ε > 0, ∀ t' ∈ S, |t' - t| < ε → t' = t := by
    intro t ht
    rw [hS] at ht
    obtain ⟨hft, hderiv⟩ := ht
    have hopen : IsOpen {x : ℝ | deriv f x ≠ 0} :=
      (isOpen_ne (x := (0 : ℝ))).preimage hcont
    obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hopen t hderiv
    refine ⟨ε, hεpos, ?_⟩
    intro t' ht' hdist
    rw [hS] at ht'
    obtain ⟨hft', _⟩ := ht'
    -- the derivative does not vanish between `t` and `t'`, so Rolle forbids a second zero
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨c, hc, hcd⟩ :=
        exists_deriv_eq_slope f hlt hfcont.continuousOn (hfdiff.mono (Set.subset_univ _))
      obtain ⟨hc1, hc2⟩ := hc
      have hcz : deriv f c = 0 := by rw [hcd, hft', hft]; simp
      have hdt : |t' - t| = t - t' := by
        rw [abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < t - t')]
      have hmem : c ∈ Metric.ball t ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hneg : c - t < 0 := by linarith
        rw [abs_of_neg hneg]
        rw [hdt] at hdist
        linarith
      exact hε hmem (by rw [hcz])
    · obtain ⟨c, hc, hcd⟩ :=
        exists_deriv_eq_slope f hlt hfcont.continuousOn (hfdiff.mono (Set.subset_univ _))
      obtain ⟨hc1, hc2⟩ := hc
      have hcz : deriv f c = 0 := by rw [hcd, hft', hft]; simp
      have hdt : |t' - t| = t' - t := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < t' - t)]
      have hmem : c ∈ Metric.ball t ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have hpos : 0 < c - t := by linarith
        rw [abs_of_pos hpos]
        rw [hdt] at hdist
        linarith
      exact hε hmem (by rw [hcz])
  exact countable_of_isolated_reals hisol

end Work.Drive.Mono
