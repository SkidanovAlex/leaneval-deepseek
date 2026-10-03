import Mathlib

/-!
# A `1`-periodic continuous function on a closed upper half plane is bounded

If `D : ℂ → ℂ` is `1`-periodic (`D (w + 1) = D w`), continuous on `{w | y ≤ w.im}` and has a
limit as `w.im → +∞` along the half planes `{w | M ≤ w.im}`, then `D` is bounded on
`{w | y ≤ w.im}`.

The proof is the classical one: the limit gives a bound on the far part `{M ≤ im}`, and on the
compact box `[0,1] × [y,M]` continuity gives a bound.  Every point of the half plane is the
translate, by an integer, of a point of that box (reduce `re w` modulo `1` using `Int.floor`), and
`D` is invariant under integer translations.
-/

namespace Work.Pert

open Filter Set

/-- A closed rectangle in `ℂ` (viewed through `re` and `im`) is compact. -/
lemma isCompact_reIm_box (a b c d : ℝ) :
    IsCompact {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · rw [show {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d}
        = (Complex.re ⁻¹' Set.Icc a b) ∩ (Complex.im ⁻¹' Set.Icc c d) by
      ext w; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
      tauto]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  · refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := |a| + |b| + |c| + |d|)).subset ?_
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have hr : |w.re| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
    have hi : |w.im| ≤ |c| + |d| := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le c, le_abs_self d, abs_nonneg c, abs_nonneg d]
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ (|a| + |b|) + (|c| + |d|) := by linarith
      _ = |a| + |b| + |c| + |d| := by ring

/-- Every point of `ℂ` is congruent modulo `ℤ` to a point whose real part lies in `[0,1]`. -/
lemma exists_translate_mem_box (w : ℂ) :
    ∃ n : ℤ, 0 ≤ (w - (n:ℂ)).re ∧ (w - (n:ℂ)).re ≤ 1 := by
  refine ⟨⌊w.re⌋, ?_, ?_⟩
  · have h := Int.floor_le w.re
    simp only [Complex.sub_re, Complex.intCast_re]
    linarith
  · have h := Int.lt_floor_add_one w.re
    simp only [Complex.sub_re, Complex.intCast_re]
    linarith

lemma bounded_on_upper_halfplane (D : ℂ → ℂ) {y : ℝ}
    (hper : ∀ w : ℂ, D (w + 1) = D w)
    (hcont : ContinuousOn D {w : ℂ | y ≤ w.im})
    (hend : ∃ L : ℂ, Filter.Tendsto D (Filter.comap Complex.im Filter.atTop) (nhds L)) :
    ∃ C : ℝ, ∀ w : ℂ, y ≤ w.im → ‖D w‖ ≤ C := by
  obtain ⟨L, hL⟩ := hend
  -- The limit at `+i∞` gives a bound on a far half plane `{w | M₀ ≤ w.im}`.
  obtain ⟨M₀, hM₀⟩ : ∃ M : ℝ, ∀ w : ℂ, M ≤ w.im → ‖D w‖ ≤ ‖L‖ + 1 := by
    have hball : D ⁻¹' Metric.ball L 1 ∈ Filter.comap Complex.im Filter.atTop :=
      hL.eventually (Metric.ball_mem_nhds L zero_lt_one)
    rw [Filter.mem_comap] at hball
    obtain ⟨t, ht, htsub⟩ := hball
    rw [Filter.mem_atTop_sets] at ht
    obtain ⟨b, hb⟩ := ht
    refine ⟨b, fun w hw => ?_⟩
    have hwb : w ∈ D ⁻¹' Metric.ball L 1 := htsub (hb (w.im) hw)
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hwb
    have h2 : ‖D w‖ ≤ ‖D w - L‖ + ‖L‖ := by simpa using norm_add_le (D w - L) L
    linarith
  set M := max M₀ y with hMdef
  have hMge0 : M₀ ≤ M := le_max_left _ _
  have hMgey : y ≤ M := le_max_right _ _
  -- Continuity on the compact fundamental box `[0,1] × [y,M]` gives a bound there.
  obtain ⟨C₁, hC₁⟩ := (isCompact_reIm_box (0:ℝ) 1 y M).exists_bound_of_continuousOn
    (hcont.mono (fun w hw => hw.2.2.1))
  refine ⟨max C₁ (‖L‖ + 1), fun w hw => ?_⟩
  by_cases hcase : w.im ≤ M
  · -- bring `w` into the box by an integer translation
    obtain ⟨n, hn0, hn1⟩ := exists_translate_mem_box w
    have him : (w - (n:ℂ)).im = w.im := by simp [Complex.sub_im]
    have hmem : w - (n:ℂ) ∈ {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 ∧ y ≤ w.im ∧ w.im ≤ M} :=
      ⟨hn0, hn1, by rw [him]; exact hw, by rw [him]; exact hcase⟩
    have hD : D (w - (n:ℂ)) = D w := by
      have hp : Function.Periodic D (1:ℂ) := hper
      have := hp.sub_int_mul_eq (x := w) n
      simpa using this
    calc ‖D w‖ = ‖D (w - (n:ℂ))‖ := by rw [hD]
      _ ≤ C₁ := hC₁ _ hmem
      _ ≤ max C₁ (‖L‖ + 1) := le_max_left _ _
  · rw [not_le] at hcase
    have hMw : M ≤ w.im := le_of_lt hcase
    calc ‖D w‖ ≤ ‖L‖ + 1 := hM₀ w (le_trans hMge0 hMw)
      _ ≤ max C₁ (‖L‖ + 1) := le_max_right _ _

end Work.Pert
