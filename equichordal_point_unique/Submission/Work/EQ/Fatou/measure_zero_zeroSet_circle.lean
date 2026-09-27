import Mathlib

/-!
# The zero set of a holomorphic function on a circle is Lebesgue-null

Let `h : ℂ → ℂ` be complex-differentiable on the open unit ball and suppose `h 0 ≠ 0`.
Then `h` is not identically zero near the origin, hence (principal of isolated zeros,
plus the identity theorem on the connected ball) its zero set is a *discrete* subset of
the ball.  Intersecting with a compact piece of the circle `|z| = ρ` (`0 < ρ < 1`) and
pulling back along the locally injective parametrisation `θ ↦ ρ e^{iθ}` shows that

  `{θ : ℝ | h (ρ e^{iθ}) = 0}`

is a closed discrete subset of `ℝ`, hence countable, hence of Lebesgue measure zero.

The main statement is `Work.EQ.Fatou.measure_zero_zeroSet_circle`.
-/

namespace Work.EQ.Fatou

open MeasureTheory Metric Complex Filter

noncomputable section

/-- The point `ρ e^{iθ}` of the circle of radius `ρ` centred at the origin. -/
private def circlePt (ρ θ : ℝ) : ℂ := (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- The parametrisation `θ ↦ e^{iθ}` of the unit circle is injective on intervals of
length `< π`: if `|θ - θ'| < π` and `e^{iθ} = e^{iθ'}`, then `θ = θ'`. -/
private theorem exp_I_inj_of_abs_sub_lt_pi {θ θ' : ℝ} (h : |θ - θ'| < Real.pi)
    (he : Complex.exp ((θ:ℂ) * Complex.I) = Complex.exp ((θ':ℂ) * Complex.I)) : θ = θ' := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have h3 : ((θ:ℂ) - (θ':ℂ)) * Complex.I = ((n:ℂ) * (2 * (Real.pi:ℂ))) * Complex.I := by
    rw [sub_mul, hn]; ring
  have h4 : (θ:ℂ) - (θ':ℂ) = (n:ℂ) * (2 * (Real.pi:ℂ)) :=
    mul_right_cancel₀ Complex.I_ne_zero h3
  have h5 : θ - θ' = (n:ℝ) * 2 * Real.pi := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sub]
    push_cast
    rw [h4]; ring
  have h6 : |(n:ℝ)| * 2 * Real.pi < Real.pi := by
    have h' : |(n:ℝ) * 2 * Real.pi| < Real.pi := by rw [← h5]; exact h
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos] at h'
    nlinarith [h']
  have h8 : |(n:ℝ)| < 1 := by nlinarith [h6, Real.pi_pos]
  have h9 : n = 0 := by
    have h8i : ((|n| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact h8
    have h8j : (|n| : ℤ) < 1 := by
      rw [show (1:ℝ) = ((1:ℤ):ℝ) by norm_num] at h8i
      exact Int.cast_lt.mp h8i
    have hpos : (0:ℤ) ≤ |n| := abs_nonneg n
    have : (|n| : ℤ) = 0 := by omega
    exact abs_eq_zero.mp this
  rw [h9] at h5; simp at h5; linarith

/-- If `h` is complex-differentiable on the open unit ball and `h 0 ≠ 0`, the zero set of
`h` inside the ball is a discrete set: every point of it has an open neighbourhood meeting
the zero set only in that point. -/
private theorem isDiscrete_zeroSet_ball {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (h0 : h 0 ≠ 0) : IsDiscrete ({z : ℂ | h z = 0} ∩ Metric.ball 0 1) := by
  have han : AnalyticOnNhd ℂ h (Metric.ball 0 1) := fun z hz =>
    AnalyticOn.analyticAt (Metric.isOpen_ball.mem_nhds hz) (hh.analyticOn Metric.isOpen_ball)
  rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected (isPreconnected_ball) with hz | hne
  · exact absurd (hz (by simp [Metric.mem_ball])) h0
  · exact isDiscrete_of_codiscreteWithin hne

theorem measure_zero_zeroSet_circle {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (h0 : h 0 ≠ 0) {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0:ℝ) 1) :
    MeasureTheory.volume {θ : ℝ | h (ρ * Complex.exp ((θ:ℂ) * Complex.I)) = 0} = 0 := by
  have hρ0 : 0 < ρ := hρ.1
  have hρ1 : ρ < 1 := hρ.2
  change MeasureTheory.volume {θ : ℝ | h (circlePt ρ θ) = 0} = 0
  set S : Set ℝ := {θ : ℝ | h (circlePt ρ θ) = 0} with hS
  have hc : Continuous (circlePt ρ) := by unfold circlePt; fun_prop
  have hnorm : ∀ θ, ‖circlePt ρ θ‖ = ρ := fun θ => by
    rw [circlePt, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    simp [abs_of_pos hρ0]
  have hball : ∀ θ : ℝ, circlePt ρ θ ∈ Metric.ball (0:ℂ) 1 := fun θ => by
    rw [Metric.mem_ball, dist_zero_right, hnorm θ]; exact hρ1
  have hcont : Continuous (fun θ : ℝ => h (circlePt ρ θ)) :=
    hh.continuousOn.comp_continuous hc hball
  have hSclosed : IsClosed S := by
    rw [hS]; exact isClosed_singleton.preimage hcont
  have hinj : ∀ θ θ' : ℝ, |θ - θ'| < Real.pi → circlePt ρ θ = circlePt ρ θ' → θ = θ' := by
    intro θ θ' hd heq
    apply exp_I_inj_of_abs_sub_lt_pi hd
    have hρne : (ρ:ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
    exact mul_left_cancel₀ hρne heq
  have hSdisc : IsDiscrete S := by
    have hZdisc := isDiscrete_zeroSet_ball hh h0
    rw [isDiscrete_iff_forall_mem_exists_isOpen] at hZdisc ⊢
    intro θ hθ
    rw [hS] at hθ
    have hz : circlePt ρ θ ∈ {z : ℂ | h z = 0} ∩ Metric.ball 0 1 := ⟨hθ, hball θ⟩
    obtain ⟨U, hUopen, hUeq⟩ := hZdisc (circlePt ρ θ) hz
    have hUmem : circlePt ρ θ ∈ U := by
      have : circlePt ρ θ ∈ U ∩ ({z : ℂ | h z = 0} ∩ Metric.ball 0 1) := by
        rw [hUeq]; exact Set.mem_singleton _
      exact this.1
    refine ⟨circlePt ρ ⁻¹' U ∩ Set.Ioo (θ - Real.pi) (θ + Real.pi), ?_, ?_⟩
    · exact (hUopen.preimage hc).inter isOpen_Ioo
    · ext θ'; constructor
      · intro hmem
        rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo, hS] at hmem
        obtain ⟨⟨hUm, hIoo⟩, hzθ'⟩ := hmem
        have hd : |θ' - θ| < Real.pi := by rw [abs_lt]; constructor <;> linarith [hIoo.1, hIoo.2]
        have hmem2 : circlePt ρ θ' ∈ U ∩ ({z : ℂ | h z = 0} ∩ Metric.ball 0 1) :=
          ⟨hUm, hzθ', hball θ'⟩
        rw [hUeq] at hmem2
        simp only [Set.mem_singleton_iff] at hmem2
        exact hinj θ' θ hd hmem2
      · intro hmem
        rw [Set.mem_singleton_iff] at hmem
        subst hmem
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [Set.mem_preimage]; exact hUmem
        · rw [Set.mem_Ioo]; exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        · rw [hS]; exact hz.1
  have hScount : S.Countable := by
    have hbdd : ∀ n : ℕ, (Set.Icc (-(n:ℝ)) (n:ℝ) ∩ S).Finite := fun n =>
      Metric.finite_isBounded_inter_isClosed hSdisc (isBounded_Icc _ _) hSclosed
    have hsub : S ⊆ ⋃ n : ℕ, (Set.Icc (-(n:ℝ)) (n:ℝ) ∩ S) := by
      intro θ hθ
      obtain ⟨n, hn⟩ := exists_nat_gt |θ|
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      refine ⟨?_, hθ⟩
      rw [Set.mem_Icc]
      constructor
      · have h1 : -(n:ℝ) < -|θ| := by rw [neg_lt_neg_iff]; exact hn
        linarith [neg_abs_le θ]
      · exact le_of_lt (lt_of_le_of_lt (le_abs_self θ) hn)
    exact (Set.countable_iUnion fun n => (hbdd n).countable).mono hsub
  exact hScount.measure_zero MeasureTheory.volume

end

end Work.EQ.Fatou
