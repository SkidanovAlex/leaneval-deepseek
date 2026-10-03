import Mathlib

open Function

namespace Work.KMTPlan.A6

/-- A function with compact support vanishes outside a symmetric interval:
there is `R` with `φ z = 0` whenever `R < |z|`. -/
private lemma exists_radius (φ : ℝ → ℂ) (h : HasCompactSupport φ) :
    ∃ R : ℝ, ∀ z : ℝ, R < |z| → φ z = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 h.isCompact.isBounded
  refine ⟨max r 0, fun z hz => ?_⟩
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  have hz' : |z| ≤ r := by
    have := hr hmem
    simpa [Metric.mem_closedBall, Real.dist_eq] using this
  linarith [le_max_left r (0:ℝ)]

/-- If `φ` vanishes off `[-R, R]`, `M ≥ |c + a| + R + 2` and `|q - c| < 1`, then
`φ (q + a + m) = 0` for every integer `m ∉ [-M, M]`. -/
private lemma eq_zero_of_notMem_Icc {φ : ℝ → ℂ} {R : ℝ} (hR : ∀ z : ℝ, R < |z| → φ z = 0)
    {a c : ℝ} {M : ℕ} (hM : |c + a| + R + 2 ≤ (M : ℝ))
    {q : ℝ} (hp : |q - c| < 1) {m : ℤ}
    (hm : m ∉ Finset.Icc (-(M : ℤ)) (M : ℤ)) : φ (q + a + m) = 0 := by
  have hp_lo : -1 < q - c := (abs_lt.mp hp).1
  have hp_hi : q - c < 1 := (abs_lt.mp hp).2
  have hmp : m < -(M : ℤ) ∨ (M : ℤ) < m := by
    rw [Finset.mem_Icc] at hm
    rw [not_and_or] at hm
    rcases hm with h | h
    · exact Or.inl (not_le.mp h)
    · exact Or.inr (not_le.mp h)
  apply hR
  rcases hmp with hm' | hm'
  · have hmR : (m : ℝ) < -(M : ℝ) := by exact_mod_cast hm'
    have : R < -(q + a + (m : ℝ)) := by
      have h1 : -q > -1 - c := by linarith
      have h2 : (c + a) ≤ |c + a| := le_abs_self _
      linarith
    exact lt_of_lt_of_le this (neg_le_abs _)
  · have hmR : (M : ℝ) < (m : ℝ) := by exact_mod_cast hm'
    have : R < q + a + (m : ℝ) := by
      have h1 : c - 1 < q := by linarith
      have h2 : -(c + a) ≤ |c + a| := neg_le_abs _
      linarith
    exact lt_of_lt_of_le this (le_abs_self _)

/-- A doubly indexed sum over `ℤ` with both index sets finitely supported collapses
to the corresponding finite sum. -/
private lemma tsum_tsum_eq_sum {g : ℤ → ℤ → ℂ} {s₁ s₂ : Finset ℤ}
    (h₁ : ∀ m₁ ∉ s₁, ∀ m₂, g m₁ m₂ = 0)
    (h₂ : ∀ m₁ m₂, m₂ ∉ s₂ → g m₁ m₂ = 0) :
    (∑' m₁ : ℤ, ∑' m₂ : ℤ, g m₁ m₂) = ∑ m₁ ∈ s₁, ∑ m₂ ∈ s₂, g m₁ m₂ := by
  have hinner : ∀ m₁, (∑' m₂ : ℤ, g m₁ m₂) = ∑ m₂ ∈ s₂, g m₁ m₂ :=
    fun m₁ => tsum_eq_sum (h₂ m₁)
  rw [show (∑' m₁ : ℤ, ∑' m₂ : ℤ, g m₁ m₂) = ∑' m₁ : ℤ, (∑ m₂ ∈ s₂, g m₁ m₂) from
      tsum_congr hinner]
  exact tsum_eq_sum (fun m₁ hm₁ => Finset.sum_eq_zero (fun m₂ _ => h₁ m₁ hm₁ m₂))

/-- **A locally finite double lattice sum of `C⁴` functions is `C⁴`.**

Let `f : ℝ² → ℂ` be `C⁴`, let `φ ψ : ℝ → ℂ` be `C⁴` with compact support, and let `a b : ℝ`.
Then the function on `ℝ²` given by
`(x,y) ↦ ∑' m₁ : ℤ, ∑' m₂ : ℤ, f (x+a+m₁) (y+b+m₂) * φ (x+a+m₁) * ψ (y+b+m₂)`
is `C⁴`.

Reason it is true: for fixed `(x,y)` the summand vanishes whenever `φ (x+a+m₁) = 0` or
`ψ (y+b+m₂) = 0`, i.e. for all but finitely many `m₁` (the set `{m₁ : |x+a+m₁| < R_φ}` is finite)
and all but finitely many `m₂`; the same finite index sets still work on a whole neighbourhood of
`(x,y)`, so locally the `tsum` is a *finite* sum of `C⁴` functions of `(x,y)`.

Suggested route: `contDiff_iff_contDiffAt`; at a point `x₀ = (x,y)` extract radii
`R_φ, R_ψ ≥ 0` with `φ = 0` off `[-R_φ, R_φ]`, `ψ = 0` off `[-R_ψ, R_ψ]` from the compact
supports (`IsCompact.isBounded`, `Metric.isBounded_iff_subset_closedBall`), choose
`M : ℕ` with `M ≥ |x + a| + R_φ + 2` and `M' : ℕ` with `M' ≥ |y + b| + R_ψ + 2`, and show that for
all `p` with `|p.1 - x| < 1`, `|p.2 - y| < 1` the two `tsum`s collapse via `tsum_eq_sum` to the
finite sum over `Finset.Icc (-(M:ℤ)) M × Finset.Icc (-(M':ℤ)) M'`; conclude with
`Filter.EventuallyEq.contDiffAt_iff` (`ContDiffAt.congr_of_eventuallyEq`) and
`ContDiff.finset_sum`. -/
theorem tsum_int_int_contDiff4 (f : ℝ → ℝ → ℂ) (hf : ContDiff ℝ 4 (fun p : ℝ × ℝ => f p.1 p.2))
    (φ ψ : ℝ → ℂ) (hφ : ContDiff ℝ 4 φ) (hψ : ContDiff ℝ 4 ψ)
    (hφc : HasCompactSupport φ) (hψc : HasCompactSupport ψ) (a b : ℝ) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ => ∑' m₁ : ℤ, ∑' m₂ : ℤ,
      f (p.1 + a + m₁) (p.2 + b + m₂) * φ (p.1 + a + m₁) * ψ (p.2 + b + m₂)) := by
  obtain ⟨Rφ, hRφ⟩ := exists_radius φ hφc
  obtain ⟨Rψ, hRψ⟩ := exists_radius ψ hψc
  rw [contDiff_iff_contDiffAt]
  intro p₀
  obtain ⟨M, hM⟩ := exists_nat_ge (|p₀.1 + a| + Rφ + 2)
  obtain ⟨M', hM'⟩ := exists_nat_ge (|p₀.2 + b| + Rψ + 2)
  -- The finite sum that our function agrees with near `p₀`.
  have hS : ContDiff ℝ 4 (fun p : ℝ × ℝ =>
      ∑ m₁ ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ m₂ ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ),
      f (p.1 + a + m₁) (p.2 + b + m₂) * φ (p.1 + a + m₁) * ψ (p.2 + b + m₂)) := by
    apply ContDiff.sum
    intro m₁ _
    apply ContDiff.sum
    intro m₂ _
    fun_prop
  -- On the neighbourhood `|p.1 - p₀.1| < 1 ∧ |p.2 - p₀.2| < 1` the two `tsum`s collapse.
  have hEv : (fun p : ℝ × ℝ => ∑' m₁ : ℤ, ∑' m₂ : ℤ,
      f (p.1 + a + m₁) (p.2 + b + m₂) * φ (p.1 + a + m₁) * ψ (p.2 + b + m₂))
      =ᶠ[nhds p₀] (fun p : ℝ × ℝ =>
      ∑ m₁ ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ m₂ ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ),
      f (p.1 + a + m₁) (p.2 + b + m₂) * φ (p.1 + a + m₁) * ψ (p.2 + b + m₂)) := by
    have h1 : ∀ᶠ p : ℝ × ℝ in nhds p₀, |p.1 - p₀.1| < 1 := by
      have := (continuous_fst.tendsto p₀).eventually (Metric.ball_mem_nhds p₀.1 zero_lt_one)
      simpa [Metric.mem_ball, Real.dist_eq] using this
    have h2 : ∀ᶠ p : ℝ × ℝ in nhds p₀, |p.2 - p₀.2| < 1 := by
      have := (continuous_snd.tendsto p₀).eventually (Metric.ball_mem_nhds p₀.2 zero_lt_one)
      simpa [Metric.mem_ball, Real.dist_eq] using this
    filter_upwards [h1, h2] with p hp1 hp2
    refine tsum_tsum_eq_sum (s₁ := Finset.Icc (-(M : ℤ)) (M : ℤ))
      (s₂ := Finset.Icc (-(M' : ℤ)) (M' : ℤ)) ?_ ?_
    · intro m₁ hm₁ m₂
      have hz := eq_zero_of_notMem_Icc (M := M) (a := a) (c := p₀.1) hRφ hM (q := p.1) hp1 hm₁
      rw [hz]; simp
    · intro m₁ m₂ hm₂
      have hz := eq_zero_of_notMem_Icc (M := M') (a := b) (c := p₀.2) hRψ hM' (q := p.2) hp2 hm₂
      rw [hz]; simp
  exact hS.contDiffAt.congr_of_eventuallyEq hEv

end Work.KMTPlan.A6
