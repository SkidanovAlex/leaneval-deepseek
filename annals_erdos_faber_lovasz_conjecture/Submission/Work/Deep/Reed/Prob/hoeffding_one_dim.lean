import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Reed.Prob.hoeffding_core
import Submission.Work.Deep.Reed.Prob.Expectation
import Submission.Work.Deep.Reed.Prob.pi_prob_inter_eq_mul_of_disjoint

open scoped BigOperators

set_option linter.style.haveILetI false

namespace Work.Deep.Reed.Prob

open Work.Deep.Reed

/-! ## The two-point (chord) convexity bound for `Real.exp`

The only input from convexity theory is that `Real.exp` is convex; the chord bound is the
`ConvexOn` combination lemma applied at two points. -/

private lemma exp_chord (x₁ x₂ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp ((1 - t) * x₁ + t * x₂) ≤ (1 - t) * Real.exp x₁ + t * Real.exp x₂ := by
  have h := convexOn_exp.2 (Set.mem_univ x₁) (Set.mem_univ x₂)
      (show (0 : ℝ) ≤ 1 - t by linarith) (show (0 : ℝ) ≤ t by linarith)
      (show (1 - t) + t = 1 by ring)
  simpa [smul_eq_mul] using h

/-! ## Expectation of `(X * c)`, `(a - Y) / D` and `(Y - a) / D` -/

private lemma exp_mul_right {Ω : Type*} [Fintype Ω] (ν : FinProb Ω) (c : ℝ) (X : Ω → ℝ) :
    ν.exp (fun ω => X ω * c) = ν.exp X * c := by
  rw [show (fun ω => X ω * c) = fun ω => c * X ω from funext fun ω => mul_comm (X ω) c,
    ν.exp_mul_left, mul_comm]

private lemma exp_div_sub {Ω : Type*} [Fintype Ω] (ν : FinProb Ω) (Y : Ω → ℝ) (a D : ℝ) :
    ν.exp (fun ω => (a - Y ω) / D) = (a - ν.exp Y) / D := by
  have hfun : (fun ω => (a - Y ω) / D) = fun ω => (1 / D) * (a - Y ω) := by
    funext ω; ring
  rw [hfun, ν.exp_mul_left]
  have h2 : ν.exp (fun ω => a - Y ω) = a - ν.exp Y := by
    simpa [ν.exp_const] using ν.exp_sub (fun _ => a) Y
  rw [h2]; ring

private lemma exp_sub_div {Ω : Type*} [Fintype Ω] (ν : FinProb Ω) (Y : Ω → ℝ) (a D : ℝ) :
    ν.exp (fun ω => (Y ω - a) / D) = (ν.exp Y - a) / D := by
  have hfun : (fun ω => (Y ω - a) / D) = fun ω => (1 / D) * (Y ω - a) := by
    funext ω; ring
  rw [hfun, ν.exp_mul_left]
  have h2 : ν.exp (fun ω => Y ω - a) = ν.exp Y - a := by
    simpa [ν.exp_const] using ν.exp_sub Y (fun _ => a)
  rw [h2]; ring

/-- **Chord bound, after centring.**  If `Y` takes values in `[a, a + D]` with `D > 0`, then

`E[e^{λ (Y - E Y)}] ≤ ((a + D - E Y)/D) e^{λ (a - E Y)} + ((E Y - a)/D) e^{λ (a + D - E Y)}`.

This is the pointwise convexity (chord) bound for `Real.exp` integrated against `ν`. -/
private lemma exp_chord_centered {Ω : Type*} [Fintype Ω] (ν : FinProb Ω) (Y : Ω → ℝ)
    {a D : ℝ} (hD : 0 < D) (hlo : ∀ ω, a ≤ Y ω) (hhi : ∀ ω, Y ω ≤ a + D) (lam : ℝ) :
    ν.exp (fun ω => Real.exp (lam * (Y ω - ν.exp Y)))
      ≤ ((a + D - ν.exp Y) / D) * Real.exp (lam * (a - ν.exp Y))
        + ((ν.exp Y - a) / D) * Real.exp (lam * (a + D - ν.exp Y)) := by
  have hpt : ∀ ω, Real.exp (lam * (Y ω - ν.exp Y))
      ≤ ((a + D - Y ω) / D) * Real.exp (lam * (a - ν.exp Y))
        + ((Y ω - a) / D) * Real.exp (lam * (a + D - ν.exp Y)) := by
    intro ω
    have ht0 : 0 ≤ (Y ω - a) / D := div_nonneg (by linarith [hlo ω]) hD.le
    have ht1 : (Y ω - a) / D ≤ 1 := by rw [div_le_one hD]; linarith [hhi ω]
    have h := exp_chord (lam * (a - ν.exp Y)) (lam * (a + D - ν.exp Y)) ((Y ω - a) / D) ht0 ht1
    have hcomb : (1 - (Y ω - a) / D) * (lam * (a - ν.exp Y))
        + ((Y ω - a) / D) * (lam * (a + D - ν.exp Y)) = lam * (Y ω - ν.exp Y) := by
      field_simp
      ring
    rw [hcomb] at h
    have hone : (1 - (Y ω - a) / D) = (a + D - Y ω) / D := by field_simp; ring
    rw [← hone]
    exact h
  calc ν.exp (fun ω => Real.exp (lam * (Y ω - ν.exp Y)))
      ≤ ν.exp (fun ω => ((a + D - Y ω) / D) * Real.exp (lam * (a - ν.exp Y))
          + ((Y ω - a) / D) * Real.exp (lam * (a + D - ν.exp Y))) := ν.exp_mono hpt
    _ = ((a + D - ν.exp Y) / D) * Real.exp (lam * (a - ν.exp Y))
        + ((ν.exp Y - a) / D) * Real.exp (lam * (a + D - ν.exp Y)) := by
        rw [ν.exp_add,
          exp_mul_right ν (Real.exp (lam * (a - ν.exp Y))) (fun ω => (a + D - Y ω) / D),
          exp_mul_right ν (Real.exp (lam * (a + D - ν.exp Y))) (fun ω => (Y ω - a) / D),
          exp_div_sub ν Y (a + D) D, exp_sub_div ν Y a D]

/-- **The numeric end game of Hoeffding's lemma.**  If `a ≤ μ ≤ a + D` and `D > 0`, then the
explicit two-point exponential moment with weights `(a + D - μ)/D`, `(μ - a)/D` is at most
`exp (λ² D² / 8)`.  This is `hoeffding_core` after substituting `θ = (μ - a)/D` and `u = λ D`. -/
private lemma hoeffding_endpoint {a μ D lam : ℝ} (hD : 0 < D) (haμ : a ≤ μ)
    (hμb : μ ≤ a + D) :
    ((a + D - μ) / D) * Real.exp (lam * (a - μ)) + ((μ - a) / D) * Real.exp (lam * (a + D - μ))
      ≤ Real.exp (lam ^ 2 * D ^ 2 / 8) := by
  have hDne : D ≠ 0 := ne_of_gt hD
  set θ : ℝ := (μ - a) / D with hθ
  set u : ℝ := lam * D with hu
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg (by linarith) hD.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hD]; linarith
  have hθD : θ * D = μ - a := by rw [hθ, div_mul_cancel₀ _ hDne]
  have key1 : θ * (lam * D) = lam * (μ - a) := by
    calc θ * (lam * D) = (θ * D) * lam := by ring
      _ = (μ - a) * lam := by rw [hθD]
      _ = lam * (μ - a) := by ring
  have key2 : (1 - θ) * (lam * D) = lam * (a + D - μ) := by
    have h1 : (1 - θ) * D = a + D - μ := by rw [sub_mul, one_mul, hθD]; ring
    calc (1 - θ) * (lam * D) = ((1 - θ) * D) * lam := by ring
      _ = (a + D - μ) * lam := by rw [h1]
      _ = lam * (a + D - μ) := by ring
  have hE1 : Real.exp (lam * (a - μ)) = Real.exp (-(θ * u)) := by
    congr 1
    rw [hu, key1]; ring
  have hE2 : Real.exp (lam * (a + D - μ)) = Real.exp ((1 - θ) * u) := by
    congr 1
    rw [hu, key2]
  have h3 : (a + D - μ) / D = 1 - θ := by rw [hθ]; field_simp; ring
  have h4 : (μ - a) / D = θ := by rw [hθ]
  calc ((a + D - μ) / D) * Real.exp (lam * (a - μ))
        + ((μ - a) / D) * Real.exp (lam * (a + D - μ))
      = (1 - θ) * Real.exp (-(θ * u)) + θ * Real.exp ((1 - θ) * u) := by
        rw [hE1, hE2, h3, h4]
    _ ≤ Real.exp (u ^ 2 / 8) := hoeffding_core (p := θ) (u := u) hθ0 hθ1
    _ = Real.exp (lam ^ 2 * D ^ 2 / 8) := by rw [hu]; congr 1; ring

/-- **Hoeffding's bound, oscillation form.**  If a real-valued `Y` on a finite probability
space takes values in an interval of length at most `D`, then
`E[e^{λ (Y - E Y)}] ≤ e^{λ² D² / 8}`.

Proof.  If `D = 0` then `Y` is constant and both sides are `1`.  Otherwise choose `ω₀`
minimising `Y`, put `a := Y ω₀` (so `a ≤ Y ω ≤ a + D` for every `ω`) and let `μ := ν.exp Y`,
so `a ≤ μ ≤ a + D`.  The chord bound for the convex function `Real.exp` gives, for every `ω`,

`exp (λ * (Y ω - μ)) ≤ ((a + D - Y ω)/D) * exp (λ*(a - μ)) + ((Y ω - a)/D) * exp (λ*(a + D - μ))`

(`(Y ω - a)/D ∈ [0,1]` because `a ≤ Y ω ≤ a + D`).  Taking `ν.exp` of both sides and using
linearity, `ν.exp (fun ω => (a + D - Y ω)/D) = (a + D - μ)/D` and
`ν.exp (fun ω => (Y ω - a)/D) = (μ - a)/D`, so the two weights are exactly `1 - θ` and `θ` for
`θ := (μ - a)/D ∈ [0,1]`; this is the numeric end game `hoeffding_endpoint`, which is
`hoeffding_core` in disguise. -/
theorem hoeffding_one_dim {Ω : Type*} [Fintype Ω] (ν : Work.Deep.Reed.FinProb Ω) (Y : Ω → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hosc : ∀ z z' : Ω, |Y z - Y z'| ≤ D) (lam : ℝ) :
    ν.exp (fun ω => Real.exp (lam * (Y ω - ν.exp Y))) ≤ Real.exp (lam ^ 2 * D ^ 2 / 8) := by
  rcases eq_or_lt_of_le hD with hD0 | hDpos
  · -- `D = 0`: the variable is constant and both sides equal `1`.
    subst hD0
    haveI : Nonempty Ω := ν.nonempty_of_finprob
    obtain ⟨ω₀⟩ := ‹Nonempty Ω›
    have hconst : ∀ ω, Y ω = Y ω₀ := by
      intro ω
      have h := hosc ω ω₀
      rw [abs_le] at h
      linarith [h.1, h.2]
    have hμ : ν.exp Y = Y ω₀ := by
      rw [show Y = (fun _ => Y ω₀) from funext hconst, ν.exp_const]
    have hL : (fun ω => Real.exp (lam * (Y ω - ν.exp Y))) = fun _ => (1 : ℝ) := by
      funext ω
      rw [hconst ω, hμ]
      simp
    rw [hL, ν.exp_const]
    simp
  · -- `D > 0`: bound the variable in `[a, a + D]` by a minimiser and apply the chord bound.
    haveI : Nonempty Ω := ν.nonempty_of_finprob
    obtain ⟨ω₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset Ω) Y Finset.univ_nonempty
    have hlo : ∀ ω, Y ω₀ ≤ Y ω := fun ω => hmin ω (Finset.mem_univ ω)
    have hhi : ∀ ω, Y ω ≤ Y ω₀ + D := by
      intro ω
      have h := hosc ω ω₀
      rw [abs_le] at h
      linarith [h.2]
    have hμlo : Y ω₀ ≤ ν.exp Y := by
      have h := ν.exp_mono (X := fun _ => Y ω₀) (Y := Y) hlo
      simpa [ν.exp_const] using h
    have hμhi : ν.exp Y ≤ Y ω₀ + D := by
      have h := ν.exp_mono (X := Y) (Y := fun _ => Y ω₀ + D) hhi
      simpa [ν.exp_const] using h
    exact (exp_chord_centered ν Y hDpos hlo hhi lam).trans
      (hoeffding_endpoint (a := Y ω₀) (μ := ν.exp Y) (D := D) (lam := lam) hDpos hμlo hμhi)

end Work.Deep.Reed.Prob
