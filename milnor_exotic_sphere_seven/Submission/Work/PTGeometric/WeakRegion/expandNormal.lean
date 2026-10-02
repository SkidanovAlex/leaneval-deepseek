import Mathlib
import Submission.Work.PTGeometric.WeakRegion.HalfSpaceGraphData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric.WeakRegion

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

/-- **One-sided signed mean-value bound.**  If `φ` is continuous on `[a,b]` (`a ≤ b`),
differentiable on `(a,b)`, and `|deriv φ - c| ≤ ε` there, then the increment of `φ` on `[a,b]`
differs from `c * (b - a)` by at most `ε * (b - a)`.  This is `derivBoundIcc` with the two bounds
`c - ε ≤ deriv φ` and `deriv φ ≤ c + ε`. -/
private lemma sliceExpansionOfLe {φ : ℝ → ℝ} {c ε a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b)) (hdiff : DifferentiableOn ℝ φ (Set.Ioo a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, |deriv φ x - c| ≤ ε) :
    |φ b - φ a - c * (b - a)| ≤ ε * (b - a) := by
  have h := derivBoundIcc (l := c - ε) (u := c + ε) hab hcont hdiff
    (fun x hx => by have := (abs_le.mp (hderiv x hx)).1; linarith)
    (fun x hx => by have := (abs_le.mp (hderiv x hx)).2; linarith)
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- **Uniform first-order expansion in the normal variable.**
For every `ε > 0` there is `η > 0` such that for all `b ∈ [0,δ]` with `|b - s₀| < η`,
`‖F (u,b) - F (u,s₀) - (∂_s F)(b - s₀)‖ ≤ ε |b - s₀|`: the normal derivative `s ↦ Ds (u,s)` is
continuous at `s₀` (continuity of `Ds` on the relative domain along the slice), and the signed
mean-value bound `derivBoundIcc` on the interval between `s₀` and `b` gives the estimate. -/
theorem expandNormal {n : ℕ} [NeZero n] (S : Work.PTGeometric.WeakRegion.HalfSpaceGraphSetup n)
    {ρ δ M : ℝ} (B : S.Box ρ δ M) {u : Work.PTGeometric.WeakRegion.hsTang n}
    (hu : u ∈ Metric.ball (Work.PTGeometric.WeakRegion.hsMk S.p) ρ)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Icc 0 δ) :
    ∀ ε > 0, ∃ η > 0, ∀ b ∈ Set.Icc 0 δ, |b - s₀| < η →
      ‖S.F (u, b) - S.F (u, s₀) - S.Ds (u, s₀) * (b - s₀)‖ ≤ ε * |b - s₀| := by
  intro ε hε
  -- The slice `t ↦ F (u,t)` is continuous on `[0,δ]`.
  have hcont0 : ContinuousOn (fun t : ℝ => S.F (u, t)) (Set.Icc 0 δ) := by
    have h1 : ContinuousOn (fun t : ℝ => (u, t)) (Set.Icc 0 δ) :=
      ((continuous_const (y := u)).prodMk continuous_id).continuousOn
    exact S.contDiffOn_F.continuousOn.comp h1 (fun t ht => B.hmem u hu t ht)
  -- The normal derivative is continuous along the slice at `s₀`.
  have hcontDs : ContinuousWithinAt (fun s : ℝ => S.Ds (u, s)) (Set.Icc 0 δ) s₀ := by
    have h1 : ContinuousWithinAt (fun s : ℝ => (u, s)) (Set.Icc 0 δ) s₀ :=
      ((continuous_const (y := u)).prodMk continuous_id).continuousWithinAt
    exact (S.continuousWithinAt_Ds_at (u, s₀) (B.hmem u hu s₀ hs₀)).comp h1
      (fun s hs => B.hmem u hu s hs)
  rw [Metric.continuousWithinAt_iff] at hcontDs
  obtain ⟨η, hηpos, hη⟩ := hcontDs ε hε
  refine ⟨η, hηpos, fun b hb hbη => ?_⟩
  have hbound : ∀ x ∈ Set.Icc (0:ℝ) δ, |x - s₀| < η → |S.Ds (u, x) - S.Ds (u, s₀)| ≤ ε := by
    intro x hx hxη
    have h1 : dist x s₀ < η := by rwa [Real.dist_eq]
    have h2 := hη hx h1
    rw [Real.dist_eq] at h2
    linarith
  rcases le_total s₀ b with hsb | hbs
  · -- `s₀ ≤ b`: apply the mean-value bound on `[s₀, b]`.
    have h := sliceExpansionOfLe (φ := fun t : ℝ => S.F (u, t)) (c := S.Ds (u, s₀)) hsb
      (hcont0.mono (Set.Icc_subset_Icc hs₀.1 hb.2))
      (fun x hx => by
        have hx' : x ∈ Set.Ioo (0:ℝ) δ :=
          ⟨lt_of_le_of_lt hs₀.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
        exact (S.hasDerivAt_slice B hu hx').differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hx' : x ∈ Set.Ioo (0:ℝ) δ :=
          ⟨lt_of_le_of_lt hs₀.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
        rw [(S.hasDerivAt_slice B hu hx').deriv]
        refine hbound x (Set.Ioo_subset_Icc_self hx') ?_
        rw [abs_of_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x - s₀)]
        linarith [hx.2, hbη, le_abs_self (b - s₀)])
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsb)]
    exact h
  · -- `b ≤ s₀`: the mean-value bound on `[b, s₀]`, with the sign reversed.
    have h := sliceExpansionOfLe (φ := fun t : ℝ => S.F (u, t)) (c := S.Ds (u, s₀)) hbs
      (hcont0.mono (Set.Icc_subset_Icc hb.1 hs₀.2))
      (fun x hx => by
        have hx' : x ∈ Set.Ioo (0:ℝ) δ :=
          ⟨lt_of_le_of_lt hb.1 hx.1, lt_of_lt_of_le hx.2 hs₀.2⟩
        exact (S.hasDerivAt_slice B hu hx').differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hx' : x ∈ Set.Ioo (0:ℝ) δ :=
          ⟨lt_of_le_of_lt hb.1 hx.1, lt_of_lt_of_le hx.2 hs₀.2⟩
        rw [(S.hasDerivAt_slice B hu hx').deriv]
        refine hbound x (Set.Ioo_subset_Icc_self hx') ?_
        rw [abs_of_nonpos (by linarith [hx.2] : x - s₀ ≤ 0)]
        linarith [hx.1, hbη, neg_le_abs (b - s₀)])
    have hX : S.F (u, b) - S.F (u, s₀) - S.Ds (u, s₀) * (b - s₀)
        = -(S.F (u, s₀) - S.F (u, b) - S.Ds (u, s₀) * (s₀ - b)) := by ring
    rw [Real.norm_eq_abs, hX, abs_neg, abs_of_nonpos (sub_nonpos.mpr hbs),
      show -(b - s₀) = s₀ - b by ring]
    exact h

end Work.PTGeometric.WeakRegion
