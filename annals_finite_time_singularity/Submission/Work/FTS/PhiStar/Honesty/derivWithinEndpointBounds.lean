import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- Calculus helper: the one-sided Taylor tail
`t ↦ f t - fb + a₁ * (b - t) - (B / 2) * (b - t) ^ 2` has derivative
`f' - a₁ + B * (b - x)` at `x`. -/
private lemma hasDerivAt_tail_sub (f : ℝ → ℝ) (fb a₁ B b x : ℝ) {f' : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => f t - fb + a₁ * (b - t) - (B / 2) * (b - t) ^ 2)
      (f' - a₁ + B * (b - x)) x := by
  have hb' : HasDerivAt (fun t : ℝ => b - t) (-1) x := (hasDerivAt_id x).const_sub b
  have h1 : HasDerivAt (fun t : ℝ => a₁ * (b - t)) (a₁ * (-1)) x := hb'.const_mul a₁
  have h2 : HasDerivAt (fun t : ℝ => (b - t) ^ 2) (2 * (b - x) ^ (2 - 1) * (-1)) x := hb'.pow 2
  have h3 : HasDerivAt (fun t : ℝ => (B / 2) * (b - t) ^ 2)
      ((B / 2) * (2 * (b - x) ^ (2 - 1) * (-1))) x := h2.const_mul (B / 2)
  convert ((hf.sub (hasDerivAt_const x fb)).add h1).sub h3 using 1
  ring

/-- Calculus helper: the one-sided Taylor tail
`t ↦ f t - fb + a₁ * (b - t) + (B / 2) * (b - t) ^ 2` has derivative
`f' - a₁ - B * (b - x)` at `x`. -/
private lemma hasDerivAt_tail_add (f : ℝ → ℝ) (fb a₁ B b x : ℝ) {f' : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => f t - fb + a₁ * (b - t) + (B / 2) * (b - t) ^ 2)
      (f' - a₁ - B * (b - x)) x := by
  have hb' : HasDerivAt (fun t : ℝ => b - t) (-1) x := (hasDerivAt_id x).const_sub b
  have h1 : HasDerivAt (fun t : ℝ => a₁ * (b - t)) (a₁ * (-1)) x := hb'.const_mul a₁
  have h2 : HasDerivAt (fun t : ℝ => (b - t) ^ 2) (2 * (b - x) ^ (2 - 1) * (-1)) x := hb'.pow 2
  have h3 : HasDerivAt (fun t : ℝ => (B / 2) * (b - t) ^ 2)
      ((B / 2) * (2 * (b - x) ^ (2 - 1) * (-1))) x := h2.const_mul (B / 2)
  convert ((hf.sub (hasDerivAt_const x fb)).add h1).add h3 using 1
  ring

/-- **Endpoint Taylor bounds from a bound on the second `derivWithin`-derivative.**

Let `f : ℝ → ℝ` be `C²` on the closed interval `[a, b]` with `a < b`, and suppose the second
`derivWithin`-derivative `u₂ = derivWithin (derivWithin f (Icc a b)) (Icc a b)` is bounded by
`B` on `Icc a b`.  Then, writing `u₁ = derivWithin f (Icc a b)` and `a₁ = u₁ b`, for every
`θ ∈ (a, b)` one has both a first-order and a second-order Taylor estimate at the right
endpoint `b`:

* `|u₁ θ - a₁| ≤ B * (b - θ)`,
* `|f θ - f b + a₁ * (b - θ)| ≤ B / 2 * (b - θ) ^ 2`.

Route: `u₁` is `ContinuousOn` the interval and differentiable on its interior with
`deriv u₁ = u₂` there, so `Convex.image_sub_le_mul_sub_of_deriv_le` and
`Convex.mul_sub_le_image_sub_of_le_deriv` (Mathlib, `Analysis/Calculus/Deriv/MeanValue.lean`)
give the first bound; applying the same pair of lemmas to
`t ↦ f t - f b + a₁ * (b - t) ∓ (B / 2) * (b - t) ^ 2` (whose derivative is
`u₁ t - a₁ ± B * (b - t)`, sign-definite by the first bound) gives the second. -/
theorem derivWithinEndpointBounds {f : ℝ → ℝ} {a b B : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b))
    (hB : ∀ x ∈ Set.Icc a b,
      |derivWithin (derivWithin f (Set.Icc a b)) (Set.Icc a b) x| ≤ B) :
    (∀ θ ∈ Set.Ioo a b,
      |derivWithin f (Set.Icc a b) θ - derivWithin f (Set.Icc a b) b| ≤ B * (b - θ)) ∧
    (∀ θ ∈ Set.Ioo a b,
      |f θ - f b + derivWithin f (Set.Icc a b) b * (b - θ)| ≤ B / 2 * (b - θ) ^ 2) := by
  have hU : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hder1 : ContDiffOn ℝ 1 (derivWithin f (Set.Icc a b)) (Set.Icc a b) :=
    hf.derivWithin hU (by norm_num)
  have hdiff1 : DifferentiableOn ℝ (derivWithin f (Set.Icc a b)) (Set.Icc a b) :=
    hder1.differentiableOn_one
  have hBnorm : ∀ x ∈ Set.Icc a b,
      ‖derivWithin (derivWithin f (Set.Icc a b)) (Set.Icc a b) x‖ ≤ B := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact hB x hx
  have hBnn : 0 ≤ B := by
    have h1 := hB a (Set.left_mem_Icc.mpr hab.le)
    have h2 := abs_nonneg (derivWithin (derivWithin f (Set.Icc a b)) (Set.Icc a b) a)
    linarith
  -- **First-order estimate**: `u₁ = derivWithin f (Icc a b)` is `C¹` on `[a, b]`, and its
  -- within-derivative on `[a, b]` is bounded by `B`; the 1-dimensional mean value theorem
  -- applied on the convex set `[a, b]` gives the bound.
  have part1 : ∀ θ ∈ Set.Ioo a b,
      |derivWithin f (Set.Icc a b) θ - derivWithin f (Set.Icc a b) b| ≤ B * (b - θ) := by
    intro θ hθ
    have hθI : θ ∈ Set.Icc a b := ⟨hθ.1.le, hθ.2.le⟩
    have hbI : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
    have h := Convex.norm_image_sub_le_of_norm_derivWithin_le (C := B) hdiff1 hBnorm
      (convex_Icc a b) hbI hθI
    have h1 : |θ - b| = b - θ := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hθ.2.le)]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h1] at h
    exact h
  refine ⟨part1, ?_⟩
  intro θ hθ
  have hθb : θ ≤ b := hθ.2.le
  have hsub : Set.Icc θ b ⊆ Set.Icc a b := fun x hx => ⟨hθ.1.le.trans hx.1, hx.2⟩
  have hcontf : ContinuousOn f (Set.Icc θ b) := (hf.mono hsub).continuousOn
  -- on the open interval, `f` is differentiable with `deriv f = derivWithin f (Icc a b)`
  have haux : ∀ x ∈ Set.Ioo a b, HasDerivAt f (derivWithin f (Set.Icc a b) x) x := by
    intro x hxab
    have hmem : Set.Icc a b ∈ nhds x :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxab) Set.Ioo_subset_Icc_self
    have hcd : ContDiffAt ℝ 2 f x := (hf x ⟨hxab.1.le, hxab.2.le⟩).contDiffAt hmem
    have hfdiff : DifferentiableAt ℝ f x := hcd.differentiableAt (by norm_num)
    have hder : deriv f x = derivWithin f (Set.Icc a b) x :=
      (derivWithin_of_mem_nhds hmem).symm
    rw [← hder]
    exact hfdiff.hasDerivAt
  -- the two one-sided Taylor tails at `b` and their derivatives
  set P : ℝ → ℝ := fun t => f t - f b + derivWithin f (Set.Icc a b) b * (b - t)
      - B / 2 * (b - t) ^ 2 with hP
  set Q : ℝ → ℝ := fun t => f t - f b + derivWithin f (Set.Icc a b) b * (b - t)
      + B / 2 * (b - t) ^ 2 with hQ
  have hcontP : ContinuousOn P (Set.Icc θ b) := by
    rw [hP]
    have h1 : ContinuousOn (fun t : ℝ => f t - f b) (Set.Icc θ b) := hcontf.sub continuousOn_const
    have h2 : ContinuousOn (fun t : ℝ => derivWithin f (Set.Icc a b) b * (b - t))
        (Set.Icc θ b) :=
      continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
    have h3 : ContinuousOn (fun t : ℝ => B / 2 * (b - t) ^ 2) (Set.Icc θ b) :=
      continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow 2)
    exact (h1.add h2).sub h3
  have hcontQ : ContinuousOn Q (Set.Icc θ b) := by
    rw [hQ]
    have h1 : ContinuousOn (fun t : ℝ => f t - f b) (Set.Icc θ b) := hcontf.sub continuousOn_const
    have h2 : ContinuousOn (fun t : ℝ => derivWithin f (Set.Icc a b) b * (b - t))
        (Set.Icc θ b) :=
      continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
    have h3 : ContinuousOn (fun t : ℝ => B / 2 * (b - t) ^ 2) (Set.Icc θ b) :=
      continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow 2)
    exact (h1.add h2).add h3
  have hderP : ∀ x ∈ interior (Set.Icc θ b),
      HasDerivWithinAt P
        (derivWithin f (Set.Icc a b) x - derivWithin f (Set.Icc a b) b + B * (b - x))
        (interior (Set.Icc θ b)) x := by
    intro x hx
    rw [interior_Icc] at hx ⊢
    have hxab : x ∈ Set.Ioo a b := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    rw [hP]
    exact (hasDerivAt_tail_sub f (f b) (derivWithin f (Set.Icc a b) b) B b x
      (haux x hxab)).hasDerivWithinAt
  have hnnP : ∀ x ∈ interior (Set.Icc θ b),
      0 ≤ derivWithin f (Set.Icc a b) x - derivWithin f (Set.Icc a b) b + B * (b - x) := by
    intro x hx
    rw [interior_Icc] at hx
    have hxab : x ∈ Set.Ioo a b := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    have h1 := (abs_le.mp (part1 x hxab)).1
    linarith
  have hmonoP : MonotoneOn P (Set.Icc θ b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc θ b) hcontP hderP hnnP
  have hPle : f θ - f b + derivWithin f (Set.Icc a b) b * (b - θ) - B / 2 * (b - θ) ^ 2 ≤ 0 := by
    have hb : P b = 0 := by rw [hP]; simp
    have h := hmonoP (Set.left_mem_Icc.mpr hθb) (Set.right_mem_Icc.mpr hθb) hθb
    rw [hb] at h
    rw [hP] at h
    simpa using h
  have hderQ : ∀ x ∈ interior (Set.Icc θ b),
      HasDerivWithinAt Q
        (derivWithin f (Set.Icc a b) x - derivWithin f (Set.Icc a b) b - B * (b - x))
        (interior (Set.Icc θ b)) x := by
    intro x hx
    rw [interior_Icc] at hx ⊢
    have hxab : x ∈ Set.Ioo a b := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    rw [hQ]
    exact (hasDerivAt_tail_add f (f b) (derivWithin f (Set.Icc a b) b) B b x
      (haux x hxab)).hasDerivWithinAt
  have hnnQ : ∀ x ∈ interior (Set.Icc θ b),
      derivWithin f (Set.Icc a b) x - derivWithin f (Set.Icc a b) b - B * (b - x) ≤ 0 := by
    intro x hx
    rw [interior_Icc] at hx
    have hxab : x ∈ Set.Ioo a b := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    have h1 := (abs_le.mp (part1 x hxab)).2
    linarith
  have hantiQ : AntitoneOn Q (Set.Icc θ b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc θ b) hcontQ hderQ hnnQ
  have hQge : 0 ≤ f θ - f b + derivWithin f (Set.Icc a b) b * (b - θ) + B / 2 * (b - θ) ^ 2 := by
    have hb : Q b = 0 := by rw [hQ]; simp
    have h := hantiQ (Set.left_mem_Icc.mpr hθb) (Set.right_mem_Icc.mpr hθb) hθb
    rw [hb] at h
    rw [hQ] at h
    simpa using h
  have hD : 0 ≤ B / 2 * (b - θ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hle : f θ - f b + derivWithin f (Set.Icc a b) b * (b - θ) ≤ B / 2 * (b - θ) ^ 2 := by
    linarith
  have hge : -(B / 2 * (b - θ) ^ 2) ≤ f θ - f b + derivWithin f (Set.Icc a b) b * (b - θ) := by
    linarith
  exact abs_le.mpr ⟨hge, hle⟩

end Work.FTS.PhiStar.Honesty
