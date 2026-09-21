import Mathlib
import Submission.Work.Geometry.Ulam.odd_radial_reconstruction

namespace Commons.Geometry.Ulam

open Set
open scoped ContDiff Topology

noncomputable section

/-- The radial Volterra system for the odd-dimensional construction:
`R^(2n+2)+r^(2n+2) = 2 + A` and `R^(2n+1)-r^(2n+1) = B` on `[0,π/2]`. -/
def radialSystem (n : ℕ) (R r A B : ℝ → ℝ) : Prop :=
  ∀ α ∈ Set.Icc 0 (Real.pi / 2),
    R α ^ (2 * n + 2) + r α ^ (2 * n + 2) = 2 + A α ∧
    R α ^ (2 * n + 1) - r α ^ (2 * n + 1) = B α

/-- The profile `f` has `R` and `r` as its radial functions: the positive
boundary is traced by `α ↦ (R α cos α, R α sin α)` and the negative one by
`α ↦ (-(r α cos α), r α sin α)`.  The support condition encodes that the
profile is zero outside the interval `[-r(0),R(0)]`. -/
def IsRadialProfile (R r f : ℝ → ℝ) : Prop :=
  Function.support f ⊆ Set.Icc (-(r 0)) (R 0) ∧
  (∀ α ∈ Set.Icc 0 (Real.pi / 2), f (R α * Real.cos α) = R α * Real.sin α) ∧
  (∀ α ∈ Set.Icc 0 (Real.pi / 2), f (-(r α * Real.cos α)) = r α * Real.sin α)

lemma IsRadialProfile.support_subset {R r f : ℝ → ℝ} (hf : IsRadialProfile R r f) :
    Function.support f ⊆ Set.Icc (-(r 0)) (R 0) :=
  hf.1

/-- The endpoint values of the profile are zero when the radial functions are
positive and the boundary point reaches the axis at `α = π/2`. -/
lemma IsRadialProfile.endpoint_left {R r f : ℝ → ℝ} (hf : IsRadialProfile R r f) :
    f (-(r 0)) = 0 := by
  have h := hf.2.2 0 (by constructor <;> positivity)
  simpa using h

lemma IsRadialProfile.endpoint_right {R r f : ℝ → ℝ} (hf : IsRadialProfile R r f) :
    f (R 0) = 0 := by
  have h := hf.2.1 0 (by constructor <;> positivity)
  simpa using h

/-- The full radial data needed for the odd-dimensional construction: the
radial functions solve the Volterra system, the profile is their radial graph,
and the auxiliary functions `h,x,y` satisfy the root and moment equations. -/
structure OddRadialProfileData (n : ℕ) where
  Rfun : ℝ → ℝ
  rfun : ℝ → ℝ
  ff : ℝ → ℝ
  hfun : ℝ → ℝ
  xfun : ℝ → ℝ
  yfun : ℝ → ℝ
  A : ℝ → ℝ
  B : ℝ → ℝ
  system : radialSystem n Rfun rfun A B
  graph : IsRadialProfile Rfun rfun ff
  /-- The joint slope condition at the seam `t=0`, needed for concavity of the
  glued profile.  It is the order relation between the one-sided slopes of the
  right and left arcs at `α = π/2`. -/
  joint_slope :
    deriv rfun (Real.pi / 2) / rfun (Real.pi / 2) +
      deriv Rfun (Real.pi / 2) / Rfun (Real.pi / 2) ≥ 0
  x_pos : ∀ s : ℝ, 0 < s → 0 < xfun s
  y_pos : ∀ s : ℝ, 0 < s → 0 < yfun s
  root_left : ∀ s : ℝ, 0 < s → ff (- xfun s) = - (s * (- xfun s) + hfun s)
  root_right : ∀ s : ℝ, 0 < s → ff (yfun s) = s * yfun s + hfun s
  moment_first : ∀ s : ℝ, 0 < s →
    (∫ t in (- xfun s)..(yfun s),
      (ff t ^ 2 - (s * t + hfun s) ^ 2) ^ n *
        Real.sqrt (ff t ^ 2 - (s * t + hfun s) ^ 2)) =
        (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
          ((1 - t ^ 2) - (s * t) ^ 2) ^ n *
            Real.sqrt ((1 - t ^ 2) - (s * t) ^ 2))
  moment_second : ∀ s : ℝ, 0 < s →
    (∫ t in (- xfun s)..(yfun s),
      (ff t ^ 2 - (s * t + hfun s) ^ 2) ^ (n - 1) *
        Real.sqrt (ff t ^ 2 - (s * t + hfun s) ^ 2) *
          (t + deriv hfun s)) = 0
  non_even : ¬ ∀ t : ℝ, ff (-t) = ff t

/-- **Bridge statement handed to the fleet.**  Small smooth perturbations
`A,B` of the ball data produce a full odd radial profile datum with support
`[-r(0),R(0)]`.  The existence of `R,r` is the first radial lemma
`spherical_radon_radial_reconstruction`; the remaining content is the
construction of `f` from the radial graph and the verification of the two
moment equations. -/
theorem exists_oddRadialProfileData_of_small_perturbation (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε > 0, ∀ A B : ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) A (Set.Icc 0 (Real.pi / 2)) →
      ContDiffOn ℝ (⊤ : ℕ∞) B (Set.Icc 0 (Real.pi / 2)) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |A α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |B α| < ε) →
      A (Real.pi / 2) = 0 →
      B (Real.pi / 2) = 0 →
      deriv A 0 = 0 →
      deriv B 0 = 0 →
      ∃ P : OddRadialProfileData n, P.A = A ∧ P.B = B := by
  sorry

end

end Commons.Geometry.Ulam
