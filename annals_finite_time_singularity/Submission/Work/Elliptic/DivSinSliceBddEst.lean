/-
Copyright: work module for the Elgindi finite-time singularity project.

# `SliceBdd` for a smooth angular slice vanishing at the endpoints

`Work.Elliptic.DivSinSliceBddEst` is the endpoint-bound input to the angular calculus behind
`DivisionBySin` (Elgindi, Annals 194 (2021), Prop. `DivisionBySin`): every `h : ℝ → ℝ` that is
smooth on an open neighbourhood of `[0, π/2]` and satisfies `h 0 = h (π/2) = 0` enjoys the ten
bounds recorded in `Work.Elliptic.SliceBdd`.

The proof assembles quantitative endpoint estimates.

* Near `0` (on `Ioo 0 (π/4)`): the bounds `|h θ| ≤ C θ`, `|h' θ - h'(0)| ≤ C θ` and
  `|h'' θ| ≤ C` are the mean-value estimates of `Work.Elliptic.htUEndpointBoundsZero` (the
  mirror at `0` of the proved `htU_endpoint_bounds`), while `|(h/sin 2θ)' θ| ≤ C` is
  `Work.Elliptic.sinq_deriv_bound_zero` below: with `G(θ) = h'(θ) sin 2θ - 2 cos 2θ · h(θ)` one
  has `G(0) = 0`, `G' = sin 2θ · (h'' + 4h)` and `sin²(2θ) · (h/sin 2θ)' = G`; the barrier
  functions `±G - K sin²` (where `K` bounds `|h'' + 4h|` on the compact `[0, π/2]`) are
  nonincreasing, whence `|G| ≤ K sin²θ` and `|(h/sin 2θ)'| ≤ K/(4 cos²θ) ≤ K/2`.
  The quotient bound `|h θ / sin 2θ| ≤ C` follows from `sin x ≥ (2/π) x` and
  `|h θ| ≤ C min θ (π/2 - θ)` (`Work.Elliptic.contDiffOn_one_bounds`).
* Near `π/2` (on `Ioo (π/4) (π/2)`): the first three bounds are the proved
  `Work.Elliptic.htU_endpoint_bounds`, the quotient bound is again
  `sin(2θ) = sin(2(π/2 - θ)) ≥ (4/π)(π/2 - θ)`, and the bound on `(h/sin 2θ)'` is obtained from
  `Work.Elliptic.htU_near_pi2` near `π/2` together with continuity at the interior point `π/4`
  (`Work.Elliptic.exists_bound_of_continuousOn_Ioo`).

The single constant of `SliceBdd` is the sum of the finitely many constants produced above.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.DivSinBddDefs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.htU_interior_facts
import Submission.Work.Elliptic.htU_near_pi2
import Submission.Work.Elliptic.exists_bound_of_continuousOn_Ioo
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Elliptic.htUEndpointBoundsZero
import Submission.Work.Elliptic.sin_sq_ge_half

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- Barrier principle on a right-hand interval: a function continuous on `[0,x]` whose
derivative is nonpositive on `(0,x)` satisfies `φ x ≤ φ 0`. -/
private theorem le_of_deriv_nonpos_on_Icc {φ : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hcont : ContinuousOn φ (Set.Icc 0 x))
    (hdiff : DifferentiableOn ℝ φ (Set.Ioo 0 x))
    (hderiv : ∀ y ∈ Set.Ioo 0 x, deriv φ y ≤ 0) : φ x ≤ φ 0 := by
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) x) hcont
    (by rw [interior_Icc]; exact hdiff)
    (by rw [interior_Icc]; intro y hy; exact hderiv y hy)
  exact hanti ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx

/-- If `g` vanishes at `0`, is continuous on `[0,x]`, has derivative `sin (2y) * q y` on
`(0,x)` with `|q y| ≤ K`, and `x ≤ π/4`, then `|g x| ≤ K * sin x ^ 2`.  This is the barrier
argument applied twice, to `g - K sin²` and to `-g - K sin²`. -/
private theorem two_sided_barrier {g q : ℝ → ℝ} {K x : ℝ} (hx : 0 ≤ x)
    (hx4 : x ≤ Real.pi / 4) (hg0 : g 0 = 0) (hgcont : ContinuousOn g (Set.Icc 0 x))
    (hgderiv : ∀ y ∈ Set.Ioo 0 x, HasDerivAt g (Real.sin (2 * y) * q y) y)
    (hq : ∀ y ∈ Set.Ioo 0 x, |q y| ≤ K) :
    |g x| ≤ K * Real.sin x ^ 2 := by
  have hsin2c : ContinuousOn (fun y : ℝ => K * Real.sin y ^ 2) (Set.Icc 0 x) :=
    (by fun_prop : ContinuousOn (fun y : ℝ => Real.sin y ^ 2) (Set.Icc 0 x)).const_mul K
  have hsin2d : DifferentiableOn ℝ (fun y : ℝ => K * Real.sin y ^ 2) (Set.Ioo 0 x) := by
    intro y hy
    exact (((Real.hasDerivAt_sin y).pow 2).const_mul K).differentiableAt.differentiableWithinAt
  have key : ∀ (ε : ℝ), ε * ε = 1 → ε * g x ≤ K * Real.sin x ^ 2 := by
    intro ε hε
    have hcont : ContinuousOn (fun y => ε * g y - K * Real.sin y ^ 2) (Set.Icc 0 x) :=
      (hgcont.const_mul ε).sub hsin2c
    have hdiff : DifferentiableOn ℝ (fun y => ε * g y - K * Real.sin y ^ 2) (Set.Ioo 0 x) := by
      intro y hy
      exact ((((hgderiv y hy).const_mul ε).sub
        (((Real.hasDerivAt_sin y).pow 2).const_mul K)).differentiableAt).differentiableWithinAt
    have hderiv : ∀ y ∈ Set.Ioo 0 x, deriv (fun y => ε * g y - K * Real.sin y ^ 2) y ≤ 0 := by
      intro y hy
      have hyl : y < Real.pi / 2 := by linarith [hy.2, hx4, Real.pi_pos]
      have hd : HasDerivAt (fun z => ε * g z - K * Real.sin z ^ 2)
          (ε * (Real.sin (2 * y) * q y) - K * (2 * Real.sin y ^ (2 - 1) * Real.cos y)) y :=
        ((hgderiv y hy).const_mul ε).sub (((Real.hasDerivAt_sin y).pow 2).const_mul K)
      rw [hd.deriv, Real.sin_two_mul, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      have hqy : q y ≤ K := (abs_le.mp (hq y hy)).2
      have hqy' : -K ≤ q y := (abs_le.mp (hq y hy)).1
      have hsiny : 0 ≤ Real.sin y :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hy.1], by linarith [hyl]⟩
      have hcosy : 0 ≤ Real.cos y :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hy.1], by linarith [hyl]⟩
      have hεq : ε * q y ≤ K := by
        have hε' : ε = 1 ∨ ε = -1 := sq_eq_one_iff.mp (by rw [sq]; exact hε)
        rcases hε' with h | h <;> rw [h] <;> linarith
      have hrw : ε * (2 * Real.sin y * Real.cos y * q y) - K * (2 * Real.sin y * Real.cos y)
          = (2 * Real.sin y * Real.cos y) * (ε * q y - K) := by ring
      rw [hrw]
      have hnn : 0 ≤ 2 * Real.sin y * Real.cos y :=
        mul_nonneg (mul_nonneg (by norm_num) hsiny) hcosy
      exact mul_nonpos_of_nonneg_of_nonpos hnn (by linarith [hεq])
    have h1 := le_of_deriv_nonpos_on_Icc (φ := fun y => ε * g y - K * Real.sin y ^ 2) hx
      hcont hdiff hderiv
    have h2 : ε * g x - K * Real.sin x ^ 2 ≤ 0 := by
      have h0v : ε * g 0 - K * Real.sin 0 ^ 2 = 0 := by rw [hg0, Real.sin_zero]; ring
      linarith [h1, h0v]
    linarith [h2]
  have hpos := key 1 (by norm_num)
  have hneg := key (-1) (by norm_num)
  rw [abs_le]
  constructor <;> linarith [hpos, hneg]

private theorem sinq_deriv_bound_zero (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h)
    (h0 : h 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 4), |deriv (Work.Elliptic.SinQ h) θ| ≤ C := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hUniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (Real.pi / 2)) := uniqueDiffOn_Icc hpi2
  have hf2 : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)) :=
    (hh.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)).of_le le_top
  obtain ⟨hCU, hcomp1, hcomp2, hid1, hid2, hcu, hcu1, hcu2, hcf2⟩ := htU_interior_facts h hf2
  -- a bound `K` for `|h'' + 4h|` on `[0, π/2]`
  have hcontK : ContinuousOn
      (fun s => iteratedDerivWithin 2 h (Set.Icc 0 (Real.pi / 2)) s + 4 * h s)
      (Set.Icc 0 (Real.pi / 2)) :=
    (hf2.continuousOn_iteratedDerivWithin (m := 2) (n := 2) (by norm_num) hUniq).add
      (continuous_const.continuousOn.mul hf2.continuousOn)
  obtain ⟨K₀, hK₀⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcontK
  set K : ℝ := max K₀ 0 with hKdef
  have hKnn : 0 ≤ K := le_max_right _ _
  have hKbd : ∀ s ∈ Set.Icc 0 (Real.pi / 2),
      |iteratedDerivWithin 2 h (Set.Icc 0 (Real.pi / 2)) s + 4 * h s| ≤ K := by
    intro s hs
    have h1 := hK₀ s hs
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  refine ⟨K / 2, by linarith, fun θ hθ => ?_⟩
  have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hGbound : |iteratedDerivWithin 1 h (Set.Icc 0 (Real.pi / 2)) θ * Real.sin (2 * θ)
      - 2 * Real.cos (2 * θ) * h θ| ≤ K * Real.sin θ ^ 2 := by
    have hGcont : ContinuousOn (fun y => iteratedDerivWithin 1 h (Set.Icc 0 (Real.pi / 2)) y
        * Real.sin (2 * y) - 2 * Real.cos (2 * y) * h y) (Set.Icc 0 θ) := by
      have h1 : ContinuousOn (iteratedDerivWithin 1 h (Set.Icc 0 (Real.pi / 2)))
          (Set.Icc 0 (Real.pi / 2)) :=
        hf2.continuousOn_iteratedDerivWithin (m := 1) (n := 2) (by norm_num) hUniq
      have hsub : Set.Icc (0 : ℝ) θ ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        Set.Icc_subset_Icc le_rfl (by linarith [hθ.2, Real.pi_pos])
      have h2 : ContinuousOn (fun y : ℝ => Real.sin (2 * y)) (Set.Icc 0 θ) := by fun_prop
      have h3 : ContinuousOn (fun y : ℝ => 2 * Real.cos (2 * y)) (Set.Icc 0 θ) := by fun_prop
      exact ((h1.mono hsub).mul h2).sub (h3.mul (hf2.continuousOn.mono hsub))
    have hGderiv : ∀ y ∈ Set.Ioo 0 θ,
        HasDerivAt (fun y => iteratedDerivWithin 1 h (Set.Icc 0 (Real.pi / 2)) y
          * Real.sin (2 * y) - 2 * Real.cos (2 * y) * h y)
          (Real.sin (2 * y) * (iteratedDerivWithin 2 h (Set.Icc 0 (Real.pi / 2)) y + 4 * h y)) y :=
      fun y hy => hasDerivAt_htAux h hf2 y ⟨hy.1, by linarith [hy.2, hθ.2, Real.pi_pos]⟩
    have hq : ∀ y ∈ Set.Ioo 0 θ,
        |iteratedDerivWithin 2 h (Set.Icc 0 (Real.pi / 2)) y + 4 * h y| ≤ K := by
      intro y hy
      exact hKbd y ⟨hy.1.le, (lt_trans hy.2 hθIoo.2).le⟩
    have := two_sided_barrier (g := fun y => iteratedDerivWithin 1 h (Set.Icc 0 (Real.pi / 2)) y
        * Real.sin (2 * y) - 2 * Real.cos (2 * y) * h y)
      (q := fun y => iteratedDerivWithin 2 h (Set.Icc 0 (Real.pi / 2)) y + 4 * h y)
      (le_of_lt hθ.1) (le_of_lt hθ.2) (by simp [h0]) hGcont hGderiv hq
    simpa using this
  -- the relation `sin²(2θ) · u' = G`
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsin2pos : 0 < (Real.sin (2 * θ)) ^ 2 := pow_pos hsinpos 2
  have hrel : deriv (SinQ h) θ * (Real.sin (2 * θ)) ^ 2
      = iteratedDerivWithin 1 h (Set.Icc 0 (Real.pi / 2)) θ * Real.sin (2 * θ)
        - 2 * Real.cos (2 * θ) * h θ := by
    have h1 := hid1 θ hθIoo
    rw [hcomp1 θ hθIoo] at h1
    rw [mul_comm] at h1
    exact h1
  have hu : deriv (SinQ h) θ
      = (iteratedDerivWithin 1 h (Set.Icc 0 (Real.pi / 2)) θ * Real.sin (2 * θ)
        - 2 * Real.cos (2 * θ) * h θ) / (Real.sin (2 * θ)) ^ 2 := by
    rw [eq_div_iff (ne_of_gt hsin2pos)]
    exact hrel
  -- the ratio `sin²θ / sin²(2θ) ≤ 1/2` on `(0, π/4)`
  have hratio : Real.sin θ ^ 2 / (Real.sin (2 * θ)) ^ 2 ≤ 1 / 2 := by
    have hsinnz : Real.sin θ ≠ 0 := ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
    have hcosnz : Real.cos θ ≠ 0 := ne_of_gt
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
    have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
      have h1 := sin_sq_ge_half (x := Real.pi / 2 - θ) (by linarith [hθ.2])
        (by linarith [hθ.1, Real.pi_pos])
      rwa [Real.sin_pi_div_two_sub] at h1
    have hsin2 : 0 < Real.sin θ ^ 2 := sq_pos_of_ne_zero hsinnz
    have hcos2pos : 0 < Real.cos θ ^ 2 := sq_pos_of_ne_zero hcosnz
    rw [Real.sin_two_mul]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hcos2, hsin2, sq_nonneg (Real.cos θ)]
  rw [hu, abs_div, abs_of_pos hsin2pos]
  have hstep1 : |iteratedDerivWithin 1 h (Set.Icc 0 (Real.pi / 2)) θ * Real.sin (2 * θ)
      - 2 * Real.cos (2 * θ) * h θ| / (Real.sin (2 * θ)) ^ 2
      ≤ (K * Real.sin θ ^ 2) / (Real.sin (2 * θ)) ^ 2 :=
    div_le_div_of_nonneg_right hGbound (le_of_lt hsin2pos)
  calc |iteratedDerivWithin 1 h (Set.Icc 0 (Real.pi / 2)) θ * Real.sin (2 * θ)
        - 2 * Real.cos (2 * θ) * h θ| / (Real.sin (2 * θ)) ^ 2
      ≤ (K * Real.sin θ ^ 2) / (Real.sin (2 * θ)) ^ 2 := hstep1
    _ = K * (Real.sin θ ^ 2 / (Real.sin (2 * θ)) ^ 2) := by ring
    _ ≤ K * (1 / 2) := mul_le_mul_of_nonneg_left hratio hKnn
    _ = K / 2 := by ring

/-- Local boundedness at a point: a function continuous at `c` is bounded on a two-sided
neighbourhood of `c`. -/
private theorem exists_bound_near_of_continuousAt {g : ℝ → ℝ} {c : ℝ} (hg : ContinuousAt g c) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Ioo (c - δ) (c + δ), |g x| ≤ C := by
  rcases Metric.continuousAt_iff.mp hg 1 (by norm_num) with ⟨δ, hδ, hδb⟩
  refine ⟨|g c| + 1, δ, hδ, fun x hx => ?_⟩
  have hxc : dist x c < δ := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := hδb hxc
  rw [Real.dist_eq, abs_lt] at h
  rw [abs_le]
  exact ⟨by linarith [h.1, neg_abs_le (g c)], by linarith [h.2, le_abs_self (g c)]⟩

/-- **Endpoint bounds for a smooth slice vanishing at both endpoints.** -/
theorem DivSinSliceBddEst (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) (h0 : h 0 = 0)
    (hπ : h (Real.pi / 2) = 0) : Work.Elliptic.SliceBdd h := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : (Real.pi / 4 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hf2 : ContDiffOn ℝ 2 h (Set.Icc 0 (Real.pi / 2)) :=
    (hh.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)).of_le le_top
  have hf1 : ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi / 2)) := hf2.of_le (by norm_num)
  obtain ⟨hCU, hcomp1, hcomp2, hid1, hid2, hcu, hcu1, hcu2, hcf2⟩ :=
    Work.Elliptic.htU_interior_facts h hf2
  -- near 0: (1),(2),(3)
  obtain ⟨Cz, hCz0, hz1, hz2, hz3⟩ := htUEndpointBoundsZero h hf2 h0 hcomp1 hcomp2
  -- near π/2: (6),(7),(8)
  obtain ⟨Cp, hCp0, hp1, hp2, hp3⟩ := Work.Elliptic.htU_endpoint_bounds h hf2 hπ hcomp1 hcomp2
  -- |h θ| ≤ Co * min θ (π/2-θ)
  obtain ⟨Co, hCo0, ho1, ho2⟩ := Work.Elliptic.contDiffOn_one_bounds hf1 h0 hπ
  -- (5)
  obtain ⟨Cu, hCu0, hu5⟩ := sinq_deriv_bound_zero h hh h0
  -- near-π/2 bounds for SinQ and its derivative
  obtain ⟨Cq, δq, hCq0, hδq, hq1, hq2, hq3, hq4, hq5, hq6⟩ :=
    Work.Elliptic.htU_near_pi2 h hf2 hπ hcomp1 hcomp2 hid1 hid2
  have hCo4nn : 0 ≤ Co * Real.pi / 4 := by positivity
  have h4pi : 0 < (4 : ℝ) / Real.pi := div_pos (by norm_num) Real.pi_pos
  -- (4)
  have hsin4 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 4), |SinQ h θ| ≤ Co * Real.pi / 4 := by
    intro θ hθ
    have hhbd : |h θ| ≤ Co * θ := by
      have hh' := ho1 θ ⟨le_of_lt hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
      rwa [min_eq_left (by linarith [Real.pi_pos, hθ.2])] at hh'
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hlow : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
      have hh' := Real.mul_le_sin (x := 2 * θ) (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
      rwa [show (2 : ℝ) / Real.pi * (2 * θ) = (4 : ℝ) / Real.pi * θ by ring] at hh'
    have hden : 0 < (4 / Real.pi) * θ := mul_pos h4pi hθ.1
    have hstep : |h θ| / Real.sin (2 * θ) ≤ (Co * θ) / ((4 / Real.pi) * θ) :=
      div_le_div₀ (mul_nonneg hCo0 (le_of_lt hθ.1)) hhbd hden hlow
    have heq : (Co * θ) / ((4 / Real.pi) * θ) = Co * Real.pi / 4 := by
      rw [mul_div_mul_right Co (4 / Real.pi) (ne_of_gt hθ.1)]
      field_simp
    calc |SinQ h θ| = |h θ| / Real.sin (2 * θ) := by
          simp only [SinQ, abs_div, abs_of_pos hsinpos]
      _ ≤ (Co * θ) / ((4 / Real.pi) * θ) := hstep
      _ = Co * Real.pi / 4 := heq
  -- (9)
  have hsin9 : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |SinQ h θ| ≤ Co * Real.pi / 4 := by
    intro θ hθ
    have hhbd : |h θ| ≤ Co * (Real.pi / 2 - θ) := by
      have hh' := ho1 θ ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt hθ.2⟩
      rwa [min_eq_right (by linarith [hθ.1])] at hh'
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2])
    have hsin_eq : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
      rw [show 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) by ring, Real.sin_pi_sub]
    have hlow : (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
      rw [hsin_eq]
      have hh' := Real.mul_le_sin (x := 2 * (Real.pi / 2 - θ)) (by linarith [hθ.2])
        (by linarith [hθ.1, Real.pi_pos])
      rwa [show (2 : ℝ) / Real.pi * (2 * (Real.pi / 2 - θ))
        = (4 : ℝ) / Real.pi * (Real.pi / 2 - θ) by ring] at hh'
    have hden : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hden' : 0 < (4 / Real.pi) * (Real.pi / 2 - θ) := mul_pos h4pi hden
    have hstep : |h θ| / Real.sin (2 * θ)
        ≤ (Co * (Real.pi / 2 - θ)) / ((4 / Real.pi) * (Real.pi / 2 - θ)) :=
      div_le_div₀ (mul_nonneg hCo0 (by linarith [hθ.2])) hhbd hden' hlow
    have heq : (Co * (Real.pi / 2 - θ)) / ((4 / Real.pi) * (Real.pi / 2 - θ))
        = Co * Real.pi / 4 := by
      rw [mul_div_mul_right Co (4 / Real.pi) (ne_of_gt hden)]
      field_simp
    calc |SinQ h θ| = |h θ| / Real.sin (2 * θ) := by
          simp only [SinQ, abs_div, abs_of_pos hsinpos]
      _ ≤ (Co * (Real.pi / 2 - θ)) / ((4 / Real.pi) * (Real.pi / 2 - θ)) := hstep
      _ = Co * Real.pi / 4 := heq
  -- (10)
  have hcont10 : ContinuousOn (fun x => deriv (SinQ h) x)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hcu1.mono (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  have hloc10 : ∃ C δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 4 + δ), |deriv (SinQ h) x| ≤ C := by
    obtain ⟨Cl, δl, hδl, hlb⟩ := exists_bound_near_of_continuousAt
      (hcu1.continuousAt (isOpen_Ioo.mem_nhds ⟨hpi4, hπ4lt⟩))
    refine ⟨Cl, min δl (Real.pi / 4), lt_min hδl hpi4, fun x hx => ?_⟩
    exact hlb x ⟨by linarith [hx.1, hδl],
      by have := min_le_left δl (Real.pi / 4); linarith [hx.2]⟩
  have hloc10' : ∃ C δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |deriv (SinQ h) x| ≤ C := by
    refine ⟨Cq, min δq (Real.pi / 4), lt_min hδq hpi4, fun x hx => ?_⟩
    exact hq5 x ⟨by have := min_le_left δq (Real.pi / 4); linarith [hx.1], hx.2⟩
  obtain ⟨C10, hC10⟩ := exists_bound_of_continuousOn_Ioo hπ4lt hcont10 hloc10 hloc10'
  have hC10nn : 0 ≤ C10 := by
    have hmem : (Real.pi / 3 : ℝ) ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hC10 _ hmem)
  -- final assembly
  set C : ℝ := Cz + Cp + Co * Real.pi / 4 + Cu + C10 + 1 with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; linarith [hCz0, hCp0, hCo4nn, hCu0, hC10nn]
  have hCzC : Cz ≤ C := by rw [hCdef]; linarith [hCp0, hCo4nn, hCu0, hC10nn]
  have hCpC : Cp ≤ C := by rw [hCdef]; linarith [hCz0, hCo4nn, hCu0, hC10nn]
  have hCoC : Co * Real.pi / 4 ≤ C := by rw [hCdef]; linarith [hCz0, hCp0, hCu0, hC10nn]
  have hCuC : Cu ≤ C := by rw [hCdef]; linarith [hCz0, hCp0, hCo4nn, hC10nn]
  have hC10C : C10 ≤ C := by rw [hCdef]; linarith [hCz0, hCp0, hCo4nn, hCu0]
  refine ⟨C, hCnn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    have h1 := hz1 θ hθ
    have h2 : Cz * θ ≤ C * θ := mul_le_mul_of_nonneg_right hCzC (le_of_lt hθ.1)
    linarith
  · intro θ hθ
    have h1 := hz2 θ hθ
    have h2 : Cz * θ ≤ C * θ := mul_le_mul_of_nonneg_right hCzC (le_of_lt hθ.1)
    linarith
  · intro θ hθ; exact le_trans (hz3 θ hθ) hCzC
  · intro θ hθ; exact le_trans (hsin4 θ hθ) hCoC
  · intro θ hθ; exact le_trans (hu5 θ hθ) hCuC
  · intro θ hθ
    have h1 := hp1 θ hθ
    have h2 : Cp * (Real.pi / 2 - θ) ≤ C * (Real.pi / 2 - θ) :=
      mul_le_mul_of_nonneg_right hCpC (by linarith [hθ.2])
    linarith
  · intro θ hθ
    have h1 := hp2 θ hθ
    have h2 : Cp * (Real.pi / 2 - θ) ≤ C * (Real.pi / 2 - θ) :=
      mul_le_mul_of_nonneg_right hCpC (by linarith [hθ.2])
    linarith
  · intro θ hθ; exact le_trans (hp3 θ hθ) hCpC
  · intro θ hθ; exact le_trans (hsin9 θ hθ) hCoC
  · intro θ hθ; exact le_trans (hC10 θ hθ) hC10C

end Work.Elliptic
