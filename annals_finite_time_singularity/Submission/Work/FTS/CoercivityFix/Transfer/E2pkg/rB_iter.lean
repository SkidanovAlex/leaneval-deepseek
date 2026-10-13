/-
# `Transfer/E2pkg/rB_iter.lean` — the explicit `(z∂_z)`-iterates of `z²/(1+z)³`

`DzdIter j` is the `j`-fold iterate of the operator `Dzd = z ∂_z` on functions of one
variable (`Work.Elliptic.DzdIter`), and `rB j` is the closed form

  `rB j z = z²·N_j(z)/(1+z)^{j+3}`,

`N_0 = 1`, `N_1 = 2 - z`, `N_2 = 4 - 7z + z²`, `N_3 = 8 - 33z + 18z² - z³`,
`N_4 = 16 - 131z + 171z² - 41z³ + z⁴`, recorded in
`Transfer/E2pkg/dzdIter_defs.lean`.  This file proves that the two agree on `(0,∞)` for
`j ≤ 4`.

The whole proof is the elementary one-dimensional recursion

  `z · d/dz [ z²·P(z)/(1+z)^{m+1} ] = z²·( (1+z)(2P(z) + zP'(z)) - (m+1)·z·P(z) ) / (1+z)^{m+2}`

(`z_mul_deriv_rat`) applied four times, starting from `P = 1`, `m = 2`:

* `P = 1` (m = 2):   numerator `(1+z)·2 - 3z = 2 - z` — this is `rB 1`;
* `P = 2-z` (m = 3): numerator `(1+z)(4-3z) - 4z(2-z) = 4 - 7z + z²` — this is `rB 2`;
* `P = 4-7z+z²` (m = 4): numerator `8 - 33z + 18z² - z³` — this is `rB 3`;
* `P = 8-33z+18z²-z³` (m = 5): numerator `16 - 131z + 171z² - 41z³ + z⁴` — this is `rB 4`.

Since the recursion is pointwise only away from the pole `z = -1`, the iterates are glued
along the germ of a point `z > 0` with `Filter.EventuallyEq.deriv_eq`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_defs
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

set_option maxHeartbeats 800000

/-! ## The one-dimensional recursion -/

/-- The recursion step for the `(z∂_z)`-iterates of a rational function
`w ↦ w²·P(w)/(1+w)^{m+1}`: for `z ≠ -1`,

  `z · d/dz [ w²·P(w)/(1+w)^{m+1} ] = z²·( (1+z)(2P(z)+zP'(z)) - (m+1)·z·P(z) ) / (1+z)^{m+2}`. -/
theorem z_mul_deriv_rat (P : ℝ → ℝ) (P' : ℝ) (m : ℕ) (z : ℝ)
    (hP : HasDerivAt P P' z) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 * P w / (1 + w) ^ (m + 1)) z
      = z ^ 2 * ((1 + z) * (2 * P z + z * P') - (m + 1) * z * P z) / (1 + z) ^ (m + 2) := by
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hnum : HasDerivAt (fun w : ℝ => w ^ 2 * P w) (2 * z * P z + z ^ 2 * P') z := by
    convert (h2.mul hP) using 1
  have h1z : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (m + 1)) ((m + 1 : ℕ) * (1 + z) ^ m) z := by
    convert h1z.pow (m + 1) using 1
    simp
  have hden0 : (1 + z) ^ (m + 1) ≠ 0 := pow_ne_zero _ hz
  have hres := hnum.div hden hden0
  have hfun : (fun w : ℝ => w ^ 2 * P w / (1 + w) ^ (m + 1))
      = (fun w : ℝ => w ^ 2 * P w) / (fun w : ℝ => (1 + w) ^ (m + 1)) := rfl
  rw [hfun, hres.deriv]
  have hsq : ((1 + z) ^ (m + 1)) ^ 2 = (1 + z) ^ (m + 2) * (1 + z) ^ m := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hsq]
  simp only [pow_succ]
  field_simp
  push_cast
  ring

/-! ## The four instances (`Dzd` of the `rB`-profiles) -/

/-- `z ∂_z` of `w²/(1+w)³` is `rB 1`. -/
theorem z_mul_deriv_rB_zero (z : ℝ) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 / (1 + w) ^ 3) z = rB 1 z := by
  have h := z_mul_deriv_rat (fun _ : ℝ => (1 : ℝ)) 0 2 z (hasDerivAt_const z 1) hz
  have heq : (fun w : ℝ => w ^ 2 / (1 + w) ^ 3)
      = (fun w : ℝ => w ^ 2 * 1 / (1 + w) ^ 3) := by
    funext w
    rw [mul_one]
  rw [heq]
  refine h.trans ?_
  simp only [rB_one]
  ring_nf

/-- `z ∂_z` of `w²(2-w)/(1+w)⁴` is `rB 2`. -/
theorem z_mul_deriv_rB_one (z : ℝ) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 * (2 - w) / (1 + w) ^ 4) z = rB 2 z := by
  have hlin : HasDerivAt (fun w : ℝ => w) (1 : ℝ) z := by simpa using hasDerivAt_pow 1 z
  have hP : HasDerivAt (fun w : ℝ => 2 - w) (-1) z := by
    have h0 := (hasDerivAt_const z (2 : ℝ)).sub hlin
    convert h0 using 1 <;> first | ring | (ext w; ring)
  refine (z_mul_deriv_rat (fun w : ℝ => 2 - w) (-1) 3 z hP hz).trans ?_
  simp only [rB_two]
  ring_nf

/-- `z ∂_z` of `w²(4-7w+w²)/(1+w)⁵` is `rB 3`. -/
theorem z_mul_deriv_rB_two (z : ℝ) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 * (4 - 7 * w + w ^ 2) / (1 + w) ^ 5) z = rB 3 z := by
  have hlin : HasDerivAt (fun w : ℝ => w) (1 : ℝ) z := by simpa using hasDerivAt_pow 1 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hP : HasDerivAt (fun w : ℝ => 4 - 7 * w + w ^ 2) (-7 + 2 * z) z := by
    have h0 := ((hasDerivAt_const z (4 : ℝ)).sub (hlin.const_mul 7)).add h2
    convert h0 using 1 <;> first | ring | (ext w; ring)
  refine (z_mul_deriv_rat (fun w : ℝ => 4 - 7 * w + w ^ 2) (-7 + 2 * z) 4 z hP hz).trans ?_
  simp only [rB_three]
  ring_nf

/-- `z ∂_z` of `w²(8-33w+18w²-w³)/(1+w)⁶` is `rB 4`. -/
theorem z_mul_deriv_rB_three (z : ℝ) (hz : 1 + z ≠ 0) :
    z * deriv (fun w : ℝ => w ^ 2 * (8 - 33 * w + 18 * w ^ 2 - w ^ 3) / (1 + w) ^ 6) z
      = rB 4 z := by
  have hlin : HasDerivAt (fun w : ℝ => w) (1 : ℝ) z := by simpa using hasDerivAt_pow 1 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have h3 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    simpa using hasDerivAt_pow 3 z
  have hP : HasDerivAt (fun w : ℝ => 8 - 33 * w + 18 * w ^ 2 - w ^ 3)
      (-33 + 36 * z - 3 * z ^ 2) z := by
    have h0 := (((hasDerivAt_const z (8 : ℝ)).sub (hlin.const_mul 33)).add (h2.const_mul 18)).sub h3
    convert h0 using 1 <;> first | ring | (ext w; ring)
  refine (z_mul_deriv_rat (fun w : ℝ => 8 - 33 * w + 18 * w ^ 2 - w ^ 3)
    (-33 + 36 * z - 3 * z ^ 2) 5 z hP hz).trans ?_
  simp only [rB_four]
  ring_nf

/-! ## The iterates, level by level -/

/-- `DzdIter 1 fB = rB 1` away from the pole. -/
theorem dzdIter_fB_one (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 1 fB z = rB 1 z :=
  z_mul_deriv_rB_zero z hz

/-- `DzdIter 2 fB = rB 2` away from the pole. -/
theorem dzdIter_fB_two (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 2 fB z = rB 2 z := by
  have hzne : z ≠ -1 := by
    intro h
    exact hz (by linarith)
  have hev : Work.Elliptic.DzdIter 1 fB =ᶠ[𝓝 z] rB 1 :=
    (eventually_ne_nhds hzne).mono
      (fun w hw => dzdIter_fB_one w (by intro h; exact hw (by linarith)))
  have key : z * deriv (Work.Elliptic.DzdIter 1 fB) z = rB 2 z := by
    rw [hev.deriv_eq, rB_one]
    exact z_mul_deriv_rB_one z hz
  exact key

/-- `DzdIter 3 fB = rB 3` away from the pole. -/
theorem dzdIter_fB_three (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 3 fB z = rB 3 z := by
  have hzne : z ≠ -1 := by
    intro h
    exact hz (by linarith)
  have hev : Work.Elliptic.DzdIter 2 fB =ᶠ[𝓝 z] rB 2 :=
    (eventually_ne_nhds hzne).mono
      (fun w hw => dzdIter_fB_two w (by intro h; exact hw (by linarith)))
  have key : z * deriv (Work.Elliptic.DzdIter 2 fB) z = rB 3 z := by
    rw [hev.deriv_eq, rB_two]
    exact z_mul_deriv_rB_two z hz
  exact key

/-- `DzdIter 4 fB = rB 4` away from the pole. -/
theorem dzdIter_fB_four (z : ℝ) (hz : 1 + z ≠ 0) :
    Work.Elliptic.DzdIter 4 fB z = rB 4 z := by
  have hzne : z ≠ -1 := by
    intro h
    exact hz (by linarith)
  have hev : Work.Elliptic.DzdIter 3 fB =ᶠ[𝓝 z] rB 3 :=
    (eventually_ne_nhds hzne).mono
      (fun w hw => dzdIter_fB_three w (by intro h; exact hw (by linarith)))
  have key : z * deriv (Work.Elliptic.DzdIter 3 fB) z = rB 4 z := by
    rw [hev.deriv_eq, rB_three]
    exact z_mul_deriv_rB_three z hz
  exact key

/-! ## The target -/

theorem rB_iter : ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
    Work.Elliptic.DzdIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z = rB j z := by
  intro j hj z hz
  have hz1 : 1 + z ≠ 0 := by
    have hzpos : (0 : ℝ) < z := hz
    intro h
    linarith
  interval_cases j
  · rfl
  · exact dzdIter_fB_one z hz1
  · exact dzdIter_fB_two z hz1
  · exact dzdIter_fB_three z hz1
  · exact dzdIter_fB_four z hz1

end Work.FTS.CoercivityFix.Transfer.E2pkg
