import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.Pieces.RNP.hkerSqAux
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# The level-`5` radial iterates of `hKer² = z²/(1+z)⁴`

This file is the level-`5` companion of
`Submission.Work.FTS.Nonlinear.Pieces.RNP.hkerSqAux` (which stops at order `4`).  It recomputes
the `D_z = z ∂_z`-iterates of the radial profile `hKer(z)² = z²/(1+z)⁴` in closed form

  `D_z^i hKer² = z² q_i(z)/(1+z)^(4+i)`,

and bounds the polynomials `q_i` on `[0,∞)`:

  `|q1| ≤ 2(1+z)`, `|q2| ≤ 12(1+z)²`, `|q3| ≤ 52(1+z)³`, `|q4| ≤ 416(1+z)⁴`,
  `|q5| ≤ 6720(1+z)⁵`.

Hence `|D_z^i hKer² z| ≤ C·z²/(1+z)^3` for `i ≤ 5`, `z ≥ 0`, with the single constant
`C = 6720` (the extra power of `1+z` in the numerator is absorbed by `(1+z)³ ≤ (1+z)⁴`).

The private lemmas of `hkerSqAux` (the recursion steps `hasDerivAt_g*`/`deriv_g*_val`, the closed
forms `dz0`–`dz4`, the coefficient bounds `q*_le`) are copied here verbatim — `hkerSqAux.lean` is
not edited — and the missing step of order `5` is added: the recurrence

  `q_{i+1} = (1+z)(2 q_i + z q_i') − (4+i) z q_i`

gives `q5 = (1+z)(2q4 + z·q4') − 8z·q4 = 32 − 684z + 2644z² − 2644z³ + 684z⁴ − 32z⁵`.
-/

/-! ## The radial profile -/

private noncomputable def hk2 (z : ℝ) : ℝ := (Work.Spaces.hKer z) ^ 2

private lemma hk2_apply (z : ℝ) : hk2 z = z ^ 2 / (1 + z) ^ 4 := by
  rw [hk2, Work.Spaces.hKer_apply, div_pow]
  congr 1
  ring

/-- `hk2` is, definitionally, the function occurring in the statement. -/
private lemma hk2_eq_fun : hk2 = fun z : ℝ => (Work.Spaces.hKer z) ^ 2 := by
  funext z; rw [hk2]

/-! ## The polynomial numerators of the `D_z`-iterates -/

private noncomputable def q1 : ℝ → ℝ := fun z => 2 - 2 * z
private noncomputable def q2 : ℝ → ℝ := fun z => 4 - 12 * z + 4 * z ^ 2
private noncomputable def q3 : ℝ → ℝ := fun z => 8 - 52 * z + 52 * z ^ 2 - 8 * z ^ 3
private noncomputable def q4 : ℝ → ℝ :=
  fun z => 16 - 196 * z + 416 * z ^ 2 - 196 * z ^ 3 + 16 * z ^ 4

/-- The level-`5` numerator, `q5 = (1+z)(2q4 + z·q4') − 8z·q4`. -/
private noncomputable def q5 : ℝ → ℝ :=
  fun z => 32 - 684 * z + 2644 * z ^ 2 - 2644 * z ^ 3 + 684 * z ^ 4 - 32 * z ^ 5

/-- The closed forms of the `D_z`-iterates of `hKer²`:
`D_z^i hKer² = z² q_i(z)/(1+z)^(4+i)`, with `q_0 = 1`. -/
private noncomputable def gfun : ℕ → ℝ → ℝ
  | 0 => fun z => z ^ 2 / (1 + z) ^ 4
  | 1 => fun z => z ^ 2 * q1 z / (1 + z) ^ 5
  | 2 => fun z => z ^ 2 * q2 z / (1 + z) ^ 6
  | 3 => fun z => z ^ 2 * q3 z / (1 + z) ^ 7
  | 4 => fun z => z ^ 2 * q4 z / (1 + z) ^ 8
  | _ => fun z => z ^ 2 * q5 z / (1 + z) ^ 9

/-! ## Derivative computations -/

private lemma hasDerivAt_one_add_pow (n : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + z) ^ (n - 1)) z := by
  have h := (hasDerivAt_pow n (1 + z)).comp z ((hasDerivAt_id z).const_add 1)
  convert h using 1
  all_goals first
    | (funext w; simp only [Function.comp_apply, id_eq])
    | ring

private lemma hasDerivAt_q1 (z : ℝ) : HasDerivAt q1 (-2) z := by
  have h := ((hasDerivAt_const (x := z) (c := (2 : ℝ))).sub ((hasDerivAt_id z).const_mul 2))
  convert h using 1
  all_goals first
    | (funext w; simp only [q1, Pi.sub_apply, Pi.mul_apply, id_eq])
    | ring

private lemma hasDerivAt_q2 (z : ℝ) : HasDerivAt q2 (8 * z - 12) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h := (((hasDerivAt_const (x := z) (c := (4 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 12)).add (h1.const_mul 4))
  convert h using 1
  all_goals first
    | (funext w; simp only [q2, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring

private lemma hasDerivAt_q3 (z : ℝ) : HasDerivAt q3 (-24 * z ^ 2 + 104 * z - 52) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    simpa using hasDerivAt_pow 3 z
  have h := ((((hasDerivAt_const (x := z) (c := (8 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 52)).add (h1.const_mul 52)).sub (h2.const_mul 8))
  convert h using 1
  all_goals first
    | (funext w; simp only [q3, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring

private lemma hasDerivAt_q4 (z : ℝ) :
    HasDerivAt q4 (64 * z ^ 3 - 588 * z ^ 2 + 832 * z - 196) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by simpa using hasDerivAt_pow 3 z
  have h3 : HasDerivAt (fun w : ℝ => w ^ 4) (4 * z ^ 3) z := by simpa using hasDerivAt_pow 4 z
  have h := (((((hasDerivAt_const (x := z) (c := (16 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 196)).add (h1.const_mul 416)).sub (h2.const_mul 196)).add
      (h3.const_mul 16))
  convert h using 1
  all_goals first
    | (funext w; simp only [q4, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring

/-- The derivative of the level-`5` numerator. -/
private lemma hasDerivAt_q5 (z : ℝ) :
    HasDerivAt q5 (-684 + 5288 * z - 7932 * z ^ 2 + 2736 * z ^ 3 - 160 * z ^ 4) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by simpa using hasDerivAt_pow 3 z
  have h3 : HasDerivAt (fun w : ℝ => w ^ 4) (4 * z ^ 3) z := by simpa using hasDerivAt_pow 4 z
  have h4 : HasDerivAt (fun w : ℝ => w ^ 5) (5 * z ^ 4) z := by simpa using hasDerivAt_pow 5 z
  have h := (((((hasDerivAt_const (x := z) (c := (32 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 684)).add (h1.const_mul 2644)).sub (h2.const_mul 2644)).add
      (h3.const_mul 684)).sub (h4.const_mul 32)
  convert h using 1
  all_goals first
    | (funext w; simp only [q5, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring

/-! ## The recursion `q_{i+1} = (1+z)(2q_i + z q_i') − (4+i) z q_i`, one step at a time -/

private lemma deriv_g0_val (z : ℝ) (hz : 0 < z) :
    ((2 * z) * (1 + z) ^ 4 - z ^ 2 * ((4 : ℝ) * (1 + z) ^ (4 - 1)))
        / ((1 + z) ^ 4) ^ 2
      = z * q1 z / (1 + z) ^ 5 := by
  rw [q1]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma deriv_g1_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q1 z + z ^ 2 * (-2)) * (1 + z) ^ 5
        - (z ^ 2 * q1 z) * ((5 : ℝ) * (1 + z) ^ (5 - 1)))
        / ((1 + z) ^ 5) ^ 2
      = z * q2 z / (1 + z) ^ 6 := by
  rw [q1, q2]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma deriv_g2_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q2 z + z ^ 2 * (8 * z - 12)) * (1 + z) ^ 6
        - (z ^ 2 * q2 z) * ((6 : ℝ) * (1 + z) ^ (6 - 1)))
        / ((1 + z) ^ 6) ^ 2
      = z * q3 z / (1 + z) ^ 7 := by
  rw [q2, q3]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma deriv_g3_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q3 z + z ^ 2 * (-24 * z ^ 2 + 104 * z - 52)) * (1 + z) ^ 7
        - (z ^ 2 * q3 z) * ((7 : ℝ) * (1 + z) ^ (7 - 1)))
        / ((1 + z) ^ 7) ^ 2
      = z * q4 z / (1 + z) ^ 8 := by
  rw [q3, q4]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The level-`5` step of the recurrence. -/
private lemma deriv_g4_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q4 z + z ^ 2 * (64 * z ^ 3 - 588 * z ^ 2 + 832 * z - 196)) * (1 + z) ^ 8
        - (z ^ 2 * q4 z) * ((8 : ℝ) * (1 + z) ^ (8 - 1)))
        / ((1 + z) ^ 8) ^ 2
      = z * q5 z / (1 + z) ^ 9 := by
  rw [q4, q5]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma hasDerivAt_g0 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 / (1 + w) ^ 4) (z * q1 z / (1 + z) ^ 5) z := by
  have hnum : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 / (1 + w) ^ 4)
      (((2 * z) * (1 + z) ^ 4 - z ^ 2 * ((4 : ℝ) * (1 + z) ^ (4 - 1)))
        / ((1 + z) ^ 4) ^ 2) z :=
    hnum.div (hasDerivAt_one_add_pow 4 z) (by positivity)
  rw [deriv_g0_val z hz] at h
  exact h

private lemma hasDerivAt_g1 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q1 w / (1 + w) ^ 5) (z * q2 z / (1 + z) ^ 6) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q1 w / (1 + w) ^ 5)
      (((2 * z * q1 z + z ^ 2 * (-2)) * (1 + z) ^ 5
        - (z ^ 2 * q1 z) * ((5 : ℝ) * (1 + z) ^ (5 - 1))) / ((1 + z) ^ 5) ^ 2) z :=
    (hp.mul (hasDerivAt_q1 z)).div (hasDerivAt_one_add_pow 5 z) (by positivity)
  rw [deriv_g1_val z hz] at h
  exact h

private lemma hasDerivAt_g2 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q2 w / (1 + w) ^ 6) (z * q3 z / (1 + z) ^ 7) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q2 w / (1 + w) ^ 6)
      (((2 * z * q2 z + z ^ 2 * (8 * z - 12)) * (1 + z) ^ 6
        - (z ^ 2 * q2 z) * ((6 : ℝ) * (1 + z) ^ (6 - 1))) / ((1 + z) ^ 6) ^ 2) z :=
    (hp.mul (hasDerivAt_q2 z)).div (hasDerivAt_one_add_pow 6 z) (by positivity)
  rw [deriv_g2_val z hz] at h
  exact h

private lemma hasDerivAt_g3 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q3 w / (1 + w) ^ 7) (z * q4 z / (1 + z) ^ 8) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q3 w / (1 + w) ^ 7)
      (((2 * z * q3 z + z ^ 2 * (-24 * z ^ 2 + 104 * z - 52)) * (1 + z) ^ 7
        - (z ^ 2 * q3 z) * ((7 : ℝ) * (1 + z) ^ (7 - 1))) / ((1 + z) ^ 7) ^ 2) z :=
    (hp.mul (hasDerivAt_q3 z)).div (hasDerivAt_one_add_pow 7 z) (by positivity)
  rw [deriv_g3_val z hz] at h
  exact h

private lemma hasDerivAt_g4 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q4 w / (1 + w) ^ 8) (z * q5 z / (1 + z) ^ 9) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q4 w / (1 + w) ^ 8)
      (((2 * z * q4 z + z ^ 2 * (64 * z ^ 3 - 588 * z ^ 2 + 832 * z - 196)) * (1 + z) ^ 8
        - (z ^ 2 * q4 z) * ((8 : ℝ) * (1 + z) ^ (8 - 1))) / ((1 + z) ^ 8) ^ 2) z :=
    (hp.mul (hasDerivAt_q4 z)).div (hasDerivAt_one_add_pow 8 z) (by positivity)
  rw [deriv_g4_val z hz] at h
  exact h

private lemma dzStep0 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 0) (z * q1 z / (1 + z) ^ 5) z :=
  hasDerivAt_g0 hz

private lemma dzStep1 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 1) (z * q2 z / (1 + z) ^ 6) z :=
  hasDerivAt_g1 hz

private lemma dzStep2 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 2) (z * q3 z / (1 + z) ^ 7) z :=
  hasDerivAt_g2 hz

private lemma dzStep3 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 3) (z * q4 z / (1 + z) ^ 8) z :=
  hasDerivAt_g3 hz

private lemma dzStep4 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 4) (z * q5 z / (1 + z) ^ 9) z :=
  hasDerivAt_g4 hz

/-! ## The closed forms of the `D_z`-iterates -/

private lemma dz0 : Set.EqOn (Work.Elliptic.DzdIter 0 hk2) (gfun 0) (Set.Ioi 0) := by
  intro z hz
  show hk2 z = z ^ 2 / (1 + z) ^ 4
  exact hk2_apply z

private lemma dz1 : Set.EqOn (Work.Elliptic.DzdIter 1 hk2) (gfun 1) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 0 hk2) z = z ^ 2 * q1 z / (1 + z) ^ 5
  rw [show Work.Elliptic.DzdIter 0 hk2 = hk2 from rfl,
    (Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall hk2_apply)),
    (hasDerivAt_g0 hz).deriv]
  ring

private lemma dz2 : Set.EqOn (Work.Elliptic.DzdIter 2 hk2) (gfun 2) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 1 hk2) z = z ^ 2 * q2 z / (1 + z) ^ 6
  rw [show deriv (Work.Elliptic.DzdIter 1 hk2) z = deriv (gfun 1) z from
      (dz1.deriv isOpen_Ioi) hz,
    (dzStep1 hz).deriv]
  ring

private lemma dz3 : Set.EqOn (Work.Elliptic.DzdIter 3 hk2) (gfun 3) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 2 hk2) z = z ^ 2 * q3 z / (1 + z) ^ 7
  rw [show deriv (Work.Elliptic.DzdIter 2 hk2) z = deriv (gfun 2) z from
      (dz2.deriv isOpen_Ioi) hz,
    (dzStep2 hz).deriv]
  ring

private lemma dz4 : Set.EqOn (Work.Elliptic.DzdIter 4 hk2) (gfun 4) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 3 hk2) z = z ^ 2 * q4 z / (1 + z) ^ 8
  rw [show deriv (Work.Elliptic.DzdIter 3 hk2) z = deriv (gfun 3) z from
      (dz3.deriv isOpen_Ioi) hz,
    (dzStep3 hz).deriv]
  ring

/-- `D_z^4 hKer² = z² q4/(1+z)^8`; the new step is `D_z^5`. -/
private lemma dz5 : Set.EqOn (Work.Elliptic.DzdIter 5 hk2) (gfun 5) (Set.Ioi 0) := by
  intro z hz
  show z * deriv (Work.Elliptic.DzdIter 4 hk2) z = z ^ 2 * q5 z / (1 + z) ^ 9
  rw [show deriv (Work.Elliptic.DzdIter 4 hk2) z = deriv (gfun 4) z from
      (dz4.deriv isOpen_Ioi) hz,
    (dzStep4 hz).deriv]
  ring

private lemma dzIter_hk2_eqOn (i : ℕ) (hi : i ≤ 5) :
    Set.EqOn (Work.Elliptic.DzdIter i (fun z : ℝ => (Work.Spaces.hKer z) ^ 2)) (gfun i)
      (Set.Ioi 0) := by
  rw [← hk2_eq_fun]
  interval_cases i
  · exact dz0
  · exact dz1
  · exact dz2
  · exact dz3
  · exact dz4
  · exact dz5

/-! ## The coefficient bounds -/

private lemma q1_le (z : ℝ) (hz : 0 ≤ z) : |q1 z| ≤ 2 * (1 + z) := by
  rw [q1, abs_le]
  constructor <;> linarith

private lemma q2_le (z : ℝ) (hz : 0 ≤ z) : |q2 z| ≤ 12 * (1 + z) ^ 2 := by
  rw [q2, abs_le]
  constructor <;>
    nlinarith [hz, sq_nonneg z, sq_nonneg (1 + z), mul_nonneg hz hz]

private lemma q3_le (z : ℝ) (hz : 0 ≤ z) : |q3 z| ≤ 52 * (1 + z) ^ 3 := by
  rw [q3, abs_le]
  constructor <;>
    nlinarith [hz, sq_nonneg z, sq_nonneg (1 + z), mul_nonneg hz hz, mul_nonneg (sq_nonneg z) hz]

private lemma q4_le (z : ℝ) (hz : 0 ≤ z) : |q4 z| ≤ 416 * (1 + z) ^ 4 := by
  rw [q4, abs_le]
  constructor <;>
    nlinarith [hz, sq_nonneg z, sq_nonneg (1 + z), mul_nonneg hz hz, mul_nonneg (sq_nonneg z) hz]

/-- The level-`5` coefficient bound.  The constant `6720` is the sum of the absolute values of
the coefficients of `q5`, and `Σ|c_k| z^k ≤ Σ|c_k|(1+z)^k ≤ (Σ|c_k|)(1+z)^5` for `z ≥ 0`. -/
private lemma q5_le (z : ℝ) (hz : 0 ≤ z) : |q5 z| ≤ 6720 * (1 + z) ^ 5 := by
  have hexp : 6720 * (1 + z) ^ 5
      = 6720 + 33600 * z + 67200 * z ^ 2 + 67200 * z ^ 3 + 33600 * z ^ 4 + 6720 * z ^ 5 := by
    ring
  have h1 : (0 : ℝ) ≤ z := hz
  have h2 : (0 : ℝ) ≤ z ^ 2 := pow_nonneg hz 2
  have h3 : (0 : ℝ) ≤ z ^ 3 := pow_nonneg hz 3
  have h4 : (0 : ℝ) ≤ z ^ 4 := pow_nonneg hz 4
  have h5 : (0 : ℝ) ≤ z ^ 5 := pow_nonneg hz 5
  rw [q5, abs_le, hexp]
  constructor <;> linarith

/-! ## The level-`5` bound -/

/-- `(1+z)^3 ≤ (1+z)^4` in the form used below. -/
private lemma div_pow4_le_div_pow3 {z : ℝ} (hz : 0 ≤ z) :
    z ^ 2 / (1 + z) ^ 4 ≤ z ^ 2 / (1 + z) ^ 3 := by
  have h1z : 0 < 1 + z := by linarith
  have hpow : (1 : ℝ) / (1 + z) ^ 4 ≤ 1 / (1 + z) ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
  calc z ^ 2 / (1 + z) ^ 4 = z ^ 2 * (1 / (1 + z) ^ 4) := by ring
    _ ≤ z ^ 2 * (1 / (1 + z) ^ 3) := mul_le_mul_of_nonneg_left hpow (sq_nonneg z)
    _ = z ^ 2 / (1 + z) ^ 3 := by ring

/-- The generic reduction: `|q z| ≤ c (1+z)^i` and `c ≤ 6720` give the level-`5` bound. -/
private lemma gf_le_of {z : ℝ} (hz : 0 ≤ z) (i : ℕ) (Q : ℝ → ℝ) {c : ℝ}
    (hc : c ≤ 6720) (hq : |Q z| ≤ c * (1 + z) ^ i) :
    |z ^ 2 * Q z / (1 + z) ^ (4 + i)| ≤ 6720 * z ^ 2 / (1 + z) ^ 3 := by
  have h1z : 0 < 1 + z := by linarith
  have hdiv : 0 < (1 + z) ^ (4 + i) := by positivity
  have hA : 0 ≤ z ^ 2 / (1 + z) ^ 4 := by positivity
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg z), abs_of_nonneg (le_of_lt hdiv)]
  have h1 : z ^ 2 * |Q z| ≤ z ^ 2 * (c * (1 + z) ^ i) :=
    mul_le_mul_of_nonneg_left hq (sq_nonneg z)
  have h2 : z ^ 2 * (c * (1 + z) ^ i) / (1 + z) ^ (4 + i) = c * (z ^ 2 / (1 + z) ^ 4) := by
    rw [pow_add]
    field_simp
  have h3 : c * (z ^ 2 / (1 + z) ^ 4) ≤ 6720 * (z ^ 2 / (1 + z) ^ 3) :=
    (mul_le_mul_of_nonneg_right hc hA).trans
      (mul_le_mul_of_nonneg_left (div_pow4_le_div_pow3 hz) (by norm_num))
  calc z ^ 2 * |Q z| / (1 + z) ^ (4 + i)
      ≤ z ^ 2 * (c * (1 + z) ^ i) / (1 + z) ^ (4 + i) :=
        div_le_div_of_nonneg_right h1 (le_of_lt hdiv)
    _ = c * (z ^ 2 / (1 + z) ^ 4) := h2
    _ ≤ 6720 * (z ^ 2 / (1 + z) ^ 3) := h3
    _ = 6720 * z ^ 2 / (1 + z) ^ 3 := by ring

/-- The pointwise bound on the closed forms, for `z > 0`. -/
private lemma hk2_iter_le (i : ℕ) (hi : i ≤ 5) {z : ℝ} (hz : 0 < z) :
    |gfun i z| ≤ 6720 * z ^ 2 / (1 + z) ^ 3 := by
  have hz0 : 0 ≤ z := le_of_lt hz
  interval_cases i
  · -- `i = 0`
    show |z ^ 2 / (1 + z) ^ 4| ≤ 6720 * z ^ 2 / (1 + z) ^ 3
    rw [abs_of_nonneg (by positivity)]
    calc z ^ 2 / (1 + z) ^ 4 ≤ z ^ 2 / (1 + z) ^ 3 := div_pow4_le_div_pow3 hz0
      _ ≤ 6720 * (z ^ 2 / (1 + z) ^ 3) := by
          have hnn : (0 : ℝ) ≤ z ^ 2 / (1 + z) ^ 3 := by positivity
          linarith
      _ = 6720 * z ^ 2 / (1 + z) ^ 3 := by ring
  · exact gf_le_of hz0 1 q1 (c := 2) (by norm_num) (by simpa using q1_le z hz0)
  · exact gf_le_of hz0 2 q2 (c := 12) (by norm_num) (by simpa using q2_le z hz0)
  · exact gf_le_of hz0 3 q3 (c := 52) (by norm_num) (by simpa using q3_le z hz0)
  · exact gf_le_of hz0 4 q4 (c := 416) (by norm_num) (by simpa using q4_le z hz0)
  · exact gf_le_of hz0 5 q5 (c := 6720) (by norm_num) (by simpa using q5_le z hz0)

/-- The level-`5` radial iterates of `hKer(z)² = z²/(1+z)⁴` are bounded by `C·z²/(1+z)³`:
`D_z^i hKer² = z²q_i(z)/(1+z)^(4+i)` with `deg q_i ≤ i`, so `|D_z^i hKer² z| ≤ (Σ|coeffs|)·z²/(1+z)³`.
The file `Submission.Work.FTS.Nonlinear.Pieces.RNP.hkerSqAux` contains the whole computation for
`i ≤ 4` (private: `dzIter_hk2_eqOn`, `q1`–`q4`, `deriv_g*_val`, `hasDerivAt_g*`, `q*_le`); the new
step is `q5 = (1+z)(2q4 + z·q4') − 8z·q4 = 32 − 684z + 2644z² − 2644z³ + 684z⁴ − 32z⁵`, with
`|q4 z| ≤ 416(1+z)^4`, `|q5 z| ≤ 6720(1+z)^5` on `[0,∞)`.  The private lemmas may be copied
into the new file (do not edit `hkerSqAux.lean`). -/
theorem DzIter_hKerSq_le5 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i (fun z : ℝ => (Work.Spaces.hKer z) ^ 2) z|
      ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  refine ⟨6720, by norm_num, fun i hi z hz => ?_⟩
  rcases eq_or_lt_of_le hz with h0 | hpos
  · -- `z = 0`: the iterates of order `≥ 1` carry a factor `z`, and `hKer 0 = 0`
    subst h0
    cases i with
    | zero => simp [Work.Elliptic.DzdIter_zero, Work.Spaces.hKer_apply]
    | succ k => rw [Work.Elliptic.DzdIter_succ]; simp [Work.Elliptic.Dzd]
  · -- `z > 0`: use the closed form `D_z^i hKer² = z² q_i/(1+z)^(4+i)`
    rw [dzIter_hk2_eqOn i hi hpos]
    exact hk2_iter_le i hi hpos

end Work.FTS.StrongEps.H5.Atoms
