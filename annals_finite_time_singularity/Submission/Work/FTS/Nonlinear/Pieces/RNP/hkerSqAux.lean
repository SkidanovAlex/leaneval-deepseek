import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.H2.InvOneAddSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The radial profile `hKer²` of row 23, in `ℋ⁴` -/

/-- The radial profile `hKer(z)² = z²/(1+z)⁴` of row 23. -/
private noncomputable def hk2 (z : ℝ) : ℝ := (Work.Spaces.hKer z) ^ 2

private lemma hk2_apply (z : ℝ) : hk2 z = z ^ 2 / (1 + z) ^ 4 := by
  rw [hk2, Work.Spaces.hKer_apply, div_pow]
  congr 1
  ring

/-! ### The polynomial numerators of the `D_z`-iterates -/

private noncomputable def q1 : ℝ → ℝ := fun z => 2 - 2 * z
private noncomputable def q2 : ℝ → ℝ := fun z => 4 - 12 * z + 4 * z ^ 2
private noncomputable def q3 : ℝ → ℝ := fun z => 8 - 52 * z + 52 * z ^ 2 - 8 * z ^ 3
private noncomputable def q4 : ℝ → ℝ :=
  fun z => 16 - 196 * z + 416 * z ^ 2 - 196 * z ^ 3 + 16 * z ^ 4

/-- The closed forms of the `D_z`-iterates of `hKer²`:
`D_z^i hKer² = z² q_i(z)/(1+z)^(4+i)`, with `q_0 = 1`. -/
private noncomputable def gfun : ℕ → ℝ → ℝ
  | 0 => fun z => z ^ 2 / (1 + z) ^ 4
  | 1 => fun z => z ^ 2 * q1 z / (1 + z) ^ 5
  | 2 => fun z => z ^ 2 * q2 z / (1 + z) ^ 6
  | 3 => fun z => z ^ 2 * q3 z / (1 + z) ^ 7
  | _ => fun z => z ^ 2 * q4 z / (1 + z) ^ 8

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

private lemma dzStep0 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 0) (z * q1 z / (1 + z) ^ 5) z :=
  hasDerivAt_g0 hz

private lemma dzStep1 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 1) (z * q2 z / (1 + z) ^ 6) z :=
  hasDerivAt_g1 hz

private lemma dzStep2 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 2) (z * q3 z / (1 + z) ^ 7) z :=
  hasDerivAt_g2 hz

private lemma dzStep3 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 3) (z * q4 z / (1 + z) ^ 8) z :=
  hasDerivAt_g3 hz

/-! ### The closed forms of the `D_z`-iterates -/

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

private lemma dzIter_hk2_eqOn (i : ℕ) (hi : i ≤ 4) :
    Set.EqOn (Work.Elliptic.DzdIter i hk2) (gfun i) (Set.Ioi 0) := by
  interval_cases i
  · exact dz0
  · exact dz1
  · exact dz2
  · exact dz3
  · exact dz4

/-! ### The coefficient bounds -/

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

/-- The radial density of `ℋ⁴` of `hKer²`: `Rint hKer² z ≤ 865280/(1+z)^4`. -/
private lemma Rint_hk2_le {z : ℝ} (hz : 0 < z) :
    Work.FTS.Nonlinear.RadialProd.Rint hk2 z ≤ 865280 / (1 + z) ^ 4 := by
  have hz0 : 0 ≤ z := le_of_lt hz
  have h1z : 0 < 1 + z := by linarith
  have hterm : ∀ i ∈ Finset.range 5,
      (Work.Elliptic.DzdIter i hk2 z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 173056 / (1 + z) ^ 4 := by
    intro i hi
    have hi4 : i ≤ 4 := by
      have := Finset.mem_range.mp hi
      omega
    have heq := dzIter_hk2_eqOn i hi4 hz
    rw [heq]
    interval_cases i
    · -- i = 0
      show (z ^ 2 / (1 + z) ^ 4) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2 ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 / (1 + z) ^ 4) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = 1 / (1 + z) ^ 4 := by
        field_simp
        try ring
      rw [hn]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h1z]
    · -- i = 1
      show (z ^ 2 * q1 z / (1 + z) ^ 5) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
        ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 * q1 z / (1 + z) ^ 5) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = (q1 z) ^ 2 / (1 + z) ^ 6 := by
        field_simp
        try ring
      rw [hn]
      have hsq : (q1 z) ^ 2 ≤ (2 * (1 + z)) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (q1 z)) (q1_le z hz0) 2
        rw [sq_abs, mul_pow] at h
        nlinarith [h]
      calc (q1 z) ^ 2 / (1 + z) ^ 6 ≤ (2 * (1 + z)) ^ 2 / (1 + z) ^ 6 := by gcongr
        _ = 4 / (1 + z) ^ 4 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring
        _ ≤ 173056 / (1 + z) ^ 4 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1z]
    · -- i = 2
      show (z ^ 2 * q2 z / (1 + z) ^ 6) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
        ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 * q2 z / (1 + z) ^ 6) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = (q2 z) ^ 2 / (1 + z) ^ 8 := by
        field_simp
        try ring
      rw [hn]
      have hsq : (q2 z) ^ 2 ≤ (12 * (1 + z) ^ 2) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (q2 z)) (q2_le z hz0) 2
        rw [sq_abs, mul_pow] at h
        nlinarith [h]
      calc (q2 z) ^ 2 / (1 + z) ^ 8 ≤ (12 * (1 + z) ^ 2) ^ 2 / (1 + z) ^ 8 := by gcongr
        _ = 144 / (1 + z) ^ 4 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring
        _ ≤ 173056 / (1 + z) ^ 4 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1z]
    · -- i = 3
      show (z ^ 2 * q3 z / (1 + z) ^ 7) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
        ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 * q3 z / (1 + z) ^ 7) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = (q3 z) ^ 2 / (1 + z) ^ 10 := by
        field_simp
        try ring
      rw [hn]
      have hsq : (q3 z) ^ 2 ≤ (52 * (1 + z) ^ 3) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (q3 z)) (q3_le z hz0) 2
        rw [sq_abs, mul_pow] at h
        nlinarith [h]
      calc (q3 z) ^ 2 / (1 + z) ^ 10 ≤ (52 * (1 + z) ^ 3) ^ 2 / (1 + z) ^ 10 := by gcongr
        _ = 2704 / (1 + z) ^ 4 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring
        _ ≤ 173056 / (1 + z) ^ 4 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1z]
    · -- i = 4
      show (z ^ 2 * q4 z / (1 + z) ^ 8) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
        ≤ 173056 / (1 + z) ^ 4
      have hn : (z ^ 2 * q4 z / (1 + z) ^ 8) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2
          = (q4 z) ^ 2 / (1 + z) ^ 12 := by
        field_simp
        try ring
      rw [hn]
      have hsq : (q4 z) ^ 2 ≤ (416 * (1 + z) ^ 4) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (q4 z)) (q4_le z hz0) 2
        rw [sq_abs, mul_pow] at h
        nlinarith [h]
      calc (q4 z) ^ 2 / (1 + z) ^ 12 ≤ (416 * (1 + z) ^ 4) ^ 2 / (1 + z) ^ 12 := by gcongr
        _ = 173056 / (1 + z) ^ 4 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring
        _ ≤ 173056 / (1 + z) ^ 4 := le_refl _
  calc Work.FTS.Nonlinear.RadialProd.Rint hk2 z
      = ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i hk2 z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        rfl
    _ ≤ ∑ _i ∈ Finset.range 5, 173056 / (1 + z) ^ 4 := Finset.sum_le_sum hterm
    _ = 865280 / (1 + z) ^ 4 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring


/-! ### Smoothness, measurability and integrability of the density -/

private lemma smoothQuad_hKer :
    Work.FTS.LocData.SmoothQuad (fun z (_ : ℝ) => Work.Spaces.hKer z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Work.Spaces.hKer p.1)
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))
  have h : (fun p : ℝ × ℝ => Work.Spaces.hKer p.1) = fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 2 := by
    funext p; exact Work.Spaces.hKer_apply p.1
  rw [h]
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := contDiffOn_fst
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (1 + p.1) ^ 2)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    exact ((contDiffOn_const.add contDiffOn_fst)).pow 2
  exact hnum.div hden (fun p hp => by
    have hp1 : (-1 : ℝ) < p.1 := hp.1
    have h1 : (0 : ℝ) < 1 + p.1 := by linarith
    positivity)

private lemma smoothQuad_hk2 : Work.FTS.LocData.SmoothQuad (fun z (_ : ℝ) => hk2 z) := by
  have h1 : (fun z (_ : ℝ) => hk2 z)
      = fun z _ => Work.Spaces.hKer z * Work.Spaces.hKer z := by
    funext z θ; rw [hk2]; ring
  rw [h1]
  exact Work.FTS.LocData.smoothQuad_mul smoothQuad_hKer smoothQuad_hKer

private lemma aesm_Rint_hk2 : AEStronglyMeasurable (Work.FTS.Nonlinear.RadialProd.Rint hk2)
    (volume.restrict Work.Spaces.Iz) := by
  have hsum : Work.FTS.Nonlinear.RadialProd.Rint hk2
      = ∑ i ∈ Finset.range 5,
          (fun z => (Work.Elliptic.DzdIter i hk2 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    funext z
    simp only [Work.FTS.Nonlinear.RadialProd.Rint, Finset.sum_apply]
  rw [hsum]
  exact Finset.aestronglyMeasurable_sum _
    (fun i hi => Work.FTS.Nonlinear.RadialProd.aesm_DzdIter_sq_w_sq hk2 smoothQuad_hk2 i)

private lemma inv_one_add_le_one {z : ℝ} (hz : 0 ≤ z) : 1 / (1 + z) ≤ 1 := by
  have h : 0 < 1 + z := by linarith
  rw [div_le_one h]; linarith

private lemma inv_one_add_pow_le {z : ℝ} (hz : 0 ≤ z) :
    (1 / (1 + z)) ^ 4 ≤ (1 / (1 + z)) ^ 2 := by
  have h4 : 1 / (1 + z) ≤ 1 := inv_one_add_le_one hz
  have h5 : 0 ≤ 1 / (1 + z) := div_nonneg zero_le_one (by linarith)
  have h6 : (1 / (1 + z)) ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ h5 h4 2
    simpa using this
  calc (1 / (1 + z)) ^ 4 = (1 / (1 + z)) ^ 2 * (1 / (1 + z)) ^ 2 := by ring
    _ ≤ 1 * (1 / (1 + z)) ^ 2 := mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = (1 / (1 + z)) ^ 2 := by ring

private lemma inv_one_add_mul_eq {z : ℝ} :
    (865280 : ℝ) / (1 + z) ^ 4 = 865280 * (1 / (1 + z)) ^ 4 := by
  rw [div_eq_mul_inv, one_div, inv_pow]

/-- The pointwise domination of the radial density, valid on all of `Iz`. -/
private lemma Rint_hk2_le' {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Work.FTS.Nonlinear.RadialProd.Rint hk2 z ≤ 865280 * (1 / (1 + z)) ^ 2 := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
  · subst h0
    have h : Work.FTS.Nonlinear.RadialProd.Rint hk2 0 = 0 := by
      rw [Work.FTS.Nonlinear.RadialProd.Rint, Work.Spaces.w]
      simp
    rw [h]
    positivity
  · have h1 : Work.FTS.Nonlinear.RadialProd.Rint hk2 z ≤ 865280 / (1 + z) ^ 4 :=
      Rint_hk2_le hpos
    rw [inv_one_add_mul_eq] at h1
    exact h1.trans
      (mul_le_mul_of_nonneg_left (inv_one_add_pow_le (le_of_lt hpos)) (by norm_num))

private lemma integrable_Rint_hk2 : MeasureTheory.IntegrableOn
    (Work.FTS.Nonlinear.RadialProd.Rint hk2) Work.Spaces.Iz := by
  have hI : MeasureTheory.IntegrableOn (fun z : ℝ => (1 / (1 + z)) ^ 2) (Set.Ioi 0) :=
    Work.FTS.H2.InvOneAddSq.1
  have hI' : MeasureTheory.IntegrableOn (fun z : ℝ => 865280 * (1 / (1 + z)) ^ 2)
      Work.Spaces.Iz := by
    show Integrable (fun z : ℝ => 865280 * (1 / (1 + z)) ^ 2)
      (volume.restrict Work.Spaces.Iz)
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hI.const_mul 865280
  refine hI'.mono' aesm_Rint_hk2 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  rw [Real.norm_of_nonneg (Work.FTS.Nonlinear.RadialProd.Rint_nonneg hk2 z)]
  exact Rint_hk2_le' hz

/-- The radial quantity `Rr hKer²` is bounded by `1730560`. -/
private lemma Rr_hk2_le : Work.FTS.Nonlinear.RadialProd.Rr hk2 ≤ 1730560 := by
  have hI : MeasureTheory.IntegrableOn (fun z : ℝ => (1 / (1 + z)) ^ 2) (Set.Ioi 0) :=
    Work.FTS.H2.InvOneAddSq.1
  have hI' : MeasureTheory.IntegrableOn (fun z : ℝ => 865280 * (1 / (1 + z)) ^ 2)
      Work.Spaces.Iz := by
    show Integrable (fun z : ℝ => 865280 * (1 / (1 + z)) ^ 2)
      (volume.restrict Work.Spaces.Iz)
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      ← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact hI.const_mul 865280
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => Work.FTS.Nonlinear.RadialProd.Rint_nonneg hk2 z)
    hI' (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
      (fun z hz => Rint_hk2_le' hz))
  have hval : (∫ z in Work.Spaces.Iz, 865280 * (1 / (1 + z)) ^ 2)
      = 865280 * ∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2 :=
    MeasureTheory.integral_const_mul _ _
  rw [hval] at hmain
  have h2' : (∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2) ≤ 2 := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      ← MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact Work.FTS.H2.InvOneAddSq.2
  calc Work.FTS.Nonlinear.RadialProd.Rr hk2
      = ∫ z in Work.Spaces.Iz, Work.FTS.Nonlinear.RadialProd.Rint hk2 z := rfl
    _ ≤ 865280 * ∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2 := hmain
    _ ≤ 865280 * 2 := mul_le_mul_of_nonneg_left h2' (by norm_num)
    _ = 1730560 := by norm_num

private lemma Kth_le : Work.FTS.Nonlinear.RadialProd.Kth ≤ 10000 := by
  have h1 : -1 < -(Work.Spaces.eta) := by have := Work.Spaces.eta_lt_one; linarith
  have h2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) h1 h2).2
  have h3 : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
  rw [h3] at h
  norm_num at h
  show (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ) ≤ 10000
  exact h

/-- **The radial input `hkerSq_radial` of row 23.** -/
theorem hkerSq_radial_alt :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) ∧
      Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) ≤ C := by
  refine ⟨Real.sqrt (1730560 * 10000) + 1, by positivity, ?_⟩
  intro α hα hα1
  have hswap : (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) = fun z (_ : ℝ) => hk2 z := by
    funext z θ; rw [hk2]
  rw [hswap]
  constructor
  · -- `HkMem`
    constructor
    · -- the `θ`-slices
      intro z hz
      have h1 : -1 < -(Work.Spaces.eta) := by have := Work.Spaces.eta_lt_one; linarith
      have h2 : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_pos; linarith
      have h3 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
        (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) h1 h2).1
      have h4 : MeasureTheory.Integrable
          (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.Rint hk2 z
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (volume.restrict Work.Spaces.Iθ) :=
        h3.const_mul _
      have hslice : MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.Rint hk2 z
            * Work.FTS.Nonlinear.RadialProd.smE θ) Work.Spaces.Iθ := by
        refine h4.congr (Filter.Eventually.of_forall fun θ => ?_)
        simp only [Work.FTS.Nonlinear.RadialProd.smE]
      refine hslice.congr_fun (fun θ hθ => ?_) measurableSet_Icc
      show Work.FTS.Nonlinear.RadialProd.Rint hk2 z * Work.FTS.Nonlinear.RadialProd.smE θ
        = Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => hk2 z) z θ
      rw [Work.Elliptic.HkIntegrand_rad α 4 hk2 z hθ, Work.FTS.Nonlinear.RadialProd.Rint,
        Finset.sum_mul]
      simp only [Work.FTS.Nonlinear.RadialProd.smE]
      rw [Finset.sum_mul, Finset.sum_mul]
    · -- the `z`-integral of the slices
      have hcongr : (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => hk2 z) z θ)
          = fun z => Work.FTS.Nonlinear.RadialProd.Rint hk2 z
              * Work.FTS.Nonlinear.RadialProd.Kth :=
        funext fun z => Work.FTS.Nonlinear.RadialProd.integral_HkIntegrand_rad α hk2 z
      rw [hcongr]
      exact integrable_Rint_hk2.mul_const _
  · -- the `Xn` bound
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Work.FTS.Nonlinear.RadialProd.HkSq_rad_eq]
    have hK0 : 0 ≤ Work.FTS.Nonlinear.RadialProd.Kth :=
      le_trans (by norm_num) Work.FTS.Nonlinear.RadialProd.one_le_Kth
    have hstep : Work.FTS.Nonlinear.RadialProd.Rr hk2 * Work.FTS.Nonlinear.RadialProd.Kth
        ≤ 1730560 * 10000 :=
      mul_le_mul Rr_hk2_le Kth_le hK0 (by norm_num)
    refine (Real.sqrt_le_sqrt hstep).trans ?_
    linarith [Real.sqrt_nonneg (1730560 * 10000)]

end Work.FTS.Nonlinear.Pieces.RNP
