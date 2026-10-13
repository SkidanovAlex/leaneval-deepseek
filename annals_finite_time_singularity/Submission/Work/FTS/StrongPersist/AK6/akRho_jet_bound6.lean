import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.NonlinRows.AkRhoJetBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The order-`6` radial jet bound for the profile `z ↦ 2z²/(1+z)³`

We prove

`∃ R, 0 ≤ R ∧ ∀ j ≤ 6, ∀ z ∈ [0,∞), ∀ θ, (D_z^j f(z,θ) · w z)^2 ≤ R/(1+z)^2`,
`f z θ = 2z²/(1+z)³`, `w z = (1+z)²/z²`, `D_z = z ∂_z`

— the order-`6` strengthening of `Work.FTS.NonlinRows.AkRhoJetBasic.akRho_jet_bound`
(which covers `j ≤ 4` and `0 < z`).

The proof identifies the jets exactly: with `P_j` an explicit polynomial of degree `j`
(coefficients `akC j`),

`D_z^j f(z,θ) = z² · P_j(z) / (1+z)^{j+3}`  (for `z ≠ -1`),

equivalently `D_z^j f(z,θ) · w z = P_j(z)/(1+z)^{j+1}` on `z > 0`.  This is proved by
induction on `j` from the closed forms: the recursion `D_z^{j+1} f = z ∂_z(D_z^j f)` turns
into `P_{j+1} = z(1+z) P_j' + (2 - (j+1)z) P_j` for the numerators, which is exactly what
the `HasDerivAt` computation of the derivative of `w ↦ w² P_j(w)/(1+w)^{j+3}` produces.
The bound then follows from `|P_j(z)| ≤ (Σ_i |akC j i|)(1+z)^j ≤ 40320·(1+z)^j` for `z ≥ 0`
(the coefficient sums are `(j+1)!`, so `40320` works uniformly for `j ≤ 6`).

The `j ≤ 4` part can also be read off from `akRho_jet_bound`, but the argument here is
uniform in `j ≤ 6`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.AK6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The profile `z ↦ 2z²/(1+z)³`, as a function of `(z,θ)` independent of `θ`. -/
def akf : ℝ → ℝ → ℝ := fun z _ => 2 * z ^ 2 / (1 + z) ^ 3

/-- Coefficients of `P_j`, the numerator of the `j`-th weighted radial jet:
`akC j i` is the coefficient of `z^i` in `P_j` (and `0` for `i > j`). -/
def akC : ℕ → ℕ → ℝ
  | 0, i => if i = 0 then 2 else 0
  | 1, i => if i = 0 then 4 else if i = 1 then -2 else 0
  | 2, i => if i = 0 then 8 else if i = 1 then -14 else if i = 2 then 2 else 0
  | 3, i => if i = 0 then 16 else if i = 1 then -66 else if i = 2 then 36
              else if i = 3 then -2 else 0
  | 4, i => if i = 0 then 32 else if i = 1 then -262 else if i = 2 then 342
              else if i = 3 then -82 else if i = 4 then 2 else 0
  | 5, i => if i = 0 then 64 else if i = 1 then -946 else if i = 2 then 2416
              else if i = 3 then -1436 else if i = 4 then 176
              else if i = 5 then -2 else 0
  | _, i => if i = 0 then 128 else if i = 1 then -3222 else if i = 2 then 14394
              else if i = 3 then -16844 else if i = 4 then 5364
              else if i = 5 then -366 else if i = 6 then 2 else 0

/-- The polynomial `P_j` whose coefficients are `akC j`. -/
def akP (j : ℕ) (z : ℝ) : ℝ := ∑ i ∈ Finset.range (j + 1), akC j i * z ^ i

/-- The formal derivative of `akP j`. -/
def akPd (j : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), akC j i * ((i : ℝ) * z ^ (i - 1))

lemma hasDerivAt_akP (j : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => akP j w) (akPd j z) z := by
  simp only [akP, akPd]
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_pow i z).const_mul (akC j i)

lemma akC_sum_le (j : ℕ) (hj : j ≤ 6) :
    (∑ i ∈ Finset.range (j + 1), |akC j i|) ≤ 40320 := by
  interval_cases j <;> simp [akC, Finset.sum_range_succ] <;> norm_num

/-- The coefficient bound `|P_j(z)| ≤ 40320 (1+z)^j` for `z ≥ 0`, `j ≤ 6`. -/
lemma akP_abs_le (j : ℕ) (hj : j ≤ 6) {z : ℝ} (hz : 0 ≤ z) :
    |akP j z| ≤ 40320 * (1 + z) ^ j := by
  have h1' : (1 : ℝ) ≤ 1 + z := by linarith
  have hsum :
      |∑ i ∈ Finset.range (j + 1), akC j i * z ^ i| ≤ 40320 * (1 + z) ^ j := by
    calc |∑ i ∈ Finset.range (j + 1), akC j i * z ^ i|
        ≤ ∑ i ∈ Finset.range (j + 1), |akC j i * z ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), |akC j i| * (1 + z) ^ j := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          have h2 : |z| ^ i ≤ (1 + z) ^ i := by
            refine pow_le_pow_left₀ (abs_nonneg z) ?_ i
            rw [abs_of_nonneg hz]; linarith
          have h3 : (1 + z) ^ i ≤ (1 + z) ^ j := pow_le_pow_right₀ h1' (by omega)
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (le_trans h2 h3) (abs_nonneg _)
      _ = (∑ i ∈ Finset.range (j + 1), |akC j i|) * (1 + z) ^ j := by rw [Finset.sum_mul]
      _ ≤ 40320 * (1 + z) ^ j :=
          mul_le_mul_of_nonneg_right (akC_sum_le j hj) (by positivity)
  rwa [akP]

/-- The derivative of the `j`-th closed form; the recursion
`P_{j+1} = z(1+z) P_j' + (2 - (j+1)z) P_j` for the numerators. -/
lemma deriv_akRatio (j : ℕ) (hj : j ≤ 5) {z : ℝ} (hz : z ≠ -1) :
    deriv (fun w : ℝ => w ^ 2 * akP j w / (1 + w) ^ (j + 3)) z
      = z * akP (j + 1) z / (1 + z) ^ (j + 4) := by
  have h1 : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have hp : (1 + z) ^ (j + 3) ≠ 0 := pow_ne_zero _ h1
  have hp2 : ((1 + z) ^ (j + 3)) ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hnum : HasDerivAt (fun w : ℝ => w ^ 2 * akP j w)
      (2 * z * akP j z + z ^ 2 * akPd j z) z := by
    have h := (hasDerivAt_pow 2 z).mul (hasDerivAt_akP j z)
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w; simp
    · ring
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (j + 3))
      (((j + 3 : ℕ) : ℝ) * (1 + z) ^ (j + 3 - 1)) z :=
    Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_one_add_pow (j + 3) z
  have hq : HasDerivAt (fun w : ℝ => w ^ 2 * akP j w / (1 + w) ^ (j + 3))
      (z * akP (j + 1) z / (1 + z) ^ (j + 4)) z := by
    refine (hnum.fun_div hden hp).congr_deriv ?_
    interval_cases j <;>
      · simp only [akP, akPd, akC, Finset.sum_range_succ]
        norm_num
        field_simp [h1, hp, hp2]
        ring
  exact hq.deriv

/-- The exact closed form of the `j`-th radial jet, `j ≤ 6`:
`D_z^j f(z,θ) = z² · P_j(z) / (1+z)^{j+3}` for `z ≠ -1`. -/
lemma akJetP (j : ℕ) : j ≤ 6 → ∀ {z : ℝ}, z ≠ -1 → ∀ (θ : ℝ),
    Work.Spaces.DzIter j akf z θ = z ^ 2 * akP j z / (1 + z) ^ (j + 3) := by
  induction j with
  | zero =>
      intro _ z _ θ
      have h0 : akP 0 z = 2 := by norm_num [akP, akC, Finset.sum_range_succ]
      rw [h0]
      simp only [Work.Spaces.DzIter_zero, akf]
      norm_num
      ring
  | succ j ih =>
      intro hj z hz θ
      have hj' : j ≤ 5 := by omega
      have hfun : (fun w : ℝ => Work.Spaces.DzIter j akf w θ) =ᶠ[𝓝 z]
          (fun w : ℝ => w ^ 2 * akP j w / (1 + w) ^ (j + 3)) := by
        filter_upwards [(isOpen_ne (x := (-1 : ℝ))).mem_nhds hz] with w hw
        exact ih (by omega) hw θ
      have hstep : Work.Spaces.DzIter (j + 1) akf z θ
          = z * deriv (fun w : ℝ => w ^ 2 * akP j w / (1 + w) ^ (j + 3)) z := by
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
        rw [Filter.EventuallyEq.deriv_eq hfun]
      rw [hstep, deriv_akRatio j hj' hz, show (j + 1) + 3 = j + 4 from by omega]
      ring

/-- The weighted form of the exact jet: `D_z^j f(z,θ) · w z = P_j(z)/(1+z)^{j+1}` for
`z > 0` (via `z ≠ 0`), `j ≤ 6`. -/
lemma akJetP_mul_w (j : ℕ) (hj : j ≤ 6) {z : ℝ} (hz : z ≠ 0) (hz1 : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter j akf z θ * Work.Spaces.w z = akP j z / (1 + z) ^ (j + 1) := by
  have h1 : (1 + z) ≠ 0 := by intro h; exact hz1 (by linarith)
  have hpow : (1 + z) ^ (j + 3) = (1 + z) ^ (j + 1) * (1 + z) ^ 2 := by
    rw [show j + 3 = (j + 1) + 2 from by omega, pow_add]
  rw [akJetP j hj hz1 θ, Work.Spaces.w, hpow]
  field_simp

theorem akRho_jet_bound6 : ∃ R : ℝ, 0 ≤ R ∧ ∀ (j : ℕ), j ≤ 6 → ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
  refine ⟨40320 ^ 2, by norm_num, fun j hj z hz θ => ?_⟩
  have hz0 : 0 ≤ z := hz
  rcases eq_or_lt_of_le hz0 with h | h
  · -- `z = 0`: the weight `w` vanishes, so the left-hand side is `0 ≤ R`.
    subst h
    have hw : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    rw [hw, mul_zero]
    simp
  · have hz1 : z ≠ -1 := by linarith
    have hzne : z ≠ 0 := ne_of_gt h
    have hpos : (0 : ℝ) < 1 + z := by linarith
    have hw : Work.Spaces.DzIter j akf z θ * Work.Spaces.w z
        = akP j z / (1 + z) ^ (j + 1) := akJetP_mul_w j hj hzne hz1 θ
    rw [show Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
          = Work.Spaces.DzIter j akf z θ from rfl, hw]
    have hb : |akP j z| ≤ 40320 * (1 + z) ^ j := akP_abs_le j hj hz0
    have hden : (0 : ℝ) < (1 + z) ^ (j + 1) := by positivity
    have hkey : |akP j z / (1 + z) ^ (j + 1)| ≤ 40320 / (1 + z) := by
      rw [abs_div, abs_of_pos hden]
      rw [div_le_div_iff₀ hden hpos]
      calc |akP j z| * (1 + z) ≤ (40320 * (1 + z) ^ j) * (1 + z) :=
            mul_le_mul_of_nonneg_right hb hpos.le
        _ = 40320 * (1 + z) ^ (j + 1) := by rw [mul_assoc, ← pow_succ]
    calc (akP j z / (1 + z) ^ (j + 1)) ^ 2
        = |akP j z / (1 + z) ^ (j + 1)| ^ 2 := (sq_abs _).symm
      _ ≤ (40320 / (1 + z)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hkey 2
      _ = 40320 ^ 2 / (1 + z) ^ 2 := by rw [div_pow]

end Work.FTS.StrongPersist.AK6
