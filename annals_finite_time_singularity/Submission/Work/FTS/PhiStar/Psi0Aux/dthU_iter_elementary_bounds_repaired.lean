import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elementary `D_θ`-bounds for the model functions `sin 2θ`, `sin²θ`, `cos²θ`, `cos 2θ`
## (repaired copy of `dthU_iter_elementary_bounds`)

This module carries the *corrected* form of the lemma requested as
`Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds`; the requested path itself is left
untouched (its statement — see "STATEMENT REPAIR" below — is not well-typed, so it cannot be
proved as filed).  Consumers should `import
Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired` and use
`Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired`.  In particular, the
extraction performed by `Psi0_exists.lean` becomes

    obtain ⟨b, hb0, hb1, hb2, hb3, hb4⟩ :=
      Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
    exact ⟨b, hb0, hb2, hb3, hb4⟩            -- : ∃ b, ElemClass b

`Work.Spaces.dthU φ θ = sin (2θ) · φ'(θ)`; here we bound the iterates `dthU^[i]`
of the four model functions on `Iθ = [0, π/2]` by multiples of the same function
(respectively by a constant).

Route.  Writing `x = cos²θ ∈ [0,1]`:

* `dthU^[i] (sin 2·) θ = sin 2θ · P_i(cos²θ)` where `P_i` is the explicit polynomial
  `P_0 = 1`, `P_{i+1} = 2(2X-1)P_i - 4X(1-X)P_i'` (`dthUiterPW`, `dthUiter_sin2_iter`);
* `dthU^[i] (sin²) θ = cos²θ · sin²θ · R_{i-1}(cos²θ)` for `i ≥ 1`, where `R_1 = 4`,
  `R_{i+1} = -4·(X(1-X)R_i)'` (`dthUiterPR`, `dthUiter_sin_sq_iter`);
* the `cos²`- and `cos 2θ`-cases are obtained from `cos² = 1 - sin²` and
  `cos 2θ = 1 - 2 sin²θ` by linearity of the iterates and `dthU 1 = 0`
  (`dthUiter_cos_sq_iter`, `dthUiter_cos_two_iter`).

Since `sin²θ = 1 - x`, every pointwise bound reduces to the elementary estimate
`|Σ_k c_k x^k| ≤ Σ_k |c_k|` for `x ∈ [0,1]` (`dthUiter_abs_sum_pow_le`), so the constants
are the `ℓ¹`-norms of the explicit coefficient lists (`norm_num`); all of them are far
below the universal `1095801216` used in the statement.

STATEMENT REPAIR (documented for the requester).  The second and third conjunct of the
statement *as originally filed* at
`Submission/Work/FTS/PhiStar/Psi0Aux/dthU_iter_elementary_bounds` read

    |dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ| ≤ b i * Real.sin t ^ 2   -- ← `t` !
    |dthU^[i] (fun t : ℝ => Real.cos t ^ 2) θ| ≤ b i * Real.cos t ^ 2   -- ← `t` !

with the *unbound* identifier `t` on the right-hand side.  With `autoImplicit = false`
(as set in `lakefile.toml` for this library) elaboration of that text fails with
`Unknown identifier t` at exactly those two places, so the file did not elaborate at all
(it was not a well-formed proposition).  Under `autoImplicit = true` it would mean a
spurious universally quantified `∀ t`, which is *false* (take `t = 0`: the right-hand side
vanishes while the left-hand side is `|sin θ ^ 2| ≠ 0` for `θ = π/2`).

The intended statement is unambiguous: the first conjunct correctly uses `θ`, and
`Work.FTS.PhiStar.ElemClass` of `Psi0Classes.lean` — which is exactly what
`Psi0_exists.lean` extracts from this theorem (the pattern
`⟨b, hb0, hb2, hb3, hb4⟩`) — uses `θ` as well.  The statement proved below is the minimal
repair (`t` ↦ `θ` in those two conjuncts) and it is the statement consumed by `ElemClass`.

Note also that no other file declares anything under this module: the helper names
(`dthUiterPW`, `dthUiterPR`, …) are unique to this module.
-/

namespace Work.FTS.PhiStar.Psi0Aux

open Polynomial

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The two explicit polynomial recursions -/

/-- Coefficient of `x^k` in the polynomial `P_i` of the recursion
`P_0 = 1`, `P_{i+1} = 2(2x-1)P_i - 4x(1-x)P_i'` (for `i ≤ 7`). -/
def dthUiterPWcoef : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 1, 0 => -2
  | 1, 1 => 4
  | 2, 0 => 4
  | 2, 1 => -32
  | 2, 2 => 32
  | 3, 0 => -8
  | 3, 1 => 208
  | 3, 2 => -576
  | 3, 3 => 384
  | 4, 0 => 16
  | 4, 1 => -1280
  | 4, 2 => 7424
  | 4, 3 => -12288
  | 4, 4 => 6144
  | 5, 0 => -32
  | 5, 1 => 7744
  | 5, 2 => -84480
  | 5, 3 => 261120
  | 5, 4 => -307200
  | 5, 5 => 122880
  | 6, 0 => 64
  | 6, 1 => -46592
  | 6, 2 => 906752
  | 6, 3 => -4669440
  | 6, 4 => 9707520
  | 6, 5 => -8847360
  | 6, 6 => 2949120
  | 7, 0 => -128
  | 7, 1 => 279808
  | 7, 2 => -9440256
  | 7, 3 => 76253184
  | 7, 4 => -249446400
  | 7, 5 => 388792320
  | 7, 6 => -289013760
  | 7, 7 => 82575360
  | _, _ => 0

/-- Coefficient of `x^k` in the polynomial `R_i` of the recursion
`R_1 = 4`, `R_{i+1} = -4·(X(1-X)R_i)'` (for `i ≤ 6`). -/
def dthUiterPRcoef : ℕ → ℕ → ℝ
  | 0, 0 => 4
  | 1, 0 => -16
  | 1, 1 => 32
  | 2, 0 => 64
  | 2, 1 => -384
  | 2, 2 => 384
  | 3, 0 => -256
  | 3, 1 => 3584
  | 3, 2 => -9216
  | 3, 3 => 6144
  | 4, 0 => 1024
  | 4, 1 => -30720
  | 4, 2 => 153600
  | 4, 3 => -245760
  | 4, 4 => 122880
  | 5, 0 => -4096
  | 5, 1 => 253952
  | 5, 2 => -2211840
  | 5, 3 => 6389760
  | 5, 4 => -7372800
  | 5, 5 => 2949120
  | 6, 0 => 16384
  | 6, 1 => -2064384
  | 6, 2 => 29589504
  | 6, 3 => -137625600
  | 6, 4 => 275251200
  | 6, 5 => -247726080
  | 6, 6 => 82575360
  | _, _ => 0

/-- `P_i = Σ_{k ≤ i} dthUiterPWcoef i k · X^k`. -/
noncomputable def dthUiterPW (i : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (i+1))
    (fun k => Polynomial.C (dthUiterPWcoef i k) * Polynomial.X ^ k)

/-- `R_i = Σ_{k ≤ i} dthUiterPRcoef i k · X^k`. -/
noncomputable def dthUiterPR (i : ℕ) : Polynomial ℝ :=
  Finset.sum (Finset.range (i+1))
    (fun k => Polynomial.C (dthUiterPRcoef i k) * Polynomial.X ^ k)

/-! ## Evaluation and recursion lemmas -/

lemma dthUiterPW_eval (i : ℕ) (x : ℝ) :
    (dthUiterPW i).eval x
      = Finset.sum (Finset.range (i+1)) (fun k => dthUiterPWcoef i k * x ^ k) := by
  rw [dthUiterPW, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

lemma dthUiterPW_deriv_eval (i : ℕ) (x : ℝ) :
    ((dthUiterPW i).derivative).eval x
      = Finset.sum (Finset.range (i+1)) (fun k => dthUiterPWcoef i k * k * x ^ (k-1)) := by
  rw [dthUiterPW, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

lemma dthUiterPR_eval (i : ℕ) (x : ℝ) :
    (dthUiterPR i).eval x
      = Finset.sum (Finset.range (i+1)) (fun k => dthUiterPRcoef i k * x ^ k) := by
  rw [dthUiterPR, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

lemma dthUiterPR_deriv_eval (i : ℕ) (x : ℝ) :
    ((dthUiterPR i).derivative).eval x
      = Finset.sum (Finset.range (i+1)) (fun k => dthUiterPRcoef i k * k * x ^ (k-1)) := by
  rw [dthUiterPR, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- The recursion `P_{i+1} = 2(2X-1)P_i - 4X(1-X)P_i'`, in evaluated form. -/
lemma dthUiterPW_rec (i : ℕ) (hi : i ≤ 6) (x : ℝ) :
    (dthUiterPW (i+1)).eval x
      = 2*(2*x-1)*(dthUiterPW i).eval x - 4*x*(1-x)*((dthUiterPW i).derivative).eval x := by
  rw [dthUiterPW_eval, dthUiterPW_eval, dthUiterPW_deriv_eval]
  interval_cases i <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, dthUiterPWcoef] <;> ring_nf

lemma dthUiter_H_deriv_eval (x : ℝ) :
    ((Polynomial.X - Polynomial.X ^ 2 : Polynomial ℝ).derivative).eval x = 1 - 2*x := by
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] <;> ring

lemma dthUiter_H_eval (x : ℝ) :
    ((Polynomial.X - Polynomial.X ^ 2 : Polynomial ℝ)).eval x = x - x^2 := by
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow] <;> ring

lemma dthUiter_Hmul_deriv_eval (i : ℕ) (x : ℝ) :
    (((Polynomial.X - Polynomial.X ^ 2) * dthUiterPR i).derivative).eval x
      = (1 - 2*x) * (dthUiterPR i).eval x + (x - x^2) * ((dthUiterPR i).derivative).eval x := by
  rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      dthUiter_H_deriv_eval, dthUiter_H_eval]

/-- The recursion `R_{i+1} = -4·(X(1-X)R_i)'`, in evaluated form
(`X - X²` evaluates to `x(1-x) = cos²θ · sin²θ`). -/
lemma dthUiterPR_rec (i : ℕ) (hi : i ≤ 5) (x : ℝ) :
    (dthUiterPR (i+1)).eval x
      = -4 * (((Polynomial.X - Polynomial.X ^ 2) * dthUiterPR i).derivative).eval x := by
  rw [dthUiterPR_eval, dthUiter_Hmul_deriv_eval, dthUiterPR_eval, dthUiterPR_deriv_eval]
  interval_cases i <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, dthUiterPRcoef] <;> ring_nf

/-! ## The elementary polynomial bound on `[0,1]` and the numeric constants -/

lemma dthUiter_abs_sum_pow_le (c : ℕ → ℝ) (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Finset.sum (Finset.range n) (fun k => c k * x ^ k)|
      ≤ Finset.sum (Finset.range n) (fun k => |c k|) := by
  calc |Finset.sum (Finset.range n) (fun k => c k * x ^ k)|
      ≤ Finset.sum (Finset.range n) (fun k => |c k * x ^ k|) := Finset.abs_sum_le_sum_abs _ _
    _ = Finset.sum (Finset.range n) (fun k => |c k| * x ^ k) := by
        apply Finset.sum_congr rfl; intro k hk
        rw [abs_mul, abs_pow, abs_of_nonneg hx0]
    _ ≤ Finset.sum (Finset.range n) (fun k => |c k|) := by
        apply Finset.sum_le_sum; intro k hk
        calc |c k| * x ^ k ≤ |c k| * 1 :=
              mul_le_mul_of_nonneg_left (pow_le_one₀ hx0 hx1) (abs_nonneg _)
          _ = |c k| := mul_one _

lemma dthUiterPWcoef_sum_le (i : ℕ) (hi : i ≤ 7) :
    Finset.sum (Finset.range (i+1)) (fun k => |dthUiterPWcoef i k|) ≤ 1095801216 := by
  interval_cases i <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, dthUiterPWcoef] <;> norm_num

lemma dthUiterPRcoef_sum_le (i : ℕ) (hi : i ≤ 6) :
    Finset.sum (Finset.range (i+1)) (fun k => |dthUiterPRcoef i k|) ≤ 1095801216 := by
  interval_cases i <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, dthUiterPRcoef] <;> norm_num

/-! ## The two one-step lemmas -/

/-- One step of the `sin 2θ`-recursion. -/
lemma dthUiter_sin2_step (i : ℕ) (hi : i ≤ 6) (θ : ℝ) :
    Work.Spaces.dthU (fun θ : ℝ => Real.sin (2*θ) * (dthUiterPW i).eval (Real.cos θ ^ 2)) θ
      = Real.sin (2*θ) * (dthUiterPW (i+1)).eval (Real.cos θ ^ 2) := by
  have h1 : HasDerivAt (fun θ : ℝ => Real.sin (2*θ)) (Real.cos (2*θ) * 2) θ := by
    have h2 : HasDerivAt (fun θ : ℝ => 2*θ) (2:ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    exact (Real.hasDerivAt_sin (2*θ)).comp θ h2
  have hx : HasDerivAt (fun θ : ℝ => Real.cos θ ^ 2) (-(Real.sin (2*θ))) θ := by
    have hc := (Real.hasDerivAt_cos θ).pow 2
    convert hc using 1
    rw [Real.sin_two_mul]; ring
  have hpoly : HasDerivAt (fun θ : ℝ => (dthUiterPW i).eval (Real.cos θ ^ 2))
      (((dthUiterPW i).derivative).eval (Real.cos θ^2) * (-(Real.sin (2*θ)))) θ := by
    convert (Polynomial.hasDerivAt (dthUiterPW i) (Real.cos θ^2)).comp θ hx using 1 <;> try rfl
  have hprod : HasDerivAt (fun θ : ℝ => Real.sin (2*θ) * (dthUiterPW i).eval (Real.cos θ^2))
      (Real.cos (2*θ) * 2 * (dthUiterPW i).eval (Real.cos θ^2)
        + Real.sin (2*θ)
          * (((dthUiterPW i).derivative).eval (Real.cos θ^2) * (-(Real.sin (2*θ))))) θ := by
    convert h1.mul hpoly using 1
  rw [Work.Spaces.dthU_apply, hprod.deriv]
  rw [dthUiterPW_rec i hi (Real.cos θ^2), Real.cos_two_mul]
  have hsin : Real.sin (2*θ)^2 = 4*Real.cos θ^2*(1-Real.cos θ^2) := by
    rw [Real.sin_sq, Real.cos_two_mul]; ring
  linear_combination (-(Real.sin (2*θ)) * ((dthUiterPW i).derivative).eval (Real.cos θ^2)) * hsin

/-- One step of the `sin²`-recursion, for a function of the shape
`θ ↦ c·(cos²θ · sin²θ · r(cos²θ))`. -/
lemma dthUiter_PR_step (i : ℕ) (hi : i ≤ 5) (c : ℝ) (θ : ℝ) :
    Work.Spaces.dthU
        (fun θ : ℝ => c * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR i).eval (Real.cos θ^2))) θ
      = c * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR (i+1)).eval (Real.cos θ^2)) := by
  have hfun : (fun θ : ℝ => c * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR i).eval (Real.cos θ^2)))
      = fun θ : ℝ =>
          c * (((Polynomial.X - Polynomial.X ^ 2) * dthUiterPR i).eval (Real.cos θ^2)) := by
    funext θ
    rw [Polynomial.eval_mul, dthUiter_H_eval]
    rw [Real.sin_sq]
    ring
  have hx : HasDerivAt (fun θ : ℝ => Real.cos θ ^ 2) (-(Real.sin (2*θ))) θ := by
    have hc := (Real.hasDerivAt_cos θ).pow 2
    convert hc using 1
    rw [Real.sin_two_mul]; ring
  have hG : HasDerivAt
      (fun θ : ℝ => ((Polynomial.X - Polynomial.X ^ 2) * dthUiterPR i).eval (Real.cos θ^2))
      (((((Polynomial.X - Polynomial.X ^ 2) * dthUiterPR i).derivative).eval (Real.cos θ^2))
        * (-(Real.sin (2*θ)))) θ := by
    convert (Polynomial.hasDerivAt ((Polynomial.X - Polynomial.X ^ 2) * dthUiterPR i)
      (Real.cos θ^2)).comp θ hx using 1 <;> try rfl
  have hc : HasDerivAt
      (fun θ : ℝ => c * (((Polynomial.X - Polynomial.X ^ 2) * dthUiterPR i).eval (Real.cos θ^2)))
      (c * (((((Polynomial.X - Polynomial.X ^ 2) * dthUiterPR i).derivative).eval (Real.cos θ^2))
        * (-(Real.sin (2*θ))))) θ :=
    hG.const_mul c
  rw [hfun, Work.Spaces.dthU_apply, hc.deriv, dthUiterPR_rec i hi (Real.cos θ^2)]
  have hsin : Real.sin (2*θ)^2 = 4*Real.cos θ^2*(1-Real.cos θ^2) := by
    rw [Real.sin_sq, Real.cos_two_mul]; ring
  have hsinθ : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
  rw [hsinθ]
  linear_combination
    (-c * ((((Polynomial.X - Polynomial.X ^ 2) * dthUiterPR i).derivative).eval (Real.cos θ^2)))
      * hsin

/-! ## The iterated identities -/

lemma dthUiter_sin2_iter : ∀ i, i ≤ 7 → ∀ θ : ℝ,
    Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin (2 * t)) θ
      = Real.sin (2*θ) * (dthUiterPW i).eval (Real.cos θ ^ 2) := by
  intro i
  induction i with
  | zero =>
      intro _ θ
      rw [Function.iterate_zero_apply, dthUiterPW_eval]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, dthUiterPWcoef] <;> ring
  | succ i ih =>
      intro hi θ
      have hi7 : i ≤ 7 := by omega
      rw [Function.iterate_succ_apply']
      have hfun : Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin (2 * t))
          = fun θ : ℝ => Real.sin (2*θ) * (dthUiterPW i).eval (Real.cos θ ^ 2) :=
        funext (fun θ => ih hi7 θ)
      rw [hfun, dthUiter_sin2_step i (by omega) θ]

lemma dthUiter_PR_iter (c : ℝ) (f : ℝ → ℝ)
    (hbase : ∀ θ : ℝ, Work.Spaces.dthU f θ
      = c * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR 0).eval (Real.cos θ^2))) :
    ∀ i, i ≤ 6 → ∀ θ : ℝ, Work.Spaces.dthU^[i+1] f θ
      = c * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR i).eval (Real.cos θ^2)) := by
  intro i
  induction i with
  | zero => intro _ θ; exact hbase θ
  | succ i ih =>
      intro hi θ
      have hi6 : i ≤ 6 := by omega
      rw [Function.iterate_succ_apply']
      have hfun : Work.Spaces.dthU^[i+1] f
          = fun θ : ℝ =>
              c * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR i).eval (Real.cos θ^2)) :=
        funext (fun θ => ih hi6 θ)
      rw [hfun, dthUiter_PR_step i (by omega) c θ]

lemma dthUiter_sin_sq_iter (i : ℕ) (hi : i ≤ 6) (θ : ℝ) :
    Work.Spaces.dthU^[i+1] (fun t : ℝ => Real.sin t ^ 2) θ
      = Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR i).eval (Real.cos θ^2) := by
  have hbase : ∀ θ : ℝ, Work.Spaces.dthU (fun t : ℝ => Real.sin t ^ 2) θ
      = 1 * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR 0).eval (Real.cos θ^2)) := by
    intro θ
    rw [Work.Spaces.dthU_apply, dthUiterPR_eval]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, dthUiterPRcoef]
    have hd : deriv (fun t : ℝ => Real.sin t ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
      simpa using ((Real.hasDerivAt_sin θ).pow 2).deriv
    rw [hd, Real.sin_two_mul]
    ring
  simpa using dthUiter_PR_iter 1 (fun t : ℝ => Real.sin t ^ 2) hbase i hi θ

lemma dthUiter_cos_sq_iter (i : ℕ) (hi : i ≤ 6) (θ : ℝ) :
    Work.Spaces.dthU^[i+1] (fun t : ℝ => Real.cos t ^ 2) θ
      = -(Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR i).eval (Real.cos θ^2)) := by
  have hbase : ∀ θ : ℝ, Work.Spaces.dthU (fun t : ℝ => Real.cos t ^ 2) θ
      = -1 * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR 0).eval (Real.cos θ^2)) := by
    intro θ
    rw [Work.Spaces.dthU_apply, dthUiterPR_eval]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, dthUiterPRcoef]
    have hd : deriv (fun t : ℝ => Real.cos t ^ 2) θ = -2 * Real.cos θ * Real.sin θ := by
      simpa using ((Real.hasDerivAt_cos θ).pow 2).deriv
    rw [hd, Real.sin_two_mul]
    ring
  simpa using dthUiter_PR_iter (-1) (fun t : ℝ => Real.cos t ^ 2) hbase i hi θ

lemma dthUiter_cos_two_iter (i : ℕ) (hi : i ≤ 6) (θ : ℝ) :
    Work.Spaces.dthU^[i+1] (fun t : ℝ => Real.cos (2*t)) θ
      = -2 * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR i).eval (Real.cos θ^2)) := by
  have hbase : ∀ θ : ℝ, Work.Spaces.dthU (fun t : ℝ => Real.cos (2*t)) θ
      = -2 * (Real.cos θ^2 * Real.sin θ^2 * (dthUiterPR 0).eval (Real.cos θ^2)) := by
    intro θ
    rw [Work.Spaces.dthU_apply, dthUiterPR_eval]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, dthUiterPRcoef]
    have hd : deriv (fun t : ℝ => Real.cos (2*t)) θ = -2 * Real.sin (2*θ) := by
      have h2 : HasDerivAt (fun t : ℝ => 2*t) (2:ℝ) θ := by
        simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
      have h3 : HasDerivAt (fun t : ℝ => Real.cos (2*t)) ((-(Real.sin (2*θ))) * 2) θ :=
        (Real.hasDerivAt_cos (2*θ)).comp θ h2
      rw [h3.deriv]; ring
    rw [hd, Real.sin_two_mul]
    ring
  exact dthUiter_PR_iter (-2) (fun t : ℝ => Real.cos (2*t)) hbase i hi θ

/-! ## The theorem -/

theorem dthU_iter_elementary_bounds_repaired : ∃ b : ℕ → ℝ, (∀ i, 0 ≤ b i) ∧
    (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin (2 * t)) θ|
      ≤ b i * Real.sin (2 * θ)) ∧
    (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ|
      ≤ b i * Real.sin θ ^ 2) ∧
    (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[i] (fun t : ℝ => Real.cos t ^ 2) θ|
      ≤ b i * Real.cos θ ^ 2) ∧
    (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[i] (fun t : ℝ => Real.cos (2 * t)) θ| ≤ b i) := by
  refine ⟨fun _ => 1095801216, fun i => by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i hi θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hsin2 : 0 ≤ Real.sin (2*θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
    rw [dthUiter_sin2_iter i hi θ, abs_mul, abs_of_nonneg hsin2]
    have hb : |(dthUiterPW i).eval (Real.cos θ^2)| ≤ 1095801216 := by
      rw [dthUiterPW_eval]
      exact le_trans (dthUiter_abs_sum_pow_le _ _ _ (sq_nonneg _) (Real.cos_sq_le_one θ))
        (dthUiterPWcoef_sum_le i hi)
    calc Real.sin (2*θ) * |(dthUiterPW i).eval (Real.cos θ^2)|
        ≤ Real.sin (2*θ) * 1095801216 := mul_le_mul_of_nonneg_left hb hsin2
      _ = 1095801216 * Real.sin (2*θ) := by ring
  · intro i hi θ hθ
    cases i with
    | zero =>
        show |Real.sin θ ^ 2| ≤ 1095801216 * Real.sin θ ^ 2
        rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
        nlinarith [sq_nonneg (Real.sin θ)]
    | succ j =>
        have hj : j ≤ 6 := by omega
        rw [dthUiter_sin_sq_iter j hj θ, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ)),
            abs_of_nonneg (sq_nonneg (Real.sin θ))]
        have hb : |(dthUiterPR j).eval (Real.cos θ^2)| ≤ 1095801216 := by
          rw [dthUiterPR_eval]
          exact le_trans (dthUiter_abs_sum_pow_le _ _ _ (sq_nonneg _) (Real.cos_sq_le_one θ))
            (dthUiterPRcoef_sum_le j hj)
        have h1 : Real.cos θ^2 ≤ 1 := Real.cos_sq_le_one θ
        have h2 : 0 ≤ Real.sin θ^2 := sq_nonneg _
        have h3 : 0 ≤ Real.cos θ^2 := sq_nonneg _
        calc Real.cos θ^2 * Real.sin θ^2 * |(dthUiterPR j).eval (Real.cos θ^2)|
            = Real.cos θ^2 * (Real.sin θ^2 * |(dthUiterPR j).eval (Real.cos θ^2)|) := by ring
          _ ≤ Real.cos θ^2 * (Real.sin θ^2 * 1095801216) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb h2) h3
          _ ≤ 1 * (Real.sin θ^2 * 1095801216) :=
              mul_le_mul_of_nonneg_right h1 (mul_nonneg h2 (by norm_num))
          _ = 1095801216 * Real.sin θ^2 := by ring
  · intro i hi θ hθ
    cases i with
    | zero =>
        show |Real.cos θ ^ 2| ≤ 1095801216 * Real.cos θ ^ 2
        rw [abs_of_nonneg (sq_nonneg (Real.cos θ))]
        nlinarith [sq_nonneg (Real.cos θ)]
    | succ j =>
        have hj : j ≤ 6 := by omega
        rw [dthUiter_cos_sq_iter j hj θ, abs_neg, abs_mul, abs_mul,
            abs_of_nonneg (sq_nonneg (Real.cos θ)), abs_of_nonneg (sq_nonneg (Real.sin θ))]
        have hb : |(dthUiterPR j).eval (Real.cos θ^2)| ≤ 1095801216 := by
          rw [dthUiterPR_eval]
          exact le_trans (dthUiter_abs_sum_pow_le _ _ _ (sq_nonneg _) (Real.cos_sq_le_one θ))
            (dthUiterPRcoef_sum_le j hj)
        have h1 : Real.sin θ^2 ≤ 1 := by rw [Real.sin_sq]; linarith [sq_nonneg (Real.cos θ)]
        have h2 : 0 ≤ Real.sin θ^2 := sq_nonneg _
        have h3 : 0 ≤ Real.cos θ^2 := sq_nonneg _
        calc Real.cos θ^2 * Real.sin θ^2 * |(dthUiterPR j).eval (Real.cos θ^2)|
            = Real.cos θ^2 * (Real.sin θ^2 * |(dthUiterPR j).eval (Real.cos θ^2)|) := by ring
          _ ≤ Real.cos θ^2 * (1 * 1095801216) :=
              mul_le_mul_of_nonneg_left (mul_le_mul h1 hb (abs_nonneg _) (by norm_num)) h3
          _ = 1095801216 * Real.cos θ^2 := by ring
  · intro i hi θ hθ
    cases i with
    | zero =>
        show |Real.cos (2*θ)| ≤ 1095801216
        rw [abs_le]
        constructor
        · have := Real.neg_one_le_cos (2*θ); linarith
        · have := Real.cos_le_one (2*θ); linarith
    | succ j =>
        have hj : j ≤ 6 := by omega
        rw [dthUiter_cos_two_iter j hj θ, abs_mul, abs_mul, abs_neg, abs_mul,
            abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
            abs_of_nonneg (sq_nonneg (Real.cos θ)), abs_of_nonneg (sq_nonneg (Real.sin θ))]
        have hb : |(dthUiterPR j).eval (Real.cos θ^2)| ≤ 1095801216 := by
          rw [dthUiterPR_eval]
          exact le_trans (dthUiter_abs_sum_pow_le _ _ _ (sq_nonneg _) (Real.cos_sq_le_one θ))
            (dthUiterPRcoef_sum_le j hj)
        have hx4 : Real.cos θ^2 * Real.sin θ^2 ≤ 1/4 := by
          nlinarith [sq_nonneg (Real.cos θ^2 - 1/2), Real.sin_sq θ]
        have hstep : Real.cos θ^2 * Real.sin θ^2 * |(dthUiterPR j).eval (Real.cos θ^2)|
            ≤ (1/4) * 1095801216 :=
          mul_le_mul hx4 hb (abs_nonneg _) (by norm_num)
        linarith [hstep]

end Work.FTS.PhiStar.Psi0Aux
