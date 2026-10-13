/-
# Radial algebra: the coefficient bounds and the Leibniz rule for `D_z = z ∂_z`

This module proves `Work.Coercivity.radial_algebra`, the elementary input to the
coercivity estimate of the Elgindi paper (*Finite-time singularity formation for
`C^{1,α}` solutions to the incompressible Euler equations on `ℝ³`*, Annals of Math.
**194** (3) 2021).  It has three independent parts.

1. For each fixed `k`, the `k`-th iterate `D_z^k (pcoef α)` of the coefficient
   `pcoef α z = 2z/(c(1+z)²)` is dominated by `M/z` after multiplication by the
   weight `w z = (1+z)²/z²`, uniformly in `z > 0`.

2. The same statement for `Wcoef α z = 2z²/(c(1+z)³)`, with `M/(1+z)`.

3. `D_z^j (R·S) = ∑_{k≤j} C(j,k) D_z^k R · D_z^{j-k} S` for `C^∞` functions on
   `(0,∞)` — the binomial (Leibniz) rule for the derivation `D_z = z ∂_z`.

The proof of (1) and (2) uses the change of variable `u = z/(1+z)`, under which
`D_z = u(1-u) ∂_u` and

  `pcoef α z = (2/c)·u(1-u)`,   `Wcoef α z = (2/c)·u²(1-u)`.

The operator `u(1-u)∂_u` maps `u^a(1-u) P(u)` to `u^a(1-u) P̃(u)` with `P̃` a
polynomial; one records the quotient polynomials `Qseq1`/`Qseq2` explicitly, so
that `D_z^k(pcoef α) = (2/c)·u(1-u)Qseq1 k(u)`.  Since `u ∈ (0,1)`, each quotient
polynomial is bounded on the unit interval by the sum of the absolute values of its
coefficients, which yields (1) and (2).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.DzRIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Polynomial
open MeasureTheory Set Filter

namespace Work.Coercivity
namespace CT

set_option autoImplicit false

/-! ## The change of variable `u = z/(1+z)` -/

/-- `u(z) = z/(1+z)`; in this coordinate `D_z = z ∂_z` becomes `u(1-u) ∂_u`. -/
def ufun : ℝ → ℝ := fun z => z / (1 + z)

/-- The operator `D_u = u(1-u) ∂_u`, the conjugate of `D_z` by `u = z/(1+z)`. -/
def Dufun (g : ℝ → ℝ) : ℝ → ℝ := fun v => v * (1 - v) * deriv g v

/-- A polynomial, viewed as a function. -/
def polyfun (p : ℝ[X]) : ℝ → ℝ := fun v => p.eval v

theorem ufun_pos {z : ℝ} (hz : 0 < z) : 0 < ufun z := by
  rw [ufun]; positivity

theorem ufun_lt_one {z : ℝ} (hz : 0 < z) : ufun z < 1 := by
  rw [ufun, div_lt_one (by linarith)]; linarith

theorem ufun_sq (z : ℝ) (hz : 1 + z ≠ 0) : ufun z * (1 - ufun z) = z / (1 + z) ^ 2 := by
  rw [ufun]; field_simp; ring

theorem one_sub_ufun (z : ℝ) (hz : 1 + z ≠ 0) : 1 - ufun z = 1 / (1 + z) := by
  rw [ufun]; field_simp; ring

theorem inv_ufun (z : ℝ) (hz : 0 < z) : 1 / ufun z = (1 + z) / z := by
  rw [ufun]; field_simp

theorem ufun_weight (z : ℝ) (hz : 0 < z) : 1 / (ufun z) ^ 2 = Spaces.w z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : 1 + z ≠ 0 := by linarith
  rw [ufun, w_eq]
  field_simp

theorem hasDerivAt_ufun (z : ℝ) (hz : 1 + z ≠ 0) : HasDerivAt ufun (1 / (1 + z) ^ 2) z := by
  have h1 : HasDerivAt (fun y : ℝ => y) 1 z := hasDerivAt_id z
  have h2 : HasDerivAt (fun y : ℝ => 1 + y) 1 z := by
    have h := (hasDerivAt_const (x := z) (1 : ℝ)).add (hasDerivAt_id z)
    convert h using 1
    · ext y; simp
    · simp
  have h := h1.div h2 (by simpa using hz)
  convert h using 1
  · ext y; simp [ufun]
  · field_simp; ring

theorem deriv_ufun (z : ℝ) (hz : 1 + z ≠ 0) : deriv ufun z = 1 / (1 + z) ^ 2 :=
  (hasDerivAt_ufun z hz).deriv

theorem differentiableAt_ufun (z : ℝ) (hz : 1 + z ≠ 0) : DifferentiableAt ℝ ufun z :=
  (hasDerivAt_ufun z hz).differentiableAt

/-! ## `D_z` in the `u` coordinate -/

theorem Dufun_polyfun (p : ℝ[X]) :
    Dufun (polyfun p) = polyfun (Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative p) := by
  funext v
  rw [Dufun]
  have h : HasDerivAt (polyfun p) ((Polynomial.derivative p).eval v) v := p.hasDerivAt v
  rw [h.deriv]
  simp only [polyfun, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X]

theorem differentiableAt_polyfun (p : ℝ[X]) (v : ℝ) : DifferentiableAt ℝ (polyfun p) v :=
  (p.hasDerivAt v).differentiableAt

/-- **The conjugation identity**: on `(0,∞)`, `D_z` applied to `g ∘ u` is `D_u g`
composed with `u`. -/
theorem DzR_comp (g : ℝ → ℝ) (z : ℝ) (hz : 1 + z ≠ 0)
    (hg : DifferentiableAt ℝ g (ufun z)) :
    DzR (fun z => g (ufun z)) z = Dufun g (ufun z) := by
  rw [DzR, Dufun]
  have hu : DifferentiableAt ℝ ufun z := differentiableAt_ufun z hz
  rw [show (fun z => g (ufun z)) = (g ∘ ufun) from rfl]
  rw [deriv_comp (x := z) (h := ufun) (h₂ := g) hg hu, deriv_ufun z hz]
  rw [ufun]
  field_simp
  ring

/-! ## The quotient polynomials `Qseq1`, `Qseq2` -/

/-- The quotient polynomials for `u(1-u)`: `D_u^k (u(1-u)) = u(1-u)·Qseq1 k(u)`. -/
def Qseq1 : ℕ → ℝ[X]
  | 0 => 1
  | (k + 1) => (1 - Polynomial.X) * Qseq1 k - Polynomial.X * Qseq1 k
      + Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (Qseq1 k)

/-- The quotient polynomials for `u²(1-u)`: `D_u^k (u²(1-u)) = u²(1-u)·Qseq2 k(u)`. -/
def Qseq2 : ℕ → ℝ[X]
  | 0 => 1
  | (k + 1) => 2 * (1 - Polynomial.X) * Qseq2 k - Polynomial.X * Qseq2 k
      + Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (Qseq2 k)

/-- `Rseq1 k(u) := u(1-u)·Qseq1 k(u) = D_u^k(u(1-u))`. -/
def Rseq1 (k : ℕ) : ℝ[X] := Polynomial.X * (1 - Polynomial.X) * Qseq1 k

/-- `Rseq2 k(u) := u²(1-u)·Qseq2 k(u) = D_u^k(u²(1-u))`. -/
def Rseq2 (k : ℕ) : ℝ[X] := Polynomial.X ^ 2 * (1 - Polynomial.X) * Qseq2 k

@[simp] theorem Qseq1_zero : Qseq1 0 = 1 := rfl
theorem Qseq1_succ (k : ℕ) : Qseq1 (k + 1) = (1 - Polynomial.X) * Qseq1 k
    - Polynomial.X * Qseq1 k
    + Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (Qseq1 k) := rfl

@[simp] theorem Qseq2_zero : Qseq2 0 = 1 := rfl
theorem Qseq2_succ (k : ℕ) : Qseq2 (k + 1) = 2 * (1 - Polynomial.X) * Qseq2 k
    - Polynomial.X * Qseq2 k
    + Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (Qseq2 k) := rfl

@[simp] theorem Rseq1_zero : Rseq1 0 = Polynomial.X * (1 - Polynomial.X) := by
  simp [Rseq1]

@[simp] theorem Rseq2_zero : Rseq2 0 = Polynomial.X ^ 2 * (1 - Polynomial.X) := by
  simp [Rseq2]

/-- The algebraic step for `u(1-u)`. -/
theorem Qstep1 (Q : ℝ[X]) :
    Polynomial.X * (1 - Polynomial.X)
        * Polynomial.derivative (Polynomial.X * (1 - Polynomial.X) * Q)
      = Polynomial.X * (1 - Polynomial.X)
        * ((1 - Polynomial.X) * Q - Polynomial.X * Q
            + Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative Q) := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X]
  ring

/-- The algebraic step for `u²(1-u)`. -/
theorem Qstep2 (Q : ℝ[X]) :
    Polynomial.X * (1 - Polynomial.X)
        * Polynomial.derivative (Polynomial.X ^ 2 * (1 - Polynomial.X) * Q)
      = Polynomial.X ^ 2 * (1 - Polynomial.X)
        * (2 * (1 - Polynomial.X) * Q - Polynomial.X * Q
            + Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative Q) := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.derivative_sub,
      Polynomial.derivative_one, Polynomial.derivative_X, Nat.cast_ofNat]
  rw [Polynomial.C_ofNat 2]
  ring

theorem Rseq1_succ (k : ℕ) :
    Rseq1 (k + 1) = Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (Rseq1 k) := by
  rw [Rseq1, Qseq1_succ, Rseq1]
  exact (Qstep1 (Qseq1 k)).symm

theorem Rseq2_succ (k : ℕ) :
    Rseq2 (k + 1) = Polynomial.X * (1 - Polynomial.X) * Polynomial.derivative (Rseq2 k) := by
  rw [Rseq2, Qseq2_succ, Rseq2]
  exact (Qstep2 (Qseq2 k)).symm

/-! ## Iterates of `D_u` on the two base polynomials -/

theorem Dufun_iterate1 (k : ℕ) :
    Dufun^[k] (polyfun (Rseq1 0)) = polyfun (Rseq1 k) := by
  induction k with
  | zero => rw [Function.iterate_zero_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, Dufun_polyfun, Rseq1_succ]

theorem Dufun_iterate2 (k : ℕ) :
    Dufun^[k] (polyfun (Rseq2 0)) = polyfun (Rseq2 k) := by
  induction k with
  | zero => rw [Function.iterate_zero_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, Dufun_polyfun, Rseq2_succ]

/-! ## The model identities `D_z^k ∘ u = (D_u)^k` -/

theorem DzRIter_model1 (k : ℕ) :
    Set.EqOn (DzRIter k (fun z => (Rseq1 0).eval (ufun z)))
      (fun z => (Rseq1 k).eval (ufun z)) (Set.Ioi 0) := by
  induction k with
  | zero => intro z hz; rfl
  | succ n ih =>
      intro z hz
      have hz1 : 1 + z ≠ 0 := by linarith [show (0 : ℝ) < z from hz]
      rw [DzRIter_succ, DzR]
      have hderiv : deriv (DzRIter n (fun z => (Rseq1 0).eval (ufun z))) z
          = deriv (fun w => (Rseq1 n).eval (ufun w)) z := (ih.deriv isOpen_Ioi) hz
      rw [hderiv]
      show DzR (fun w => polyfun (Rseq1 n) (ufun w)) z = (Rseq1 (n + 1)).eval (ufun z)
      rw [DzR_comp (polyfun (Rseq1 n)) z hz1 (differentiableAt_polyfun _ _)]
      rw [Dufun_polyfun, ← Rseq1_succ]
      rfl

theorem DzRIter_model2 (k : ℕ) :
    Set.EqOn (DzRIter k (fun z => (Rseq2 0).eval (ufun z)))
      (fun z => (Rseq2 k).eval (ufun z)) (Set.Ioi 0) := by
  induction k with
  | zero => intro z hz; rfl
  | succ n ih =>
      intro z hz
      have hz1 : 1 + z ≠ 0 := by linarith [show (0 : ℝ) < z from hz]
      rw [DzRIter_succ, DzR]
      have hderiv : deriv (DzRIter n (fun z => (Rseq2 0).eval (ufun z))) z
          = deriv (fun w => (Rseq2 n).eval (ufun w)) z := (ih.deriv isOpen_Ioi) hz
      rw [hderiv]
      show DzR (fun w => polyfun (Rseq2 n) (ufun w)) z = (Rseq2 (n + 1)).eval (ufun z)
      rw [DzR_comp (polyfun (Rseq2 n)) z hz1 (differentiableAt_polyfun _ _)]
      rw [Dufun_polyfun, ← Rseq2_succ]
      rfl

/-! ## The coefficient functions `pcoef` and `Wcoef` -/

theorem pcoef_eq_model (α : ℝ) (hc : Spaces.c α ≠ 0) (k : ℕ) :
    Set.EqOn (DzRIter k (pcoef α))
      (fun z => (2 / Spaces.c α) * (Rseq1 k).eval (ufun z)) (Set.Ioi 0) := by
  induction k with
  | zero =>
      intro z hz
      have hz1 : 1 + z ≠ 0 := by linarith [show (0 : ℝ) < z from hz]
      show pcoef α z = (2 / Spaces.c α) * (Rseq1 0).eval (ufun z)
      rw [pcoef, Rseq1_zero]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
        ufun]
      field_simp
      ring
  | succ n ih =>
      intro z hz
      have hz1 : 1 + z ≠ 0 := by linarith [show (0 : ℝ) < z from hz]
      rw [DzRIter_succ, DzR]
      have hderiv : deriv (DzRIter n (pcoef α)) z
          = deriv (fun w => (2 / Spaces.c α) * (Rseq1 n).eval (ufun w)) z :=
        (ih.deriv isOpen_Ioi) hz
      rw [hderiv]
      have hdiff : DifferentiableAt ℝ (fun w => (Rseq1 n).eval (ufun w)) z :=
        (differentiableAt_polyfun (Rseq1 n) (ufun z)).comp z (differentiableAt_ufun z hz1)
      rw [deriv_const_mul (2 / Spaces.c α) hdiff]
      have h2 : z * deriv (fun w => (Rseq1 n).eval (ufun w)) z = (Rseq1 (n + 1)).eval (ufun z) := by
        show DzR (fun w => polyfun (Rseq1 n) (ufun w)) z = (Rseq1 (n + 1)).eval (ufun z)
        rw [DzR_comp (polyfun (Rseq1 n)) z hz1 (differentiableAt_polyfun _ _)]
        rw [Dufun_polyfun, ← Rseq1_succ]
        rfl
      rw [← mul_assoc, mul_comm z (2 / Spaces.c α), mul_assoc, h2]

theorem Wcoef_eq_model (α : ℝ) (hc : Spaces.c α ≠ 0) (k : ℕ) :
    Set.EqOn (DzRIter k (Wcoef α))
      (fun z => (2 / Spaces.c α) * (Rseq2 k).eval (ufun z)) (Set.Ioi 0) := by
  induction k with
  | zero =>
      intro z hz
      have hz1 : 1 + z ≠ 0 := by linarith [show (0 : ℝ) < z from hz]
      show Wcoef α z = (2 / Spaces.c α) * (Rseq2 0).eval (ufun z)
      rw [Wcoef, Rseq2_zero]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
        Polynomial.eval_pow, ufun]
      field_simp
      ring
  | succ n ih =>
      intro z hz
      have hz1 : 1 + z ≠ 0 := by linarith [show (0 : ℝ) < z from hz]
      rw [DzRIter_succ, DzR]
      have hderiv : deriv (DzRIter n (Wcoef α)) z
          = deriv (fun w => (2 / Spaces.c α) * (Rseq2 n).eval (ufun w)) z :=
        (ih.deriv isOpen_Ioi) hz
      rw [hderiv]
      have hdiff : DifferentiableAt ℝ (fun w => (Rseq2 n).eval (ufun w)) z :=
        (differentiableAt_polyfun (Rseq2 n) (ufun z)).comp z (differentiableAt_ufun z hz1)
      rw [deriv_const_mul (2 / Spaces.c α) hdiff]
      have h2 : z * deriv (fun w => (Rseq2 n).eval (ufun w)) z = (Rseq2 (n + 1)).eval (ufun z) := by
        show DzR (fun w => polyfun (Rseq2 n) (ufun w)) z = (Rseq2 (n + 1)).eval (ufun z)
        rw [DzR_comp (polyfun (Rseq2 n)) z hz1 (differentiableAt_polyfun _ _)]
        rw [Dufun_polyfun, ← Rseq2_succ]
        rfl
      rw [← mul_assoc, mul_comm z (2 / Spaces.c α), mul_assoc, h2]

/-! ## Bounding a polynomial on the unit interval -/

theorem poly_eval_unit_bound (p : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, u ∈ Set.Icc 0 1 → |p.eval u| ≤ C := by
  refine ⟨1 + ∑ i ∈ p.support, |p.coeff i|, by positivity, ?_⟩
  intro u hu
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ 1 := hu.2
  have hsum : p.eval u = ∑ i ∈ p.support, p.coeff i * u ^ i := by
    rw [Polynomial.eval_eq_sum]; rfl
  calc |p.eval u| = |∑ i ∈ p.support, p.coeff i * u ^ i| := by rw [hsum]
    _ ≤ ∑ i ∈ p.support, |p.coeff i * u ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ p.support, |p.coeff i| * |u ^ i| := by simp [abs_mul]
    _ ≤ ∑ i ∈ p.support, |p.coeff i| * 1 := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have h1 : |u ^ i| ≤ 1 := by
          rw [abs_of_nonneg (pow_nonneg hu0 i)]
          exact pow_le_one₀ hu0 hu1
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = ∑ i ∈ p.support, |p.coeff i| := by simp
    _ ≤ 1 + ∑ i ∈ p.support, |p.coeff i| := le_add_of_nonneg_left (by norm_num)

/-! ## The weighted bounds on `Rseq1`, `Rseq2` -/

theorem Rseq1_weight_bound (k : ℕ) (C : ℝ)
    (hCC : ∀ u : ℝ, u ∈ Set.Icc 0 1 → |(Qseq1 k).eval u| ≤ C) (z : ℝ) (hz : 0 < z) :
    |(Rseq1 k).eval (ufun z)| * Spaces.w z ≤ C / z := by
  have hz1 : 1 + z ≠ 0 := by linarith
  have hupos : 0 < ufun z := ufun_pos hz
  have hu1 : ufun z < 1 := ufun_lt_one hz
  have hu : ufun z ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hupos, le_of_lt hu1⟩
  have hQ := hCC (ufun z) hu
  have hR : (Rseq1 k).eval (ufun z)
      = ufun z * (1 - ufun z) * (Qseq1 k).eval (ufun z) := by
    rw [Rseq1]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  rw [hR, ← ufun_weight z hz, abs_mul, abs_mul, abs_of_pos hupos,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ufun z)]
  have hval : ufun z * (1 - ufun z) * |(Qseq1 k).eval (ufun z)| * (1 / (ufun z) ^ 2)
      = ((1 - ufun z) / ufun z) * |(Qseq1 k).eval (ufun z)| := by
    field_simp
  rw [hval]
  have hrec : (1 - ufun z) / ufun z = 1 / z := by
    rw [ufun]
    field_simp
    ring
  rw [hrec]
  have hzpos : (0 : ℝ) < 1 / z := by positivity
  calc (1 / z) * |(Qseq1 k).eval (ufun z)| ≤ (1 / z) * C :=
        mul_le_mul_of_nonneg_left hQ (le_of_lt hzpos)
    _ = C / z := by ring

theorem Rseq2_weight_bound (k : ℕ) (C : ℝ)
    (hCC : ∀ u : ℝ, u ∈ Set.Icc 0 1 → |(Qseq2 k).eval u| ≤ C) (z : ℝ) (hz : 0 < z) :
    |(Rseq2 k).eval (ufun z)| * Spaces.w z ≤ C / (1 + z) := by
  have hz1 : 1 + z ≠ 0 := by linarith
  have hupos : 0 < ufun z := ufun_pos hz
  have hu1 : ufun z < 1 := ufun_lt_one hz
  have hu : ufun z ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hupos, le_of_lt hu1⟩
  have hQ := hCC (ufun z) hu
  have hR : (Rseq2 k).eval (ufun z)
      = ufun z ^ 2 * (1 - ufun z) * (Qseq2 k).eval (ufun z) := by
    rw [Rseq2]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_pow]
  rw [hR, ← ufun_weight z hz, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ufun z ^ 2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ufun z)]
  have hval : ufun z ^ 2 * (1 - ufun z) * |(Qseq2 k).eval (ufun z)| * (1 / (ufun z) ^ 2)
      = (1 - ufun z) * |(Qseq2 k).eval (ufun z)| := by
    field_simp
  rw [hval, one_sub_ufun z hz1]
  have hzpos : (0 : ℝ) < 1 / (1 + z) := by positivity
  calc (1 / (1 + z)) * |(Qseq2 k).eval (ufun z)| ≤ (1 / (1 + z)) * C :=
        mul_le_mul_of_nonneg_left hQ (le_of_lt hzpos)
    _ = C / (1 + z) := by ring

/-! ## The two per-`k` estimates -/

theorem pcoef_k_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℝ, 0 < z →
      |DzRIter k (pcoef α) z| * Spaces.w z ≤ M / z := by
  have hc : Spaces.c α ≠ 0 := c_ne_zero hα hα1
  have hcp : 0 < Spaces.c α := c_pos hα hα1
  obtain ⟨C, hCp, hC⟩ := poly_eval_unit_bound (Qseq1 k)
  refine ⟨(2 / Spaces.c α) * C, by positivity, ?_⟩
  intro z hz
  rw [(pcoef_eq_model α hc k) hz, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / Spaces.c α)]
  have h1 : |(Rseq1 k).eval (ufun z)| * Spaces.w z ≤ C / z :=
    Rseq1_weight_bound k C hC z hz
  calc (2 / Spaces.c α) * |(Rseq1 k).eval (ufun z)| * Spaces.w z
      = (2 / Spaces.c α) * (|(Rseq1 k).eval (ufun z)| * Spaces.w z) := by ring
    _ ≤ (2 / Spaces.c α) * (C / z) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (by positivity : (0 : ℝ) < 2 / Spaces.c α))
    _ = (2 / Spaces.c α) * C / z := by ring

theorem Wcoef_k_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℝ, 0 < z →
      |DzRIter k (Wcoef α) z| * Spaces.w z ≤ M / (1 + z) := by
  have hc : Spaces.c α ≠ 0 := c_ne_zero hα hα1
  have hcp : 0 < Spaces.c α := c_pos hα hα1
  obtain ⟨C, hCp, hC⟩ := poly_eval_unit_bound (Qseq2 k)
  refine ⟨(2 / Spaces.c α) * C, by positivity, ?_⟩
  intro z hz
  rw [(Wcoef_eq_model α hc k) hz, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / Spaces.c α)]
  have h1 : |(Rseq2 k).eval (ufun z)| * Spaces.w z ≤ C / (1 + z) :=
    Rseq2_weight_bound k C hC z hz
  calc (2 / Spaces.c α) * |(Rseq2 k).eval (ufun z)| * Spaces.w z
      = (2 / Spaces.c α) * (|(Rseq2 k).eval (ufun z)| * Spaces.w z) := by ring
    _ ≤ (2 / Spaces.c α) * (C / (1 + z)) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (by positivity : (0 : ℝ) < 2 / Spaces.c α))
    _ = (2 / Spaces.c α) * C / (1 + z) := by ring

end CT

/-! ## The target theorem -/

open CT in
theorem radial_algebra (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) :
    (∃ M : ℝ, 0 < M ∧ ∀ k ≤ j, ∀ z : ℝ, 0 < z →
        |Work.Coercivity.CT.DzRIter k (Work.Coercivity.CT.pcoef α) z| * Work.Spaces.w z ≤ M / z)
    ∧ (∃ M : ℝ, 0 < M ∧ ∀ k ≤ j, ∀ z : ℝ, 0 < z →
        |Work.Coercivity.CT.DzRIter k (Work.Coercivity.CT.Wcoef α) z| * Work.Spaces.w z ≤ M / (1 + z))
    ∧ (∀ (R S : ℝ → ℝ), ContDiffOn ℝ ⊤ R (Set.Ioi 0) → ContDiffOn ℝ ⊤ S (Set.Ioi 0) →
        ∀ z : ℝ, 0 < z → Work.Coercivity.CT.DzRIter j (fun t => R t * S t) z
          = ∑ k ∈ Finset.range (j + 1),
              ((j.choose k : ℝ) * Work.Coercivity.CT.DzRIter k R z
                * Work.Coercivity.CT.DzRIter (j - k) S z)) := by
  have hM1 : ∀ k : ℕ, 0 < Classical.choose (CT.pcoef_k_bound α hα hα1 k) ∧
      ∀ z : ℝ, 0 < z →
        |Work.Coercivity.CT.DzRIter k (Work.Coercivity.CT.pcoef α) z| * Work.Spaces.w z
          ≤ Classical.choose (CT.pcoef_k_bound α hα hα1 k) / z :=
    fun k => Classical.choose_spec (CT.pcoef_k_bound α hα hα1 k)
  have hM2 : ∀ k : ℕ, 0 < Classical.choose (CT.Wcoef_k_bound α hα hα1 k) ∧
      ∀ z : ℝ, 0 < z →
        |Work.Coercivity.CT.DzRIter k (Work.Coercivity.CT.Wcoef α) z| * Work.Spaces.w z
          ≤ Classical.choose (CT.Wcoef_k_bound α hα hα1 k) / (1 + z) :=
    fun k => Classical.choose_spec (CT.Wcoef_k_bound α hα hα1 k)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨∑ k ∈ Finset.range (j + 1),
        (Classical.choose (CT.pcoef_k_bound α hα hα1 k) + 1), ?_, ?_⟩
    · refine Finset.sum_pos (fun k _ => by linarith [(hM1 k).1])
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
    · intro k hk z hz
      have hmem : k ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
      have hle : Classical.choose (CT.pcoef_k_bound α hα hα1 k) + 1
          ≤ ∑ k ∈ Finset.range (j + 1),
              (Classical.choose (CT.pcoef_k_bound α hα hα1 k) + 1) :=
        Finset.single_le_sum (f := fun k => Classical.choose (CT.pcoef_k_bound α hα hα1 k) + 1)
          (fun k _ => by linarith [(hM1 k).1]) hmem
      calc |Work.Coercivity.CT.DzRIter k (Work.Coercivity.CT.pcoef α) z| * Work.Spaces.w z
          ≤ Classical.choose (CT.pcoef_k_bound α hα hα1 k) / z := (hM1 k).2 z hz
        _ ≤ (Classical.choose (CT.pcoef_k_bound α hα hα1 k) + 1) / z := by
            rw [div_le_div_iff_of_pos_right hz]; linarith [(hM1 k).1]
        _ ≤ (∑ k ∈ Finset.range (j + 1),
              (Classical.choose (CT.pcoef_k_bound α hα hα1 k) + 1)) / z := by
            rw [div_le_div_iff_of_pos_right hz]; exact hle
  · refine ⟨∑ k ∈ Finset.range (j + 1),
        (Classical.choose (CT.Wcoef_k_bound α hα hα1 k) + 1), ?_, ?_⟩
    · refine Finset.sum_pos (fun k _ => by linarith [(hM2 k).1])
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
    · intro k hk z hz
      have hz1 : (0 : ℝ) < 1 + z := by linarith
      have hmem : k ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
      have hle : Classical.choose (CT.Wcoef_k_bound α hα hα1 k) + 1
          ≤ ∑ k ∈ Finset.range (j + 1),
              (Classical.choose (CT.Wcoef_k_bound α hα hα1 k) + 1) :=
        Finset.single_le_sum (f := fun k => Classical.choose (CT.Wcoef_k_bound α hα hα1 k) + 1)
          (fun k _ => by linarith [(hM2 k).1]) hmem
      calc |Work.Coercivity.CT.DzRIter k (Work.Coercivity.CT.Wcoef α) z| * Work.Spaces.w z
          ≤ Classical.choose (CT.Wcoef_k_bound α hα hα1 k) / (1 + z) := (hM2 k).2 z hz
        _ ≤ (Classical.choose (CT.Wcoef_k_bound α hα hα1 k) + 1) / (1 + z) := by
            rw [div_le_div_iff_of_pos_right hz1]; linarith [(hM2 k).1]
        _ ≤ (∑ k ∈ Finset.range (j + 1),
              (Classical.choose (CT.Wcoef_k_bound α hα hα1 k) + 1)) / (1 + z) := by
            rw [div_le_div_iff_of_pos_right hz1]; exact hle
  · intro R S hR hS z hz
    exact DzRIter_mul j R S hR hS z hz

end Work.Coercivity
