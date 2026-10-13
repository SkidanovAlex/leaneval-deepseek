/-
# `Work.FTS.PhiStar.Series.eFamSupDefs` — the radial energy machinery for `eFam`

The angular Dirichlet basis of `Lzero` is `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`
(`Work.FTS.PhiStar.Gegenbauer.eFam`).  Put `q = gC (2m+1) = C^{(3/2)}_{2m+1}`,
`N = Npsi m = (2m+2)(2m+3)` (so `n(n+3) = N - 2` for `n = 2m+1`) and

  `u = ug m = (1 - x^2)·q`,   `E = ene m = (u')^2 + N·(1 - x^2)·q^2`.

Two elementary facts drive the `O(m)` sup bound `|eFam m θ| ≤ C(m+1)`:

* (`ug_ode`) the function `u` satisfies the *regular* Sturm–Liouville equation
  `u'' + N/(1-x^2)·u = 0` on `(-1,1)` — this is the Gegenbauer equation
  `(1-x^2)q'' - 4xq' + n(n+3)q = 0` rewritten;
* (`deriv_ene`) the associated "energy" `E` has `E'(x) = 2xN·q(x)^2 ≥ 0` for `x ≥ 0`,
  while `u(1) = 0` and `u'(1) = -2q(1) = -N`, so `E(x) ≤ E(1) = N^2` for `0 ≤ x ≤ 1`
  (`ene_le`).  Hence `u(x)^2 ≤ N(1-x^2)` (`ug_bound`), which is exactly the bound
  `|eFam m θ| ≤ √N` after substituting `x = sin θ`.

Note that `ene` is written *without denominators* — that is the whole point: it makes sense
at `x = 1`, where the quotient form `(u')^2 + N u^2/(1-x^2)` does not, and
`ene m 1 = (u'(1))^2 = N^2` is then a direct evaluation.

**Remaining piece** (`ug_bound`): `(ug m x)^2 ≤ Npsi m * (1 - x^2)` for `x ∈ [0,1]`,
obtained from `ene_le` and `ene_eq`, dividing by `N` at the end.  All the derivative
bookkeeping needed for it (`deriv_ug`, `deriv2_ug`, `ug_ode`, `ene_eq`, `ene_one`) is proved
below.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

open Work.FTS.PhiStar.Gegenbauer (gC gC_rec gC_ode contDiff_gC)

/-- `Npsi m = (2m+2)(2m+3)`: the constant of the radial Sturm–Liouville equation of `eFam m`.
It equals `(n+1)(n+2) = n(n+3) + 2` for `n = 2m+1`. -/
def Npsi (m : ℕ) : ℝ := (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)

/-- `ug m x = (1 - x^2)·C^{(3/2)}_{2m+1}(x)`. -/
def ug (m : ℕ) : ℝ → ℝ := fun x => (1 - x ^ 2) * gC (2 * m + 1) x

/-- The radial energy, written with products to keep the derivative bookkeeping free of
function powers: `ene m x = (u')^2 + N·(1-x^2)·q^2`.  Away from `x = ±1` it equals
`(u')^2 + N u^2/(1-x^2)`, and at `x = 1` it evaluates to `N^2`. -/
def ene (m : ℕ) : ℝ → ℝ :=
  fun x => deriv (ug m) x * deriv (ug m) x
    + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x * gC (2 * m + 1) x))

/-! ## Elementary facts about `Npsi` -/

lemma Npsi_pos (m : ℕ) : 0 < Npsi m := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [Npsi]
  positivity

lemma Npsi_eq (m : ℕ) :
    Npsi m = (((2 * m + 1 : ℕ) : ℝ) + 1) * (((2 * m + 1 : ℕ) : ℝ) + 2) := by
  rw [Npsi]
  push_cast
  ring

lemma Npsi_eq_two (m : ℕ) :
    Npsi m = (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) + 2 := by
  rw [Npsi_eq]
  ring

lemma Npsi_ge_one (m : ℕ) : 1 ≤ Npsi m := by
  rw [Npsi]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-- The value of `C^{(3/2)}_k` at `1`: `C^{(3/2)}_k(1) = (k+1)(k+2)/2`. -/
lemma gC_one (k : ℕ) : gC k 1 = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    norm_num
  | one =>
    rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
    norm_num
  | more n ih1 ih2 =>
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have h : ((n : ℝ) + 2) * gC (n + 2) 1
        = ((n : ℝ) + 2) * (((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2) / 2) := by
      rw [gC_rec n 1, ih1, ih2]
      push_cast
      ring
    have hh := mul_left_cancel₀ h2 h
    push_cast
    exact hh

/-- `√b` bounds `|a|` as soon as `a^2 ≤ b`. -/
lemma abs_le_sqrt_of_sq_le {a b : ℝ} (h : a ^ 2 ≤ b) : |a| ≤ Real.sqrt b := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-! ## Differentiability of `gC` -/

lemma differentiable_gC (k : ℕ) : Differentiable ℝ (gC k) :=
  (contDiff_gC k).differentiable (by norm_num)

lemma differentiable_deriv_gC (k : ℕ) : Differentiable ℝ (deriv (gC k)) :=
  ((contDiff_gC k).deriv' (n := 2)).differentiable (by norm_num)

lemma hasDerivAt_one_sub_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (-(2 * x)) x := by
  simpa using (hasDerivAt_pow 2 x).const_sub (1 : ℝ)

/-! ## The first and second derivatives of `ug` -/

lemma deriv_ug (m : ℕ) (x : ℝ) :
    deriv (ug m) x
      = -2 * x * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
  have h3 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y)
      ((-(2 * x)) * gC (2 * m + 1) x
        + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x) x :=
    (hasDerivAt_one_sub_sq x).mul
      ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h4 : deriv (ug m) x
      = (-(2 * x)) * gC (2 * m + 1) x
        + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
    rw [show ug m = fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y from rfl]
    exact h3.deriv
  rw [h4]
  ring

lemma differentiable_deriv_ug (m : ℕ) : Differentiable ℝ (deriv (ug m)) := by
  rw [funext (deriv_ug m)]
  have h1 : Differentiable ℝ (fun y : ℝ => (-2 : ℝ) * y) :=
    (differentiable_const (-2 : ℝ)).mul differentiable_id
  have h2 : Differentiable ℝ (fun y : ℝ => (1 : ℝ) - y ^ 2) :=
    (differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)
  exact (h1.mul (differentiable_gC (2 * m + 1))).add
    (h2.mul (differentiable_deriv_gC (2 * m + 1)))

lemma deriv2_ug (m : ℕ) (x : ℝ) :
    deriv (deriv (ug m)) x
      = -2 * gC (2 * m + 1) x - 4 * x * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x := by
  have hfun : deriv (ug m)
      = fun y : ℝ => -2 * y * gC (2 * m + 1) y
        + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y := funext (deriv_ug m)
  rw [hfun]
  have h1 : HasDerivAt (fun y : ℝ => -2 * y * gC (2 * m + 1) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x) x := by
    have hlin : HasDerivAt (fun y : ℝ => (-2 : ℝ) * y) (-2) x := by
      simpa using (hasDerivAt_id x).const_mul (-2 : ℝ)
    exact hlin.mul ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h2 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((-(2 * x)) * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x) x :=
    (hasDerivAt_one_sub_sq x).mul
      ((differentiable_deriv_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h3 : HasDerivAt (fun y : ℝ => -2 * y * gC (2 * m + 1) y
        + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x
        + ((-(2 * x)) * deriv (gC (2 * m + 1)) x
          + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x)) x :=
    h1.add h2
  rw [h3.deriv]
  ring

/-- **The Sturm–Liouville equation for `u = (1-x^2)q`**: `u'' + N/(1-x^2)·u = 0` for
`x^2 ≠ 1`. -/
lemma ug_ode (m : ℕ) {x : ℝ} (hx : x ^ 2 ≠ 1) :
    deriv (deriv (ug m)) x + (Npsi m / (1 - x ^ 2)) * ug m x = 0 := by
  have hode := (gC_ode (2 * m + 1)).2 x
  have hkey : (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x
      = 4 * x * deriv (gC (2 * m + 1)) x
        - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) * gC (2 * m + 1) x := by
    linarith [hode]
  have hne : 1 - x ^ 2 ≠ 0 := by
    intro h
    exact hx (by linarith)
  have hq : (Npsi m / (1 - x ^ 2)) * ((1 - x ^ 2) * gC (2 * m + 1) x)
      = Npsi m * gC (2 * m + 1) x := by
    field_simp
  rw [deriv2_ug m x, hkey,
    show ug m x = (1 - x ^ 2) * gC (2 * m + 1) x from rfl, hq, Npsi_eq_two m]
  ring

/-- `u'(1) = -2 q(1) = -N`. -/
lemma deriv_ug_one (m : ℕ) : deriv (ug m) 1 = -Npsi m := by
  rw [deriv_ug m 1, gC_one (2 * m + 1), Npsi_eq m]
  push_cast
  ring

/-- `E(1) = (u'(1))^2 = N^2`. -/
lemma ene_one (m : ℕ) : ene m 1 = Npsi m * Npsi m := by
  show deriv (ug m) 1 * deriv (ug m) 1
      + Npsi m * ((1 - (1 : ℝ) ^ 2) * (gC (2 * m + 1) 1 * gC (2 * m + 1) 1))
      = Npsi m * Npsi m
  rw [deriv_ug_one m]
  ring

/-- `E` in quotient form, away from `x = ±1`: `E = (u')^2 + N u^2/(1-x^2)`. -/
lemma ene_eq (m : ℕ) {x : ℝ} (hx : 1 - x ^ 2 ≠ 0) :
    ene m x = deriv (ug m) x * deriv (ug m) x
      + (Npsi m / (1 - x ^ 2)) * (ug m x * ug m x) := by
  show deriv (ug m) x * deriv (ug m) x
      + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x * gC (2 * m + 1) x))
      = deriv (ug m) x * deriv (ug m) x
        + (Npsi m / (1 - x ^ 2)) * (ug m x * ug m x)
  rw [show ug m x = (1 - x ^ 2) * gC (2 * m + 1) x from rfl]
  field_simp

/-- **`E'(x) = 2xN·q(x)^2 ≥ 0` for `x ≥ 0`**: the energy is non-decreasing. -/
lemma deriv_ene (m : ℕ) (x : ℝ) :
    deriv (ene m) x = 2 * x * Npsi m * (gC (2 * m + 1) x * gC (2 * m + 1) x) := by
  have hdu : HasDerivAt (deriv (ug m)) (deriv (deriv (ug m)) x) x :=
    (differentiable_deriv_ug m).differentiableAt.hasDerivAt
  have hg : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) x) x :=
    (differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => deriv (ug m) y * deriv (ug m) y)
      (2 * deriv (ug m) x * deriv (deriv (ug m)) x) x := by
    have h := hdu.mul hdu
    convert h using 1
    ring
  have h2 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * (gC (2 * m + 1) y * gC (2 * m + 1) y))
      ((-(2 * x)) * (gC (2 * m + 1) x * gC (2 * m + 1) x)
        + (1 - x ^ 2) * (2 * gC (2 * m + 1) x * deriv (gC (2 * m + 1)) x)) x := by
    have hg2 : HasDerivAt (fun y : ℝ => gC (2 * m + 1) y * gC (2 * m + 1) y)
        (2 * gC (2 * m + 1) x * deriv (gC (2 * m + 1)) x) x := by
      have h := hg.mul hg
      convert h using 1
      ring
    have h := (hasDerivAt_one_sub_sq x).mul hg2
    convert h using 1
  have h3 : HasDerivAt (ene m)
      (2 * deriv (ug m) x * deriv (deriv (ug m)) x
        + Npsi m * ((-(2 * x)) * (gC (2 * m + 1) x * gC (2 * m + 1) x)
          + (1 - x ^ 2) * (2 * gC (2 * m + 1) x * deriv (gC (2 * m + 1)) x))) x := by
    have h := h1.add (h2.const_mul (Npsi m))
    convert h using 1
    rfl
  rw [h3.deriv, deriv2_ug m x, deriv_ug m x]
  have hode := (gC_ode (2 * m + 1)).2 x
  have hkey : (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x
      = 4 * x * deriv (gC (2 * m + 1)) x
        - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) * gC (2 * m + 1) x := by
    linarith [hode]
  rw [hkey, Npsi_eq_two m]
  ring

lemma differentiable_ene (m : ℕ) : Differentiable ℝ (ene m) := by
  have h1 : Differentiable ℝ
      (fun x : ℝ => deriv (ug m) x * deriv (ug m) x) :=
    (differentiable_deriv_ug m).mul (differentiable_deriv_ug m)
  have h2 : Differentiable ℝ (fun y : ℝ => (1 : ℝ) - y ^ 2) :=
    (differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)
  have h3 : Differentiable ℝ
      (fun x : ℝ => gC (2 * m + 1) x * gC (2 * m + 1) x) :=
    (differentiable_gC (2 * m + 1)).mul (differentiable_gC (2 * m + 1))
  have h4 : Differentiable ℝ
      (fun x : ℝ => Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x * gC (2 * m + 1) x))) :=
    (differentiable_const (Npsi m)).mul (h2.mul h3)
  exact h1.add h4

lemma continuous_ene (m : ℕ) : Continuous (ene m) := (differentiable_ene m).continuous

/-- **The energy bound**: `E(x) ≤ E(1) = N^2` for `0 ≤ x ≤ 1`. -/
lemma ene_le (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : ene m x ≤ Npsi m * Npsi m := by
  have hmono : MonotoneOn (ene m) (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuous_ene m).continuousOn
      (differentiable_ene m).differentiableOn ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    rw [deriv_ene m y]
    exact mul_nonneg (mul_nonneg (by linarith) (le_of_lt (Npsi_pos m))) (mul_self_nonneg _)
  have h1 : ene m x ≤ ene m 1 := hmono hx ⟨by norm_num, le_rfl⟩ hx.2
  rwa [ene_one m] at h1

end Work.FTS.PhiStar.Series
