/-
# `Work.FTS.PhiStar.Series.Deleg.psiAngBounds`

Angular bounds for the Gegenbauer family `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`.

**Route.**  Let `q = gC (2m+1) = C^{(3/2)}_{2m+1}` and `N = (2m+2)(2m+3)` (so `n(n+3) = N-2`
for `n = 2m+1`).  Two elementary facts drive everything:

* (`ug_ode`) the function `u(x) = (1-x^2)·q(x)` satisfies the *regular* Sturm–Liouville
  equation `u'' + N/(1-x^2)·u = 0` on `(-1,1)` — this is the Gegenbauer equation
  `(1-x^2)q'' - 4xq' + n(n+3)q = 0` rewritten;
* (`deriv_ene`) the associated "energy" `E(x) = u'(x)^2 + N/(1-x^2)·u(x)^2` has
  `E'(x) = 2xN·q(x)^2 ≥ 0` for `x ≥ 0`, while `u(1) = 0` and `u'(1) = -2q(1) = -N`, so
  `E(x) ≤ E(1) = N^2` for `0 ≤ x ≤ 1`.  Hence `u(x)^2 ≤ N(1-x^2)` and `u'(x)^2 ≤ N^2` on
  `[0,1]`.

Finally `eFam m θ = u(sin θ)/cos θ` and the chain rule gives the bounds for the first and
second derivatives of `eFam` and of `tan θ · eFam`.
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open Filter

namespace Work.FTS.PhiStar.Series.Deleg

open Work.FTS.PhiStar.Gegenbauer
  (eFam gC gC_rec gC_ode contDiff_gC deriv_cos_comp_sin deriv2_cos_comp_sin
    deriv_tan_cos_comp_sin)

/-- `N m = (2m+2)(2m+3)`: the constant of the statement. -/
def Npsi (m : ℕ) : ℝ := (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)

/-- `u_m(x) = (1-x^2)·C^{(3/2)}_{2m+1}(x)`. -/
def ug (m : ℕ) : ℝ → ℝ := fun x => (1 - x ^ 2) * gC (2 * m + 1) x

/-- The energy `(u')^2 + (N/(1-x^2))u^2`, written as a sum of two functions. -/
def ene (m : ℕ) : ℝ → ℝ :=
  (fun x => (deriv (ug m) x) ^ 2) +
    (fun x => Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x) ^ 2))

/-! ## Elementary facts about `Npsi` -/

lemma Npsi_pos (m : ℕ) : 0 < Npsi m := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  simp only [Npsi]
  positivity

lemma Npsi_eq (m : ℕ) :
    Npsi m = (((2 * m + 1 : ℕ) : ℝ) + 1) * (((2 * m + 1 : ℕ) : ℝ) + 2) := by
  simp only [Npsi]; push_cast; ring

lemma Npsi_eq_two (m : ℕ) :
    Npsi m = (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) + 2 := by
  rw [Npsi_eq]; ring

lemma Npsi_ge_one (m : ℕ) : 1 ≤ Npsi m := by
  have h0 : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Npsi_eq m]
  nlinarith

/-- The value of `C^{(3/2)}_k` at `1`. -/
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

/-- A triangle-type inequality used below. -/
lemma abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · have h1 := neg_abs_le a; have h2 := le_abs_self b; linarith
  · have h1 := le_abs_self a; have h2 := neg_abs_le b; linarith

/-! ## Differentiability of `gC` and of `ug` -/

lemma differentiable_gC (k : ℕ) : Differentiable ℝ (gC k) :=
  (contDiff_gC k).differentiable (by norm_num)

lemma differentiable_deriv_gC (k : ℕ) : Differentiable ℝ (deriv (gC k)) :=
  ((contDiff_gC k).deriv' (n := 2)).differentiable (by norm_num)

lemma hasDerivAt_one_sub_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (0 - 2 * x) x := by
  have h0 := (hasDerivAt_pow 2 x).const_sub (1 : ℝ)
  convert h0 using 1
  simp

/-! ## The first and second derivatives of `ug` -/

lemma deriv_ug (m : ℕ) (x : ℝ) :
    deriv (ug m) x
      = -2 * x * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
  have h1 := hasDerivAt_one_sub_sq x
  have h2 : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) x) x :=
    (differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y)
      ((0 - 2 * x) * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x) x :=
    h1.mul h2
  have h4 : deriv (ug m) x
      = (0 - 2 * x) * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
    rw [show ug m = fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y from rfl]
    exact h3.deriv
  rw [h4]; ring

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
      = fun y : ℝ => -2 * y * gC (2 * m + 1) y + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y :=
    funext (deriv_ug m)
  rw [hfun]
  have h1 : HasDerivAt (fun y : ℝ => -2 * y * gC (2 * m + 1) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x) x := by
    have hlin : HasDerivAt (fun y : ℝ => (-2 : ℝ) * y) (-2) x := hasDerivAt_const_mul (-2)
    exact hlin.mul ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h2 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((0 - 2 * x) * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x) x :=
    (hasDerivAt_one_sub_sq x).mul
      ((differentiable_deriv_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h3 : HasDerivAt
      (fun y : ℝ => -2 * y * gC (2 * m + 1) y + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x
        + ((0 - 2 * x) * deriv (gC (2 * m + 1)) x
          + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x)) x :=
    h1.add h2
  rw [h3.deriv]
  ring

/-- **The Sturm–Liouville equation for `u`**: `u'' + N/(1-x^2)·u = 0` for `x ≠ ±1`. -/
lemma ug_ode (m : ℕ) {x : ℝ} (hx : x ^ 2 ≠ 1) :
    deriv (deriv (ug m)) x + (Npsi m / (1 - x ^ 2)) * ug m x = 0 := by
  have hode := (gC_ode (2 * m + 1)).2 x
  have hkey : (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x
      = 4 * x * deriv (gC (2 * m + 1)) x
        - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) * gC (2 * m + 1) x := by
    linarith [hode]
  have hN : (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) + 2 = Npsi m :=
    (Npsi_eq_two m).symm
  have hne : 1 - x ^ 2 ≠ 0 := by
    intro h; exact hx (by linarith)
  rw [deriv2_ug m x, hkey]
  rw [show ug m x = (1 - x ^ 2) * gC (2 * m + 1) x from rfl, ← hN]
  field_simp
  try ring

/-! ## The energy -/

lemma differentiable_ene (m : ℕ) : Differentiable ℝ (ene m) := by
  have h1 : Differentiable ℝ (fun x : ℝ => (deriv (ug m) x) ^ 2) :=
    (differentiable_deriv_ug m).pow 2
  have h2 : Differentiable ℝ (fun y : ℝ => (1 : ℝ) - y ^ 2) :=
    (differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)
  have h3 : Differentiable ℝ (fun x : ℝ => (gC (2 * m + 1) x) ^ 2) :=
    (differentiable_gC (2 * m + 1)).pow 2
  have h4 : Differentiable ℝ
      (fun x : ℝ => Npsi m * (((1 : ℝ) - x ^ 2) * (gC (2 * m + 1) x) ^ 2)) :=
    (differentiable_const (Npsi m)).mul (h2.mul h3)
  exact h1.add h4

lemma continuous_ene (m : ℕ) : Continuous (ene m) := (differentiable_ene m).continuous

lemma ene_eq (m : ℕ) {x : ℝ} (hx : 1 - x ^ 2 ≠ 0) :
    ene m x = (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 := by
  show (deriv (ug m) x) ^ 2 + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x) ^ 2)
      = (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
  rw [show ug m x = (1 - x ^ 2) * gC (2 * m + 1) x from rfl]
  field_simp
  try ring

/-- `E'(x) = 2xN·q(x)^2`. -/
lemma deriv_ene (m : ℕ) (x : ℝ) :
    deriv (ene m) x = 2 * x * Npsi m * (gC (2 * m + 1) x) ^ 2 := by
  have hdu : HasDerivAt (deriv (ug m)) (deriv (deriv (ug m)) x) x :=
    (differentiable_deriv_ug m).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => (deriv (ug m) y) ^ 2)
      ((2 : ℝ) * (deriv (ug m) x) ^ (2 - 1) * deriv (deriv (ug m)) x) x := hdu.pow 2
  have h2 : HasDerivAt (fun y : ℝ => ((1 : ℝ) - y ^ 2) * (gC (2 * m + 1) y) ^ 2)
      ((0 - 2 * x) * (gC (2 * m + 1) x) ^ 2
        + (1 - x ^ 2) * ((2 : ℝ) * (gC (2 * m + 1) x) ^ (2 - 1)
            * deriv (gC (2 * m + 1)) x)) x := by
    have hg : HasDerivAt (fun y : ℝ => (gC (2 * m + 1) y) ^ 2)
        ((2 : ℝ) * (gC (2 * m + 1) x) ^ (2 - 1) * deriv (gC (2 * m + 1)) x) x :=
      ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt).pow 2
    exact (hasDerivAt_one_sub_sq x).mul hg
  have h3 : HasDerivAt
      (fun y : ℝ => Npsi m * (((1 : ℝ) - y ^ 2) * (gC (2 * m + 1) y) ^ 2))
      (Npsi m * ((0 - 2 * x) * (gC (2 * m + 1) x) ^ 2
        + (1 - x ^ 2) * ((2 : ℝ) * (gC (2 * m + 1) x) ^ (2 - 1)
            * deriv (gC (2 * m + 1)) x))) x :=
    h2.const_mul (Npsi m)
  have h4 : HasDerivAt (ene m)
      ((2 : ℝ) * (deriv (ug m) x) ^ (2 - 1) * deriv (deriv (ug m)) x
        + Npsi m * ((0 - 2 * x) * (gC (2 * m + 1) x) ^ 2
          + (1 - x ^ 2) * ((2 : ℝ) * (gC (2 * m + 1) x) ^ (2 - 1)
              * deriv (gC (2 * m + 1)) x))) x :=
    h1.add h3
  rw [h4.deriv]
  rw [deriv2_ug m x]
  have hode := (gC_ode (2 * m + 1)).2 x
  have hkey : (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x
      = 4 * x * deriv (gC (2 * m + 1)) x
        - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) * gC (2 * m + 1) x := by
    linarith [hode]
  have hN : (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) + 2 = Npsi m :=
    (Npsi_eq_two m).symm
  rw [hkey, ← hN, deriv_ug m x]
  ring

/-- `u'(1) = -N`. -/
lemma deriv_ug_one (m : ℕ) : deriv (ug m) 1 = -Npsi m := by
  rw [deriv_ug m 1]
  have hg := gC_one (2 * m + 1)
  have hN := Npsi_eq m
  rw [hg, hN]
  ring_nf

/-- `E(1) = N^2`. -/
lemma ene_one (m : ℕ) : ene m 1 = Npsi m ^ 2 := by
  show (deriv (ug m) 1) ^ 2 + Npsi m * ((1 - (1 : ℝ) ^ 2) * (gC (2 * m + 1) 1) ^ 2)
      = Npsi m ^ 2
  rw [deriv_ug_one m]
  ring_nf

/-- `E ≤ E(1) = N^2` on `[0,1]`. -/
lemma ene_le (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : ene m x ≤ Npsi m ^ 2 := by
  have hmono : MonotoneOn (ene m) (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuous_ene m).continuousOn
      (differentiable_ene m).differentiableOn ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    rw [deriv_ene m y]
    exact mul_nonneg (mul_nonneg (by linarith) (le_of_lt (Npsi_pos m))) (sq_nonneg _)
  have h1 : ene m x ≤ ene m 1 := hmono hx ⟨by norm_num, le_rfl⟩ hx.2
  rwa [ene_one m] at h1

/-! ## The two bounds on `u` -/

lemma ug_bound (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (ug m x) ^ 2 ≤ Npsi m * (1 - x ^ 2) := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hc : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hE : (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
        ≤ Npsi m ^ 2 := by
      rw [← ene_eq m hne]; exact ene_le m hx
    have h3 : (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 ≤ Npsi m ^ 2 := by
      linarith [hE, sq_nonneg (deriv (ug m) x)]
    rw [div_mul_eq_mul_div₀, div_le_iff₀ hc] at h3
    have h4 : Npsi m ^ 2 * (1 - x ^ 2) / Npsi m = Npsi m * (1 - x ^ 2) := by
      rw [sq, mul_assoc, mul_div_cancel_left₀ _ (ne_of_gt (Npsi_pos m))]
    have h5 : (ug m x) ^ 2 ≤ Npsi m ^ 2 * (1 - x ^ 2) / Npsi m :=
      (le_div_iff₀ (Npsi_pos m)).mpr (by linarith [h3])
    rwa [h4] at h5
  · subst heq
    rw [show ug m 1 = 0 from by simp [ug]]
    simp

lemma du_bound (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (deriv (ug m) x) ^ 2 ≤ Npsi m ^ 2 := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hc : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hE : (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
        ≤ Npsi m ^ 2 := by
      rw [← ene_eq m hne]; exact ene_le m hx
    have h3 : 0 ≤ (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 :=
      mul_nonneg (div_nonneg (le_of_lt (Npsi_pos m)) (le_of_lt hc)) (sq_nonneg _)
    linarith [hE, h3]
  · subst heq
    rw [deriv_ug_one m, neg_sq]

/-! ## Arithmetic helpers -/

lemma arith2 {c r : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) (h2 : 1 ≤ r) :
    r ^ 2 + 3 * r / c ≤ 100 * r ^ 2 / c ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hr : 0 < r := by linarith
  have hL : (r ^ 2 + 3 * r / c) * c ^ 2 = r ^ 2 * c ^ 2 + 3 * r * c := by
    field_simp
    try ring
  have hc2le : c ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 2
    simpa using this
  have hA : r ^ 2 * c ^ 2 ≤ r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hc2le (sq_nonneg r)
    simpa using this
  have hB : 3 * r * c ≤ 99 * r ^ 2 := by
    have hstep : 3 * r * c ≤ 3 * r := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 * r)
      simpa using this
    have hstep2 : 3 * r ≤ 99 * r ^ 2 := by
      have h3 : (3 : ℝ) ≤ 99 * r := by linarith
      have := mul_le_mul_of_nonneg_right h3 (le_of_lt hr)
      calc 3 * r = 3 * r := rfl
        _ ≤ (99 * r) * r := this
        _ = 99 * r ^ 2 := by ring
    linarith
  rw [le_div_iff₀ hc2, hL]
  linarith [hA, hB, sq_nonneg r]

lemma arith3 {c r : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) (h2 : 1 ≤ r) :
    r ^ 2 / c + 2 * r / c ^ 2 + (r ^ 2 - 1) * r ≤ 1000 * r ^ 2 * r / c ^ 4 := by
  have hc4 : 0 < c ^ 4 := by positivity
  have hr : 0 < r := by linarith
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hL : (r ^ 2 / c + 2 * r / c ^ 2 + (r ^ 2 - 1) * r) * c ^ 4
      = r ^ 2 * c ^ 3 + 2 * r * c ^ 2 + (r ^ 2 - 1) * r * c ^ 4 := by
    field_simp
    try ring
  have hc2le : c ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 2
    simpa using this
  have hc3le : c ^ 3 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 3
    simpa using this
  have hc4le : c ^ 4 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 4
    simpa using this
  have hrn1 : 0 ≤ r ^ 2 - 1 := by nlinarith
  have hA : r ^ 2 * c ^ 3 ≤ r ^ 2 * r := by
    have h1' : r ^ 2 * c ^ 3 ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left hc3le hr2
    have h2' : r ^ 2 * 1 ≤ r ^ 2 * r := by
      have := mul_le_mul_of_nonneg_left h2 hr2
      simpa using this
    linarith
  have hB : 2 * r * c ^ 2 ≤ 2 * (r ^ 2 * r) := by
    have h1' : 2 * r * c ^ 2 ≤ 2 * r := by
      have := mul_le_mul_of_nonneg_left hc2le (by positivity : (0 : ℝ) ≤ 2 * r)
      simpa using this
    have h2' : 2 * r ≤ 2 * (r ^ 2 * r) := by
      have h3 : (1 : ℝ) ≤ r ^ 2 := by nlinarith
      have h4 : r ≤ r ^ 2 * r := by
        have := mul_le_mul_of_nonneg_right h3 (le_of_lt hr)
        simpa using this
      exact mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hC : (r ^ 2 - 1) * r * c ^ 4 ≤ r ^ 2 * r := by
    have h1' : (r ^ 2 - 1) * r * c ^ 4 ≤ (r ^ 2 - 1) * r * 1 :=
      mul_le_mul_of_nonneg_left hc4le (mul_nonneg hrn1 (le_of_lt hr))
    have h2' : (r ^ 2 - 1) * r * 1 ≤ r ^ 2 * r := by
      have h3 : r ^ 2 - 1 ≤ r ^ 2 := by linarith
      have := mul_le_mul_of_nonneg_right h3 (le_of_lt hr)
      simpa using this
    linarith
  have hr2r : 0 ≤ r ^ 2 * r := by positivity
  rw [le_div_iff₀ hc4, hL]
  linarith [hA, hB, hC, hr2r]

lemma arith4 {c r : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) (h2 : 1 ≤ r) :
    r + r ^ 2 / c + 2 * r / c ^ 2 ≤ 1000 * r ^ 2 / c ^ 3 := by
  have hc3 : 0 < c ^ 3 := by positivity
  have hr : 0 < r := by linarith
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hL : (r + r ^ 2 / c + 2 * r / c ^ 2) * c ^ 3
      = r * c ^ 3 + r ^ 2 * c ^ 2 + 2 * r * c := by
    field_simp
    try ring
  have hc2le : c ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 2
    simpa using this
  have hc3le : c ^ 3 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 3
    simpa using this
  have hrle : r ≤ r ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (le_of_lt hr)
    simpa [sq] using this
  have hA : r * c ^ 3 ≤ r ^ 2 := by
    have h1' : r * c ^ 3 ≤ r * 1 := mul_le_mul_of_nonneg_left hc3le (le_of_lt hr)
    linarith [h1', hrle]
  have hB : r ^ 2 * c ^ 2 ≤ r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hc2le hr2
    simpa using this
  have hC : 2 * r * c ≤ 2 * r ^ 2 := by
    have h1' : 2 * r * c ≤ 2 * r := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * r)
      simpa using this
    linarith [h1', hrle]
  rw [le_div_iff₀ hc3, hL]
  linarith [hA, hB, hC, hr2]

/-! ## Reduction to `θ`-bounds -/

lemma sin_cos_facts {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.cos θ ∧ Real.cos θ ≤ 1 ∧ 0 ≤ Real.sin θ ∧ Real.sin θ ≤ 1 ∧
      1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
  obtain ⟨h0, h1⟩ := hθ
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt h0, by linarith [Real.pi_pos]⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsq : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ; linarith
  exact ⟨hc, hc1, hs0, hs1, hsq⟩

lemma gC_div_ug (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    gC (2 * m + 1) (Real.sin θ) = ug m (Real.sin θ) / (Real.cos θ) ^ 2 := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  show gC (2 * m + 1) (Real.sin θ)
    = (1 - (Real.sin θ) ^ 2) * gC (2 * m + 1) (Real.sin θ) / (Real.cos θ) ^ 2
  rw [hsq]
  field_simp

lemma ug_sin_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |ug m (Real.sin θ)| ≤ Real.sqrt (Npsi m) * Real.cos θ := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have hb := ug_bound m ⟨hs0, hs1⟩
  rw [hsq] at hb
  have h1 : (ug m (Real.sin θ)) ^ 2 ≤ (Real.sqrt (Npsi m) * Real.cos θ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt (Npsi_pos m))]
    exact hb
  have h2 := sq_le_sq.mp h1
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt (Npsi m) * Real.cos θ)] at h2

lemma c_mul_gC_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ * |gC (2 * m + 1) (Real.sin θ)| ≤ Real.sqrt (Npsi m) := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have h := ug_sin_bound m hθ
  rw [gC_div_ug m hθ, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (Real.cos θ) ^ 2)]
  have hgoal : Real.cos θ * (|ug m (Real.sin θ)| / (Real.cos θ) ^ 2)
      = |ug m (Real.sin θ)| / Real.cos θ := by
    field_simp
  rw [hgoal, div_le_iff₀ hc]
  exact h

lemma gC_abs_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |gC (2 * m + 1) (Real.sin θ)| ≤ Real.sqrt (Npsi m) / Real.cos θ := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  rw [le_div_iff₀ hc]
  simpa [mul_comm] using c_mul_gC_bound m hθ

lemma deriv_ug_abs_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |deriv (ug m) (Real.sin θ)| ≤ Npsi m := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have h := Real.sqrt_le_sqrt (du_bound m ⟨hs0, hs1⟩)
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (le_of_lt (Npsi_pos m))] at h

lemma two_sin_gC_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |2 * Real.sin θ * gC (2 * m + 1) (Real.sin θ)|
      ≤ 2 * (Real.sqrt (Npsi m) / Real.cos θ) := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have hsabs : |Real.sin θ| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith, hs1⟩
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * |Real.sin θ| * |gC (2 * m + 1) (Real.sin θ)|
      ≤ 2 * 1 * (Real.sqrt (Npsi m) / Real.cos θ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsabs (by norm_num)) (gC_abs_bound m hθ)
          (abs_nonneg _) (by norm_num)
    _ = 2 * (Real.sqrt (Npsi m) / Real.cos θ) := by ring

lemma deriv_gC_mul_eq (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)
      = deriv (ug m) (Real.sin θ)
        + 2 * Real.sin θ * gC (2 * m + 1) (Real.sin θ) := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  rw [deriv_ug m (Real.sin θ), hsq]
  ring

lemma c2_mul_deriv_gC_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.cos θ) ^ 2 * |deriv (gC (2 * m + 1)) (Real.sin θ)|
      ≤ Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  rw [show (Real.cos θ) ^ 2 * |deriv (gC (2 * m + 1)) (Real.sin θ)|
      = |(Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)| from by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.cos θ) ^ 2)]]
  rw [deriv_gC_mul_eq m hθ]
  calc |deriv (ug m) (Real.sin θ) + 2 * Real.sin θ * gC (2 * m + 1) (Real.sin θ)|
      ≤ |deriv (ug m) (Real.sin θ)| + |2 * Real.sin θ * gC (2 * m + 1) (Real.sin θ)| :=
        abs_add_le _ _
    _ ≤ Npsi m + 2 * (Real.sqrt (Npsi m) / Real.cos θ) :=
        add_le_add (deriv_ug_abs_bound m hθ) (two_sin_gC_bound m hθ)
    _ = Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ := by ring

lemma scq_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)|
      ≤ (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) / Real.cos θ := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have hsabs : |Real.sin θ| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith, hs1⟩
  have hq' := c2_mul_deriv_gC_bound m hθ
  rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hc)]
  rw [le_div_iff₀ hc]
  calc |Real.sin θ| * Real.cos θ * |deriv (gC (2 * m + 1)) (Real.sin θ)| * Real.cos θ
      = |Real.sin θ| * ((Real.cos θ) ^ 2 * |deriv (gC (2 * m + 1)) (Real.sin θ)|) := by ring
    _ ≤ 1 * (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) :=
        mul_le_mul hsabs hq' (by positivity) (by norm_num)
    _ = Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ := by ring

/-! ## The derivative formulas for `eFam` -/

lemma deriv_eFam (m : ℕ) (θ : ℝ) :
    deriv (eFam m) θ
      = -Real.sin θ * gC (2 * m + 1) (Real.sin θ)
        + (Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ) := by
  have h := congrFun (deriv_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1))) θ
  rw [show deriv (eFam m) θ
      = deriv (fun θ' : ℝ => Real.cos θ' * gC (2 * m + 1) (Real.sin θ')) θ from rfl]
  exact h

lemma deriv2_eFam (m : ℕ) (θ : ℝ) :
    deriv (deriv (eFam m)) θ
      = -Real.cos θ * gC (2 * m + 1) (Real.sin θ)
        - 3 * Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)
        + (Real.cos θ) ^ 3 * deriv (deriv (gC (2 * m + 1))) (Real.sin θ) := by
  have h := deriv2_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1)) θ
  rw [show deriv (deriv (eFam m))
      = deriv (deriv (fun θ' : ℝ => Real.cos θ' * gC (2 * m + 1) (Real.sin θ'))) from rfl]
  exact h

lemma deriv_tan_eFam (m : ℕ) {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' => Real.tan θ' * eFam m θ') θ
      = Real.cos θ * gC (2 * m + 1) (Real.sin θ)
        + Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ) := by
  have h := deriv_tan_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1)) θ hθ
  rw [show (fun θ' : ℝ => Real.tan θ' * eFam m θ')
      = (fun θ' : ℝ => Real.tan θ' * (Real.cos θ' * gC (2 * m + 1) (Real.sin θ'))) from rfl]
  exact h

end Work.FTS.PhiStar.Series.Deleg
