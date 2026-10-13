/-
# `Work.FTS.PhiStar.Series.eFam_energy_bound`

The pointwise growth bound for the Dirichlet Gegenbauer family
`eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)` of `Lzero`:

  `|eFam m θ| ≤ C · (2m+1)^{3/2} · (cos θ)^{-1/2}`   (`m ≥ 1`, `θ ∈ (0, π/2)`)

with a universal constant `C`.

**Route.**  Put `q = gC (2m+1) = C^{(3/2)}_{2m+1}` and `u(x) = (1-x²)·q(x)`.  The Gegenbauer
equation `(1-x²)q'' - 4xq' + n(n+3)q = 0` for `n = 2m+1` (`gC_ode`) is exactly the statement
that `u'' = -N·q` with `N = (2m+2)(2m+3) = n(n+3)+2`; equivalently `u` solves the *regular*
Sturm–Liouville equation `u'' + N/(1-x²)·u = 0` on `(-1,1)`.

The associated energy `E(x) = u'(x)² + N/(1-x²)·u(x)²` — used below in the denominator-free
form `ene m x = u'(x)² + N·(1-x²)·q(x)²` — satisfies `E'(x) = 2xN·q(x)² ≥ 0`, so `E` is
nondecreasing on `[0,1]`.  At `x = 1` we have `u(1) = 0`, `u'(1) = -2q(1)` and
`q(1) = (n+1)(n+2)/2 = N/2` (`gC_at_one`), so `E(1) = N²`.  Hence for `0 ≤ x ≤ 1`

  `N·u(x)²/(1-x²) ≤ E(x) ≤ N²`,  i.e.  `u(x)² ≤ N(1-x²)`.

Substituting `x = sin θ` and using `u(sin θ) = cos²θ·q(sin θ)` together with
`eFam m θ = cos θ·q(sin θ)` gives `|eFam m θ|² ≤ N`, i.e. `|eFam m θ| ≤ √((2m+2)(2m+3))`
— the sharp order in `m`.  The stated bound follows because the final factor
`(2m+1)^{3/2}·(cos θ)^{-1/2}` is `≥ 1` and dominates `√((2m+2)(2m+3)) ≤ 2(2m+1)`.

The two auxiliary facts `u' = -2xq + (1-x²)q'` and `u'' + N·q = 0` (`deriv_ug`, `ug_deriv2`)
and the endpoint value `q(1) = N/2` (`gC_at_one`) are also being verified independently in
`Submission/Work/FTS/PhiStar/Series/Deleg/{ugDerivFacts,gCAtOne}.lean`, and the final
arithmetic in `.../Deleg/eFamSqrtArith.lean`.
-/
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
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.EllipticEst.ModalSolution.Lzero1_energy_cos_correct
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series

open Work.FTS.PhiStar.Gegenbauer (eFam gC contDiff_gC gC_ode gC_rec)

namespace EB

set_option autoImplicit false

/-! ## The Sturm–Liouville set-up -/

/-- `Npsi m = (2m+2)(2m+3)`: the spectral constant of the `θ`-equation of `eFam m`
(namely `n(n+3)+2` for `n = 2m+1`). -/
def Npsi (m : ℕ) : ℝ := (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)

lemma Npsi_pos (m : ℕ) : 0 < Npsi m := by
  have h1 : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
  have h2 : (0 : ℝ) < 2 * (m : ℝ) + 3 := by positivity
  unfold Npsi
  exact mul_pos h1 h2

/-- `ug m x = (1 - x²)·gC (2m+1) x`. -/
def ug (m : ℕ) : ℝ → ℝ := fun x => (1 - x ^ 2) * gC (2 * m + 1) x

/-- The energy of `ug m`, written without denominators:
`ene m x = u'(x)² + N·(1-x²)·q(x)²`.  For `x ≠ ±1` this equals `u'(x)² + N·u(x)²/(1-x²)`. -/
def ene (m : ℕ) : ℝ → ℝ :=
  fun x => (deriv (ug m) x) ^ 2 + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x) ^ 2)

/-! ## Smoothness of the Gegenbauer polynomials -/

lemma differentiable_gC (k : ℕ) : Differentiable ℝ (gC k) :=
  (contDiff_gC k).differentiable (by norm_num)

lemma differentiable_deriv_gC (k : ℕ) : Differentiable ℝ (deriv (gC k)) :=
  ((contDiff_gC k).deriv' (n := 2)).differentiable (by norm_num)

/-- `C^{(3/2)}_k(1) = (k+1)(k+2)/2`. -/
lemma gC_at_one (k : ℕ) : gC k 1 = (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2 := by
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
        = ((n : ℝ) + 2) * ((((n : ℝ) + 2) + 1) * (((n : ℝ) + 2) + 2) / 2) := by
      rw [gC_rec n 1, ih1, ih2]
      push_cast
      ring
    have hh := mul_left_cancel₀ h2 h
    rw [hh]
    push_cast
    ring

/-! ## The first and second derivatives of `ug` -/

lemma deriv_ug (m : ℕ) (x : ℝ) :
    deriv (ug m) x
      = -2 * x * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub (1 : ℝ))
  have h2 : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) x) x :=
    (differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y)
      ((-(2 * x)) * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x) x :=
    h1.mul h2
  have h4 : deriv (ug m) x
      = (-(2 * x)) * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
    rw [show ug m = fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y from rfl]
    exact h3.deriv
  rw [h4]
  ring

lemma deriv2_ug (m : ℕ) (x : ℝ) :
    deriv (deriv (ug m)) x
      = -2 * gC (2 * m + 1) x - 4 * x * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x := by
  have hfun : deriv (ug m)
      = fun y : ℝ => -2 * y * gC (2 * m + 1) y + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y :=
    funext (deriv_ug m)
  rw [hfun]
  have hlin : HasDerivAt (fun y : ℝ => (-2 : ℝ) * y) (-2) x := hasDerivAt_const_mul (-2)
  have h1 : HasDerivAt (fun y : ℝ => -2 * y * gC (2 * m + 1) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x) x :=
    hlin.mul ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h1' : HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub (1 : ℝ))
  have h2 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((-(2 * x)) * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x) x :=
    h1'.mul ((differentiable_deriv_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h3 : HasDerivAt
      (fun y : ℝ => -2 * y * gC (2 * m + 1) y + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      (((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x)
        + ((-(2 * x)) * deriv (gC (2 * m + 1)) x
          + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x)) x :=
    h1.add h2
  rw [h3.deriv]
  ring

/-- **The Sturm–Liouville equation in `u`-form**: `u'' = -N·q`. -/
lemma ug_deriv2 (m : ℕ) (x : ℝ) :
    deriv (deriv (ug m)) x = -(Npsi m) * gC (2 * m + 1) x := by
  have hode := (gC_ode (2 * m + 1)).2 x
  have hkey : (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x
      = 4 * x * deriv (gC (2 * m + 1)) x
        - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) * gC (2 * m + 1) x := by
    linarith [hode]
  have hN : Npsi m = (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) + 2 := by
    unfold Npsi
    push_cast
    ring
  rw [deriv2_ug m x, hkey, hN]
  ring

/-- `u'(1) = -N`. -/
lemma deriv_ug_one (m : ℕ) : deriv (ug m) 1 = -Npsi m := by
  rw [deriv_ug m 1]
  have hg : gC (2 * m + 1) 1 = Npsi m / 2 := by
    rw [gC_at_one (2 * m + 1)]
    unfold Npsi
    push_cast
    ring
  rw [hg]
  ring

lemma differentiable_deriv_ug (m : ℕ) : Differentiable ℝ (deriv (ug m)) := by
  rw [funext (deriv_ug m)]
  exact (((differentiable_const (-2 : ℝ)).mul differentiable_id).mul
      (differentiable_gC (2 * m + 1))).add
    (((differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)).mul
      (differentiable_deriv_gC (2 * m + 1)))

/-! ## The energy and its monotonicity -/

lemma differentiable_ene (m : ℕ) : Differentiable ℝ (ene m) := by
  have h1 : Differentiable ℝ (fun x : ℝ => (deriv (ug m) x) ^ 2) :=
    (differentiable_deriv_ug m).pow 2
  have h2 : Differentiable ℝ (fun x : ℝ => (1 : ℝ) - x ^ 2) :=
    (differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)
  have h3 : Differentiable ℝ (fun x : ℝ => (gC (2 * m + 1) x) ^ 2) :=
    (differentiable_gC (2 * m + 1)).pow 2
  have h4 : Differentiable ℝ
      (fun x : ℝ => Npsi m * (((1 : ℝ) - x ^ 2) * (gC (2 * m + 1) x) ^ 2)) :=
    (differentiable_const (Npsi m)).mul (h2.mul h3)
  exact h1.add h4

lemma continuous_ene (m : ℕ) : Continuous (ene m) := (differentiable_ene m).continuous

/-- On `x ≠ ±1` the denominator-free energy is the usual `u'² + N·u²/(1-x²)`. -/
lemma ene_eq (m : ℕ) {x : ℝ} (hx : 1 - x ^ 2 ≠ 0) :
    ene m x = (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 := by
  show (deriv (ug m) x) ^ 2 + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x) ^ 2)
      = (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
  rw [show ug m x = (1 - x ^ 2) * gC (2 * m + 1) x from rfl]
  field_simp

/-- `E'(x) = 2xN·q(x)²`. -/
lemma deriv_ene (m : ℕ) (x : ℝ) :
    deriv (ene m) x = 2 * x * Npsi m * (gC (2 * m + 1) x) ^ 2 := by
  have hdu : HasDerivAt (deriv (ug m)) (deriv (deriv (ug m)) x) x :=
    (differentiable_deriv_ug m).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => (deriv (ug m) y) ^ 2)
      (2 * (deriv (ug m) x) ^ (2 - 1) * deriv (deriv (ug m)) x) x := hdu.pow 2
  have hsq : HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub (1 : ℝ))
  have h2 : HasDerivAt (fun y : ℝ => ((1 : ℝ) - y ^ 2) * (gC (2 * m + 1) y) ^ 2)
      ((-(2 * x)) * (gC (2 * m + 1) x) ^ 2
        + (1 - x ^ 2) * (2 * (gC (2 * m + 1) x) ^ (2 - 1)
            * deriv (gC (2 * m + 1)) x)) x := by
    have hg : HasDerivAt (fun y : ℝ => (gC (2 * m + 1) y) ^ 2)
        (2 * (gC (2 * m + 1) x) ^ (2 - 1) * deriv (gC (2 * m + 1)) x) x :=
      ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt).pow 2
    exact hsq.mul hg
  have h3 : HasDerivAt
      (fun y : ℝ => Npsi m * (((1 : ℝ) - y ^ 2) * (gC (2 * m + 1) y) ^ 2))
      (Npsi m * ((-(2 * x)) * (gC (2 * m + 1) x) ^ 2
        + (1 - x ^ 2) * (2 * (gC (2 * m + 1) x) ^ (2 - 1)
            * deriv (gC (2 * m + 1)) x))) x :=
    h2.const_mul (Npsi m)
  have h4 : HasDerivAt (ene m)
      (2 * (deriv (ug m) x) ^ (2 - 1) * deriv (deriv (ug m)) x
        + Npsi m * ((-(2 * x)) * (gC (2 * m + 1) x) ^ 2
          + (1 - x ^ 2) * (2 * (gC (2 * m + 1) x) ^ (2 - 1)
              * deriv (gC (2 * m + 1)) x))) x :=
    h1.add h3
  rw [h4.deriv, ug_deriv2 m x, deriv_ug m x]
  ring

/-- `E(1) = N²`. -/
lemma ene_one (m : ℕ) : ene m 1 = Npsi m ^ 2 := by
  show (deriv (ug m) 1) ^ 2 + Npsi m * ((1 - (1 : ℝ) ^ 2) * (gC (2 * m + 1) 1) ^ 2)
      = Npsi m ^ 2
  rw [deriv_ug_one m]
  ring

/-- `E ≤ E(1) = N²` on `[0,1]`. -/
lemma ene_le (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : ene m x ≤ Npsi m ^ 2 := by
  have hmono : MonotoneOn (ene m) (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuous_ene m).continuousOn
      (differentiable_ene m).differentiableOn ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    rw [deriv_ene m y]
    exact mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * y) (le_of_lt (Npsi_pos m)))
      (sq_nonneg _)
  have h1 : ene m x ≤ ene m 1 := hmono hx ⟨by norm_num, le_rfl⟩ hx.2
  rwa [ene_one m] at h1

/-! ## The pointwise bound on `u` and on `eFam` -/

lemma ug_bound (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (ug m x) ^ 2 ≤ Npsi m * (1 - x ^ 2) := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hc : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hE : (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
        ≤ Npsi m ^ 2 := by
      rw [← ene_eq m hne]
      exact ene_le m hx
    have h3 : (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 ≤ Npsi m ^ 2 := by
      linarith [hE, sq_nonneg (deriv (ug m) x)]
    rw [div_mul_eq_mul_div₀, div_le_iff₀ hc] at h3
    have h5 : Npsi m * (ug m x) ^ 2 ≤ Npsi m * (Npsi m * (1 - x ^ 2)) := by
      calc Npsi m * (ug m x) ^ 2 ≤ Npsi m ^ 2 * (1 - x ^ 2) := h3
        _ = Npsi m * (Npsi m * (1 - x ^ 2)) := by ring
    exact le_of_mul_le_mul_left h5 (Npsi_pos m)
  · subst heq
    simp [ug]

/-- **The energy bound**: `|eFam m θ| ≤ √((2m+2)(2m+3))` for `θ ∈ (0, π/2)`. -/
lemma eFam_abs_le_sqrt_N (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |eFam m θ| ≤ Real.sqrt (Npsi m) := by
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsq : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  have hb := ug_bound m (show (Real.sin θ) ∈ Set.Icc (0 : ℝ) 1 from ⟨hs0, hs1⟩)
  have h2 : (ug m (Real.sin θ)) ^ 2 = (Real.cos θ) ^ 2 * (eFam m θ) ^ 2 := by
    show ((1 - (Real.sin θ) ^ 2) * gC (2 * m + 1) (Real.sin θ)) ^ 2
        = (Real.cos θ) ^ 2 * (Real.cos θ * gC (2 * m + 1) (Real.sin θ)) ^ 2
    rw [hsq]
    ring
  rw [h2] at hb
  have hsq2 : (eFam m θ) ^ 2 ≤ Npsi m := by
    have hc2 : 0 < (Real.cos θ) ^ 2 := pow_pos hc 2
    have hbb : (Real.cos θ) ^ 2 * (eFam m θ) ^ 2 ≤ (Real.cos θ) ^ 2 * Npsi m := by
      calc (Real.cos θ) ^ 2 * (eFam m θ) ^ 2 ≤ Npsi m * (1 - (Real.sin θ) ^ 2) := hb
        _ = Npsi m * (Real.cos θ) ^ 2 := by rw [hsq]
        _ = (Real.cos θ) ^ 2 * Npsi m := by ring
    exact le_of_mul_le_mul_left hbb hc2
  calc |eFam m θ| = Real.sqrt ((eFam m θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Npsi m) := Real.sqrt_le_sqrt hsq2

/-! ## The final arithmetic -/

/-- `√((2m+2)(2m+3)) ≤ 2·(2m+1)^{3/2}·(cos θ)^{-1/2}` for `m ≥ 1`, `θ ∈ (0, π/2)`. -/
lemma sqrt_Npsi_le (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sqrt (Npsi m) ≤ 2 * ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
      * Real.sqrt (1 / Real.cos θ) := by
  have hmn : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn0 : 0 ≤ 2 * (m : ℝ) + 1 := by linarith
  have hle : Npsi m ≤ (2 * (2 * (m : ℝ) + 1)) ^ 2 := by
    have hsq : 0 ≤ ((m : ℝ) - 1) ^ 2 := sq_nonneg _
    unfold Npsi
    nlinarith [hmn, hsq]
  have h2n : (0 : ℝ) ≤ 2 * (2 * (m : ℝ) + 1) := by linarith
  have h1 : Real.sqrt (Npsi m) ≤ 2 * (2 * (m : ℝ) + 1) := by
    have h := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg h2n] at h
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hs : 1 ≤ Real.sqrt (2 * (m : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hn0]
    linarith
  have hy : 1 ≤ Real.sqrt (1 / Real.cos θ) := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ 1 / Real.cos θ)]
    rw [le_div_iff₀ hc]
    linarith
  have hmid : (1 : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (1 / Real.cos θ) :=
    by simpa using mul_le_mul hs hy zero_le_one (Real.sqrt_nonneg _)
  have h2 : 2 * (2 * (m : ℝ) + 1) ≤ 2 * ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
      * Real.sqrt (1 / Real.cos θ) := by
    have hstep : (2 * (m : ℝ) + 1)
        ≤ ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) * Real.sqrt (1 / Real.cos θ) := by
      have h0 := mul_le_mul_of_nonneg_left hmid hn0
      calc (2 * (m : ℝ) + 1) = (2 * (m : ℝ) + 1) * 1 := by ring
        _ ≤ (2 * (m : ℝ) + 1)
            * (Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (1 / Real.cos θ)) := h0
        _ = ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
            * Real.sqrt (1 / Real.cos θ) := by ring
    linarith [hstep]
  linarith [h1, h2]

end EB

theorem eFam_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤
        C * ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) *
          Real.sqrt (1 / Real.cos θ) := by
  refine ⟨2, by norm_num, fun m hm θ hθ => ?_⟩
  exact le_trans (EB.eFam_abs_le_sqrt_N m hθ) (EB.sqrt_Npsi_le m hm hθ)

end Work.FTS.PhiStar.Series
