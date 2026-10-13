/-
Copyright: work module for the Elgindi finite-time singularity project.

# The derivative of the `θ`-slice operator `L₀` on `(0, π/2)`

`Lzero1 u = -(deriv (deriv u)) + deriv (tan θ · u) - 6u`, hence on the open interval
`(0, π/2)` (where `tan` has no pole)

  `(Lzero1 u)' = -u''' + (tan θ · u)'' - 6u'`.

Consequently, if `g` agrees with `Lzero1 u` on `(0, π/2)`, then

  `g' = -u''' + (tan θ · u)'' - 6u'`

on `(0, π/2)`: the derivative `deriv` is a local operation, so the identity only has to be
checked inside the interval.  This is the `g`-equation input of the modulation fixed point
(`F = F_* + g`).

# Proof

The computation of `deriv (Lzero1 u)` is done with `iteratedDeriv`, for which Mathlib
provides the linearity lemmas `iteratedDeriv_add`, `iteratedDeriv_sub`, `iteratedDeriv_neg`,
`iteratedDeriv_const_mul` (all under `ContDiffAt` hypotheses).  The smoothness of the pieces
comes from `hu` at the point `θ` (the interval is a neighbourhood of `θ`) together with
`contDiffAt_iteratedDeriv_aux`, and the resulting `iteratedDeriv` statement is translated
back into `deriv` form by `iteratedDeriv_one`, `itd_two_aux` and `itd_three_aux`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ### Two elementary bridges between `deriv` and `iteratedDeriv` -/

/-- A `C^n` function has a `C^{n-k}` `k`-th derivative (for the one-dimensional `deriv`). -/
private lemma contDiffAt_iteratedDeriv_aux {f : ℝ → ℝ} {x : ℝ} {n k : ℕ}
    (h : ContDiffAt ℝ (n : WithTop ℕ∞) f x) (hk : k ≤ n) :
    ContDiffAt ℝ ((n - k : ℕ) : WithTop ℕ∞) (iteratedDeriv k f) x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
      have h1 : n - k - 1 + 1 = n - k := by omega
      have hle : ((n - k - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((n - k : ℕ) : WithTop ℕ∞) := by
        rw [show ((n - k - 1 : ℕ) : WithTop ℕ∞) + 1 = (((n - k - 1) + 1 : ℕ) : WithTop ℕ∞) from by
          push_cast; ring, h1]
      have hstep : ContDiffAt ℝ ((n - k - 1 : ℕ) : WithTop ℕ∞) (deriv (iteratedDeriv k f)) x :=
        (ih hk').derivWithin (m := ((n - k - 1 : ℕ) : WithTop ℕ∞)) hle
      convert hstep using 2
      exact iteratedDeriv_succ

/-- The second `iteratedDeriv` is the second `deriv`. -/
private lemma itd_two_aux (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- The third `iteratedDeriv` is the third `deriv`. -/
private lemma itd_three_aux (f : ℝ → ℝ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, itd_two_aux]

/-- One `iteratedDeriv` on top of a `k`-th one is the `(k+1)`-st one. -/
private lemma itd_comp_one_val_aux (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv 1 (iteratedDeriv n f) x = iteratedDeriv (n + 1) f x := by
  rw [iteratedDeriv_one, ← iteratedDeriv_succ]

/-- `deriv (deriv f)` written with an explicit `λ`, as `iteratedDeriv 2 f`. -/
private lemma itd_two_lambda_val (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun t => deriv f t) x = iteratedDeriv 2 f x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-! ### The identity -/

theorem slice_gprime_ident (u g : ℝ → ℝ) (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ = - deriv (deriv (deriv u)) θ
        + deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ - 6 * deriv u θ := by
  intro θ hθ
  -- `g` and `Lzero1 u` agree in a neighbourhood of `θ`, so their derivatives do too
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hg_ev : g =ᶠ[𝓝 θ] Work.FTS.EllipticEst.Lzero1 u := by
    filter_upwards [hIoo] with t ht
    exact (hg t ht).symm
  rw [hg_ev.deriv_eq]
  -- `tan` is smooth at `θ`
  have hcosθ : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [hθ.1, Real.pi_pos]
    · linarith [hθ.2, Real.pi_pos]
  have huC1 : ContDiffAt ℝ 1 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have huC2 : ContDiffAt ℝ 2 u θ := (hu.contDiffAt hIoo).of_le (by norm_num)
  have htuC2 : ContDiffAt ℝ 2 (fun s => Real.tan s * u s) θ :=
    (Real.contDiffAt_tan.mpr hcosθ).mul huC2
  -- `Lzero1 u` as a function, in terms of `iteratedDeriv`
  have hL_eq : Work.FTS.EllipticEst.Lzero1 u
      = -(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)
        - (fun t => 6 * u t) := by
    funext t
    have hd2 : deriv (fun s => deriv u s) t = iteratedDeriv 2 u t := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hd1 : deriv (fun s => Real.tan s * u s) t
        = iteratedDeriv 1 (fun s => Real.tan s * u s) t := by
      rw [iteratedDeriv_one]
    unfold Work.FTS.EllipticEst.Lzero1
    rw [hd2, hd1]
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
  -- smoothness of the two pieces of `hL_eq`
  have hu2C1 : ContDiffAt ℝ 1 (iteratedDeriv 2 u) θ :=
    contDiffAt_iteratedDeriv_aux (f := u) (n := 3) (k := 2) (hu.contDiffAt hIoo) (by norm_num)
  have htu1C1 : ContDiffAt ℝ 1 (iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
    contDiffAt_iteratedDeriv_aux (f := fun s => Real.tan s * u s) (n := 2) (k := 1) htuC2
      (by norm_num)
  -- the first derivative of `Lzero1 u`, in `iteratedDeriv` form
  have hL1 : iteratedDeriv 1 (Work.FTS.EllipticEst.Lzero1 u) θ
      = -iteratedDeriv 3 u θ + iteratedDeriv 2 (fun s => Real.tan s * u s) θ
        - 6 * iteratedDeriv 1 u θ := by
    rw [hL_eq]
    have hA : ContDiffAt ℝ 1
        (-(iteratedDeriv 2 u) + iteratedDeriv 1 (fun s => Real.tan s * u s)) θ :=
      (ContDiffAt.neg hu2C1).add htu1C1
    have hB : ContDiffAt ℝ 1 (fun t => 6 * u t) θ := contDiffAt_const.mul huC1
    rw [iteratedDeriv_sub hA hB]
    have hA1 : ContDiffAt ℝ 1 (-(iteratedDeriv 2 u)) θ := ContDiffAt.neg hu2C1
    rw [iteratedDeriv_add hA1 htu1C1, iteratedDeriv_neg,
      iteratedDeriv_const_mul (6 : ℝ) huC1]
    rw [itd_comp_one_val_aux 2 u θ, itd_comp_one_val_aux 1 (fun s => Real.tan s * u s) θ]
  -- transport the four `deriv` slots of the goal into `iteratedDeriv` form
  have h1 : deriv (Work.FTS.EllipticEst.Lzero1 u) θ
      = iteratedDeriv 1 (Work.FTS.EllipticEst.Lzero1 u) θ := by rw [iteratedDeriv_one]
  have h2 : deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = iteratedDeriv 2 (fun s => Real.tan s * u s) θ := itd_two_lambda_val _ _
  have h3 : deriv (deriv (deriv u)) θ = iteratedDeriv 3 u θ := by rw [← itd_three_aux u]
  have h4 : deriv u θ = iteratedDeriv 1 u θ := by rw [iteratedDeriv_one]
  rw [h1, h2, h3, h4]
  exact hL1

end Work.FTS.EllipticEst.remov
