/-
# `Work.FTS.GalBasis.cc.PsiCutAux` — the operator machinery behind `psiCut_spec`

This module collects the definitions and lemmas used by the proof of
`Work.FTS.GalBasis.cc.psiCut_spec`.  Everything here is proved in this file (no `sorry`).

The point of the file is the *uniform in `N`* bound on the iterated derivatives of the two
one-dimensional steps `cutA N` and `cutB N` of `CutDefs`.  Both steps have mesh `1/(N+1)`, and
the scale-invariant operators `D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ` of the paper are bounded on a
step of mesh `h` *uniformly in* `h` — this is what makes the cutoffs harmless and is the
content of the estimate below.

The mechanism is the following.  Substituting the rescaled variable (`u = λ z + a` for the
radial factor, `u = λ θ + c` for the angular one) converts `D_z` resp. `D_θ` into the operator

  `Eiter k ρ f = (ρ ∂)^k f`,   `Eop ρ f = ρ * deriv f`,

where `ρ` is an explicit rescaled coefficient: `ρ(u) = u - a` in the radial case and
`ρ(u) = λ sin(2 (u - c)/λ)` in the angular case (with `λ ≠ 0`).  Those two coefficient
functions are uniformly bounded, together with their first few derivatives, on the relevant
compact interval `[0,1]` — and the profile `Real.smoothTransition` is constant off `(0,1)`,
so only that interval matters.

`Eiter_deriv_bound` is the abstract induction producing the bound on all the derivatives
`iteratedDeriv j (Eiter k ρ f)` with `k + j ≤ 4` from pointwise bounds on `iteratedDeriv m ρ`
and `iteratedDeriv m f` on `[0,1]`.  The constants are the recursive `Cbnd`; only their
existence matters.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.GalBasis.cc.CutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The iterated operator `E_ρ = ρ ∂` -/

/-- The operator `E_ρ f = ρ · f'` on functions `ℝ → ℝ`. -/
def Eop (ρ f : ℝ → ℝ) : ℝ → ℝ := ρ * deriv f

/-- The `k`-th iterate of `E_ρ`. -/
def Eiter : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, _, f => f
  | n + 1, ρ, f => Eop ρ (Eiter n ρ f)

@[simp] theorem Eiter_zero (ρ f : ℝ → ℝ) : Eiter 0 ρ f = f := rfl

@[simp] theorem Eiter_succ (n : ℕ) (ρ f : ℝ → ℝ) : Eiter (n + 1) ρ f = Eop ρ (Eiter n ρ f) := rfl

/-- `Eiter k ρ f` is smooth as soon as `ρ` and `f` are. -/
theorem contDiff_Eiter {ρ f : ℝ → ℝ} (hρ : ∀ n : ℕ, ContDiff ℝ n ρ)
    (hf : ∀ n : ℕ, ContDiff ℝ n f) : ∀ k n : ℕ, ContDiff ℝ n (Eiter k ρ f) := by
  intro k
  induction k with
  | zero => intro n; simpa using hf n
  | succ k ih =>
      intro n
      rw [Eiter_succ]
      have h1 : ContDiff ℝ n (deriv (Eiter k ρ f)) := (ih (n + 1)).deriv'
      exact (hρ n).mul h1

theorem contDiff_smoothTransition (n : ℕ) : ContDiff ℝ n Real.smoothTransition :=
  Real.smoothTransition.contDiff

theorem contDiff_sub_const (a : ℝ) : ∀ n : ℕ, ContDiff ℝ n (fun u : ℝ => u - a) :=
  fun n => contDiff_id.sub contDiff_const

theorem contDiff_affine (lam c : ℝ) : ∀ n : ℕ, ContDiff ℝ n (fun θ : ℝ => lam * θ + c) :=
  fun n => (contDiff_const.mul contDiff_id).add contDiff_const

theorem contDiff_rhoU (lam c : ℝ) :
    ∀ n : ℕ, ContDiff ℝ n (fun u : ℝ => lam * Real.sin (2 * ((u - c) / lam))) :=
  fun n => contDiff_const.mul
    (Real.contDiff_sin.comp (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const lam)))

/-! ## Vanishing of the iterates at points where `f` is locally constant -/

/-- If `f` is constant on the open set `U` then all positive iterates of `E_ρ` applied to `f`
vanish on `U`. -/
theorem Eiter_eq_zero_of_open_const {ρ f : ℝ → ℝ} {U : Set ℝ} {u : ℝ} (hU : IsOpen U)
    (hu : u ∈ U) (hconst : ∀ w ∈ U, f w = f u) :
    ∀ k, 1 ≤ k → ∀ v ∈ U, Eiter k ρ f v = 0 := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro _ v hv
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp only [Eiter_succ, Eiter_zero, Eop, Pi.mul_apply]
        have hev : f =ᶠ[𝓝 v] fun _ => f u := by
          filter_upwards [hU.mem_nhds hv] with w hw; exact hconst w hw
        rw [hev.deriv_eq, deriv_const, mul_zero]
      · have hev : (fun w => Eiter k ρ f w) =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
          filter_upwards [hU.mem_nhds hv] with w hw
          exact ih hkpos w hw
        simp only [Eiter_succ, Eop, Pi.mul_apply]
        rw [hev.deriv_eq, deriv_const, mul_zero]

/-! ## The abstract derivative bound -/

/-- The recursive constants of the bound: `Cbnd M B k j` bounds `|iteratedDeriv j (E_ρ^k f)|`
on `[0,1]` whenever `M` bounds the derivatives of `ρ` and `B` those of `f` there. -/
def Cbnd (M B : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => B j
  | (k + 1), j => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * M i * Cbnd M B k (j - i + 1)

theorem Cbnd_nonneg {M B : ℕ → ℝ} (hM : ∀ m, 0 ≤ M m) (hB : ∀ m, 0 ≤ B m) :
    ∀ k j, 0 ≤ Cbnd M B k j := by
  intro k
  induction k with
  | zero => intro j; simp only [Cbnd]; exact hB j
  | succ k ih =>
      intro j
      simp only [Cbnd]
      refine Finset.sum_nonneg ?_
      intro i _
      exact mul_nonneg (mul_nonneg (by positivity) (hM i)) (ih (j - i + 1))

/-- **The abstract bound.**  If `M` bounds the first four derivatives of `ρ` and `B` those of
`f` on `[0,1]`, then `Cbnd M B k j` bounds the `j`-th derivative of `Eiter k ρ f` on `[0,1]`,
for all `k + j ≤ 4`. -/
theorem Eiter_deriv_bound {ρ f : ℝ → ℝ} {M B : ℕ → ℝ}
    (hMnn : ∀ m, 0 ≤ M m) (hBnn : ∀ m, 0 ≤ B m)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hf : ∀ n : ℕ, ContDiff ℝ n f)
    (hM : ∀ m ≤ 3, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m ρ u| ≤ M m)
    (hB : ∀ m ≤ 4, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m f u| ≤ B m) :
    ∀ k j : ℕ, k + j ≤ 4 → ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv j (Eiter k ρ f) u| ≤ Cbnd M B k j := by
  intro k
  induction k with
  | zero =>
    intro j hj u hu
    have e : iteratedDeriv j (Eiter 0 ρ f) u = iteratedDeriv j f u := by rw [Eiter_zero]
    rw [e]
    exact hB j (by omega) u hu
  | succ k ih =>
    intro j hj u hu
    rw [Eiter_succ, Eop]
    have hρj : ContDiffAt ℝ (↑j) ρ u := (hρ j).contDiffAt
    have hgard : ContDiffAt ℝ (↑j) (deriv (Eiter k ρ f)) u :=
      ((contDiff_Eiter hρ hf k (j + 1)).deriv').contDiffAt
    rw [iteratedDeriv_mul hρj hgard]
    simp only [Cbnd]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro i hi
    simp only [Finset.mem_range] at hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp hi
    have hji : j ≤ 3 := by omega
    rw [abs_mul, abs_mul]
    have hci : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
    rw [abs_of_nonneg hci]
    have h1 : |iteratedDeriv i ρ u| ≤ M i := hM i (by omega) u hu
    have he : iteratedDeriv (j - i + 1) (Eiter k ρ f) u
        = iteratedDeriv (j - i) (deriv (Eiter k ρ f)) u := by
      rw [iteratedDeriv_succ']
    rw [← he]
    have h2 : |iteratedDeriv (j - i + 1) (Eiter k ρ f) u| ≤ Cbnd M B k (j - i + 1) :=
      ih (j - i + 1) (by omega) u hu
    exact mul_le_mul (mul_le_mul le_rfl h1 (abs_nonneg _) (by positivity)) h2 (abs_nonneg _)
      (mul_nonneg (by positivity) (hMnn i))

/-! ## The rescaled angular coefficient -/

/-- The coefficient `ρ_λ(u) = λ sin(2 (u+1)/λ)` of the angular substitution: in the rescaled
angular variable `u = λ θ - 1` the operator `D_θ = sin(2θ)∂_θ` becomes `E_{ρ_λ}`. -/
def rhoM (lam : ℝ) : ℝ → ℝ := fun u => lam * Real.sin (2 * (u + 1) / lam)

theorem contDiff_rhoM (lam : ℝ) : ∀ n : ℕ, ContDiff ℝ n (rhoM lam) := by
  intro n
  unfold rhoM
  fun_prop

/-! ## Substitution: the rescaled variables -/

/-- **Radial substitution.**  In the rescaled variable `u = λ z + a` the operator `D_z` becomes
`E_{u ↦ u - a}`. -/
theorem DzIter_affine (f : ℝ → ℝ) (lam a : ℝ) (j : ℕ)
    (hf : ∀ n : ℕ, ContDiff ℝ n f) :
    ∀ z θ : ℝ, Work.Spaces.DzIter j (fun z' (_ : ℝ) => f (lam * z' + a)) z θ
      = Eiter j (fun u => u - a) f (lam * z + a) := by
  induction j with
  | zero => intro z θ; simp
  | succ j ih =>
      intro z θ
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      have hfun : (fun z' => Work.Spaces.DzIter j (fun z' (_ : ℝ) => f (lam * z' + a)) z' θ)
          = fun z' => Eiter j (fun u => u - a) f (lam * z' + a) := by
        funext z'; exact ih z' θ
      rw [hfun]
      have hd : DifferentiableAt ℝ (Eiter j (fun u => u - a) f) (lam * z + a) :=
        ((contDiff_Eiter (contDiff_sub_const a) hf j 1).differentiable (by norm_num)).differentiableAt
      have hlin : HasDerivAt (fun z' : ℝ => lam * z' + a) lam z := by
        have h := ((hasDerivAt_id z).const_mul lam).add_const a
        rw [mul_one] at h
        exact h
      have hcomp : HasDerivAt (fun z' => Eiter j (fun u => u - a) f (lam * z' + a))
          (deriv (Eiter j (fun u => u - a) f) (lam * z + a) * lam) z :=
        hd.hasDerivAt.comp z hlin
      rw [hcomp.deriv, Eiter_succ, Eop]
      simp only [Pi.mul_apply]
      ring

/-- **Angular substitution.**  In the rescaled variable `u = λ θ + c` (`λ ≠ 0`) the operator
`D_θ` becomes `E_{u ↦ λ sin(2 (u - c)/λ)}`. -/
theorem DthIter_affine (f : ℝ → ℝ) (lam c : ℝ) (hlam : lam ≠ 0) (i : ℕ)
    (hf : ∀ n : ℕ, ContDiff ℝ n f) :
    ∀ z θ : ℝ, Work.Spaces.DthIter i (fun _ θ' => f (lam * θ' + c)) z θ
      = Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f (lam * θ + c) := by
  induction i with
  | zero => intro z θ; simp
  | succ i ih =>
      intro z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hfun : (fun θ' => Work.Spaces.DthIter i (fun _ θ' => f (lam * θ' + c)) z θ')
          = fun θ' => Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f (lam * θ' + c) := by
        funext θ'; exact ih z θ'
      rw [hfun]
      have hd : DifferentiableAt ℝ (Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f)
          (lam * θ + c) :=
        ((contDiff_Eiter (contDiff_rhoU lam c) hf i 1).differentiable (by norm_num)).differentiableAt
      have hlin : HasDerivAt (fun θ' : ℝ => lam * θ' + c) lam θ := by
        have h := ((hasDerivAt_id θ).const_mul lam).add_const c
        rw [mul_one] at h
        exact h
      have hcomp : HasDerivAt
          (fun θ' => Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f (lam * θ' + c))
          (deriv (Eiter i (fun u => lam * Real.sin (2 * ((u - c) / lam))) f)
            (lam * θ + c) * lam) θ :=
        hd.hasDerivAt.comp θ hlin
      rw [hcomp.deriv, Eiter_succ, Eop]
      have hq : (lam * θ + c - c) / lam = θ := by
        field_simp
        ring
      simp only [Pi.mul_apply, hq]
      ring

end Work.FTS.GalBasis.cc
