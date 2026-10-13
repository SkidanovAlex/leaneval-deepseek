import Mathlib
import Submission.Work.WilG4c.Engine

namespace Work.WilG4c

open Work.WilkG4c

open scoped BigOperators

/-! ## The chain rule along the curve `t ↦ (t, γ t)`

We prove the requested statement in two independent steps.

* `hasDerivAt_curveFun`: the curve `t ↦ curveFun γ t = (t, γ t)` is differentiable at `t`, with
  derivative the tangent vector `curveTangent γ t` (which has `1` in the `x`-coordinate and
  `γ_j'(t)` in the `j`-th `y`-coordinate).
* `fderiv_curveTangent`: applying `fderiv ℝ f c` to that tangent vector splits, by linearity,
  into the `x`-derivative plus the sum of the `y`-derivatives weighted by `γ_j'(t)`.
* `differentiableAt_iterDir`: `ContDiffAt ℝ (L.length + 1) G c` makes the iterated directional
  derivative `iterDir L G` differentiable at `c`.

The main theorem is then the chain rule for the composed function `t ↦ iterDir L G (curveFun γ t)`,
using that `iterDir (i :: L) G c` is *by definition* the `i`-directional derivative
`fderiv ℝ (iterDir L G) c (Pi.single i 1)`. -/

/-! ### The tangent vector of the curve -/

/-- The tangent vector at time `t` of the curve `t ↦ (t, γ t)`: `1` in the `x`-coordinate and
`γ_j'(t)` in the `j`-th `y`-coordinate. -/
noncomputable def curveTangent {n : ℕ} (γ : ℝ → Fin n → ℝ) (t : ℝ) : Fin (n + 1) → ℝ :=
  Pi.single (0 : Fin (n + 1)) 1 + ∑ j : Fin n, deriv (fun s => γ s j) t • Pi.single j.succ 1

@[simp] theorem curveTangent_zero {n : ℕ} (γ : ℝ → Fin n → ℝ) (t : ℝ) : curveTangent γ t 0 = 1 := by
  simp [curveTangent]

@[simp] theorem curveTangent_succ {n : ℕ} (γ : ℝ → Fin n → ℝ) (t : ℝ) (j : Fin n) :
    curveTangent γ t j.succ = deriv (fun s => γ s j) t := by
  rw [curveTangent, Pi.add_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero j), zero_add,
    Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    have h : ¬ (j.succ = b.succ) := fun hh => hb (Fin.succ_inj.mp hh.symm)
    simp [Pi.smul_apply, h]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The curve `t ↦ (t, γ t)` is differentiable, with derivative the tangent vector. -/
theorem hasDerivAt_curveFun {n : ℕ} (γ : ℝ → Fin n → ℝ) (t : ℝ)
    (hγ : ∀ j : Fin n, DifferentiableAt ℝ (fun s => γ s j) t) :
    HasDerivAt (curveFun γ) (curveTangent γ t) t := by
  rw [hasDerivAt_pi]
  intro i
  induction i using Fin.cases with
  | zero => simpa using hasDerivAt_id' t
  | succ j => simpa using (hγ j).hasDerivAt

/-- Linearity of `fderiv ℝ f c` applied to the tangent vector of the curve: it splits into the
`x`-direction derivative plus the `y`-direction derivatives weighted by the derivatives of `γ`. -/
theorem fderiv_curveTangent {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (c : Fin (n + 1) → ℝ)
    (γ : ℝ → Fin n → ℝ) (t : ℝ) :
    fderiv ℝ f c (curveTangent γ t)
      = fderiv ℝ f c (Pi.single (0 : Fin (n + 1)) 1) +
        ∑ j : Fin n, fderiv ℝ f c (Pi.single j.succ 1) * deriv (fun s => γ s j) t := by
  rw [curveTangent, map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-! ### Smoothness of iterated directional derivatives -/

/-- An iterated directional derivative of a `C^{|L| + k}` function is `C^k`:
each step takes the Fréchet derivative (losing one order of smoothness) and evaluates it at a
fixed direction (a continuous linear operation). -/
theorem contDiffAt_iterDir {m : ℕ} {G : (Fin m → ℝ) → ℝ} {c : Fin m → ℝ} {L : List (Fin m)}
    {k : ℕ} (hG : ContDiffAt ℝ ((L.length + k : ℕ) : WithTop ℕ∞) G c) :
    ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (iterDir L G) c := by
  induction L generalizing k with
  | nil => simpa using hG
  | cons i L ih =>
    rw [iterDir_cons]
    have hstep : ((L.length + (k + 1) : ℕ) : WithTop ℕ∞) = (((i :: L).length + k : ℕ)) := by
      congr 1
      simp only [List.length_cons]
      omega
    have hL : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (iterDir L G) c :=
      ih (k := k + 1) (hstep ▸ hG)
    have hL' : ContDiffAt ℝ (((k : ℕ) : WithTop ℕ∞) + 1) (iterDir L G) c := by
      simpa only [Nat.cast_add, Nat.cast_one] using hL
    have hfd : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fderiv ℝ (iterDir L G)) c :=
      ContDiffAt.fderiv_right_succ (n := ((k : ℕ) : WithTop ℕ∞)) hL'
    have hc : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞)
        (fun _ : Fin m → ℝ => (Pi.single i (1 : ℝ) : Fin m → ℝ)) c := by fun_prop
    exact hfd.clm_apply hc

/-- An iterated directional derivative of a function which is `C^{|L|+1}` at a point is
differentiable there. -/
theorem differentiableAt_iterDir {m : ℕ} {G : (Fin m → ℝ) → ℝ} {c : Fin m → ℝ}
    {L : List (Fin m)} (hG : ContDiffAt ℝ (L.length + 1) G c) :
    DifferentiableAt ℝ (iterDir L G) c := by
  have h : ContDiffAt ℝ ((L.length + 1 : ℕ) : WithTop ℕ∞) G c := by
    simpa only [Nat.cast_add, Nat.cast_one] using hG
  exact (contDiffAt_iterDir (k := 1) h).differentiableAt_one

/-- The chain rule along the curve `t ↦ (t, γ t)`: differentiating `t ↦ ∂^L G (t, γ t)` gives
the `x`-direction derivative (the extra `0` at the head of the list) plus, for each `y`
coordinate, the extra `y`-derivative times `γ_j'`.  (`iterDir L G` is the iterated directional
derivative along the list `L` of directions, `curveFun γ t = Fin.cons t (γ t)`; both are
defined in `Submission/Work/WilG4c/Engine.lean`.) -/
theorem hasDerivAt_iterDir_curve {n : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ) (γ : ℝ → Fin n → ℝ)
    (L : List (Fin (n + 1))) (t : ℝ)
    (hG : ContDiffAt ℝ (L.length + 1) G (curveFun γ t))
    (hγ : ∀ j : Fin n, DifferentiableAt ℝ (fun s => γ s j) t) :
    HasDerivAt (fun s => iterDir L G (curveFun γ s))
      (iterDir ((0 : Fin (n + 1)) :: L) G (curveFun γ t) +
        ∑ j : Fin n, iterDir (j.succ :: L) G (curveFun γ t) * deriv (fun s => γ s j) t) t := by
  have hmain : HasDerivAt (fun s => iterDir L G (curveFun γ s))
      ((fderiv ℝ (iterDir L G) (curveFun γ t)) (curveTangent γ t)) t :=
    (differentiableAt_iterDir hG).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_curveFun γ t hγ)
  convert hmain using 1
  rw [fderiv_curveTangent]
  simp only [iterDir_cons]

end Work.WilG4c
