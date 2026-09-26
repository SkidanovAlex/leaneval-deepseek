/-
# The CKMRV open set `U₀` and its geometry

This file fixes the vocabulary used by `Work.CKFinal.paperLayer_mdifferentiableOn_U0`:

* `Work.CKFinal.U0` — the open set of the strip `-1 < Re τ < 1` lying strictly outside the four
  closed discs of radius `1/4` centred at `±1/4` and `±3/4`.  It is the union of the four open
  Farey triangles `(-1,0,∞)`, `(0,1,∞)`, `(0,1/2,1)`, `(-1,-1/2,0)` together with their three
  common edges, the imaginary axis and the two bottom arcs `|τ ∓ 1/2| = 1/2`.
* `Work.CKFinal.OnAxis` — the imaginary axis.
* `Work.CKFinal.OnArc` — the two bottom arcs (the geodesics `0 ↔ ±1`).
* `Work.CKFinal.CleanAt` / `Work.CKFinal.CleanOnClosedBall` — the pointwise and closed-ball forms of
  the *cleanliness* condition `j τ ≠ j (i t)` for every `t > 0`, which is exactly the statement
  that `w ↦ K(w, i t)` is holomorphic at `w = τ` for every `t > 0`.

The complement of `U0 ∪ OnAxis ∪ OnArc` in `U0` consists of the four open triangles, on which the
`SL(2,ℤ)`-orbit of a point misses the imaginary axis: the Farey geodesics are exactly the
`SL(2,ℤ)`-translates of `iℝ`, and the only such geodesics meeting `U₀` are the imaginary axis and
the two bottom arcs.  This is `Work.CKFinal.U0Orbit.orbit_imagAxis_of_mem_U0` (delegated).
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane

namespace Work.CKFinal

open Work.Kernels

/-- **The open set `U₀`** of the strip `-1 < Re τ < 1` outside the four closed Farey discs of
radius `1/4` centred at `±1/4` and `±3/4`. -/
def U0 : Set ℍ :=
  {τ : ℍ | -1 < τ.re ∧ τ.re < 1 ∧
    (1 : ℝ) / 4 < ‖(τ : ℂ) - (1 / 4 : ℂ)‖ ∧ (1 : ℝ) / 4 < ‖(τ : ℂ) + (1 / 4 : ℂ)‖ ∧
    (1 : ℝ) / 4 < ‖(τ : ℂ) - (3 / 4 : ℂ)‖ ∧ (1 : ℝ) / 4 < ‖(τ : ℂ) + (3 / 4 : ℂ)‖}

/-- The imaginary axis, as a subset of `ℍ`. -/
def OnAxis (τ : ℍ) : Prop := τ.re = 0

/-- The two bottom arcs `|τ ∓ 1/2| = 1/2` (the geodesics `0 ↔ ±1`, together `SL(2,ℤ)·iℝ`). -/
def OnArc (τ : ℍ) : Prop :=
  ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2 ∨ ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2

/-- The point `i t` of the imaginary axis is **clean** with respect to `τ`, i.e. `w ↦ K(w, it)` is
holomorphic at `w = τ` for that `t`. -/
def CleanAt (τ : ℍ) : Prop :=
  ∀ (t : ℝ) (ht : 0 < t), jInvariantFun τ ≠ jInvariantFun (imagAxis t ht)

/-- **Cleanliness on a closed ball**: every `τ` with `dist τ τ₀ ≤ ρ` is clean. -/
def CleanOnClosedBall (τ₀ : ℍ) (ρ : ℝ) : Prop :=
  ∀ (t : ℝ) (ht : 0 < t), ∀ τ : ℍ, dist τ τ₀ ≤ ρ →
    jInvariantFun τ ≠ jInvariantFun (imagAxis t ht)

lemma mem_U0_iff {τ : ℍ} :
    τ ∈ U0 ↔ -1 < τ.re ∧ τ.re < 1 ∧
      (1 : ℝ) / 4 < ‖(τ : ℂ) - (1 / 4 : ℂ)‖ ∧ (1 : ℝ) / 4 < ‖(τ : ℂ) + (1 / 4 : ℂ)‖ ∧
      (1 : ℝ) / 4 < ‖(τ : ℂ) - (3 / 4 : ℂ)‖ ∧ (1 : ℝ) / 4 < ‖(τ : ℂ) + (3 / 4 : ℂ)‖ :=
  Iff.rfl

/-- `U₀` is open. -/
theorem isOpen_U0 : IsOpen U0 := by
  have h1 : IsOpen {τ : ℍ | -1 < τ.re} := isOpen_lt continuous_const UpperHalfPlane.continuous_re
  have h2 : IsOpen {τ : ℍ | τ.re < 1} := isOpen_lt UpperHalfPlane.continuous_re continuous_const
  have h3 : IsOpen {τ : ℍ | (1 : ℝ) / 4 < ‖(τ : ℂ) - (1 / 4 : ℂ)‖} :=
    isOpen_lt continuous_const (by fun_prop)
  have h4 : IsOpen {τ : ℍ | (1 : ℝ) / 4 < ‖(τ : ℂ) + (1 / 4 : ℂ)‖} :=
    isOpen_lt continuous_const (by fun_prop)
  have h5 : IsOpen {τ : ℍ | (1 : ℝ) / 4 < ‖(τ : ℂ) - (3 / 4 : ℂ)‖} :=
    isOpen_lt continuous_const (by fun_prop)
  have h6 : IsOpen {τ : ℍ | (1 : ℝ) / 4 < ‖(τ : ℂ) + (3 / 4 : ℂ)‖} :=
    isOpen_lt continuous_const (by fun_prop)
  have hset : U0 = {τ : ℍ | -1 < τ.re} ∩ {τ : ℍ | τ.re < 1} ∩
      {τ : ℍ | (1 : ℝ) / 4 < ‖(τ : ℂ) - (1 / 4 : ℂ)‖} ∩
      {τ : ℍ | (1 : ℝ) / 4 < ‖(τ : ℂ) + (1 / 4 : ℂ)‖} ∩
      {τ : ℍ | (1 : ℝ) / 4 < ‖(τ : ℂ) - (3 / 4 : ℂ)‖} ∩
      {τ : ℍ | (1 : ℝ) / 4 < ‖(τ : ℂ) + (3 / 4 : ℂ)‖} := by
    ext τ; simp only [U0, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [hset]
  exact ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6

/-- The imaginary axis is a closed subset of `ℍ`. -/
theorem isClosed_onAxis : IsClosed {τ : ℍ | OnAxis τ} :=
  isClosed_eq UpperHalfPlane.continuous_re continuous_const

/-- The two bottom arcs form a closed subset of `ℍ`. -/
theorem isClosed_onArc : IsClosed {τ : ℍ | OnArc τ} := by
  have hc1 : Continuous fun τ : ℍ => ‖(τ : ℂ) - (1 / 2 : ℂ)‖ := by fun_prop
  have hc2 : Continuous fun τ : ℍ => ‖(τ : ℂ) + (1 / 2 : ℂ)‖ := by fun_prop
  have h1 : IsClosed {τ : ℍ | ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2} :=
    isClosed_eq hc1 continuous_const
  have h2 : IsClosed {τ : ℍ | ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2} :=
    isClosed_eq hc2 continuous_const
  have hset : {τ : ℍ | OnArc τ} = {τ : ℍ | ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2} ∪
      {τ : ℍ | ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2} := by
    ext τ; simp only [OnArc, Set.mem_ofPred_eq, Set.mem_union]
  rw [hset]; exact h1.union h2

end Work.CKFinal
