import Mathlib
import Submission.Work.SSS.HornDefs

/-!
# `θ_n : I^n → Δ^n` is injective off the boundary of the cube

The parametrization `Work.SSS.cubeToSimplexFun n` of the `n`-simplex by the `n`-cube is defined by
iterating the cone description `Δ^{n+1} = C(Δ^n)`: writing `x = (Fin.init x, t)` with
`t = x (Fin.last n)`,

* the last coordinate of `θ_{n+1} x` is `1 - t`,
* the `l`-th coordinate (`l : Fin (n+1)`) of `θ_{n+1} x`, at the position
  `(Fin.last (n+1)).succAbove l`, is `t * θ_n (Fin.init x) l`.

A point of the cube is off the boundary `Cube.boundary (Fin n) = {x | ∃ i, x i = 0 ∨ x i = 1}`
exactly when all of its coordinates lie in the open unit interval `(0,1)`.  In that case the last
coordinate `1 - t` of `θ_n x` equals the last coordinate of `θ_n x'` forces `t = t'`, and `t ≠ 0`
lets us cancel `t` to compare `θ_{n-1}` of the two initial segments.  Induction on `n` then
reconstructs `x` from `Fin.init x` and `x (Fin.last n)`.
-/

set_option autoImplicit false

namespace Work.SSS

/-- A point of the cube off the boundary has all its coordinates different from `0` and `1`
(and conversely). -/
theorem not_mem_cubeBoundary_iff {n : ℕ} (x : Fin n → unitInterval) :
    x ∉ Cube.boundary (Fin n) ↔ ∀ i, x i ≠ 0 ∧ x i ≠ 1 := by
  simp only [Cube.boundary, Set.mem_ofPred_eq, not_exists, not_or]

/-- **The parametrization `θ_n : I^n → Δ^n` is injective off the boundary of the cube.** -/
theorem cubeToSimplexFun_injective_off_boundary_aux (n : ℕ) :
    ∀ x x' : Fin n → unitInterval, x ∉ Cube.boundary (Fin n) →
      x' ∉ Cube.boundary (Fin n) →
      cubeToSimplexFun n x = cubeToSimplexFun n x' → x = x' := by
  induction n with
  | zero =>
    -- `Fin 0 → unitInterval` is a subsingleton
    intro x x' hx hx' h
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro x x' hx hx' h
    have hx_bd : ∀ i, x i ≠ 0 ∧ x i ≠ 1 := not_mem_cubeBoundary_iff x |>.mp hx
    have hx'_bd : ∀ i, x' i ≠ 0 ∧ x' i ≠ 1 := not_mem_cubeBoundary_iff x' |>.mp hx'
    -- last coordinate: `1 - x (Fin.last n) = 1 - x' (Fin.last n)`
    have hlast : (x (Fin.last n) : ℝ) = (x' (Fin.last n) : ℝ) := by
      have h1 := congrArg (fun a : stdSimplex ℝ (Fin (n + 2)) =>
        (a : Fin (n + 2) → ℝ) (Fin.last (n + 1))) h
      simp only [cubeToSimplexFun_last] at h1
      linarith
    have hlastI : x (Fin.last n) = x' (Fin.last n) := Subtype.ext hlast
    have hne : (x (Fin.last n) : ℝ) ≠ 0 := by
      intro h0
      exact (hx_bd (Fin.last n)).1 (Subtype.ext h0)
    -- the remaining coordinates: cancel the common factor `x (Fin.last n)`
    have hcoord : ∀ l : Fin (n + 1),
        (cubeToSimplexFun n (Fin.init x) : Fin (n + 1) → ℝ) l =
          (cubeToSimplexFun n (Fin.init x') : Fin (n + 1) → ℝ) l := by
      intro l
      have h1 := congrArg (fun a : stdSimplex ℝ (Fin (n + 2)) =>
        (a : Fin (n + 2) → ℝ) ((Fin.last (n + 1)).succAbove l)) h
      simp only [cubeToSimplexFun_succAbove] at h1
      rw [← hlast] at h1
      exact mul_left_cancel₀ hne h1
    have hθ : cubeToSimplexFun n (Fin.init x) = cubeToSimplexFun n (Fin.init x') :=
      Subtype.ext (funext hcoord)
    -- the initial segments are off the boundary, so we may apply the induction hypothesis
    have hxinit : Fin.init x ∉ Cube.boundary (Fin n) := by
      rw [not_mem_cubeBoundary_iff]
      intro i
      exact hx_bd i.castSucc
    have hx'init : Fin.init x' ∉ Cube.boundary (Fin n) := by
      rw [not_mem_cubeBoundary_iff]
      intro i
      exact hx'_bd i.castSucc
    have hinit : Fin.init x = Fin.init x' := ih _ _ hxinit hx'init hθ
    -- reassemble the two halves
    calc x = Fin.snoc (Fin.init x) (x (Fin.last n)) := (Fin.snoc_init_self x).symm
      _ = Fin.snoc (Fin.init x') (x' (Fin.last n)) := by rw [hinit, hlastI]
      _ = x' := Fin.snoc_init_self x'

/-- The parametrization `θ_n : I^n → Δ^n` of the `n`-simplex by the `n`-cube is injective off the
boundary of the cube. -/
theorem cubeToSimplexFun_injective_off_boundary (n : ℕ) {x x' : Fin n → unitInterval}
    (hx : x ∉ Cube.boundary (Fin n)) (hx' : x' ∉ Cube.boundary (Fin n))
    (h : Work.SSS.cubeToSimplexFun n x = Work.SSS.cubeToSimplexFun n x') : x = x' :=
  cubeToSimplexFun_injective_off_boundary_aux n x x' hx hx' h

end Work.SSS
