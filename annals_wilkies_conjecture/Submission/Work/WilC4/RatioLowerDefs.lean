/-
  WilC4/RatioLowerDefs : the *argument-inverted* family `ArgInv Y` used by
  `Work.WilC4.ratio_lower_zero`.

  `ratio_lower_zero` needs a uniform lower bound `|f_c(2t)| ≥ m |f_c(t)|` for small positive `t`.
  The only uniform input available is `PolyBoundedRExp` (`hPB`), which describes the fibre
  `x ↦ y` of a `∅`-definable family as `x → +∞`.  To read the asymptotics at `0` we invert the
  *argument*: `ArgInv Y` has fibre `u ↦ f_c(1/u)` at large `u`, so `hPB` applied to `ArgInv Y`
  (which is again a `∅`-definable graph family, `argInv_definable`) describes `f_c` as `t → 0⁺`.

  ## Contents

  * the index embedding `ArgInvEmb` reading `(x, y, c)` off a tuple `(x, y, c, w)` in which the
    *argument* slot is the quantified coordinate `w`;
  * `ArgInv Y` itself, with the defining polynomial constraint `w * x = 1`;
  * `gr_argInv_iff`: `Gr (ArgInv Y) c x y ↔ x ≠ 0 ∧ Gr Y c x⁻¹ y`;
  * `argInv_functional`: `ArgInv Y` is a graph family as soon as `Y` is.
-/
import Mathlib
import Submission.Work.WilC4.ULPMRoute

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr)

variable {k : ℕ}

/-! ## 1. The index embedding -/

/-- The index embedding along which the tuple `(w, y, c)` is read off the tuple
`(x, y, c, w)`: the argument slot `0` is sent to the quantified coordinate `Sum.inr 0`, the value
slot `1` to `Sum.inl 1`, and the parameters `i + 2` to `Sum.inl (i + 2)`. -/
def ArgInvEmb (k : ℕ) : Fin (k + 2) → (Fin (k + 2) ⊕ Fin 1) :=
  Fin.cases (Sum.inr (0 : Fin 1))
    (fun i : Fin (k + 1) => Fin.cases (Sum.inl (1 : Fin (k + 2)))
      (fun i' : Fin k => Sum.inl (i'.succ.succ)) i)

theorem argInvEmb_zero (k : ℕ) : ArgInvEmb k (0 : Fin (k + 2)) = Sum.inr (0 : Fin 1) := rfl

theorem argInvEmb_one (k : ℕ) :
    ArgInvEmb k (Fin.succ (0 : Fin (k + 1))) = Sum.inl (1 : Fin (k + 2)) := by
  simp only [ArgInvEmb, Fin.cases_succ, Fin.cases_zero]

theorem argInvEmb_succ_succ (k : ℕ) (i : Fin k) :
    ArgInvEmb k (i.succ.succ) = Sum.inl (i.succ.succ) := by
  simp only [ArgInvEmb, Fin.cases_succ]

/-- The composition of `Sum.elim v u` with the index embedding is exactly the fibre tuple
`(u 0, v 1, v 2, …, v (k+1))` of `Y`, i.e. `(argument, value, parameters) = (u 0, v 1, c)`. -/
theorem argInvEmb_comp (k : ℕ) (v : Fin (k + 2) → ℝ) (u : Fin 1 → ℝ) :
    (Sum.elim v u) ∘ (ArgInvEmb k) =
      Fin.cons (u 0) (Fin.cons (v 1) (fun i : Fin k => v i.succ.succ)) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [Function.comp_apply, argInvEmb_zero, Sum.elim_inr, Fin.cons_zero]
  · intro j'
    refine Fin.cases ?_ ?_ j'
    · simp only [Function.comp_apply, argInvEmb_one, Sum.elim_inl, Fin.cons_zero, Fin.cons_succ]
    · intro i
      simp only [Function.comp_apply, argInvEmb_succ_succ, Sum.elim_inl, Fin.cons_succ]

/-! ## 2. The argument-inverted family -/

/-- The *argument-inverted* family: `v ∈ ArgInv Y` iff `v` encodes `(x, y, c)` with some `w ≠ 0`
such that `w * x = 1` and `(w, y, c) ∈ Y`.  Equivalently the fibre of `ArgInv Y` at `(c, x)` is
the value of the fibre of `Y` at `(c, x⁻¹)` (and empty when `x = 0`).

The definition is written with the index embedding `ArgInvEmb` so that it is a finite-existential
projection of a polynomial preimage of `Y` (`argInv_definable`). -/
def ArgInv (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 2) → ℝ) :=
  {v | ∃ u : Fin 1 → ℝ, u 0 * v 0 = 1 ∧ (Sum.elim v u) ∘ (ArgInvEmb k) ∈ Y}

/-- Membership in `ArgInv Y` read on the free coordinates `(x, y, c)` of `v`. -/
theorem mem_argInv_iff (Y : Set (Fin (k + 2) → ℝ)) (v : Fin (k + 2) → ℝ) :
    v ∈ ArgInv Y ↔ ∃ u : Fin 1 → ℝ, u 0 * v 0 = 1 ∧
      Fin.cons (u 0) (Fin.cons (v 1) (fun i : Fin k => v i.succ.succ)) ∈ Y := by
  unfold ArgInv
  constructor
  · rintro ⟨u, h1, h2⟩
    exact ⟨u, h1, by rwa [argInvEmb_comp] at h2⟩
  · rintro ⟨u, h1, h2⟩
    exact ⟨u, h1, by rwa [argInvEmb_comp]⟩

/-- Membership in `ArgInv Y` for a fibre tuple, in the coordinates used by `Y`. -/
theorem mem_argInv_cons_iff (Y : Set (Fin (k + 2) → ℝ)) (x y : ℝ) (c : Fin k → ℝ) :
    (Fin.cons x (Fin.cons y c) : Fin (k + 2) → ℝ) ∈ ArgInv Y ↔
      ∃ u : Fin 1 → ℝ, u 0 * x = 1 ∧ Fin.cons (u 0) (Fin.cons y c) ∈ Y := by
  rw [mem_argInv_iff]
  simp only [Fin.cons_one, Fin.cons_zero, Fin.cons_succ]

/-- **The graph relation of the argument-inverted family.**  `Gr (ArgInv Y) c x y` iff `x ≠ 0`
and `y` is a value of the fibre of `Y` at `(c, x⁻¹)`. -/
theorem gr_argInv_iff (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x y : ℝ) :
    Gr (ArgInv Y) c x y ↔ x ≠ 0 ∧ Gr Y c x⁻¹ y := by
  show Fin.cons x (Fin.cons y c) ∈ ArgInv Y ↔ x ≠ 0 ∧ Fin.cons x⁻¹ (Fin.cons y c) ∈ Y
  rw [mem_argInv_cons_iff]
  constructor
  · rintro ⟨u, hux, hY⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hux
      exact zero_ne_one hux
    have hu : u 0 = x⁻¹ := eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact hux)
    exact ⟨hx0, by simpa [hu] using hY⟩
  · rintro ⟨hx0, hY⟩
    exact ⟨fun _ : Fin 1 => x⁻¹, by simp [inv_mul_cancel₀ hx0], by simpa using hY⟩

/-- The argument-inverted family is a family of graphs as soon as `Y` is. -/
theorem argInv_functional {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y') :
    ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr (ArgInv Y) c x y → Gr (ArgInv Y) c x y' → y = y' := by
  intro c x y y' hy hy'
  rw [gr_argInv_iff] at hy hy'
  exact hfun c x⁻¹ y y' hy.2 hy'.2

end Work.WilC4
