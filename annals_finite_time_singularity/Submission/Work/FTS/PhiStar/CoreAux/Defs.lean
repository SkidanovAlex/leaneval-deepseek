/-
# `FTS/PhiStar/CoreAux/Defs.lean` — the flat class of the `StarCore` → `StarPkgo2` route

`VocabO2.StarCore α Cs Φs` supplies a single analytic input,
`core : FlatW 7 (Ycheck α Φs) (Cs·α)`, i.e. bounds on

* `(z+1)^k ∂_z^k Y` (`k ≤ 7`) and
* `(z+1)^k ∂_z^k D_θ^i (∂_θ Y)` (`k+i+1 ≤ 7`)

on the open quadrant, for `Y = Ŷ = Ycheck α Φs = ((z+1)/z)·(Φ̃_*/σ)`, `σ = sin 2θ`.

The eleven fields of `StarPkgo2` are explicit algebraic combinations of `Ŷ` and its mixed
derivatives, so the proof goes by *flat calculus*: one class of functions whose
`(z+1)^k ∂_z^k D_θ^i`-derivatives are bounded on the open quadrant, closed under the
operations that occur (sums, products, multiplication by the bounded angular coefficients
`σ, sin²θ, cos 2θ, cos²θ - 2 sin²θ` and the radial coefficients `z/(z+1)`, `1/(z+1)`).

This file fixes the three classes used throughout:

* `F0 n K f` — `|(z+1)^k ∂_z^k D_θ^i f| ≤ K` on the open quadrant for `k + i ≤ n`
  (the *flat* class, with the `z`-weights of `Work.Spaces.WlInf` and of `FlatW`);
* `Fb n K f` — `F0` of `f` **and** of `∂_θ f` (the "shifted" pair, which is what the
  `WlInf` angular slot and the products need; it is the invariant class);
* `F0c n K f` — the closed-quadrant version used by `Work.Spaces.WlInf`.

Nothing here is a `sorry` or an axiom.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.VocabO2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The flat class on the open quadrant.**  `F0 n K f` says that all the mixed
`(z+1)^k ∂_z^k D_θ^i f` with `k + i ≤ n` are bounded by `K` on `Q0 = (0,∞)×(0,π/2)`. -/
def F0 (n : ℕ) (K : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ k i : ℕ, k + i ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ| ≤ K

/-- **The flat class on the closed quadrant** `[0,∞) × [0,π/2]` — the shape needed by
`Work.Spaces.WlInf`. -/
def F0c (n : ℕ) (K : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ k i : ℕ, k + i ≤ n → ∀ z θ : ℝ, 0 ≤ z → 0 ≤ θ → θ ≤ Real.pi / 2 →
    |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ| ≤ K

/-- **The invariant flat class**: `F0` of `f` together with `F0` of `∂_θ f`.  This pair is
what survives products (`F0` alone does not: the product rule for `∂_θ` needs the shifted
family) and it is exactly the data consumed by the `WlInf` angular slot. -/
structure Fb (n : ℕ) (K : ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  /-- flat bounds on `f` itself -/
  f0 : F0 n K f
  /-- flat bounds on `∂_θ f` -/
  fd : F0 n K (Work.Spaces.pth f)

/-! ## Elementary API -/

theorem F0.mono {n n' : ℕ} {K K' : ℝ} {f : ℝ → ℝ → ℝ} (hn : n ≤ n') (hK : K' ≤ K)
    (h : F0 n' K' f) : F0 n K f :=
  fun k i hki z θ hz hθ hθ' => le_trans (h k i (le_trans hki hn) z θ hz hθ hθ') hK

theorem F0c.mono {n n' : ℕ} {K K' : ℝ} {f : ℝ → ℝ → ℝ} (hn : n ≤ n') (hK : K' ≤ K)
    (h : F0c n' K' f) : F0c n K f :=
  fun k i hki z θ hz hθ hθ' => le_trans (h k i (le_trans hki hn) z θ hz hθ hθ') hK

theorem F0.of_F0c {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (h : F0c n K f) : F0 n K f :=
  fun k i hki z θ hz hθ hθ' => h k i hki z θ hz.le hθ.le hθ'.le

theorem Fb.mono {n n' : ℕ} {K K' : ℝ} {f : ℝ → ℝ → ℝ} (hn : n ≤ n') (hK : K' ≤ K)
    (h : Fb n' K' f) : Fb n K f :=
  ⟨h.f0.mono hn hK, h.fd.mono hn hK⟩

theorem Fb.of_both {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (h1 : F0 n K f)
    (h2 : F0 n K (Work.Spaces.pth f)) : Fb n K f :=
  ⟨h1, h2⟩

/-- `∂_z` of a function which does not depend on `z` is `0`, and so are all its iterates. -/
theorem pzIter_const_of_theta_only (d : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => d) = fun _ _ => 0 := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      funext z θ
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      rw [deriv_const]
    · rw [Work.Spaces.pzIter_succ, ih hn]
      funext z θ
      simp only [Work.Spaces.pz]
      rw [deriv_const]

/-- `D_θ^i` of a constant function is `0` for `i ≥ 1` and the constant itself for `i = 0`. -/
theorem DthIter_const (d : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => d) = fun _ _ => (if i = 0 then d else 0) := by
  induction i with
  | zero => funext z θ; simp
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const]
    simp

/-- The constant function belongs to the flat class. -/
theorem F0.const (n : ℕ) (c : ℝ) : F0 n |c| (fun _ _ => c) := by
  intro k i hki z θ hz hθ hθ'
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [DthIter_const]
    simp only [Work.Spaces.pzIter_zero, pow_zero, one_mul]
    split_ifs with hi
    · subst hi; simp
    · simp
  · rw [DthIter_const, pzIter_const_of_theta_only _ k hk]
    simp

end Work.FTS.PhiStar
