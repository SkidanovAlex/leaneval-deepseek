import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRDefs
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ## Locality of `bslOp α` on an arbitrary open set

`Work.Elliptic.bslOp α Ψ` is built from the operators `∂_z`, `∂_z²`, `∂_θ²` and the
θ-derivative of `tan θ · Ψ`, together with pointwise evaluation of `Ψ`.  Each is local:
if two functions agree on an open set `V`, their `z`- and `θ`-derivatives agree there too
(`Work.Spaces.pz_congr_of_isOpen`, `Work.Spaces.pth_congr_of_isOpen`, iterated below).
Hence `bslOp α φ` and `bslOp α g` agree on `V` whenever `φ` and `g` do.

The iterated version is the only place where openness (rather than mere pointwise
agreement) is used: the derivative at a point only sees a neighbourhood of that point. -/

/-- Functions agreeing on an open set have the same iterated `z`-derivatives there. -/
lemma pzIter_congr_of_isOpen_aux {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pzIter k f))
      (Function.uncurry (Work.Spaces.pzIter k g)) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      exact Work.Spaces.pz_congr_of_isOpen hV ih hy

/-- Functions agreeing on an open set have the same iterated `θ`-derivatives there. -/
lemma pthIter_congr_of_isOpen_aux {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter k f))
      (Function.uncurry (Work.Spaces.pthIter k g)) V := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      exact Work.Spaces.pth_congr_of_isOpen hV ih hy

/-- Multiplication by `tan θ` preserves agreement on an open set. -/
lemma tan_mul_eqOn_of_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (fun z θ => Real.tan θ * f z θ))
      (Function.uncurry (fun z θ => Real.tan θ * g z θ)) V := by
  intro p hp
  have hp' : f p.1 p.2 = g p.1 p.2 := h hp
  simp only [Function.uncurry]
  rw [hp']

/-- `Work.Elliptic.Lzero` is local on an open set. -/
lemma Lzero_congr_of_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (Work.Elliptic.Lzero f))
      (Function.uncurry (Work.Elliptic.Lzero g)) V := by
  intro y hy
  obtain ⟨z, θ⟩ := y
  have h0 : f z θ = g z θ := h hy
  have h2 : Work.Spaces.pthIter 2 f z θ = Work.Spaces.pthIter 2 g z θ :=
    pthIter_congr_of_isOpen_aux hV h 2 hy
  have h3 : Work.Spaces.pth (fun z θ => Real.tan θ * f z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z θ :=
    Work.Spaces.pth_congr_of_isOpen hV (tan_mul_eqOn_of_isOpen h) hy
  simp only [Function.uncurry, Work.Elliptic.Lzero, h0, h2, h3]

/-- **`bslOp α` is local on an open set**: functions agreeing on an open `V ⊆ ℝ²` have the same
`bslOp α` on `V`. -/
theorem bslOp_congr_of_isOpen {α : ℝ} {φ g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry φ) (Function.uncurry g) V) :
    Set.EqOn (Function.uncurry (Work.Elliptic.bslOp α φ))
      (Function.uncurry (Work.Elliptic.bslOp α g)) V := by
  intro y hy
  obtain ⟨z, θ⟩ := y
  have h1 : Work.Spaces.pz φ z θ = Work.Spaces.pz g z θ :=
    Work.Spaces.pz_congr_of_isOpen hV h hy
  have h2 : Work.Spaces.pzIter 2 φ z θ = Work.Spaces.pzIter 2 g z θ :=
    pzIter_congr_of_isOpen_aux hV h 2 hy
  have h4 : Work.Elliptic.Lzero φ z θ = Work.Elliptic.Lzero g z θ :=
    Lzero_congr_of_isOpen hV h hy
  simp only [Function.uncurry, Work.Elliptic.bslOp_apply, h1, h2, h4]

end Work.EllipticEst.InteriorRegularity.Q0
