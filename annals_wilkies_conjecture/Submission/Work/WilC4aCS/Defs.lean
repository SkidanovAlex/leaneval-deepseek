/-
  WilC4aCS -- area C4a's curve-selection induction step (`C4a_CS_step`).

  Route (see the lead's DESIGN.md, step 2): the induction step `CurveSel n -> CurveSel (n+1)`.
  No square systems, no resultants, no Lojasiewicz.

  * If the defining function `F` is not identically zero near `0`, apply simultaneous real
    Weierstrass preparation (`RealWeierstrass`) in a generic linear coordinate `L`; the basic
    semianalytic set becomes sign conditions on monic polynomials in the last variable whose
    coefficients are analytic functions of the first `n` variables.  Reading the coefficients as
    free parameters, Tarski-Seidenberg (`TS1`) gives a semialgebraic description of the base; a
    DNF disjunct yields a basic semianalytic set `W` in `R^n` with `0` in its closure, and
    `CurveSel n` produces a base arc `γ'` inside `W`.  Lifting back over `γ'` with the sign-vector
    form of real Puiseux (`ArcLift`) produces the last coordinate `ζ` with `ζ 0 = 0`, and
    `γ r = L (γ'(r^N), ζ r)` is the required analytic arc.
  * If `F` *is* identically zero near `0` (so only inequalities remain) we manufacture an
    equation: for a small radius we maximise `ψ = ∏ gⱼ` (or `(1+x₀)·∏ gⱼ` in the degenerate case)
    over the closed ball intersected with `{g ≥ 0}`.  The maximiser has all `gⱼ > 0` and satisfies
    the Lagrange/Fermat condition, hence lies on `{rotSq ψ = 0}`, and it tends to `0`.  So
    `{rotSq ψ = 0} ∩ Y` still accumulates at `0` and we are reduced to the first case.
  * Dimension `1` with `F =ᶠ 0` is the one case the maximiser trick cannot see (there are no
    rotation directions and no last-variable to solve for); there the signs of the `gⱼ` are
    constant on each side of `0` and `0 ∈ closure {g > 0}` forces one whole side to lie in `Y`.

  Everything here is stated for the frozen vocabulary of
  `Submission/Work/Wilkies/CG/C4a/Spec.lean`.
-/
import Submission.Work.Wilkies.CG.C4a.Spec

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4aCS

open WilkiesDesign.CG.C4a
open WilkiesDesign.E

/-! ## 1. Directional derivatives and the radial-orthogonality defect -/

/-- The directional derivative `v ↦ ∂_v ψ` at the point `x`, as a function of `x`. -/
def ddir {m : ℕ} (ψ : (Fin m → ℝ) → ℝ) (v : Fin m → ℝ) : (Fin m → ℝ) → ℝ :=
  fun x => fderiv ℝ ψ x v

/-- The radial-orthogonality defect `Σ_{a,b} (x_a ∂_b ψ − x_b ∂_a ψ)²`.  It vanishes exactly where
`∇ψ` is parallel to `x` (Lagrange at a constrained critical point on a sphere) or where `∇ψ = 0`
(Fermat at an unconstrained critical point).  Both orders `(a,b)` and `(b,a)` occur, so this is
`2 · Σ_{a<b}`; the diagonal terms vanish. -/
def rotSq {m : ℕ} (ψ : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ p : Fin m × Fin m,
    (x p.1 * ddir ψ (Pi.single p.2 1) x - x p.2 * ddir ψ (Pi.single p.1 1) x) ^ 2

/-- The `(a,b)` summand of `rotSq`. -/
def rotTerm {m : ℕ} (ψ : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) (a b : Fin m) : ℝ :=
  x a * ddir ψ (Pi.single b 1) x - x b * ddir ψ (Pi.single a 1) x

lemma rotSq_eq_sum (m : ℕ) (ψ : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) :
    rotSq ψ x = ∑ p : Fin m × Fin m, rotTerm ψ x p.1 p.2 ^ 2 := rfl

/-! ## 2. Coefficient bookkeeping for Weierstrass preparation -/

/-- Flattened index of the coefficient `(i,j)` in `Σᵢ dᵢ`-dimensional coefficient space. -/
def coefIdx {K : ℕ} (d : Fin K → ℕ) (i : Fin K) (j : Fin (d i)) : Fin (∑ i, d i) :=
  finSigmaFinEquiv ⟨i, j⟩

/-- The value of the monic polynomial `z^{dᵢ} + Σ_j A_{ij} z^j` attached to the coefficient
vector `A` and the value `z` of the last variable. -/
def Qeval {K : ℕ} (d : Fin K → ℕ) (A : Fin (∑ i, d i) → ℝ) (z : ℝ) (i : Fin K) : ℝ :=
  z ^ (d i) + ∑ j : Fin (d i), A (coefIdx d i j) * z ^ (j : ℕ)

/-- The coefficient vector of a Weierstrass family `a`, as a function of the first `n` variables. -/
def coefFun {n K : ℕ} (d : Fin K → ℕ) (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → Fin (∑ i, d i) → ℝ :=
  fun x t => a (finSigmaFinEquiv.symm t).1 (finSigmaFinEquiv.symm t).2 x

/-- The Weierstrass variable (`z`) as a variable of the coefficient space `Fin (D+1)`. -/
def zIdx (D : ℕ) : Fin (D + 1) := Fin.last D

/-- A coefficient coordinate embedded in `Fin (D+1)`. -/
def cIdx {D : ℕ} (t : Fin D) : Fin (D + 1) := t.castSucc

/-- The monic polynomial `z^{dᵢ} + Σ_j X_{ij} z^j` in the `D+1` variables
`(X_{ij}, z)`, as an element of `EAPoly (D+1) 0`. -/
def Qpoly {K : ℕ} (d : Fin K → ℕ) (i : Fin K) : EAPoly (∑ i, d i + 1) 0 :=
  MvPolynomial.X (Sum.inl (zIdx (∑ i, d i))) ^ (d i) +
    ∑ j : Fin (d i),
      MvPolynomial.X (Sum.inl (cIdx (coefIdx d i j))) *
        MvPolynomial.X (Sum.inl (zIdx (∑ i, d i))) ^ (j : ℕ)

/-- The sign `±1` of a nonzero real number. -/
def posSign (c : ℝ) : ℝ := if 0 < c then 1 else -1

/-- The semialgebraic set in coefficient space: `Q₀ = 0` together with `τⱼ · Q_{j+1} > 0`.
This is the Tarski-Seidenberg input of the induction step. -/
def SAcoef (l : ℕ) (d : Fin (l + 1) → ℕ) (τ : Fin l → ℝ) : E.SA (∑ i, d i + 1) :=
  ⟨[⟨[Qpoly d 0],
      List.ofFn (fun j : Fin l => MvPolynomial.C (τ j) * Qpoly d (Fin.succ j))⟩]⟩

/-- Evaluation of an `EAPoly (D) 0` (semialgebraic atom) at a point of `R^D`. -/
def ev0 {D : ℕ} (v : Fin D → ℝ) (p : EAPoly D 0) : ℝ :=
  MvPolynomial.eval (Sum.elim v (fun _ : Fin 0 => (0 : ℝ))) p

/-- The base of the lift: the set of `y` whose coefficient vector and last coordinate satisfy the
sign conditions in coefficient space. -/
def Yw {n l : ℕ} (d : Fin (l + 1) → ℕ) (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (τ : Fin l → ℝ) :
    Set (Fin (n + 1) → ℝ) :=
  {y | Fin.snoc (coefFun d a (Fin.init y)) (y (Fin.last n)) ∈ (SAcoef l d τ).set}

/-- The corresponding set in the original coordinates, i.e. `Yw` pulled back by `L`. -/
def YwL {n l : ℕ} (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (d : Fin (l + 1) → ℕ) (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (τ : Fin l → ℝ) :
    Set (Fin (n + 1) → ℝ) :=
  {x | L.symm x ∈ Yw d a τ}

/-- The set of points of `R^D` satisfying one `Basic` atom family over the trivial chain. -/
def BSet {D : ℕ} (B : Basic D 0) : Set (Fin D → ℝ) := {v | B.holds (EAChain.nil D) v}

/-- The base set in `R^n` attached to a coefficient map and a semialgebraic family. -/
def Base {n l : ℕ} (d : Fin (l + 1) → ℕ) (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ)
    (B : Basic (∑ i, d i) 0) : Set (Fin n → ℝ) :=
  coefFun d a ⁻¹' BSet B

/-! ## 3. Curve selection at the origin -/

/-- Curve selection for data analytic at the origin.  `CurveSel m` follows from `CurveSelAt0 m` by
translation, and conversely. -/
def CurveSelAt0 (m : ℕ) : Prop :=
  ∀ (l : ℕ) (F : (Fin m → ℝ) → ℝ) (g : Fin l → (Fin m → ℝ) → ℝ),
    AnalyticAt ℝ F 0 → (∀ j, AnalyticAt ℝ (g j) 0) → (0 : Fin m → ℝ) ∈ closure (BasicSA F g) →
    ∃ γ : ℝ → (Fin m → ℝ), AnalyticAt ℝ γ 0 ∧ γ 0 = 0 ∧
      ∃ ε > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) ε, γ s ∈ BasicSA F g

/-- Curve selection at the origin in the *reduced* case: all inequality functions vanish at the
origin (the ones positive there are harmless and are added back by continuity). -/
def CurveSelAt0Red (m : ℕ) : Prop :=
  ∀ (l : ℕ) (F : (Fin m → ℝ) → ℝ) (g : Fin l → (Fin m → ℝ) → ℝ),
    AnalyticAt ℝ F 0 → (∀ j, AnalyticAt ℝ (g j) 0) → (∀ j, g j 0 = 0) →
    (0 : Fin m → ℝ) ∈ closure (BasicSA F g) →
    ∃ γ : ℝ → (Fin m → ℝ), AnalyticAt ℝ γ 0 ∧ γ 0 = 0 ∧
      ∃ ε > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) ε, γ s ∈ BasicSA F g

end Work.WilC4aCS
