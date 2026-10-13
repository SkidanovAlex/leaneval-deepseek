import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Count.Defs

/-!
# Area H (counting) — the two interfaces of the §6 induction

The counting induction of BNZ §6 (`WilkiesH/ARCHITECTURE.md` §7.4) is split here into

* `ChartCover S F n` — **the output of the interpolation step** (BNZ Prop. 6.1): for a set
  `X ∈ S.Ω F D n` contained in `cube01 n` with `DimLE X μ`, and for the points of bounded
  degree `g` and height `H` in `X`, a covering by at most `p(D,g,log H)` sets, each
  `Ω`-definable with a fixed format `a` and a degree bounded by `q(D,g,log H)`, each of
  dimension `≤ μ`.  This is what the Siegel–Wilkie/determinant work produces (the `V i`
  are the intersections `⋂_J {P_J ∘ π_J = 0}` of the per-chart hypersurfaces);

* `CountBoundDimCube S F n μ` — the *cube-restricted* counting statement, i.e.
  `CountBoundDim` with the extra hypothesis `X ⊆ cube01 n`.  The induction step
  (`Count/step_cube`, delegated) proves this from `SharpCD`, the block input
  `CellSemialgWitness` and `ChartCover`; the normalisation (`Norm/`) then removes the cube
  hypothesis to give `CountBoundDim` itself.

Since `dim X ≤ n` and `DimLE X n` is vacuous, `CountBoundDim S F n n` is the lead's
`CountBound S F n` (`Count.countBound_of_countBoundDim`).
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH

open WilkiesDesign WilkiesConjecture

/-- **The interface produced by the interpolation step** (BNZ Prop. 6.1), in the form the
counting induction consumes: a cover of the `(g,H)`-points of `X` by polynomially many
`Ω`-sets of dimension `≤ μ` and controlled format/degree.

The format `a` is a constant (independent of `D, g, H`), while both the number of pieces
and their degree index are bounded by polynomials in `(D, g, log H)`.

The pieces are moreover required to be *semialgebraic*: in the intended instantiation they
are finite intersections `⋂_J {P_J ∘ π_J = 0}` of hypersurface zero sets.  The block input
`CellSemialgWitness` needs this (a cell inside the semialgebraic `V i` of dimension `≤ μ`
and of exact dimension `μ` lies in `X.alg`); `Ω`-membership alone would not suffice. -/
def ChartCover (S : SOMin) (F n : ℕ) : Prop :=
  ∃ (a : ℕ) (p q : MvPolynomial (Fin 3) ℝ),
    ∀ (D : ℕ) (X : Set (Fin n → ℝ)) (μ : ℕ), μ ≤ n → X ∈ S.Ω F D n → X ⊆ cube01 n →
      DimLE X μ →
      ∀ (g H : ℕ) (T : Finset (Fin n → ℝ)), (↑T : Set (Fin n → ℝ)) ⊆ X →
        (↑T : Set (Fin n → ℝ)) ⊆ degreeHeightLE X g H →
        ∃ (m : ℕ) (V : Fin m → Set (Fin n → ℝ)) (d : ℕ),
          (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p ∧
          (d : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ∧
          (∀ i, V i ∈ S.Ω a d n) ∧ (∀ i, DimLE (V i) μ) ∧
          (∀ i, IsSemialgebraic (V i)) ∧
          (↑T : Set (Fin n → ℝ)) ⊆ ⋃ i, V i

/-- **The interpolation step, per chart** (BNZ Prop. 6.1): the statement the
Siegel–Wilkie/determinant work must produce.  For every chart `φ : openCube μ → X` of a
set `X ∈ S.Ω F D n`, `X ⊆ cube01 n`, `DimLE X μ`, and every `(μ+1)`-element list `e` of
coordinates, there is a nonzero polynomial `P` in `μ+1` variables, of degree `≤ d` and
vanishing at `x|_e` for every `x ∈ degreeHeightLE X g H` within `ε` of the chart image.
The parameters `d`, `r` (the smoothness used) and `log (1/ε)` are all bounded by one
polynomial in `(D, g, log H)`.  (The bound on `log (1/ε)`, rather than on `1/ε`, is what the
arguments of §7.2 produce: `ε` is exponentially small in `poly(g, log H)`.)
-/
def InterpPerChart (S : SOMin) (F n : ℕ) : Prop :=
  ∃ q : MvPolynomial (Fin 3) ℝ,
    ∀ (D μ : ℕ) (X : Set (Fin n → ℝ)), μ ≤ n → X ∈ S.Ω F D n → X ⊆ cube01 n → DimLE X μ →
      ∀ (g H : ℕ),
        ∃ (d r : ℕ) (ε : ℝ),
          0 < ε ∧ ε < 1 ∧
          (d : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ∧
          (r : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ∧
          Real.log (1 / ε) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] q ∧
          ∀ (φ : (Fin μ → ℝ) → (Fin n → ℝ)), (∀ t ∈ openCube μ, φ t ∈ X) →
            ContDiffOn ℝ r φ (openCube μ) →
            (∀ k ≤ r, ∀ t ∈ openCube μ, ‖iteratedFDeriv ℝ k φ t‖ ≤ 1) →
            ∀ (e : Fin (μ + 1) ↪ Fin n),
              ∃ P : MvPolynomial (Fin (μ + 1)) ℝ, P ≠ 0 ∧ P.totalDegree ≤ d ∧
                ∀ x : Fin n → ℝ, x ∈ degreeHeightLE X g H →
                  (∃ t ∈ openCube μ, dist (φ t) x < ε) →
                  MvPolynomial.eval (fun i : Fin (μ + 1) => x (e i)) P = 0

/-- The counting statement `CountBoundDim` with the additional hypothesis
`X ⊆ cube01 n` — the form in which the induction step is proved (the normalisation of
`Norm/` reduces the general statement to it). -/
def CountBoundDimCube (S : SOMin) (F n μ : ℕ) : Prop :=
  ∃ f : MvPolynomial (Fin 3) ℝ,
    ∀ (D : ℕ) (X : Set (Fin n → ℝ)), X ∈ S.Ω F D n → X ⊆ cube01 n → DimLE X μ →
      ∀ (g H : ℕ) (T : Finset (Fin n → ℝ)),
        (↑T : Set (Fin n → ℝ)) ⊆ degreeHeightLE X.trans g H →
        (T.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] f

/-- Forgetting the cube hypothesis: `CountBoundDim` implies `CountBoundDimCube`. -/
theorem countBoundDimCube_of_countBoundDim {S : SOMin} {F n μ : ℕ}
    (h : CountBoundDim S F n μ) : CountBoundDimCube S F n μ := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun D X hX _ hdim g H T hT => hf D X hX hdim g H T hT⟩

end Work.WilkiesH
