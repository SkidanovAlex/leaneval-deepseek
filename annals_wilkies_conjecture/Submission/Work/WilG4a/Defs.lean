/-
  WilG4a : area G4a of the Wilkie/Pfaffian project (BNZ §5.1, the `n = 1` base case).

  Vocabulary.  The frozen `FLem S p n` (`Submission.Work.Wilkies.CG.Spec`) lives in
  coordinates `Fin p → ℝ` (parameters), `Fin n → ℝ` (variables), `Fin k → ℝ` (values).
  For the one-variable case `n = 1` it is much more convenient to work with plain real
  variables `ℝ`, and to use the `iteratedDeriv`/`ContDiffOn` API of Mathlib on `ℝ`.

  This file introduces the `ℝ`-coordinate versions `FLem1`, `FLem1On`, `F1Affine1` of
  `FLem S p 1` and `F1Affine S p`, the graph `graphFam` of a one-parameter family, and the
  chart predicate `ChartOK` that both statements are built from.
-/
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

/-- The open unit interval `I = (0,1)`. -/
abbrev I : Set ℝ := Set.Ioo 0 1

/-- Case-split (`if-then-else`) function, defined classically so that the graph of a
piecewise-defined chart can be analysed as a set. -/
noncomputable def iteFun {α : Type*} {β : Sort*} (P : Set α) (f g : α → β) (l : α) : β :=
  if l ∈ P then f l else g l

/-- Graph of a family `f : ℝᵖ × ℝ → ℝ`, as a subset of `ℝ^{p+2}`
(coordinates: `p` parameters, then the variable `x`, then the value `y`).
This is the `n = 1` case of the frozen `famGraph`. -/
def graphFam {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 1 + 1) → ℝ) :=
  graphOf (fun z : Fin (p + 1) → ℝ => f (fun i => z (Fin.castSucc i)) (z (Fin.last p)))

theorem mem_graphFam {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (z : Fin (p + 1 + 1) → ℝ) :
    z ∈ graphFam f ↔
      z (Fin.last (p + 1)) = f (fun i => z (Fin.castSucc (Fin.castSucc i)))
        (z (Fin.castSucc (Fin.last p))) := by
  simp only [graphFam, graphOf, Set.mem_ofPred_eq, Fin.init]

@[simp] theorem mem_graphFam_iff {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ)
    (l : Fin p → ℝ) (x y : ℝ) :
    Fin.snoc (Fin.snoc l x) y ∈ graphFam f ↔ y = f l x := by
  rw [mem_graphFam]
  simp

/-! ## The chart predicate -/

/-- The per-chart conditions of the `n = 1` family lemma: the graph of the chart is
`Ω`-definable with the prescribed format `a` and degree `bD`; the chart maps the cube into
the cube; and along the chart all derivatives of order `≤ r` of every composite
`x ↦ Fᵢ(l, x)` are bounded by `1` on `I`. -/
def ChartOK (S : SOMin) {p : ℕ} (a bD : ℕ) (Λ : Set (Fin p → ℝ)) (k r : ℕ)
    (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (φ : (Fin p → ℝ) → ℝ → ℝ) : Prop :=
  graphFam φ ∈ S.Ω a bD (p + 1 + 1) ∧
    ∀ l ∈ Λ, (∀ t ∈ I, φ l t ∈ I) ∧
      ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (φ l t)) I ∧
        ∀ m ≤ r, ∀ t ∈ I, |iteratedDeriv m (fun t : ℝ => F i l (φ l t)) t| ≤ 1

/-- The coverage condition of the `n = 1` family lemma. -/
def Covers {p : ℕ} (Λ : Set (Fin p → ℝ)) (k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ)
    (Φ : Finset ((Fin p → ℝ) → ℝ → ℝ)) (ε : ℝ) : Prop :=
  ∀ l ∈ Λ, ∀ x ∈ I, ∃ φ ∈ Φ, ∃ t ∈ I, ∀ i, |F i l (φ l t) - F i l x| < ε

/-- **The `n = 1` family lemma (BNZ Lemma 5.1, `n = 1`), in `ℝ`-coordinates**, restricted
to the parameter set `Λ`.  Every `l ∈ Λ` carries a finite collection of charts whose graphs
are `Ω`-definable with format/degree depending only on `F0` and `D` (resp. `D`, `r`), whose
size is polynomially bounded in `D, r, k, |log ε|`, and which `ε`-covers the image of the
family at `l`. -/
def FLem1On (S : SOMin) (p : ℕ) (F0 : ℕ) (Λ : Set (Fin p → ℝ)) : Prop :=
  ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
      (∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F i l x ∈ I) →
      ∃ Φ : Finset ((Fin p → ℝ) → ℝ → ℝ),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ φ ∈ Φ, ChartOK S a (MvPolynomial.eval ![D, r] b) Λ k r F φ) ∧
        Covers Λ k F Φ ε

/-- The `n = 1` family lemma, free of `Λ`: the bounds `(a, b, c)` may depend on `F0` only,
not on the parameter set `Λ`. -/
def FLem1 (S : SOMin) (p : ℕ) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
      (∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F i l x ∈ I) →
      ∃ Φ : Finset ((Fin p → ℝ) → ℝ → ℝ),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ φ ∈ Φ, ChartOK S a (MvPolynomial.eval ![D, r] b) Λ k r F φ) ∧
        Covers Λ k F Φ ε

/-- **BNZ Corollary 5.5 (`n = 1`), in `ℝ`-coordinates**: affine charts `x = α l + β l · t`
with `Ω`-definable coefficients, giving an `ε`-cover of the *domain* `I`. -/
def F1Affine1 (S : SOMin) (p : ℕ) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
      (∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F i l x ∈ I) →
      ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ αβ ∈ Φ, graphOf αβ.1 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          graphOf αβ.2 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          ∀ l ∈ Λ, 0 < αβ.2 l ∧ 0 ≤ αβ.1 l ∧ αβ.1 l + αβ.2 l ≤ 1 ∧
            ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) I ∧
              ∀ m ≤ r, ∀ t ∈ I,
                |iteratedDeriv m (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) t| ≤ 1) ∧
        ∀ l ∈ Λ, ∀ x ∈ I, ∃ αβ ∈ Φ, ∃ t ∈ I, |αβ.1 l + αβ.2 l * t - x| < ε

end Work.WilG4a
