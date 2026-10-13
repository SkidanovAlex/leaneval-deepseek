/-
  Area E7, module `Submission.Work.WilE7.Deg.Seq`: the *bookkeeping vocabulary* of the degree/count
  version of BV's fibre-cutting recursion (`Work.WilE7.cover_cut_deg`).

  * the three frozen interfaces `E2Interface`, `E5Interface`, `E6Interface` (definitionally the
    hypotheses of the target);
  * `cdpoly`/`cdspec`: the degree bound for `critSet` (from `Work.WilE7.critSet_deg_bound_Sdeg`);
  * the chosen bounds `e5fmt`/`e5deg`/`e6fmt`/`e6deg` extracted from `hE5`/`hE6`;
  * the iterated *format* sequence `fmtSeq` (`F ↦ max F (a5 F) (a5 (a6 F))`) and *degree* sequence
    `degSeq` (`p ↦ p + chpoly F p`), the budget-indexed versions `Fb`, `Pb`, the child bound `brB`
    and the accumulated count bound `Kb`.

  All parameters are written explicitly (no section variables) so that the signatures are
  predictable.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.critSet_deg_bound_Sdeg

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The three frozen interfaces -/

/-- `E2`: an EA semi-Pfaffian set has polynomially many connected components. -/
abbrev E2Interface : Prop :=
  ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
    ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
      ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y

/-- `E5`: fibrewise weak stratification with polynomially many strata. -/
abbrev E5Interface : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
    X.fmt ≤ F →
    ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
      (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
      X.set = (⋃ S ∈ L, S.X.set) ∧
      L.Pairwise (fun S T => Disjoint S.X.set T.X.set)

/-- `E6`: fibrewise closure and frontier of an EA set. -/
abbrev E6Interface : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
    X.fmt ≤ F →
    ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
      Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
      Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set

/-! ## The degree bound for `critSet` -/

/-- The polynomial bound for the degree of a fibre-critical set, chosen from
`Work.WilE7.critSet_deg_bound_Sdeg`. -/
noncomputable def cdpoly (F : ℕ) : Polynomial ℕ := (critSet_deg_bound_Sdeg F).choose

/-- The specification of `cdpoly`. -/
theorem cdspec (F : ℕ) :
    ∀ (p q : ℕ) (S : Stratum p q), S.X.fmt ≤ F → S.j ≤ q → S.X.basics.length ≤ S.X.deg + 1 →
      ∀ l : Fin q, (critSet S l).deg ≤ (cdpoly F).eval S.deg :=
  (critSet_deg_bound_Sdeg F).choose_spec

/-! ## The chosen bounds and the iterated sequences -/

/-- The format bound chosen for `E5` at bound `F`. -/
noncomputable def e5fmt (hE5 : E5Interface) (F : ℕ) : ℕ := (hE5 F).choose

/-- The degree/count polynomial chosen for `E5` at bound `F`. -/
noncomputable def e5deg (hE5 : E5Interface) (F : ℕ) : Polynomial ℕ := (hE5 F).choose_spec.choose

/-- The format bound chosen for `E6` at bound `F`. -/
noncomputable def e6fmt (hE6 : E6Interface) (F : ℕ) : ℕ := (hE6 F).choose

/-- The degree polynomial chosen for `E6` at bound `F`. -/
noncomputable def e6deg (hE6 : E6Interface) (F : ℕ) : Polynomial ℕ :=
  (hE6 F).choose_spec.choose

/-- The specification of `e5fmt`/`e5deg`. -/
theorem e5spec (hE5 : E5Interface) (F : ℕ) :
    ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ L : List (Stratum p q), L.length ≤ (e5deg hE5 F).eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ e5fmt hE5 F ∧ S.deg ≤ (e5deg hE5 F).eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set) :=
  (hE5 F).choose_spec.choose_spec

/-- The specification of `e6fmt`/`e6deg`. -/
theorem e6spec (hE6 : E6Interface) (F : ℕ) :
    ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ e6fmt hE6 F ∧ Y.deg ≤ (e6deg hE6 F).eval X.deg ∧
        Y'.fmt ≤ e6fmt hE6 F ∧ Y'.deg ≤ (e6deg hE6 F).eval X.deg ∧
        Y.set = fiberClosure X.set ∧ Y'.set = fiberClosure X.set \ X.set :=
  (hE6 F).choose_spec.choose_spec

/-- One round of the format iteration. -/
noncomputable def fmtStep (hE5 : E5Interface) (hE6 : E6Interface) (F : ℕ) : ℕ :=
  max F (max (e5fmt hE5 F) (e5fmt hE5 (e6fmt hE6 F)))

/-- The format bound after `t` rounds, starting from `A₀`. -/
noncomputable def fmtSeq (hE5 : E5Interface) (hE6 : E6Interface) (A₀ : ℕ) : ℕ → ℕ
  | 0 => A₀
  | (t + 1) => fmtStep hE5 hE6 (fmtSeq hE5 hE6 A₀ t)

/-- The degree/count step of the recursion: it keeps the previous bound and adds a polynomial
dominating both the frontier children (`e5 (a6 F) ∘ e6 F`) and the critical children
(`(A₀+1) · e5 F ∘ cd F`). -/
noncomputable def chpoly (hE5 : E5Interface) (hE6 : E6Interface) (A₀ : ℕ) (F : ℕ)
    (p : Polynomial ℕ) : Polynomial ℕ :=
  (e5deg hE5 (e6fmt hE6 F)).comp ((e6deg hE6 F).comp p)
    + Polynomial.C (A₀ + 1) * ((e5deg hE5 F).comp ((cdpoly F).comp p)) + 1

/-- The degree step of the recursion. -/
noncomputable def degStep (hE5 : E5Interface) (hE6 : E6Interface) (A₀ : ℕ) (F : ℕ)
    (p : Polynomial ℕ) : Polynomial ℕ := p + chpoly hE5 hE6 A₀ F p

/-- The degree bound after `t` rounds. -/
noncomputable def degSeq (hE5 : E5Interface) (hE6 : E6Interface) (A₀ : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | (t + 1) => degStep hE5 hE6 A₀ (fmtSeq hE5 hE6 A₀ t) (degSeq hE5 hE6 A₀ t)

/-- The format bound with `k` rounds *remaining*. -/
noncomputable def Fb (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ : ℕ) (k : ℕ) : ℕ :=
  fmtSeq hE5 hE6 A₀ (k₀ - k)

/-- The degree bound with `k` rounds *remaining*. -/
noncomputable def Pb (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ : ℕ) (k : ℕ) :
    Polynomial ℕ := degSeq hE5 hE6 A₀ (k₀ - k)

/-- The child bound (degree *and* count) at a round with format bound `Fb j` and degree polynomial
`Pb j`. -/
noncomputable def brB (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ : ℕ) (j : ℕ) :
    Polynomial ℕ :=
  chpoly hE5 hE6 A₀ (Fb hE5 hE6 A₀ k₀ j) (Pb hE5 hE6 A₀ k₀ j)

/-- The accumulated count bound after `j` rounds. -/
noncomputable def Kb (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ : ℕ) : ℕ → Polynomial ℕ
  | 0 => 1
  | (j + 1) => brB hE5 hE6 A₀ k₀ (j + 1) * Kb hE5 hE6 A₀ k₀ j

end Work.WilE7
