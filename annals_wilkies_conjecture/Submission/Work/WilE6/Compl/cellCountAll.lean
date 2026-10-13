/-
  WilE6 / Compl — `cellCountAll`: the number of nonempty sign cells of a `SemiPf` set of bounded
  format is bounded by a polynomial in its degree.

  `Work.WilE5.Cells.khovCount` proves this bound for the *good* cells (nonempty cells contained in
  `X.set`), which is what the `E5_strat` assembly feeds on.  The complement route needs the bound
  for an arbitrary finite family `T` of sign assignments whose cells are merely *nonempty*: the
  subset condition `cellSemiPf X σ ⊆ X.set` is never used in the Khovanskii–Gabrielov–Vorobjov
  argument, so the same proof gives the sharper statement.

  The argument (Gabrielov–Vorobjov; see `WilE5/Cells/khovCount`): let `f_i` be the atoms of `X`
  and pick a point `z_σ` in every nonempty cell `σ`.  Choose `ε > 0` below every nonzero
  `|f_i (z_σ)|`, put `g_i := (f_i + ε)² (f_i - ε)²` and `Z := {x ∈ cubeC : ∀ i, g_i x > 0}`, a
  semi-Pfaffian set of the same format as `X` and of degree `≤ 4 * X.deg`.  Each `z_σ` lies in `Z`;
  the intermediate value theorem on a component of `Z` shows that two different cells cannot share
  a component, since crossing from one sign regime to the other forces some `f_i` to take the value
  `± ε`, where `g_i = 0`.  The frozen hypothesis `E2` bounds the number of components of `Z` by
  `p.eval Z.deg`; the map `σ ↦` the component representative is injective, and the count follows.

  The two halves of that argument are `Cells.khovCellPt_mem`-style statements about the perturbed
  set, proved in the sibling modules of this directory: `cellPtKhovSet` (the chosen points of the
  nonempty cells lie in `Z`) and `cellPtCompsNe` (different cells, different components).
-/
import Mathlib
import Submission.Work.WilE5.Cells.khovCount
import Submission.Work.WilE5.Cells.cellBasic
import Submission.Work.WilE6.Compl.cellPtKhovSet
import Submission.Work.WilE6.Compl.cellPtCompsNe

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE6.Compl

open WilkiesDesign WilkiesDesign.E

theorem cellCountAll
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    (F : ℕ) :
    ∃ b : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∀ T : Finset (Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign),
        (∀ σ ∈ T, (Work.WilE5.cellSemiPf X σ).set.Nonempty) → T.card ≤ b.eval X.deg := by
  classical
  obtain ⟨p, hp⟩ := hE2 F
  refine ⟨p.comp (Polynomial.C 4 * Polynomial.X + Polynomial.C 1), ?_⟩
  intro k X hF T hTne
  -- the threshold `ε`, small enough at all the chosen cell points
  obtain ⟨ε, hεpos, hε⟩ := Work.WilE5.Cells.khovEps
    (fun q : Fin (Work.WilE5.atomsOf X).length ×
        (Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign) =>
      eaEval X.c ((Work.WilE5.atomsOf X).get q.1) (Work.WilE5.Cells.khovCellPt X q.2))
  have hsmall : ∀ (i : Fin (Work.WilE5.atomsOf X).length)
      (σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign),
      eaEval X.c ((Work.WilE5.atomsOf X).get i) (Work.WilE5.Cells.khovCellPt X σ) ≠ 0 →
      ε < |eaEval X.c ((Work.WilE5.atomsOf X).get i)
        (Work.WilE5.Cells.khovCellPt X σ)| := fun i σ h => hε (i, σ) h
  -- every chosen point lies in the perturbed set
  have hmem : ∀ σ ∈ T, Work.WilE5.Cells.khovCellPt X σ ∈
      (Work.WilE5.Cells.khovSet X ε).set :=
    fun σ hσ => cellPtKhovSet X hεpos hsmall (hTne σ hσ)
  -- distinct cells have chosen points in different components
  have hsep : ∀ σ ∈ T, ∀ τ ∈ T, σ ≠ τ →
      connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
          (Work.WilE5.Cells.khovCellPt X σ) ≠
        connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
          (Work.WilE5.Cells.khovCellPt X τ) :=
    fun σ hσ τ hτ hne => cellPtCompsNe X hεpos hsmall (hTne σ hσ) (hTne τ hτ) hne
  -- the perturbed set has the same format as `X`
  have hYfmt : (Work.WilE5.Cells.khovSet X ε).fmt ≤ F := hF
  obtain ⟨s, hscard, _hssub, hscov⟩ := hp k (Work.WilE5.Cells.khovSet X ε) hYfmt
  -- the covering map is injective on the nonempty cells of `T`
  have hex2 : ∀ σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign,
      ∃ y : Fin k → ℝ, (σ ∈ T → y ∈ s ∧
        connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
            (Work.WilE5.Cells.khovCellPt X σ) =
          connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set y) := by
    intro σ
    by_cases h : σ ∈ T
    · obtain ⟨y, hys, hyc⟩ := hscov (Work.WilE5.Cells.khovCellPt X σ) (hmem σ h)
      exact ⟨y, fun _ => ⟨hys, hyc⟩⟩
    · exact ⟨0, fun hh => absurd hh h⟩
  let φ : (Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign) → (Fin k → ℝ) :=
    fun σ => (hex2 σ).choose
  have hφmem : ∀ σ ∈ T, φ σ ∈ s := fun σ hσ => ((hex2 σ).choose_spec hσ).1
  have hφcomp : ∀ σ ∈ T, connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set
      (Work.WilE5.Cells.khovCellPt X σ) =
      connectedComponentIn (Work.WilE5.Cells.khovSet X ε).set (φ σ) :=
    fun σ hσ => ((hex2 σ).choose_spec hσ).2
  have hφinj : Set.InjOn φ ↑T := by
    intro σ hσ τ hτ heq
    by_contra hne
    exact hsep σ hσ τ hτ hne (by rw [hφcomp σ hσ, heq, ← hφcomp τ hτ])
  have hcard : T.card ≤ s.card := by
    have h1 : (T.image φ).card = T.card := Finset.card_image_of_injOn hφinj
    have h2 : T.image φ ⊆ s := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨σ, hσ, rfl⟩ := hy
      exact hφmem σ hσ
    have h3 := Finset.card_le_card h2
    omega
  calc T.card ≤ s.card := hcard
    _ ≤ p.eval (Work.WilE5.Cells.khovSet X ε).deg := hscard
    _ ≤ p.eval (4 * X.deg + 1) :=
        Work.WilE5.Cells.khovEval_mono (by have := Work.WilE5.Cells.khovSet_deg_le X ε; omega)
    _ = (p.comp (Polynomial.C 4 * Polynomial.X + Polynomial.C 1)).eval X.deg := by
        rw [Polynomial.eval_comp]
        congr 1
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]

end Work.WilE6.Compl
