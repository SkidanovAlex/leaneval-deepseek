import Mathlib
import Submission.Work.WilG4c.graphOf_tail_mem
import Submission.Work.WilG4c.thickBase_loOf
import Submission.Work.WilE8.Sharp.CellTransport
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Cell.isCell_of_mem_cylDecomp
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.FiberEndsLo
import Submission.Work.WilG4c.FiberEndsA.A_lo_mem
import Submission.Work.WilG4c.sliceGraph_mem_gen
import Submission.Work.WilG4c.StepFiberEnds
import Submission.Work.WilG4c.CellParamDefs
import Submission.Work.WilG4c.cellFibre_param
import Submission.Work.WilkG4c.ExactCellDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-!
## The cell section lemma

Every empty-interior cell `Z ⊆ ℝ^m` which is `Ω F D m`-definable is covered by a single map
`θ : ℝ^q → ℝ^m` with `q < m` whose coordinate functions have `Ω`-definable graphs, of a
format independent of `D` and a degree polynomial in `D`.

The proof is an induction on the dimension `m`, by "peeling the last coordinate":

* if the projection `projLast Z` of `Z` has empty interior, the parametrisation
  `θ' : ℝ^q' → ℝ^{m}` of `projLast Z` given by the induction hypothesis is extended by a *free*
  last coordinate, `μ ↦ Fin.snoc (θ' (Fin.tail μ)) (μ 0)`; the new coordinate's graph is a
  coordinate hyperplane and the old coordinate graphs are pulled back along `Fin.tail`
  (`graphOf_tail_mem`);
* if `projLast Z` has nonempty interior then `Z` cannot be a band cell (a band over a thick
  base has nonempty interior, `Work.WilG1.Cell.interior_band_nonempty`), so it is a graph cell
  and its fibres are subsingletons; the last coordinate is then pinned by the definable fibre
  infimum `loOf m Z`, whose graph is the `Ω`-set `A_lo m Z` (`thickBase_loOf`), and
  `θ = Fin.snoc id (loOf)`.
-/

/-- `CellSectionProp S m F a b`: every empty-interior cell `Z ⊆ ℝ^m` which is
`Ω F D m`-definable is covered by a map `ℝ^q → ℝ^m` with `q < m` whose coordinate graphs are
`Ω a (b(D,1)) (q+1)`-definable, uniformly in the input degree `D`. -/
def CellSectionProp (S : WilkiesDesign.SOMin) (m F : ℕ) (a : ℕ)
    (b : MvPolynomial (Fin 2) ℕ) : Prop :=
  ∀ (D : ℕ) (Z : Set (Fin m → ℝ)), IsCell m Z → Z ∈ S.Ω F D m → interior Z = ∅ →
    ∃ (q : ℕ) (θ : (Fin q → ℝ) → (Fin m → ℝ)),
      q < m ∧
      (∀ j : Fin m, graphOf (fun μ : Fin q → ℝ => θ μ j) ∈
        S.Ω a (MvPolynomial.eval ![D, 1] b) (q + 1)) ∧
      (∀ l ∈ Z, ∃ μ : Fin q → ℝ, θ μ = l)

theorem cellSection_aux (S : WilkiesDesign.SOMin) :
    ∀ m F : ℕ, ∃ a b, CellSectionProp S m F a b := by
  intro m
  induction m with
  | zero =>
      intro F
      refine ⟨0, 1, ?_⟩
      intro D Z hcell hΩ hInt
      exfalso
      have hZu : Z = Set.univ := by cases hcell with | zero => rfl
      have hne : (interior (Set.univ : Set (Fin 0 → ℝ))).Nonempty := by
        rw [interior_univ]
        exact ⟨fun i => i.elim0, Set.mem_univ _⟩
      rw [hZu] at hInt
      rw [hInt] at hne
      exact Set.not_nonempty_empty hne
  | succ m ih =>
      intro F
      -- the induction hypothesis at the next format, and the fibre-end constants
      obtain ⟨a₁, b₁, H₁⟩ := ih (F + 1)
      obtain ⟨a_lo, H_lo⟩ := FiberEndsA.A_lo_mem S m F
      refine ⟨max (a₁ + 4 * m + 8) (max a_lo (m + 1)),
        b₁ + (MvPolynomial.C 2 + MvPolynomial.C 1000
          + MvPolynomial.C 100 * MvPolynomial.X 0), ?_⟩
      have ha1 : a₁ + 4 * m + 8 ≤ max (a₁ + 4 * m + 8) (max a_lo (m + 1)) :=
        Nat.le_max_left _ _
      have ha2 : a_lo ≤ max (a₁ + 4 * m + 8) (max a_lo (m + 1)) :=
        le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have ha3 : m + 1 ≤ max (a₁ + 4 * m + 8) (max a_lo (m + 1)) :=
        le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      have hb_eval : ∀ D : ℕ, MvPolynomial.eval ![D, 1]
          (b₁ + (MvPolynomial.C 2 + MvPolynomial.C 1000
            + MvPolynomial.C 100 * MvPolynomial.X 0))
          = MvPolynomial.eval ![D, 1] b₁ + (2 + 1000 + 100 * D) := by
        intro D
        simp
      have hb1 : ∀ D : ℕ, MvPolynomial.eval ![D, 1] b₁ + 2 ≤ MvPolynomial.eval ![D, 1]
          (b₁ + (MvPolynomial.C 2 + MvPolynomial.C 1000
            + MvPolynomial.C 100 * MvPolynomial.X 0)) := by
        intro D; rw [hb_eval D]; omega
      have hb2 : ∀ D : ℕ, 100 * D + 1000 ≤ MvPolynomial.eval ![D, 1]
          (b₁ + (MvPolynomial.C 2 + MvPolynomial.C 1000
            + MvPolynomial.C 100 * MvPolynomial.X 0)) := by
        intro D; rw [hb_eval D]; omega
      have hb3 : ∀ D : ℕ, 1 ≤ MvPolynomial.eval ![D, 1]
          (b₁ + (MvPolynomial.C 2 + MvPolynomial.C 1000
            + MvPolynomial.C 100 * MvPolynomial.X 0)) := by
        intro D; rw [hb_eval D]; omega
      intro D Z hcell hΩ hInt
      have hZ'cell : IsCell m (projLast Z) := Work.WilE8.Sharp.isCell_projLast hcell
      have hZ'Ω : projLast Z ∈ S.Ω (F + 1) D m := S.proj hΩ
      by_cases hthick : (interior (projLast Z)).Nonempty
      · -- **thick base**: the cell is a graph, the vertical coordinate is pinned by `loOf`
        obtain ⟨hgraph, hcover⟩ := thickBase_loOf hcell hInt hthick
        refine ⟨(m : ℕ), ?_⟩
        refine ⟨(fun μ : Fin m → ℝ => Fin.snoc μ (loOf m Z μ)),
          Nat.lt_succ_self m, ?_, hcover⟩
        intro j
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]
          exact Work.WilG1.Omega.mono (graphOf_coord_mem (S := S) j₀) ha3 (hb3 D)
        · simp only [Fin.snoc_last]
          have heta : (fun μ : Fin m → ℝ => loOf m Z μ) = loOf m Z := rfl
          rw [heta, hgraph]
          exact Work.WilG1.Omega.mono (H_lo D Z hΩ) ha2 (hb2 D)
      · -- **thin base**: recurse on the projection and add a free vertical coordinate
        have hZ'int : interior (projLast Z) = ∅ := Set.not_nonempty_iff_eq_empty.mp hthick
        obtain ⟨q', θ', hq', hgraphs, hcov⟩ := H₁ D (projLast Z) hZ'cell hZ'Ω hZ'int
        refine ⟨(q' + 1 : ℕ), ?_⟩
        refine ⟨(fun μ : Fin (q' + 1) → ℝ => Fin.snoc (θ' (Fin.tail μ)) (μ 0)),
          by omega, ?_, ?_⟩
        · intro j
          rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
          · simp only [Fin.snoc_castSucc]
            refine Work.WilG1.Omega.mono (graphOf_tail_mem S (hgraphs j₀))
              (le_trans (by omega) ha1) (hb1 D)
          · simp only [Fin.snoc_last]
            exact Work.WilG1.Omega.mono (graphOf_coord_mem (S := S) (0 : Fin (q' + 1)))
              (le_trans (by omega) ha3) (hb3 D)
        · intro l hl
          have hx : Fin.init l ∈ projLast Z := by
            refine ⟨l (Fin.last m), ?_⟩
            rw [Work.WilG4c.snoc_init_self m l]
            exact hl
          obtain ⟨μ', hμ'⟩ := hcov (Fin.init l) hx
          refine ⟨Fin.cons (l (Fin.last m)) μ', ?_⟩
          dsimp only []
          rw [Fin.tail_cons, Fin.cons_zero, hμ', Work.WilG4c.snoc_init_self m l]

theorem CellSectionMain (S : WilkiesDesign.SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (C : Finset (Set (Fin p → ℝ))), WilkiesDesign.IsCylDecomp p C →
        (∀ κ ∈ C, κ ∈ S.Ω F0 D p) →
        ∀ (κ : Set (Fin p → ℝ)), κ ∈ C → interior κ = ∅ →
          ∃ (q : ℕ) (θ : (Fin q → ℝ) → (Fin p → ℝ)),
            q < p ∧
            (∀ j : Fin p, WilkiesDesign.graphOf (fun μ : Fin q → ℝ => θ μ j) ∈
              S.Ω a (MvPolynomial.eval ![D, 1] b) (q + 1)) ∧
            (∀ l ∈ κ, ∃ μ : Fin q → ℝ, θ μ = l) := by
  obtain ⟨a, b, H⟩ := cellSection_aux S p F0
  exact ⟨a, b, fun D C hcd hΩ κ hκ hInt =>
    H D κ (Work.WilG1.Cell.isCell_of_mem_cylDecomp hcd hκ) (hΩ κ hκ) hInt⟩

end Work.WilG4c
