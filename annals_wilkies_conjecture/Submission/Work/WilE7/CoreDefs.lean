/-
  Area E7 (`Work.WilE7.CoreDefs`): the induction skeleton for `E7_prop_main_proved`.

  The target (`WilkiesDesign.E.E7_prop_main`) is

  ```
  ∀ F n, ∃ a b c, ∀ D k m (X : Fin k → SemiPf (n+m)), (∀ i, fmt ≤ F ∧ deg ≤ D) →
    ∃ C, IsCylDecompOn n (cubeC n) C ∧ compat ∧ C.card ≤ eval ![D,k] b ∧
      ∀ κ ∈ C, Star a (c.eval D) n κ ∧ SubPf n κ
  ```

  Following `NOTES_S26_level_step.md`, the induction is run on the stronger statement `Core n`,
  in which every cell carries a *single* `StarPiece` presentation `P` with `P.set = κ` (this is
  the form the level-`n+1` step needs as the base covering set for the cell lemmas of S11).
  `Core n → target` is `Core_all_imp_target` below; `Core 0` is `Core_zero`.
-/
import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- A cell presented as the projection of a single connected component: this is what `Star` is
made of, and it is the form in which the level-by-level induction must hand its cells to the
cell lemmas of S11 (which take a base cell `C = π_p '' connectedComponentIn Z.set u₀`). -/
theorem star_of_piece {n : ℕ} {κ : Set (Fin n → ℝ)} {a d : ℕ} (P : StarPiece n)
    (hP : P.set = κ) (hf : P.X.fmt ≤ a) (hd : P.X.deg ≤ d) :
    Star a d n κ := by
  refine ⟨[P], ?_, ?_, ?_⟩
  · rw [← hP]
    ext x
    simp
  · intro Q hQ
    rw [List.mem_singleton] at hQ
    subst hQ
    exact hf
  · simpa using hd

/-- The strengthened induction statement: a cylindrical decomposition of `cubeC n` compatible
with the projections of `k` semi-Pfaffian sets, whose cells are `SubPf` and each carry a single
`StarPiece` presentation with format `≤ a` and degree `≤ c.eval D`. -/
def Core (n : ℕ) : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
    ∀ (D k m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf (n + m)),
      (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
      ∃ C : Finset (Set (Fin n → ℝ)),
        WilkiesDesign.E.IsCylDecompOn n (WilkiesDesign.E.cubeC n) C ∧
        (∀ i, ∀ κ ∈ C, κ ⊆ WilkiesDesign.E.projFirst n m '' (X i).set ∨
          Disjoint κ (WilkiesDesign.E.projFirst n m '' (X i).set)) ∧
        C.card ≤ MvPolynomial.eval ![D, k] b ∧
        ∀ κ ∈ C, (∃ P : WilkiesDesign.E.StarPiece n,
            P.set = κ ∧ P.X.fmt ≤ a ∧ P.X.deg ≤ c.eval D) ∧
          WilkiesDesign.E.SubPf n κ

/-- `Core n` for all `n` implies the target. -/
theorem Core_all_imp_target (H : ∀ n : ℕ, Core n) :
    ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf (n + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        ∃ C : Finset (Set (Fin n → ℝ)),
          WilkiesDesign.E.IsCylDecompOn n (WilkiesDesign.E.cubeC n) C ∧
          (∀ i, ∀ κ ∈ C, κ ⊆ WilkiesDesign.E.projFirst n m '' (X i).set ∨
            Disjoint κ (WilkiesDesign.E.projFirst n m '' (X i).set)) ∧
          C.card ≤ MvPolynomial.eval ![D, k] b ∧
          ∀ κ ∈ C, WilkiesDesign.E.Star a (c.eval D) n κ ∧ WilkiesDesign.E.SubPf n κ := by
  intro F n
  obtain ⟨a, b, c, h⟩ := H n F
  refine ⟨a, b, c, ?_⟩
  intro D k m X hX
  obtain ⟨C, hCyl, hcompat, hcard, hcell⟩ := h D k m X hX
  exact ⟨C, hCyl, hcompat, hcard, fun κ hκ =>
    ⟨(hcell κ hκ).1.elim fun P hP => star_of_piece P hP.1 hP.2.1 hP.2.2, (hcell κ hκ).2⟩⟩

/-! ## The base case `n = 0` -/

/-- The "whole space" semi-Pfaffian set in `ℝ^0` (one vacuous basic set, no chain). -/
def univSemiPf0 : WilkiesDesign.E.SemiPf 0 :=
  ⟨0, EAChain.nil 0, [⟨[], []⟩]⟩

theorem univSemiPf0_set : univSemiPf0.set = Set.univ := by
  show (⟨0, EAChain.nil 0, [⟨[], []⟩]⟩ : WilkiesDesign.E.SemiPf 0).set = Set.univ
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  refine ⟨fun i => absurd i.isLt (by omega), ⟨[], []⟩, by simp, ?_⟩
  refine ⟨fun f hf => absurd hf ?_, fun g hg => absurd hg ?_⟩ <;> simp

theorem cubeC_zero : WilkiesDesign.E.cubeC 0 = (Set.univ : Set (Fin 0 → ℝ)) := by
  ext x
  refine ⟨fun _ => trivial, fun _ => fun i => absurd i.isLt (by omega)⟩

theorem Core_zero : Core 0 := by
  intro F
  refine ⟨0, 1, 1, ?_⟩
  intro D k m X hX
  refine ⟨{Set.univ}, ?_, ?_, ?_, ?_⟩
  · exact Or.inl ⟨cubeC_zero, rfl⟩
  · intro i κ hκ
    rw [Finset.mem_singleton] at hκ
    subst hκ
    by_cases hne : (X i).set = ∅
    · right
      rw [Set.disjoint_left]
      intro y hy hproj
      obtain ⟨z, hz, -⟩ := hproj
      rw [hne] at hz
      exact hz
    · left
      intro y _
      obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact ⟨z, hz, Subsingleton.elim _ _⟩
  · show ({Set.univ} : Finset (Set (Fin 0 → ℝ))).card ≤
      MvPolynomial.eval ![D, k] (1 : MvPolynomial (Fin 2) ℕ)
    simp
  · intro κ hκ
    rw [Finset.mem_singleton] at hκ
    subst hκ
    constructor
    · refine ⟨⟨0, univSemiPf0, fun _ => default⟩, ?_, ?_, ?_⟩
      · apply Set.eq_univ_of_forall
        intro y
        refine ⟨default, ?_, Subsingleton.elim _ _⟩
        rw [show univSemiPf0.set = Set.univ from univSemiPf0_set]
        exact mem_connectedComponentIn trivial
      · show univSemiPf0.fmt ≤ 0
        simp [univSemiPf0, WilkiesDesign.E.SemiPf.fmt]
      · show univSemiPf0.deg ≤ (1 : Polynomial ℕ).eval D
        simp [univSemiPf0, WilkiesDesign.E.SemiPf.deg, Basic.deg]
    · refine ⟨0, univSemiPf0, ?_⟩
      rw [show univSemiPf0.set = Set.univ from univSemiPf0_set]
      ext y
      exact ⟨fun _ => ⟨default, trivial, Subsingleton.elim _ _⟩, fun _ => trivial⟩

end Work.WilE7
