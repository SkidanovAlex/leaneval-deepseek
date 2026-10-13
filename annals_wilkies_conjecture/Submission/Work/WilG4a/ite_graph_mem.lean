/-
  WilG4a : area G4a of the Wilkie/Pfaffian project (BNZ §5.1).

  This module proves that the graph of a *case-split* (`if-then-else`) function is again
  `Ω`-definable, with parameters depending only polynomially on the format `F` and the degree
  `D` of the inputs.  This is the elementary "gluing" step needed to turn finitely many
  partial charts into a single global chart.

  The key point is the set identity

    `graphOf (iteFun P f g)
       = (graphOf f ∩ {z | Fin.init z ∈ P}) ∪ (graphOf g ∩ {z | Fin.init z ∈ P}ᶜ)`

  together with the `Ω`-closure axioms `prod_right` (pull back along `Fin.init`), `compl`,
  `inter` and `union` of `SOMin`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign Work.WilG5

/-- The sum of a `Fin 2`-indexed family of naturals, written with `![·,·]`. -/
theorem sum_fin_two_nat_ite (D1 D2 : ℕ) : (∑ i : Fin 2, ![D1, D2] i) = D1 + D2 := by
  simp [Fin.sum_univ_two]

/-- `SOMin.inter` in the binary case, with the two sets at the same format. -/
theorem inter_mem_ite {S : SOMin} {n : ℕ} {F D1 D2 : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D1 n) (hB : B ∈ S.Ω F D2 n) :
    A ∩ B ∈ S.Ω (F + 1) (D1 + D2) n := by
  have h : ∀ i : Fin 2, ![A, B] i ∈ S.Ω F (![D1, D2] i) n := by
    intro i
    fin_cases i
    · simpa using hA
    · simpa using hB
  have hmain := S.inter ![D1, D2] ![A, B] h
  rw [show (⋂ i : Fin 2, ![A, B] i) = A ∩ B from by ext z; simp [Set.mem_iInter]] at hmain
  rw [sum_fin_two_nat_ite] at hmain
  exact hmain

/-- `SOMin.union` in the binary case, with the two sets at the same format. -/
theorem union_mem {S : SOMin} {n : ℕ} {F D1 D2 : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D1 n) (hB : B ∈ S.Ω F D2 n) :
    A ∪ B ∈ S.Ω F (D1 + D2) n := by
  have h : ∀ i : Fin 2, ![A, B] i ∈ S.Ω F (![D1, D2] i) n := by
    intro i
    fin_cases i
    · simpa using hA
    · simpa using hB
  have hmain := S.union ![D1, D2] ![A, B] h
  rw [show (⋃ i : Fin 2, ![A, B] i) = A ∪ B from by ext z; simp [Set.mem_iUnion]] at hmain
  rw [sum_fin_two_nat_ite] at hmain
  exact hmain

/-- The graph of the case-split function `iteFun P f g`, decomposed as the union of the
graph of `f` over `P` and the graph of `g` over the complement of `P`. -/
theorem graphOf_iteFun_eq {p : ℕ} (P : Set (Fin p → ℝ)) (f g : (Fin p → ℝ) → ℝ) :
    graphOf (iteFun P f g) =
      (graphOf f ∩ {z : Fin (p + 1) → ℝ | Fin.init z ∈ P}) ∪
        (graphOf g ∩ {z : Fin (p + 1) → ℝ | Fin.init z ∈ P}ᶜ) := by
  ext z
  simp only [graphOf, iteFun, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union,
    Set.mem_compl_iff]
  constructor
  · intro h
    by_cases hP : Fin.init z ∈ P
    · exact Or.inl ⟨h.trans (ite_eq_left hP), hP⟩
    · exact Or.inr ⟨h.trans (ite_eq_right hP), hP⟩
  · rintro (⟨hf, hP⟩ | ⟨hg, hP⟩)
    · rw [ite_eq_left hP]; exact hf
    · rw [ite_eq_right hP]; exact hg

/-- The graph of a case-split function is `Ω`-definable, with format and degree depending
only on those of the input graphs and of the case-set.  Concretely, if `P ∈ Ω F D p` and the
graphs of `f`, `g` lie in `Ω F D (p+1)`, then the graph of `iteFun P f g` lies in
`Ω (F+4) (4*D) (p+1)`. -/
theorem ite_graph_mem (S : WilkiesDesign.SOMin) (p : ℕ) (F : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) {P : Set (Fin p → ℝ)} {f g : (Fin p → ℝ) → ℝ},
        P ∈ S.Ω F D p → WilkiesDesign.graphOf f ∈ S.Ω F D (p + 1) →
          WilkiesDesign.graphOf g ∈ S.Ω F D (p + 1) →
            WilkiesDesign.graphOf (Work.WilG4a.iteFun P f g) ∈
              S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) := by
  refine ⟨F + 4, MvPolynomial.C 4 * MvPolynomial.X (0 : Fin 2), ?_⟩
  intro D r P f g hP hf hg
  -- The projection `{z | Fin.init z ∈ P}` and its complement.
  have hproj : {z : Fin (p + 1) → ℝ | Fin.init z ∈ P} ∈ S.Ω (F + 1) D (p + 1) :=
    S.prod_right hP
  have hprojC : ({z : Fin (p + 1) → ℝ | Fin.init z ∈ P})ᶜ ∈ S.Ω (F + 2) D (p + 1) :=
    mem_mono (S.compl hproj) (F + 2) D (by omega) (le_refl D)
  -- Raise the graphs to the formats of the two pieces.
  have hf1 : graphOf f ∈ S.Ω (F + 1) D (p + 1) :=
    mem_mono hf (F + 1) D (by omega) (le_refl D)
  have hg2 : graphOf g ∈ S.Ω (F + 2) D (p + 1) :=
    mem_mono hg (F + 2) D (by omega) (le_refl D)
  -- The two pieces, both brought to the common format `F + 4`.
  have hA : graphOf f ∩ {z : Fin (p + 1) → ℝ | Fin.init z ∈ P} ∈
      S.Ω (F + 4) (D + D) (p + 1) :=
    mem_mono (inter_mem_ite hf1 hproj) (F + 4) (D + D) (by omega) (le_refl _)
  have hB : graphOf g ∩ ({z : Fin (p + 1) → ℝ | Fin.init z ∈ P})ᶜ ∈
      S.Ω (F + 4) (D + D) (p + 1) :=
    mem_mono (inter_mem_ite hg2 hprojC) (F + 4) (D + D) (by omega) (le_refl _)
  -- Glue the two pieces with `union`.
  have hU : (graphOf f ∩ {z : Fin (p + 1) → ℝ | Fin.init z ∈ P}) ∪
      (graphOf g ∩ ({z : Fin (p + 1) → ℝ | Fin.init z ∈ P})ᶜ) ∈
      S.Ω (F + 4) ((D + D) + (D + D)) (p + 1) := union_mem hA hB
  rw [← graphOf_iteFun_eq] at hU
  -- Degree bookkeeping: `(D+D)+(D+D) = 4*D = eval ![D,r] (C 4 * X 0)`.
  have hb : MvPolynomial.eval ![D, r] (MvPolynomial.C 4 * MvPolynomial.X (0 : Fin 2))
      = 4 * D := by simp
  have hdeg : (D + D) + (D + D) = 4 * D := by omega
  rw [hb, ← hdeg]
  exact hU

end Work.WilG4a
