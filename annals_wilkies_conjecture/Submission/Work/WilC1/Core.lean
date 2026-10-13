/-
  WilC1 — the C1 argument, with every input as an explicit hypothesis.

  This file contains the whole logical skeleton of `C1_TR_modelComplete` (the "mechanical" part:
  formula ↔ existential formula, both ways, so that embeddings between models of `T_r` are
  elementary), taking as hypotheses:
  * the four inductive cases of the graph induction (`REx_graph_tAdd`, …),
  * `REx_eq_of_terms` (the atomic case),
  * the complement closure (`REx_compl` composed with `REx_iff_RExpExist` and `hR`),
  * `exists_term_of_poly` (exp-polynomials are `LRc`-terms),
  * `IsQF_isExistential_iExs` (existential closure of a quantifier-free formula).

  `Submission/Work/WilC1/Main.lean` instantiates all of them.
-/
import Submission.Work.WilC1.Defs
import Submission.Work.WilC1.Graph
import Submission.Work.WilC1.Sof
import Mathlib.ModelTheory.ElementarySubstructures

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture

/-! ## Two small reindexings -/

/-- The equivalence `τ ≃ τ ⊕ Fin 0`. -/
def sumFinZeroSymm (τ : Type) : τ ≃ τ ⊕ Fin 0 := (Equiv.sumEmpty τ (Fin 0)).symm

/-- `Sum.elim` of the components of a function along `sumFinZeroSymm` is the function. -/
theorem elim_comp_sumFinZeroSymm {τ : Type} (x : τ → ℝ) (y : Fin 0 → ℝ) :
    (Sum.elim x y) ∘ (sumFinZeroSymm τ) = x := by
  funext a
  simp only [Function.comp_apply, sumFinZeroSymm, Equiv.sumEmpty_symm_apply, Sum.elim_inl]

/-- The equivalence `Fin n ≃ Empty ⊕ Fin n`. -/
def emptySumSymm (n : ℕ) : Fin n ≃ Empty ⊕ Fin n := (Equiv.emptySum Empty (Fin n)).symm

/-- `Sum.elim` of the components of a function along `emptySumSymm` is the function. -/
theorem elim_comp_emptySumSymm {n : ℕ} {M : Type} (v : Empty → M) (x : Fin n → M) :
    (Sum.elim v x) ∘ (emptySumSymm n) = x := by
  funext j
  simp only [Function.comp_apply, emptySumSymm, Equiv.emptySum_symm_apply, Sum.elim_inr]

/-! ## Membership in `Sof`, realization of the zero-equality atom -/

/-- Membership in `Sof φ` unravels the coordinate split. -/
theorem mem_Sof_iff {α : Type} {k : ℕ} (φ : LRc.BoundedFormula α k) (x : α → ℝ)
    (y : Fin k → ℝ) : Sum.elim x y ∈ Sof φ ↔ φ.Realize x y := by
  rw [Sof]
  simp only [Set.mem_ofPred_eq, Sum.elim_comp_inl, Sum.elim_comp_inr]

/-- `BoundedFormula.Realize` of a formula without bound variables. -/
theorem bounded_realize_iff_formula {τ M : Type} [LRc.Structure M] (φ : LRc.Formula τ)
    (v : τ → M) (y : Fin 0 → M) : BoundedFormula.Realize φ v y ↔ φ.Realize v :=
  Formula.boundedFormula_realize_eq_realize φ v y

/-- Realization of an equality with the zero term. -/
theorem realize_bdEqual_tZero {τ : Type} (t : LRc.Term (τ ⊕ Fin 0)) (v : τ → ℝ)
    (y : Fin 0 → ℝ) :
    BoundedFormula.Realize (Term.bdEqual t (tZero (τ := τ ⊕ Fin 0))) v y ↔
      Term.realize (Sum.elim v y) t = 0 := by
  rw [BoundedFormula.realize_bdEqual]
  simp only [realize_tZero]

/-- The realization of a sentence does not depend on the (unique) empty assignment. -/
theorem formula_realize_empty_congr {M : Type} [LRc.Structure M] (φ : LRc.Sentence)
    {v v' : Empty → M} : Formula.Realize φ v ↔ Formula.Realize φ v' := by
  rw [Subsingleton.elim v v']

/-- Realization of a formula relabelled along an equivalence of the free variables. -/
theorem realize_relabelEquiv_formula {τ τ' M : Type} [LRc.Structure M] (e : τ ≃ τ')
    (φ : LRc.Formula τ) (v : τ' → M) :
    Formula.Realize ((BoundedFormula.relabelEquiv e) φ) v ↔ Formula.Realize φ (v ∘ e) := by
  have h₁ : Formula.Realize ((BoundedFormula.relabelEquiv e) φ) v ↔
      BoundedFormula.Realize ((BoundedFormula.relabelEquiv e) φ) v (fun i : Fin 0 => i.elim0) :=
    (bounded_realize_iff_formula ((BoundedFormula.relabelEquiv e) φ) v
      (fun i : Fin 0 => i.elim0)).symm
  have h₂ := BoundedFormula.realize_relabelEquiv (g := e) (φ := φ) (v := v)
    (xs := fun i : Fin 0 => i.elim0)
  have h₃ := bounded_realize_iff_formula φ (v ∘ e) (fun i : Fin 0 => i.elim0)
  exact h₁.trans (h₂.trans h₃)

/-! ## The bridge: `REx` sets are realization sets of existential formulas -/

theorem exists_existential_formula
    (hTerm : ∀ {τ : Type} (P : MvPolynomial (τ ⊕ τ) ℝ),
      ∃ t : LRc.Term τ, ∀ v : τ → ℝ, Term.realize v t = rexpEval v P)
    (hIExs : ∀ {α γ : Type} [Finite γ] {φ : LRc.Formula (α ⊕ γ)},
      BoundedFormula.IsQF φ → BoundedFormula.IsExistential (Formula.iExs γ φ))
    {ι : Type} (X : Set (ι → ℝ)) (hX : REx ι X) :
    ∃ ψ : LRc.Formula ι, ψ.IsExistential ∧ ∀ x : ι → ℝ, (ψ.Realize x ↔ x ∈ X) := by
  obtain ⟨γ, hγ, P, hP⟩ := hX
  letI : Fintype γ := hγ
  obtain ⟨t, ht⟩ := hTerm (τ := ι ⊕ γ) P
  let bd : LRc.Formula (ι ⊕ γ) := Term.bdEqual (t.relabel (sumFinZeroSymm (ι ⊕ γ)))
    (tZero (τ := (ι ⊕ γ) ⊕ Fin 0))
  have hIsEx : (Formula.iExs (β := γ) bd).IsExistential :=
    hIExs (α := ι) (γ := γ) (φ := bd) (BoundedFormula.IsAtomic.equal _ _).isQF
  refine ⟨Formula.iExs (β := γ) bd, hIsEx, ?_⟩
  intro x
  rw [Formula.realize_iExs, hP, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← bounded_realize_iff_formula bd (Sum.elim x y) (fun j : Fin 0 => j.elim0),
      realize_bdEqual_tZero, Term.realize_relabel, elim_comp_sumFinZeroSymm, ht] at hy
    exact hy
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← bounded_realize_iff_formula bd (Sum.elim x y) (fun j : Fin 0 => j.elim0),
      realize_bdEqual_tZero, Term.realize_relabel, elim_comp_sumFinZeroSymm, ht]
    exact hy

/-! ## Sentences realizing a formula and its negation in every model of `T_r` -/

theorem exists_sentence_of_formula
    (hReal : ∀ {α : Type} [Fintype α] {k : ℕ} (φ : LRc.BoundedFormula α k),
      REx (α ⊕ Fin k) (Sof φ))
    (hCompl : ∀ {ι : Type} [Fintype ι] (X : Set (ι → ℝ)), REx ι X → REx ι Xᶜ)
    (hBridge : ∀ {ι : Type} (X : Set (ι → ℝ)), REx ι X →
      ∃ ψ : LRc.Formula ι, ψ.IsExistential ∧ ∀ x : ι → ℝ, (ψ.Realize x ↔ x ∈ X))
    {n : ℕ} (φ : LRc.Formula (Fin n)) :
    ∃ ψ : LRc.Formula (Fin n), ψ.IsExistential ∧
      (∀ x : Fin n → ℝ, (ψ.Realize x ↔ φ.Realize x)) ∧
      ∀ (M : Type) [LRc.Structure M] [M ⊨ WilkiesDesign.CG.TR] (x : Fin n → M),
        (ψ.Realize x ↔ φ.Realize x) := by
  have hset : {x : Fin n → ℝ | φ.Realize x}
      = {x : Fin n → ℝ | ∃ y : Fin 0 → ℝ, Sum.elim x y ∈ Sof φ} := by
    ext x
    constructor
    · intro h
      refine ⟨fun i => i.elim0, ?_⟩
      rw [mem_Sof_iff, bounded_realize_iff_formula]
      exact h
    · rintro ⟨y, hy⟩
      rw [mem_Sof_iff, bounded_realize_iff_formula] at hy
      exact hy
  have hREx : REx (Fin n) {x : Fin n → ℝ | φ.Realize x} :=
    REx.congr hset.symm (REx_proj 0 (hReal φ))
  obtain ⟨ψ, hψE, hψ⟩ := hBridge _ hREx
  have hiff : ∀ x : Fin n → ℝ, (ψ.Realize x ↔ φ.Realize x) := fun x =>
    ⟨fun h => (hψ x).mp h, fun h => (hψ x).mpr h⟩
  refine ⟨ψ, hψE, hiff, ?_⟩
  intro M _ _ x
  let σ₀ : LRc.Formula (Empty ⊕ Fin n) :=
    Formula.iff ((BoundedFormula.relabelEquiv (emptySumSymm n)) φ)
      ((BoundedFormula.relabelEquiv (emptySumSymm n)) ψ)
  let σ : LRc.Sentence := Formula.iAlls (Fin n) σ₀
  have hpt : ∀ i : Fin n → ℝ,
      σ₀.Realize (fun a => Sum.elim (default : Empty → ℝ) i a) := by
    intro i
    rw [Formula.realize_iff]
    simp only [realize_relabelEquiv_formula, elim_comp_emptySumSymm]
    exact (hiff i).symm
  have hσℝ : ℝ ⊨ σ := by
    rw [Sentence.Realize]
    exact (formula_realize_empty_congr σ).mpr
      ((Formula.realize_iAlls (β := Fin n) (φ := σ₀) (v := (default : Empty → ℝ))).mpr hpt)
  have hMT : M ⊨ LRc.completeTheory ℝ := ‹M ⊨ WilkiesDesign.CG.TR›
  have hσM : M ⊨ σ := (Language.realize_iff_of_model_completeTheory (L := LRc) ℝ M σ).mpr hσℝ
  rw [Sentence.Realize] at hσM
  have h1 := (Formula.realize_iAlls (β := Fin n) (φ := σ₀)
    (v := (default : Empty → M))).mp ((formula_realize_empty_congr σ).mp hσM)
  have h2 := h1 x
  rw [Formula.realize_iff] at h2
  simp only [realize_relabelEquiv_formula, elim_comp_emptySumSymm] at h2
  exact h2.symm

/-! ## The assembly -/

theorem modelComplete_of_parts
    (hCompl : ∀ {ι : Type} [Fintype ι] (X : Set (ι → ℝ)), REx ι X → REx ι Xᶜ)
    (hAdd : ∀ {ι : Type} {a b : LRc.Term ι}, REx (ι ⊕ Fin 1) (GraphSet a) →
      REx (ι ⊕ Fin 1) (GraphSet b) → REx (ι ⊕ Fin 1) (GraphSet (tAdd a b)))
    (hMul : ∀ {ι : Type} {a b : LRc.Term ι}, REx (ι ⊕ Fin 1) (GraphSet a) →
      REx (ι ⊕ Fin 1) (GraphSet b) → REx (ι ⊕ Fin 1) (GraphSet (tMul a b)))
    (hNeg : ∀ {ι : Type} {a : LRc.Term ι}, REx (ι ⊕ Fin 1) (GraphSet a) →
      REx (ι ⊕ Fin 1) (GraphSet (tNeg a)))
    (hExp : ∀ {ι : Type} {a : LRc.Term ι}, REx (ι ⊕ Fin 1) (GraphSet a) →
      REx (ι ⊕ Fin 1) (GraphSet (tRexp a)))
    (hEqTerms : ∀ {ι : Type} (t₁ t₂ : LRc.Term ι)
      (hg : ∀ (t : LRc.Term ι), REx (ι ⊕ Fin 1) (GraphSet t)),
      REx ι {x : ι → ℝ | Term.realize x t₁ = Term.realize x t₂})
    (hTerm : ∀ {τ : Type} (P : MvPolynomial (τ ⊕ τ) ℝ),
      ∃ t : LRc.Term τ, ∀ v : τ → ℝ, Term.realize v t = rexpEval v P)
    (hIExs : ∀ {α γ : Type} [Finite γ] {φ : LRc.Formula (α ⊕ γ)},
      BoundedFormula.IsQF φ → BoundedFormula.IsExistential (Formula.iExs γ φ)) :
    ModelComplete WilkiesDesign.CG.TR := by
  have hgraph : ∀ {ι : Type} (t : LRc.Term ι), REx (ι ⊕ Fin 1) (GraphSet t) :=
    fun t => REx_graphSet_of_cases hAdd hMul hNeg hExp t
  have hReal : ∀ {α : Type} [Fintype α] {k : ℕ} (φ : LRc.BoundedFormula α k),
      REx (α ⊕ Fin k) (Sof φ) := fun φ =>
    REx_Sof_of (fun t₁ t₂ => hEqTerms t₁ t₂ (fun t => hgraph t)) (fun _ hX => hCompl _ hX) φ
  have hBridge : ∀ {ι : Type} (X : Set (ι → ℝ)), REx ι X →
      ∃ ψ : LRc.Formula ι, ψ.IsExistential ∧ ∀ x : ι → ℝ, (ψ.Realize x ↔ x ∈ X) :=
    fun X hX => exists_existential_formula hTerm hIExs X hX
  intro M N _ _ _ _ f n φ x
  obtain ⟨ψ, hψE, -, hψM⟩ := exists_sentence_of_formula hReal hCompl hBridge φ
  obtain ⟨ψ', hψ'E, -, hψ'M⟩ := exists_sentence_of_formula hReal hCompl hBridge (Formula.not φ)
  constructor
  · -- `N ⊨ φ(f x)` implies `M ⊨ φ(x)`
    intro hN
    by_contra hM
    have hM' : (Formula.not φ).Realize x := by rw [Formula.realize_not]; exact hM
    have h1 : ψ'.Realize x := (hψ'M M x).mpr hM'
    have h1' : BoundedFormula.Realize ψ' x (default : Fin 0 → M) :=
      (bounded_realize_iff_formula ψ' x (default : Fin 0 → M)).mpr h1
    have h2 : BoundedFormula.Realize ψ' (f ∘ x) (f ∘ (default : Fin 0 → M)) :=
      hψ'E.realize_embedding f h1'
    have h2' : ψ'.Realize (f ∘ x) :=
      (bounded_realize_iff_formula ψ' (f ∘ x) (f ∘ (default : Fin 0 → M))).mp h2
    have h3 : (Formula.not φ).Realize (f ∘ x) := (hψ'M N (f ∘ x)).mp h2'
    rw [Formula.realize_not] at h3
    exact h3 hN
  · -- `M ⊨ φ(x)` implies `N ⊨ φ(f x)`
    intro hM
    have h1 : ψ.Realize x := (hψM M x).mpr hM
    have h1' : BoundedFormula.Realize ψ x (default : Fin 0 → M) :=
      (bounded_realize_iff_formula ψ x (default : Fin 0 → M)).mpr h1
    have h2 : BoundedFormula.Realize ψ (f ∘ x) (f ∘ (default : Fin 0 → M)) :=
      hψE.realize_embedding f h1'
    have h2' : ψ.Realize (f ∘ x) :=
      (bounded_realize_iff_formula ψ (f ∘ x) (f ∘ (default : Fin 0 → M))).mp h2
    exact (hψM N (f ∘ x)).mp h2'

end Work.WilC1
