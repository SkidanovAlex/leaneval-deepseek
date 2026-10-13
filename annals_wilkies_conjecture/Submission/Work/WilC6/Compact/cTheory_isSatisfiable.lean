import Mathlib
import Submission.Work.WilC6.Compact.Defs
import Submission.Work.WilC6.Base

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6.Compact

/-- Realization of a finite disjunction of formulas: a `foldr` of `⊔` is true exactly when one of
its members is. -/
theorem realize_foldr_sup_formula {L : Language} {α : Type*} {M : Type} [L.Structure M]
    (l : List (L.Formula α)) (v : α → M) :
    (l.foldr (· ⊔ ·) ⊥).Realize v ↔ ∃ φ ∈ l, φ.Realize v := by
  simp only [Formula.Realize, BoundedFormula.realize_foldr_sup]

/-- The finite piece `cTheory φ b F` of the compactness theory is satisfiable: the disjunction
`Ψ'` of the members of `F` is an `IsEF` formula which is false at `b`, so it is not an `IsEF`
consequence of `φ`; a counterexample model realizes `φ` and the negations of all members of `F`.
(When `F = ∅` the disjunction is `⊥`, and the same argument shows `φ` is satisfiable in a model of
`TE`.) -/
theorem cTheory_isSatisfiable {n : ℕ} (φ : WilkiesDesign.CG.LEc.Formula (Fin n))
    (N : Type) [WilkiesDesign.CG.LEc.Structure N]
    [FirstOrder.Language.Theory.Model N WilkiesDesign.CG.TE] (b : Fin n → N)
    (hΓ : ∀ Ψ : WilkiesDesign.CG.LEc.Formula (Fin n),
      Work.WilC6.IsEF Ψ → Work.WilC6.EFCons φ Ψ → Ψ.Realize b)
    (F : Finset (Work.WilC6.Compact.EFIndex b)) :
    (Work.WilC6.Compact.cTheory φ b F).IsSatisfiable := by
  classical
  -- the disjunction `Ψ'` of the members of `F`
  set l : List (LEc.Formula (Fin n)) := F.toList.map (fun Ψ : EFIndex b => Ψ.val) with hl
  set Ψ' : LEc.Formula (Fin n) := l.foldr (· ⊔ ·) ⊥ with hΨ'
  have hmem_l : ∀ Ψ : EFIndex b, Ψ ∈ F → Ψ.val ∈ l := by
    intro Ψ hΨ
    rw [hl, List.mem_map]
    exact ⟨Ψ, by rwa [Finset.mem_toList], rfl⟩
  have hlIsEF : ∀ Ψ ∈ l, IsEF Ψ := by
    intro Ψ hΨ
    rw [hl, List.mem_map] at hΨ
    obtain ⟨Ψ₀, -, rfl⟩ := hΨ
    exact Ψ₀.2.1
  have hEF' : IsEF Ψ' := by
    rw [hΨ']
    exact IsEF.folds_sup l hlIsEF
  have hrealize' : ∀ {M : Type} [inst : LEc.Structure M] (x : Fin n → M),
      Formula.Realize Ψ' x ↔ ∃ Ψ : EFIndex b, Ψ ∈ F ∧ Formula.Realize Ψ.val x := by
    intro M inst x
    letI := inst
    rw [hΨ', realize_foldr_sup_formula]
    constructor
    · rintro ⟨Ψ, hΨl, hΨx⟩
      rw [hl, List.mem_map] at hΨl
      obtain ⟨Ψ₀, hΨ₀F, rfl⟩ := hΨl
      exact ⟨Ψ₀, by rwa [Finset.mem_toList] at hΨ₀F, hΨx⟩
    · rintro ⟨Ψ, hΨF, hΨx⟩
      exact ⟨Ψ.val, hmem_l Ψ hΨF, hΨx⟩
  -- `Ψ'` is false at `b`, so it is not an `IsEF` consequence of `φ`
  have hb : ¬ Formula.Realize Ψ' b := by
    rw [hrealize' b]
    rintro ⟨Ψ, hΨF, hΨb⟩
    exact Ψ.2.2 hΨb
  have hne : ¬ EFCons φ Ψ' := fun h => hb (hΓ Ψ' hEF' h)
  -- a counterexample model for `EFCons φ Ψ'`
  simp only [EFCons] at hne
  push_neg at hne
  obtain ⟨M, hMstr, hMTE, x, hφx, hΨ'x⟩ := hne
  letI : LEc.Structure M := hMstr
  letI : M ⊨ TE := hMTE
  have hnot : ∀ Ψ : EFIndex b, Ψ ∈ F → ¬ Formula.Realize Ψ.val x := by
    intro Ψ hΨF hΨx
    exact hΨ'x ((hrealize' x).2 ⟨Ψ, hΨF, hΨx⟩)
  -- name the elements of `x` by constants and put the structure on `LEc[[Fin n]]`
  letI : (constantsOn (Fin n)).Structure M := constantsOn.structure x
  have hmodel : M ⊨ cTheory φ b F := by
    rw [Theory.model_iff]
    intro ψ hψ
    rw [cTheory] at hψ
    rcases hψ with (hψ | hψ) | hψ
    · -- the transported theory `TE`
      haveI hone : M ⊨ (LEc.lhomWithConstants (Fin n)).onTheory TE :=
        (LHom.onTheory_model (LEc.lhomWithConstants (Fin n)) TE).2 hMTE
      exact Theory.realize_sentence_of_mem _ hψ
    · -- the sentence `φ`
      rw [Set.mem_singleton_iff] at hψ
      rw [hψ, Formula.realize_equivSentence]
      exact hφx
    · -- the negations of the members of `F`
      obtain ⟨Ψ, hΨF, rfl⟩ := hψ
      rw [Sentence.realize_not]
      intro hc
      exact hnot Ψ hΨF ((Formula.realize_equivSentence M Ψ.val).1 hc)
  haveI : M ⊨ cTheory φ b F := hmodel
  haveI : Nonempty M := Language.nonempty_of_nonempty_constants (L := LEc) (M := M)
    (h := ⟨(Sum.inr (0 : ℝ) : LEc.Constants)⟩)
  exact Theory.Model.isSatisfiable M

end Work.WilC6.Compact
