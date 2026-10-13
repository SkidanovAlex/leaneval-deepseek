import Mathlib
import Submission.Work.WilC6.Base

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6.Compact

/-- Every `LEc`-structure is nonempty: `LEc` contains constant symbols (the reals), and the
interpretation of a constant symbol is an element. -/
theorem nonempty_of_LEc_structure (M : Type) [LEc.Structure M] : Nonempty M :=
  Language.nonempty_of_nonempty_constants (L := LEc) (M := M)
    (h := ⟨(Sum.inr (0 : ℝ) : LEc.Constants)⟩)

theorem exists_isEF_of_entails {n : ℕ} (φ : WilkiesDesign.CG.LEc.Formula (Fin n))
    (h : ∀ (N : Type) [WilkiesDesign.CG.LEc.Structure N]
      [FirstOrder.Language.Theory.Model N WilkiesDesign.CG.TE] (b : Fin n → N),
      (∀ Ψ : WilkiesDesign.CG.LEc.Formula (Fin n),
        Work.WilC6.IsEF Ψ → Work.WilC6.EFCons φ Ψ → Ψ.Realize b) → φ.Realize b) :
    ∃ Ψ : WilkiesDesign.CG.LEc.Formula (Fin n),
      Work.WilC6.IsEF Ψ ∧ Work.WilC6.EFCons φ Ψ ∧ Work.WilC6.EFCons Ψ φ := by
  classical
  -- `G` is the set of `IsEF`-consequences of `φ`
  let G : Set (LEc.Formula (Fin n)) := {Ψ | IsEF Ψ ∧ EFCons φ Ψ}
  -- `TE` together with those consequences, in the language with constants for `Fin n`
  let T : (LEc[[Fin n]]).Theory :=
    (LEc.lhomWithConstants (Fin n)).onTheory TE ∪ Formula.equivSentence '' G
  have hTdef : T = (LEc.lhomWithConstants (Fin n)).onTheory TE ∪ Formula.equivSentence '' G :=
    rfl
  -- the whole theory entails `φ`
  have hTmodel : T ⊨ᵇ Formula.equivSentence φ := by
    rw [Theory.models_sentence_iff]
    intro M
    letI : LEc.Structure M := (LEc.lhomWithConstants (Fin n)).reduct M
    have hMTE : M ⊨ TE :=
      ((LEc.lhomWithConstants (Fin n)).onTheory_model TE).1
        (Theory.Model.mono M.is_model (by rw [hTdef]; exact Set.subset_union_left))
    haveI := hMTE
    refine (Formula.realize_equivSentence M φ).2 (h M (fun a => (LEc.con a : M)) ?_)
    intro Ψ hIsEF hEFC
    have hmem : Formula.equivSentence Ψ ∈ T := by
      rw [hTdef]
      exact Set.mem_union_right _ ⟨Ψ, ⟨hIsEF, hEFC⟩, rfl⟩
    exact (Formula.realize_equivSentence M Ψ).1 (Theory.realize_sentence_of_mem T hmem)
  -- compactness: a finite subtheory already entails `φ`
  obtain ⟨T0, hT0sub, hT0model⟩ :=
    (Language.Theory.models_iff_finset_models (T := T)
      (φ := Formula.equivSentence φ)).1 hTmodel
  -- extract the finitely many `IsEF`-consequences occurring in `T0`
  let pick : (LEc[[Fin n]]).Sentence → LEc.Formula (Fin n) := fun ψ =>
    if hh : ∃ Ψ : LEc.Formula (Fin n), IsEF Ψ ∧ EFCons φ Ψ ∧ Formula.equivSentence Ψ = ψ
      then hh.choose else ⊤
  let l : List (LEc.Formula (Fin n)) := T0.toList.map pick
  have hpick : ∀ ψ : (LEc[[Fin n]]).Sentence, IsEF (pick ψ) ∧ EFCons φ (pick ψ) := by
    intro ψ
    dsimp only [pick]
    by_cases hh : ∃ Ψ : LEc.Formula (Fin n), IsEF Ψ ∧ EFCons φ Ψ ∧
        Formula.equivSentence Ψ = ψ
    · rw [dif_pos hh]
      exact ⟨hh.choose_spec.1, hh.choose_spec.2.1⟩
    · rw [dif_neg hh]
      exact ⟨IsEF.top, fun M _ _ x _ => Formula.realize_top.mpr trivial⟩
  have hlIsEF : ∀ Ψ ∈ l, IsEF Ψ := by
    intro Ψ hΨ
    rw [List.mem_map] at hΨ
    obtain ⟨ψ, _, hEq⟩ := hΨ
    rw [← hEq]
    exact (hpick ψ).1
  have hlEFCons : ∀ Ψ ∈ l, EFCons φ Ψ := by
    intro Ψ hΨ
    rw [List.mem_map] at hΨ
    obtain ⟨ψ, _, hEq⟩ := hΨ
    rw [← hEq]
    exact (hpick ψ).2
  -- the conjunction of the extracted formulas entails `φ`
  have hl_entails : EFCons (l.foldr (· ⊓ ·) ⊤) φ := by
    intro M hMstr hMTE x hx
    have hx' : ∀ Ψ ∈ l, Ψ.Realize x := by
      have h' := hx
      rw [Formula.Realize, BoundedFormula.realize_foldr_inf] at h'
      exact h'
    letI : (constantsOn (Fin n)).Structure M := constantsOn.structure x
    -- reading a sentence of `LEc[[Fin n]]` back in the variables `x`
    have key : ∀ Ψ : LEc.Formula (Fin n),
        (Formula.equivSentence Ψ).Realize M ↔ Ψ.Realize x := by
      intro Ψ
      exact (Formula.realize_equivSentence_symm M (Formula.equivSentence Ψ) x).symm.trans
        (by rw [_root_.Equiv.symm_apply_apply])
    haveI : M ⊨ (LEc.lhomWithConstants (Fin n)).onTheory TE :=
      ((LEc.lhomWithConstants (Fin n)).onTheory_model TE).2 hMTE
    have hMT0 : M ⊨ (T0 : (LEc[[Fin n]]).Theory) := by
      rw [Theory.model_iff]
      intro ψ hψ
      have hψT := hT0sub hψ
      rw [hTdef, Set.mem_union] at hψT
      rcases hψT with hψT | hψimg
      · exact Theory.realize_sentence_of_mem
          ((LEc.lhomWithConstants (Fin n)).onTheory TE) hψT
      · rw [Set.mem_image] at hψimg
        obtain ⟨Ψ, ⟨hIsEF, hEFC⟩, hEq⟩ := hψimg
        rw [← hEq]
        have hh : ∃ Ψ' : LEc.Formula (Fin n), IsEF Ψ' ∧ EFCons φ Ψ' ∧
            Formula.equivSentence Ψ' = Formula.equivSentence Ψ := ⟨Ψ, hIsEF, hEFC, rfl⟩
        have hpickψ : pick (Formula.equivSentence Ψ) = hh.choose := by
          dsimp only [pick]
          rw [dif_pos hh]
        have hmeml : pick (Formula.equivSentence Ψ) ∈ l := by
          rw [List.mem_map]
          exact ⟨Formula.equivSentence Ψ,
            by rw [Finset.mem_toList, hEq]; exact hψ, rfl⟩
        rw [← hh.choose_spec.2.2, ← hpickψ]
        exact (key (pick (Formula.equivSentence Ψ))).2 (hx' _ hmeml)
    haveI : Nonempty M := nonempty_of_LEc_structure M
    haveI : M ⊨ (T0 : (LEc[[Fin n]]).Theory) := hMT0
    exact (key φ).1 (hT0model.realize_sentence M)
  exact ⟨l.foldr (· ⊓ ·) ⊤, IsEF.folds_inf l hlIsEF, EFCons.folds_inf l hlEFCons, hl_entails⟩

end Work.WilC6.Compact
