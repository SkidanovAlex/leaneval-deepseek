import Mathlib
import Submission.Work.WilC6.Base
import Submission.Work.WilC6.Transfer.exists_chi_of_isEF
import Submission.Work.WilC6.Transfer.defs

set_option autoImplicit false
noncomputable section

open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open Work.WilC6

namespace Work.WilC6.Transfer

/-! ### Auxiliary syntactic sentences -/

/-- The `LEc[[M]]`-sentence saying that two `M`-constants are distinct. -/
def injSent {M : Type} [LEc.Structure M] (m₁ m₂ : M) : LEc[[M]].Sentence :=
  BoundedFormula.not
    (Term.bdEqual (cTerm (L := LEc[[M]]) (LEc.con m₁))
      (cTerm (L := LEc[[M]]) (LEc.con m₂)))

/-- The `LEc[[M]]`-sentence saying that a function symbol is compatible with the constants. -/
def funSent {M : Type} [LEc.Structure M] {j : ℕ} (f : LEc.Functions j) (x : Fin j → M) :
    LEc[[M]].Sentence :=
  Term.bdEqual (cTerm (L := LEc[[M]]) (LEc.con (Structure.funMap (L := LEc) f x)))
    (Term.func (Sum.inl f : (LEc[[M]]).Functions j)
      fun l => cTerm (L := LEc[[M]]) (LEc.con (x l)))

theorem isEF_injSent {M : Type} [LEc.Structure M] (m₁ m₂ : M) : IsEF (injSent m₁ m₂) :=
  IsEF.bdNe _ _

theorem isEF_funSent {M : Type} [LEc.Structure M] {j : ℕ} (f : LEc.Functions j)
    (x : Fin j → M) : IsEF (funSent f x) :=
  IsEF.bdEq _ _

theorem realize_injSent {M : Type} [LEc.Structure M] {K : Type} [LEc.Structure K]
    [LEc[[M]].Structure K] [(LEc.lhomWithConstants M).IsExpansionOn K] (m₁ m₂ : M) :
    (K ⊨ injSent m₁ m₂) ↔
      (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m₁) : K)
        ≠ (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m₂) : K) := by
  simp only [Sentence.Realize, Formula.Realize, injSent, BoundedFormula.realize_not]
  rw [BoundedFormula.realize_bdEqual]
  simp only [Term.realize, funMap_eq_coe_constants]

theorem realize_funSent {M : Type} [LEc.Structure M] {K : Type} [LEc.Structure K]
    [LEc[[M]].Structure K] [(LEc.lhomWithConstants M).IsExpansionOn K]
    {j : ℕ} (f : LEc.Functions j) (x : Fin j → M) :
    (K ⊨ funSent f x) ↔
      (FirstOrder.Language.constantMap (L := LEc[[M]])
          (LEc.con (Structure.funMap (L := LEc) f x)) : K)
        = (Structure.funMap (L := LEc[[M]]) (Sum.inl f : (LEc[[M]]).Functions j)
            (fun l => (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con (x l)) : K)) : K) := by
  simp only [Sentence.Realize, Formula.Realize, funSent]
  rw [BoundedFormula.realize_bdEqual]
  simp only [Term.realize, funMap_eq_coe_constants]

/-! ### The atomic-diagram embedding -/

/-- **The atomic-diagram embedding.**  If `K` satisfies every `IsEF` sentence of `LEc[[M]]` true in
`M`, then `M` embeds into `K` by sending `m` to the interpretation of the constant `m`. -/
theorem exists_embedding_of_isEF {M : Type} [LEc.Structure M] {K : Type} [LEc.Structure K]
    [LEc[[M]].Structure K] [(LEc.lhomWithConstants M).IsExpansionOn K]
    (h : ∀ ψ : LEc[[M]].Sentence, IsEF ψ → (M ⊨ ψ) → (K ⊨ ψ)) :
    ∃ e : M ↪[LEc] K,
      ∀ m, e m = (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m) : K) := by
  have hinj : Function.Injective
      (fun m => (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m) : K)) := by
    intro m₁ m₂ hm
    by_contra hne
    have hM : M ⊨ injSent m₁ m₂ := by
      rw [realize_injSent, constantMap_con_self, constantMap_con_self]
      exact hne
    have hK := h _ (isEF_injSent m₁ m₂) hM
    rw [realize_injSent] at hK
    exact hK hm
  have hmap : ∀ {j : ℕ} (f : LEc.Functions j) (x : Fin j → M),
      (fun m => (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m) : K))
          (Structure.funMap (L := LEc) f x)
        = Structure.funMap (L := LEc) f
          ((fun m => (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m) : K)) ∘ x) := by
    intro j f x
    have hM : M ⊨ funSent f x := by
      rw [realize_funSent]
      simp only [constantMap_con_self]
      exact (LHom.map_onFunction (LEc.lhomWithConstants M) f (fun l => x l)).symm
    have hK := h _ (isEF_funSent f x) hM
    rw [realize_funSent] at hK
    have hbeta : (fun m => (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m) : K))
        (Structure.funMap (L := LEc) f x)
        = (FirstOrder.Language.constantMap (L := LEc[[M]])
            (LEc.con (Structure.funMap (L := LEc) f x)) : K) := rfl
    rw [hbeta, hK]
    exact LHom.map_onFunction (LEc.lhomWithConstants M) f
      (fun l => (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con (x l)) : K))
  refine ⟨⟨⟨fun m => (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m) : K), hinj⟩,
    fun {j} f x => hmap f x, fun {j} r x => ?_⟩, fun m => rfl⟩
  haveI : IsEmpty (LEc.Relations j) := by
    have hAlg : LEc.IsAlgebraic := by
      rw [show LEc = WilkiesConjecture.expRing.sum (constantsOn ℝ) from rfl]
      infer_instance
    exact hAlg j
  exact isEmptyElim r

/-! ### Satisfiability of the amalgamation theory -/

theorem amalgTheory_isSatisfiable {n : ℕ} (M : Type) [LEc.Structure M] (N : Type)
    [LEc.Structure N] [Theory.Model N TE] (a : Fin n → M) (b : Fin n → N)
    (h : ∀ Ψ : LEc.Formula (Fin n), IsEF Ψ → Formula.Realize Ψ a → Formula.Realize Ψ b)
    (hb : ∀ i j : Fin n, a i = a j → b i = b j) :
    Theory.IsSatisfiable (amalgTheory M N a b) := by
  haveI : Nonempty (diagIdx M) := ⟨⟨∅, by intro ψ hψ; simp at hψ⟩⟩
  have hdir : Directed (· ⊆ ·) (Tp M N a b) := by
    rintro F G
    refine ⟨⟨F.val ∪ G.val, by
      intro ψ hψ
      rw [Finset.mem_union] at hψ
      exact hψ.elim (F.property ψ) (G.property ψ)⟩, ?_, ?_⟩
    · intro φ hφ
      have hone : (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).onTheory ((F.val : Set _)) ⊆
          (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).onTheory ((F.val ∪ G.val : Finset _) : Set _) :=
        Set.image_mono (by intro x hx; rw [Finset.mem_coe, Finset.mem_union]; exact Or.inl hx)
      simp only [Tp, Set.mem_union] at hφ ⊢
      exact Or.elim hφ (fun h => Or.inl h) (fun h => Or.inr (hone h))
    · intro φ hφ
      have hone : (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).onTheory ((G.val : Set _)) ⊆
          (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).onTheory ((F.val ∪ G.val : Finset _) : Set _) :=
        Set.image_mono (by intro x hx; rw [Finset.mem_coe, Finset.mem_union]; exact Or.inr hx)
      simp only [Tp, Set.mem_union] at hφ ⊢
      exact Or.elim hφ (fun h => Or.inl h) (fun h => Or.inr (hone h))
  show Theory.IsSatisfiable (⋃ F, Tp M N a b F)
  refine (Theory.isSatisfiable_directed_union_iff hdir).2 (fun F => ?_)
  have hF' : ∀ ψ ∈ F.val, IsEF ψ ∧
      Formula.Realize (BoundedFormula.constantsVarsEquiv ψ) (Sum.elim id (fun e : Empty => e.elim)) :=
    fun ψ hψ => (diagM_mem_iff ψ).1 (F.property ψ hψ)
  obtain ⟨χ, hχa, hχF⟩ := exists_chi_of_isEF a b h hb F.val hF'
  let Φ : M ⊕ N → N := Sum.elim χ id
  letI hΦinst : (constantsOn (M ⊕ N)).Structure N := constantsOn.structure Φ
  letI hL2 : (LEc[[M ⊕ N]]).Structure N := Language.sumStructure LEc (constantsOn (M ⊕ N)) N
  letI hLM : LEc[[M]].Structure N := (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).reduct N
  have hΦi : ∀ m, Φ (Sum.inl m) = χ m := fun m => rfl
  have hΦr : ∀ nn, Φ (Sum.inr nn) = nn := fun nn => rfl
  have hcoe : ∀ z : M ⊕ N, (FirstOrder.Language.constantMap (L := LEc.sum (constantsOn (M ⊕ N)))
      (Sum.inr z) : N) = Φ z := by
    intro z
    dsimp only [FirstOrder.Language.constantMap, Language.sumStructure,
      Language.constantsOn.structure]
    rfl
  haveI hAexp : (LEc.lhomWithConstants (M ⊕ N)).IsExpansionOn N :=
    LHom.isExpansionOn_reduct (LEc.lhomWithConstants (M ⊕ N)) N
  haveI hBmap : (LHom.constantsOnMap (Sum.inr : N → M ⊕ N)).IsExpansionOn N :=
    Language.constantsOnMap_isExpansionOn (f := (Sum.inr : N → M ⊕ N)) (fα := fun nn : N => nn)
      (fβ := Φ) (by funext nn; rfl)
  haveI hBexp : (LEc.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)).IsExpansionOn N :=
    LHom.sumMap_isExpansionOn (LHom.id LEc) (LHom.constantsOnMap (Sum.inr : N → M ⊕ N)) N
  haveI hCexp : (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).IsExpansionOn N :=
    LHom.isExpansionOn_reduct (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)) N
  haveI hMexp : (LEc.lhomWithConstants M).IsExpansionOn N :=
    LHom.isExpansionOn_reduct (LEc.lhomWithConstants M) N
  have hA : N ⊨ (LEc.lhomWithConstants (M ⊕ N)).onTheory TE := by
    rw [LHom.onTheory_model]
    exact ‹N ⊨ TE›
  have hB : N ⊨ (LEc.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)).onTheory
      (LEc[[N]].completeTheory N) := by
    refine ⟨fun φ hφ => ?_⟩
    obtain ⟨ψ, hψ, rfl⟩ := LHom.mem_onTheory.1 hφ
    exact (LHom.realize_onSentence (M := N)
      (LEc.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)) ψ).2 hψ
  have hD : N ⊨ Set.range (linkSentence a b) := by
    refine ⟨fun φ hφ => ?_⟩
    obtain ⟨i, rfl⟩ := hφ
    have hbd : (linkSentence a b i).Realize N ↔
        (FirstOrder.Language.constantMap (L := LEc.sum (constantsOn (M ⊕ N)))
            (Sum.inr (Sum.inl (a i)) : (LEc.sum (constantsOn (M ⊕ N))).Functions 0) : N)
          = (FirstOrder.Language.constantMap (L := LEc.sum (constantsOn (M ⊕ N)))
            (Sum.inr (Sum.inr (b i)) : (LEc.sum (constantsOn (M ⊕ N))).Functions 0) : N) :=
      BoundedFormula.realize_bdEqual _ _
    rw [hbd, hcoe, hcoe, hΦi, hΦr]
    exact hχa i
  have hC : N ⊨ (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).onTheory (F.val : Set _) := by
    refine ⟨fun φ hφ => ?_⟩
    obtain ⟨ψ, hψF, rfl⟩ := LHom.mem_onTheory.1 hφ
    rw [LHom.realize_onSentence (M := N) (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)) ψ]
    have hkey : (N ⊨ ψ) ↔
        Formula.Realize (BoundedFormula.constantsVarsEquiv ψ) (Sum.elim χ (fun e : Empty => e.elim)) := by
      have h := @BoundedFormula.realize_constantsVarsEquiv LEc N _ M Empty _ _ 0 ψ
        (default : Empty → N) (default : Fin 0 → N)
      have hass : (Sum.elim (fun m : M => ↑(LEc.con m)) (default : Empty → N) : M ⊕ Empty → N)
          = Sum.elim χ (fun e : Empty => e.elim) := by
        funext x; rcases x with m | e
        · simp only [Sum.elim_inl]
          show (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m) : N) = χ m
          dsimp only [FirstOrder.Language.constantMap, LHom.reduct,
            FirstOrder.Language.lhomWithConstantsMap, LHom.sumMap, LHom.id,
            LHom.constantsOnMap, Sum.map_inr, Sum.map_inl]
          exact (hcoe (Sum.inl m)).trans (hΦi m)
        · exact e.elim
      rw [hass] at h
      exact h.symm
    rw [hkey]
    exact hχF ψ hψF
  have hmodel : N ⊨ Tp M N a b F := by
    refine ⟨fun φ hφ => ?_⟩
    simp only [Tp, Set.mem_union] at hφ
    rcases hφ with ((hφ | hφ) | hφ) | hφ
    · exact hA.realize_of_mem φ hφ
    · exact hB.realize_of_mem φ hφ
    · exact hD.realize_of_mem φ hφ
    · exact hC.realize_of_mem φ hφ
  haveI : Nonempty N :=
    ⟨(FirstOrder.Language.constantMap (L := LEc) (Sum.inr (0 : ℝ) : LEc.Constants) : N)⟩
  exact Theory.Model.isSatisfiable N

/-! ### The transfer theorem -/

theorem transfer_of_isEF (hMC : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TE) {n : ℕ}
    (M N : Type) [WilkiesDesign.CG.LEc.Structure M] [WilkiesDesign.CG.LEc.Structure N]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE]
    [FirstOrder.Language.Theory.Model N WilkiesDesign.CG.TE]
    (a : Fin n → M) (b : Fin n → N)
    (h : ∀ Ψ : WilkiesDesign.CG.LEc.Formula (Fin n),
      Work.WilC6.IsEF Ψ → Ψ.Realize a → Ψ.Realize b)
    (φ : WilkiesDesign.CG.LEc.Formula (Fin n)) : φ.Realize a → φ.Realize b := by
  intro hφa
  have hb : ∀ i j : Fin n, a i = a j → b i = b j := by
    intro i j hij
    have h1 := h (Term.bdEqual (Term.var (Sum.inl i)) (Term.var (Sum.inl j))) (IsEF.bdEq _ _)
      (by simpa [Formula.Realize] using hij)
    simpa [Formula.Realize] using h1
  obtain ⟨KM⟩ := amalgTheory_isSatisfiable M N a b h hb
  letI hKLEc : LEc.Structure KM := (LEc.lhomWithConstants (M ⊕ N)).reduct KM
  letI hKN : LEc[[N]].Structure KM := (LEc.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)).reduct KM
  letI hKM : LEc[[M]].Structure KM := (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).reduct KM
  letI hKcMN : (constantsOn (M ⊕ N)).Structure KM :=
    constantsOn.structure
      fun z => (FirstOrder.Language.constantMap (L := LEc[[M ⊕ N]]) (Sum.inr z) : KM)
  haveI hAexpK : (LEc.lhomWithConstants (M ⊕ N)).IsExpansionOn KM :=
    LHom.isExpansionOn_reduct (LEc.lhomWithConstants (M ⊕ N)) KM
  haveI hBexpK : (LEc.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)).IsExpansionOn KM :=
    LHom.isExpansionOn_reduct (LEc.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)) KM
  haveI hCexpK : (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).IsExpansionOn KM :=
    LHom.isExpansionOn_reduct (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)) KM
  haveI hKNE : (LEc.lhomWithConstants N).IsExpansionOn KM :=
    LHom.isExpansionOn_reduct (LEc.lhomWithConstants N) KM
  haveI hKME : (LEc.lhomWithConstants M).IsExpansionOn KM :=
    LHom.isExpansionOn_reduct (LEc.lhomWithConstants M) KM
  have hmem : ∀ φ' ∈ amalgTheory M N a b, KM ⊨ φ' :=
    (Theory.model_iff _).1 KM.is_model
  have hA : KM ⊨ (LEc.lhomWithConstants (M ⊕ N)).onTheory TE := by
    refine ⟨fun φ' hφ' => hmem φ' ?_⟩
    refine Set.mem_iUnion.mpr ⟨⟨∅, by intro ψ hψ; simp at hψ⟩, ?_⟩
    simp only [Tp, Set.mem_union]
    exact Or.inl (Or.inl (Or.inl hφ'))
  haveI hKTE : KM ⊨ TE := (LHom.onTheory_model _ _).1 hA
  have hB : KM ⊨ (LEc.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)).onTheory
      (LEc[[N]].completeTheory N) := by
    refine ⟨fun φ' hφ' => hmem φ' ?_⟩
    refine Set.mem_iUnion.mpr ⟨⟨∅, by intro ψ hψ; simp at hψ⟩, ?_⟩
    simp only [Tp, Set.mem_union]
    exact Or.inl (Or.inl (Or.inr hφ'))
  haveI hKED : KM ⊨ LEc[[N]].completeTheory N := (LHom.onTheory_model _ _).1 hB
  let f : N ↪ₑ[LEc] KM := ElementaryEmbedding.ofModelsElementaryDiagram LEc N KM
  have hdiag : ∀ ψ : LEc[[M]].Sentence, IsEF ψ → (M ⊨ ψ) → (KM ⊨ ψ) := by
    intro ψ hI hM
    have h2 : KM ⊨ (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).onSentence ψ := by
      refine hmem _ (Set.mem_iUnion.mpr ⟨⟨({ψ} : Finset (LEc[[M]].Sentence)), by
        intro ψ' hψ'
        rw [Finset.mem_singleton] at hψ'
        subst hψ'
        exact ⟨hI, hM⟩⟩, ?_⟩)
      simp only [Tp, Set.mem_union]
      exact Or.inr (Set.mem_image_of_mem _ (Finset.mem_singleton_self ψ))
    exact (LHom.realize_onSentence (M := KM) (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)) ψ).1 h2
  obtain ⟨e, he⟩ := exists_embedding_of_isEF (M := M) (K := KM) hdiag
  have helem : ∀ r : Fin n, e (a r) = f (b r) := by
    intro r
    have h1 : KM ⊨ (linkSentence a b r) := by
      refine hmem _ (Set.mem_iUnion.mpr ⟨⟨∅, by intro ψ hψ; simp at hψ⟩, ?_⟩)
      simp only [Tp, Set.mem_union]
      exact Or.inl (Or.inr (Set.mem_range_self r))
    have h1' : (FirstOrder.Language.constantMap (L := LEc[[M ⊕ N]])
        (Sum.inr (Sum.inl (a r)) : (LEc[[M ⊕ N]]).Functions 0) : KM)
        = (FirstOrder.Language.constantMap (L := LEc[[M ⊕ N]])
        (Sum.inr (Sum.inr (b r)) : (LEc[[M ⊕ N]]).Functions 0) : KM) :=
      (realize_linkSentence a b r).1 h1
    have hA' : (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con (a r)) : KM)
        = (FirstOrder.Language.constantMap (L := LEc[[M ⊕ N]])
           (Sum.inr (Sum.inl (a r)) : (LEc[[M ⊕ N]]).Functions 0) : KM) := by
      dsimp only [FirstOrder.Language.constantMap, LHom.reduct,
        FirstOrder.Language.lhomWithConstantsMap, LHom.sumMap, LHom.id, LHom.constantsOnMap,
        Sum.map_inr, Sum.map_inl]
      rfl
    have hB' : (FirstOrder.Language.constantMap (L := LEc[[N]]) (LEc.con (b r)) : KM)
        = (FirstOrder.Language.constantMap (L := LEc[[M ⊕ N]])
           (Sum.inr (Sum.inr (b r)) : (LEc[[M ⊕ N]]).Functions 0) : KM) := by
      dsimp only [FirstOrder.Language.constantMap, LHom.reduct,
        FirstOrder.Language.lhomWithConstantsMap, LHom.sumMap, LHom.id, LHom.constantsOnMap,
        Sum.map_inr, Sum.map_inl]
      rfl
    rw [he (a r), hA', h1', ← hB']
    rfl
  have heq : (e ∘ a) = (f ∘ b) := funext helem
  have h1 : φ.Realize (e ∘ a) ↔ φ.Realize a := hMC M KM e φ a
  have h2 : φ.Realize (f ∘ b) ↔ φ.Realize b := f.map_formula φ b
  rw [← h2, ← heq, h1]
  exact hφa

end Work.WilC6.Transfer
