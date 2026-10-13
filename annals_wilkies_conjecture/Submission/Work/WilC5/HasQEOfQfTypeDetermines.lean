/-
  WilC5 — the quantifier-elimination criterion "the quantifier-free type determines the type".

  The target `Work.WilC5.HasQEOfQfTypeDetermines` proves quantifier elimination for a theory `T`
  from the semantic hypothesis

    `hdet`: two tuples in two models of `T` which realize the same quantifier-free formulas
            realize the same formulas (of the language under consideration).

  The argument has two halves.

  * On *nonempty* models the criterion is a compactness argument, carried out in the language
    `L[[Fin n]]` obtained by naming the `n` free variables by constants: the set `Φ` of
    quantifier-free consequences of `φ` is closed under finite conjunctions and finitely
    axiomatises `φ` modulo `T`.  The key point (`qf_equiv_nonempty`) is that a model `K` of
    `T' ∪ Φ'` cannot satisfy `¬φ`: if it did, the finite subsets of `T' ∪ (quantifier-free type
    of the tuple)' ∪ {φ}` would be satisfiable — otherwise `¬⋀p₀` would be a quantifier-free
    consequence of `φ` and would have to hold at the tuple — so by compactness there is a model
    `L` and a tuple of the same quantifier-free type as the tuple of `K`, and `hdet` transfers
    `φ` from one to the other, a contradiction.

  * On *empty* models the statement is not vacuous only for formulas with no free variables
    (`n = 0`); there the truth value of `φ` is computed by replacing the universal quantifiers of
    `φ` by `⊤` (`qfSkeleton`), and the empty models of `T` are separated from the nonempty ones by
    a quantifier-free sentence (`exists_qf_isEmpty`, proved from `hdet` by compactness: no nonempty
    model can satisfy all the quantifier-free sentences which hold in all empty models of `T`,
    since the empty structure with the same pattern as such a model would have the same
    quantifier-free type and would be a model of `T` as well).
-/
import Mathlib
import Submission.Work.WilC5.ExtQE
import Submission.Work.WilC5.QfSkeleton

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language
open scoped FirstOrder

/-! ## Conjunctions of finitely many quantifier-free formulas -/

theorem isQF_foldr_inf {L : FirstOrder.Language} {α : Type} {n : ℕ}
    (l : List (L.BoundedFormula α n)) (h : ∀ φ ∈ l, φ.IsQF) :
    (l.foldr (· ⊓ ·) ⊤).IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.imp BoundedFormula.IsQF.falsum BoundedFormula.IsQF.falsum
  | cons a t ih =>
      exact BoundedFormula.IsQF.inf (h a (List.mem_cons_self ..))
        (ih fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))

theorem isQF_iInf {L : FirstOrder.Language} {α : Type} {n : ℕ} {β : Type} [Finite β]
    {f : β → L.BoundedFormula α n} (h : ∀ b, (f b).IsQF) : (BoundedFormula.iInf f).IsQF := by
  rw [BoundedFormula.iInf]
  exact isQF_foldr_inf _ (by
    intro φ hφ
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hφ
    exact h b)

/-! ## The criterion on nonempty models -/

/-- **Quantifier elimination on nonempty models.**  If the quantifier-free type determines the full
type (the hypothesis `hdet`), then every formula `φ` is equivalent, on every *nonempty* model of
`T`, to a quantifier-free formula. -/
theorem qf_equiv_nonempty {L : FirstOrder.Language.{0, 0}} (T : L.Theory)
    (hdet : ∀ {n : ℕ} (M N : Type) [L.Structure M] [L.Structure N],
      FirstOrder.Language.Theory.Model M T → FirstOrder.Language.Theory.Model N T →
      ∀ (v : Fin n → M) (w : Fin n → N), Work.WilC5.IsQFEqv (L := L) v w →
      ∀ ψ : L.Formula (Fin n),
        (FirstOrder.Language.Formula.Realize ψ v ↔ FirstOrder.Language.Formula.Realize ψ w))
    {n : ℕ} (φ : L.Formula (Fin n)) :
    ∃ θ : L.Formula (Fin n), θ.IsQF ∧
      ∀ (M : Type) [L.Structure M] [Nonempty M], M ⊨ T → ∀ x : Fin n → M,
        φ.Realize x ↔ θ.Realize x := by
  classical
  -- the quantifier-free consequences of `φ` over the nonempty models of `T`
  let Φ : Set (L.Formula (Fin n)) := {θ | θ.IsQF ∧
    (∀ (N : Type) [L.Structure N] [Nonempty N], N ⊨ T → ∀ y : Fin n → N,
      φ.Realize y → θ.Realize y)}
  -- the same language with the `n` free variables named by constants
  let T' : L[[Fin n]].Theory := (L.lhomWithConstants (Fin n)).onTheory T
  let Φ' : Set L[[Fin n]].Sentence := {σ | ∃ θ ∈ Φ, σ = Formula.equivSentence θ}
  -- every nonempty `L[[Fin n]]`-model of `T' ∪ Φ'` satisfies `φ`
  have hmain : (T' ∪ Φ') ⊨ᵇ (Formula.equivSentence φ) := by
    rw [Theory.models_sentence_iff]
    intro K
    letI : L.Structure ↑K := (L.lhomWithConstants (Fin n)).reduct ↑K
    have hK : (↑K : Type) ⊨ (T' ∪ Φ') := K.is_model
    have hTM : (↑K : Type) ⊨ T' := Theory.Model.mono hK Set.subset_union_left
    have hKT : (↑K : Type) ⊨ T := (LHom.onTheory_model (L.lhomWithConstants (Fin n)) T).1 hTM
    let w : Fin n → (↑K : Type) := fun i => (L.con i : ↑K)
    have hKΦ : ∀ θ ∈ Φ, θ.Realize w := by
      intro θ hθ
      have hmem : Formula.equivSentence θ ∈ (T' ∪ Φ') := Set.mem_union_right _ ⟨θ, hθ, rfl⟩
      have h1 : (↑K : Type) ⊨ Formula.equivSentence θ := (Theory.model_iff _).mp hK _ hmem
      exact (Formula.realize_equivSentence (↑K : Type) θ).1 h1
    suffices hfin : φ.Realize w by
      exact (Formula.realize_equivSentence (↑K : Type) φ).2 hfin
    by_contra hw
    -- the quantifier-free type of the tuple `w`
    let Q : Set L[[Fin n]].Sentence :=
      {σ | ∃ θ, θ.IsQF ∧ θ.Realize w ∧ σ = Formula.equivSentence θ}
    -- `T' ∪ (quantifier-free type of `w`)' ∪ {φ}` is satisfiable
    have hVsat : Theory.IsSatisfiable (T' ∪ Q ∪ {Formula.equivSentence φ}) := by
      rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
      intro F hFsub
      let Fq : Finset L[[Fin n]].Sentence :=
        F.filter (fun σ => ∃ θ, θ.IsQF ∧ θ.Realize w ∧ σ = Formula.equivSentence θ)
      let pick : ↥Fq → L.Formula (Fin n) :=
        fun σ => Classical.choose (Finset.mem_filter.mp σ.2).2
      have pick_spec : ∀ σ : ↥Fq, (pick σ).IsQF ∧ (pick σ).Realize w ∧
          (σ : L[[Fin n]].Sentence) = Formula.equivSentence (pick σ) :=
        fun σ => Classical.choose_spec (Finset.mem_filter.mp σ.2).2
      let θF : L.Formula (Fin n) := Formula.iInf (fun σ : ↥Fq => pick σ)
      have hθFqf : θF.IsQF := isQF_iInf (fun σ => (pick_spec σ).1)
      have hθFre : ∀ {M : Type} [L.Structure M] (y : Fin n → M),
          θF.Realize y ↔ ∀ σ : ↥Fq, (pick σ).Realize y := fun y => Formula.realize_iInf
      by_cases hcase : ∃ (M : T.ModelType), ∃ y : Fin n → ↑M, θF.Realize y ∧ φ.Realize y
      · -- there is a model whose tuple satisfies the finitely many formulas and `φ`
        obtain ⟨M, y, hyθ, hyφ⟩ := hcase
        letI : (constantsOn (Fin n)).Structure ↑M := constantsOn.structure y
        letI : L[[Fin n]].Structure ↑M := Language.sumStructure L (constantsOn (Fin n)) ↑M
        haveI : (L.lhomWithConstants (Fin n)).IsExpansionOn ↑M := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
        have hMT : (↑M : Type) ⊨ T := M.is_model
        have hMF : (↑M : Type) ⊨ (↑F : L[[Fin n]].Theory) := by
          rw [Theory.model_iff]
          intro σ hσ
          have hσV : σ ∈ T' ∪ Q ∪ {Formula.equivSentence φ} := hFsub hσ
          rcases hσV with (hσT | hσQ) | hσφ
          · exact (Theory.model_iff _).mp
              ((LHom.onTheory_model (L.lhomWithConstants (Fin n)) T).2 hMT) σ hσT
          · have hσFq : σ ∈ Fq := Finset.mem_filter.mpr ⟨hσ, hσQ⟩
            have hspec : (σ : L[[Fin n]].Sentence) = Formula.equivSentence (pick ⟨σ, hσFq⟩) :=
              (pick_spec ⟨σ, hσFq⟩).2.2
            rw [hspec]
            exact (Formula.realize_equivSentence (↑M : Type) (pick ⟨σ, hσFq⟩)).2
              ((hθFre y).1 hyθ ⟨σ, hσFq⟩)
          · rw [Set.mem_singleton_iff] at hσφ
            rw [hσφ]
            exact (Formula.realize_equivSentence (↑M : Type) φ).2 hyφ
        exact Theory.Model.isSatisfiable (↑M : Type)
      · -- otherwise `¬θF` is a quantifier-free consequence of `φ`, contradicting `w ⊨ Φ`
        exfalso
        have hmemΦ : (θF.not) ∈ Φ := by
          refine ⟨hθFqf.not, ?_⟩
          intro N instN hNe hN y hyφ
          rw [Formula.realize_not]
          intro hyθ
          exact hcase ⟨Theory.ModelType.of T N, y, hyθ, hyφ⟩
        exact (hKΦ _ hmemΦ) ((hθFre w).mpr (fun σ => (pick_spec σ).2.1))
    -- a model of `T' ∪ Q ∪ {φ}` has a tuple of the same quantifier-free type as `w`
    obtain ⟨K2⟩ := hVsat
    letI : L.Structure ↑K2 := (L.lhomWithConstants (Fin n)).reduct ↑K2
    have hK2U : (↑K2 : Type) ⊨ (T' ∪ Q ∪ {Formula.equivSentence φ}) := K2.is_model
    have hK2T : (↑K2 : Type) ⊨ T :=
      (LHom.onTheory_model (L.lhomWithConstants (Fin n)) T).1
        (Theory.Model.mono (Theory.Model.mono hK2U Set.subset_union_left) Set.subset_union_left)
    let z : Fin n → (↑K2 : Type) := fun i => (L.con i : ↑K2)
    have hzφ : φ.Realize z := by
      have h1 : (↑K2 : Type) ⊨ Formula.equivSentence φ :=
        (Theory.model_iff _).mp hK2U _ (Set.mem_union_right _ (Set.mem_singleton _))
      exact (Formula.realize_equivSentence (↑K2 : Type) φ).1 h1
    have hzQF : ∀ θ : L.Formula (Fin n), θ.IsQF → θ.Realize w → θ.Realize z := by
      intro θ hθqf hθw
      have hmem : Formula.equivSentence θ ∈ (T' ∪ Q ∪ {Formula.equivSentence φ}) :=
        Set.mem_union_left _ (Set.mem_union_right _ ⟨θ, hθqf, hθw, rfl⟩)
      have h1 : (↑K2 : Type) ⊨ Formula.equivSentence θ := (Theory.model_iff _).mp hK2U _ hmem
      exact (Formula.realize_equivSentence (↑K2 : Type) θ).1 h1
    have hiso : IsQFEqv (L := L) z w := by
      intro θ hθqf
      refine ⟨?_, hzQF θ hθqf⟩
      intro hz
      by_contra hwnot
      exact (hzQF θ.not hθqf.not hwnot) hz
    exact hw ((hdet (M := ↑K2) (N := ↑K) hK2T hKT z w hiso φ).1 hzφ)
  -- the finite subset of `T' ∪ Φ'` which axiomatises `φ` modulo `T'`
  have hunsat : ¬ (T' ∪ Φ' ∪ {Formula.equivSentence φ.not}).IsSatisfiable := by
    rintro ⟨K⟩
    letI : L.Structure ↑K := (L.lhomWithConstants (Fin n)).reduct ↑K
    have hK : (↑K : Type) ⊨ (T' ∪ Φ' ∪ {Formula.equivSentence φ.not}) := K.is_model
    haveI hK' : (↑K : Type) ⊨ (T' ∪ Φ') := Theory.Model.mono hK Set.subset_union_left
    have h1 : (↑K : Type) ⊨ Formula.equivSentence φ :=
      (Theory.models_sentence_iff.mp hmain) (Theory.ModelType.of (T' ∪ Φ') (↑K : Type))
    have h2 : (↑K : Type) ⊨ Formula.equivSentence φ.not :=
      (Theory.model_iff _).mp hK _ (Set.mem_union_right _ (Set.mem_singleton _))
    have h2' : ¬ φ.Realize (fun i => (L.con i : ↑K)) := by
      have h := (Formula.realize_equivSentence (↑K : Type) φ.not).1 h2
      rwa [Formula.realize_not] at h
    exact h2' ((Formula.realize_equivSentence (↑K : Type) φ).1 h1)
  have hnotfin : ¬ (T' ∪ Φ' ∪ {Formula.equivSentence φ.not}).IsFinitelySatisfiable :=
    fun h => hunsat ((Theory.isSatisfiable_iff_isFinitelySatisfiable).2 h)
  simp only [Theory.IsFinitelySatisfiable, not_forall] at hnotfin
  obtain ⟨F, hFsub, hFunsat⟩ := hnotfin
  let FΦ : Finset L[[Fin n]].Sentence := F.filter (fun σ => ∃ θ ∈ Φ, σ = Formula.equivSentence θ)
  let pick : ↥FΦ → L.Formula (Fin n) := fun σ => Classical.choose (Finset.mem_filter.mp σ.2).2
  have pick_mem : ∀ σ : ↥FΦ, pick σ ∈ Φ ∧
      (σ : L[[Fin n]].Sentence) = Formula.equivSentence (pick σ) :=
    fun σ => Classical.choose_spec (Finset.mem_filter.mp σ.2).2
  let θs : L.Formula (Fin n) := Formula.iInf (fun σ : ↥FΦ => pick σ)
  have hθsqf : θs.IsQF := isQF_iInf (fun σ => (pick_mem σ).1.1)
  have hθsre : ∀ {M : Type} [L.Structure M] (y : Fin n → M),
      θs.Realize y ↔ ∀ σ : ↥FΦ, (pick σ).Realize y := fun y => Formula.realize_iInf
  refine ⟨θs, hθsqf, fun M instM hne hM x => ⟨?_, ?_⟩⟩
  · intro hx
    exact (hθsre x).mpr (fun σ => (pick_mem σ).1.2 M hM x hx)
  · intro hx
    by_contra hxφ
    -- `M`, expanded by constants for `x`, is a model of the finite subset `F`
    letI : (constantsOn (Fin n)).Structure M := constantsOn.structure x
    letI : L[[Fin n]].Structure M := Language.sumStructure L (constantsOn (Fin n)) M
    haveI : (L.lhomWithConstants (Fin n)).IsExpansionOn M := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    have hMF : M ⊨ (↑F : L[[Fin n]].Theory) := by
      rw [Theory.model_iff]
      intro σ hσ
      have hσU : σ ∈ T' ∪ Φ' ∪ {Formula.equivSentence φ.not} := hFsub hσ
      rcases hσU with (hσT | hσΦ) | hσn
      · exact (Theory.model_iff _).mp
          ((LHom.onTheory_model (L.lhomWithConstants (Fin n)) T).2 hM) σ hσT
      · have hσFΦ : σ ∈ FΦ := Finset.mem_filter.mpr ⟨hσ, hσΦ⟩
        have hspec : (σ : L[[Fin n]].Sentence) = Formula.equivSentence (pick ⟨σ, hσFΦ⟩) :=
          (pick_mem ⟨σ, hσFΦ⟩).2
        rw [hspec]
        refine (Formula.realize_equivSentence M (pick ⟨σ, hσFΦ⟩)).2 ?_
        have hcon : (fun a => (L.con a : M)) = x := funext fun a => rfl
        rw [hcon]
        exact (hθsre x).1 hx ⟨σ, hσFΦ⟩
      · rw [Set.mem_singleton_iff] at hσn
        rw [hσn]
        refine (Formula.realize_equivSentence M φ.not).2 ?_
        rw [Formula.realize_not]
        have hcon : (fun a => (L.con a : M)) = x := funext fun a => rfl
        rw [hcon]
        exact hxφ
    exact hFunsat (Theory.Model.isSatisfiable M)

/-! ## Emptiness is quantifier-free

The second input to the empty case: given `hdet`, the empty models of `T` are separated from the
nonempty ones by a single quantifier-free sentence.  The key point is that no *nonempty* model of
`T` can satisfy all the quantifier-free sentences which hold in all the empty models of `T`: if
`N` did, then the empty structure with the same values of the nullary relation symbols as `N`
would have the same quantifier-free type as `N` (`qfRealize_pattern`) and would be a model of `T`
(because the skeleton of every axiom of `T` is one of the quantifier-free sentences in question),
so `hdet` would make an empty and a nonempty structure elementarily equivalent. -/

/-- In a language without nullary function symbols there are no closed terms. -/
instance isEmpty_term {L : FirstOrder.Language} {α : Type} [IsEmpty α] [IsEmpty (L.Functions 0)] :
    IsEmpty (L.Term α) :=
  ⟨fun t => Term.rec (motive := fun _ => False) (fun a => isEmptyElim a)
    (fun {l} f _ ih => match l with
      | 0 => IsEmpty.false f
      | (m+1) => ih ⟨0, Nat.succ_pos m⟩) t⟩

/-- A quantifier-free formula without free variables in a language without constants has the same
truth value in any two structures with the same values of the nullary relation symbols. -/
theorem qfRealize_pattern {L : FirstOrder.Language} {α : Type} [IsEmpty α]
    [IsEmpty (L.Functions 0)] {M : Type} [L.Structure M] {N : Type} [L.Structure N]
    (hpat : ∀ R : L.Relations 0,
      @Structure.RelMap L M _ 0 R (default : Fin 0 → M) ↔
        @Structure.RelMap L N _ 0 R (default : Fin 0 → N))
    (v : α → M) (w : α → N) {θ : L.BoundedFormula α 0} (hθ : θ.IsQF) :
    @BoundedFormula.Realize L M _ α 0 θ v (default : Fin 0 → M) ↔
      @BoundedFormula.Realize L N _ α 0 θ w (default : Fin 0 → N) := by
  induction hθ with
  | falsum => exact Iff.rfl
  | of_isAtomic h => cases h with
    | equal t₁ t₂ => exact (IsEmpty.false t₁).elim
    | rel R ts =>
        cases ‹ℕ› with
        | zero =>
            change @Structure.RelMap L M _ 0 R (fun i : Fin 0 =>
                Term.realize (Sum.elim v (default : Fin 0 → M)) (ts i)) ↔
              @Structure.RelMap L N _ 0 R (fun i : Fin 0 =>
                Term.realize (Sum.elim w (default : Fin 0 → N)) (ts i))
            rw [show (fun i : Fin 0 => Term.realize (Sum.elim v (default : Fin 0 → M)) (ts i))
                  = (default : Fin 0 → M) from funext fun i => i.elim0,
              show (fun i : Fin 0 => Term.realize (Sum.elim w (default : Fin 0 → N)) (ts i))
                  = (default : Fin 0 → N) from funext fun i => i.elim0]
            exact hpat R
        | succ m => exact (IsEmpty.false (ts ⟨0, Nat.succ_pos m⟩)).elim
  | imp ha hb iha ihb =>
      exact ⟨fun h ha' => ihb.mp (h (iha.mpr ha')),
             fun h ha' => ihb.mpr (h (iha.mp ha'))⟩

/-- The (unique) `L`-structure with a prescribed pattern on the empty type. -/
@[instance_reducible]
def emptyStruct {L : FirstOrder.Language} [IsEmpty (L.Functions 0)]
    (σ : L.Relations 0 → Prop) : L.Structure Empty where
  funMap := fun {n} f => match n, f with
    | 0, f => fun _ => isEmptyElim f
    | _ + 1, _ => fun x => x ⟨0, Nat.succ_pos _⟩
  RelMap := fun {n} R => match n, R with
    | 0, R => fun _ => σ R
    | _ + 1, _ => fun _ => False

/-- Relabelling the free variables of a quantifier-free formula keeps it quantifier-free. -/
theorem isQF_relabelEquiv {L : FirstOrder.Language} {α β : Type} {k : ℕ} (g : α ≃ β)
    {φ : L.BoundedFormula α k} (h : φ.IsQF) : (BoundedFormula.relabelEquiv g φ).IsQF := by
  induction h with
  | falsum => exact BoundedFormula.IsQF.falsum
  | of_isAtomic ha => cases ha with
    | equal t₁ t₂ => exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.equal _ _)
    | rel R ts => exact BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)
  | imp ha hb iha ihb => exact BoundedFormula.IsQF.imp iha ihb

/-- **Emptiness is quantifier-free.**  Under the hypothesis `hdet` that the quantifier-free type
determines the full type, there is a quantifier-free formula without free variables which holds in
exactly the empty models of `T`. -/
theorem exists_qf_isEmpty {L : FirstOrder.Language.{0, 0}} (T : L.Theory)
    (hdet : ∀ {n : ℕ} (M N : Type) [L.Structure M] [L.Structure N],
      FirstOrder.Language.Theory.Model M T → FirstOrder.Language.Theory.Model N T →
      ∀ (v : Fin n → M) (w : Fin n → N), Work.WilC5.IsQFEqv (L := L) v w →
      ∀ ψ : L.Formula (Fin n),
        (FirstOrder.Language.Formula.Realize ψ v ↔ FirstOrder.Language.Formula.Realize ψ w)) :
    ∃ ξ : L.Formula (Fin 0), ξ.IsQF ∧
      ∀ (M : Type) [L.Structure M], FirstOrder.Language.Theory.Model M T →
        (FirstOrder.Language.Formula.Realize ξ (fun i : Fin 0 => i.elim0 : Fin 0 → M) ↔ IsEmpty M) := by
  classical
  by_cases hempty : ∃ (K : Type) (inst : L.Structure K), @Theory.Model L K inst T ∧ IsEmpty K
  · obtain ⟨K, instK, hKT, hKempty⟩ := hempty
    haveI hFn : IsEmpty (L.Functions 0) :=
      ⟨fun f => hKempty.false (@Structure.funMap L K instK 0 f (default : Fin 0 → K))⟩
    -- the quantifier-free sentences which hold in every empty model of `T`
    let Ξ : L.Theory := {σ : L.Sentence | σ.IsQF ∧
      ∀ (K' : Type) (inst : L.Structure K'), IsEmpty K' → @Theory.Model L K' inst T →
        @Sentence.Realize L K' inst σ}
    -- no nonempty model of `T` satisfies all of them
    have hunsat : ¬ (T ∪ Ξ).IsSatisfiable := by
      rintro ⟨N⟩
      have hN1 : @Theory.Model L ↑N _ T := Theory.Model.mono N.is_model Set.subset_union_left
      have hN2 : @Theory.Model L ↑N _ Ξ := Theory.Model.mono N.is_model Set.subset_union_right
      let σ₀ : L.Relations 0 → Prop := fun R => @Structure.RelMap L ↑N _ 0 R (default : Fin 0 → ↑N)
      letI : L.Structure Empty := emptyStruct σ₀
      have hpat : ∀ R : L.Relations 0,
          @Structure.RelMap L Empty _ 0 R (default : Fin 0 → Empty) ↔
            @Structure.RelMap L ↑N _ 0 R (default : Fin 0 → ↑N) := fun R => Iff.rfl
      have hskE : ∀ ψ : L.Sentence, @Sentence.Realize L Empty _ ψ ↔
          @Sentence.Realize L Empty _ (qfSkeleton ψ) := fun ψ =>
        (qfSkeleton_realize (M := Empty) ψ (default : Empty → Empty)
          (default : Fin 0 → Empty)).symm
      have hpq : ∀ ψ : L.Sentence, @Sentence.Realize L Empty _ (qfSkeleton ψ) ↔
          @Sentence.Realize L ↑N _ (qfSkeleton ψ) := fun ψ =>
        qfRealize_pattern (α := Empty) hpat (default : Empty → Empty) (default : Empty → ↑N)
          (isQF_qfSkeleton ψ)
      have hET : @Theory.Model L Empty _ T := by
        rw [Theory.model_iff]
        intro ψ hψ
        have hmem : qfSkeleton ψ ∈ Ξ :=
          ⟨isQF_qfSkeleton ψ, fun K' inst' hK'i hK'T =>
            (qfSkeleton_realize ψ (default : Empty → K') (default : Fin 0 → K')).mpr
              ((Theory.model_iff _).mp hK'T ψ hψ)⟩
        exact (hskE ψ).mpr ((hpq ψ).mpr ((Theory.model_iff _).mp hN2 (qfSkeleton ψ) hmem))
      have hiso : IsQFEqv (L := L) (fun i : Fin 0 => i.elim0 : Fin 0 → Empty)
          (fun i : Fin 0 => i.elim0 : Fin 0 → ↑N) := fun θ hθ =>
        qfRealize_pattern (α := Fin 0) hpat (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) hθ
      -- an empty and a nonempty model of `T` with the same quantifier-free type
      have hcon := hdet (M := Empty) (N := ↑N) hET hN1
        (fun i : Fin 0 => i.elim0 : Fin 0 → Empty) (fun i : Fin 0 => i.elim0 : Fin 0 → ↑N) hiso
        ((⊤ : L.BoundedFormula (Fin 0) 1).exs)
      simp only [BoundedFormula.realize_exs, BoundedFormula.realize_top] at hcon
      obtain ⟨xs, -⟩ := hcon.mpr ⟨fun _ => Classical.arbitrary ↑N, trivial⟩
      exact isEmptyElim (xs 0)
    have hnotfin : ¬ (T ∪ Ξ).IsFinitelySatisfiable :=
      fun h => hunsat ((Theory.isSatisfiable_iff_isFinitelySatisfiable).2 h)
    simp only [Theory.IsFinitelySatisfiable, not_forall] at hnotfin
    obtain ⟨F, hFsub, hFunsat⟩ := hnotfin
    let ΞF : Finset L.Sentence := F.filter (fun σ => σ ∈ Ξ)
    let ξs : L.Sentence := Formula.iInf (fun σ : ↥ΞF => (σ : L.Sentence))
    have hξsqf : ξs.IsQF := isQF_iInf (fun σ => (Finset.mem_filter.mp σ.2).2.1)
    have hξsre : ∀ {M : Type} [L.Structure M] (v : Empty → M),
        @Formula.Realize L M _ Empty ξs v ↔
          ∀ σ : ↥ΞF, @Formula.Realize L M _ Empty (σ : L.Sentence) v :=
      fun v => Formula.realize_iInf
    have htrue : ∀ (K' : Type) (inst : L.Structure K'), IsEmpty K' → @Theory.Model L K' inst T →
        @Sentence.Realize L K' inst ξs := by
      intro K' inst' hK'i hK'T
      rw [show @Sentence.Realize L K' inst' ξs ↔
          ∀ σ : ↥ΞF, @Sentence.Realize L K' inst' (σ : L.Sentence) from hξsre (default : Empty → K')]
      intro σ
      exact (Finset.mem_filter.mp σ.2).2.2 K' inst' hK'i hK'T
    have hfalse : ∀ (M : Type) (inst : L.Structure M), Nonempty M → @Theory.Model L M inst T →
        ¬ @Sentence.Realize L M inst ξs := by
      intro M inst' hne hMT hξ
      have hMF : @Theory.Model L M inst' (↑F : L.Theory) := by
        rw [Theory.model_iff]
        intro σ hσ
        have hσU : σ ∈ T ∪ Ξ := hFsub hσ
        rcases hσU with hσT | hσΞ
        · exact (Theory.model_iff _).mp hMT σ hσT
        · have hσΞF : σ ∈ ΞF := Finset.mem_filter.mpr ⟨hσ, hσΞ⟩
          exact (hξsre (default : Empty → M)).mp hξ ⟨σ, hσΞF⟩
      exact hFunsat (Theory.Model.isSatisfiable M)
    refine ⟨(BoundedFormula.relabelEquiv (Equiv.equivOfIsEmpty Empty (Fin 0))) ξs, ?_, ?_⟩
    · exact isQF_relabelEquiv _ hξsqf
    · intro M instM hMT
      have hconv : @Formula.Realize L M instM (Fin 0)
            ((BoundedFormula.relabelEquiv (Equiv.equivOfIsEmpty Empty (Fin 0))) ξs)
            (fun i : Fin 0 => i.elim0) ↔ @Sentence.Realize L M instM ξs := by
        refine (@BoundedFormula.realize_relabelEquiv L M instM Empty (Fin 0)
          (Equiv.equivOfIsEmpty Empty (Fin 0)) 0 ξs (fun i : Fin 0 => i.elim0)
          (default : Fin 0 → M)).trans ?_
        rw [show ((fun i : Fin 0 => i.elim0) ∘ (Equiv.equivOfIsEmpty Empty (Fin 0))) =
            (default : Empty → M) from funext fun e => e.elim]
        rfl
      refine hconv.trans ?_
      by_cases hne : Nonempty M
      · exact ⟨fun h => absurd h (hfalse M instM hne hMT),
          fun h => absurd h (not_isEmpty_iff.mpr hne)⟩
      · exact ⟨fun _ => not_nonempty_iff.mp hne,
          fun h => htrue M instM (not_nonempty_iff.mp hne) hMT⟩
  · -- `T` has no empty model: `⊥` works
    refine ⟨⊥, BoundedFormula.IsQF.falsum, fun M instM hMT => ?_⟩
    have hne : ¬ IsEmpty M := fun h => hempty ⟨M, instM, hMT, h⟩
    exact ⟨fun h => (h : False).elim, fun h => absurd h hne⟩

/-! ## The target -/

theorem HasQEOfQfTypeDetermines {L : FirstOrder.Language.{0, 0}} (T : L.Theory)
    (hdet : ∀ {n : ℕ} (M N : Type) [L.Structure M] [L.Structure N],
      FirstOrder.Language.Theory.Model M T → FirstOrder.Language.Theory.Model N T →
      ∀ (v : Fin n → M) (w : Fin n → N), Work.WilC5.IsQFEqv (L := L) v w →
      ∀ ψ : L.Formula (Fin n),
        (FirstOrder.Language.Formula.Realize ψ v ↔ FirstOrder.Language.Formula.Realize ψ w)) :
    Work.WilC5.HasQE T := by
  classical
  intro n φ
  obtain ⟨θ, hθqf, hθ⟩ := qf_equiv_nonempty T hdet φ
  by_cases hn : n = 0
  · -- no free variables: the empty models have to be handled separately
    subst hn
    obtain ⟨ξ, hξqf, hξ⟩ := exists_qf_isEmpty T hdet
    refine ⟨(ξ ⊓ qfSkeleton φ) ⊔ (ξ.not ⊓ θ), ?_, ?_⟩
    · exact BoundedFormula.IsQF.sup (BoundedFormula.IsQF.inf hξqf (isQF_qfSkeleton φ))
        (BoundedFormula.IsQF.inf hξqf.not hθqf)
    · intro M instM hM x
      by_cases hne : Nonempty M
      · -- a nonempty model: `ξ` is false, so `θ` decides
        haveI : Nonempty M := hne
        have hξx : ¬ ξ.Realize x := by
          intro h
          have hx : x = (fun i : Fin 0 => i.elim0) := funext fun i => i.elim0
          rw [hx] at h
          exact (not_isEmpty_iff.mpr hne) ((hξ M hM).mp h)
        rw [Formula.realize_sup, Formula.realize_inf, Formula.realize_inf, Formula.realize_not]
        constructor
        · intro hφx
          exact Or.inr ⟨hξx, (hθ M hM x).mp hφx⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h hξx
          · exact (hθ M hM x).mpr h
      · -- an empty model: `ξ` holds and the skeleton of `φ` computes `φ`
        haveI hMempty : IsEmpty M := not_nonempty_iff.mp hne
        have hξx : ξ.Realize x := by
          have hx : x = (fun i : Fin 0 => i.elim0) := funext fun i => i.elim0
          rw [hx]
          exact (hξ M hM).mpr hMempty
        have hφsk : @Formula.Realize L M instM (Fin 0) (qfSkeleton φ) x ↔
            @Formula.Realize L M instM (Fin 0) φ x := qfSkeleton_realize_formula φ x
        rw [Formula.realize_sup, Formula.realize_inf, Formula.realize_inf, Formula.realize_not]
        constructor
        · intro hφx
          exact Or.inl ⟨hξx, hφsk.mpr hφx⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact hφsk.mp h
          · exact absurd hξx h
  · -- at least one free variable: an empty model carries no tuples
    refine ⟨θ, hθqf, fun M instM hM x => ?_⟩
    by_cases hne : Nonempty M
    · haveI : Nonempty M := hne
      exact hθ M hM x
    · exact absurd ⟨x ⟨0, Nat.pos_of_ne_zero hn⟩⟩ hne

end Work.WilC5
