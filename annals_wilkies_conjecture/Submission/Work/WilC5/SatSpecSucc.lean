/-
  WilC5 — the successor step of the transfinite construction of a `κ`-saturated elementary
  extension.

  Given that `SatMod3 m` realizes every sentence of the specification `SatSpecG m` (the induction
  hypothesis `hIH`), every finite set of sentences of the specification `SatSpecG (m+1)` is
  satisfiable.  The model is an expansion of `SatMod3 m`: the constants of level `m+1` that already
  existed at level `m` keep their meaning (`SatExpansion` along `SatIncSucc m`), while the constants
  created at level `m` — one for every type over the constants of level `m` — are interpreted by
  witnesses for the (finitely many) formulas required by the given finite set of sentences; those
  witnesses exist by the consistency of the types with `SatTh3 m`.

  The proof splits the specification `SatSpecG (m+1)` into its three parts.  Sentences coming from
  the elementary diagram of `M`, from the complete theory `SatTh3 y` of a lower level `y < m` and
  from witness sentences created at a lower level `p < m` are, up to the language map `SatIncSucc`,
  sentences of `SatTh3 m`, hence are realized by the expansion (`SatExpansionModel`).  A sentence
  that is itself the image of the complete theory at level `m` is again realized by the expansion,
  and a witness sentence created at level `m` is realized because the required finite fragment of
  its type was made true at the value chosen for the corresponding new constant.
-/
import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatBuild
import Submission.Work.WilC5.SatCore
import Submission.Work.WilC5.SatExpand
import Submission.Work.WilC5.SatExpansionModel
import Submission.Work.WilC5.SatSentRealize
import Submission.Work.WilC5.SatCons2_exists_realize

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilC5

attribute [local implicit_reducible] FirstOrder.Language.withConstants Work.WilC5.SatTyp2

/-! ## The witness sentence of a term-parameter type in an expansion

Realising the witness sentence `SatWitSent2 inc cnew q φ` in the expansion `SatExpansion inc hinc N
instN w` is the same as realising `φ` in `N` at the assignment that sends every parameter term of
`q` to its value in `N` and the last variable to the value of the new constant `cnew q`. -/

private theorem SatWitSent2_realize {L : FirstOrder.Language.{0, 0}} {C C' : Type}
    (inc : C → C') (hinc : Function.Injective inc) (N : Type)
    (instN : L[[C]].Structure N) (w : C' → N) (cnew : SatTyp2 L C → C')
    (q : SatTyp2 L C) (φ : L[[C]].Formula (q.1 ⊕ Fin 1)) :
    @FirstOrder.Language.Sentence.Realize L[[C']] N
        (@SatExpansion L C C' inc hinc N instN w) (SatWitSent2 inc cnew q φ) ↔
      @FirstOrder.Language.Formula.Realize L[[C]] N instN (q.1 ⊕ Fin 1) φ
        (Sum.elim (fun t : q.1 =>
            @FirstOrder.Language.Term.realize L[[C]] N instN Empty (default : Empty → N) t.1)
          (fun _ : Fin 1 => @SatExpVal L C C' inc hinc N instN w (cnew q))) := by
  letI : L[[C']].Structure N := @SatExpansion L C C' inc hinc N instN w
  haveI : (SatLangMap (L := L) inc).IsExpansionOn N := SatExpansion_isExpansionOn inc hinc N instN w
  have hfun : (fun a : q.1 ⊕ Fin 1 =>
        @Term.realize L[[C']] N inferInstance Empty (default : Empty → N)
          (match a with
           | Sum.inl t => (SatLangMap (L := L) inc).onTerm t.1
           | Sum.inr _ => (Constants.term (Sum.inr (cnew q)) : L[[C']].Term Empty)))
      = Sum.elim (fun t : q.1 =>
            @Term.realize L[[C]] N instN Empty (default : Empty → N) t.1)
          (fun _ : Fin 1 => @SatExpVal L C C' inc hinc N instN w (cnew q)) := by
    funext a
    cases a with
    | inl t =>
      simp only [Sum.elim_inl]
      exact LHom.realize_onTerm (SatLangMap (L := L) inc) t.1 (default : Empty → N)
    | inr i =>
      simp only [Sum.elim_inr]
      exact @SatExpansion_const L C C' inc hinc N instN w Empty (cnew q) (default : Empty → N)
  rw [SatWitSent2, Sentence.Realize, Formula.Realize, BoundedFormula.realize_subst]
  rw [Formula.boundedFormula_realize_eq_realize]
  rw [LHom.realize_onFormula]
  exact iff_of_eq (congrArg (Formula.Realize φ) hfun)

/-! ## Functoriality of `SatLangMap` -/

private theorem constantsOnMap_comp {α β γ : Type} (f : β → γ) (g : α → β) :
    LHom.constantsOnMap (f ∘ g) = (LHom.constantsOnMap f).comp (LHom.constantsOnMap g) := by
  refine LHom.funext (funext fun n => funext fun c => ?_) (funext fun n => funext fun R => ?_)
  · cases n with
    | zero => rfl
    | succ n => exact isEmptyElim c
  · exact isEmptyElim R

private theorem sumMap_comp {L L' L'' L₁ L₁' L₁'' : Language} (φ : L →ᴸ L') (φ' : L' →ᴸ L'')
    (ψ : L₁ →ᴸ L₁') (ψ' : L₁' →ᴸ L₁'') :
    (φ'.comp φ).sumMap (ψ'.comp ψ) = (φ'.sumMap ψ').comp (φ.sumMap ψ) := by
  refine LHom.funext (funext fun n => funext fun x => ?_) (funext fun n => funext fun R => ?_)
  · rcases x with a | a <;> rfl
  · rcases R with a | a <;> rfl

private theorem SatLangMap_comp {L : Language} {C C' C'' : Type} (f : C' → C'') (g : C → C') :
    SatLangMap (L := L) (f ∘ g) = (SatLangMap (L := L) f).comp (SatLangMap (L := L) g) := by
  rw [SatLangMap, SatLangMap, SatLangMap, constantsOnMap_comp]
  exact sumMap_comp (LHom.id L) (LHom.id L) (LHom.constantsOnMap g) (LHom.constantsOnMap f)

private theorem SatLangMap_congr {L : Language} {C C' : Type} {f g : C → C'} (h : ∀ c, f c = g c) :
    SatLangMap (L := L) f = SatLangMap (L := L) g := by
  rw [SatLangMap, SatLangMap]
  refine LHom.funext (funext fun n => funext fun x => ?_) (funext fun n => funext fun R => ?_)
  · rcases x with a | a
    · rfl
    · cases n with
      | zero =>
        show Sum.inr (f a) = Sum.inr (g a)
        exact congrArg Sum.inr (h a)
      | succ n => exact isEmptyElim a
  · rcases R with a | a
    · rfl
    · exact isEmptyElim a

private theorem LHom_comp_onSentence {L L' L'' : Language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L')
    (σ : L.Sentence) : (φ.comp ψ).onSentence σ = φ.onSentence (ψ.onSentence σ) := by
  have h := congrFun (LHom.comp_onBoundedFormula (α := Empty) (n := 0) φ ψ) σ
  simpa only [LHom.onSentence, LHom.onFormula, Function.comp_apply] using h

private theorem SatLangMap_onSentence_comp {L : Language} {C C' C'' : Type} (f : C' → C'')
    (g : C → C') (σ : (SatLang L C).Sentence) :
    (SatLangMap (L := L) f).onSentence ((SatLangMap (L := L) g).onSentence σ) =
      (SatLangMap (L := L) (f ∘ g)).onSentence σ := by
  have h := LHom_comp_onSentence (SatLangMap (L := L) f) (SatLangMap (L := L) g) σ
  rw [← SatLangMap_comp f g] at h
  exact h.symm

private theorem SatLangMap_onSentence_congr {L : Language} {C C' : Type} {f g : C → C'}
    (h : ∀ c, f c = g c) (σ : (SatLang L C).Sentence) :
    (SatLangMap (L := L) f).onSentence σ = (SatLangMap (L := L) g).onSentence σ := by
  rw [SatLangMap_congr h]

private theorem SatLangMap_onSentence_id {L : Language} {C : Type} (σ : (SatLang L C).Sentence) :
    (SatLangMap (L := L) (id : C → C)).onSentence σ = σ := by
  have hid : SatLangMap (L := L) (id : C → C) = LHom.id (SatLang L C) := by
    rw [SatLangMap]
    refine LHom.funext (funext fun n => funext fun x => ?_) (funext fun n => funext fun R => ?_)
    · rcases x with a | a
      · rfl
      · cases n with
        | zero => rfl
        | succ n => exact isEmptyElim a
    · rcases R with a | a
      · rfl
      · exact isEmptyElim a
  rw [hid]
  exact congrFun (LHom.id_onBoundedFormula (L := SatLang L C) (α := Empty) (n := 0)) σ

private theorem SatLangMap_onSentence_self {L : Language} {C : Type} {f : C → C} (hf : ∀ c, f c = c)
    (σ : (SatLang L C).Sentence) : (SatLangMap (L := L) f).onSentence σ = σ := by
  rw [SatLangMap_onSentence_congr (g := id) hf, SatLangMap_onSentence_id]

/-! ## The inclusions `C m → C (m+1)` -/

section IncSucc

variable (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M] (κ : Cardinal.{0})

private theorem SatIncSucc_injective (m : SatIdx κ) : Function.Injective (SatIncSucc L M κ m) :=
  SatInc_injective L M κ (le_of_lt (Order.lt_succ m))

private theorem SatIncSucc_inl_comp (m : SatIdx κ) :
    (SatIncSucc L M κ m) ∘ (Sum.inl : M → SatC L M κ m) =
      (Sum.inl : M → SatC L M κ (Order.succ m)) := by
  funext x
  exact SatIncSucc_inl L M κ m x

private theorem SatIncSucc_comp_le (m : SatIdx κ) {y : SatIdx κ} (hy : y < m) :
    (SatIncSucc L M κ m) ∘ (SatInc L M κ (le_of_lt hy)) =
      SatInc L M κ (le_of_lt (lt_trans hy (Order.lt_succ m))) := by
  funext c
  show SatInc L M κ (le_of_lt (Order.lt_succ m)) (SatInc L M κ (le_of_lt hy) c) =
    SatInc L M κ (le_of_lt (lt_trans hy (Order.lt_succ m))) c
  rw [SatInc_proof_irrel L M κ (le_of_lt (lt_trans hy (Order.lt_succ m)))
        (le_trans (le_of_lt hy) (le_of_lt (Order.lt_succ m)))]
  exact congrFun (SatInc_comp L M κ (le_of_lt hy) (le_of_lt (Order.lt_succ m))) c

private theorem SatIncSucc_comp_succ_le (m : SatIdx κ) {p : SatIdx κ} (hp : p < m) :
    (SatIncSucc L M κ m) ∘ (SatInc L M κ (Order.succ_le_of_lt hp)) =
      SatInc L M κ (Order.succ_le_of_lt (lt_trans hp (Order.lt_succ m))) := by
  funext c
  show SatInc L M κ (le_of_lt (Order.lt_succ m)) (SatInc L M κ (Order.succ_le_of_lt hp) c) =
    SatInc L M κ (Order.succ_le_of_lt (lt_trans hp (Order.lt_succ m))) c
  rw [SatInc_proof_irrel L M κ (Order.succ_le_of_lt (lt_trans hp (Order.lt_succ m)))
        (le_trans (Order.succ_le_of_lt hp) (le_of_lt (Order.lt_succ m)))]
  exact congrFun (SatInc_comp L M κ (Order.succ_le_of_lt hp) (le_of_lt (Order.lt_succ m))) c

/-! ## The complete theory at a level -/

private theorem SatTh3_model (m : SatIdx κ) :
    @FirstOrder.Language.Theory.Model (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
      (SatStruc3 L M κ m) (SatTh3 L M κ m) :=
  (@FirstOrder.Language.Theory.model_iff (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
    (SatStruc3 L M κ m) (SatTh3 L M κ m)).mpr fun _ hσ => hσ

private theorem SatTh3_realize {m : SatIdx κ} {σ : (SatLang L (SatC L M κ m)).Sentence}
    (hσ : σ ∈ SatTh3 L M κ m) :
    @FirstOrder.Language.Sentence.Realize (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
      (SatStruc3 L M κ m) σ := hσ

private theorem SatSpecG_subset_SatTh3 {m : SatIdx κ}
    (hIH : ∀ σ : (SatLang L (SatC L M κ m)).Sentence, σ ∈ SatSpecG L M κ m →
      @FirstOrder.Language.Sentence.Realize (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
        (SatStruc3 L M κ m) σ) :
    SatSpecG L M κ m ⊆ SatTh3 L M κ m := fun σ hσ => hIH σ hσ

/-! ## The finite fragment of a type required by a finite set of sentences, and the witnesses -/

/-- The finite fragment of a type `q` over the constants of level `m` required by `T0`: for every
sentence of `T0` that is the witness sentence of a formula of `q`, one such formula; explicitly a
subset of `q.2`. -/
private noncomputable def SatFreq (m : SatIdx κ)
    (T0 : Finset ((SatLang L (SatC L M κ (Order.succ m))).Sentence))
    (q : SatTyp2 L (SatC L M κ m)) : Finset ((SatLang L (SatC L M κ m)).Formula (q.1 ⊕ Fin 1)) :=
  (T0.attach.image (fun σ =>
      if h : ∃ (φ : (SatLang L (SatC L M κ m)).Formula (q.1 ⊕ Fin 1)),
          φ ∈ q.2 ∧ SatWitSent2 (SatIncSucc L M κ m) (SatNewConst L M κ m) q φ = σ.1
      then h.choose else ⊥)).filter (fun φ => φ ∈ q.2)

private theorem SatFreq_sub (m : SatIdx κ)
    (T0 : Finset ((SatLang L (SatC L M κ (Order.succ m))).Sentence)) (q : SatTyp2 L (SatC L M κ m)) :
    ∀ φ ∈ SatFreq L M κ m T0 q, φ ∈ q.2 := by
  intro φ hφ
  exact (Finset.mem_filter.mp hφ).2

private theorem SatFreq_mem (m : SatIdx κ)
    (T0 : Finset ((SatLang L (SatC L M κ (Order.succ m))).Sentence)) (q : SatTyp2 L (SatC L M κ m))
    {σ : (SatLang L (SatC L M κ (Order.succ m))).Sentence} (hσ : σ ∈ T0)
    (h : ∃ (φ : (SatLang L (SatC L M κ m)).Formula (q.1 ⊕ Fin 1)),
        φ ∈ q.2 ∧ SatWitSent2 (SatIncSucc L M κ m) (SatNewConst L M κ m) q φ = σ) :
    Classical.choose h ∈ SatFreq L M κ m T0 q := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨⟨σ, hσ⟩, Finset.mem_attach _ _, ?_⟩,
    (Classical.choose_spec h).1⟩
  exact dif_pos h

/-- A common realization of the finite fragment `SatFreq m T0 q` of a type `q` (which is consistent
with `SatTh3 m`). -/
private noncomputable def SatWitFun {m : SatIdx κ} (hne : Nonempty (SatMod3 L M κ m))
    (T0 : Finset ((SatLang L (SatC L M κ (Order.succ m))).Sentence)) :
    SatTyp2 L (SatC L M κ m) → SatMod3 L M κ m := fun q =>
  if hq : SatCons2 (SatTh3 L M κ m) q then
    Classical.choose (SatCons2_exists_realize (SatMod3 L M κ m) (SatStruc3 L M κ m)
      (SatTh3_model L M κ m) q hq (SatFreq L M κ m T0 q) (SatFreq_sub L M κ m T0 q))
  else hne.some

private theorem SatWitFun_spec {m : SatIdx κ} (hne : Nonempty (SatMod3 L M κ m))
    (T0 : Finset ((SatLang L (SatC L M κ (Order.succ m))).Sentence)) (q : SatTyp2 L (SatC L M κ m))
    (hq : SatCons2 (SatTh3 L M κ m) q) {φ : (SatLang L (SatC L M κ m)).Formula (q.1 ⊕ Fin 1)}
    (hφ : φ ∈ SatFreq L M κ m T0 q) :
    @FirstOrder.Language.Formula.Realize (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
      (SatStruc3 L M κ m) (q.1 ⊕ Fin 1) φ
      (Sum.elim (fun t : q.1 =>
          @FirstOrder.Language.Term.realize (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
            (SatStruc3 L M κ m) Empty (default : Empty → SatMod3 L M κ m) t.1)
        (fun _ : Fin 1 => SatWitFun L M κ hne T0 q)) := by
  have hspec := Classical.choose_spec (SatCons2_exists_realize (SatMod3 L M κ m)
    (SatStruc3 L M κ m) (SatTh3_model L M κ m) q hq (SatFreq L M κ m T0 q)
    (SatFreq_sub L M κ m T0 q))
  have hwit : SatWitFun L M κ hne T0 q
      = Classical.choose (SatCons2_exists_realize (SatMod3 L M κ m) (SatStruc3 L M κ m)
          (SatTh3_model L M κ m) q hq (SatFreq L M κ m T0 q) (SatFreq_sub L M κ m T0 q)) := by
    dsimp only [SatWitFun]
    exact dif_pos hq
  rw [hwit]
  exact hspec φ hφ

/-- The interpretation of the constants of level `m+1` in the expansion of `SatMod3 m` along
`SatIncSucc`: the new constants `SatNewConst m q` are interpreted by the witnesses `SatWitFun`; the
old constants (which lie in the range of `SatIncSucc`) get arbitrary values, since their values in
the expansion are computed from `SatStruc3`. -/
private noncomputable def SatWitVal {m : SatIdx κ} (hne : Nonempty (SatMod3 L M κ m))
    (T0 : Finset ((SatLang L (SatC L M κ (Order.succ m))).Sentence)) :
    SatC L M κ (Order.succ m) → SatMod3 L M κ m := fun c =>
  if h : ∃ q : SatTyp2 L (SatC L M κ m), SatNewConst L M κ m q = c
  then SatWitFun L M κ hne T0 h.choose
  else hne.some

private theorem SatWitVal_newConst {m : SatIdx κ} (hne : Nonempty (SatMod3 L M κ m))
    (T0 : Finset ((SatLang L (SatC L M κ (Order.succ m))).Sentence))
    (q : SatTyp2 L (SatC L M κ m)) :
    SatWitVal L M κ hne T0 (SatNewConst L M κ m q) = SatWitFun L M κ hne T0 q := by
  dsimp only [SatWitVal]
  rw [dif_pos (⟨q, rfl⟩ : ∃ q' : SatTyp2 L (SatC L M κ m),
    SatNewConst L M κ m q' = SatNewConst L M κ m q)]
  exact congrArg (SatWitFun L M κ hne T0) (SatNewConst_injective L M κ m
    (Classical.choose_spec (⟨q, rfl⟩ : ∃ q' : SatTyp2 L (SatC L M κ m),
      SatNewConst L M κ m q' = SatNewConst L M κ m q)))

/-! ## The realization lemmas for the successor stage -/

/-- Push-forward of a sentence of the complete theory at level `m` to level `m+1` along `SatIncSucc`
is realized in the expansion of `SatMod3 m` along `SatIncSucc`. -/
private theorem SatTh3_push_realize (m : SatIdx κ) (w : SatC L M κ (Order.succ m) → SatMod3 L M κ m)
    {σ : (SatLang L (SatC L M κ (Order.succ m))).Sentence}
    (hσ : σ ∈ (SatLangMap (L := L) (SatIncSucc L M κ m)).onTheory (SatTh3 L M κ m)) :
    @FirstOrder.Language.Sentence.Realize (SatLang L (SatC L M κ (Order.succ m))) (SatMod3 L M κ m)
      (@SatExpansion L (SatC L M κ m) (SatC L M κ (Order.succ m)) (SatIncSucc L M κ m)
        (SatIncSucc_injective L M κ m) (SatMod3 L M κ m) (SatStruc3 L M κ m) w) σ :=
  SatExpansionModel (SatIncSucc L M κ m) (SatIncSucc_injective L M κ m) (SatMod3 L M κ m)
    (SatStruc3 L M κ m) w (SatTh3 L M κ m) (SatTh3_model L M κ m) σ hσ

/-- The witness realization lemma, specialized to the successor stage: the new constant is
`SatNewConst m q` and the expansion is along `SatIncSucc m`. -/
private theorem SatWitSent2_realize_succ (m : SatIdx κ) (w : SatC L M κ (Order.succ m) → SatMod3 L M κ m)
    (q : SatTyp2 L (SatC L M κ m)) (φ : (SatLang L (SatC L M κ m)).Formula (q.1 ⊕ Fin 1)) :
    @FirstOrder.Language.Sentence.Realize (SatLang L (SatC L M κ (Order.succ m))) (SatMod3 L M κ m)
        (@SatExpansion L (SatC L M κ m) (SatC L M κ (Order.succ m)) (SatIncSucc L M κ m)
          (SatIncSucc_injective L M κ m) (SatMod3 L M κ m) (SatStruc3 L M κ m) w)
        (SatWitSent2 (SatIncSucc L M κ m) (SatNewConst L M κ m) q φ) ↔
      @FirstOrder.Language.Formula.Realize (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
        (SatStruc3 L M κ m) (q.1 ⊕ Fin 1) φ
        (Sum.elim (fun t : q.1 =>
            @FirstOrder.Language.Term.realize (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
              (SatStruc3 L M κ m) Empty (default : Empty → SatMod3 L M κ m) t.1)
          (fun _ : Fin 1 =>
            @SatExpVal L (SatC L M κ m) (SatC L M κ (Order.succ m)) (SatIncSucc L M κ m)
              (SatIncSucc_injective L M κ m) (SatMod3 L M κ m) (SatStruc3 L M κ m) w
              (SatNewConst L M κ m q))) :=
  SatWitSent2_realize (SatIncSucc L M κ m) (SatIncSucc_injective L M κ m) (SatMod3 L M κ m)
    (SatStruc3 L M κ m) w (SatNewConst L M κ m) q φ

end IncSucc

/-! ## The successor step -/

section Main

variable (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M] (κ : Cardinal.{0})

/-- **The successor step of the transfinite construction.**  Given that `SatMod3 m` realizes every
sentence of `SatSpecG m`, every finite set of sentences of `SatSpecG (m+1)` is satisfiable: expand
`SatMod3 m` along `SatIncSucc m`, interpreting the constants created at level `m` by witnesses for
the finite fragments of the types required by the given finite set of sentences. -/
theorem SatSpecSucc {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} {m : SatIdx κ} (hne : Nonempty (SatMod3 L M κ m))
    (hIH : ∀ σ : (SatLang L (SatC L M κ m)).Sentence, σ ∈ SatSpecG L M κ m →
      @FirstOrder.Language.Sentence.Realize (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
        (SatStruc3 L M κ m) σ)
    (T0 : Finset ((SatLang L (SatC L M κ (Order.succ m))).Sentence))
    (hT0 : ∀ σ ∈ T0, σ ∈ SatSpecG L M κ (Order.succ m)) :
    @FirstOrder.Language.Theory.IsSatisfiable (SatLang L (SatC L M κ (Order.succ m))) (↑T0) := by
  classical
  letI hStruct : (SatLang L (SatC L M κ (Order.succ m))).Structure (SatMod3 L M κ m) :=
    @SatExpansion L (SatC L M κ m) (SatC L M κ (Order.succ m)) (SatIncSucc L M κ m)
      (SatIncSucc_injective L M κ m) (SatMod3 L M κ m) (SatStruc3 L M κ m)
      (SatWitVal L M κ hne T0)
  have hModel : @FirstOrder.Language.Theory.Model (SatLang L (SatC L M κ (Order.succ m)))
      (SatMod3 L M κ m) hStruct
      (↑T0 : (SatLang L (SatC L M κ (Order.succ m))).Theory) := by
    rw [@FirstOrder.Language.Theory.model_iff (SatLang L (SatC L M κ (Order.succ m)))
      (SatMod3 L M κ m) hStruct (↑T0 : (SatLang L (SatC L M κ (Order.succ m))).Theory)]
    intro σ hσ
    rw [Finset.mem_coe] at hσ
    have hspec := (mem_SatSpecG L M κ (x := Order.succ m) (σ := σ)).mp (hT0 σ hσ)
    rcases hspec with ⟨τ, hτ, hσeq⟩ | ⟨y, hy, τ, hτ, hσeq⟩ | ⟨p, hp, q, hq, φ, hφ, hσeq⟩
    · -- the image of the elementary diagram of `M`
      have hτ'mem : (SatLangMap (L := L) (Sum.inl : M → SatC L M κ m)).onSentence τ
          ∈ SatSpecG L M κ m :=
        (mem_SatSpecG L M κ).mpr (Or.inl ⟨τ, hτ, rfl⟩)
      have hτ'th : (SatLangMap (L := L) (Sum.inl : M → SatC L M κ m)).onSentence τ
          ∈ SatTh3 L M κ m := SatSpecG_subset_SatTh3 L M κ hIH hτ'mem
      have heq : (SatLangMap (L := L) (SatIncSucc L M κ m)).onSentence
          ((SatLangMap (L := L) (Sum.inl : M → SatC L M κ m)).onSentence τ) = σ := by
        rw [← hσeq]
        exact (SatLangMap_onSentence_comp (L := L) (f := SatIncSucc L M κ m)
          (g := (Sum.inl : M → SatC L M κ m)) τ).trans
          (SatLangMap_onSentence_congr (fun c => congrFun (SatIncSucc_inl_comp L M κ m) c) τ)
      rw [← heq]
      exact SatTh3_push_realize L M κ m (SatWitVal L M κ hne T0) ⟨_, hτ'th, rfl⟩
    · rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hy) with hylt | hyeq
      · -- the image of the complete theory of a lower level
        have hτ'mem : (SatLangMap (L := L) (SatInc L M κ (le_of_lt hylt))).onSentence τ
            ∈ SatSpecG L M κ m :=
          (mem_SatSpecG L M κ).mpr (Or.inr (Or.inl ⟨y, hylt, τ, hτ, rfl⟩))
        have hτ'th : (SatLangMap (L := L) (SatInc L M κ (le_of_lt hylt))).onSentence τ
            ∈ SatTh3 L M κ m := SatSpecG_subset_SatTh3 L M κ hIH hτ'mem
        have heq : (SatLangMap (L := L) (SatIncSucc L M κ m)).onSentence
            ((SatLangMap (L := L) (SatInc L M κ (le_of_lt hylt))).onSentence τ) = σ := by
          rw [← hσeq]
          exact (SatLangMap_onSentence_comp (L := L) (f := SatIncSucc L M κ m)
            (g := SatInc L M κ (le_of_lt hylt)) τ).trans
            (SatLangMap_onSentence_congr
              (fun c => congrFun (SatIncSucc_comp_le L M κ m hylt) c) τ)
        rw [← heq]
        exact SatTh3_push_realize L M κ m (SatWitVal L M κ hne T0) ⟨_, hτ'th, rfl⟩
      · -- `y = m`: the sentence is the image of the complete theory at level `m` itself
        subst y
        have heq : (SatLangMap (L := L) (SatIncSucc L M κ m)).onSentence τ = σ := by
          rw [← hσeq]
          exact SatLangMap_onSentence_congr (fun c => congrFun
            (SatInc_proof_irrel L M κ (le_of_lt (Order.lt_succ m)) (le_of_lt hy)) c) τ
        rw [← heq]
        exact SatTh3_push_realize L M κ m (SatWitVal L M κ hne T0) ⟨τ, hτ, rfl⟩
    · rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hp) with hplt | hpeq
      · -- a witness sentence created at a lower level
        have hτ'mem : (SatLangMap (L := L) (SatInc L M κ (Order.succ_le_of_lt hplt))).onSentence
            (SatWitSent2 (SatIncSucc L M κ p) (SatNewConst L M κ p) q φ) ∈ SatSpecG L M κ m :=
          (mem_SatSpecG L M κ).mpr (Or.inr (Or.inr ⟨p, hplt, q, hq, φ, hφ, rfl⟩))
        have hτ'th : (SatLangMap (L := L) (SatInc L M κ (Order.succ_le_of_lt hplt))).onSentence
            (SatWitSent2 (SatIncSucc L M κ p) (SatNewConst L M κ p) q φ) ∈ SatTh3 L M κ m :=
          SatSpecG_subset_SatTh3 L M κ hIH hτ'mem
        have heq : (SatLangMap (L := L) (SatIncSucc L M κ m)).onSentence
            ((SatLangMap (L := L) (SatInc L M κ (Order.succ_le_of_lt hplt))).onSentence
              (SatWitSent2 (SatIncSucc L M κ p) (SatNewConst L M κ p) q φ)) = σ := by
          rw [← hσeq]
          exact (SatLangMap_onSentence_comp (L := L) (f := SatIncSucc L M κ m)
            (g := SatInc L M κ (Order.succ_le_of_lt hplt))
            (SatWitSent2 (SatIncSucc L M κ p) (SatNewConst L M κ p) q φ)).trans
            (SatLangMap_onSentence_congr
              (fun c => congrFun (SatIncSucc_comp_succ_le L M κ m hplt) c) _)
        rw [← heq]
        exact SatTh3_push_realize L M κ m (SatWitVal L M κ hne T0) ⟨_, hτ'th, rfl⟩
      · -- `p = m`: the new constant of the type `q` has to realize the required fragment of `q`
        subst p
        have hident : (SatLangMap (L := L) (SatInc L M κ (Order.succ_le_of_lt hp))).onSentence
            (SatWitSent2 (SatIncSucc L M κ m) (SatNewConst L M κ m) q φ)
            = SatWitSent2 (SatIncSucc L M κ m) (SatNewConst L M κ m) q φ := by
          refine SatLangMap_onSentence_self (fun c => ?_) _
          show SatInc L M κ (Order.succ_le_of_lt hp) c = c
          rw [SatInc_proof_irrel L M κ (Order.succ_le_of_lt hp) (le_refl (Order.succ m))]
          exact congrFun (SatInc_id L M κ (x := Order.succ m)) c
        have hSσ : SatWitSent2 (SatIncSucc L M κ m) (SatNewConst L M κ m) q φ = σ :=
          hident.symm.trans hσeq
        have hex : ∃ (φ' : (SatLang L (SatC L M κ m)).Formula (q.1 ⊕ Fin 1)),
            φ' ∈ q.2 ∧ SatWitSent2 (SatIncSucc L M κ m) (SatNewConst L M κ m) q φ' = σ :=
          ⟨φ, hφ, hSσ⟩
        have hψF : Classical.choose hex ∈ SatFreq L M κ m T0 q := SatFreq_mem L M κ m T0 q hσ hex
        have hψr : @FirstOrder.Language.Formula.Realize (SatLang L (SatC L M κ m))
            (SatMod3 L M κ m) (SatStruc3 L M κ m) (q.1 ⊕ Fin 1) (Classical.choose hex)
            (Sum.elim (fun t : q.1 =>
                @FirstOrder.Language.Term.realize (SatLang L (SatC L M κ m)) (SatMod3 L M κ m)
                  (SatStruc3 L M κ m) Empty (default : Empty → SatMod3 L M κ m) t.1)
              (fun _ : Fin 1 => SatWitFun L M κ hne T0 q)) :=
          SatWitFun_spec L M κ hne T0 q hq hψF
        have hval : @SatExpVal L (SatC L M κ m) (SatC L M κ (Order.succ m)) (SatIncSucc L M κ m)
            (SatIncSucc_injective L M κ m) (SatMod3 L M κ m) (SatStruc3 L M κ m)
            (SatWitVal L M κ hne T0) (SatNewConst L M κ m q) = SatWitFun L M κ hne T0 q := by
          rw [@SatExpVal_notMem L (SatC L M κ m) (SatC L M κ (Order.succ m)) (SatIncSucc L M κ m)
            (SatIncSucc_injective L M κ m) (SatMod3 L M κ m) (SatStruc3 L M κ m)
            (SatWitVal L M κ hne T0) (SatNewConst L M κ m q)
            (SatNewConst_not_mem_range L M κ m q)]
          exact SatWitVal_newConst L M κ hne T0 q
        rw [← hSσ]
        rw [show SatWitSent2 (SatIncSucc L M κ m) (SatNewConst L M κ m) q φ
            = SatWitSent2 (SatIncSucc L M κ m) (SatNewConst L M κ m) q (Classical.choose hex) from
          hSσ.trans (Classical.choose_spec hex).2.symm]
        refine (SatWitSent2_realize_succ L M κ m (SatWitVal L M κ hne T0) q
          (Classical.choose hex)).mpr ?_
        rw [hval]
        exact hψr
  exact @FirstOrder.Language.Theory.Model.isSatisfiable (SatLang L (SatC L M κ (Order.succ m)))
    (↑T0) (SatMod3 L M κ m) hne hStruct hModel

end Main

end Work.WilC5
