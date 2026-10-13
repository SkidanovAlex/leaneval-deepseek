/-
  WilC5 — the strong saturation property of the term hull.

  Let `N` be a model of the total theory `SatTot`.  The term hull `E = SatHull N` realizes, inside
  `N`, every type over a parameter set `A ⊆ E` that is finite or of cardinality `< κ` and is
  finitely satisfiable in `N`.  This is the key step of the final argument:

  * applied to finite `A` it gives `E ≼ N` (Tarski–Vaught, `IsElementary_of_finSat`);
  * applied to `A` with `|A| < κ` it gives the `κ`-saturation of `E`.
-/
import Mathlib
import Submission.Work.WilC5.SatHull
import Submission.Work.WilC5.SatTrans
import Submission.Work.WilC5.SatRelabRealize
import Submission.Work.WilC5.SatWitRealize
import Submission.Work.WilC5.SatHullLevTerm
import Submission.Work.WilC5.SatHullEqIUnion
import Submission.Work.WilC5.SatHullLevMono
import Submission.Work.WilC5.SatSentRealize
import Submission.Work.WilC5.SatTotSat
import Submission.Work.WilC5.SatIdxBdd2
import Submission.Work.WilC5.SatTh3Mono
import Submission.Work.WilC5.SatLangMapComp

open FirstOrder Language
open scoped FirstOrder

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

variable (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M] (κ : Cardinal.{0})

/-- Membership in the complete theory at level `x` is realization in `SatMod3 x`. -/
theorem mem_SatTh3_iff (x : SatIdx κ) (σ : (SatLang L (SatC L M κ x)).Sentence) :
    σ ∈ SatTh3 L M κ x ↔
      @Sentence.Realize (SatLang L (SatC L M κ x)) (SatMod3 L M κ x) (SatStruc3 L M κ x) σ :=
  Iff.rfl

/-- Realization of a formula depends only on the formula. -/
theorem satFormula_realize_congr {L : FirstOrder.Language.{0, 0}} {N : Type}
    [inst : L.Structure N] {α : Type} {φ ψ : L.Formula α} (h : φ = ψ) (v : α → N) :
    @Formula.Realize L N inst α φ v ↔ @Formula.Realize L N inst α ψ v := by
  rw [h]

/-- The complete theory at level `x` contains each sentence or its negation. -/
theorem SatTh3_mem_or_not (x : SatIdx κ) (σ : (SatLang L (SatC L M κ x)).Sentence) :
    σ ∈ SatTh3 L M κ x ∨ σ.not ∈ SatTh3 L M κ x :=
  @FirstOrder.Language.completeTheory.mem_or_not_mem (SatLang L (SatC L M κ x))
    (SatMod3 L M κ x) (SatStruc3 L M κ x) σ

theorem SatHullStrong (hM : Nonempty M) (N : Type)
    [instN : (SatLang L (SatCTotal L M κ)).Structure N] (hN : N ⊨ SatTot L M κ)
    (A : Set (SatHull L M κ N)) (hA : A.Finite ∨ Cardinal.mk A < κ)
    (p : Set (L.Formula (A ⊕ Fin 1)))
    (hp : ∀ F : Finset (L.Formula (A ⊕ Fin 1)), (∀ φ ∈ F, φ ∈ p) →
        ∃ a : N, ∀ φ ∈ F, @Formula.Realize L N (SatReduct L M κ N) (A ⊕ Fin 1) φ
          (Sum.elim (fun x : A => (x : N)) (fun _ : Fin 1 => a))) :
    ∃ a : SatHull L M κ N, ∀ φ ∈ p,
      @Formula.Realize L N (SatReduct L M κ N) (A ⊕ Fin 1) φ
        (Sum.elim (fun x : A => (x : N)) (fun _ : Fin 1 => (a : N))) := by
  -- Step 1: bound the levels of the elements of `A`.
  have hlv : ∀ a : A, ∃ z : SatIdx κ, (a : N) ∈ (SatHullLev L M κ N z : Set N) :=
    fun a => (SatHullEqIUnion N (a : N)).mp a.1.2
  choose lvl hlvl using hlv
  have hZfin : (Set.range lvl).Finite ∨ Cardinal.mk (Set.range lvl) < κ := by
    rcases hA with hfin | hlt
    · haveI : Finite A := hfin
      exact Or.inl (Set.finite_range lvl)
    · exact Or.inr (lt_of_le_of_lt (Cardinal.mk_range_le (f := lvl)) hlt)
  obtain ⟨z, hzb⟩ := SatIdxBdd2 κ (Set.range lvl) hZfin
  have hAz : ∀ a : A, (a : N) ∈ (SatHullLev L M κ N z : Set N) :=
    fun a => SatHullLevMono N (hzb (lvl a) ⟨a, rfl⟩) (hlvl a)
  -- Step 2: choose, for each element of `A`, a closed term of level `z` naming it.
  have ht : ∀ a : A, ∃ t : (SatLang L (SatC L M κ z)).Term Empty,
      @Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty (default : Empty → N)
        ((SatLangMap (SatIncTotal L M κ z)).onTerm t) = (a : N) :=
    fun a => (SatHullLevTerm N z (a : N)).mp (hAz a)
  choose f hf using ht
  -- Step 3: the translated type over the constants of level `z`.
  let q : SatTyp2 L (SatC L M κ z) :=
    ⟨Set.range f, {ψ | ∃ φ : L.Formula (A ⊕ Fin 1), φ ∈ p ∧ SatRelab L M κ z f φ = ψ}⟩
  have hqmem : ∀ ψ : (SatLang L (SatC L M κ z)).Formula (q.1 ⊕ Fin 1),
      ψ ∈ q.2 ↔ ∃ φ : L.Formula (A ⊕ Fin 1), φ ∈ p ∧ SatRelab L M κ z f φ = ψ :=
    fun _ => Iff.rfl
  -- Step 4: `q` is consistent with the complete theory at level `z`.
  have hcons : SatCons2 (SatTh3 L M κ z) q := by
    intro F hF
    dsimp only [q] at hF ⊢
    have hmem : ∀ ψ : {ψ // ψ ∈ F}, ∃ φ : L.Formula (A ⊕ Fin 1),
        φ ∈ p ∧ SatRelab L M κ z f φ
          = (ψ.1 : (SatLang L (SatC L M κ z)).Formula (Set.range f ⊕ Fin 1)) :=
      fun ψ => hF ψ.1 ψ.2
    choose g hg hgeq using hmem
    have hFp : ∀ φ ∈ F.attach.image g, φ ∈ p := by
      intro φ hφ
      obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.mp hφ
      exact hg ψ
    obtain ⟨a0, ha0⟩ := hp (F.attach.image g) hFp
    have hv : (Sum.elim (fun a : A =>
          @Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty (default : Empty → N)
            ((SatLangMap (SatIncTotal L M κ z)).onTerm (f a))) (fun _ : Fin 1 => a0))
        = (Sum.elim (fun a : A => (a : N)) (fun _ : Fin 1 => a0)) := by
      funext i
      rcases i with a | k
      · exact hf a
      · rfl
    have hval : ∀ t : Set.range f,
        @Term.realize (SatLang L (SatC L M κ z)) N ((SatLangMap (SatIncTotal L M κ z)).reduct N)
          Empty (default : Empty → N) t.1
          = @Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty (default : Empty → N)
              ((SatLangMap (SatIncTotal L M κ z)).onTerm t.1) := by
      intro t
      exact (@FirstOrder.Language.LHom.realize_onTerm (SatLang L (SatC L M κ z))
        (SatLang L (SatCTotal L M κ)) N ((SatLangMap (SatIncTotal L M κ z)).reduct N) Empty instN
        (SatLangMap (SatIncTotal L M κ z))
        (FirstOrder.Language.LHom.isExpansionOn_reduct _ _) t.1 (default : Empty → N)).symm
    have hsent : @Formula.Realize (SatLang L (SatC L M κ z)) N
        ((SatLangMap (SatIncTotal L M κ z)).reduct N) Empty
        (SatTyp2.sent ⟨Set.range f, {ψ | ∃ φ : L.Formula (A ⊕ Fin 1),
          φ ∈ p ∧ SatRelab L M κ z f φ = ψ}⟩ F)
        (default : Empty → N) := by
      rw [SatSentRealize N ((SatLangMap (SatIncTotal L M κ z)).reduct N) _ F]
      refine ⟨a0, fun ψ hψ => ?_⟩
      rw [show (Sum.elim (fun t : Set.range f =>
            @Term.realize (SatLang L (SatC L M κ z)) N ((SatLangMap (SatIncTotal L M κ z)).reduct N)
              Empty (default : Empty → N) t.1) (fun _ : Fin 1 => a0))
          = (Sum.elim (fun t : Set.range f =>
              @Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty (default : Empty → N)
                ((SatLangMap (SatIncTotal L M κ z)).onTerm t.1)) (fun _ : Fin 1 => a0)) from by
            funext i
            rcases i with t | k
            · exact hval t
            · rfl]
      have h1 : @Formula.Realize (SatLang L (SatC L M κ z)) N
          ((SatLangMap (SatIncTotal L M κ z)).reduct N) (Set.range f ⊕ Fin 1)
          (SatRelab L M κ z f (g ⟨ψ, hψ⟩))
          (Sum.elim (fun a : Set.range f =>
              @Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty (default : Empty → N)
                ((SatLangMap (SatIncTotal L M κ z)).onTerm a.1)) (fun _ : Fin 1 => a0)) := by
        rw [SatRelabRealize f (g ⟨ψ, hψ⟩) a0]
        rw [hv]
        exact ha0 (g ⟨ψ, hψ⟩)
          (Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach F ⟨ψ, hψ⟩, rfl⟩)
      exact (satFormula_realize_congr (inst := (SatLangMap (SatIncTotal L M κ z)).reduct N)
        (hgeq ⟨ψ, hψ⟩) _).mp h1
    rcases SatTh3_mem_or_not L M κ z
      (SatTyp2.sent ⟨Set.range f, {ψ | ∃ φ : L.Formula (A ⊕ Fin 1),
        φ ∈ p ∧ SatRelab L M κ z f φ = ψ}⟩ F) with h | h
    · exact h
    · exfalso
      have h1 : (SatLangMap (SatIncTotal L M κ z)).onSentence
          (SatTyp2.sent ⟨Set.range f, {ψ | ∃ φ : L.Formula (A ⊕ Fin 1),
            φ ∈ p ∧ SatRelab L M κ z f φ = ψ}⟩ F).not ∈ SatTot L M κ :=
        Set.mem_iUnion.mpr ⟨z, FirstOrder.Language.LHom.mem_onTheory.mpr ⟨_, h, rfl⟩⟩
      have h2 := hN.realize_of_mem _ h1
      have h3 : @Sentence.Realize (SatLang L (SatC L M κ z)) N
          ((SatLangMap (SatIncTotal L M κ z)).reduct N)
          (SatTyp2.sent ⟨Set.range f, {ψ | ∃ φ : L.Formula (A ⊕ Fin 1),
            φ ∈ p ∧ SatRelab L M κ z f φ = ψ}⟩ F).not :=
        (@FirstOrder.Language.LHom.realize_onSentence (SatLang L (SatC L M κ z))
          (SatLang L (SatCTotal L M κ)) N
          ((SatLangMap (SatIncTotal L M κ z)).reduct N) instN
          (SatLangMap (SatIncTotal L M κ z)) _ _).mp h2
      rw [Sentence.realize_not] at h3
      exact h3 hsent
  -- Step 5: the witness constant at level `z` realizes `q` in `N`.
  have hwit : ∀ φ ∈ q.2, @Formula.Realize (SatLang L (SatC L M κ z)) N
      ((SatLangMap (SatIncTotal L M κ z)).reduct N) (q.1 ⊕ Fin 1) φ
      (Sum.elim (fun a : q.1 =>
          @Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty (default : Empty → N)
            ((SatLangMap (SatIncTotal L M κ z)).onTerm a.1))
        (fun _ : Fin 1 =>
          @SatConVal L (SatCTotal L M κ) N instN
            (SatIncTotal L M κ (Order.succ z) (SatNewConst L M κ z q)))) := by
    intro φ hφ
    have hspec : (SatLangMap (SatInc L M κ (Order.succ_le_of_lt (Order.lt_succ z)))).onSentence
        (SatWitSent2 (SatIncSucc L M κ z) (SatNewConst L M κ z) q φ)
          ∈ SatSpecG L M κ (Order.succ z) :=
      (mem_SatSpecG L M κ (x := Order.succ z)
        (σ := (SatLangMap (SatInc L M κ (Order.succ_le_of_lt (Order.lt_succ z)))).onSentence
          (SatWitSent2 (SatIncSucc L M κ z) (SatNewConst L M κ z) q φ))).mpr
        (Or.inr (Or.inr ⟨z, Order.lt_succ z, q, hcons, φ, hφ, rfl⟩))
    have hth : (SatLangMap (SatInc L M κ (Order.succ_le_of_lt (Order.lt_succ z)))).onSentence
        (SatWitSent2 (SatIncSucc L M κ z) (SatNewConst L M κ z) q φ)
          ∈ SatTh3 L M κ (Order.succ z) :=
      (mem_SatTh3_iff L M κ (Order.succ z) _).mpr
        ((SatMain L M κ hM (Order.succ z)).2 _ hspec)
    have himg : (SatLangMap (SatIncTotal L M κ (Order.succ z))).onSentence
          ((SatLangMap (SatInc L M κ (Order.succ_le_of_lt (Order.lt_succ z)))).onSentence
            (SatWitSent2 (SatIncSucc L M κ z) (SatNewConst L M κ z) q φ))
        = (SatLangMap (SatIncTotal L M κ (Order.succ z))).onSentence
            (SatWitSent2 (SatIncSucc L M κ z) (SatNewConst L M κ z) q φ) := by
      rw [SatLangMapComp, congrArg SatLangMap (SatIncTotal_comp L M κ (le_refl (Order.succ z)))]
    have htot : (SatLangMap (SatIncTotal L M κ (Order.succ z))).onSentence
        (SatWitSent2 (SatIncSucc L M κ z) (SatNewConst L M κ z) q φ) ∈ SatTot L M κ := by
      rw [← himg]
      exact Set.mem_iUnion.mpr ⟨Order.succ z,
        FirstOrder.Language.LHom.mem_onTheory.mpr ⟨_, hth, rfl⟩⟩
    have h3 : @Sentence.Realize (SatLang L (SatC L M κ (Order.succ z))) N
        ((SatLangMap (SatIncTotal L M κ (Order.succ z))).reduct N)
        (SatWitSent2 (SatIncSucc L M κ z) (SatNewConst L M κ z) q φ) :=
      (@FirstOrder.Language.LHom.realize_onSentence (SatLang L (SatC L M κ (Order.succ z)))
        (SatLang L (SatCTotal L M κ)) N
        ((SatLangMap (SatIncTotal L M κ (Order.succ z))).reduct N) instN
        (SatLangMap (SatIncTotal L M κ (Order.succ z))) _ _).mp (hN.realize_of_mem _ htot)
    exact (SatWitRealize q φ).mp h3
  -- Step 6: the value of the witness constant lies in the hull and realizes the type.
  refine ⟨@Subtype.mk N (fun x => x ∈ (SatHull L M κ N : Set N))
      (@SatConVal L (SatCTotal L M κ) N instN
        (SatIncTotal L M κ (Order.succ z) (SatNewConst L M κ z q))) ?_, ?_⟩
  · exact @FirstOrder.Language.Substructure.subset_closure L N (SatReduct L M κ N)
      (Set.range (fun c : SatCt L M κ => @SatConVal L (SatCt L M κ) N instN c)) _
      ⟨_, rfl⟩
  · intro φ hφ
    have hψ : SatRelab L M κ z f φ ∈ q.2 := ⟨φ, hφ, rfl⟩
    have hres := hwit _ hψ
    rw [SatRelabRealize f φ (@SatConVal L (SatCTotal L M κ) N instN
      (SatIncTotal L M κ (Order.succ z) (SatNewConst L M κ z q)))] at hres
    have hv : (Sum.elim (fun a : A =>
          @Term.realize (SatLang L (SatCTotal L M κ)) N instN Empty (default : Empty → N)
            ((SatLangMap (SatIncTotal L M κ z)).onTerm (f a)))
          (fun _ : Fin 1 => @SatConVal L (SatCTotal L M κ) N instN
            (SatIncTotal L M κ (Order.succ z) (SatNewConst L M κ z q))))
        = (Sum.elim (fun a : A => (a : N)) (fun _ : Fin 1 =>
            @SatConVal L (SatCTotal L M κ) N instN
              (SatIncTotal L M κ (Order.succ z) (SatNewConst L M κ z q)))) := by
      funext i
      rcases i with a | k
      · exact hf a
      · rfl
    rw [hv] at hres
    exact hres

end Work.WilC5
