/-
  WilC5 — over models of `TE`, every `LElog`-formula is equivalent to an `LEc`-formula.

  `LElog = LEc ⊕ {log, ≤}` is the expansion of `LEc` by a symbol for the definable logarithm
  (`ExpLog.lean`) and a symbol for the definable order.  Both extra symbols are *definable in
  `LEc`*: the order is the ring formula `∃z, z*z = y - x`, and the graph of the logarithm is

      `logDefSet x y  :=  (0 < x ∧ exp y = x) ∨ (¬ 0 < x ∧ exp y = 1)`,

  which is the graph of a total function in every model of `TE` (`LogDefSetModel.lean`,
  `LogFunMap.lean`).

  This module makes that definability *syntactic*: for every `LElog`-term `t` (with free
  variables `β`) the `LEc`-formula `logTermGraph t` (with one extra free variable) says "the value
  of `t` is the extra variable", the only non-trivial case being the function symbol `log`, where
  the graph `logDefSet` of `logFun` is used.  The recursion `logTrans` on `LElog`-formulas is then
  completed by `⊥`, the equality of two terms, the binary relation `≤` (which needs two auxiliary
  values), `⟹` and `∀`.

  The main theorem `LogTranslation` states that `logTrans φ` has exactly the same realizations as
  `φ` in every model of `TE`.  Its proof is structural; the only model-theoretic input is
  `logDefSet_iff_logFun`, i.e. that in a model of `TE` the definable logarithm `logFun` is
  described by its graph — this is where the totalness of `logDefSet` (`LogDefSetModel`) enters.
-/
import Mathlib
import Submission.Work.WilC5.ExpLog
import Submission.Work.WilC5.Translate
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC5.LogFunMap

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

variable {M : Type} [LEc.Structure M]

def logGraphForm {β : Type} {l : ℕ} (s t : LEc.Term (β ⊕ Fin l)) : LEc.BoundedFormula β l :=
  ((leForm eZero s ⊓ (leForm s eZero).not) ⊓ Term.bdEqual (eExp t) s) ⊔
    (((leForm eZero s ⊓ (leForm s eZero).not).not) ⊓ Term.bdEqual (eExp t) eOne)

def logRealize {β : Type} (v : β → M) (t : LElog.Term β) : M :=
  @Term.realize LElog M (logStruct M) β v t

@[simp] theorem logRealize_var {β : Type} (v : β → M) (a : β) :
    logRealize v (Term.var a : LElog.Term β) = v a := rfl

@[simp] theorem logRealize_func {β : Type} {l : ℕ} (v : β → M) (f : LElog.Functions l)
    (ts : Fin l → LElog.Term β) :
    logRealize v (Term.func f ts) =
      @Structure.funMap LElog M (logStruct M) l f (fun i => logRealize v (ts i)) := rfl

theorem logGraphForm_realize {β : Type} {l : ℕ} (s t : LEc.Term (β ⊕ Fin l)) (v : β → M)
    (xs : Fin l → M) :
    (logGraphForm s t).Realize v xs ↔
      logDefSet (Term.realize (Sum.elim v xs) s) (Term.realize (Sum.elim v xs) t) := by
  simp only [logGraphForm, logDefSet, leE, BoundedFormula.realize_sup, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, leForm_realize, realize_eZero,
    realize_eExp, realize_eOne]

def outerRelLog {β : Type} {l : ℕ} (f : LElog.Functions l) : LEc.BoundedFormula (β ⊕ Fin 1) l :=
  match f with
  | Sum.inl g => Term.bdEqual (valVar (β := β) l) (Term.func g (fun i => argVar (β := β) i))
  | Sum.inr r => match r with
    | logFunc.log => logGraphForm (argVar (β := β) 0) (valVar (β := β) 1)

theorem outerRelLog_realize {β : Type} {l : ℕ} (f : LElog.Functions l)
    (hLog : ∀ x y : M, logDefSet x y ↔ logFun x = y)
    (w : (β ⊕ Fin 1) → M) (xs : Fin l → M) :
    (outerRelLog (β := β) f).Realize w xs ↔
      @Structure.funMap LElog M (logStruct M) l f xs = w (Sum.inr 0) := by
  rcases f with (g | r)
  · show (Term.bdEqual (valVar (β := β) l) (Term.func g (fun i => argVar (β := β) i))).Realize w xs ↔ _
    rw [BoundedFormula.realize_bdEqual, realize_valVar, realize_funcE]
    have h1 : (fun i => Term.realize (Sum.elim w xs) (argVar (β := β) i)) = xs := by
      funext i
      exact realize_argVar w xs i
    rw [h1, logStruct_funMap_inl, eq_comm]
  · cases r
    show (logGraphForm (argVar (β := β) 0) (valVar (β := β) 1)).Realize w xs ↔ _
    rw [logGraphForm_realize, realize_argVar, realize_valVar, logStruct_funMap_log]
    exact hLog (xs 0) (w (Sum.inr 0))

def logTermGraph {β : Type} : LElog.Term β → LEc.Formula (β ⊕ Fin 1)
  | .var a => Term.equal (Term.var (Sum.inl a)) (Term.var (Sum.inr 0))
  | .func f ts =>
      (finAnd _ (fun i => BoundedFormula.relabel (freshMap i) (logTermGraph (ts i))) ⊓
        outerRelLog f).exs

theorem logTermGraph_realize {β : Type} (hLog : ∀ x y : M, logDefSet x y ↔ logFun x = y)
    (t : LElog.Term β) (w : (β ⊕ Fin 1) → M) :
    (logTermGraph t).Realize w ↔ logRealize (w ∘ Sum.inl) t = w (Sum.inr 0) := by
  revert w
  induction t with
  | var a =>
      intro w
      rw [logTermGraph, Term.equal, Formula.Realize, BoundedFormula.realize_bdEqual,
        Term.realize_relabel, Term.realize_relabel, Term.realize_var, Term.realize_var,
        logRealize_var]
      simp only [Function.comp_apply, Sum.elim_inl]
  | func f ts ih =>
      intro w
      rw [logTermGraph, BoundedFormula.realize_exs]
      constructor
      · rintro ⟨xs, hxs⟩
        rw [BoundedFormula.realize_inf, finAnd_realize] at hxs
        obtain ⟨hsub, hout⟩ := hxs
        have hval : ∀ i, logRealize (w ∘ Sum.inl) (ts i) = xs i := by
          intro i
          have hi := hsub i
          rw [BoundedFormula.realize_relabel, freshMap_elim i w xs] at hi
          exact (ih i (Sum.elim (w ∘ Sum.inl) (fun _ => xs i))).mp
            (formulaRealize_of_bounded (logTermGraph (ts i)) _ _ hi)
        have hout' := (outerRelLog_realize f hLog w xs).mp hout
        rw [logRealize_func]
        rw [show (fun i => logRealize (w ∘ Sum.inl) (ts i)) = xs from funext hval]
        exact hout'
      · intro h
        refine ⟨fun i => logRealize (w ∘ Sum.inl) (ts i), ?_⟩
        rw [BoundedFormula.realize_inf, finAnd_realize]
        refine ⟨fun i => ?_, (outerRelLog_realize f hLog w _).mpr ?_⟩
        · have hgoal : (logTermGraph (ts i)).Realize (Sum.elim (w ∘ Sum.inl)
              (fun _ => logRealize (w ∘ Sum.inl) (ts i))) :=
            (ih i (Sum.elim (w ∘ Sum.inl) (fun _ => logRealize (w ∘ Sum.inl) (ts i)))).mpr rfl
          rw [BoundedFormula.realize_relabel, freshMap_elim i w _]
          exact bounded_of_formulaRealize (logTermGraph (ts i)) _ _ hgoal
        · rw [logRealize_func] at h
          exact h

theorem logTermGraph_realize' {β : Type} (hLog : ∀ x y : M, logDefSet x y ↔ logFun x = y)
    (t : LElog.Term β) (w : (β ⊕ Fin 1) → M) (ys : Fin 0 → M) :
    BoundedFormula.Realize (logTermGraph t) w ys ↔
      logRealize (w ∘ Sum.inl) t = w (Sum.inr 0) :=
  ⟨fun h => (logTermGraph_realize hLog t w).mp (formulaRealize_of_bounded _ _ _ h),
   fun h => bounded_of_formulaRealize _ _ _ ((logTermGraph_realize hLog t w).mpr h)⟩

def logValPush {α : Type} {m : ℕ} : ((α ⊕ Fin m) ⊕ Fin 1) → ((α ⊕ Fin m) ⊕ Fin 1) ⊕ Fin 1 :=
  Sum.map Sum.inl id

omit [LEc.Structure M] in
theorem logValPush_elim {α : Type} {m : ℕ} (v : ((α ⊕ Fin m) ⊕ Fin 1) → M) (xs : Fin 1 → M) :
    Sum.elim v (xs ∘ Fin.castAdd 0) ∘ logValPush (α := α) (m := m) =
      Sum.elim (v ∘ Sum.inl) xs := by
  funext z
  rcases z with (y | e)
  · rcases y with (i | j) <;> rfl
  · fin_cases e
    show (xs ∘ Fin.castAdd 0) (0 : Fin 1) = xs 0
    simp

omit [LEc.Structure M] in
theorem logSnoc0_apply (ys : Fin 0 → M) (b : M) :
    (Fin.snoc ys b : Fin (0 + 1) → M) 0 = b := by
  rw [Fin.snoc_zero]

def logRelLt {α : Type} {m : ℕ} (t₁ t₂ : LElog.Term (α ⊕ Fin m)) : LEc.BoundedFormula α m :=
  (BoundedFormula.relabel (atomMap (α := α))
    (logTermGraph t₁ ⊓
      BoundedFormula.ex
        (BoundedFormula.relabel (logValPush (α := α) (m := m)) (logTermGraph t₂) ⊓
          sqForm (eSub (Term.var (Sum.inr 0)) (Term.var (Sum.inl (Sum.inr 0))))))).ex

theorem logRelLt_realize {α : Type} {m : ℕ} (t₁ t₂ : LElog.Term (α ⊕ Fin m))
    (hLog : ∀ x y : M, logDefSet x y ↔ logFun x = y) (v : α → M) (xs : Fin m → M) :
    (logRelLt t₁ t₂).Realize v xs ↔
      leE (logRealize (Sum.elim v xs) t₁) (logRealize (Sum.elim v xs) t₂) := by
  rw [logRelLt, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨a, ha⟩
    rw [BoundedFormula.realize_relabel, atomMap_elim, BoundedFormula.realize_inf] at ha
    obtain ⟨h1, h2⟩ := ha
    have h1' : logRealize (Sum.elim v xs) t₁ = a := by
      have h := (logTermGraph_realize' hLog t₁ _ _).mp h1
      rw [elim_inl_comp] at h
      simpa using h
    rw [BoundedFormula.realize_ex] at h2
    obtain ⟨b, hb⟩ := h2
    rw [BoundedFormula.realize_inf, BoundedFormula.realize_relabel, logValPush_elim] at hb
    obtain ⟨hb1, hb2⟩ := hb
    have h2' : logRealize (Sum.elim v xs) t₂ = b := by
      have h := (logTermGraph_realize' hLog t₂ _ _).mp hb1
      simp only [elim_inl_comp, Sum.elim_inr, logSnoc0_apply] at h
      simpa using h
    rw [h1', h2']
    have hb2' : ∃ z : M, mulE z z = subE b a := by
      have h := (sqForm_realize _ _ _).mp hb2
      simpa [Term.realize_var, realize_eSub, Sum.elim_inl, Sum.elim_inr, logSnoc0_apply,
        leE, isSquare] using h
    simpa [leE, isSquare] using hb2'
  · intro h
    refine ⟨logRealize (Sum.elim v xs) t₁, ?_⟩
    rw [BoundedFormula.realize_relabel, atomMap_elim, BoundedFormula.realize_inf]
    refine ⟨?_, ?_⟩
    · refine (logTermGraph_realize' hLog t₁ _ _).mpr ?_
      simp only [elim_inl_comp, Sum.elim_inr]
    · rw [BoundedFormula.realize_ex]
      refine ⟨logRealize (Sum.elim v xs) t₂, ?_⟩
      rw [BoundedFormula.realize_inf]
      refine ⟨?_, ?_⟩
      · rw [BoundedFormula.realize_relabel, logValPush_elim]
        refine (logTermGraph_realize' hLog t₂ _ _).mpr ?_
        simp only [elim_inl_comp, Sum.elim_inr, logSnoc0_apply]
      · refine (sqForm_realize _ _ _).mpr ?_
        simp only [Term.realize_var, realize_eSub, Sum.elim_inl, Sum.elim_inr, logSnoc0_apply,
          leE, isSquare] at h ⊢
        exact h

/-! ## The relation case -/

def logRelTrans {α : Type} {m l : ℕ} (R : LElog.Relations l)
    (ts : Fin l → LElog.Term (α ⊕ Fin m)) : LEc.BoundedFormula α m :=
  match R with
  | Sum.inr q => match q with
    | ordRel.lt => logRelLt (ts 0) (ts 1)
  | Sum.inl r => nomatch r

def logTrans {α : Type} : ∀ {m : ℕ}, LElog.BoundedFormula α m → LEc.BoundedFormula α m
  | _, .falsum => ⊥
  | _, .equal t₁ t₂ =>
      (BoundedFormula.relabel (atomMap (α := α)) (logTermGraph t₁ ⊓ logTermGraph t₂)).ex
  | _, .rel R ts => logRelTrans R ts
  | _, .imp φ ψ => (logTrans φ).imp (logTrans ψ)
  | _, .all φ => (logTrans φ).all

/-! ## Unfolding lemmas for the `LElog` realization (stated with the raw constructors) -/

theorem logRealize_falsum {α : Type} {m : ℕ} (v : α → M) (xs : Fin m → M) :
    (@BoundedFormula.Realize LElog M (logStruct M) α m BoundedFormula.falsum v xs) ↔ False :=
  Iff.rfl

theorem logRealize_equal {α : Type} {m : ℕ} (t₁ t₂ : LElog.Term (α ⊕ Fin m)) (v : α → M)
    (xs : Fin m → M) :
    (@BoundedFormula.Realize LElog M (logStruct M) α m (BoundedFormula.equal t₁ t₂) v xs) ↔
      (@Term.realize LElog M (logStruct M) (α ⊕ Fin m) (Sum.elim v xs) t₁ =
        @Term.realize LElog M (logStruct M) (α ⊕ Fin m) (Sum.elim v xs) t₂) :=
  Iff.rfl

theorem logRealize_imp {α : Type} {m : ℕ} (φ ψ : LElog.BoundedFormula α m) (v : α → M)
    (xs : Fin m → M) :
    (@BoundedFormula.Realize LElog M (logStruct M) α m (BoundedFormula.imp φ ψ) v xs) ↔
      ((@BoundedFormula.Realize LElog M (logStruct M) α m φ v xs) →
        (@BoundedFormula.Realize LElog M (logStruct M) α m ψ v xs)) :=
  Iff.rfl

theorem logRealize_all {α : Type} {m : ℕ} (φ : LElog.BoundedFormula α (m + 1)) (v : α → M)
    (xs : Fin m → M) :
    (@BoundedFormula.Realize LElog M (logStruct M) α m (BoundedFormula.all φ) v xs) ↔
      ∀ a : M, @BoundedFormula.Realize LElog M (logStruct M) α (m + 1) φ v (Fin.snoc xs a) :=
  Iff.rfl

theorem logRealize_relMap_lt {α : Type} {m : ℕ} (ts : Fin 2 → LElog.Term (α ⊕ Fin m))
    (v : α → M) (xs : Fin m → M) :
    (@BoundedFormula.Realize LElog M (logStruct M) α m
        (BoundedFormula.rel (Sum.inr ordRel.lt) ts) v xs) ↔
      leE (logRealize (Sum.elim v xs) (ts 0)) (logRealize (Sum.elim v xs) (ts 1)) := by
  show @Structure.RelMap LElog M (logStruct M) 2 (Sum.inr ordRel.lt)
      (fun i => @Term.realize LElog M (logStruct M) (α ⊕ Fin m) (Sum.elim v xs) (ts i)) ↔
    leE (logRealize (Sum.elim v xs) (ts 0)) (logRealize (Sum.elim v xs) (ts 1))
  rw [logStruct_relMap_lt]
  exact Iff.rfl

theorem logTrans_realize {α : Type} {m : ℕ} (φ : LElog.BoundedFormula α m)
    (hLog : ∀ x y : M, logDefSet x y ↔ logFun x = y) (v : α → M) (xs : Fin m → M) :
    (logTrans φ).Realize v xs ↔ @BoundedFormula.Realize LElog M (logStruct M) α m φ v xs := by
  revert v xs
  induction φ with
  | falsum =>
      intro v xs
      rw [logTrans, BoundedFormula.realize_bot]
      exact (logRealize_falsum v xs).symm
  | equal t₁ t₂ =>
      intro v xs
      simp only [logTrans, BoundedFormula.realize_ex, BoundedFormula.realize_relabel,
        BoundedFormula.realize_inf]
      rw [logRealize_equal t₁ t₂ v xs]
      constructor
      · rintro ⟨a, h₁, h₂⟩
        rw [atomMap_elim] at h₁ h₂
        have h₁' : logRealize (Sum.elim v xs) t₁ = a := by
          have h := (logTermGraph_realize' hLog t₁ _ _).mp h₁
          rw [elim_inl_comp] at h
          simpa using h
        have h₂' : logRealize (Sum.elim v xs) t₂ = a := by
          have h := (logTermGraph_realize' hLog t₂ _ _).mp h₂
          rw [elim_inl_comp] at h
          simpa using h
        exact h₁'.trans h₂'.symm
      · rintro h
        refine ⟨logRealize (Sum.elim v xs) t₁, ?_, ?_⟩
        · rw [atomMap_elim]
          refine (logTermGraph_realize' hLog t₁ _ _).mpr ?_
          simp only [elim_inl_comp, Sum.elim_inr]
        · rw [atomMap_elim]
          refine (logTermGraph_realize' hLog t₂ _ _).mpr ?_
          simp only [elim_inl_comp, Sum.elim_inr]
          exact h.symm
  | rel R ts =>
      intro v xs
      rcases R with (r | q)
      · nomatch r
      · cases q
        show (logRelLt (ts 0) (ts 1)).Realize v xs ↔ _
        rw [logRelLt_realize _ _ hLog v xs, logRealize_relMap_lt]
  | imp φ ψ ihφ ihψ =>
      intro v xs
      rw [logTrans, BoundedFormula.realize_imp, logRealize_imp φ ψ v xs]
      exact imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
      intro v xs
      rw [logTrans, BoundedFormula.realize_all, logRealize_all φ v xs]
      exact forall_congr' fun a => ih v (Fin.snoc xs a)

/-! ## The definable logarithm is described by its graph -/

/-- In a model of `TE` the definable logarithm `logFun` is exactly the function defined by the
graph `logDefSet`: `logDefSet` is total (`LogDefSetModel`) and single-valued. -/
theorem logDefSet_iff_logFun {M : Type} [LEc.Structure M] (hM : M ⊨ TE) (x y : M) :
    logDefSet x y ↔ logFun x = y := by
  constructor
  · intro h
    exact (logDefSet_unique_of_model hM h (logFun_spec_of_model hM x)).symm
  · intro h
    rw [← h]
    exact logFun_spec_of_model hM x

/-! ## The main theorem -/

theorem LogTranslation {α : Type} {n : ℕ} (φ : Work.WilC5.LElog.BoundedFormula α n) :
    ∃ ψ : WilkiesDesign.CG.LEc.BoundedFormula α n,
      ∀ (M : Type) [WilkiesDesign.CG.LEc.Structure M],
        FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TE → ∀ (v : α → M) (xs : Fin n → M),
          (@FirstOrder.Language.BoundedFormula.Realize Work.WilC5.LElog M _ α n φ v xs) ↔
            (@FirstOrder.Language.BoundedFormula.Realize WilkiesDesign.CG.LEc M _ α n ψ v xs)
  := by
  refine ⟨logTrans φ, ?_⟩
  intro M instM hM v xs
  have hLog : ∀ x y : M, logDefSet x y ↔ logFun x = y := fun x y => logDefSet_iff_logFun hM x y
  have h := logTrans_realize (M := M) φ hLog v xs
  exact h.symm

end Work.WilC5
