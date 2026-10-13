/-
  WilC5, step "no new value" — `logFun (1 + δ)` stays inside the `rexp`-definable closure.

  The definable logarithm `logFun` is an `LEc`-notion (its graph `logDefSet` uses the *full*
  exponential), while the definable closure `Work.WilC2.Dcl A` is taken in the `rexp`-reduct
  `LRc = (ring ⊕ rexp)[[ℝ]]` of the `LEc`-structure (`Work.WilC5.reductStruct`).  The content of
  the lemma is therefore that, *on the relevant region*, `logFun` is recovered by an
  `LRc`-definable relation, so that it is automatically in `Dcl A` whenever its argument is.

  This is exactly what the two imported lemmas give, for `|2δ| ≤ 1` (i.e. `1 + δ ∈ [1/2, 3/2]`):

  * existence — `Work.WilC5.logFun_one_add_rexp`:
    `rexp (logFun (1 + δ)) = 1 + δ`, where `rexp = rexpFromExp` is the interpretation of the
    `rexp`-symbol of `LRc`;
  * uniqueness — `Work.WilC5.logFun_eq_of_rexp_eq`:
    *any* `u` with `rexp u = 1 + δ` equals `logFun (1 + δ)`.

  Hence the set `{v | rexp v = 1 + δ}` is the singleton `{logFun (1 + δ)}`, and it is
  `LRc`-definable from `A` because `δ` is: the relation `rexp v = 1 + y` is `LRc`-definable
  without parameters (both sides are `LRc`-terms), and the parameter `y` is replaced by a formula
  defining `δ` over `A` (`definable_setOf_of_definable_param`).
-/
import Mathlib
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical

namespace Work.WilC5.StepNoNewAux

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. Reading off `LEc`-operations from `LRc`-terms

The `rexp`-reduct `Work.WilC5.reductStruct` interprets the ring symbols of `LRc` exactly as the
`LEc`-structure does and the `rexp` symbol as `Work.WilC5.rexpFromExp`.  The following terms and
their realization lemmas make this explicit for the three operations appearing in the statement:
the restricted exponential, the constant `1`, and addition. -/

namespace LogAux

/-- The `LRc`-term `rexp t`. -/
def rexpTermL {α : Type} (t : LRc.Term α) : LRc.Term α :=
  Term.func (Sum.inl (Sum.inr rexpFunc.rexp)) ![t]

/-- The `LRc`-term for the constant `1`. -/
def oneTermL {α : Type} : LRc.Term α :=
  Term.func (Sum.inl (Sum.inl FirstOrder.Ring.oneFunc)) (Fin.elim0 : Fin 0 → LRc.Term α)

/-- The `LRc`-term `t₁ + t₂`. -/
def addTermL {α : Type} (t₁ t₂ : LRc.Term α) : LRc.Term α :=
  Term.func (Sum.inl (Sum.inl FirstOrder.Ring.addFunc)) ![t₁, t₂]

/-- The term `rexp (v ↦ v (Sum.inl 0))` on `(Fin 1 ⊕ Fin 1)`-tuples: the first variable is the
point, the second is the (existentially quantified) parameter. -/
def rexpVarTerm : LRc.Term (Fin 1 ⊕ Fin 1) :=
  rexpTermL (Term.var (L := LRc) (Sum.inl (0 : Fin 1)))

/-- The term `1 + v (Sum.inr 0)` on `(Fin 1 ⊕ Fin 1)`-tuples. -/
def addOneVarTerm : LRc.Term (Fin 1 ⊕ Fin 1) :=
  addTermL oneTermL (Term.var (L := LRc) (Sum.inr (0 : Fin 1)))

theorem rexpTermL_realize {K : Type} [WilkiesDesign.CG.LEc.Structure K] {α : Type} (v : α → K)
    (t : LRc.Term α) :
    (rexpTermL t).realize v = Work.WilC5.rexpFromExp (Term.realize v t) := by
  rw [rexpTermL, Term.realize_func]
  rw [show (fun i => Term.realize v (![t] i)) = ![Term.realize v t] from by
        funext i; fin_cases i; rfl]
  exact Work.WilC5.reductStruct_funMap_rexp K ![Term.realize v t]

theorem oneTermL_realize {K : Type} [WilkiesDesign.CG.LEc.Structure K] {α : Type} (v : α → K) :
    (oneTermL (α := α)).realize v = Work.WilC5.oneE := by
  rw [oneTermL, Term.realize_func]
  rw [show (fun i : Fin 0 => Term.realize v (Fin.elim0 i)) = (default : Fin 0 → K) from
        Subsingleton.elim _ _]
  exact Work.WilC5.reductStruct_funMap_ring K FirstOrder.Ring.oneFunc (default : Fin 0 → K)

theorem addTermL_realize {K : Type} [WilkiesDesign.CG.LEc.Structure K] {α : Type} (v : α → K)
    (t₁ t₂ : LRc.Term α) :
    (addTermL t₁ t₂).realize v = Work.WilC5.addE (Term.realize v t₁) (Term.realize v t₂) := by
  rw [addTermL, Term.realize_func]
  rw [show (fun i => Term.realize v (![t₁,t₂] i)) = ![Term.realize v t₁, Term.realize v t₂] from by
        funext i; fin_cases i <;> rfl]
  exact Work.WilC5.reductStruct_funMap_ring K FirstOrder.Ring.addFunc
    ![Term.realize v t₁, Term.realize v t₂]

end LogAux

/-! ## 2. Replacing a definable parameter by a formula

If the parameter `c` is `A`-definable (as a singleton), then any relation `P v c` that is
`A`-definable as a relation in `(v, y)` is also `A`-definable as a set of points `v`. -/

theorem definable_setOf_of_definable_param {K : Type} [LRc.Structure K] {A : Set K}
    {c : K} {P : K → K → Prop}
    (hP : A.Definable LRc {w : (Fin 1 ⊕ Fin 1) → K | P (w (Sum.inl 0)) (w (Sum.inr 0))})
    (hc : A.Definable LRc {p : Fin 1 → K | p 0 = c}) :
    A.Definable LRc {p : Fin 1 → K | P (p 0) c} := by
  -- the condition `w (Sum.inr 0) = c` is `A`-definable on `(Fin 1 ⊕ Fin 1)`-tuples
  have hC : A.Definable LRc {w : (Fin 1 ⊕ Fin 1) → K | w (Sum.inr 0) = c} := by
    have h := hc.preimage_comp (fun _ : Fin 1 => (Sum.inr 0 : Fin 1 ⊕ Fin 1))
    convert h using 1
    ext w; simp
  have hInt : A.Definable LRc
      ({w : (Fin 1 ⊕ Fin 1) → K | P (w (Sum.inl 0)) (w (Sum.inr 0))} ∩
       {w : (Fin 1 ⊕ Fin 1) → K | w (Sum.inr 0) = c}) := hP.inter hC
  -- existentially quantify the parameter block
  have hProj := Set.Definable.exists_of_finite hInt
  convert hProj using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro hp
    exact ⟨fun _ => c, hp, rfl⟩
  · rintro ⟨u, h1, h2⟩
    rwa [h2] at h1

/-! ## 3. The theorem -/

theorem logFun_one_add_mem_dcl {K : Type} [WilkiesDesign.CG.LEc.Structure K]
    (hK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    {A : Set K} {δ : K} (hδA : δ ∈ Work.WilC2.Dcl A)
    (hδ : Work.WilC5.absLeOne
      (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) δ)) :
    Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ) ∈ Work.WilC2.Dcl A := by
  set z : K := Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE δ) with hz
  rw [Work.WilC2.mem_dcl]
  -- `δ` is `A`-definable
  have hc : A.Definable LRc {p : Fin 1 → K | p 0 = δ} := by
    have h := hδA
    rw [Work.WilC2.mem_dcl] at h
    simpa only [Set.Definable₁, Set.mem_singleton_iff] using h
  -- the relation `rexp v = 1 + y` is `LRc`-definable without parameters
  have hR0 : (∅ : Set K).Definable LRc
      {w : (Fin 1 ⊕ Fin 1) → K | Work.WilC5.rexpFromExp (w (Sum.inl 0)) =
        Work.WilC5.addE Work.WilC5.oneE (w (Sum.inr 0))} := by
    have hf : (∅ : Set K).DefinableFun LRc
        (fun w : (Fin 1 ⊕ Fin 1) → K => Work.WilC5.rexpFromExp (w (Sum.inl 0))) := by
      have h := Term.definableFun_realize (L := LRc) (M := K) (α := Fin 1 ⊕ Fin 1)
        LogAux.rexpVarTerm
      convert h using 1
      funext w
      rw [LogAux.rexpVarTerm, LogAux.rexpTermL_realize, Term.realize_var]
    have hg : (∅ : Set K).DefinableFun LRc
        (fun w : (Fin 1 ⊕ Fin 1) → K => Work.WilC5.addE Work.WilC5.oneE (w (Sum.inr 0))) := by
      have h := Term.definableFun_realize (L := LRc) (M := K) (α := Fin 1 ⊕ Fin 1)
        LogAux.addOneVarTerm
      convert h using 1
      funext w
      rw [LogAux.addOneVarTerm, LogAux.addTermL_realize, LogAux.oneTermL_realize,
        Term.realize_var]
    exact Set.DefinableFun.ofPred_eq hf hg
  have hR : A.Definable LRc
      {w : (Fin 1 ⊕ Fin 1) → K | Work.WilC5.rexpFromExp (w (Sum.inl 0)) =
        Work.WilC5.addE Work.WilC5.oneE (w (Sum.inr 0))} :=
    hR0.mono (Set.empty_subset A)
  -- replace the parameter `δ` by its defining formula
  have hparam := definable_setOf_of_definable_param (A := A) (c := δ)
      (P := fun v y => Work.WilC5.rexpFromExp v = Work.WilC5.addE Work.WilC5.oneE y) hR hc
  -- `z` is the *unique* solution of `rexp · = 1 + δ`
  have huniq : ∀ u : K, Work.WilC5.rexpFromExp u = Work.WilC5.addE Work.WilC5.oneE δ → u = z := by
    intro u hu
    rw [hz]
    exact Work.WilC5.logFun_eq_of_rexp_eq hK hδ hu
  have hexp : Work.WilC5.rexpFromExp z = Work.WilC5.addE Work.WilC5.oneE δ := by
    rw [hz]
    exact Work.WilC5.logFun_one_add_rexp hK hδ
  have hsing : {p : Fin 1 → K | Work.WilC5.rexpFromExp (p 0) = Work.WilC5.addE Work.WilC5.oneE δ}
      = {fun _ : Fin 1 => z} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hp
      funext i
      rw [Subsingleton.elim i 0]
      exact huniq (p 0) hp
    · intro hp
      subst hp
      simpa using hexp
  rw [hsing] at hparam
  -- `A.Definable₁ LRc {z}` is `A.Definable LRc {v | v 0 ∈ {z}}`
  rw [Set.Definable₁]
  convert hparam using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    rw [Subsingleton.elim i 0]
    exact h
  · intro h
    rw [h]

end Work.WilC5.StepNoNewAux
