/-
  WilC5 / FOV — `SubfieldClosureL`.

  Let `K` be a model of `TE` (the `LEc`-theory of `ℝ_exp`) whose `LEc`-symbols are related to
  the field operations by the hypotheses `hadd`, `hmul`, `hone`, and let `B` be an `LRc`-
  substructure closed under `LRc`-definable closure in the `rexp`-reduct `reductStruct K`.
  Then the underlying set of `B` is a *subfield* of `K`: it contains `0` and `1` and is closed
  under negation, inversion, addition and multiplication.

  The mathematical content is that all those field operations are *definable* in the language
  `LRc`: `+` and `*` directly, as function symbols; `1` as the value of the constant term; `0` as
  the unique solution of `x + x = x`; `-x` as the unique solution of `(y + x) + (y + x) = y + x`
  (i.e. of `y + x = 0`); and `x⁻¹` as the unique solution of `x * y = 1`.  The interpretations
  of `+`, `*`, `1` in `reductStruct K` are the field operations by `hadd`, `hmul`, `hone`.  The
  remaining parts of the `LRc`-structure (the reals as constants, the symbol `0`, and negation
  `-`) are irrelevant for the conclusion, so `K ⊨ TE` is not used beyond the compatibility
  hypotheses `hrexp`, `hadd`, `hmul`, `hone` already record.

  The work is done by the general lemma `dcl_fieldClosure`, stated for an arbitrary
  `LRc`-structure on a field, which is then specialised to the `rexp`-reduct of `K`.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.S4Setup
import Submission.Work.WilC5.Bridge
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC4.dcl_mul
import Submission.Work.WilC4.dcl_inv
import Submission.Work.WilC4.dcl_neg
import Submission.Work.WilC4.dcl_add
import Submission.Work.WilC2.Square
import Submission.Work.WilC5.LRcOps

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign.CG

namespace Work.WilC5.FOV

variable {M : Type} [LRc.Structure M] [Field M]

/-! ## Decomposing "`x ∈ Dcl A`" -/

/-- Membership in the definable closure of `A` (in the `LRc`-sense) is the definability of the
singleton `{x}`, i.e. of the set of `Fin 1`-tuples with zeroth coordinate `x`. -/
lemma mem_dcl_iff {A : Set M} {c : M} :
    c ∈ Work.WilC2.Dcl A ↔ A.Definable LRc {v : Fin 1 → M | v 0 = c} := by
  rw [Work.WilC2.mem_dcl]
  rfl

/-! ## Two tools for building definable singletons -/

/-- The set of tuples equal to a fixed tuple `b` all of whose entries lie in `A` is `A`-definable
(as a finite intersection of singleton fibers). -/
lemma definable_const_vec {A : Set M} {n : ℕ} {b : Fin n → M} (hb : ∀ i, b i ∈ A) :
    A.Definable LRc {u : Fin n → M | u = b} := by
  have hset : {u : Fin n → M | u = b} = ⋂ i, {u : Fin n → M | u i = b i} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
  rw [hset]
  refine Set.definable_iInter_of_finite (fun i => ?_)
  have h1 : A.Definable LRc {x : Fin 1 → M | x 0 = b i} := by
    simpa [Set.Definable₁, Set.mem_singleton_iff] using
      (Set.Definable.singleton_of_mem (L := LRc) (hb i))
  exact (h1.preimage_comp (fun _ : Fin 1 => i))

/-- **If `f` is `A`-definable and every entry of `b` lies in `A`, then the singleton `{f b}` is
`A`-definable.**  The graph of `f` lives on `Option (Fin n)`-tuples; pulling it back along
`none ↦ Sum.inl 0`, `some j ↦ Sum.inr j` and intersecting it with the cylinder `u = b` gives a
definable set of `Fin 1 ⊕ Fin n`-tuples whose projection onto the first block is `{f b}`. -/
lemma definable_singleton_apply {A : Set M} {n : ℕ} {f : (Fin n → M) → M}
    (hf : A.DefinableFun LRc f) {b : Fin n → M} (hb : ∀ i, b i ∈ A) :
    A.Definable LRc {v : Fin 1 → M | v 0 = f b} := by
  let σ : Option (Fin n) → Fin 1 ⊕ Fin n := fun i =>
    match i with
    | none => Sum.inl 0
    | some j => Sum.inr j
  have hS : A.Definable LRc
      {w : (Fin 1 ⊕ Fin n) → M | w (Sum.inl 0) = f (w ∘ Sum.inr)} := by
    have hf' : A.Definable LRc f.tupleGraph := hf
    have h := Set.Definable.preimage_comp (A := A) (L := LRc) σ hf'
    convert h using 1
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Function.tupleGraph, Function.comp_def]
    exact eq_comm
  have hC : A.Definable LRc {w : (Fin 1 ⊕ Fin n) → M | w ∘ Sum.inr = b} := by
    have h := (definable_const_vec (A := A) hb).preimage_comp (Sum.inr : Fin n → Fin 1 ⊕ Fin n)
    convert h using 1
    ext w; rfl
  have hproj := (hS.inter hC).exists_of_finite (α := Fin 1) (β := Fin n)
  have hset : {v : Fin 1 → M | ∃ u : Fin n → M, Sum.elim v u ∈
      ({w : (Fin 1 ⊕ Fin n) → M | w (Sum.inl 0) = f (w ∘ Sum.inr)} ∩
       {w : (Fin 1 ⊕ Fin n) → M | w ∘ Sum.inr = b})} = {v : Fin 1 → M | v 0 = f b} := by
    ext v
    constructor
    · rintro ⟨u, h1, h2⟩
      have h2' : u = b := h2
      rw [h2'] at h1
      simpa using h1
    · intro hv
      exact ⟨b, hv, rfl⟩
  rw [hset] at hproj
  exact hproj

/-! ## The field operations are definable functions of the `LRc`-structure -/

/-- Addition is a definable function: it is the interpretation of the binary symbol `+`, which
the hypothesis `hadd` identifies with the addition of the field. -/
lemma definableFun_add {A : Set M}
    (hadd : ∀ x y : M,
      (@Structure.funMap LRc M _ 2 (Sum.inl (Sum.inl Ring.addFunc)) ![x,y] : M) = x + y) :
    A.DefinableFun LRc (fun v : Fin 2 → M => v 0 + v 1) := by
  have hfun : (fun v : Fin 2 → M => v 0 + v 1)
      = fun v : Fin 2 → M => @Structure.funMap LRc M _ 2 (Sum.inl (Sum.inl Ring.addFunc)) v := by
    funext v
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv]
    exact (hadd (v 0) (v 1)).symm
  rw [hfun]
  exact (Set.DefinableFun.fun_symbol (L := LRc)
    (f := (Sum.inl (Sum.inl Ring.addFunc) : LRc.Functions 2))).of_empty

/-- Multiplication is a definable function, for the same reason. -/
lemma definableFun_mul {A : Set M}
    (hmul : ∀ x y : M,
      (@Structure.funMap LRc M _ 2 (Sum.inl (Sum.inl Ring.mulFunc)) ![x,y] : M) = x * y) :
    A.DefinableFun LRc (fun v : Fin 2 → M => v 0 * v 1) := by
  have hfun : (fun v : Fin 2 → M => v 0 * v 1)
      = fun v : Fin 2 → M => @Structure.funMap LRc M _ 2 (Sum.inl (Sum.inl Ring.mulFunc)) v := by
    funext v
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv]
    exact (hmul (v 0) (v 1)).symm
  rw [hfun]
  exact (Set.DefinableFun.fun_symbol (L := LRc)
    (f := (Sum.inl (Sum.inl Ring.mulFunc) : LRc.Functions 2))).of_empty

/-- A definable binary operation applied to two definable functions is a definable function. -/
lemma definableFun_binop {A : Set M} {γ : Type*} [Finite γ] {f : (Fin 2 → M) → M}
    (hf : A.DefinableFun LRc f) {g₁ g₂ : (γ → M) → M}
    (h₁ : A.DefinableFun LRc g₁) (h₂ : A.DefinableFun LRc g₂) :
    A.DefinableFun LRc (fun v : γ → M => f ![g₁ v, g₂ v]) := by
  refine Set.DefinableFun.comp (A := A) (f := f) ?_ hf
  intro i
  fin_cases i
  · simpa using h₁
  · simpa using h₂

/-- Sums of `A`-definable functions are `A`-definable. -/
lemma DefinableFun.add {A : Set M} {γ : Type*} [Finite γ] {g₁ g₂ : (γ → M) → M}
    (hadd : ∀ x y : M,
      (@Structure.funMap LRc M _ 2 (Sum.inl (Sum.inl Ring.addFunc)) ![x,y] : M) = x + y)
    (h₁ : A.DefinableFun LRc g₁) (h₂ : A.DefinableFun LRc g₂) :
    A.DefinableFun LRc (fun v : γ → M => g₁ v + g₂ v) := by
  have h := definableFun_binop (A := A) (definableFun_add (A := A) hadd) h₁ h₂
  have heq : (fun v : γ → M => g₁ v + g₂ v)
      = (fun v : γ → M => (fun w : Fin 2 → M => w 0 + w 1) ![g₁ v, g₂ v]) := by
    funext v; simp
  rw [heq]
  exact h

/-- Products of `A`-definable functions are `A`-definable. -/
lemma DefinableFun.mul {A : Set M} {γ : Type*} [Finite γ] {g₁ g₂ : (γ → M) → M}
    (hmul : ∀ x y : M,
      (@Structure.funMap LRc M _ 2 (Sum.inl (Sum.inl Ring.mulFunc)) ![x,y] : M) = x * y)
    (h₁ : A.DefinableFun LRc g₁) (h₂ : A.DefinableFun LRc g₂) :
    A.DefinableFun LRc (fun v : γ → M => g₁ v * g₂ v) := by
  have h := definableFun_binop (A := A) (definableFun_mul (A := A) hmul) h₁ h₂
  have heq : (fun v : γ → M => g₁ v * g₂ v)
      = (fun v : γ → M => (fun w : Fin 2 → M => w 0 * w 1) ![g₁ v, g₂ v]) := by
    funext v; simp
  rw [heq]
  exact h

/-! ## The main lemma: a `Dcl`-closed set is a subfield -/

/-- **A set closed under `LRc`-definable closure is a subfield.**

Let `M` be a field carrying an arbitrary `LRc`-structure whose binary symbols `+` and `*` and
whose constant `1` are interpreted as the field operations (`hadd`, `hmul`, `hone`).  If
`Dcl A ⊆ A`, then `A` contains `0, 1` and is closed under `-`, `⁻¹`, `+` and `*`.

Indeed `1` is the value of the constant term; `0` is the unique solution of `x + x = x`; `-x` is
the unique solution of `(y + x) + (y + x) = y + x`, i.e. of `y + x = 0`; `x⁻¹` is the unique
solution of `x * y = 1`; and the graphs of `+` and `*` are definable. -/
theorem dcl_fieldClosure {A : Set M}
    (hadd : ∀ x y : M,
      (@Structure.funMap LRc M _ 2 (Sum.inl (Sum.inl Ring.addFunc)) ![x,y] : M) = x + y)
    (hmul : ∀ x y : M,
      (@Structure.funMap LRc M _ 2 (Sum.inl (Sum.inl Ring.mulFunc)) ![x,y] : M) = x * y)
    (hone : (@Structure.funMap LRc M _ 0 (Sum.inl (Sum.inl Ring.oneFunc))
      (default : Fin 0 → M) : M) = 1)
    (hA : Work.WilC2.Dcl A ⊆ A) :
    (0 : M) ∈ A ∧ (1 : M) ∈ A ∧ (∀ x ∈ A, -x ∈ A) ∧
      (∀ x ∈ A, x ≠ 0 → x⁻¹ ∈ A) ∧
      (∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) ∧ (∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) := by
  have h1 : (1 : M) ∈ A := by
    apply hA
    rw [mem_dcl_iff]
    have hf : A.DefinableFun LRc
        (@Structure.funMap LRc M _ 0 (Sum.inl (Sum.inl Ring.oneFunc)) : (Fin 0 → M) → M) :=
      (Set.DefinableFun.fun_symbol (L := LRc)
        (f := (Sum.inl (Sum.inl Ring.oneFunc) : LRc.Functions 0))).of_empty
    have h := definable_singleton_apply (A := A)
      (f := (@Structure.funMap LRc M _ 0 (Sum.inl (Sum.inl Ring.oneFunc)) : (Fin 0 → M) → M)) hf
      (b := (default : Fin 0 → M)) (by intro i; exact Fin.elim0 i)
    rwa [hone] at h
  have h0 : (0 : M) ∈ A := by
    apply hA
    rw [mem_dcl_iff]
    have hF : A.DefinableFun LRc (fun v : Fin 1 → M => v 0 + v 0) :=
      DefinableFun.add (A := A) hadd (Set.DefinableFun.proj LRc) (Set.DefinableFun.proj LRc)
    have hG : A.DefinableFun LRc (fun v : Fin 1 → M => v 0) := Set.DefinableFun.proj LRc
    have h := hF.ofPred_eq hG
    have hset : {v : Fin 1 → M | v 0 = (0 : M)} = {v : Fin 1 → M | v 0 + v 0 = v 0} := by
      ext v
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hv; rw [hv, zero_add]
      · intro hv; exact add_left_cancel (by rw [hv, add_zero])
    rw [hset]
    exact h
  have hneg : ∀ x ∈ A, -x ∈ A := by
    intro x hx
    apply hA
    rw [mem_dcl_iff]
    have hx' : A.DefinableFun LRc (fun v : Fin 1 → M => v 0 + x) :=
      DefinableFun.add (A := A) hadd (Set.DefinableFun.proj LRc)
        (Language.definableFun_const LRc (γ := Fin 1) hx)
    have h := (DefinableFun.add (A := A) hadd hx' hx').ofPred_eq hx'
    have hset : {v : Fin 1 → M | v 0 = -x}
        = {v : Fin 1 → M | (v 0 + x) + (v 0 + x) = v 0 + x} := by
      ext v
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hv; rw [hv]; ring
      · intro hv
        exact eq_neg_iff_add_eq_zero.mpr (add_left_cancel (by rw [hv, add_zero]))
    rw [hset]
    exact h
  have hinv : ∀ x ∈ A, x ≠ 0 → x⁻¹ ∈ A := by
    intro x hx hx0
    apply hA
    rw [mem_dcl_iff]
    have hf : A.DefinableFun LRc (fun v : Fin 1 → M => x * v 0) :=
      DefinableFun.mul (A := A) hmul (Language.definableFun_const LRc (γ := Fin 1) hx)
        (Set.DefinableFun.proj LRc)
    have h := hf.ofPred_eq_const h1
    have hset : {v : Fin 1 → M | v 0 = x⁻¹} = {v : Fin 1 → M | x * v 0 = 1} := by
      ext v
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hv; rw [hv, mul_inv_cancel₀ hx0]
      · intro hv
        calc v 0 = (x⁻¹ * x) * v 0 := by rw [inv_mul_cancel₀ hx0, one_mul]
          _ = x⁻¹ * (x * v 0) := by rw [mul_assoc]
          _ = x⁻¹ := by rw [hv, mul_one]
    rw [hset]
    exact h
  have haddm : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A := by
    intro x hx y hy
    apply hA
    rw [mem_dcl_iff]
    have h := definable_singleton_apply (A := A) (n := 2) (f := fun v : Fin 2 → M => v 0 + v 1)
      (definableFun_add hadd) (b := ![x, y]) (by
        intro i
        fin_cases i
        · simpa using hx
        · simpa using hy)
    simpa using h
  have hmulm : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A := by
    intro x hx y hy
    apply hA
    rw [mem_dcl_iff]
    have h := definable_singleton_apply (A := A) (n := 2) (f := fun v : Fin 2 → M => v 0 * v 1)
      (definableFun_mul hmul) (b := ![x, y]) (by
        intro i
        fin_cases i
        · simpa using hx
        · simpa using hy)
    simpa using h
  exact ⟨h0, h1, hneg, hinv, haddm, hmulm⟩

/-! ## The requested theorem -/

theorem SubfieldClosureL {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K)) :
    (0 : K) ∈ (B : Set K) ∧ (1 : K) ∈ (B : Set K) ∧
      (∀ x ∈ (B : Set K), -x ∈ (B : Set K)) ∧
      (∀ x ∈ (B : Set K), x ≠ 0 → x⁻¹ ∈ (B : Set K)) ∧
      (∀ x ∈ (B : Set K), ∀ y ∈ (B : Set K), x + y ∈ (B : Set K)) ∧
      (∀ x ∈ (B : Set K), ∀ y ∈ (B : Set K), x * y ∈ (B : Set K)) := by
  -- The `LRc`-symbols `+`, `*`, `1` of the `rexp`-reduct are the field operations.
  have hAddR : ∀ x y : K, (@Structure.funMap LRc K (Work.WilC5.reductStruct K) 2
      (Sum.inl (Sum.inl Ring.addFunc)) ![x,y] : K) = x + y := fun x y => hadd x y
  have hMulR : ∀ x y : K, (@Structure.funMap LRc K (Work.WilC5.reductStruct K) 2
      (Sum.inl (Sum.inl Ring.mulFunc)) ![x,y] : K) = x * y := fun x y => hmul x y
  have hOneR : (@Structure.funMap LRc K (Work.WilC5.reductStruct K) 0
      (Sum.inl (Sum.inl Ring.oneFunc)) (default : Fin 0 → K) : K) = 1 := hone
  exact @dcl_fieldClosure K (Work.WilC5.reductStruct K) _ (B : Set K) hAddR hMulR hOneR hBdcl

end Work.WilC5.FOV
