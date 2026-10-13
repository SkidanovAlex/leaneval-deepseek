/-
  WilC4/ULPMSyntax : the first-order content of the *uniform log-piecewise-monomiality*
  statement `Route.ModelULPM` (`WilC4/ULPMDefs.lean`), for a fixed parameter-free formula.

  `Route.ModelULPM M` quantifies over an `∅`-definable set `Y ⊆ M^{k+2}` (a family of graphs
  `x ↦ y` in the parameters `c`), and produces `N : ℕ`, a finite set `Qs : Finset ℚ` and an
  `∅`-definable `B ⊆ M^{k+1}` (the breakpoint family).  To *transfer* it from `ℝ` to every model
  of `TR` we must exhibit, for a fixed parameter-free `LRc`-formula `φ` defining `Y` and a fixed
  parameter-free `LRc`-formula `ψ` defining `B`, and fixed meta-data `N : ℕ`, `qs : Fin Nq → ℚ`,
  a single `LRc`-**sentence** `ulpmSent k N Nq φ ψ qs` asserting the conclusion.  This file
  builds that sentence and proves the semantic characterisation `ulpmSent_realize`.

  The sentence (with `N` the ULPM constant, `Nq` the number of listed exponents) reads

      (∀ c x y y', φ(x,y,c) → φ(x,y',c) → y = y') →
      ∀ c,  (at most `N` many `x` with ψ(x,c))
            ∧ ∀ x₁ x₂ > 0, (`x₁, x₂` on the same side of all breakpoints of `ψ(·,c)`, factor `N`,
                i.e. ∀ b, ψ(b,c) → (N·b < x₁ ∧ N·b < x₂) ∨ (N·x₁ < b ∧ N·x₂ < b)) →
                 (∃ y, φ(x₁,y,c)) ↔ (∃ y, φ(x₂,y,c))
                 ∧ ∀ y₁ y₂, φ(x₁,y₁,c) → φ(x₂,y₂,c) →
                     ∃ i : Fin Nq, ∃ t₁ t₂, IsRpow x₁ (qs i) t₁ ∧ IsRpow x₂ (qs i) t₂
                       ∧ |y₂|·t₁ ≤ N·(|y₁|·t₂) ∧ |y₁|·t₂ ≤ N·(|y₂|·t₁)

  `IsRpow` is *not* a symbol of `LRc`, so it is written in the `LRc`-definable form
  `t ^ den * x ^ (-num).toNat = x ^ num.toNat ∧ (t = 0 ∨ ∃ w ≠ 0, w * w = t)`
  (`rpowRel`); for `0 < x` the two are equivalent (`rpowRel_iff_isRpow`, from `isRpow_iff_form`).
  The order and the absolute values are expressed *inside the language of rings*, via "`u ≤ v`"
  = `∃ z, u + z * z = v` (`leTerm`) and "`|y₂|·t₁ ≤ N·(|y₁|·t₂)`" = "`(y₂ t₁)² ≤ (N y₁ t₂)²`"
  (`approxAtom`, valid because `t₁, t₂ ≥ 0`), so that the sentence means the same thing in `ℝ`
  and in every model of `TR`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.PBRealize
import Submission.Work.WilC4.isRpow_definable
import Submission.Work.WilC4.isRpow_iff_form

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR liftR_realize leF leF_realize leF_realize_le)

/-! ## 1. Numeral terms and the arithmetic atoms -/

/-- The numeral `N` as a term of the language of rings. -/
def nTerm {α : Type*} : ℕ → ring.Term α
  | 0 => 0
  | (n + 1) => nTerm n + 1

theorem nTerm_realize {R : Type*} [Ring R] [Ring.CompatibleRing R] {α : Type*}
    (v : α → R) (N : ℕ) : Term.realize v (nTerm N : ring.Term α) = (N : R) := by
  induction N with
  | zero => simp [nTerm]
  | succ n ih =>
      rw [show (nTerm (n + 1) : ring.Term α) = nTerm n + 1 from rfl, Ring.realize_add,
        Ring.realize_one, ih, Nat.cast_succ]

/-- `leTerm u v` is the ring atom `∃ z, u + z * z = v`, i.e. `u ≤ v` in an ordered field in
which every nonnegative element is a square. -/
def leTerm {α : Type*} (u v : ring.Term α) : ring.Formula α :=
  (Term.bdEqual (Term.relabel (Sum.inl : α → α ⊕ Fin 1) u +
      (Term.var (Sum.inr 0) * Term.var (Sum.inr 0)))
    (Term.relabel (Sum.inl : α → α ⊕ Fin 1) v)).ex

theorem leTerm_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] {α : Type*} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (u v : ring.Term α) (w : α → M) :
    (leTerm u v).Realize w ↔ Term.realize w u ≤ Term.realize w v := by
  have hrel : ∀ (z : M) (t : ring.Term α),
      Term.realize (Sum.elim w (fun _ : Fin 1 => z)) (Term.relabel (Sum.inl : α → α ⊕ Fin 1) t)
        = Term.realize w t := by
    intro z t
    rw [Term.realize_relabel]
    rfl
  unfold leTerm
  rw [Formula.Realize, BoundedFormula.realize_ex]
  constructor
  · rintro ⟨z, hz⟩
    rw [BoundedFormula.realize_bdEqual, Fin.snoc_zero, Ring.realize_add, Ring.realize_mul,
      Term.realize_var, hrel z u, hrel z v] at hz
    simp only [Sum.elim_inr] at hz
    nlinarith [mul_self_nonneg z]
  · intro huv
    obtain ⟨z, hz⟩ := hsq (Term.realize w v - Term.realize w u) (by linarith)
    refine ⟨z, ?_⟩
    rw [BoundedFormula.realize_bdEqual, Fin.snoc_zero, Ring.realize_add, Ring.realize_mul,
      Term.realize_var, hrel z u, hrel z v]
    simp only [Sum.elim_inr]
    linarith

/-- The atom `(N : R) * b < x` (variables `(b, x)`). -/
def ltNMul (N : ℕ) : ring.Formula (Fin 2) :=
  (leTerm (Term.var 1) ((nTerm N : ring.Term (Fin 2)) * Term.var 0)).not

theorem ltNMul_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (N : ℕ)
    (v : Fin 2 → M) : (ltNMul N).Realize v ↔ (N : M) * v 0 < v 1 := by
  rw [ltNMul, Formula.realize_not, leTerm_realize hsq, Ring.realize_mul, nTerm_realize,
    Term.realize_var, Term.realize_var]
  exact not_le

/-- The atom `|y₂| * t₁ ≤ (N : R) * (|y₁| * t₂)` (variables `(y₁, y₂, t₁, t₂)`), written as the
equivalent `(y₂ t₁)² ≤ ((N y₁) t₂)²`. -/
def approxAtom (N : ℕ) : ring.Formula (Fin 4) :=
  let t : ring.Term (Fin 4) := ((nTerm N : ring.Term (Fin 4)) * Term.var 0) * Term.var 3
  leTerm ((Term.var 1 * Term.var 2) * (Term.var 1 * Term.var 2)) (t * t)

theorem approxAtom_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (N : ℕ)
    (v : Fin 4 → M) (h2 : 0 ≤ v 2) (h3 : 0 ≤ v 3) :
    (approxAtom N).Realize v ↔ |v 1| * v 2 ≤ (N : M) * (|v 0| * v 3) := by
  have hN : (0 : M) ≤ (N : M) := Nat.cast_nonneg N
  have e1 : (v 1 * v 2) * (v 1 * v 2) = (v 1 * v 2) ^ 2 := by ring
  have e2 : ((↑N * v 0) * v 3) * ((↑N * v 0) * v 3) = ((↑N * v 0) * v 3) ^ 2 := by ring
  rw [approxAtom, leTerm_realize hsq]
  simp only [Ring.realize_mul, nTerm_realize, Term.realize_var, e1, e2, sq_le_sq]
  simp only [abs_mul, abs_of_nonneg h2, abs_of_nonneg h3, abs_of_nonneg hN, mul_assoc]

/-! ## 2. The `LRc`-definable form of `IsRpow` -/

/-- `rpowRel p n` (variables `(x, t)`) is
`t ^ n * x ^ (-p).toNat = x ^ p.toNat ∧ (t = 0 ∨ ∃ w ≠ 0, w * w = t)`. -/
def rpowRel (p : ℤ) (n : ℕ) : LRc.Formula (Fin 2) :=
  (liftR (id : Fin 2 → Fin 2) (rpowAtom n (-p).toNat p.toNat)) ⊓
    ((liftR (fun _ : Fin 1 => (1 : Fin 2)) zeroAtom) ⊔
      (liftR (fun _ : Fin 1 => (1 : Fin 2)) isSqNeZeroAtom))

theorem rpowRel_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (p : ℤ) (n : ℕ) (v : Fin 2 → M) :
    (rpowRel p n).Realize v ↔
      v 1 ^ n * v 0 ^ (-p).toNat = v 0 ^ p.toNat ∧
        (v 1 = 0 ∨ ∃ w : M, w ≠ 0 ∧ w * w = v 1) := by
  have h1 := rpowAtom_lift n (-p).toNat p.toNat (id : Fin 2 → Fin 2) v
  have h2 := zeroAtom_lift (fun _ : Fin 1 => (1 : Fin 2)) v
  have h3 := isSqNeZeroAtom_lift (fun _ : Fin 1 => (1 : Fin 2)) v
  simp only [rpowRel, Formula.realize_inf, Formula.realize_sup]
  rw [h1, h2, h3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons,
    id_eq]

theorem rpowRel_relabel {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {Ctx : Type} (p : ℤ) (n : ℕ) (xt tt : Ctx) (rw : Ctx → M) :
    (Formula.relabel ![xt, tt] (rpowRel p n)).Realize rw ↔
      rw tt ^ n * rw xt ^ (-p).toNat = rw xt ^ p.toNat ∧
        (rw tt = 0 ∨ ∃ w : M, w ≠ 0 ∧ w * w = rw tt) := by
  rw [Formula.realize_relabel]
  have h : rw ∘ ![xt, tt] = ![rw xt, rw tt] := by
    funext i; fin_cases i <;> rfl
  rw [h, rpowRel_realize]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem rpowRel_iff_isRpow {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (q : ℚ) {x t : M} (hx : 0 < x) :
    (rpowRel q.num q.den).Realize ![x, t] ↔ IsRpow x q t := by
  have h : IsRpow x q t ↔ (t = 0 ∨ ∃ w : M, w ≠ 0 ∧ w ^ 2 = t) ∧
      t ^ q.den * x ^ (-q.num).toNat = x ^ q.num.toNat := by
    have h0 := isRpow_iff_form (x := x) (t := t) (p := q.num) (n := q.den) q.den_pos hx
    rwa [Rat.num_div_den q] at h0
  have h' : (t = 0 ∨ ∃ w : M, w ≠ 0 ∧ w ^ 2 = t) ↔
      (t = 0 ∨ ∃ w : M, w ≠ 0 ∧ w * w = t) := by
    simp only [pow_two]
  rw [rpowRel_realize]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [h, h']
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ## 3. The atoms lifted to a context, with positivity hypotheses -/

/-- The lifted `approxAtom`: with `t₁, t₂ ≥ 0` it is `|y₂| t₁ ≤ N (|y₁| t₂)`. -/
theorem approxAtom_lift2 {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) {Ctx : Type}
    (N : ℕ) (y₁ y₂ t₁ t₂ : Ctx)
    (rw : Ctx → M) (h1 : 0 ≤ rw t₁) (h2 : 0 ≤ rw t₂) :
    (liftR ![y₁, y₂, t₁, t₂] (approxAtom N)).Realize rw ↔
      |rw y₂| * rw t₁ ≤ (N : M) * (|rw y₁| * rw t₂) := by
  have hh : rw ∘ ![y₁, y₂, t₁, t₂] = ![rw y₁, rw y₂, rw t₁, rw t₂] := by
    funext i; fin_cases i <;> rfl
  rw [liftR_realize, hh, approxAtom_realize hsq N _ h1 h2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

theorem ltNMul_lift {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) {Ctx : Type}
    (N : ℕ) (b x : Ctx) (rw : Ctx → M) :
    (liftR ![b, x] (ltNMul N)).Realize rw ↔ (N : M) * rw b < rw x := by
  have hh : rw ∘ ![b, x] = ![rw b, rw x] := by funext i; fin_cases i <;> rfl
  rw [liftR_realize, hh, ltNMul_realize hsq N]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! ## 4. Contexts and variable maps of the sentence -/

/-- The outer context: the family parameters `c`. -/
abbrev UC0 (k : ℕ) : Type := Empty ⊕ Fin k
/-- The parameter variable. -/
def ucC {k : ℕ} (j : Fin k) : UC0 k := Sum.inr j

/-- The graph-condition context: parameters and the three variables `x, y, y'`. -/
abbrev UCG (k : ℕ) : Type := UC0 k ⊕ Fin 3
def ucgC {k : ℕ} (j : Fin k) : UCG k := Sum.inl (ucC j)
def ucgX {k : ℕ} : UCG k := Sum.inr 0
def ucgY {k : ℕ} : UCG k := Sum.inr 1
def ucgY' {k : ℕ} : UCG k := Sum.inr 2

/-- The cardinality context: parameters and the `(N+1)`-tuple of candidate breakpoints. -/
abbrev UCT (k N : ℕ) : Type := UC0 k ⊕ Fin (N + 1)
def uctC {k N : ℕ} (j : Fin k) : UCT k N := Sum.inl (ucC j)
def uctT {k N : ℕ} (i : Fin (N + 1)) : UCT k N := Sum.inr i

/-- The cardinality context with a second `(N+1)`-block (the universally quantified index). -/
abbrev UCTI (k N : ℕ) : Type := UCT k N ⊕ Fin (N + 1)
def uctiC {k N : ℕ} (j : Fin k) : UCTI k N := Sum.inl (uctC j)
def uctiB {k N : ℕ} (i : Fin (N + 1)) : UCTI k N := Sum.inr i

/-- The context of the `x₁, x₂` clause. -/
abbrev UCP (k : ℕ) : Type := UC0 k ⊕ Fin 2
def ucpC {k : ℕ} (j : Fin k) : UCP k := Sum.inl (ucC j)
def ucpX1 {k : ℕ} : UCP k := Sum.inr 0
def ucpX2 {k : ℕ} : UCP k := Sum.inr 1

/-- The context of the breakpoint clause (with the bound breakpoint `b`). -/
abbrev UCPB (k : ℕ) : Type := UCP k ⊕ Fin 1
def ucpbC {k : ℕ} (j : Fin k) : UCPB k := Sum.inl (ucpC j)
def ucpbX1 {k : ℕ} : UCPB k := Sum.inl ucpX1
def ucpbX2 {k : ℕ} : UCPB k := Sum.inl ucpX2
def ucpbB {k : ℕ} : UCPB k := Sum.inr 0

/-- The context of the "domain" clause (the bound witness `y`). -/
abbrev UCPD (k : ℕ) : Type := UCP k ⊕ Fin 1
def ucpdC {k : ℕ} (j : Fin k) : UCPD k := Sum.inl (ucpC j)
def ucpdX1 {k : ℕ} : UCPD k := Sum.inl ucpX1
def ucpdX2 {k : ℕ} : UCPD k := Sum.inl ucpX2
def ucpdY {k : ℕ} : UCPD k := Sum.inr 0

/-- The context of the approximation clause: `y₁, y₂` block. -/
abbrev UCPY (k : ℕ) : Type := UCP k ⊕ Fin 2
def ucpyC {k : ℕ} (j : Fin k) : UCPY k := Sum.inl (ucpC j)
def ucpyX1 {k : ℕ} : UCPY k := Sum.inl ucpX1
def ucpyX2 {k : ℕ} : UCPY k := Sum.inl ucpX2
def ucpyY1 {k : ℕ} : UCPY k := Sum.inr 0
def ucpyY2 {k : ℕ} : UCPY k := Sum.inr 1

/-- The context of the innermost body: `t₁, t₂` block. -/
abbrev UAPT (k : ℕ) : Type := UCPY k ⊕ Fin 2
def uaptC {k : ℕ} (j : Fin k) : UAPT k := Sum.inl (ucpyC j)
def uaptX1 {k : ℕ} : UAPT k := Sum.inl ucpyX1
def uaptX2 {k : ℕ} : UAPT k := Sum.inl ucpyX2
def uaptY1 {k : ℕ} : UAPT k := Sum.inl ucpyY1
def uaptY2 {k : ℕ} : UAPT k := Sum.inl ucpyY2
def uaptT1 {k : ℕ} : UAPT k := Sum.inr 0
def uaptT2 {k : ℕ} : UAPT k := Sum.inr 1

/-! ## 5. The sentence -/

/-- `φ` with the parameter block renamed along `cc` and the two coordinates `x, y`. -/
def uphiG {Ctx : Type} (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (cc : Fin k → Ctx)
    (xt yt : Ctx) : LRc.Formula Ctx :=
  Formula.relabel (Fin.cases xt (Fin.cases yt cc)) φ

/-- `ψ` with the parameter block renamed along `cc` and the breakpoint `b`. -/
def upsiG {Ctx : Type} (k : ℕ) (ψ : LRc.Formula (Fin (k + 1))) (cc : Fin k → Ctx)
    (bt : Ctx) : LRc.Formula Ctx :=
  Formula.relabel (Fin.cases bt cc) ψ

/-- The graph condition at one parameter value: `φ(x,y) → φ(x,y') → y = y'`. -/
def uGC (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) : LRc.Formula (UCG k) :=
  (uphiG k φ ucgC ucgX ucgY) ⟹
    ((uphiG k φ ucgC ucgX ucgY') ⟹ (liftR ![ucgY, ucgY'] eqAtom))

/-- The uniform graph condition. -/
def uGraphAll (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) : LRc.Formula (UC0 k) :=
  Formula.iAlls (Fin 3) (uGC k φ)

/-- The body of the cardinality clause: if all entries of the tuple lie in the `ψ`-fibre, two
of them coincide. -/
def ucardB (k N : ℕ) (ψ : LRc.Formula (Fin (k + 1))) : LRc.Formula (UCT k N) :=
  (Formula.iInf (fun i : Fin (N + 1) => upsiG k ψ uctC (uctT i))) ⟹
    (Formula.iSup (fun pq : {pq : Fin (N + 1) × Fin (N + 1) // pq.1 < pq.2} =>
      liftR ![uctT pq.1.1, uctT pq.1.2] eqAtom))

/-- The cardinality clause "the `ψ`-fibre has at most `N` elements". -/
def ucard (k N : ℕ) (ψ : LRc.Formula (Fin (k + 1))) : LRc.Formula (UC0 k) :=
  Formula.iAlls (Fin (N + 1)) (ucardB k N ψ)

/-- The SameSide hypothesis at one breakpoint. -/
def ussB (k N : ℕ) (ψ : LRc.Formula (Fin (k + 1))) : LRc.Formula (UCPB k) :=
  (upsiG k ψ ucpbC ucpbB) ⟹
    (((liftR ![ucpbB, ucpbX1] (ltNMul N)) ⊓ (liftR ![ucpbB, ucpbX2] (ltNMul N))) ⊔
     ((liftR ![ucpbX1, ucpbB] (ltNMul N)) ⊓ (liftR ![ucpbX2, ucpbB] (ltNMul N))))

/-- The SameSide hypothesis: `x₁, x₂` lie on the same side of every breakpoint, factor `N`. -/
def ussHyp (k N : ℕ) (ψ : LRc.Formula (Fin (k + 1))) : LRc.Formula (UCP k) :=
  Formula.iAlls (Fin 1) (ussB k N ψ)

/-- `∃ y, φ(x₁, y)`. -/
def uexistsY1 (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) : LRc.Formula (UCP k) :=
  Formula.iExs (Fin 1) (uphiG k φ ucpdC ucpdX1 ucpdY)

/-- `∃ y, φ(x₂, y)`. -/
def uexistsY2 (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) : LRc.Formula (UCP k) :=
  Formula.iExs (Fin 1) (uphiG k φ ucpdC ucpdX2 ucpdY)

/-- The "domain status agrees" clause. -/
def udomIff (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) : LRc.Formula (UCP k) :=
  (uexistsY1 k φ ⟹ uexistsY2 k φ) ⊓ (uexistsY2 k φ ⟹ uexistsY1 k φ)

/-- The body of the approximation clause for the exponent `qs i`: the two `rpowRel` relations
and the two comparisons. -/
def uapproxB (k N : ℕ) {Nq : ℕ} (qs : Fin Nq → ℚ)
    (i : Fin Nq) : LRc.Formula (UAPT k) :=
  (Formula.relabel ![uaptX1, uaptT1] (rpowRel (qs i).num (qs i).den)) ⊓
    ((Formula.relabel ![uaptX2, uaptT2] (rpowRel (qs i).num (qs i).den)) ⊓
      ((liftR ![uaptY1, uaptY2, uaptT1, uaptT2] (approxAtom N)) ⊓
       (liftR ![uaptY2, uaptY1, uaptT2, uaptT1] (approxAtom N))))

/-- The approximation clause: for `y₁` over `x₁` and `y₂` over `x₂` there is an exponent in the
list and witnesses `t₁, t₂` with the comparison. -/
def uapprox (k N : ℕ) {Nq : ℕ} (φ : LRc.Formula (Fin (k + 2))) (qs : Fin Nq → ℚ) :
    LRc.Formula (UCP k) :=
  Formula.iAlls (Fin 2) ((uphiG k φ ucpyC ucpyX1 ucpyY1) ⟹
    ((uphiG k φ ucpyC ucpyX2 ucpyY2) ⟹
      (Formula.iSup (fun i : Fin Nq =>
        Formula.iExs (Fin 2) (uapproxB k N qs i)))))

/-- The `∀ x₁ x₂` clause. -/
def uconclB (k N : ℕ) {Nq : ℕ} (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1)))
    (qs : Fin Nq → ℚ) : LRc.Formula (UCP k) :=
  (liftR ![ucpX1] posStrictAtom) ⟹
    ((liftR ![ucpX2] posStrictAtom) ⟹
      ((ussHyp k N ψ) ⟹ ((udomIff k φ) ⊓ (uapprox k N φ qs))))

/-- The `∀ x₁ x₂` clause, quantified. -/
def uconcl (k N : ℕ) {Nq : ℕ} (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1)))
    (qs : Fin Nq → ℚ) : LRc.Formula (UC0 k) :=
  Formula.iAlls (Fin 2) (uconclB k N φ ψ qs)

/-- The body of the ULPM sentence: the cardinality clause and the `x₁, x₂` clause. -/
def uBody (k N : ℕ) {Nq : ℕ} (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1)))
    (qs : Fin Nq → ℚ) : LRc.Formula (UC0 k) :=
  (ucard k N ψ) ⊓ (uconcl k N φ ψ qs)

/-- **The ULPM sentence** for the formula `φ` (the family), the formula `ψ` (the breakpoint set),
the constant `N` and the list `qs` of exponents. -/
def ulpmSent (k N Nq : ℕ) (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1)))
    (qs : Fin Nq → ℚ) : LRc.Sentence :=
  (Formula.iAlls (Fin k) (uGraphAll k φ)) ⟹ (Formula.iAlls (Fin k) (uBody k N φ ψ qs))

/-! ## 6. The clean semantics -/

/-- `φ(x, y)` with the parameters `cc`. -/
def uphiVal (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (M : Type) [LRc.Structure M]
    (cc : Fin k → M) (x y : M) : Prop :=
  φ.Realize (Fin.cases x (Fin.cases y cc))

/-- `ψ(b)` with the parameters `cc`. -/
def upsiVal (k : ℕ) (ψ : LRc.Formula (Fin (k + 1))) (M : Type) [LRc.Structure M]
    (cc : Fin k → M) (b : M) : Prop :=
  ψ.Realize (Fin.cases b cc)

/-- **The clean semantic content of `ulpmSent`.**  For every parameter value whose fibre is a
graph, the `ψ`-fibre has at most `N` breakpoints and any two positive points on the same side of
all of them have the same domain status and satisfy the monomial comparison with some exponent
from the list `qs`. -/
def ULPMGood (k N Nq : ℕ) (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1)))
    (qs : Fin Nq → ℚ) (M : Type) [LRc.Structure M] [Field M] [LinearOrder M] : Prop :=
  (∀ (c : Fin k → M) (x y y' : M), uphiVal k φ M c x y → uphiVal k φ M c x y' → y = y') →
  ∀ c : Fin k → M,
    {x : M | upsiVal k ψ M c x}.encard ≤ N ∧
    ∀ x₁ x₂ : M, 0 < x₁ → 0 < x₂ →
      (∀ b : M, upsiVal k ψ M c b → ((N : M) * b < x₁ ∧ (N : M) * b < x₂) ∨
        ((N : M) * x₁ < b ∧ (N : M) * x₂ < b)) →
      ((∃ y, uphiVal k φ M c x₁ y) ↔ (∃ y, uphiVal k φ M c x₂ y)) ∧
      ∀ y₁ y₂ : M, uphiVal k φ M c x₁ y₁ → uphiVal k φ M c x₂ y₂ →
        ∃ i : Fin Nq, ∃ t₁ t₂ : M, IsRpow x₁ (qs i) t₁ ∧ IsRpow x₂ (qs i) t₂ ∧
          |y₂| * t₁ ≤ (N : M) * (|y₁| * t₂) ∧ |y₁| * t₂ ≤ (N : M) * (|y₂| * t₁)

end Work.WilC4
