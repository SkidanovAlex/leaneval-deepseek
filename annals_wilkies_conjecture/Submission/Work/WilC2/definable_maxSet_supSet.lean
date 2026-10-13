/-
  Area C2 (WilC2): `maxSet X` and `supSet X` are definable over the parameters of `X`.

  The point is that although `maxSet` and `supSet` are defined by unbounded universal
  quantifiers ("for every `y ∈ X` above `x` there is a gap"), first-order logic *does* have
  unbounded quantifiers, so the definitions can be transcribed directly into `LRc`-formulas
  with parameters, provided only that the strict order of the model is expressible: in a model
  `M ⊨ TR` every nonnegative element is a square (`Work.WilC2.model_exists_sq`), so
  `u ≤ v ↔ ∃ z, u + z * z = v` is a ring formula (`Work.WilC2.leF`), and
  `u < v ↔ u ≤ v ∧ u ≠ v` (`ltF` below).

  The formulas are built in the `Formula (↥A ⊕ Fin 1)` style of `Basic.lean`: free variables are
  the parameters together with the point variable.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC2.CutDefs
import Submission.Work.WilC2.Square

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-! ## The strict-order formula -/

namespace MaxSupDef

/-- `ltF i j` is the `LRc`-formula `v i < v j`, i.e. `v i ≤ v j` and `v i ≠ v j`. -/
def ltF {α : Type*} (i j : α) : LRc.Formula α :=
  liftR ![i, j] leF ⊓ ∼(Term.equal (Term.var i) (Term.var j))

theorem ltF_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) {α : Type*} (i j : α) (v : α → M) :
    (ltF i j).Realize v ↔ v i < v j := by
  have hv : v ∘ ![i, j] = ![v i, v j] := by
    funext k
    fin_cases k <;> rfl
  rw [ltF, Formula.realize_inf, Formula.realize_not, Formula.realize_equal, liftR_realize,
    hv, leF_realize_le hsq]
  simp only [Term.realize_var]
  exact ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨le_of_lt h, ne_of_lt h⟩⟩

/-! ## The `maxSet` formula -/

/-- Index type for the `maxSet` formula: the parameters and the point, the candidate `y`, and the
witness `z`. -/
abbrev QIdx {M : Type*} (A : Set M) := ((↥A ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1

/-- The parameter variables inside `QIdx A`. -/
def parQ {M : Type*} {A : Set M} (a : ↥A) : QIdx A := Sum.inl (Sum.inl (Sum.inl a))

/-- The point variable inside `QIdx A`. -/
def ptQ {M : Type*} {A : Set M} : QIdx A := Sum.inl (Sum.inl (Sum.inr 0))

/-- The `y`-variable inside `QIdx A`. -/
def yQ {M : Type*} {A : Set M} : QIdx A := Sum.inl (Sum.inr 0)

/-- The `z`-variable inside `QIdx A`. -/
def zQ {M : Type*} {A : Set M} : QIdx A := Sum.inr 0

/-- Relabelling `↥A ⊕ Fin 1` into `QIdx A` that sends the point variable to `y`. -/
def toQy {M : Type*} {A : Set M} : (↥A ⊕ Fin 1) → QIdx A
  | Sum.inl a => parQ a
  | Sum.inr _ => yQ

/-- Relabelling `↥A ⊕ Fin 1` into `QIdx A` that sends the point variable to `z`. -/
def toQz {M : Type*} {A : Set M} : (↥A ⊕ Fin 1) → QIdx A
  | Sum.inl a => parQ a
  | Sum.inr _ => zQ

/-- The `z`-variable of the `∀z ∃y` block of the `supSet` formula (inside `QIdx A`): the middle
quantifier block. -/
def zS {M : Type*} {A : Set M} : QIdx A := Sum.inl (Sum.inr 0)

/-- The `y`-variable of the `∀z ∃y` block of the `supSet` formula (inside `QIdx A`): the last
quantifier block. -/
def yS {M : Type*} {A : Set M} : QIdx A := Sum.inr 0

/-- The assignment of `QIdx A` produced by the parameter-point function `v` and the two functions
`i` (for `y`) and `j` (for `z`). -/
def asgQ {M : Type*} {A : Set M} (v i j : Fin 1 → M) : QIdx A → M :=
  Sum.elim (Sum.elim (Sum.elim Subtype.val v) i) j

@[simp] theorem asgQ_parQ {M : Type*} {A : Set M} (v i j : Fin 1 → M) (a : ↥A) :
    asgQ v i j (parQ a) = (a : M) := rfl

@[simp] theorem asgQ_ptQ {M : Type*} {A : Set M} (v i j : Fin 1 → M) :
    asgQ v i j (ptQ : QIdx A) = v 0 := rfl

@[simp] theorem asgQ_yQ {M : Type*} {A : Set M} (v i j : Fin 1 → M) :
    asgQ v i j (yQ : QIdx A) = i 0 := rfl

@[simp] theorem asgQ_zQ {M : Type*} {A : Set M} (v i j : Fin 1 → M) :
    asgQ v i j (zQ : QIdx A) = j 0 := rfl

@[simp] theorem asgQ_zS {M : Type*} {A : Set M} (v i j : Fin 1 → M) :
    asgQ v i j (zS : QIdx A) = i 0 := rfl

@[simp] theorem asgQ_yS {M : Type*} {A : Set M} (v i j : Fin 1 → M) :
    asgQ v i j (yS : QIdx A) = j 0 := rfl

theorem asgQ_comp_toQy {M : Type*} {A : Set M} (v i j : Fin 1 → M) :
    asgQ (A := A) v i j ∘ toQy = Sum.elim Subtype.val (fun _ : Fin 1 => i 0) := by
  funext a
  rcases a with a | k <;> rfl

theorem asgQ_comp_toQz {M : Type*} {A : Set M} (v i j : Fin 1 → M) :
    asgQ (A := A) v i j ∘ toQz = Sum.elim Subtype.val (fun _ : Fin 1 => j 0) := by
  funext a
  rcases a with a | k <;> rfl

/-- The body of the `maxSet` formula: `φ(y) ∧ x < y ⟹ (x < z ∧ (z < y ∧ ¬φ(z)))`. -/
def maxBody {M : Type*} {A : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1)) : LRc.Formula (QIdx A) :=
  (φ.relabel toQy ⊓ ltF (ptQ : QIdx A) yQ) ⟹
    (ltF (ptQ : QIdx A) zQ ⊓ (ltF (zQ : QIdx A) yQ ⊓ ∼(φ.relabel toQz)))

/-- `maxSet X` as a formula, given a formula `φ` defining `X` over the parameters.  Semantics
(`maxForm_realize`): the formula is `φ(x) ∧ ∀ y (φ(y) ∧ x < y ⟹ ∃ z (x < z ∧ z < y ∧ ¬φ(z)))`,
i.e. exactly the definition of `maxSet`. -/
def maxForm {M : Type*} {A : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1)) : LRc.Formula (↥A ⊕ Fin 1) :=
  φ ⊓ Formula.iAlls (Fin 1) (Formula.iExs (Fin 1) (maxBody φ))

theorem maxBody_realize_apply {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {A : Set M} {X : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1))
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hφ : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X)
    (v i j : Fin 1 → M) :
    (maxBody φ).Realize (asgQ v i j) ↔
      ((i 0 ∈ X ∧ v 0 < i 0) → (v 0 < j 0 ∧ j 0 < i 0 ∧ j 0 ∉ X)) := by
  simp only [maxBody, Formula.realize_imp, Formula.realize_inf, Formula.realize_not,
    Formula.realize_relabel, asgQ_comp_toQy, asgQ_comp_toQz, hφ, ltF_realize hsq,
    asgQ_ptQ, asgQ_yQ, asgQ_zQ]

theorem maxForm_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {A : Set M} {X : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1))
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hφ : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X)
    (v : Fin 1 → M) :
    (maxForm φ).Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ maxSet X := by
  rw [maxForm, Formula.realize_inf, Formula.realize_iAlls, hφ, mem_maxSet]
  constructor
  · rintro ⟨hvX, h⟩
    refine ⟨hvX, fun y hyX hvy => ?_⟩
    have h' : ∃ j : Fin 1 → M, (maxBody φ).Realize (asgQ v (fun _ => y) j) := by
      have hh := h (fun _ => y)
      rw [Formula.realize_iExs] at hh
      exact hh
    obtain ⟨j, hj⟩ := h'
    obtain ⟨h1, h2, h3⟩ :=
      (maxBody_realize_apply φ hsq hφ v (fun _ => y) j).mp hj ⟨hyX, hvy⟩
    exact ⟨j 0, h1, h2, h3⟩
  · rintro ⟨hvX, h⟩
    refine ⟨hvX, fun i => ?_⟩
    by_cases hc : i 0 ∈ X ∧ v 0 < i 0
    · obtain ⟨z, h1, h2, h3⟩ := h (i 0) hc.1 hc.2
      refine (Formula.realize_iExs).mpr ⟨fun _ => z, ?_⟩
      exact (maxBody_realize_apply φ hsq hφ v i (fun _ => z)).mpr (fun _ => ⟨h1, h2, h3⟩)
    · refine (Formula.realize_iExs).mpr ⟨fun _ => 0, ?_⟩
      exact (maxBody_realize_apply φ hsq hφ v i (fun _ => 0)).mpr (fun hcon => absurd hcon hc)

/-! ## The `supSet` formula -/

/-- Index type for the `∃ y` block of the `supSet` formula. -/
abbrev PIdx {M : Type*} (A : Set M) := (↥A ⊕ Fin 1) ⊕ Fin 1

/-- The parameter variables inside `PIdx A`. -/
def parP {M : Type*} {A : Set M} (a : ↥A) : PIdx A := Sum.inl (Sum.inl a)

/-- The point variable inside `PIdx A`. -/
def xP {M : Type*} {A : Set M} : PIdx A := Sum.inl (Sum.inr 0)

/-- The `y`-variable inside `PIdx A`. -/
def yP {M : Type*} {A : Set M} : PIdx A := Sum.inr 0

/-- Relabelling `↥A ⊕ Fin 1` into `PIdx A` that sends the point variable to `y`. -/
def toPy {M : Type*} {A : Set M} : (↥A ⊕ Fin 1) → PIdx A
  | Sum.inl a => parP a
  | Sum.inr _ => yP

/-- The assignment of `PIdx A` produced by the parameter-point function `v` and the `y`-function
`i`. -/
def asgP {M : Type*} {A : Set M} (v i : Fin 1 → M) : PIdx A → M :=
  Sum.elim (Sum.elim Subtype.val v) i

@[simp] theorem asgP_parP {M : Type*} {A : Set M} (v i : Fin 1 → M) (a : ↥A) :
    asgP v i (parP a) = (a : M) := rfl

@[simp] theorem asgP_xP {M : Type*} {A : Set M} (v i : Fin 1 → M) :
    asgP v i (xP : PIdx A) = v 0 := rfl

@[simp] theorem asgP_yP {M : Type*} {A : Set M} (v i : Fin 1 → M) :
    asgP v i (yP : PIdx A) = i 0 := rfl

theorem asgP_comp_toPy {M : Type*} {A : Set M} (v i : Fin 1 → M) :
    asgP (A := A) v i ∘ toPy = Sum.elim Subtype.val (fun _ : Fin 1 => i 0) := by
  funext a
  rcases a with a | k <;> rfl

/-- The `∃ y` block of the `supSet` formula: `y ∈ X ∧ y < x`. -/
def supBody1 {M : Type*} {A : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1)) : LRc.Formula (PIdx A) :=
  φ.relabel toPy ⊓ ltF (yP : PIdx A) xP

/-- The `∀ z ∃ y` block of the `supSet` formula: `z < x ⟹ (y ∈ X ∧ z < y ∧ y < x)`.
The universal variable `z` is the middle quantifier block, the existential variable `y` the
last one. -/
def supBody2 {M : Type*} {A : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1)) : LRc.Formula (QIdx A) :=
  ltF (zS : QIdx A) ptQ ⟹
    (φ.relabel toQz ⊓ (ltF (zS : QIdx A) yS ⊓ ltF (yS : QIdx A) ptQ))

/-- `supSet X` as a formula, given a formula `φ` defining `X` over the parameters.  Semantics
(`supForm_realize`): the formula is
`¬φ(x) ∧ (∃ y (φ(y) ∧ y < x)) ∧ (∀ z (z < x ⟹ ∃ y (φ(y) ∧ z < y ∧ y < x)))`,
i.e. exactly the definition of `supSet`. -/
def supForm {M : Type*} {A : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1)) : LRc.Formula (↥A ⊕ Fin 1) :=
  ∼φ ⊓ Formula.iExs (Fin 1) (supBody1 φ) ⊓
    Formula.iAlls (Fin 1) (Formula.iExs (Fin 1) (supBody2 φ))

theorem supBody1_realize_apply {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {A : Set M} {X : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1))
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hφ : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X)
    (v i : Fin 1 → M) :
    (supBody1 φ).Realize (asgP v i) ↔ (i 0 ∈ X ∧ i 0 < v 0) := by
  simp only [supBody1, Formula.realize_inf, Formula.realize_relabel, asgP_comp_toPy, hφ,
    ltF_realize hsq, asgP_xP, asgP_yP]

theorem supBody2_realize_apply {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {A : Set M} {X : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1))
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hφ : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X)
    (v i j : Fin 1 → M) :
    (supBody2 φ).Realize (asgQ v i j) ↔ (i 0 < v 0 → (j 0 ∈ X ∧ i 0 < j 0 ∧ j 0 < v 0)) := by
  simp only [supBody2, Formula.realize_imp, Formula.realize_inf, Formula.realize_relabel,
    asgQ_comp_toQz, hφ, ltF_realize hsq, asgQ_ptQ, asgQ_zS, asgQ_yS]

theorem supForm_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {A : Set M} {X : Set M} (φ : LRc.Formula (↥A ⊕ Fin 1))
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hφ : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X)
    (v : Fin 1 → M) :
    (supForm φ).Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ supSet X := by
  rw [supForm, Formula.realize_inf, Formula.realize_inf, Formula.realize_iExs,
    Formula.realize_iAlls, Formula.realize_not, hφ, mem_supSet]
  constructor
  · rintro ⟨⟨hvX, hex⟩, hall⟩
    obtain ⟨i, hi⟩ := hex
    obtain ⟨hiX, hiv⟩ := (supBody1_realize_apply φ hsq hφ v i).mp hi
    refine ⟨hvX, ⟨i 0, hiX, hiv⟩, fun z hzv => ?_⟩
    have hz := hall (fun _ => z)
    rw [Formula.realize_iExs] at hz
    obtain ⟨j, hj⟩ := hz
    obtain ⟨hjX, hzj, hjv⟩ :=
      (supBody2_realize_apply φ hsq hφ v (fun _ => z) j).mp hj hzv
    exact ⟨j 0, hjX, hzj, hjv⟩
  · rintro ⟨hvX, ⟨y, hyX, hyv⟩, hall⟩
    refine ⟨⟨hvX, ⟨fun _ => y, ?_⟩⟩, fun i => ?_⟩
    · exact (supBody1_realize_apply φ hsq hφ v (fun _ => y)).mpr ⟨hyX, hyv⟩
    · by_cases hc : i 0 < v 0
      · obtain ⟨y', hy'X, hiy', hy'v⟩ := hall (i 0) hc
        refine (Formula.realize_iExs).mpr ⟨fun _ => y', ?_⟩
        exact (supBody2_realize_apply φ hsq hφ v i (fun _ => y')).mpr
          (fun _ => ⟨hy'X, hiy', hy'v⟩)
      · refine (Formula.realize_iExs).mpr ⟨fun _ => 0, ?_⟩
        exact (supBody2_realize_apply φ hsq hφ v i (fun _ => 0)).mpr
          (fun hcv => absurd hcv hc)

/-! ## The main theorem -/

end MaxSupDef

theorem definable_maxSet_supSet
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hM : M ⊨ WilkiesDesign.CG.TR) {A : Set M} {X : Set M}
    (hX : A.Definable₁ WilkiesDesign.CG.LRc X) :
    A.Definable₁ WilkiesDesign.CG.LRc (Work.WilC2.maxSet X) ∧
      A.Definable₁ WilkiesDesign.CG.LRc (Work.WilC2.supSet X) := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hX
  have hφ' : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X :=
    fun v => (Set.ext_iff.mp hφ v).symm
  have hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq hM
  constructor
  · refine Set.definable_iff_exists_formula_sum.mpr ⟨MaxSupDef.maxForm φ, ?_⟩
    ext v
    exact (MaxSupDef.maxForm_realize φ hsq hφ' v).symm
  · refine Set.definable_iff_exists_formula_sum.mpr ⟨MaxSupDef.supForm φ, ?_⟩
    ext v
    exact (MaxSupDef.supForm_realize φ hsq hφ' v).symm

end Work.WilC2
