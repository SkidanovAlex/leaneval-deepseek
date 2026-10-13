/-
  Area C2 (WilC2): `comp X u` is definable over the parameters of `X` together with `u`.

  The definition of `comp X u` (see `CutDefs.lean`) is already a first-order statement with an
  unbounded universal quantifier on either side of `u`, so it can be transcribed directly into an
  `LRc`-formula with parameters in `A ∪ {u}`, provided only that the strict order of a model of `TR`
  is expressible by a ring formula: every nonnegative element of a model of `TR` is a square
  (`Work.WilC2.model_exists_sq`), so `x ≤ y ↔ ∃ z, x + z * z = y` is the ring formula `leF`.

  Concretely, given `φ : LRc.Formula (↥A ⊕ Fin 1)` defining `X` over `A`, the formula

  ```
  φ(x) ∧ ∀ z ((x ≤ z ∧ z ≤ u) → φ(z)) ∧ ∀ z ((u ≤ z ∧ z ≤ x) → φ(z))
  ```

  (with `u` used as a further parameter) defines `comp X u`.  The construction below keeps the
  index types explicit: parameters live in `↥(A ∪ {u})`, the point variable is `ccPt`, the extra
  parameter is `ccPu`, and the bound variable of each universal block is `ccZ`.

  The file mirrors the shape of `Submission/Work/WilC2/definable_maxSet_supSet.lean`.
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

/-! ## The index type and its distinguished variables -/

/-- Index type for the `comp`-formula: the parameters `A ∪ {u}` and the point variable. -/
abbrev ccIdx {M : Type*} (A : Set M) (u : M) := ↥(A ∪ {u}) ⊕ Fin 1

/-- The parameter `a ∈ A` inside `ccIdx A u`. -/
def ccPar {M : Type*} {A : Set M} {u : M} (a : ↥A) : ccIdx A u :=
  Sum.inl ⟨(a : M), Or.inl a.2⟩

/-- The extra parameter `u` inside `ccIdx A u`. -/
def ccPu {M : Type*} {A : Set M} {u : M} : ccIdx A u := Sum.inl ⟨u, Or.inr rfl⟩

/-- The point variable inside `ccIdx A u`. -/
def ccPt {M : Type*} {A : Set M} {u : M} : ccIdx A u := Sum.inr 0

/-- The parameters of `A` inside `ccIdx A u`. -/
def ccEC {M : Type*} {A : Set M} {u : M} : ↥A → ccIdx A u := fun a => ccPar a

/-- The parameters of `A` inside `ccIdx A u ⊕ Fin 1`. -/
def ccEC1 {M : Type*} {A : Set M} {u : M} : ↥A → ccIdx A u ⊕ Fin 1 := fun a => Sum.inl (ccPar a)

/-- The bound variable of a universal block, inside `ccIdx A u ⊕ Fin 1`. -/
def ccZ {M : Type*} {A : Set M} {u : M} : ccIdx A u ⊕ Fin 1 := Sum.inr 0

/-! ## Reading a formula for `X` at a variable -/

/-- `ccXat e w φ` is the formula `φ`, with the parameters of `A` embedded by `e` and with its
point variable read at the variable `w`. -/
def ccXat {M : Type*} {A : Set M} {γ : Type*} (e : ↥A → γ) (w : γ)
    (φ : LRc.Formula (↥A ⊕ Fin 1)) : LRc.Formula γ :=
  φ.relabel (Sum.elim e (fun _ : Fin 1 => w))

theorem ccXat_realize {M : Type} [LRc.Structure M] {A : Set M} {X : Set M} {γ : Type*}
    (e : ↥A → γ) (w : γ) (φ : LRc.Formula (↥A ⊕ Fin 1))
    (hφ : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X)
    (σ : γ → M) (hσ : ∀ a : ↥A, σ (e a) = (a : M)) :
    (ccXat e w φ).Realize σ ↔ σ w ∈ X := by
  rw [ccXat, Formula.realize_relabel]
  have hv : σ ∘ Sum.elim e (fun _ : Fin 1 => w) =
      Sum.elim (Subtype.val) (fun _ : Fin 1 => σ w) := by
    funext b
    rcases b with a | k
    · simp only [Function.comp_apply, Sum.elim_inl]
      exact hσ a
    · simp only [Function.comp_apply, Sum.elim_inr]
  rw [hv]
  exact hφ (fun _ : Fin 1 => σ w)

/-! ## The order formula -/

/-- `liftR ![i, j] leF`, realised as `τ i ≤ τ j`. -/
theorem ccLeF_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {γ : Type*} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (i j : γ) (τ : γ → M) :
    (liftR ![i, j] leF).Realize τ ↔ τ i ≤ τ j := by
  rw [liftR_realize]
  have hv : τ ∘ ![i, j] = ![τ i, τ j] := by funext k; fin_cases k <;> rfl
  rw [hv, leF_realize_le hsq]

/-! ## The two universal blocks and the formula for `comp X u` -/

/-- The block `∀ z, (x ≤ z ∧ z ≤ u) → z ∈ X`. -/
def ccBody2 {M : Type*} {A : Set M} {u : M} (φ : LRc.Formula (↥A ⊕ Fin 1)) :
    LRc.Formula (ccIdx A u ⊕ Fin 1) :=
  (liftR ![Sum.inl (ccPt (A := A) (u := u)), ccZ (A := A) (u := u)] leF ⊓
      liftR ![ccZ (A := A) (u := u), Sum.inl (ccPu (A := A) (u := u))] leF) ⟹
    ccXat (ccEC1 (A := A) (u := u)) (ccZ (A := A) (u := u)) φ

/-- The block `∀ z, (u ≤ z ∧ z ≤ x) → z ∈ X`. -/
def ccBody3 {M : Type*} {A : Set M} {u : M} (φ : LRc.Formula (↥A ⊕ Fin 1)) :
    LRc.Formula (ccIdx A u ⊕ Fin 1) :=
  (liftR ![Sum.inl (ccPu (A := A) (u := u)), ccZ (A := A) (u := u)] leF ⊓
      liftR ![ccZ (A := A) (u := u), Sum.inl (ccPt (A := A) (u := u))] leF) ⟹
    ccXat (ccEC1 (A := A) (u := u)) (ccZ (A := A) (u := u)) φ

/-- `comp X u`, as a formula over the parameters `A ∪ {u}`. -/
def ccForm {M : Type*} {A : Set M} {u : M} (φ : LRc.Formula (↥A ⊕ Fin 1)) :
    LRc.Formula (ccIdx A u) :=
  ccXat (ccEC (A := A) (u := u)) (ccPt (A := A) (u := u)) φ ⊓
    Formula.iAlls (Fin 1) (ccBody2 φ) ⊓ Formula.iAlls (Fin 1) (ccBody3 φ)

/-! ## Semantics of the blocks -/

theorem ccBody2_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {A : Set M} {X : Set M} {u : M} (φ : LRc.Formula (↥A ⊕ Fin 1))
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hφ : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X)
    (σ : ccIdx A u → M) (hσ : ∀ a : ↥(A ∪ {u}), σ (Sum.inl a) = (a : M))
    (z : Fin 1 → M) :
    (ccBody2 φ).Realize (Sum.elim σ z) ↔ (σ ccPt ≤ z 0 ∧ z 0 ≤ σ ccPu → z 0 ∈ X) := by
  have hσ' : ∀ a : ↥A, (Sum.elim σ z) (ccEC1 (A := A) (u := u) a) = (a : M) := by
    intro a
    simp only [ccEC1, ccPar, Sum.elim_inl]
    exact hσ ⟨(a : M), Or.inl a.2⟩
  have h1 : (liftR ![Sum.inl (ccPt (A := A) (u := u)), ccZ (A := A) (u := u)] leF).Realize
      (Sum.elim σ z) ↔ σ ccPt ≤ z 0 := ccLeF_realize hsq _ _ _
  have h2 : (liftR ![ccZ (A := A) (u := u), Sum.inl (ccPu (A := A) (u := u))] leF).Realize
      (Sum.elim σ z) ↔ z 0 ≤ σ ccPu := ccLeF_realize hsq _ _ _
  have h3 : (ccXat (ccEC1 (A := A) (u := u)) (ccZ (A := A) (u := u)) φ).Realize
      (Sum.elim σ z) ↔ z 0 ∈ X := ccXat_realize _ _ _ hφ _ hσ'
  simp only [ccBody2, Formula.realize_imp, Formula.realize_inf, h1, h2, h3]

theorem ccBody3_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {A : Set M} {X : Set M} {u : M} (φ : LRc.Formula (↥A ⊕ Fin 1))
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hφ : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X)
    (σ : ccIdx A u → M) (hσ : ∀ a : ↥(A ∪ {u}), σ (Sum.inl a) = (a : M))
    (z : Fin 1 → M) :
    (ccBody3 φ).Realize (Sum.elim σ z) ↔ (σ ccPu ≤ z 0 ∧ z 0 ≤ σ ccPt → z 0 ∈ X) := by
  have hσ' : ∀ a : ↥A, (Sum.elim σ z) (ccEC1 (A := A) (u := u) a) = (a : M) := by
    intro a
    simp only [ccEC1, ccPar, Sum.elim_inl]
    exact hσ ⟨(a : M), Or.inl a.2⟩
  have h1 : (liftR ![Sum.inl (ccPu (A := A) (u := u)), ccZ (A := A) (u := u)] leF).Realize
      (Sum.elim σ z) ↔ σ ccPu ≤ z 0 := ccLeF_realize hsq _ _ _
  have h2 : (liftR ![ccZ (A := A) (u := u), Sum.inl (ccPt (A := A) (u := u))] leF).Realize
      (Sum.elim σ z) ↔ z 0 ≤ σ ccPt := ccLeF_realize hsq _ _ _
  have h3 : (ccXat (ccEC1 (A := A) (u := u)) (ccZ (A := A) (u := u)) φ).Realize
      (Sum.elim σ z) ↔ z 0 ∈ X := ccXat_realize _ _ _ hφ _ hσ'
  simp only [ccBody3, Formula.realize_imp, Formula.realize_inf, h1, h2, h3]

/-! ## The main realisation theorem -/

theorem ccForm_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {A : Set M} {X : Set M} {u : M} (φ : LRc.Formula (↥A ⊕ Fin 1))
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hφ : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X)
    (v : Fin 1 → M) :
    (ccForm (A := A) (u := u) φ).Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ comp X u := by
  have hσ : ∀ a : ↥(A ∪ {u}), (Sum.elim Subtype.val v) (Sum.inl a) = (a : M) := fun _ => rfl
  have hpt : (ccXat (ccEC (A := A) (u := u)) (ccPt (A := A) (u := u)) φ).Realize
      (Sum.elim Subtype.val v) ↔ v 0 ∈ X :=
    ccXat_realize _ _ _ hφ _ (fun a => hσ ⟨(a : M), Or.inl a.2⟩)
  rw [ccForm, Formula.realize_inf, Formula.realize_inf, hpt, Formula.realize_iAlls,
    Formula.realize_iAlls, mem_comp]
  constructor
  · rintro ⟨⟨hX, h2⟩, h3⟩
    refine ⟨hX, ?_, ?_⟩
    · intro z h1 h1'
      exact (ccBody2_realize φ hsq hφ (Sum.elim Subtype.val v) hσ (fun _ : Fin 1 => z)).mp
        (h2 (fun _ => z)) ⟨h1, h1'⟩
    · intro z h1 h1'
      exact (ccBody3_realize φ hsq hφ (Sum.elim Subtype.val v) hσ (fun _ : Fin 1 => z)).mp
        (h3 (fun _ => z)) ⟨h1, h1'⟩
  · rintro ⟨hX, h2, h3⟩
    refine ⟨⟨hX, ?_⟩, ?_⟩
    · intro z
      exact (ccBody2_realize φ hsq hφ (Sum.elim Subtype.val v) hσ z).mpr
        (fun hcon => h2 (z 0) hcon.1 hcon.2)
    · intro z
      exact (ccBody3_realize φ hsq hφ (Sum.elim Subtype.val v) hσ z).mpr
        (fun hcon => h3 (z 0) hcon.1 hcon.2)

/-! ## The theorem -/

theorem definable_comp
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hM : M ⊨ WilkiesDesign.CG.TR) {A : Set M} {X : Set M} {u : M}
    (hX : A.Definable₁ WilkiesDesign.CG.LRc X) :
    (A ∪ {u}).Definable₁ WilkiesDesign.CG.LRc (Work.WilC2.comp X u) := by
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hX
  have hφ' : ∀ v : Fin 1 → M, φ.Realize (Sum.elim Subtype.val v) ↔ v 0 ∈ X :=
    fun v => (Set.ext_iff.mp hφ v).symm
  have hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq hM
  refine Set.definable_iff_exists_formula_sum.mpr ⟨ccForm φ, ?_⟩
  ext v
  exact (ccForm_realize φ hsq hφ' v).symm

end Work.WilC2
