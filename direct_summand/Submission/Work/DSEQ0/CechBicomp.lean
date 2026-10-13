import Mathlib
import Submission.Work.DSMap.Map

/-!
# The bicomplex comparing two Čech complexes

For a scheme `X`, a morphism `f : X ⟶ Spec A`, and two families of opens
`U : ι → X.Opens`, `V : κ → X.Opens`, this file builds the (first-quadrant) bicomplex

`C^{p,q} = ∏_{x : Fin (p+1) → ι} ∏_{y : Fin (q+1) → κ} Γ(X, (⨅_a U (x a)) ⊓ (⨅_b V (y b)))`

together with its total complex `Tot`, as the first step of the double-complex comparison of the
Čech complexes `DSMap.cechZ A X f U` and `DSMap.cechZ A X f V`.

The bicomplex is obtained by applying `cechComplexFunctor U` to the *presheaf of complexes*
`Q : X.Opensᵒᵖ ⥤ CochainComplex (ModuleCat A) ℕ`, `Q W = ` the Čech complex of the family `V`
with coefficients `W' ↦ Γ(X, W ⊓ W')`.  All the signs of the total complex are those of
Mathlib's `HomologicalComplex₂.total`.
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

/-- The total complex shape for the first-quadrant bicomplex `ℕ × ℕ → ℕ`, `(p, q) ↦ p + q`,
with the horizontal sign `1` and the vertical sign `(-1)^p`. -/
noncomputable instance totalComplexShapeUpNat : TotalComplexShape (ComplexShape.up ℕ)
    (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  π := fun pq => pq.1 + pq.2
  ε₁ := fun _ => 1
  ε₂ := fun pq => ((pq.1 : ℕ) : ℤ).negOnePow
  rel₁ := by
    intro i₁ i₁' h i₂
    have hh : i₁ + 1 = i₁' := h
    show i₁ + i₂ + 1 = i₁' + i₂
    omega
  rel₂ := by
    intro i₁ i₂ i₂' h
    have hh : i₂ + 1 = i₂' := h
    show i₁ + i₂ + 1 = i₁ + i₂'
    omega
  ε₂_ε₁ := by
    intro i₁ i₁' i₂ i₂' h₁ h₂
    have hh : i₁ + 1 = i₁' := h₁
    subst hh
    show ((i₁ : ℕ) : ℤ).negOnePow * 1 = -1 * (((i₁ + 1 : ℕ) : ℤ)).negOnePow
    rw [mul_one, Nat.cast_add, Nat.cast_one, Int.negOnePow_add, Int.negOnePow_one,
      mul_comm (-1 : ℤˣ), mul_assoc, Int.units_mul_self, mul_one]

/-- The symmetry of the total complex shape `(ℕ, ℕ) → ℕ`, with the Koszul sign `(-1)^{pq}`. -/
noncomputable instance totalComplexShapeSymmetryUpNat :
    TotalComplexShapeSymmetry (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  symm i₁ i₂ := Nat.add_comm i₂ i₁
  σ i₁ i₂ := ((i₁ : ℤ) * (i₂ : ℤ)).negOnePow
  σ_ε₁ := by
    intro i₁ i₁' h₁ i₂
    have hh : i₁ + 1 = i₁' := h₁
    subst hh
    show (((i₁ : ℤ) * (i₂ : ℤ))).negOnePow * 1
      = ((i₂ : ℤ)).negOnePow * ((((i₁ : ℤ) + 1) * (i₂ : ℤ))).negOnePow
    rw [mul_one, ← Int.negOnePow_add, add_comm (i₂ : ℤ), add_mul, one_mul, Int.negOnePow_add,
      Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
  σ_ε₂ := by
    intro i₁ i₂ i₂' h₂
    have hh : i₂ + 1 = i₂' := h₂
    subst hh
    show (((i₁ : ℤ) * (i₂ : ℤ))).negOnePow * ((i₁ : ℤ)).negOnePow
      = 1 * (((i₁ : ℤ) * ((i₂ : ℤ) + 1))).negOnePow
    rw [one_mul, ← Int.negOnePow_add, mul_add, mul_one]

variable {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
  (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))

/-- The `⊓`-bifunctor on the poset of opens of `X`, on opposite categories. -/
noncomputable def meetBif : (X.Opens)ᵒᵖ × (X.Opens)ᵒᵖ ⥤ (X.Opens)ᵒᵖ where
  obj pq := Opposite.op (pq.1.unop ⊓ pq.2.unop)
  map {pq pq'} hpq := (homOfLE (le_inf (le_trans inf_le_left (leOfHom hpq.1.unop))
    (le_trans inf_le_right (leOfHom hpq.2.unop)))).op
  map_id pq := Subsingleton.elim _ _
  map_comp a b := Subsingleton.elim _ _

/-- `cechPresheafBif` is the two-variable presheaf `(W, W') ↦ Γ(X, W ⊓ W')`, as a bifunctor. -/
noncomputable def cechPresheafBif :
    (X.Opens)ᵒᵖ × (X.Opens)ᵒᵖ ⥤ ModuleCat A :=
  meetBif ⋙ DSMap.cechPresheaf A X f

/-- The presheaf `W ↦ ((W' ↦ Γ(X, W ⊓ W')))`; `cechPresheafCurry.obj (op W)` is the
presheaf whose sections over `W'` are `Γ(X, W ⊓ W')`. -/
noncomputable def cechPresheafCurry :
    (X.Opens)ᵒᵖ ⥤ ((X.Opens)ᵒᵖ ⥤ ModuleCat A) :=
  Functor.curry.obj (cechPresheafBif f)

variable {κ : Type u} (V : κ → X.Opens)

/-- The presheaf of complexes `Q` on `X.Opens`: `Q W` is the Čech complex of the family `V` with
coefficients `W' ↦ Γ(X, W ⊓ W')`.  Its degree-`q` term is
`∏_{y : Fin (q+1) → κ} Γ(X, W ⊓ V (y 0) ⊓ ⋯ ⊓ V (y q))`. -/
noncomputable def cechShQC : (X.Opens)ᵒᵖ ⥤ CochainComplex (ModuleCat A) ℕ :=
  cechPresheafCurry f ⋙ CategoryTheory.cechComplexFunctor (C := X.Opens) (A := ModuleCat A) V

variable {ι : Type u} (U : ι → X.Opens)

/-- The Čech complex functor of the family `U`, with values in complexes of `A`-modules (so that
applying it to `cechShQC` produces the bicomplex `C^{p,q}`). -/
noncomputable def cechUComplex :
    ((X.Opens)ᵒᵖ ⥤ CochainComplex (ModuleCat A) ℕ) ⥤
      CochainComplex (CochainComplex (ModuleCat A) ℕ) ℕ :=
  CategoryTheory.cechComplexFunctor (C := X.Opens) (A := CochainComplex (ModuleCat A) ℕ) U

/-- The bicomplex `C^{p,q} = ∏_{x} ∏_{y} Γ(X, U_x ⊓ V_y)`. -/
noncomputable def cechBicomp :
    HomologicalComplex₂ (ModuleCat A) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (cechUComplex U).obj (cechShQC f V)

/-- The total complex of the bicomplex `cechBicomp`. -/
noncomputable def cechTot : CochainComplex (ModuleCat A) ℕ :=
  (cechBicomp f U V).total (ComplexShape.up ℕ)

/-- The `0`-th cycles of the columns of the bicomplex, as a cochain complex: this is the
"`q = 0` row" `∏_x ker (C^{x,0} → C^{x,1})`, equipped with the differential induced by the
horizontal (i.e. `U`-direction) differential of the bicomplex. -/
noncomputable def cechCycles : CochainComplex (ModuleCat A) ℕ :=
  ((HomologicalComplex.cyclesFunctor (ModuleCat A) (ComplexShape.up ℕ) 0).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (cechBicomp f U V)

end Work.DSEQ0
