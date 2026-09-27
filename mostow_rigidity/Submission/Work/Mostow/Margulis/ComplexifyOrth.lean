import Mathlib

/-!
# Complexification of a real inner product space

`V` is a finite-dimensional real inner product space.  We equip `V × V` with the structure of a
complex vector space (multiplication by `i` is `(x, y) ↦ (-y, x)`), and with the action of the
orthogonal group `V ≃ₗᵢ[ℝ] V` given by `p ↦ (p × p)`.  The point of the construction is that the
complexification of an orthogonal map is *semisimple* (its invariant subspaces have invariant
complements), which is what lets the virtual-abelianness induction run over `ℂ`.
-/

noncomputable section

open Complex

namespace Work.Mostow.Margulis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Complex scalar multiplication on `V × V`, i.e. the complexification of `V`. -/
def csmul (c : ℂ) (x : V × V) : V × V := (c.re • x.1 - c.im • x.2, c.im • x.1 + c.re • x.2)

instance instSMulComplexProd : SMul ℂ (V × V) := ⟨csmul⟩

instance instModuleComplexProd : Module ℂ (V × V) where
  one_smul x := by
    rw [show (1 : ℂ) • x = csmul 1 x from rfl, csmul, Complex.one_re, Complex.one_im]
    simp
  mul_smul a b x := by
    rw [show (a * b) • x = csmul (a * b) x from rfl, show b • x = csmul b x from rfl,
      show a • (csmul b x) = csmul a (csmul b x) from rfl]
    simp only [csmul, Complex.mul_re, Complex.mul_im, Prod.mk.injEq]
    constructor <;> simp only [smul_sub, smul_add] <;> module
  smul_zero c := by
    rw [show c • (0 : V × V) = csmul c 0 from rfl, csmul]
    simp
  smul_add c x y := by
    rw [show c • (x + y) = csmul c (x + y) from rfl, show c • x = csmul c x from rfl,
      show c • y = csmul c y from rfl]
    simp only [csmul, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> simp only [smul_add] <;> module
  add_smul a b x := by
    rw [show (a + b) • x = csmul (a + b) x from rfl, show a • x = csmul a x from rfl,
      show b • x = csmul b x from rfl]
    simp only [csmul, Complex.add_re, Complex.add_im, Prod.mk_add_mk, Prod.mk.injEq, add_smul]
    constructor <;> module
  zero_smul x := by
    rw [show (0 : ℂ) • x = csmul 0 x from rfl, csmul, Complex.zero_re, Complex.zero_im]
    simp

@[simp] lemma csmul_apply (c : ℂ) (x : V × V) :
    c • x = (c.re • x.1 - c.im • x.2, c.im • x.1 + c.re • x.2) := rfl

/-- The action of an orthogonal map on the complexification. -/
def cAct (p : V ≃ₗᵢ[ℝ] V) : (V × V) ≃ₗ[ℂ] (V × V) where
  toFun x := (p x.1, p x.2)
  invFun x := (p.symm x.1, p.symm x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [Prod.mk_add_mk]
  map_smul' c x := by
    simp only [RingHom.id_apply, csmul_apply, Prod.mk.injEq]
    constructor <;> simp

@[simp] lemma cAct_apply (p : V ≃ₗᵢ[ℝ] V) (x : V × V) : cAct p x = (p x.1, p x.2) := rfl

@[simp] lemma cAct_coe (p : V ≃ₗᵢ[ℝ] V) : (cAct p : V × V → V × V) = fun x => (p x.1, p x.2) := rfl

/-- The action of the orthogonal group on the complexification, as a monoid homomorphism. -/
def cActHom : (V ≃ₗᵢ[ℝ] V) →* ((V × V) ≃ₗ[ℂ] (V × V)) where
  toFun := cAct
  map_one' := by ext x <;> simp
  map_mul' p q := by ext x <;> simp

@[simp] lemma cActHom_apply (p : V ≃ₗᵢ[ℝ] V) : cActHom p = cAct p := rfl

end Work.Mostow.Margulis

namespace Work.Mostow.Margulis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

instance instIsScalarTowerComplexProd : IsScalarTower ℝ ℂ (V × V) where
  smul_assoc r c x := by
    obtain ⟨u, w⟩ := x
    rw [show (r • c) • (u, w) = csmul (r • c) (u, w) from rfl,
        show c • (u, w) = csmul c (u, w) from rfl]
    simp only [csmul, Algebra.smul_def, Prod.smul_mk]
    simp only [Complex.coe_algebraMap, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, zero_add, smul_sub, smul_add]
    refine Prod.ext ?_ ?_ <;> module

instance instModuleFiniteComplexProd : Module.Finite ℂ (V × V) := by
  have hR : Module.Finite ℝ (V × V) := Module.Finite.prod
  refine Module.Finite.of_fg_top ?_
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp hR.fg_top
  refine Submodule.fg_def.mpr ⟨S, hSfin, le_antisymm le_top ?_⟩
  have hle : (⊤ : Submodule ℝ (V × V)) ≤ Submodule.restrictScalars ℝ (Submodule.span ℂ S) := by
    rw [← hS]
    refine Submodule.span_le.mpr ?_
    intro y hy
    exact Submodule.subset_span hy
  intro x hx
  have hx' : x ∈ Submodule.restrictScalars ℝ (Submodule.span ℂ S) := hle hx
  exact hx'

end Work.Mostow.Margulis
