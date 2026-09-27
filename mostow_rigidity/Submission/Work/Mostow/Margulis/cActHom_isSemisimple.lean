import Mathlib
import Submission.Work.Mostow.Margulis.ComplexifyOrth

/-!
# The complexification of an orthogonal map is semisimple

Let `V` be a finite-dimensional real inner product space and let `p : V ≃ₗᵢ[ℝ] V` be a
linear isometry.  The complexification of `V` is modelled in `ComplexifyOrth` as `V × V`
with the `ℂ`-module structure `(a + bi) • (x, y) = (a • x - b • y, b • x + a • y)`, and `p`
acts on it through `cActHom p : (V × V) ≃ₗ[ℂ] (V × V)`.

The main result of this file is that this `ℂ`-linear map is **semisimple**, i.e. that the
`ℂ[X]`-module structure it induces on `V × V` is semisimple (every invariant subspace has an
invariant complement).

The proof runs as follows.  We put a Hermitian inner product `cForm` on `V × V` (the
complexification of the real inner product of `V`) and check that `cActHom p` is unitary for
it.  Writing `e` for the complexified isometry and `e'` for its inverse, the operators
`S = e + e'` and `T = i (e - e')` are self-adjoint (`LinearMap.IsSymmetric`), they commute,
and `e = (1/2) (S + (-i) T)`.  Self-adjoint endomorphisms of inner product spaces are
semisimple (`LinearMap.IsSymmetric.isFinitelySemisimple`), and semisimplicity is preserved by
sums of commuting semisimple operators (`Module.End.IsSemisimple.add_of_commute`), so `e` is
semisimple.
-/

noncomputable section

open Complex

namespace Work.Mostow.Margulis

set_option warn.classDefReducibility false

section Hermitian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The (positive definite, Hermitian) complex inner product on the complexification `V × V`
of a real inner product space, expressed in the real coordinates `x = (x₁, x₂)` as
`⟨x, y⟩ = ⟨x₁, y₁⟩ + ⟨x₂, y₂⟩ + i (⟨x₁, y₂⟩ - ⟨x₂, y₁⟩)`.

With the convention of Mathlib's `InnerProductSpace` (conjugate linear in the first
variable, linear in the second) this form satisfies `⟪c • x, y⟫ = conj c * ⟪x, y⟫`. -/
def cForm (x y : V × V) : ℂ :=
  ((inner ℝ x.1 y.1 + inner ℝ x.2 y.2 : ℝ) : ℂ) +
    Complex.I * ((inner ℝ x.1 y.2 - inner ℝ x.2 y.1 : ℝ) : ℂ)

@[simp] lemma cForm_apply (x y : V × V) :
    cForm x y = ((inner ℝ x.1 y.1 + inner ℝ x.2 y.2 : ℝ) : ℂ) +
      Complex.I * ((inner ℝ x.1 y.2 - inner ℝ x.2 y.1 : ℝ) : ℂ) := rfl

/-- The `ℂ`-inner product structure on the complexification. -/
def cInnerCore : InnerProductSpace.Core ℂ (V × V) where
  inner x y := cForm x y
  conj_inner_symm := by
    intro x y
    simp only [cForm, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [real_inner_comm (x := y.1) (y := x.1), real_inner_comm (x := y.2) (y := x.2),
      real_inner_comm (x := y.1) (y := x.2), real_inner_comm (x := y.2) (y := x.1)]
    push_cast
    ring
  re_inner_nonneg := by
    intro x
    have h : cForm x x = ((inner ℝ x.1 x.1 + inner ℝ x.2 x.2 : ℝ) : ℂ) := by
      simp only [cForm, real_inner_comm (x := x.2) (y := x.1), sub_self, Complex.ofReal_zero,
        mul_zero, add_zero]
    rw [h]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left := by
    intro x y z
    simp only [cForm, Prod.fst_add, Prod.snd_add, inner_add_left]
    push_cast
    ring
  smul_left := by
    intro x y r
    simp only [cForm, csmul_apply, inner_sub_left, inner_add_left, real_inner_smul_left]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;>
      ring
  definite := by
    intro x hx
    have h : cForm x x = ((inner ℝ x.1 x.1 + inner ℝ x.2 x.2 : ℝ) : ℂ) := by
      simp only [cForm, real_inner_comm (x := x.2) (y := x.1), sub_self, Complex.ofReal_zero,
        mul_zero, add_zero]
    rw [h] at hx
    have h1 : inner ℝ x.1 x.1 = 0 := by
      have := real_inner_self_nonneg (x := x.1)
      have := real_inner_self_nonneg (x := x.2)
      have hx' : inner ℝ x.1 x.1 + inner ℝ x.2 x.2 = 0 := by exact_mod_cast hx
      linarith
    have h2 : inner ℝ x.2 x.2 = 0 := by
      have := real_inner_self_nonneg (x := x.1)
      have := real_inner_self_nonneg (x := x.2)
      have hx' : inner ℝ x.1 x.1 + inner ℝ x.2 x.2 = 0 := by exact_mod_cast hx
      linarith
    exact Prod.ext (inner_self_eq_zero.mp h1) (inner_self_eq_zero.mp h2)

/-- The complexification `V × V` of a finite-dimensional real inner product space is
finite dimensional over `ℂ`. -/
lemma finiteDimensional_prod_complex : FiniteDimensional ℂ (V × V) := by
  haveI : IsScalarTower ℝ ℂ (V × V) := ⟨fun r c x => by
    simp only [csmul_apply, Prod.smul_mk, smul_sub, smul_add, smul_smul, Complex.smul_re,
      Complex.smul_im, smul_eq_mul]⟩
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ (V × V)

end Hermitian

section Instances

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

attribute [local instance] cInnerCore

/-- The `ℂ`-inner product of `cInnerCore` defines a norm on the complexification. -/
local instance instSeminormedProd : SeminormedAddCommGroup (V × V) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ) (F := V × V)

/-- ... which is a genuine norm. -/
local instance instNormedProd : NormedAddCommGroup (V × V) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (V × V) _ _ _ cInnerCore

/-- The complexification `V × V` as a complex inner product space. -/
local instance instInnerProductProd : InnerProductSpace ℂ (V × V) := InnerProductSpace.ofCore _

local instance instFiniteDimensionalProd : FiniteDimensional ℂ (V × V) :=
  finiteDimensional_prod_complex

theorem cActHom_isSemisimple {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (p : V ≃ₗᵢ[ℝ] V) : Module.End.IsSemisimple ((cActHom p : (V × V) ≃ₗ[ℂ] (V × V)) : Module.End ℂ (V × V)) := by
  -- the inner product really is `cForm`
  have hcF : ∀ x y : V × V, inner ℂ x y = cForm x y := fun x y => rfl
  -- `cAct p` is unitary
  have hunit : ∀ x y : V × V, inner ℂ (cAct p x) (cAct p y) = inner ℂ x y := by
    intro x y
    simp only [hcF, cForm_apply, cAct_apply]
    rw [LinearIsometryEquiv.inner_map_map p, LinearIsometryEquiv.inner_map_map p,
        LinearIsometryEquiv.inner_map_map p, LinearIsometryEquiv.inner_map_map p]
  -- the complexified isometry `e` and its inverse `e'`
  set e : Module.End ℂ (V × V) := (cAct p : (V × V) →ₗ[ℂ] (V × V)) with he
  set e' : Module.End ℂ (V × V) := ((cAct p).symm : (V × V) →ₗ[ℂ] (V × V)) with he'
  have hee' : e * e' = 1 := by
    rw [he, he']
    ext x : 1
    simp only [Module.End.mul_apply, Module.End.one_apply]
    change (cAct p) ((cAct p).symm x) = x
    exact LinearEquiv.apply_symm_apply _ _
  have he'e : e' * e = 1 := by
    rw [he, he']
    ext x : 1
    simp only [Module.End.mul_apply, Module.End.one_apply]
    change (cAct p).symm ((cAct p) x) = x
    exact LinearEquiv.symm_apply_apply _ _
  have hee'a : ∀ y : V × V, e (e' y) = y := by
    intro y
    have h := congrArg (fun f : Module.End ℂ (V × V) => f y) hee'
    simpa using h
  have he'ea : ∀ y : V × V, e' (e y) = y := by
    intro y
    have h := congrArg (fun f : Module.End ℂ (V × V) => f y) he'e
    simpa using h
  have hunit_e : ∀ x y : V × V, inner ℂ (e x) (e y) = inner ℂ x y := by
    intro x y
    rw [he]
    exact hunit x y
  have hunit_e' : ∀ x y : V × V, inner ℂ (e' x) (e' y) = inner ℂ x y := by
    intro x y
    rw [he']
    have h := hunit_e ((cAct p).symm x) ((cAct p).symm y)
    rw [show e ((cAct p).symm x) = x from by rw [he]; exact LinearEquiv.apply_symm_apply _ _,
      show e ((cAct p).symm y) = y from by rw [he]; exact LinearEquiv.apply_symm_apply _ _] at h
    exact h.symm
  -- the two cross relations expressing unitarity of `e` (and of `e'`)
  have hxy : ∀ x y : V × V, inner ℂ (e x) y = inner ℂ x (e' y) := by
    intro x y
    calc inner ℂ (e x) y = inner ℂ (e x) (e (e' y)) := by rw [hee'a y]
      _ = inner ℂ x (e' y) := hunit_e x (e' y)
  have hxy' : ∀ x y : V × V, inner ℂ (e' x) y = inner ℂ x (e y) := by
    intro x y
    calc inner ℂ (e' x) y = inner ℂ (e' x) (e' (e y)) := by rw [he'ea y]
      _ = inner ℂ x (e y) := hunit_e' x (e y)
  -- `S = e + e'` and `T = i (e - e')` are self-adjoint
  have hS : (e + e').IsSymmetric := by
    intro x y
    rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_right, hxy x y,
      hxy' x y, add_comm]
  have hT : (Complex.I • (e - e')).IsSymmetric := by
    intro x y
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.sub_apply,
      inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, hxy x y, hxy' x y,
      Complex.conj_I]
    ring
  have hSss : Module.End.IsSemisimple (e + e') :=
    Module.End.isFinitelySemisimple_iff_isSemisimple.mp hS.isFinitelySemisimple
  have hTss : Module.End.IsSemisimple (Complex.I • (e - e')) :=
    Module.End.isFinitelySemisimple_iff_isSemisimple.mp hT.isFinitelySemisimple
  -- `S` and `T` commute, and `e = (1/2) (S + (-i) T)`
  have hcomm : Commute (e + e') (Complex.I • (e - e')) := by
    have h1 : Commute e e' := by rw [commute_iff_eq, hee', he'e]
    have hae : Commute (e + e') e := Commute.add_left (Commute.refl e) h1.symm
    have hae' : Commute (e + e') e' := Commute.add_left h1 (Commute.refl e')
    exact (hae.sub_right hae').smul_right Complex.I
  have hneg : Module.End.IsSemisimple ((-Complex.I) • (Complex.I • (e - e'))) :=
    Module.End.IsSemisimple_smul (-Complex.I) hTss
  have hcomm2 : Commute (e + e') ((-Complex.I) • (Complex.I • (e - e'))) :=
    hcomm.smul_right (-Complex.I)
  have hsum : Module.End.IsSemisimple ((e + e') + (-Complex.I) • (Complex.I • (e - e'))) :=
    Module.End.IsSemisimple.add_of_commute hcomm2 hSss hneg
  have htwo : (2 : ℂ) • e = (e + e') + (-Complex.I) • (Complex.I • (e - e')) := by
    ext x : 1
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, smul_smul]
    rw [show (-Complex.I) * Complex.I = 1 by simp, one_smul]
    module
  have hfinal : Module.End.IsSemisimple e := by
    have h := Module.End.IsSemisimple_smul ((1 / 2 : ℂ)) hsum
    rwa [show ((1 / 2 : ℂ) • ((e + e') + (-Complex.I) • (Complex.I • (e - e')))) = e from by
      rw [← htwo]; simp [smul_smul]] at h
  exact hfinal

end Instances

end Work.Mostow.Margulis
