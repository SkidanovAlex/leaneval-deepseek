import Mathlib
import Submission.Work.Core.Defs

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open scoped ContDiff

namespace Work.AlmostComplex.Types

variable {n : ℕ}

/-!
# Almost complex structures: complexification, types, the Nijenhuis torsion

This file sets up the vocabulary of the chapter.  Throughout, `E n = ℝ^{2n}` is the model
space of the Newlander–Nirenberg problem (`E n = EuclideanSpace ℝ (Fin (2*n))`) and
`J : E n → E n →L[ℝ] E n` is a field of endomorphisms with `J x ∘ J x = -1` on an open set.
For the *linear* theory one fixes `J₀ : E n →L[ℝ] E n` with `J₀ (J₀ v) = -v` and works at one
point; the pointwise statements about `J` are then obtained by specialising to `J x`.

## The complexified tangent space

`Cx n := E n × E n`, where the pair `(a, b)` represents the complexified vector `a + i·b`.
The `ℂ`-module structure is the canonical one (`i·(a,b) = (-b, a)`); it does *not* depend on
`J`.  A real-linear `J₀` extends to a `ℂ`-linear map `Jcx J₀` by `z ↦ (J₀ z.1, J₀ z.2)`, and
the two idempotents `proj10`, `proj01` are the projections onto the `±i` eigenspaces of `Jcx`:
`π^{1,0} = (1 - iJ)/2`, `π^{0,1} = (1 + iJ)/2`.  On the pair picture

  `proj10 J₀ (a,b) = ((a + J₀ b)/2, (b - J₀ a)/2)`  and
  `proj01 J₀ (a,b) = ((a - J₀ b)/2, (b + J₀ a)/2)`,

which are exactly `Submission.proj10 J x` and `Submission.proj01 J x` for `J₀ = J x`.

## Main definitions

* `Cx`, `inl`, `conjC`, `Jcx`, `proj10`, `proj01`, `IsType10`, `IsType01`
* `proj10Dual`, `proj01Dual`, `IsType10Form`, `IsType01Form` (the cotangent side)
* `proj20`, `proj11`, `proj02` (type decomposition of `2`-forms), `dExterior`
* `nijenhuisAt` (the pointwise Nijenhuis tensor), `nijenhuisCx` (its complexified version)
* `InvolutiveOn` (involutivity of the `(0,1)`-distribution), `NijenhuisVanishesAt`,
  `DbarSqVanishesOn`
* `Jsub` (the almost complex structure induced on a `J`-invariant subspace)

## Conventions

A real vector `v` sits in `Cx n` as `inl v = (v, 0)`; a complexified vector `z` is
`inl z.1 + i·inl z.2`.  The `(0,1)`-field of a real field `X` is `Z01 J X = X + i·JX`, i.e.
the pair `(X y, J y (X y))`, definitionally `Submission.Z01`.

Scalars: `half` is `1/2` viewed in `ℂ` as the image of `(1/2 : ℝ)`.  The lemma
`ofReal_smul` converts `((r : ℝ) : ℂ) • x` to `r • x` in any `ℂ`-module.
-/

/-- The complexified tangent space at a point of `E n`: the pair `(a, b)` represents the
complexified vector `a + i·b`. -/
abbrev Cx (n : ℕ) := E n × E n

/-! ### The `ℂ`-module structure on `Cx n` -/

instance instSMulCx (n : ℕ) : SMul ℂ (Cx n) where
  smul c z := (c.re • z.1 - c.im • z.2, c.im • z.1 + c.re • z.2)

@[simp] theorem smul_fst (c : ℂ) (z : Cx n) :
    (c • z).1 = c.re • z.1 - c.im • z.2 := rfl

@[simp] theorem smul_snd (c : ℂ) (z : Cx n) :
    (c • z).2 = c.im • z.1 + c.re • z.2 := rfl

instance instModuleCx (n : ℕ) : Module ℂ (Cx n) :=
  Module.ofMinimalAxioms
    (fun r x y => by
      refine Prod.ext ?_ ?_ <;> simp only [smul_fst, smul_snd, Prod.fst_add, Prod.snd_add] <;>
        rw [smul_add, smul_add] <;> abel)
    (fun r s x => by
      refine Prod.ext ?_ ?_ <;> simp only [smul_fst, smul_snd, Prod.fst_add, Prod.snd_add,
        Complex.add_re, Complex.add_im] <;> rw [add_smul, add_smul] <;> abel)
    (fun r s x => by
      refine Prod.ext ?_ ?_ <;> simp only [smul_fst, smul_snd, Complex.mul_re, Complex.mul_im]
      · module
      · module)
    (fun x => by
      refine Prod.ext ?_ ?_ <;> simp only [smul_fst, smul_snd, Complex.one_re, Complex.one_im,
        zero_smul, sub_zero, one_smul, zero_add])

instance instIsScalarTowerCx (n : ℕ) : IsScalarTower ℝ ℂ (Cx n) :=
  ⟨fun r c z => by
    refine Prod.ext ?_ ?_ <;>
      simp only [smul_fst, smul_snd, Prod.smul_fst, Prod.smul_snd, Complex.smul_re,
        Complex.smul_im, smul_sub, smul_add, smul_smul, smul_eq_mul]⟩

instance instSMulCommClassCx (n : ℕ) : SMulCommClass ℝ ℂ (Cx n) :=
  ⟨fun r c z => by
    refine Prod.ext ?_ ?_ <;>
      simp only [smul_fst, smul_snd, Prod.smul_fst, Prod.smul_snd, Complex.smul_re,
        Complex.smul_im, smul_sub, smul_add, smul_smul, smul_eq_mul, mul_comm]⟩

/-! ### Scalars -/

/-- `1/2` as a complex number, namely the image of the real number `1/2`. -/
noncomputable def half : ℂ := ((1/2 : ℝ) : ℂ)

@[simp] theorem half_re : half.re = 1/2 := Complex.ofReal_re _

@[simp] theorem half_im : half.im = 0 := Complex.ofReal_im _

/-- The scalar action of a real number seen in `ℂ` is the real scalar action:
`((r : ℝ) : ℂ) • x = r • x` in any `ℂ`-module (with compatible real structure). -/
theorem ofReal_smul {M : Type*} [AddCommMonoid M] [Module ℝ M] [Module ℂ M]
    [IsScalarTower ℝ ℂ M] (r : ℝ) (x : M) : ((r : ℝ) : ℂ) • x = r • x := by
  have h : ((r : ℝ) : ℂ) = r • (1 : ℂ) := by
    show algebraMap ℝ ℂ r = _
    rw [Algebra.smul_def, mul_one]
  rw [h, IsScalarTower.smul_assoc, one_smul]

theorem half_smul {M : Type*} [AddCommMonoid M] [Module ℝ M] [Module ℂ M]
    [IsScalarTower ℝ ℂ M] (x : M) : half • x = (1/2 : ℝ) • x := by
  rw [half]; exact ofReal_smul _ _

/-- Multiplication by `i` on the complexified tangent space: `i·(a, b) = (-b, a)`. -/
@[simp] theorem I_smul (z : Cx n) : (Complex.I : ℂ) • z = (-z.2, z.1) := by
  refine Prod.ext ?_ ?_ <;>
    simp [smul_fst, smul_snd, Complex.I_re, Complex.I_im, zero_smul, one_smul]

/-- Multiplication by `-i`: `(-i)·(a, b) = (b, -a)`. -/
@[simp] theorem negI_smul (z : Cx n) : (-Complex.I : ℂ) • z = (z.2, -z.1) := by
  refine Prod.ext ?_ ?_ <;>
    simp [smul_fst, smul_snd, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      zero_smul, one_smul, neg_smul]

/-! ### The real subspace and conjugation -/

/-- The real embedding `v ↦ v + i·0` of `E n` into its complexification. -/
def inl (v : E n) : Cx n := (v, 0)

@[simp] theorem inl_fst (v : E n) : (inl v).1 = v := rfl
@[simp] theorem inl_snd (v : E n) : (inl v).2 = 0 := rfl

theorem inl_add (v w : E n) : inl (v + w) = inl v + inl w := by simp [inl]

theorem inl_smul (c : ℝ) (v : E n) : inl (c • v) = c • inl v := by simp [inl]

theorem inl_injective : Function.Injective (inl : E n → Cx n) := fun v w h => by
  simpa [inl] using congrArg Prod.fst h

/-- A complexified vector is the sum of its real and imaginary parts: `z = z.1 + i·z.2`. -/
theorem eq_inl_add_I_smul_inl (z : Cx n) : z = inl z.1 + Complex.I • inl z.2 := by
  refine Prod.ext ?_ ?_ <;>
    simp [inl, smul_fst, smul_snd, Complex.I_re, Complex.I_im, zero_smul, one_smul]

/-- Complex conjugation on the complexification: `(a, b) ↦ (a, -b)`.  It is real linear but
conjugate linear over `ℂ`, and swaps the `(1,0)` and `(0,1)` types. -/
def conjC (z : Cx n) : Cx n := (z.1, -z.2)

@[simp] theorem conjC_fst (z : Cx n) : (conjC z).1 = z.1 := rfl
@[simp] theorem conjC_snd (z : Cx n) : (conjC z).2 = -z.2 := rfl
@[simp] theorem conjC_conjC (z : Cx n) : conjC (conjC z) = z := by
  refine Prod.ext ?_ ?_ <;> simp [conjC]

theorem conjC_add (z w : Cx n) : conjC (z + w) = conjC z + conjC w := by
  refine Prod.ext ?_ ?_ <;> simp only [conjC_fst, conjC_snd, Prod.fst_add, Prod.snd_add] <;> abel

theorem conjC_I_smul (z : Cx n) : conjC (Complex.I • z) = (-Complex.I) • conjC z := by
  refine Prod.ext ?_ ?_ <;> simp [conjC, smul_fst, smul_snd, Complex.I_re, Complex.I_im,
    zero_smul, one_smul, neg_smul]

/-! ### The extension of a real-linear endomorphism to the complexification -/

/-- The `ℂ`-linear extension of a real-linear endomorphism `J₀` of `E n` to `Cx n`:
`J(a + i·b) = J a + i·J b`. -/
noncomputable def Jcx (J₀ : E n →L[ℝ] E n) : Cx n →ₗ[ℂ] Cx n where
  toFun z := (J₀ z.1, J₀ z.2)
  map_add' z w := by simp
  map_smul' c z := by
    refine Prod.ext ?_ ?_ <;>
      simp only [smul_fst, smul_snd, Prod.smul_fst, Prod.smul_snd] <;> simp [map_sub, map_add]

@[simp] theorem Jcx_apply (J₀ : E n →L[ℝ] E n) (z : Cx n) :
    Jcx J₀ z = (J₀ z.1, J₀ z.2) := rfl

@[simp] theorem Jcx_fst (J₀ : E n →L[ℝ] E n) (z : Cx n) : (Jcx J₀ z).1 = J₀ z.1 := rfl

@[simp] theorem Jcx_snd (J₀ : E n →L[ℝ] E n) (z : Cx n) : (Jcx J₀ z).2 = J₀ z.2 := rfl

/-- `Jcx` commutes with `i`: it is `ℂ`-linear. -/
theorem Jcx_I_smul (J₀ : E n →L[ℝ] E n) (z : Cx n) :
    Jcx J₀ (Complex.I • z) = Complex.I • Jcx J₀ z :=
  (Jcx J₀).map_smul Complex.I z

/-- If `J₀² = -1` then its extension satisfies `Jcx² = -1`. -/
theorem Jcx_comp_self (J₀ : E n →L[ℝ] E n) (hJ : ∀ v, J₀ (J₀ v) = -v) (z : Cx n) :
    Jcx J₀ (Jcx J₀ z) = -z := by
  refine Prod.ext ?_ ?_ <;> simp [hJ]

/-! ### The `(1,0)`- and `(0,1)`-projections -/

/-- The `(1,0)`-projection `π^{1,0} = (1 - i·J)/2` of the complexified tangent space. -/
noncomputable def proj10 (J₀ : E n →L[ℝ] E n) : Cx n →ₗ[ℂ] Cx n :=
  half • (LinearMap.id - Complex.I • Jcx J₀)

/-- The `(0,1)`-projection `π^{0,1} = (1 + i·J)/2` of the complexified tangent space. -/
noncomputable def proj01 (J₀ : E n →L[ℝ] E n) : Cx n →ₗ[ℂ] Cx n :=
  half • (LinearMap.id + Complex.I • Jcx J₀)

/-- The `(1,0)`-part of `(a, b)`: `((a + J b)/2, (b - J a)/2)`. -/
theorem proj10_apply (J₀ : E n →L[ℝ] E n) (z : Cx n) :
    proj10 J₀ z = ((1/2 : ℝ) • (z.1 + J₀ z.2), (1/2 : ℝ) • (z.2 - J₀ z.1)) := by
  have h : proj10 J₀ z = half • (z - (-(J₀ z.2), J₀ z.1)) := by
    rw [proj10, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, Jcx_apply, I_smul]
  rw [h, half_smul]
  refine Prod.ext ?_ ?_ <;>
    simp [smul_fst, smul_snd, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]

/-- The `(0,1)`-part of `(a, b)`: `((a - J b)/2, (b + J a)/2)`. -/
theorem proj01_apply (J₀ : E n →L[ℝ] E n) (z : Cx n) :
    proj01 J₀ z = ((1/2 : ℝ) • (z.1 - J₀ z.2), (1/2 : ℝ) • (z.2 + J₀ z.1)) := by
  have h : proj01 J₀ z = half • (z + (-(J₀ z.2), J₀ z.1)) := by
    rw [proj01, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, Jcx_apply, I_smul]
  rw [h, half_smul]
  refine Prod.ext ?_ ?_ <;>
    simp [smul_fst, smul_snd, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, smul_sub, sub_eq_add_neg]

/-- `proj10 (J x)` is `Submission.proj10 J x` (the `(1,0)`-projection of the pair picture). -/
theorem proj10_eq_submission (J : E n → E n →L[ℝ] E n) (x : E n) (z : Cx n) :
    proj10 (J x) z = Submission.proj10 J x z := by
  simp only [proj10_apply, Submission.proj10]

/-- `proj01 (J x)` is `Submission.proj01 J x`. -/
theorem proj01_eq_submission (J : E n → E n →L[ℝ] E n) (x : E n) (z : Cx n) :
    proj01 (J x) z = Submission.proj01 J x z := by
  simp only [proj01_apply, Submission.proj01]

/-- A complexified vector is of type `(1,0)` if it is an eigenvector of `J` with eigenvalue `i`. -/
def IsType10 (J₀ : E n →L[ℝ] E n) (z : Cx n) : Prop := Jcx J₀ z = Complex.I • z

/-- A complexified vector is of type `(0,1)` if it is an eigenvector of `J` with eigenvalue `-i`. -/
def IsType01 (J₀ : E n →L[ℝ] E n) (z : Cx n) : Prop := Jcx J₀ z = (-Complex.I) • z

/-- `(0,1)`-type on a set, for a complexified vector *field*. -/
def IsType01On (J : E n → E n →L[ℝ] E n) (Z : E n → Cx n) (U : Set (E n)) : Prop :=
  ∀ x ∈ U, IsType01 (J x) (Z x)

/-- `(1,0)`-type on a set, for a complexified vector *field*. -/
def IsType10On (J : E n → E n →L[ℝ] E n) (Z : E n → Cx n) (U : Set (E n)) : Prop :=
  ∀ x ∈ U, IsType10 (J x) (Z x)

/-- The complexified `(0,1)`-vector field `X + i·JX` associated to a real vector field `X`,
i.e. the pair `(X y, J y (X y))`.  Definitionally `Submission.Z01`. -/
def Z01 (J : E n → E n →L[ℝ] E n) (X : E n → E n) : E n → Cx n :=
  fun y => (X y, J y (X y))

@[simp] theorem Z01_apply (J : E n → E n →L[ℝ] E n) (X : E n → E n) (y : E n) :
    Z01 J X y = (X y, J y (X y)) := rfl

theorem Z01_eq_submission (J : E n → E n →L[ℝ] E n) (X : E n → E n) :
    Z01 J X = Submission.Z01 J X := rfl

/-! ### The cotangent side: `(1,0)`- and `(0,1)`-forms -/

/-- The `(1,0)`-projection of a complex valued real-linear form: `θ^{1,0} = (θ - i·θ∘J)/2`.
This is `Submission.dpartial J u x` for `θ = fderiv ℝ u x`. -/
noncomputable def proj10Dual (J₀ : E n →L[ℝ] E n) (θ : E n →L[ℝ] ℂ) : E n →L[ℝ] ℂ :=
  half • (θ - Complex.I • (θ.comp J₀))

/-- The `(0,1)`-projection of a complex valued real-linear form: `θ^{0,1} = (θ + i·θ∘J)/2`.
This is `Submission.dbar J u x` for `θ = fderiv ℝ u x`. -/
noncomputable def proj01Dual (J₀ : E n →L[ℝ] E n) (θ : E n →L[ℝ] ℂ) : E n →L[ℝ] ℂ :=
  half • (θ + Complex.I • (θ.comp J₀))

@[simp] theorem proj10Dual_apply (J₀ : E n →L[ℝ] E n) (θ : E n →L[ℝ] ℂ) (v : E n) :
    proj10Dual J₀ θ v = (1/2 : ℝ) • (θ v - Complex.I * θ (J₀ v)) := by
  rw [proj10Dual, half, ofReal_smul (1/2 : ℝ) (θ - Complex.I • (θ.comp J₀)),
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]

@[simp] theorem proj01Dual_apply (J₀ : E n →L[ℝ] E n) (θ : E n →L[ℝ] ℂ) (v : E n) :
    proj01Dual J₀ θ v = (1/2 : ℝ) • (θ v + Complex.I * θ (J₀ v)) := by
  rw [proj01Dual, half, ofReal_smul (1/2 : ℝ) (θ + Complex.I • (θ.comp J₀)),
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]

/-- `∂̄u` is the `(0,1)`-projection of the differential of `u`. -/
theorem dbar_eq_proj01Dual (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x : E n) :
    dbar J u x = proj01Dual (J x) (fderiv ℝ u x) := by
  simp only [Submission.dbar, proj01Dual, half]
  exact (ofReal_smul (1/2 : ℝ)
    (fderiv ℝ u x + Complex.I • (fderiv ℝ u x).comp (J x))).symm

/-- `∂u` is the `(1,0)`-projection of the differential of `u`. -/
theorem dpartial_eq_proj10Dual (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x : E n) :
    dpartial J u x = proj10Dual (J x) (fderiv ℝ u x) := by
  simp only [Submission.dpartial, proj10Dual, half]
  exact (ofReal_smul (1/2 : ℝ)
    (fderiv ℝ u x - Complex.I • (fderiv ℝ u x).comp (J x))).symm

/-- A form is of type `(1,0)` if `θ ∘ J = i·θ`; equivalently it is fixed by `proj10Dual`. -/
def IsType10Form (J₀ : E n →L[ℝ] E n) (θ : E n →L[ℝ] ℂ) : Prop :=
  ∀ v, θ (J₀ v) = Complex.I * θ v

/-- A form is of type `(0,1)` if `θ ∘ J = -i·θ`; equivalently it is fixed by `proj01Dual`. -/
def IsType01Form (J₀ : E n →L[ℝ] E n) (θ : E n →L[ℝ] ℂ) : Prop :=
  ∀ v, θ (J₀ v) = - Complex.I * θ v

/-! ### Type decomposition of `2`-forms and the exterior derivative of a `1`-form -/

/-- The `(0,2)`-projection of a `2`-form, evaluated on two vectors:
`α^{0,2}(X,Y) = (1/4)(α(X,Y) + i α(JX,Y) + i α(X,JY) - α(JX,JY))`. -/
noncomputable def proj02 (J₀ : E n →L[ℝ] E n) (α : E n → E n → ℂ) (X Y : E n) : ℂ :=
  (1/4 : ℂ) * (α X Y + Complex.I * α (J₀ X) Y + Complex.I * α X (J₀ Y)
    - α (J₀ X) (J₀ Y))

/-- The `(2,0)`-projection of a `2`-form, evaluated on two vectors:
`α^{2,0}(X,Y) = (1/4)(α(X,Y) - i α(JX,Y) - i α(X,JY) - α(JX,JY))`. -/
noncomputable def proj20 (J₀ : E n →L[ℝ] E n) (α : E n → E n → ℂ) (X Y : E n) : ℂ :=
  (1/4 : ℂ) * (α X Y - Complex.I * α (J₀ X) Y - Complex.I * α X (J₀ Y)
    - α (J₀ X) (J₀ Y))

/-- The `(1,1)`-projection of a `2`-form, evaluated on two vectors:
`α^{1,1}(X,Y) = (1/2)(α(X,Y) + α(JX,JY))`. -/
noncomputable def proj11 (J₀ : E n →L[ℝ] E n) (α : E n → E n → ℂ) (X Y : E n) : ℂ :=
  (1/2 : ℂ) * (α X Y + α (J₀ X) (J₀ Y))

/-- The exterior derivative of a complex valued `1`-form field at a point, evaluated on two
vectors: `dθ_x(u,w) = D_u(θ(·)(w)) - D_w(θ(·)(u))`.  This is the value on the constant
extensions of `u` and `w` of the alternating bilinear form `dθ`; it is bilinear. -/
noncomputable def dExterior (θ : E n → E n →L[ℝ] ℂ) (x X Y : E n) : ℂ :=
  fderiv ℝ (fun y => θ y Y) x X - fderiv ℝ (fun y => θ y X) x Y

/-! ### The Nijenhuis tensor at a point -/

/-- The Nijenhuis tensor of a field of endomorphisms `J` on an arbitrary real normed space `G`,
evaluated on two vector fields:

  `N(V, W) = [JV, JW] - J[JV, W] - J[V, JW] - [V, W]`.

On `G = E n` this is `nijenhuis` definitionally (see `nijenhuisG_eq`); the general form is needed
for the restriction of an almost complex structure to an invariant subspace. -/
noncomputable def nijenhuisG {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (J : G → G →L[ℝ] G) (V W : G → G) (x : G) : G :=
  VectorField.lieBracket ℝ (fun y => J y (V y)) (fun y => J y (W y)) x
    - J x (VectorField.lieBracket ℝ (fun y => J y (V y)) W x)
    - J x (VectorField.lieBracket ℝ V (fun y => J y (W y)) x)
    - VectorField.lieBracket ℝ V W x

theorem nijenhuisG_eq (J : E n → E n →L[ℝ] E n) (V W : E n → E n) (x : E n) :
    nijenhuisG J V W x = nijenhuis J V W x := rfl

/-- The Nijenhuis tensor at a point, evaluated on two tangent vectors: `nijenhuis J V W x` for
the constant extensions of `u` and `w`.  When `J` is an almost complex structure near `x` this
is a tensor, i.e. it depends only on `u` and `w` (see `nijenhuis_eq_nijenhuisAt`). -/
noncomputable def nijenhuisAt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (J : G → G →L[ℝ] G) (x u w : G) : G :=
  nijenhuisG J (fun _ => u) (fun _ => w) x

/-- The `ℂ`-bilinear extension of the Nijenhuis tensor to complexified vector fields: for
`Z = X + iX'` and `W = Y + iY'`,
`N_ℂ(Z,W) = N(X,Y) - N(X',Y') + i(N(X,Y') + N(X',Y))`. -/
noncomputable def nijenhuisCx (J : E n → E n →L[ℝ] E n) (Z W : E n → Cx n) (x : E n) : Cx n :=
  (nijenhuis J (fun y => (Z y).1) (fun y => (W y).1) x
      - nijenhuis J (fun y => (Z y).2) (fun y => (W y).2) x,
    nijenhuis J (fun y => (Z y).1) (fun y => (W y).2) x
      + nijenhuis J (fun y => (Z y).2) (fun y => (W y).1) x)

/-! ### Involutivity of the `(0,1)`-distribution and vanishing conditions -/

/-- The `(0,1)`-distribution `T^{0,1}` is involutive on `U`: the Lie bracket of two smooth
complexified `(0,1)`-vector fields is again of type `(0,1)` on `U`. -/
def InvolutiveOn (J : E n → E n →L[ℝ] E n) (U : Set (E n)) : Prop :=
  ∀ Z W : E n → Cx n, IsType01On J Z U → IsType01On J W U →
    ContDiffOn ℝ ∞ (fun y => (Z y).1) U → ContDiffOn ℝ ∞ (fun y => (Z y).2) U →
    ContDiffOn ℝ ∞ (fun y => (W y).1) U → ContDiffOn ℝ ∞ (fun y => (W y).2) U →
    ∀ x ∈ U, IsType01 (J x) (cbracket Z W x)

/-- The pointwise Nijenhuis tensor of `J` vanishes on `U`. -/
def NijenhuisVanishesAt (J : E n → E n →L[ℝ] E n) (U : Set (E n)) : Prop :=
  ∀ x ∈ U, ∀ u w : E n, nijenhuisAt J x u w = 0

/-- The `(0,2)`-part of the structure equations vanishes on `U`: `∂̄²u = 0` for every smooth
complex valued function `u`, tested on every pair of smooth vector fields. -/
def DbarSqVanishesOn (J : E n → E n →L[ℝ] E n) (U : Set (E n)) : Prop :=
  ∀ x ∈ U, ∀ u : E n → ℂ, ContDiffAt ℝ 2 u x → ∀ X Y : E n → E n,
    ContDiffAt ℝ 1 X x → ContDiffAt ℝ 1 Y x → dbarSq J u X Y x = 0

/-! ### Restriction to an invariant subspace -/

/-- The almost complex structure induced on a `J`-invariant real subspace `V ⊆ E n`: at the
point `x ∈ V` the endomorphism `J x` restricts to an endomorphism of `V`. -/
noncomputable def Jsub (J : E n → E n →L[ℝ] E n) (V : Submodule ℝ (E n))
    (hV : ∀ x v, v ∈ V → J x v ∈ V) : V → V →L[ℝ] V :=
  fun x => (J (x : E n)).restrict (hV (x : E n))

@[simp] theorem Jsub_apply (J : E n → E n →L[ℝ] E n) (V : Submodule ℝ (E n))
    (hV : ∀ x v, v ∈ V → J x v ∈ V) (x : V) (v : V) :
    ((Jsub J V hV x v : V) : E n) = J (x : E n) v := rfl

end Work.AlmostComplex.Types
