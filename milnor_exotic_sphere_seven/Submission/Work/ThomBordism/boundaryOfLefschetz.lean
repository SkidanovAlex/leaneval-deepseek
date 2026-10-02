import Mathlib
import Submission.Work.ThomBordism.bdryInterfaces
import Submission.Work.ThomBordism.transgressionCapPairConnecting
import Submission.Work.ThomBordism.nondegenerate_midForm_of_good
import Submission.Work.UnimodularForms.Signature
import Submission.Work.ThomBordism.PontryaginThom.Torsion
import Submission.Work.ThomBordism.homologyFiniteOfNullBordism
import Submission.Work.Bordism.LesImage
import Submission.Work.Cohomology.kronH_kernel_eq_torsion
import Submission.Work.Cohomology.kronH_natural
import Submission.Work.ThomBordism.evaluation_kernel_torsion_of_pd

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.boundaryOfLefschetz` — the reduction of the crux to **detection**

**Target.** `(∀ W, LefschetzDualityBdry W) → BoundaryMaximalIsotropic`: the relative middle-degree
Lefschetz duality of the pair `(W, ∂W)` implies that the image `K = bdryK W` of the restriction
`H⁴(W;ℚ) → H⁴(∂W;ℚ)` is *maximal* isotropic for the middle form of `∂W`.

## What is proved here (all sorry-free)

Write `X = TopCat.of W.W`, `A = bdrySet W.W` (`∂W`), `β = bdryClass W = hPairδ X A 8 W.w ∈ H₈(A;ℤ)`.

1. **Exactness** (`bdryK_eq_ker_deltaRat`): `bdryK W = ker (deltaRat W)`, i.e. the image of the
   restriction is the kernel of the rationalised connecting map `δ`.  This is the integral exactness
   `Work.Bordism.range_restr_eq_ker_pairDelta` base-changed along the flat map `ℤ → ℚ`; the two
   ingredients `range_baseChange_rat`, `ker_baseChange_rat` (the latter from
   `Module.Flat.ker_lTensor_eq`) are proved here.
2. **The rationalised two-variable base change** (`baseChange_bilinear_exists₂`,
   `baseChangeBilin₂_tmul`, `tensor_bilin_ext₂`) and hence the rationalised Kronecker pairing on `W`
   (`kronRatX`, `kronRatX_tmul`) — the workspace's `Work.SignatureBordism.baseChangeBilin` handles
   only the case of one module, and the pairing here is between `H⁴(W;ℤ)` and `H₄(W;ℤ)`.
3. **`Φ` and the transgression** (`capBdry`, `phiBdry`, `phiBdry_apply`):
   `Φ y = i_*(y ⌢ β) = (δ y) ⌢ w` (`Work.ThomBordism.transgressionCapPairConnecting`).
4. **The adjunction** (`interForm_pullback_eq_kron`, `bdryFormBilin_pullback_eq_kron`): for
   `u ∈ H⁴(W;ℚ)` and `y ∈ H⁴(∂W;ℚ)`,

   `B (i^* u) y = ⟨u, Φ y⟩_W`   (`B = bdryFormBilin W`),

   the composition of the symmetry of the middle form of `∂W` (`interForm_symm_of_even`,
   reproved here as `bdryFormBilin_sym` to avoid importing `boundaryHalfDimension`) with the
   naturality of the Kronecker pairing (`Work.Cohomology.kronH_natural`).
5. **The reduction** (`boundaryOfLefschetz_of_detection`): from `Detection`, the crux follows.
   Given `y ∈ H⁴(∂W;ℚ)` orthogonal to `K` and `u ∈ H⁴(W;ℚ)`, the adjunction gives
   `⟨u, Φ y⟩_W = B (i^*u) y = 0`; detection gives `Φ y = 0`; the transgression and the injectivity
   of the rationalised cap product with `w` (`capRat_injective`, a consequence of the hypothesis)
   give `δ y = 0`; exactness (1) gives `y ∈ K`.

So the crux is reduced to **one** statement, `Detection` (defined in this file):
an integral class `z ∈ H₄(W;ℤ) ⊗ ℚ` which is orthogonal, for the Kronecker pairing, to every class
of `H⁴(W;ℤ) ⊗ ℚ` must vanish.  This is the statement that the Kronecker pairing
`H⁴(W;ℚ) × H₄(W;ℚ) → ℚ` is non-degenerate in its second variable; it is *equivalent* to the crux
(given the hypothesis), and it is what the previous sessions called "half lives, half dies".

## The three inputs

1. `capRat_injective` — `Φ_ℚ y = 0 → δ y = 0`.  By the transgression identity (3) the integral
   `Φ` is `ψ ∘ δ` with `ψ z = (z ⌢ w)`, and `ψ` is injective by the hypothesis `hinj` (bidegree
   `(5,4)` of `LefschetzDualityBdry`); hence `ker Φ = ker δ` **integrally**.  Since `ℚ` is a flat
   `ℤ`-module, the equality of integral kernels rationalises (`ker_baseChange_rat`), giving
   `ker Φ_ℚ = ker δ_ℚ`.  (This is the route that avoids the `ℤ`-module instance diamond between
   `singularCochainComplex` and `cochainC`: the kernel comparison is made on the *integral* linear
   maps, where both spellings coincide definitionally.)
2. `detectionH : Detection` — the geometric input: an integral middle homology class of `W` whose
   rationalisation is orthogonal to every rational middle cohomology class must vanish rationally.
   Equivalently, `H₄(W;ℤ)` is finitely generated, so `Work.Cohomology.kronH_kernel_eq_torsion`
   plus the surjectivity of the integral Kronecker pairing (`Work.ThomBordism.kronH_surjective`)
   apply; the finite generation of the homology of the compact `C^∞` manifold with boundary `W` is
   `Work.ThomBordism.homologyFiniteOfNullBordism` (Whitney embedding + Euclidean neighbourhood
   retract, Hatcher A.8/A.9).
3. `boundaryOfLefschetz` — the target, assembled from 1 and 2 by
   `boundaryOfLefschetz_of_detection`.

Also delegated while this file was written (not needed by the final proof, which goes through
kernel comparison instead): `ThomBordism/bdryCapBdryBijective` (middle-degree Poincaré duality for
the closed `8`-manifold `∂W`) and `ThomBordism/bdryHalfDimConnecting` (the equivalent
"half lives, half dies" statement `2 dim ker i_* = dim H₄(∂W;ℚ)`).

-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open TensorProduct

namespace Work.ThomBordism

noncomputable section

-- Prefer the module structure induced on a submodule (as everywhere in this workspace).
attribute [local instance 5000] Submodule.module


/-! ## Base change of the range and the kernel of a linear map along `ℤ → ℚ`

The universal coefficient / exactness steps of the reduction are all instances of the fact that
`ℚ` is a *flat* `ℤ`-module: tensoring with `ℚ` preserves kernels, and it sends the range of `f` to
the range of `f ⊗ ℚ`. -/

/-- **The range of a base-changed linear map is the base change of the range.** -/
theorem range_baseChange_rat {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →ₗ[ℤ] N) :
    (f.baseChange ℚ).range = (f.range).baseChange ℚ := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
        rw [LinearMap.baseChange_tmul]
        exact Submodule.tmul_mem_baseChange_of_mem a ⟨m, rfl⟩
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · rw [Submodule.baseChange_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨m, ⟨n, rfl⟩, rfl⟩
    exact ⟨(1 : ℚ) ⊗ₜ[ℤ] n, by rw [LinearMap.baseChange_tmul]; simp⟩

/-- **The kernel of a base-changed linear map is the base change of the kernel** (`ℚ` is flat over
`ℤ`). -/
theorem ker_baseChange_rat {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →ₗ[ℤ] N) :
    (f.baseChange ℚ).ker = (f.ker).baseChange ℚ := by
  -- the two spellings of the base-changed map have the same underlying function
  have hcoe : ∀ x : ℚ ⊗[ℤ] M, (AlgebraTensorModule.lTensor ℚ ℚ f) x = (f.baseChange ℚ) x :=
    fun x => by rw [AlgebraTensorModule.coe_lTensor, LinearMap.baseChange_eq_ltensor]
  have hker : (AlgebraTensorModule.lTensor ℚ ℚ f).ker = (f.baseChange ℚ).ker :=
    Submodule.ext fun x => by simp only [LinearMap.mem_ker, hcoe x]
  rw [← hker, Module.Flat.ker_lTensor_eq (R := ℤ) (S := ℚ) (M := ℚ) f]
  have hsub : (AlgebraTensorModule.lTensor ℚ ℚ (LinearMap.ker f).subtype)
      = ((LinearMap.ker f).subtype.baseChange ℚ) :=
    LinearMap.ext fun x => by
      rw [AlgebraTensorModule.coe_lTensor, LinearMap.baseChange_eq_ltensor]
  rw [show (AlgebraTensorModule.lTensor ℚ ℚ (LinearMap.ker f).subtype).range
        = ((LinearMap.ker f).subtype.baseChange ℚ).range from congrArg _ hsub,
    range_baseChange_rat, Submodule.range_subtype]

/-! ## The exactness of the pair sequence at `H⁴(∂W)` -/

/-- **Exactness of the pair sequence at `H⁴(∂W;ℚ)`**: the image `K` of the restriction is the kernel
of the rationalised connecting map `δ`.  This is the integral exactness
`Work.Bordism.range_restr_eq_ker_pairDelta` base-changed along the flat map `ℤ → ℚ`. -/
theorem bdryK_eq_ker_deltaRat {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F) :
    bdryK W = LinearMap.ker (deltaRat W) := by
  have h1 : bdryK W = (((HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℤ (TopCat.of W.W) (bdrySet W.W)) 4).hom).range).baseChange ℚ := by
    show LinearMap.range (Work.Bordism.pullbackRat 4 (bdryIncl W)) = _
    have hbridge : Work.Bordism.pullbackRat 4 (bdryIncl W)
        = ((HomologicalComplex.homologyMap
            (Work.Cohomology.restr ℤ (TopCat.of W.W) (bdrySet W.W)) 4).hom).baseChange ℚ := rfl
    rw [hbridge, range_baseChange_rat]
  have h2 : (((HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℤ (TopCat.of W.W) (bdrySet W.W)) 4).hom).range).baseChange ℚ
      = (((Work.Cohomology.pairδ ℤ (TopCat.of W.W) (bdrySet W.W) 4).hom).ker).baseChange ℚ := by
    rw [Work.Bordism.range_restr_eq_ker_pairDelta]
  have h3 : ((((Work.Cohomology.pairδ ℤ (TopCat.of W.W) (bdrySet W.W) 4).hom).ker).baseChange ℚ)
      = LinearMap.ker (deltaRat W) := by
    show _ = LinearMap.ker
      (((Work.Cohomology.pairδ ℤ (TopCat.of W.W) (bdrySet W.W) 4).hom).baseChange ℚ)
    rw [ker_baseChange_rat]
  rw [h1, h2, h3]

/-! ## Rationalising a bilinear form in two different modules -/

open TensorProduct in
/-- **The base change of a `ℤ`-bilinear form in two (possibly different) variables**: for
`B : M →ₗ[ℤ] M' →ₗ[ℤ] ℤ` there is a `ℚ`-bilinear form on `ℚ ⊗ M × ℚ ⊗ M'` with
`(a ⊗ m, b ⊗ m') ↦ (a * b) * B m m'`. -/
theorem baseChange_bilinear_exists₂ {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    [Module ℤ M] [Module ℤ M'] (B : M →ₗ[ℤ] M' →ₗ[ℤ] ℤ) :
    ∃ F : (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] M') →ₗ[ℚ] ℚ,
      ∀ (a b : ℚ) (m : M) (m' : M'), F (a ⊗ₜ[ℤ] m) (b ⊗ₜ[ℤ] m') = (a * b) * (B m m' : ℚ) := by
  let castT : ℤ →ₗ[ℤ] ℚ := Algebra.linearMap ℤ ℚ
  -- the `ℚ`-valued version of `B`
  let Bq : M →ₗ[ℤ] M' →ₗ[ℤ] ℚ := (LinearMap.compRight ℤ castT).comp B
  -- `k m` is the `ℚ`-linear map `x ↦ x • (Bq m)` into the dual of `M'`
  let k : M →ₗ[ℤ] (ℚ →ₗ[ℚ] (M' →ₗ[ℤ] ℚ)) :=
    (LinearMap.restrictScalars ℤ
      ((LinearMap.ringLmapEquivSelf ℚ ℚ (M' →ₗ[ℤ] ℚ)).symm).toLinearMap).comp Bq
  -- base change of `k m` along `ℤ → ℚ`: `ℚ`-linear on `ℚ ⊗[ℤ] M'`
  let h : M →ₗ[ℤ] ((ℚ ⊗[ℤ] M') →ₗ[ℚ] ℚ) :=
    (TensorProduct.AlgebraTensorModule.uncurry ℤ ℚ ℤ ℚ M' ℚ).comp k
  -- `g` is `ℚ`-linear in its first variable and `ℤ`-linear in the second
  let g : ℚ →ₗ[ℚ] M →ₗ[ℤ] ((ℚ ⊗[ℤ] M') →ₗ[ℚ] ℚ) :=
    LinearMap.toSpanSingleton ℚ (M →ₗ[ℤ] ((ℚ ⊗[ℤ] M') →ₗ[ℚ] ℚ)) h
  refine ⟨TensorProduct.AlgebraTensorModule.lift g, ?_⟩
  intro a b m m'
  have hBq : ∀ (m : M) (m' : M'), Bq m m' = (B m m' : ℚ) := by
    intro m m'
    simp [Bq, castT, LinearMap.compRight_apply, Algebra.linearMap_apply]
  have hk : ∀ (m : M) (x : ℚ) (m' : M'), (k m) x m' = x * (B m m' : ℚ) := by
    intro m x m'
    have e1 : k m = (LinearMap.restrictScalars ℤ
        ((LinearMap.ringLmapEquivSelf ℚ ℚ (M' →ₗ[ℤ] ℚ)).symm).toLinearMap) (Bq m) := rfl
    rw [e1]
    have e2 : (LinearMap.restrictScalars ℤ
        ((LinearMap.ringLmapEquivSelf ℚ ℚ (M' →ₗ[ℤ] ℚ)).symm).toLinearMap) (Bq m)
        = LinearMap.toSpanSingleton ℚ (M' →ₗ[ℤ] ℚ) (Bq m) := rfl
    rw [e2, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, hBq m m', smul_eq_mul]
  have hh : ∀ (m : M) (x : ℚ) (m' : M'), h m (x ⊗ₜ[ℤ] m') = x * (B m m' : ℚ) := by
    intro m x m'
    have e1 : h m = TensorProduct.AlgebraTensorModule.lift (k m) := by
      simp only [h, LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.uncurry_apply]
    rw [e1, TensorProduct.AlgebraTensorModule.lift_tmul]
    exact hk m x m'
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  have e3 : g a m = a • h m := by
    simp only [g, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply]
  rw [e3, LinearMap.smul_apply, hh m b m', smul_eq_mul, mul_assoc]

open TensorProduct in
/-- The definite choice of the rationalised two-variable bilinear form. -/
noncomputable def baseChangeBilin₂ {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    [Module ℤ M] [Module ℤ M'] (B : M →ₗ[ℤ] M' →ₗ[ℤ] ℤ) :
    (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] M') →ₗ[ℚ] ℚ :=
  Classical.choose (baseChange_bilinear_exists₂ B)

/-- **The computation rule** for the rationalised two-variable form. -/
theorem baseChangeBilin₂_tmul {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    [Module ℤ M] [Module ℤ M'] (B : M →ₗ[ℤ] M' →ₗ[ℤ] ℤ) (a b : ℚ) (m : M) (m' : M') :
    baseChangeBilin₂ B (a ⊗ₜ[ℤ] m) (b ⊗ₜ[ℤ] m') = (a * b) * (B m m' : ℚ) :=
  Classical.choose_spec (baseChange_bilinear_exists₂ B) a b m m'

open TensorProduct in
/-- **Extensionality** for the rationalised two-variable forms. -/
theorem tensor_bilin_ext₂ {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    [Module ℤ M] [Module ℤ M']
    {F G : (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] M') →ₗ[ℚ] ℚ}
    (h : ∀ (a b : ℚ) (m : M) (m' : M'),
      F (a ⊗ₜ[ℤ] m) (b ⊗ₜ[ℤ] m') = G (a ⊗ₜ[ℤ] m) (b ⊗ₜ[ℤ] m')) : F = G := by
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b n => exact h a b m n
      | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-! ## The rationalised Kronecker pairing on `W` and on `∂W` -/

/-- The boundary class `β = ∂w ∈ H₈(∂W;ℤ)` of a null-bordism family. -/
abbrev bdryClass {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :=
  Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w

/-- **The rationalised Kronecker pairing on `W`**: the base change to `ℚ` of
`⟨·,·⟩ : H⁴(W;ℤ) × H₄(W;ℤ) → ℤ`. -/
noncomputable def kronRatX {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    (ℚ ⊗[ℤ] (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of W.W))).homology 4) →ₗ[ℚ]
      (ℚ ⊗[ℤ] (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of W.W))).homology 4) →ₗ[ℚ] ℚ :=
  baseChangeBilin₂ (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of W.W)) 4)

/-- **The computation rule** for the rationalised Kronecker pairing on `W`. -/
theorem kronRatX_tmul {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F)
    (a b : ℚ) (x : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of W.W))).homology 4)
    (z : (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of W.W))).homology 4) :
    kronRatX W (a ⊗ₜ[ℤ] x) (b ⊗ₜ[ℤ] z) = (a * b) * ((Work.Cohomology.kronH ℤ
        (TopCat.toSSet.obj (TopCat.of W.W)) 4 x z : ℤ) : ℚ) :=
  baseChangeBilin₂_tmul _ a b x z

/-- **The integral class `y ⌢ β`** attached to `y ∈ H⁴(∂W;ℤ)`. -/
noncomputable def capBdry {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))).homology 4 →ₗ[ℤ]
      (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))).homology 4 :=
  (LinearMap.applyₗ (bdryClass W)).comp
    (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 4)

/-- **The integral map `Φ y = i_*(y ⌢ β) ∈ H₄(W;ℤ)`**: the composite of `y ↦ y ⌢ β` with the
homology class of the inclusion of the boundary. -/
noncomputable def phiBdry {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))).homology 4 →ₗ[ℤ]
      (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of W.W))).homology 4 :=
  ((HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of W.W) (bdrySet W.W)) 4).hom).comp (capBdry W)

/-- The transgression identity, in the spelling used below: `Φ y = (δ y) ⌢ w`. -/
theorem phiBdry_apply {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F)
    (y : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))).homology 4) :
    phiBdry W y = (Work.Cohomology.relCapPair (TopCat.of W.W) (bdrySet W.W) 5 4)
      ((Work.Cohomology.pairδ ℤ (TopCat.of W.W) (bdrySet W.W) 4) y) W.w := by
  unfold phiBdry capBdry bdryClass
  simp only [LinearMap.comp_apply]
  exact transgressionCapPairConnecting W y

/-- **The adjunction between the restriction and the connecting map, integrally**: for
`u ∈ H⁴(W;ℤ)` and `y ∈ H⁴(∂W;ℤ)`,

`⟨i^* u, y⟩_{∂W} = ⟨u, Φ y⟩_W`,  with `Φ y = i_*(y ⌢ β) ∈ H₄(W;ℤ)`.

This is the symmetry `⟨x, y ⌢ β⟩ = ⟨y, x ⌢ β⟩` of the middle intersection form of `∂W` (degree `4`
is even, `Work.ThomBordism.interForm_symm_of_even`) composed with the naturality of the Kronecker
pairing (`Work.Cohomology.kronH_natural`) for the inclusion `∂W ⊆ W`. -/
theorem interForm_pullback_eq_kron {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F)
    (u : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of W.W))).homology 4)
    (y : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))).homology 4) :
    Work.SignatureBordism.interForm ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 4
        (bdryClass W)
        ((Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (bdrySet W.W)) (TopCat.of W.W)
          (bdryIncl W) 4).hom u) y
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of W.W)) 4 u (phiBdry W y) := by
  -- symmetry of the middle intersection form of `∂W`
  have hcomm : ∀ (α β : (Work.Cohomology.cochainC ℤ
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))).homology 4),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 α
          ((Work.Cohomology.capPair ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 4) β
            (bdryClass W))
        = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 β
          ((Work.Cohomology.capPair ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 4) α
            (bdryClass W)) := by
    intro α β
    rw [← Work.SignatureBordism.interForm_apply_eq_kronH_capPair
        (X := TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) (m := 4) (n := 4)
        (c := bdryClass W) (y := β) (z := α),
      ← Work.SignatureBordism.interForm_apply_eq_kronH_capPair
        (X := TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) (m := 4) (n := 4)
        (c := bdryClass W) (y := α) (z := β),
      interForm_symm_of_even (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 (by norm_num)]
  rw [Work.SignatureBordism.interForm_apply_eq_kronH_capPair]
  rw [hcomm y ((Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (bdrySet W.W))
    (TopCat.of W.W) (bdryIncl W) 4).hom u)]
  rw [← Work.Cohomology.kronH_natural (TopCat.of (bdrySet W.W)) (TopCat.of W.W) (bdryIncl W) 4 u
    ((Work.Cohomology.capPair ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 4) y
      (bdryClass W))]
  rfl


/-! ## The rationalised adjunction, and the reduction of the crux to *detection* -/

/-- **The rationalised adjunction**: for `u ∈ H⁴(W;ℚ)` and `y ∈ H⁴(∂W;ℚ)`,

`B (i^* u) y = ⟨u, Φ y⟩_W`,  with `B = bdryFormBilin W` the middle intersection form of `∂W` and
`Φ y = i_*(y ⌢ β) ∈ H₄(W;ℤ)` (`phiBdry`). -/
theorem bdryFormBilin_pullback_eq_kron {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F) :
    (bdryFormBilin W).comp (Work.Bordism.pullbackRat 4 (bdryIncl W))
      = (kronRatX W).compl₂ ((phiBdry W).baseChange ℚ) := by
  refine tensor_bilin_ext₂ (fun a b m n => ?_)
  rw [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearMap.baseChange_tmul, kronRatX_tmul,
    Work.Bordism.pullbackRat_tmul]
  rw [show bdryFormBilin W
      = Work.SignatureBordism.baseChangeBilin (Work.SignatureBordism.interForm ℤ
          (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 4 (bdryClass W)) from rfl]
  rw [Work.SignatureBordism.baseChangeBilin_tmul, interForm_pullback_eq_kron]

/-- **The computation rule** for the rationalised connecting map `deltaRat` on pure tensors. -/
theorem deltaRat_tmul {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F)
    (a : ℚ) (n : (Work.Cohomology.cochainC ℤ
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))).homology 4) :
    deltaRat W (a ⊗ₜ[ℤ] n) = a ⊗ₜ[ℤ]
      ((Work.Cohomology.pairδ ℤ (TopCat.of W.W) (bdrySet W.W) 4) n) :=
  LinearMap.baseChange_tmul _ a n

attribute [local instance 100] ZSMul.toSMul in
/-- **Integral scalars move across a pure tensor**: `a ⊗ (c • m) = c • (a ⊗ m)` in `ℚ ⊗[ℤ] M`. -/
private lemma ratSmulTmul' {M : Type*} [AddCommGroup M] [Module ℤ M] (a : ℚ) (c : ℤ) (m : M) :
    a ⊗ₜ[ℤ] (c • m) = c • (a ⊗ₜ[ℤ] m) := by
  have h : (TensorProduct.mk ℤ ℚ M a) (c • m) = c • ((TensorProduct.mk ℤ ℚ M a) m) :=
    LinearMap.map_smul _ c m
  rwa [TensorProduct.mk_apply, TensorProduct.mk_apply] at h

attribute [local instance 100] ZSMul.toSMul in
/-- **Torsion dies in `ℚ ⊗[ℤ] M`.** -/
private lemma ratTmulOneEqZeroOfMemTorsion {M : Type*} [AddCommGroup M] [Module ℤ M] {m : M}
    (hm : m ∈ Submodule.torsion ℤ M) : (1 : ℚ) ⊗ₜ[ℤ] m = 0 := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (M := M) m).mp hm
  have hane : (a : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero a
  have hq : ((a : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hane
  have ha' : (a : ℤ) • m = 0 := Submonoid.smul_def a m ▸ ha
  have h1 : (a : ℤ) • ((1 : ℚ) ⊗ₜ[ℤ] m) = 0 := by
    rw [← ratSmulTmul' (1 : ℚ) (a : ℤ) m, ha', TensorProduct.tmul_zero]
  have h2 : ((a : ℤ) : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] m) = 0 := by
    rw [Int.cast_smul_eq_zsmul, h1]
  calc (1 : ℚ) ⊗ₜ[ℤ] m
      = (((a : ℤ) : ℚ)⁻¹ * ((a : ℤ) : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] m) := by
        rw [inv_mul_cancel₀ hq, one_smul]
    _ = ((a : ℤ) : ℚ)⁻¹ • (((a : ℤ) : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] m)) := by rw [mul_smul]
    _ = 0 := by rw [h2, smul_zero]

/-- **Extensionality for a `ℚ`-linear map on a base change**: two `ℚ`-linear maps out of
`ℚ ⊗[ℤ] M` which agree on the pure tensors are equal. -/
theorem baseChangeLin_ext {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] {F G : (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] N)}
    (h : ∀ (a : ℚ) (m : M), F (a ⊗ₜ[ℤ] m) = G (a ⊗ₜ[ℤ] m)) : F = G := by
  apply LinearMap.ext; intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => exact h a m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Evaluation at a fixed element, as an additive homomorphism.**  Going through
`AddMonoidHom.toIntLinearMap` (rather than `LinearMap.applyₗ`) is what makes the scalar action on
linear maps behave under coercions: `map_zsmul` for additive homomorphisms moves the `ℤ`-action
through `⇑`. -/
def evalHom {M N : Type*} [AddCommGroup M] [AddCommGroup N] (c : M) : (M →ₗ[ℤ] N) →+ N where
  toFun f := f c
  map_zero' := rfl
  map_add' f g := rfl

@[simp] theorem evalHom_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N] (c : M)
    (f : M →ₗ[ℤ] N) : evalHom c f = f c := rfl

/-- **The integral connecting map** `δ : H⁴(∂W;ℤ) → H⁵(W,∂W;ℤ)` of the pair `(W, ∂W)`, whose
rationalisation is `deltaRat`. -/
abbrev deltaInt {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))).homology 4 →ₗ[ℤ]
      (Work.Cohomology.relComplex ℤ (TopCat.of W.W) (bdrySet W.W)).homology 5 :=
  (Work.Cohomology.pairδ ℤ (TopCat.of W.W) (bdrySet W.W) 4).hom

/-- `deltaRat` is the rationalisation of `deltaInt`. -/
theorem deltaRat_eq_baseChange {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F) :
    deltaRat W = (deltaInt W).baseChange ℚ := rfl

/-- **The final step of the reduction**: on the rationalised relative middle cohomology of
`(W, ∂W)`, `Φ_ℚ y = 0` implies `δ y = 0`.

By the transgression identity (`phiBdry_apply`) the integral map `Φ = ψ ∘ δ` with
`ψ z = (z ⌢ w)`, and `ψ` is injective by hypothesis (`hinj`, the bidegree `(5,4)` instance of
`LefschetzDualityBdry`); hence `ker Φ = ker δ` **integrally**.  Since `ℚ` is a *flat* `ℤ`-module,
taking kernels commutes with `- ⊗[ℤ] ℚ` (`ker_baseChange_rat`), so the equality of integral kernels
rationalises to `ker Φ_ℚ = (ker Φ) ⊗ ℚ = (ker δ) ⊗ ℚ = ker δ_ℚ`.  In particular `Φ_ℚ y = 0`
implies `δ_ℚ y = 0`, i.e. `deltaRat W y = 0`. -/
theorem capRat_injective {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F)
    (hinj : Function.Injective (fun z : ↑(Work.Cohomology.relCohomology ℤ (TopCat.of W.W)
        (bdrySet W.W) 5) =>
      (Work.Cohomology.relCapPair (TopCat.of W.W) (bdrySet W.W) 5 4) z W.w)) :
    ∀ y : Work.SignatureBordism.ratCohomology 4
        (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))),
      (phiBdry W).baseChange ℚ y = 0 → deltaRat W y = 0 := by
  -- `Φ = ψ ∘ δ` with `ψ` injective, so `ker Φ = ker δ` integrally
  have hker : LinearMap.ker (phiBdry W) = LinearMap.ker (deltaInt W) := by
    ext z
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    have hp : phiBdry W z = (Work.Cohomology.relCapPair (TopCat.of W.W) (bdrySet W.W) 5 4)
        ((deltaInt W) z) W.w := phiBdry_apply W z
    rw [hp]
    constructor
    · intro hz
      exact hinj (by simpa using hz)
    · intro hz
      show (Work.Cohomology.relCapPair (TopCat.of W.W) (bdrySet W.W) 5 4)
        ((deltaInt W) z) W.w = 0
      rw [hz, map_zero, LinearMap.zero_apply]
  -- `ℚ` is flat over `ℤ`, so the equality of integral kernels rationalises
  have h1 : LinearMap.ker ((phiBdry W).baseChange ℚ) = LinearMap.ker (deltaRat W) := by
    rw [ker_baseChange_rat (phiBdry W), hker, deltaRat_eq_baseChange W,
      ker_baseChange_rat (deltaInt W)]
  intro y hy
  have hmem : y ∈ LinearMap.ker (deltaRat W) := by
    rw [← h1]
    exact hy
  exact LinearMap.mem_ker.mp hmem

/-- **The middle intersection form of `∂W` is symmetric** (degree `4` of an `8`-manifold is even).
This is `Work.ThomBordism.bdryFormBilin_symm` (`Submission/Work/ThomBordism/boundaryHalfDimension.lean`)
reproved here to avoid importing that module. -/
theorem bdryFormBilin_sym {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F)
    (x y : Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))) :
    bdryFormBilin W x y = bdryFormBilin W y x := by
  have hflip : bdryFormBilin W = (bdryFormBilin W).flip := by
    refine Work.SignatureBordism.tensor_bilin_ext (fun a b m n => ?_)
    rw [LinearMap.flip_apply]
    show (Work.SignatureBordism.baseChangeBilin (Work.SignatureBordism.interForm ℤ
        (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 4 (bdryClass W)) (a ⊗ₜ[ℤ] m) (b ⊗ₜ[ℤ] n))
      = Work.SignatureBordism.baseChangeBilin (Work.SignatureBordism.interForm ℤ
        (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 4 (bdryClass W)) (b ⊗ₜ[ℤ] n) (a ⊗ₜ[ℤ] m)
    rw [Work.SignatureBordism.baseChangeBilin_tmul, Work.SignatureBordism.baseChangeBilin_tmul,
      interForm_symm_of_even (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) 4 (by norm_num)]
    ring
  conv_lhs => rw [hflip]
  rw [LinearMap.flip_apply]

/-- **The associated bilinear form of the middle form of `∂W`** is `2` times the middle intersection
form `bdryFormBilin W`. -/
theorem associated_midForm {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F)
    (x y : Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))) :
    QuadraticMap.associated (Work.Bordism.midForm (k := 4) (bdryClosed W)) x y
      = bdryFormBilin W x y := by
  have hQ : ∀ z : Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))),
      Work.Bordism.midForm (k := 4) (bdryClosed W) z
        = Work.SignatureBordism.quadOfBilin (bdryFormBilin W) z := by
    intro z
    show Work.SignatureBordism.quadOfBilin (Work.SignatureBordism.ratInterForm 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) (bdryClass W)) z
      = Work.SignatureBordism.quadOfBilin (bdryFormBilin W) z
    rfl
  rw [QuadraticMap.associated_apply, hQ (x + y), hQ x, hQ y,
    Work.SignatureBordism.quadOfBilin_apply, Work.SignatureBordism.quadOfBilin_apply,
    Work.SignatureBordism.quadOfBilin_apply]
  simp only [map_add, LinearMap.add_apply]
  rw [bdryFormBilin_sym W y x]
  -- `associated (quadOfBilin B) x y = ⅟2 • (B x y + B y x) = ⅟2 • (2 • B x y) = B x y`
  rw [show bdryFormBilin W x x + bdryFormBilin W x y
      + (bdryFormBilin W x y + bdryFormBilin W y y)
      - bdryFormBilin W x x - bdryFormBilin W y y = (2 : ℚ) • bdryFormBilin W x y from by
    rw [two_smul]; abel]
  -- `associated (quadOfBilin B) x y = ⅟2 • (B x y + B y x) = ⅟2 • (2 • B x y) = B x y`.
  -- The `ℚ`-scalar identity `⅟2 • (2 • z) = z`, through `mul_smul` and `one_smul` (the
  -- instance-agnostic route; `inv_smul_smul₀` does not fire through the `SMul ℚ` instance used here).
  calc (⅟2 : ℚ) • ((2 : ℚ) • bdryFormBilin W x y)
      = ((⅟2 : ℚ) * 2) • bdryFormBilin W x y := (mul_smul _ _ _).symm
    _ = bdryFormBilin W x y := by
        rw [show (⅟2 : ℚ) * 2 = 1 by norm_num, one_smul]

/-- **Detection** (the geometric input of the reduction): an integral middle homology class of `W`
whose rationalisation is orthogonal, for the Kronecker pairing, to every rational middle cohomology
class of `W`, must vanish rationally.

Over a field of characteristic zero it follows from the finite generation of `H₄(W;ℤ)`
(`Work.Cohomology.kronH_kernel_eq_torsion` together with the surjectivity of the Kronecker pairing
`Work.ThomBordism.kronH_surjective`); equivalently it is the "half lives, half dies" dimension count
for `∂W`. -/
def Detection : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F)
    (z : ℚ ⊗[ℤ] (Work.Cohomology.chainC ℤ
      (TopCat.toSSet.obj (TopCat.of W.W))).homology 4),
    (∀ u : ℚ ⊗[ℤ] (Work.Cohomology.cochainC ℤ
      (TopCat.toSSet.obj (TopCat.of W.W))).homology 4, kronRatX W u z = 0) → z = 0

/-- **The reduction of the crux to detection**: from the relative Lefschetz duality of the pair
`(W, ∂W)` and `Detection`, the image `K` of the restriction `H⁴(W;ℚ) → H⁴(∂W;ℚ)` is maximal
isotropic.

Indeed, let `y ∈ H⁴(∂W;ℚ)` be orthogonal to `K`.  Then for every `u ∈ H⁴(W;ℚ)`,

`0 = B (i^* u) y = ⟨u, Φ y⟩_W`   (`bdryFormBilin_pullback_eq_kron`),

so `Φ y = 0` by detection; by the transgression identity `Φ_ℚ y = (δ y) ⌢ w`
(`phiBdry_apply`), the injectivity of the rationalised cap product with `w` (`capRat_injective`,
a consequence of the hypothesis) gives `δ y = 0`, i.e. `y ∈ ker δ = K` by exactness of the pair
sequence (`bdryK_eq_ker_deltaRat`). -/
theorem boundaryOfLefschetz_of_detection
    (h : ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
      LefschetzDualityBdry W)
    (hdet : Detection) :
    BoundaryMaximalIsotropic := by
  intro ι _ F W y hy
  have hz : (phiBdry W).baseChange ℚ y = 0 := by
    apply hdet ι F W
    intro u
    change ((kronRatX W).compl₂ ((phiBdry W).baseChange ℚ)) u y = 0
    rw [← bdryFormBilin_pullback_eq_kron W]
    have h1 := hy (Work.Bordism.pullbackRat 4 (bdryIncl W) u) ⟨u, rfl⟩
    rw [associated_midForm W] at h1
    exact h1
  have hdelta : deltaRat W y = 0 := capRat_injective W (h ι F W 5 4 rfl).1 y hz
  rw [bdryK_eq_ker_deltaRat]
  exact hdelta

/-- **Detection** (the geometric input of the reduction): an integral middle homology class of `W`
whose rationalisation is orthogonal, for the Kronecker pairing, to every rational middle cohomology
class of `W`, must vanish rationally.

Write `z = n ⊗ x`; since every `ℤ`-linear functional on `H₄(W;ℤ)` is a Kronecker pairing
(`Work.ThomBordism.kronH_surjective`), the hypothesis kills every functional on `x`, so `x` is
torsion (`Work.ThomBordism.mem_torsion_of_forall_apply_eq_zero`, using the finite generation of
`H₄(W;ℤ)` — `Work.ThomBordism.homologyFiniteOfNullBordism`, a compact manifold with boundary being a
Euclidean neighbourhood retract), and torsion dies in `ℚ ⊗[ℤ] ·`. -/
theorem detectionH : Detection := by
  intro ι _ F W z hz
  obtain ⟨n, x, rfl⟩ := Work.UnimodularForms.exists_tmul_eq z
  rcases eq_or_ne n 0 with hn | hn
  · rw [hn, TensorProduct.zero_tmul]
  have hkill : ∀ χ : (Work.Cohomology.chainC ℤ
      (TopCat.toSSet.obj (TopCat.of W.W))).homology 4 →ₗ[ℤ] ℤ, χ x = 0 := by
    intro χ
    obtain ⟨v, hv⟩ := Work.ThomBordism.kronH_surjective
      (TopCat.toSSet.obj (TopCat.of W.W)) 4
      (fun k => Work.Cohomology.chainC_X_free (TopCat.toSSet.obj (TopCat.of W.W)) k) χ
    have h := hz ((1 : ℚ) ⊗ₜ[ℤ] v)
    rw [kronRatX_tmul] at h
    rw [hv] at h
    have h3 : ((χ x : ℤ) : ℚ) = 0 := by
      rcases mul_eq_zero.mp h with h4 | h4
      · exact absurd (by simpa using h4) (by simpa using hn)
      · exact h4
    exact_mod_cast h3
  have htor := Work.ThomBordism.mem_torsion_of_forall_apply_eq_zero
    (Work.ThomBordism.homologyFiniteOfNullBordism W 4) x hkill
  have hx0 : (1 : ℚ) ⊗ₜ[ℤ] x = 0 := ratTmulOneEqZeroOfMemTorsion htor
  rw [show n ⊗ₜ[ℤ] x = n • ((1 : ℚ) ⊗ₜ[ℤ] x) by
        rw [TensorProduct.smul_tmul']; simp, hx0, smul_zero]

/-- **The target**: the crux of `Work.ThomBordism.BoundarySigma` from the relative Lefschetz duality
of the pair `(W, ∂W)`, via the reduction `boundaryOfLefschetz_of_detection`. -/
theorem boundaryOfLefschetz
    (h : ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
      LefschetzDualityBdry W) :
    BoundaryMaximalIsotropic :=
  boundaryOfLefschetz_of_detection h detectionH

end
end Work.ThomBordism
