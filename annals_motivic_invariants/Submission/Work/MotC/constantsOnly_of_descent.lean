import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotC.C6.Defs
import Submission.Work.MotC.constantsOnly_all
import Submission.Work.MotC.ratFunc_eq_C_of_isAlgebraic
import Submission.Work.MotC.exists_algebraMap_genXY_of_algHom_ratFunc
import Submission.Work.MotC.adjoin_genX_genY_eq_top
import Submission.Work.MotC.not_algEquiv_ratFunc_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Constants-only for a descent of an elliptic function field

Let `𝕜 → L` be an algebraic field extension, `W⁄L` a non-singular Weierstrass curve with function
field `K = L(W)`, and `A ⊆ K` a `𝕜`-subfield which is linearly disjoint from `L` over `𝕜` and
satisfies `A · L = K` — the situation of a descent of `K` to `𝕜`.  Then every `𝕜`-algebra
embedding `ι : A → M(t)` of `A` into a one-variable rational function field over a `𝕜`-field `M`
has image in the constants `M`.

The proof is the "descent" argument of the Lin–Shinder chapter:

1. choose an algebraic closure `N = M̄` of `M` and an embedding `σ : L ↪ N` over `𝕜`;
2. `A ⊗[𝕜] L ≅ K` (`Work.MotC.C6.exists_tensorAlgEquiv`), so `ι` together with `σ` produce an
   `L`-algebra map `Ψ : K → N(t)` (with `L` acting on `N(t)` through `σ`);
3. the one-variable rigidity `Work.MotC.exists_algebraMap_genXY_of_algHom_ratFunc` makes the image
   of the generic point of `W` constant, and `K = L(x, y)`
   (`Work.MotC.adjoin_genX_genY_eq_top`) then makes the whole image of `Ψ` constant;
4. hence the image of `ι` lies in the image of the coefficient extension `ρ : M(t) → N(t)` and is
   therefore algebraic over `M`, so constant by `Work.MotC.ratFunc_eq_C_of_isAlgebraic`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open scoped TensorProduct

namespace Work.MotC

noncomputable section

/-- An injective `R`-algebra homomorphism pulls back algebraicity: if `f x` satisfies a non-trivial
polynomial relation, so does `x`. -/
theorem isAlgebraic_of_injective_algHom {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (hf : Function.Injective f) {x : A}
    (h : IsAlgebraic R (f x)) : IsAlgebraic R x :=
  (isAlgebraic_algHom_iff f hf).mp h

/-- **Constants-only for a descent.**  Let `L⁄𝕜` be algebraic, `W⁄L` a non-singular Weierstrass
curve with function field `K = L(W)`, and `A ⊆ K` a `𝕜`-subfield linearly disjoint from `L` with
`A ⊔ L = K`.  Then every `𝕜`-embedding of `A` into a one-variable rational function field over a
`𝕜`-field has constant image. -/
theorem constantsOnly_of_descent {𝕜 L : Type} [Field 𝕜] [Field L] [DecidableEq L] [Algebra 𝕜 L]
    [Algebra.IsAlgebraic 𝕜 L] (W : WeierstrassCurve L) (hΔ : W.Δ ≠ 0)
    (A : IntermediateField 𝕜 (WeierstrassCurve.Affine.FunctionField W))
    (hLI : A.LinearDisjoint L)
    (hsup : A ⊔ (IsScalarTower.toAlgHom 𝕜 L
      (WeierstrassCurve.Affine.FunctionField W)).fieldRange = ⊤) :
    Work.MotV.ConstantsOnly 𝕜 A := by
  classical
  intro M _ _ ι x
  -- ## The algebraic closure `N := M̄` and the embedding `σ : L ↪ N` over `𝕜`.
  let σ : L →ₐ[𝕜] AlgebraicClosure M := IsAlgClosed.lift
  letI : Algebra L (AlgebraicClosure M) := σ.toRingHom.toAlgebra
  -- ## The coefficient extension `ρ : M(t) → N(t)`.
  have hcoeff : Function.Injective
      (Polynomial.mapAlgHom (Algebra.ofId M (AlgebraicClosure M)) :
        Polynomial M →ₐ[M] Polynomial (AlgebraicClosure M)) := by
    intro p q hpq
    exact Polynomial.map_injective (algebraMap M (AlgebraicClosure M))
      (algebraMap M (AlgebraicClosure M)).injective hpq
  have hφ : nonZeroDivisors (Polynomial M) ≤
      Submonoid.comap (Polynomial.mapAlgHom (Algebra.ofId M (AlgebraicClosure M)))
        (nonZeroDivisors (Polynomial (AlgebraicClosure M))) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hcoeff
  let ρ₀ : RatFunc M →ₐ[M] RatFunc (AlgebraicClosure M) :=
    RatFunc.mapAlgHom (Polynomial.mapAlgHom (Algebra.ofId M (AlgebraicClosure M))) hφ
  -- ## The comparison map `Ψ : K → N(t)`.
  let g : L →ₐ[𝕜] RatFunc (AlgebraicClosure M) :=
    ((Algebra.ofId (AlgebraicClosure M) (RatFunc (AlgebraicClosure M))).restrictScalars 𝕜).comp σ
  have hg : ∀ l : L, g l = algebraMap L (RatFunc (AlgebraicClosure M)) l := fun l => rfl
  let Φ : (↥A ⊗[𝕜] L) →ₐ[𝕜] RatFunc (AlgebraicClosure M) :=
    Algebra.TensorProduct.lift ((ρ₀.restrictScalars 𝕜).comp ι) g (fun _ _ => Commute.all _ _)
  have hfield : IsField (TensorProduct 𝕜 ↥A L) :=
    hLI.isField_of_isAlgebraic (Or.inr (inferInstance : Algebra.IsAlgebraic 𝕜 L))
  obtain ⟨e, he1, he2⟩ := C6.exists_tensorAlgEquiv A hLI hfield hsup
  let Ψ : WeierstrassCurve.Affine.FunctionField W →ₐ[𝕜] RatFunc (AlgebraicClosure M) :=
    Φ.comp e.symm.toAlgHom
  have hΨL : ∀ l : L, Ψ (algebraMap L (WeierstrassCurve.Affine.FunctionField W) l)
      = algebraMap L (RatFunc (AlgebraicClosure M)) l := by
    intro l
    have h1 : e.symm (algebraMap L (WeierstrassCurve.Affine.FunctionField W) l)
        = TensorProduct.tmul 𝕜 (1 : ↥A) l := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply, he2 l]
    show Φ (e.symm (algebraMap L (WeierstrassCurve.Affine.FunctionField W) l))
      = algebraMap L (RatFunc (AlgebraicClosure M)) l
    rw [h1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact hg l
  let Ψ' : WeierstrassCurve.Affine.FunctionField W →ₐ[L] RatFunc (AlgebraicClosure M) :=
    { Ψ with commutes' := hΨL }
  -- ## The generic point of `W` has constant image, and it generates `K` over `L`.
  obtain ⟨⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩ :=
    exists_algebraMap_genXY_of_algHom_ratFunc W hΔ (AlgebraicClosure M) Ψ'
  let c : AlgebraicClosure M →ₐ[L] RatFunc (AlgebraicClosure M) :=
    (Algebra.ofId (AlgebraicClosure M) (RatFunc (AlgebraicClosure M))).restrictScalars L
  have hc : ∀ n : AlgebraicClosure M, c n = algebraMap (AlgebraicClosure M)
      (RatFunc (AlgebraicClosure M)) n := fun n => rfl
  have hgenX : Ψ' (C6.genX W) ∈ c.fieldRange := by
    rw [AlgHom.mem_fieldRange]
    exact ⟨n₁, (hc n₁).trans hn₁.symm⟩
  have hgenY : Ψ' (C6.genY W) ∈ c.fieldRange := by
    rw [AlgHom.mem_fieldRange]
    exact ⟨n₂, (hc n₂).trans hn₂.symm⟩
  have hle : IntermediateField.adjoin L ({C6.genX W, C6.genY W} : Set _)
      ≤ IntermediateField.comap Ψ' c.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact (Subalgebra.mem_comap _ _ _).mpr hgenX
    · exact (Subalgebra.mem_comap _ _ _).mpr hgenY
  have htop : (⊤ : IntermediateField L (WeierstrassCurve.Affine.FunctionField W))
      ≤ IntermediateField.comap Ψ' c.fieldRange := by
    rw [← adjoin_genX_genY_eq_top W]
    exact hle
  have hconst : ∀ y : WeierstrassCurve.Affine.FunctionField W, ∃ n : AlgebraicClosure M,
      Ψ' y = algebraMap (AlgebraicClosure M) (RatFunc (AlgebraicClosure M)) n := by
    intro y
    have hy : y ∈ IntermediateField.comap Ψ' c.fieldRange := htop trivial
    have hy2 : Ψ' y ∈ c.fieldRange := (Subalgebra.mem_comap _ _ _).mp hy
    rw [AlgHom.mem_fieldRange] at hy2
    obtain ⟨n, hn⟩ := hy2
    exact ⟨n, (hn.symm).trans (hc n)⟩
  -- ## `Ψ x = ρ (ι x)`, and `Ψ x` is constant.
  have hΨx : Ψ (x : WeierstrassCurve.Affine.FunctionField W) = ρ₀ (ι x) := by
    have h1 : e.symm (x : WeierstrassCurve.Affine.FunctionField W)
        = TensorProduct.tmul 𝕜 (x : ↥A) (1 : L) := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply, he1 x]
    show Φ (e.symm (x : WeierstrassCurve.Affine.FunctionField W)) = ρ₀ (ι x)
    rw [h1, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      map_one, mul_one]
  obtain ⟨n, hn⟩ := hconst (x : WeierstrassCurve.Affine.FunctionField W)
  have hρx : ρ₀ (ι x) = algebraMap (AlgebraicClosure M) (RatFunc (AlgebraicClosure M)) n := by
    rw [← hΨx]
    exact hn
  -- ## Hence `ι x` is algebraic over `M`, so constant.
  have hnN : IsAlgebraic M (algebraMap (AlgebraicClosure M) (RatFunc (AlgebraicClosure M)) n) :=
    IsAlgebraic.algebraMap (Algebra.IsAlgebraic.isAlgebraic n)
  have hinj : Function.Injective ρ₀ :=
    RingHom.injective (ρ₀ : RatFunc M →+* RatFunc (AlgebraicClosure M))
  have halg : IsAlgebraic M (ι x) :=
    isAlgebraic_of_injective_algHom ρ₀ hinj (by rw [hρx]; exact hnN)
  obtain ⟨m, hm⟩ := ratFunc_eq_C_of_isAlgebraic (ι x) halg
  exact ⟨m, hm.symm⟩

end

end Work.MotC
