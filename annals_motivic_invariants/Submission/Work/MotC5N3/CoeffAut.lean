import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The coefficient action on `Work.MotC5N3.OmA K D` (`Work.MotV5.coeffAut`)

`Work.MotC5N3.OmA K D = K̄(E)` is the function field of the marked elliptic curve `D.E` of a Klein datum
`D` over `𝕜`, base changed to `K̄ = Work.MotC5N3.KbA K = AlgebraicClosure (K)`.

An automorphism `σ` of the coefficient field `K̄` over `K = K` acts on `K̄(E)` by acting on
the coefficients of the Weierstrass equation and fixing the two generators `x, y` — the elliptic
curve is defined over `𝕜 ⊆ K`, so the Weierstrass polynomial is fixed by `σ`, and both the coordinate
ring and its fraction field inherit the automorphism.  Since the Klein co-ordinates
`kleinCoord D K̄ i` are `𝕜`-linear combinations of monomials in `x, y`, this automorphism fixes them
all; that is `coeffAut`.

The general construction is that of `Work.MotC.coeffAut` (`Submission/Work/MotC/Coeff.lean`),
transported from `𝕜`-coefficients to `K = K`-coefficients: `AdjoinRoot.mapRingEquiv` on the
affine coordinate ring, `IsFractionRing.ringEquivOfRingEquiv` on the function field, and
`AlgEquiv.ofRingEquiv` to record the `K`-linearity.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace Work.MotC5N3
open Work.MotV5
noncomputable section

/-! ## §1 The coefficient action of a field automorphism on a base-changed Weierstrass curve -/

section General

variable {R K L : Type*} [Field R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]

/-- A `K`-algebra automorphism of `L` fixes the constants coming from `R ⊆ K`. -/
lemma coeff_fixes_base (σ : L ≃ₐ[K] L) (c : R) : σ (algebraMap R L c) = algebraMap R L c := by
  rw [IsScalarTower.algebraMap_apply R K L c, σ.commutes]

/-- The Weierstrass polynomial of `E ⁄ L` is fixed by the coefficient action of `σ`, because
`E ⁄ L` is defined over `R ⊆ K` and `σ` fixes `R`. -/
lemma coeff_polynomial_baseChange (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L) :
    (Affine.polynomial (E.baseChange L)).map (Polynomial.mapAlgEquiv σ).toRingEquiv
      = Affine.polynomial (E.baseChange L) := by
  have hσ : ∀ c : R, σ (algebraMap R L c) = algebraMap R L c := coeff_fixes_base σ
  simp only [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  simp [hσ]

/-- **The coefficient action on the coordinate ring** `L[E ⁄ L]`: the ring automorphism which
applies `σ` to the `L`-coefficients and fixes the classes of `X` and `Y`. -/
noncomputable def coeffCoordEquiv (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L) :
    Affine.CoordinateRing (E.baseChange L) ≃+* Affine.CoordinateRing (E.baseChange L) :=
  AdjoinRoot.mapRingEquiv (Polynomial.mapAlgEquiv σ).toRingEquiv _ _
    (by rw [coeff_polynomial_baseChange E σ])

/-- On the image of `L[X]` (the `x`-co-ordinate polynomial ring) the coefficient action is
coefficientwise. -/
lemma coeffCoordEquiv_of (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L) (r : L[X]) :
    coeffCoordEquiv E σ (AdjoinRoot.of _ r) = AdjoinRoot.of _ (r.map σ.toRingHom) := by
  simp [coeffCoordEquiv]

/-- The coefficient action restricts to `σ` on the `L`-constants of the coordinate ring. -/
lemma coeffCoordEquiv_algebraMap (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L) (c : L) :
    coeffCoordEquiv E σ (algebraMap L (Affine.CoordinateRing (E.baseChange L)) c)
      = algebraMap L (Affine.CoordinateRing (E.baseChange L)) (σ c) := by
  have h1 : ∀ d : L, algebraMap L (Affine.CoordinateRing (E.baseChange L)) d
      = AdjoinRoot.of _ (Polynomial.C d) := fun d => rfl
  rw [h1 c, h1 (σ c), coeffCoordEquiv_of]
  simp

/-- The coefficient action is `K`-linear on the coordinate ring. -/
lemma coeffCoordEquiv_algebraMap_base (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L) (k : K) :
    coeffCoordEquiv E σ (algebraMap K (Affine.CoordinateRing (E.baseChange L)) k)
      = algebraMap K (Affine.CoordinateRing (E.baseChange L)) k := by
  rw [IsScalarTower.algebraMap_apply K L (Affine.CoordinateRing (E.baseChange L)) k,
    coeffCoordEquiv_algebraMap, σ.commutes]

/-- **The coefficient action on the function field `L(E ⁄ L)`**, i.e. `σ` acting on the
coefficients of `L(E ⁄ L)`. -/
noncomputable def coeffAction (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L) :
    Affine.FunctionField (E.baseChange L) ≃ₐ[K] Affine.FunctionField (E.baseChange L) :=
  AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv (coeffCoordEquiv E σ)) (by
    intro k
    rw [IsScalarTower.algebraMap_apply K (Affine.CoordinateRing (E.baseChange L))
      (Affine.FunctionField (E.baseChange L)) k,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, coeffCoordEquiv_algebraMap_base,
      ← IsScalarTower.algebraMap_apply K (Affine.CoordinateRing (E.baseChange L))
      (Affine.FunctionField (E.baseChange L)) k])

lemma coeffAction_apply (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L)
    (x : Affine.FunctionField (E.baseChange L)) :
    coeffAction E σ x = IsFractionRing.ringEquivOfRingEquiv (coeffCoordEquiv E σ) x := by
  simp only [coeffAction, AlgEquiv.ofRingEquiv_apply]

/-- The coefficient action restricts to `σ` on the `L`-constants of the function field. -/
lemma coeffAction_algebraMap (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L) (c : L) :
    coeffAction E σ (algebraMap L (Affine.FunctionField (E.baseChange L)) c)
      = algebraMap L (Affine.FunctionField (E.baseChange L)) (σ c) := by
  rw [coeffAction_apply, IsScalarTower.algebraMap_apply L (Affine.CoordinateRing (E.baseChange L))
    (Affine.FunctionField (E.baseChange L)) c,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, coeffCoordEquiv_algebraMap,
    ← IsScalarTower.algebraMap_apply L (Affine.CoordinateRing (E.baseChange L))
    (Affine.FunctionField (E.baseChange L)) (σ c)]

/-- The coefficient action fixes the `x`-co-ordinate `x = genX`. -/
lemma coeffAction_genX (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L) :
    coeffAction E σ (Work.MotV.genX (E.baseChange L)) = Work.MotV.genX (E.baseChange L) := by
  simp only [Work.MotV.genX]
  rw [show CoordinateRing.mk (E.baseChange L) (Polynomial.C Polynomial.X)
      = AdjoinRoot.of _ Polynomial.X from rfl]
  rw [coeffAction_apply, IsFractionRing.ringEquivOfRingEquiv_algebraMap, coeffCoordEquiv_of]
  simp

/-- The coefficient action fixes the `y`-co-ordinate `y = genY`. -/
lemma coeffAction_genY (E : WeierstrassCurve R) (σ : L ≃ₐ[K] L) :
    coeffAction E σ (Work.MotV.genY (E.baseChange L)) = Work.MotV.genY (E.baseChange L) := by
  simp only [Work.MotV.genY]
  rw [coeffAction_apply, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [coeffCoordEquiv]

end General

/-! ## §2 The Klein co-ordinates are fixed -/

section Klein

variable {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜)

variable (σ : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K)

/-- The basis `1, x, y, x², xy` in which the Klein forms are written is fixed by the coefficient
action, since `x` and `y` are. -/
lemma coeffAction_kleinBas (m : Fin 5) :
    coeffAction D.E σ (Work.MotV.kleinBas D (Work.MotC5N3.KbA K) m)
      = Work.MotV.kleinBas D (Work.MotC5N3.KbA K) m := by
  fin_cases m <;>
    simp [Work.MotV.kleinBas, coeffAction_genX, coeffAction_genY]

end Klein

/-! ## §3 The target -/

/-- Every `K`-algebra automorphism `σ` of `Work.MotC5N3.KbA K` extends to an automorphism of the
function field `Work.MotC5N3.OmA K D` (acting on the coefficients of the Weierstrass equation and fixing `x, y`),
and this extension fixes all Klein co-ordinates `kleinCoord D (Work.MotC5N3.KbA K) i`. -/
theorem coeffAut (𝕜 : Type) [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜)
    (σ : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K) :
    ∃ τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D,
      (∀ c : Work.MotC5N3.KbA K,
        τ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
          = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c)) ∧
      (∀ i : Fin 5, τ (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i)
          = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i) := by
  refine ⟨coeffAction D.E σ, fun c => coeffAction_algebraMap D.E σ c, fun i => ?_⟩
  simp only [Work.MotV.kleinCoord_eq_sum, map_sum, map_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  · rw [← IsScalarTower.algebraMap_apply 𝕜 (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (D.coord i m),
      IsScalarTower.algebraMap_apply 𝕜 (K) (Work.MotC5N3.OmA K D) (D.coord i m)]
    exact (coeffAction D.E σ).commutes _
  · exact coeffAction_kleinBas D σ m

end

end Work.MotC5N3