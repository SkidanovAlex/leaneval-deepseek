import Mathlib
import Submission.Work.TorsorExistence.Defs
import Submission.Work.MotC.TransData
import Submission.Work.MotC.twistField_tensor
import Submission.Work.MotC.constantsOnly_all
import Submission.Work.MotC.C6.Defs
import Submission.Work.MotC.C6.exists_tensorAlgEquiv
import Submission.Work.MotC.C6.exists_algHom_ratFunc_mvPolynomial
import Submission.Work.MotC.C6.exists_baseChange_eq_of_point_ratFunc2
import Submission.Work.MotC.C6.genX_genY_nonsingular

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The twisted curve times `ℙ¹` is not rational (audit node C6 (i))

This file proves `Work.MotC.not_algEquiv_ratFunc_mvPolynomial`.

## The argument

Let `𝕜` be a field, `D` a quintic twist datum over `𝕜`, `L = D.ext.L` the cyclic quintic
extension, `E` the marked elliptic curve, `K = L(E)` its function field over `L`, and
`F = twistField D α` the fixed field of the twisted-translation automorphism `α`.  The descent
`Work.MotC.twistField_tensor` says that `F` and `L` are linearly disjoint over `𝕜` with compositum
`K`, so that the multiplication map `F ⊗[𝕜] L → K` is an isomorphism (`Work.MotC.C6.exists_tensorAlgEquiv`).

Suppose there were a `𝕜`-algebra isomorphism `θ : RatFunc F ≅ 𝕜(u,v)`.  Composing `θ` with a
`𝕜`-algebra map `𝕜(u,v) → RatFunc (RatFunc L) = L(u)(v)`
(`Work.MotC.C6.exists_algHom_ratFunc_mvPolynomial`) and with the inclusion of `F` into `RatFunc F`
gives a `𝕜`-algebra map `F → L(u)(v)`, which combines with the structure map `L → L(u)(v)` to a
map `F ⊗[𝕜] L → L(u)(v)`, i.e. an `L`-algebra map `Ψ : K → L(u)(v)`.

Pushing the generic point `(x, y)` of `E` over `K` (`Work.MotC.C6.genX`, `genY`) through `Ψ`
produces a point of `E` over `L(u)(v)`, and the two-variable rigidity
`Work.MotC.C6.exists_baseChange_eq_of_point_ratFunc2` (two applications of `constantsOnly_all`)
shows that this point is constant: `Ψ x = algebraMap L _ l` for some `l ∈ L`
(`Work.MotC.C6.exists_algebraMap_of_algHom_ratFunc`).  Since `Ψ` is injective and `L`-linear,
`x = algebraMap L K l` would be a constant — contradicting the elementary fact
`Work.MotC.C6.genX_notMem_range` that the generic `x`-coordinate is not constant.
-/

namespace Work.MotC

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped TensorProduct

namespace C6

/-- **The generic `x`-coordinate is not a constant.** In the function field `K = L(W)`, the class
of the coordinate function `X` is not in the image of `L`.

If `genX W = algebraMap L K l`, then in the coordinate ring `L[W]` one has
`mk W (C X) = algebraMap L (L[W]) l = mk W (C (C l))`, i.e. `mk W (C (X - C l)) = 0`.  Since
`mk W (C p) = p • 1` and `mk W (C p) = 0` is impossible for `p = X - C l ≠ 0`
(`WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero`), this is a contradiction. -/
theorem genX_notMem_range {L : Type} [Field L] (W : WeierstrassCurve L) :
    genX W ∉ Set.range (algebraMap L (WeierstrassCurve.Affine.FunctionField W)) := by
  rintro ⟨l, hl⟩
  have hinj := IsFractionRing.injective (WeierstrassCurve.Affine.CoordinateRing W)
    (WeierstrassCurve.Affine.FunctionField W)
  have h1 : algebraMap L (WeierstrassCurve.Affine.CoordinateRing W) l
      = WeierstrassCurve.Affine.CoordinateRing.mk W (Polynomial.C Polynomial.X) := by
    apply hinj
    rw [← IsScalarTower.algebraMap_apply L (WeierstrassCurve.Affine.CoordinateRing W)
      (WeierstrassCurve.Affine.FunctionField W), hl]
    rfl
  have h2 : algebraMap L (WeierstrassCurve.Affine.CoordinateRing W) l
      = WeierstrassCurve.Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C l)) := by
    rw [IsScalarTower.algebraMap_apply L (Polynomial L)
      (WeierstrassCurve.Affine.CoordinateRing W), Algebra.algebraMap_eq_smul_one,
      WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, Polynomial.algebraMap_eq]
  have h3 : WeierstrassCurve.Affine.CoordinateRing.mk W (Polynomial.C Polynomial.X)
      - WeierstrassCurve.Affine.CoordinateRing.mk W (Polynomial.C (Polynomial.C l)) = 0 := by
    rw [← h1, ← h2, sub_self]
  have hzero : WeierstrassCurve.Affine.CoordinateRing.mk W
      (Polynomial.C (Polynomial.X - Polynomial.C l)) = 0 := by
    rw [Polynomial.C_sub, map_sub]
    exact h3
  have hsmul : (Polynomial.X - Polynomial.C l) •
      (1 : WeierstrassCurve.Affine.CoordinateRing W) = 0 := by
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
    exact hzero
  have hpq := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero
    (W' := W) (p := Polynomial.X - Polynomial.C l) (q := 0) (by
      rw [zero_smul, add_zero]
      exact hsmul)
  exact Polynomial.X_sub_C_ne_zero l hpq.1

/-- **The image of the generic `x`-coordinate is a constant.**  For a nonsingular Weierstrass curve
`W` over `L`, every `L`-algebra map `L(W) → RatFunc (RatFunc L)` sends the generic `x`-coordinate
`[X]` into the image of `L`.

The generic point `([X], [Y])` is a nonsingular point of `W` over `K = L(W)`
(`Work.MotC.C6.genX_genY_nonsingular`); pushing it forward along `Ψ` and applying the two-variable
rigidity `Work.MotC.C6.exists_baseChange_eq_of_point_ratFunc2` twice exhibits its coordinates as the
base change of the coordinates of a point of `W` over `L`. -/
theorem exists_algebraMap_of_algHom_ratFunc {L : Type} [Field L] [DecidableEq L]
    [DecidableEq (RatFunc L)] [DecidableEq (RatFunc (RatFunc L))]
    (W : WeierstrassCurve L) (hΔ : W.Δ ≠ 0)
    (Ψ : WeierstrassCurve.Affine.FunctionField W →ₐ[L] RatFunc (RatFunc L)) :
    ∃ l : L, Ψ (genX W) = algebraMap L (RatFunc (RatFunc L)) l := by
  classical
  have hns := genX_genY_nonsingular W hΔ
  obtain ⟨Q₁, Q, hQ₁, hQ⟩ := exists_baseChange_eq_of_point_ratFunc2 (L := L) W hΔ
    (WeierstrassCurve.Affine.Point.map Ψ
      (WeierstrassCurve.Affine.Point.some (genX W) (genY W) hns))
  have hsome : WeierstrassCurve.Affine.Point.map Ψ
      (WeierstrassCurve.Affine.Point.some (genX W) (genY W) hns)
      = WeierstrassCurve.Affine.Point.some (Ψ (genX W)) (Ψ (genY W)) _ :=
    WeierstrassCurve.Affine.Point.map_some Ψ hns
  rw [hsome] at hQ₁
  have hQ₁ne : Q₁ ≠ 0 := by
    intro h
    rw [h] at hQ₁
    rw [WeierstrassCurve.Affine.Point.map_zero] at hQ₁
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hQ₁.symm
  rcases Q₁ with _ | ⟨q₁x, q₁y, hq₁⟩
  · exact absurd rfl hQ₁ne
  have hQne : Q ≠ 0 := by
    intro h
    rw [h] at hQ
    rw [WeierstrassCurve.Affine.Point.map_zero] at hQ
    exact hQ₁ne hQ.symm
  rcases Q with _ | ⟨qx, qy, hq⟩
  · exact absurd rfl hQne
  have hx : Ψ (genX W) = algebraMap (RatFunc L) (RatFunc (RatFunc L)) q₁x := by
    have h1 := hQ₁
    rw [WeierstrassCurve.Affine.Point.map_some] at h1
    simp only [Algebra.ofId_apply] at h1
    exact ((WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp h1).1.symm
  have hqx : q₁x = algebraMap L (RatFunc L) qx := by
    have h1 := hQ
    rw [WeierstrassCurve.Affine.Point.map_some] at h1
    simp only [Algebra.ofId_apply] at h1
    exact (((WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp h1).1).symm
  exact ⟨qx, by rw [hx, hqx, IsScalarTower.algebraMap_apply L (RatFunc L) (RatFunc (RatFunc L))]⟩

end C6

/-- **Audit node C6 (i).** `RatFunc K_P = K_P(t)` is not isomorphic over `𝕜` to the rational
function field `𝕜(u,v) = FractionRing (MvPolynomial (Fin 2) 𝕜)` of the plane: the twisted curve's
product with `ℙ¹` is not rational.

Intended route.  `twistField_tensor` gives that `A = ↥(twistField D α)` and `L = D.ext.L` are
linearly disjoint over `𝕜` with compositum `⊤` in `K = L(E)`; hence `A ⊗[𝕜] L ≃ₐ[L] K` (the
multiplication map `a ⊗ l ↦ a * l` is an `𝕜`-algebra hom by `Algebra.TensorProduct.lift`, injective
by linear disjointness, surjective because its image contains `A ⊔ L = ⊤`).  Tensoring with `L` and
localizing (`Frac(A[X]) ⊗[𝕜] L ≅ Frac((A ⊗[𝕜] L)[X])`, using that `A ⊗[𝕜] L` is a field) gives

  `RatFunc A ⊗[𝕜] L ≅ RatFunc (A ⊗[𝕜] L) ≅ RatFunc K = K(t) = L(E)(t)`,

and `FractionRing (MvPolynomial (Fin 2) 𝕜) ⊗[𝕜] L ≅ L(u,v)`.  A `𝕜`-isomorphism
`RatFunc A ≃ₐ[𝕜] 𝕜(u,v)` therefore base-changes to an `L`-algebra isomorphism
`φ : L(E)(t) ≅ L(u,v)`.  Now the generic point of `E` over `L(E)` base-changes through
`L(E) ⊆ L(E)(t) \xrightarrow{φ} L(u,v)` to a point of `E(L(u,v))`; `constantsOnly_all` applied
twice (with `M := L(u)` and with `M := L`) shows `E(L(u,v)) = E(L)`, so the image of the generic
point is constant: `φ(x) ∈ L` where `x` is the `x`-coordinate of the generic point.  Since `φ` is
injective, `φ` restricts to an injective `L`-algebra map `L(x) → L`; but `x` is transcendental over
`L`, so `trdeg L L(x) = 1 ≤ trdeg L L = 0`, a contradiction. -/
theorem not_algEquiv_ratFunc_mvPolynomial {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (TD : Work.MotC.TransData D)
    (h5 : (Work.MotC.twistAut D (TD.τ (Work.MotC.markPoint D))) ^ 5 = 1)
    (hne : Work.MotC.twistAut D (TD.τ (Work.MotC.markPoint D)) ≠ 1) :
    IsEmpty (RatFunc ↥(Work.MotC.twistField D (Work.MotC.twistAut D (TD.τ (Work.MotC.markPoint D))))
      ≃ₐ[𝕜] FractionRing (MvPolynomial (Fin 2) 𝕜)) := by
  classical
  rw [isEmpty_iff]
  intro θ
  obtain ⟨hLI, hsup, -⟩ :=
    Work.MotC.twistField_tensor D (TD.τ (Work.MotC.markPoint D)) h5 hne
  let F : IntermediateField 𝕜 (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) :=
    Work.MotC.twistField D (Work.MotC.twistAut D (TD.τ (Work.MotC.markPoint D)))
  have hΔE : D.E.Δ ≠ 0 := fun h =>
    (isUnit_iff_ne_zero.mp (WeierstrassCurve.isUnit_Δ D.E)) h
  have hΔ : (Work.MotC.baseCurve D).Δ ≠ 0 := by
    rw [Work.MotC.baseCurve]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact fun h => hΔE ((algebraMap 𝕜 D.ext.L).injective (by rw [h, map_zero]))
  have halg : Algebra.IsAlgebraic 𝕜 D.ext.L := Algebra.IsAlgebraic.of_finite 𝕜 D.ext.L
  have hfield : IsField (TensorProduct 𝕜 ↥F D.ext.L) :=
    hLI.isField_of_isAlgebraic (Or.inr halg)
  obtain ⟨e, he1, he2⟩ := Work.MotC.C6.exists_tensorAlgEquiv F hLI hfield hsup
  obtain ⟨g⟩ := Work.MotC.C6.exists_algHom_ratFunc_mvPolynomial (𝕜 := 𝕜) (L := D.ext.L)
  let f₁ : ↥F →ₐ[𝕜] RatFunc (RatFunc D.ext.L) :=
    g.comp (θ.toAlgHom.comp (IsScalarTower.toAlgHom 𝕜 ↥F (RatFunc ↥F)))
  let Φ : (↥F ⊗[𝕜] D.ext.L) →ₐ[𝕜] RatFunc (RatFunc D.ext.L) :=
    Algebra.TensorProduct.lift f₁ (IsScalarTower.toAlgHom 𝕜 D.ext.L (RatFunc (RatFunc D.ext.L)))
      (fun _ _ => Commute.all _ _)
  let Ψ : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) →ₐ[𝕜]
      RatFunc (RatFunc D.ext.L) := Φ.comp e.symm.toAlgHom
  have hΨL : ∀ l : D.ext.L,
      Ψ (algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) l)
        = algebraMap D.ext.L (RatFunc (RatFunc D.ext.L)) l := by
    intro l
    have h1 : e.symm (algebraMap D.ext.L
        (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) l)
        = TensorProduct.tmul 𝕜 (1 : ↥F) l := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply, he2 l]
    show Φ (e.symm (algebraMap D.ext.L _ l)) = algebraMap D.ext.L _ l
    rw [h1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  let Ψ' : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) →ₐ[D.ext.L]
      RatFunc (RatFunc D.ext.L) := { Ψ with commutes' := hΨL }
  obtain ⟨l, hl⟩ := Work.MotC.C6.exists_algebraMap_of_algHom_ratFunc (L := D.ext.L)
    (Work.MotC.baseCurve D) hΔ Ψ'
  have h2 : Ψ' (algebraMap D.ext.L
      (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) l)
      = algebraMap D.ext.L (RatFunc (RatFunc D.ext.L)) l := Ψ'.commutes l
  have hinj : Function.Injective (Ψ' : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) →
      RatFunc (RatFunc D.ext.L)) :=
    RingHom.injective (Ψ' : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) →+*
      RatFunc (RatFunc D.ext.L))
  have h4 : Ψ' (Work.MotC.C6.genX (Work.MotC.baseCurve D))
      = Ψ' (algebraMap D.ext.L
          (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) l) := by
    rw [hl, h2]
  have h3 : Work.MotC.C6.genX (Work.MotC.baseCurve D) = algebraMap D.ext.L
      (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) l := hinj h4
  exact Work.MotC.C6.genX_notMem_range (Work.MotC.baseCurve D) ⟨l, h3.symm⟩

end

end Work.MotC
