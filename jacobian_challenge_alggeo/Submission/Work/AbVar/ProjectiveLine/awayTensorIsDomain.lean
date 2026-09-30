import Mathlib
import Submission.Work.AbVar.ProjectiveLine.chart
import Submission.Work.AbVar.ProjectiveLine.polyToAwaySurjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.AbVar.ProjectiveLine

open HomogeneousLocalization Polynomial

/-- The other index in `Fin 2`. -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

lemma other_ne (i : Fin 2) : other i ≠ i := by
  unfold other
  split_ifs with h
  · rw [h]; decide
  · exact fun hh => h hh.symm

section

variable (k : Type*) [Field k]

/-- Key computation: the algebra map `↥(𝒜 0)[T] → Away 𝒜 (X i)` sending `T ↦ X j / X i`
agrees with `polyToAway` after transporting coefficients along `k ≅ ↥(𝒜 0)`. -/
lemma aeval_mapEquiv (i j : Fin 2) (p : Polynomial k) :
    Polynomial.aeval (R := ↥(StdG k 0)) (awayU (R := k) i j)
      ((Polynomial.mapEquiv (constToZeroEquiv (R := k))) p)
      = polyToAway (R := k) i j p := by
  let ψ : Polynomial k →ₐ[k] HomogeneousLocalization.Away (StdG k) (MvPolynomial.X i) :=
    { toRingHom := (Polynomial.aeval (R := ↥(StdG k 0)) (awayU (R := k) i j)).toRingHom.comp
        (Polynomial.mapEquiv (constToZeroEquiv (R := k))).toRingHom
      commutes' := fun r => by
        show Polynomial.aeval (R := ↥(StdG k 0)) (awayU (R := k) i j)
            ((Polynomial.mapEquiv (constToZeroEquiv (R := k))) ((algebraMap k (Polynomial k)) r))
          = (algebraMap k (HomogeneousLocalization.Away (StdG k) (MvPolynomial.X i))) r
        rw [show (algebraMap k (Polynomial k)) r = Polynomial.C r from rfl]
        rw [show (Polynomial.mapEquiv (constToZeroEquiv (R := k))) (Polynomial.C r)
            = Polynomial.C (constToZeroEquiv (R := k) r) by
              rw [Polynomial.mapEquiv_apply, Polynomial.map_C]; rfl]
        rw [Polynomial.aeval_C]
        show (fromZeroRingHom (StdG k) (Submonoid.powers (MvPolynomial.X i))) (constToZero r)
            = (algebraMap k (HomogeneousLocalization.Away (StdG k) (MvPolynomial.X i))) r
        rw [algebraMap_awayAlg, awayAlg]
        rfl }
  have hψ : ψ = polyToAway (R := k) i j := by
    apply Polynomial.algHom_ext
    show Polynomial.aeval (R := ↥(StdG k 0)) (awayU (R := k) i j)
        ((Polynomial.mapEquiv (constToZeroEquiv (R := k))) Polynomial.X)
      = (polyToAway (R := k) i j) Polynomial.X
    rw [show (Polynomial.mapEquiv (constToZeroEquiv (R := k))) Polynomial.X = Polynomial.X from
      Polynomial.map_X _]
    rw [Polynomial.aeval_X, polyToAway_X]
  have : ψ p = polyToAway (R := k) i j p := by rw [hψ]
  simpa [ψ] using this

/-- The composite identity in the form used for injectivity. -/
lemma aeval_eq_symm (i j : Fin 2) (p : Polynomial ↥(StdG k 0)) :
    Polynomial.aeval (R := ↥(StdG k 0)) (awayU (R := k) i j) p
      = polyToAway (R := k) i j ((Polynomial.mapEquiv (constToZeroEquiv (R := k))).symm p) := by
  have h := aeval_mapEquiv (k := k) i j
    ((Polynomial.mapEquiv (constToZeroEquiv (R := k))).symm p)
  rw [show (Polynomial.mapEquiv (constToZeroEquiv (R := k)))
      ((Polynomial.mapEquiv (constToZeroEquiv (R := k))).symm p) = p from
        RingEquiv.apply_symm_apply _ _] at h
  exact h

/-- The `↥(𝒜 0)`-algebra map `↥(𝒜 0)[T] → Away 𝒜 (X i)`, `T ↦ X j / X i`, is bijective. -/
lemma aeval_awayU_bijective (i : Fin 2) :
    Function.Bijective (Polynomial.aeval (R := ↥(StdG k 0))
      (awayU (R := k) i (other i))) := by
  refine ⟨fun p q h => ?_, fun b => ?_⟩
  · have h' : polyToAway (R := k) i (other i)
          ((Polynomial.mapEquiv (constToZeroEquiv (R := k))).symm p)
        = polyToAway (R := k) i (other i)
          ((Polynomial.mapEquiv (constToZeroEquiv (R := k))).symm q) := by
      rw [← aeval_eq_symm (k := k) i (other i) p, ← aeval_eq_symm (k := k) i (other i) q, h]
    exact (Polynomial.mapEquiv (constToZeroEquiv (R := k))).symm.injective
      (polyToAway_injective (R := k) (other_ne i) h')
  · obtain ⟨p, hp⟩ := polyToAwaySurjective (R := k) (other_ne i) b
    exact ⟨(Polynomial.mapEquiv (constToZeroEquiv (R := k))) p,
      by rw [aeval_mapEquiv (k := k) i (other i) p, hp]⟩

end

theorem awayTensorIsDomain (k : Type*) [Field k] (i : Fin 2) (K : Type*) [Field K]
    [Algebra ↥(Work.AbVar.ProjectiveLine.StdG k 0) K] :
    IsDomain (TensorProduct ↥(Work.AbVar.ProjectiveLine.StdG k 0)
      (HomogeneousLocalization (Work.AbVar.ProjectiveLine.StdG k)
        (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))) K) := by
  let A := ↥(StdG k 0)
  let B := HomogeneousLocalization (StdG k)
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
  let e : Polynomial A ≃ₐ[A] B :=
    AlgEquiv.ofBijective (Polynomial.aeval (R := A) (awayU (R := k) i (other i)))
      (aeval_awayU_bijective k i)
  refine MulEquiv.isDomain (Polynomial K) ?_
  exact (((Algebra.TensorProduct.congr e
      (AlgEquiv.refl : K ≃ₐ[A] K)).symm).toRingEquiv.trans
    ((Algebra.TensorProduct.comm A (Polynomial A) K).toRingEquiv.trans
      (polyEquivTensor' A K).symm.toRingEquiv)).toMulEquiv

end Work.AbVar.ProjectiveLine
