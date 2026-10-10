import Mathlib.Tactic.Have
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.HeckeL.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace NK.HeckeL.Basic

/-- The idèle attached to the product of two nonzero ideals is the product of the idèles attached
to the factors: the local exponents (the `q`-adic orders of vanishing) are additive. -/
theorem ideleOfIdeal_mul_aux {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    NK.HeckeL.ideleOfIdeal K (I * J) =
      NK.HeckeL.ideleOfIdeal K I * NK.HeckeL.ideleOfIdeal K J := by
  have hI' : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    simpa [FractionalIdeal.coeIdeal_ne_zero] using hI
  have hJ' : (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    simpa [FractionalIdeal.coeIdeal_ne_zero] using hJ
  apply NK.GlobalCFT.Idele.ext
  intro v
  rw [NK.GlobalCFT.Idele.mul_apply]
  match v with
  | Sum.inl w =>
      show (1 : (NK.GlobalCFT.Place.localField K (Sum.inl w))ˣ) = 1 * 1
      simp
  | Sum.inr q =>
      show NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^
          (FractionalIdeal.count K q (↑(I * J) : FractionalIdeal (𝓞 K)⁰ K)) =
        NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^
            (FractionalIdeal.count K q (I : FractionalIdeal (𝓞 K)⁰ K)) *
          NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^
            (FractionalIdeal.count K q (J : FractionalIdeal (𝓞 K)⁰ K))
      rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K q hI' hJ', zpow_add]

theorem classOfIdeal_mul {K : Type*} [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (I J : Ideal (NumberField.RingOfIntegers K))
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    NK.HeckeL.classOfIdeal K U (I * J) =
      NK.HeckeL.classOfIdeal K U I * NK.HeckeL.classOfIdeal K U J := by
  have hmain := ideleOfIdeal_mul_aux (K := K) I J hI hJ
  unfold NK.HeckeL.classOfIdeal
  rw [hmain, map_mul, map_mul]

end NK.HeckeL.Basic
