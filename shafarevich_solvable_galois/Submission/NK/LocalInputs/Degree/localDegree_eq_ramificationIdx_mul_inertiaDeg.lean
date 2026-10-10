import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.LocalInputs.Inputs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs.Degree

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The algebra map `𝓞 ℚ → 𝓞 K` is `(ℤ → 𝓞 K) ∘ Rat.ringOfIntegersEquiv`. -/
theorem rat_algMap {K : Type*} [Field K] [NumberField K] :
    (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)) =
      (algebraMap ℤ (NumberField.RingOfIntegers K)).comp
        (Rat.ringOfIntegersEquiv : NumberField.RingOfIntegers ℚ →+* ℤ) := by
  ext z
  rw [RingHom.comp_apply]
  have h1 : (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)) z
      = NumberField.RingOfIntegers.mapRingHom (algebraMap ℚ K) z := rfl
  rw [h1, NumberField.RingOfIntegers.mapRingHom_apply]
  change (algebraMap ℚ K) (algebraMap (NumberField.RingOfIntegers ℚ) ℚ z) =
    algebraMap (NumberField.RingOfIntegers K) K
      ((algebraMap ℤ (NumberField.RingOfIntegers K)) (Rat.ringOfIntegersEquiv z))
  rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers K) K,
      IsScalarTower.algebraMap_apply ℤ ℚ K]
  congr 1
  exact (Rat.ringOfIntegersEquiv_apply_coe z).symm

/-- The algebra map `ℤ → 𝓞 ℚ` is `Rat.ringOfIntegersEquiv.symm`. -/
theorem int_algMap {K : Type*} [Field K] [NumberField K] :
    (algebraMap ℤ (NumberField.RingOfIntegers ℚ)) =
      (Rat.ringOfIntegersEquiv.symm : ℤ →+* NumberField.RingOfIntegers ℚ) := by
  ext x
  simp

/-- `ℤ ⊆ 𝓞 ℚ ⊆ 𝓞 K` is a scalar tower. -/
theorem isScalarTower_int_rat {K : Type*} [Field K] [NumberField K] :
    IsScalarTower ℤ (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K) := by
  refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
  show (algebraMap ℤ (NumberField.RingOfIntegers K)) x =
    (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K))
      ((algebraMap ℤ (NumberField.RingOfIntegers ℚ)) x)
  rw [int_algMap (K := K), rat_algMap (K := K), RingHom.comp_apply]
  exact congrArg (algebraMap ℤ (NumberField.RingOfIntegers K))
    (Rat.ringOfIntegersEquiv.apply_symm_apply x).symm

/-- The prime of `𝓞 ℚ` under `q` is the preimage, along `Rat.ringOfIntegersEquiv`, of the prime
of `ℤ` under `q`. -/
theorem under_rat {K : Type*} [Field K] [NumberField K]
    (q : Ideal (NumberField.RingOfIntegers K)) :
    q.under (NumberField.RingOfIntegers ℚ) =
      (q.under ℤ).comap (Rat.ringOfIntegersEquiv : NumberField.RingOfIntegers ℚ →+* ℤ) := by
  rw [Ideal.under_def, Ideal.under_def, rat_algMap (K := K),
    ← Ideal.comap_comap (Rat.ringOfIntegersEquiv : NumberField.RingOfIntegers ℚ →+* ℤ)
      (algebraMap ℤ (NumberField.RingOfIntegers K))]

/-- `Rat.ringOfIntegersEquiv` maps the prime of `𝓞 ℚ` under `q` to the prime of `ℤ` under `q`. -/
theorem map_under_rat {K : Type*} [Field K] [NumberField K]
    (q : Ideal (NumberField.RingOfIntegers K)) :
    (q.under (NumberField.RingOfIntegers ℚ)).map
        (Rat.ringOfIntegersEquiv : NumberField.RingOfIntegers ℚ →+* ℤ) = q.under ℤ := by
  rw [under_rat (K := K)]
  exact Ideal.map_comap_of_surjective _ Rat.ringOfIntegersEquiv.surjective _

/-- Extending the prime under `q` from `𝓞 ℚ` to `𝓞 K` agrees with extending it from `ℤ`. -/
theorem ideal_eq {K : Type*} [Field K] [NumberField K]
    (q : Ideal (NumberField.RingOfIntegers K)) :
    (q.under (NumberField.RingOfIntegers ℚ)).map
        (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)) =
      (q.under ℤ).map (algebraMap ℤ (NumberField.RingOfIntegers K)) := by
  rw [rat_algMap (K := K), ← Ideal.map_map, map_under_rat (K := K)]

/-- The ramification index of `q` over `ℤ` agrees with its ramification index over `𝓞 ℚ`. -/
theorem ramificationIdx_rat_eq {K : Type*} [Field K] [NumberField K]
    (q : Ideal (NumberField.RingOfIntegers K)) (hq : q ≠ ⊥) [_hqp : q.IsPrime] :
    q.ramificationIdx (NumberField.RingOfIntegers ℚ) = q.ramificationIdx ℤ := by
  have hunderZ : q.under ℤ ≠ ⊥ := Ideal.under_ne_bot ℤ hq
  have hunderQ : q.under (NumberField.RingOfIntegers ℚ) ≠ ⊥ := by
    intro h
    exact hunderZ (by rw [← map_under_rat (K := K), h]; simp)
  have h1 : q.ramificationIdx ℤ =
      (UniqueFactorizationMonoid.factors
        ((q.under ℤ).map (algebraMap ℤ (NumberField.RingOfIntegers K)))).count q :=
    Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count (q.under ℤ) q
      (Ideal.map_ne_bot_of_ne_bot hunderZ)
  have h2 : q.ramificationIdx (NumberField.RingOfIntegers ℚ) =
      (UniqueFactorizationMonoid.factors
        ((q.under (NumberField.RingOfIntegers ℚ)).map
          (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)))).count q :=
    Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count
      (q.under (NumberField.RingOfIntegers ℚ)) q (Ideal.map_ne_bot_of_ne_bot hunderQ)
  rw [h2, h1, ideal_eq (K := K)]

/-- The residue field of `𝓞 ℚ` at the prime under `q` and the residue field of `ℤ` at the prime
under `q` give the same degree to the residue field of `q`. -/
theorem finrank_quot_eq {K : Type*} [Field K] [NumberField K]
    (q : Ideal (NumberField.RingOfIntegers K)) :
    Module.finrank (NumberField.RingOfIntegers ℚ ⧸ q.under (NumberField.RingOfIntegers ℚ))
        (NumberField.RingOfIntegers K ⧸ q)
      = Module.finrank (ℤ ⧸ q.under ℤ) (NumberField.RingOfIntegers K ⧸ q) := by
  refine Algebra.finrank_eq_of_equiv_equiv
    (Ideal.quotientEquiv (q.under (NumberField.RingOfIntegers ℚ)) (q.under ℤ)
      Rat.ringOfIntegersEquiv (map_under_rat (K := K) q).symm) (RingEquiv.refl _) ?_
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.refl_apply, RingHom.id_apply]
  rw [Ideal.quotientEquiv_mk, Ideal.Quotient.algebraMap_mk_of_liesOver,
    Ideal.Quotient.algebraMap_mk_of_liesOver, rat_algMap (K := K), RingHom.comp_apply,
    RingEquiv.coe_toRingHom]

/-- The inertia degree of `q` over `ℤ` agrees with its inertia degree over `𝓞 ℚ`. -/
theorem inertiaDeg_rat_eq {K : Type*} [Field K] [NumberField K]
    (q : Ideal (NumberField.RingOfIntegers K)) (hq : q ≠ ⊥) [hqp : q.IsPrime] :
    q.inertiaDeg (NumberField.RingOfIntegers ℚ) = q.inertiaDeg ℤ := by
  have hunderZ : q.under ℤ ≠ ⊥ := Ideal.under_ne_bot ℤ hq
  have hunderQ : q.under (NumberField.RingOfIntegers ℚ) ≠ ⊥ := by
    intro h
    exact hunderZ (by rw [← map_under_rat (K := K), h]; simp)
  have hqmax : q.IsMaximal := hqp.isMaximal hq
  haveI := hqmax
  haveI : (q.under ℤ).IsMaximal :=
    (inferInstance : (q.under ℤ).IsPrime).isMaximal hunderZ
  haveI : (q.under (NumberField.RingOfIntegers ℚ)).IsMaximal :=
    (inferInstance : (q.under (NumberField.RingOfIntegers ℚ)).IsPrime).isMaximal hunderQ
  rw [Ideal.inertiaDeg_eq_of_isMaximal (q.under (NumberField.RingOfIntegers ℚ)) q,
    Ideal.inertiaDeg_eq_of_isMaximal (q.under ℤ) q, finrank_quot_eq (K := K) q]

/-- **The absolute local degree is the product of ramification index and inertia degree.**

For a number field `K` and a finite prime `𝔭`, the degree `[K_𝔭 : ℚ_p]` of the completion, computed
as the dimension of `𝔭.adicCompletion K` over the `p`-adic field `(primeBelow K 𝔭).adicCompletion ℚ`,
equals `e(𝔭/p) · f(𝔭/p)`. -/
theorem localDegree_eq_ramificationIdx_mul_inertiaDeg {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.LocalInputs.localDegree K 𝔭 = 𝔭.asIdeal.ramificationIdx ℤ * 𝔭.asIdeal.inertiaDeg ℤ := by
  rw [NK.LocalInputs.localDegree]
  rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
    (K := ℚ) (L := K) (NK.LocalInputs.primeBelow K 𝔭) 𝔭
    (NK.LocalInputs.primeBelow_liesOver K 𝔭)]
  rw [ramificationIdx_rat_eq 𝔭.asIdeal 𝔭.ne_bot, inertiaDeg_rat_eq 𝔭.asIdeal 𝔭.ne_bot]

end

end NK.LocalInputs.Degree
