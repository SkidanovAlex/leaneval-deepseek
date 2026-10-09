/-
# The Chinese-remainder algebra equivalence `K ⊗[ℚ] ℚ_p ≅ ∏_{Q | Q₀} K_Q`, with its formula

This is the `z ↦ (z_Q)_Q` clause of the standard isomorphism, which the library lemma
`Commons.…Completion.exists_algEquiv_tensor_adicCompletion_prod` produces only as an abstract
`Nonempty`.

Together with `trace_tensorProduct_tmul` and `trace_pi_apply` it gives the local–global trace
identity `∑_Q Tr_{K_Q/ℚ_p}(z) = Tr_{K/ℚ}(z)`
(`FinitenessHM/sum_trace_adicCompletion_eq_trace.lean`).
-/
import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.completionSetup
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.trace_tensorProduct_tmul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open IsDedekindDomain

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem adicCompletion_algEquiv_tensor_tmul {K : Type*} [Field K] [NumberField K]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    [Fintype {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
      Q.asIdeal.LiesOver Q0.asIdeal}] :
    letI : Algebra (Q0.adicCompletion ℚ) (TensorProduct ℚ K (Q0.adicCompletion ℚ)) :=
      Algebra.TensorProduct.rightAlgebra
    letI : ∀ Q : {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
        Q.asIdeal.LiesOver Q0.asIdeal},
        Algebra (Q0.adicCompletion ℚ) (Q.1.adicCompletion K) :=
      fun Q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q.1 Q.2)
    ∃ e : (TensorProduct ℚ K (Q0.adicCompletion ℚ)) ≃ₐ[Q0.adicCompletion ℚ]
        (∀ Q : {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
          Q.asIdeal.LiesOver Q0.asIdeal}, Q.1.adicCompletion K),
      ∀ z : K, e (TensorProduct.mk ℚ K (Q0.adicCompletion ℚ) z 1)
        = (fun Q : {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
            Q.asIdeal.LiesOver Q0.asIdeal} => algebraMap K (Q.1.adicCompletion K) z) := by
  classical
  let F := Q0.adicCompletion ℚ
  let A := TensorProduct ℚ K F
  let ι := {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
      Q.asIdeal.LiesOver Q0.asIdeal}
  letI : Fintype ι :=
    Fintype.ofEquiv _ (Commons.NumberTheory.NumberField.Completion.primesOverEquiv Q0).symm
  letI : ∀ Q : ι, Algebra F (Q.1.adicCompletion K) :=
    fun Q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q.1 Q.2)
  letI : ∀ Q : ι, Module.Finite F (Q.1.adicCompletion K) :=
    fun Q => Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q0 Q.1 Q.2
  haveI : Module.Finite F A := by
    haveI : Module.Finite F (F ⊗[ℚ] K) := inferInstance
    exact Module.Finite.equiv (M := F ⊗[ℚ] K) (N := K ⊗[ℚ] F)
      (Commons.LinearAlgebra.Dimension.flipRight ℚ K F).symm
  let φ : ∀ Q : ι, A →+* Q.1.adicCompletion K := fun Q =>
    Classical.choose
      (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon Q0 Q.1 Q.2)
  have hφ_formula : ∀ (Q : ι) (z : K) (f : F),
      φ Q (z ⊗ₜ[ℚ] f) = (algebraMap K (Q.1.adicCompletion K) z) *
        (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q.1 Q.2 f) := fun Q =>
    (Classical.choose_spec
      (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon
        Q0 Q.1 Q.2)).2
  have hφ_surj : ∀ Q : ι, Function.Surjective (φ Q) := fun Q =>
    (Classical.choose_spec
      (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon
        Q0 Q.1 Q.2)).1
  have hlin : ∀ Q : ι, ∀ (f : F) (x : A), φ Q (f • x) = f • (φ Q x) := by
    intro Q f x
    have h1 : f • x = (1 ⊗ₜ[ℚ] f : A) * x := by
      rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply]
    have h2 : φ Q (1 ⊗ₜ[ℚ] f) =
        (Commons.RingTheory.Henselian.adicCompletionMap Q0 Q.1 Q.2) f := by
      rw [hφ_formula Q 1 f, map_one, one_mul]
    rw [h1, map_mul, h2, Algebra.smul_def]
    congr 1
  have hcop : Pairwise fun i j : ι => IsCoprime (RingHom.ker (φ i)) (RingHom.ker (φ j)) := by
    intro i j hij
    have hne : i.1.asIdeal ≠ j.1.asIdeal := by
      intro hIJ
      exact hij (Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext hIJ))
    exact Commons.NumberTheory.NumberField.Completion.adicCompletionMap_kernels_coprime
      Q0 i.1 j.1 i.2 j.2 hne
  have hdim : (∑ Q : ι, Module.finrank F (Q.1.adicCompletion K)) = Module.finrank F A := by
    have hbase : Module.finrank F A = Module.finrank ℚ K :=
      Commons.LinearAlgebra.Dimension.tensor_field_baseChange_finrank (K := ℚ) (L := K) (F := F)
    rw [hbase, ← Commons.NumberTheory.NumberField.Completion.sum_finrank_adicCompletion_eq_finrank
      (K := ℚ) (L := K) Q0]
    refine Fintype.sum_equiv (Commons.NumberTheory.NumberField.Completion.primesOverEquiv Q0) _ _ ?_
    intro q
    dsimp only
    congr 1
  -- Chinese remainder + dimension count, with the map exposed
  let Φ : A →+* (∀ Q : ι, Q.1.adicCompletion K) := RingHom.pi φ
  have hΦsurj : Function.Surjective Φ := by
    intro y
    choose a ha using fun Q => hφ_surj Q (y Q)
    obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal (I := fun Q => RingHom.ker (φ Q)) hcop a
    refine ⟨r, funext fun Q => ?_⟩
    have hz : φ Q (r - a Q) = 0 := by
      have h := hr Q
      rwa [RingHom.mem_ker] at h
    have hsub : φ Q r - φ Q (a Q) = 0 := by rw [← map_sub]; exact hz
    have hthis : φ Q r = φ Q (a Q) := sub_eq_zero.mp hsub
    change φ Q r = y Q
    rw [hthis, ha Q]
  have hΦcomm : ∀ f : F, Φ (algebraMap F A f) =
      algebraMap F (∀ Q : ι, Q.1.adicCompletion K) f := by
    intro f
    funext Q
    have h1 : algebraMap F A f = f • (1 : A) := by rw [Algebra.smul_def, mul_one]
    rw [h1]
    change φ Q (f • (1 : A)) = (algebraMap F (Q.1.adicCompletion K)) f
    rw [hlin Q f 1, map_one, Algebra.smul_def, mul_one]
  let Φa : A →ₐ[F] (∀ Q : ι, Q.1.adicCompletion K) := AlgHom.mk Φ hΦcomm
  have hsurjA : Function.Surjective (Φa : A →ₗ[F] (∀ Q : ι, Q.1.adicCompletion K)) := by
    intro y
    obtain ⟨a, ha⟩ := hΦsurj y
    exact ⟨a, ha⟩
  have hfr : Module.finrank F A = Module.finrank F (∀ Q : ι, Q.1.adicCompletion K) := by
    rw [Module.finrank_pi_fintype F, hdim]
  have hinj : Function.Injective Φa :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mpr hsurjA
  let e : A ≃ₐ[F] (∀ Q : ι, Q.1.adicCompletion K) := AlgEquiv.ofBijective Φa ⟨hinj, hsurjA⟩
  refine ⟨e, fun z => ?_⟩
  funext Q
  change φ Q (z ⊗ₜ[ℚ] (1 : F)) = algebraMap K (Q.1.adicCompletion K) z
  rw [hφ_formula Q z 1, map_one, mul_one]

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
