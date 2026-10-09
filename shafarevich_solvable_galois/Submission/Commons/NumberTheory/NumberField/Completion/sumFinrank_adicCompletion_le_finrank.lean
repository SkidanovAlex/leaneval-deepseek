import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon
import Submission.Commons.LinearAlgebra.Dimension.tensor_field_baseChange_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_kernels_coprime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField TensorProduct
set_option autoImplicit false
set_option linter.style.haveILetI false
attribute [local instance] Algebra.TensorProduct.rightAlgebra
noncomputable section

open IsDedekindDomain.HeightOneSpectrum
open Commons.RingTheory.Henselian
open BigOperators

namespace Commons.NumberTheory.NumberField.Completion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The `e qq` gadget: each `qq ∈ primesOver Q` names a `HeightOneSpectrum` of `𝓞 L`. -/
noncomputable def sumFinrank_eQ (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Q.asIdeal.primesOver (𝓞 L) → IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
  fun qq => IsDedekindDomain.HeightOneSpectrum.mk qq.1 qq.2.1
    (Ideal.ne_bot_of_mem_primesOver (A := 𝓞 K) (B := 𝓞 L) Q.ne_bot qq.2)

/-- The canonical surjective hom `L ⊗_K K_Q → L_q` (per prime `q` over `Q`). -/
noncomputable def sumFinrank_phiRing (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    (L ⊗[K] Q.adicCompletion K) →+* q.adicCompletion L :=
  Classical.choose (exists_surjective_ringHom_tensor_completion_canon Q q hq)

lemma sumFinrank_phiRing_tmul (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (l : L) (f : Q.adicCompletion K) :
    sumFinrank_phiRing Q q hq (l ⊗ₜ[K] f) =
      (algebraMap L (q.adicCompletion L) l) * (adicCompletionMap Q q hq f) :=
  (Classical.choose_spec (exists_surjective_ringHom_tensor_completion_canon Q q hq)).2 l f

/-- kernel of the per-prime map, as an ideal of `L ⊗_K K_Q`. -/
noncomputable def sumFinrank_mQ (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Ideal (L ⊗[K] Q.adicCompletion K) :=
  RingHom.ker (sumFinrank_phiRing Q q hq)

/-- `sumFinrank_phiRing` commutes with the `K_Q`-algebra maps, i.e. is a `K_Q`-algebra
homomorphism. -/
lemma sumFinrank_phiRing_algebraMap (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (f : Q.adicCompletion K) :
    sumFinrank_phiRing Q q hq (algebraMap (Q.adicCompletion K)
        (L ⊗[K] Q.adicCompletion K) f) =
      adicCompletionMap Q q hq f := by
  rw [Algebra.TensorProduct.right_algebraMap_apply (R := K) (A := L) (B := Q.adicCompletion K) f]
  rw [sumFinrank_phiRing_tmul Q q hq (1 : L) f]
  simp

/-- Base-change dimension: `finrank_{K_Q} (L ⊗_K K_Q) = finrank_K L`. -/
lemma sumFinrank_tensorBase_finrank (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Module.finrank (Q.adicCompletion K) (L ⊗[K] Q.adicCompletion K) =
      Module.finrank K L := by
  simpa using (Commons.LinearAlgebra.Dimension.tensor_field_baseChange_finrank (K := K) (L := L)
    (F := Q.adicCompletion K))

/-- `L ⊗_K K_Q` is finite over `K_Q` (base change of the finite extension `L / K`). -/
lemma sumFinrank_moduleFinite_base (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Module.Finite (Q.adicCompletion K) (L ⊗[K] Q.adicCompletion K) := by
  let F := Q.adicCompletion K
  let b := Module.Free.chooseBasis K L
  let bF : Module.Basis (Module.Free.ChooseBasisIndex K L) F (F ⊗[K] L) :=
    Module.Basis.baseChange (S := F) b
  haveI : Module.Finite F (F ⊗[K] L) := Module.Finite.of_basis bF
  have hflip : (L ⊗[K] F) ≃ₗ[F] (F ⊗[K] L) :=
    Commons.LinearAlgebra.Dimension.flipRight K L F
  exact Module.Finite.equiv hflip.symm

/-- For a prime `q` over `Q`, the local degree `[L_q : K_Q]` (module structure via
`adicCompletionMap`) equals the `K_Q`-dimension of the quotient of `L ⊗_K K_Q` by the kernel of
the canonical map. -/
lemma sumFinrank_quotient_degree_eq (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Module.finrank (Q.adicCompletion K)
        ((L ⊗[K] Q.adicCompletion K) ⧸ sumFinrank_mQ Q q hq) =
      @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        (RingHom.toAlgebra (adicCompletionMap Q q hq)).toModule := by
  classical
  let F := Q.adicCompletion K
  let V := L ⊗[K] F
  letI : Algebra F (q.adicCompletion L) := RingHom.toAlgebra (adicCompletionMap Q q hq)
  have hsurj : Function.Surjective ⇑(sumFinrank_phiRing Q q hq) :=
    (Classical.choose_spec (exists_surjective_ringHom_tensor_completion_canon Q q hq)).1
  let ψ : (V ⧸ sumFinrank_mQ Q q hq) →ₐ[F] q.adicCompletion L :=
    AlgHom.mk (RingHom.kerLift (sumFinrank_phiRing Q q hq)) (by
      intro r
      change (RingHom.kerLift (sumFinrank_phiRing Q q hq))
          (Ideal.Quotient.mk (RingHom.ker (sumFinrank_phiRing Q q hq)) (algebraMap F V r)) =
          adicCompletionMap Q q hq r
      rw [RingHom.kerLift_mk]
      exact sumFinrank_phiRing_algebraMap Q q hq r)
  have hbij : Function.Bijective ⇑ψ := by
    constructor
    · exact RingHom.kerLift_injective (sumFinrank_phiRing Q q hq)
    · intro y
      rcases hsurj y with ⟨a, ha⟩
      refine ⟨Ideal.Quotient.mk (sumFinrank_mQ Q q hq) a, ?_⟩
      change (RingHom.kerLift (sumFinrank_phiRing Q q hq))
          (Ideal.Quotient.mk (RingHom.ker (sumFinrank_phiRing Q q hq)) a) = y
      rw [RingHom.kerLift_mk]
      exact ha
  let e : (V ⧸ sumFinrank_mQ Q q hq) ≃ₐ[F] q.adicCompletion L := AlgEquiv.ofBijective ψ hbij
  let el := AlgEquiv.toLinearEquiv e
  change Module.finrank F ((V ⧸ sumFinrank_mQ Q q hq)) =
      Module.finrank F (q.adicCompletion L)
  exact el.finrank_eq

/-- If pairwise-coprime ideals of a finite `F`-algebra are quotiented, the sum of the dimensions
of the quotients is bounded by the dimension of the algebra (module Chinese-remainder theorem,
`Ideal.pi_mkQ_surjective`). -/
lemma sumFinrank_finrank_sum_quotient_le {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    {A : Type*} [CommRing A] [Algebra F A] [Module.Finite F A]
    (m : ι → Ideal A) (hcop : Pairwise (Function.onFun IsCoprime m)) :
    (∑ i : ι, Module.finrank F (A ⧸ m i)) ≤ Module.finrank F A := by
  classical
  have hd : Function.Surjective ⇑(LinearMap.pi (fun i : ι => (m i).mkQ)) :=
    Ideal.pi_mkQ_surjective hcop
  haveI : ∀ i, Module.Finite F (A ⧸ m i) := by
    intro i
    exact Module.Finite.quotient F (m i)
  have hle : Module.finrank F (∀ i : ι, A ⧸ m i) ≤ Module.finrank F A := by
    refine LinearMap.finrank_le_finrank_of_surjective (R := F)
      (f := LinearMap.pi (fun i : ι => (m i).mkQ)) hd
  have hpi : Module.finrank F (∀ i : ι, A ⧸ m i) = ∑ i : ι, Module.finrank F (A ⧸ m i) := by
    exact Module.finrank_pi_fintype F
  rwa [hpi] at hle

/-- The kernels `sumFinrank_mQ` are pairwise coprime: the canonical surjections onto the
completions at distinct primes over `Q` have comaximal kernels
(`Commons.NumberTheory.NumberField.Completion.adicCompletionMap_kernels_coprime`). -/
lemma sumFinrank_mQ_pairwise_coprime (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    let m : Q.asIdeal.primesOver (𝓞 L) → Ideal (L ⊗[K] Q.adicCompletion K) :=
      fun qq => sumFinrank_mQ Q (sumFinrank_eQ Q qq) qq.2.2
    Pairwise (Function.onFun IsCoprime m) := by
  classical
  dsimp
  intro qq1 qq2 hne
  let q1 := sumFinrank_eQ Q qq1
  let q2 := sumFinrank_eQ Q qq2
  have hq1 : q1.asIdeal.LiesOver Q.asIdeal := qq1.2.2
  have hq2 : q2.asIdeal.LiesOver Q.asIdeal := qq2.2.2
  have hne' : q1.asIdeal ≠ q2.asIdeal := by
    intro hI
    apply hne
    apply Subtype.ext
    simpa [q1, q2, sumFinrank_eQ] using hI
  change IsCoprime (sumFinrank_mQ Q q1 hq1) (sumFinrank_mQ Q q2 hq2)
  change IsCoprime (RingHom.ker (sumFinrank_phiRing Q q1 hq1))
      (RingHom.ker (sumFinrank_phiRing Q q2 hq2))
  exact adicCompletionMap_kernels_coprime Q q1 q2 hq1 hq2 hne'

/-- Upper bound in the sum-of-local-degrees identity for adic completions of number fields.

Let `L / K` be an extension of number fields and `Q` a height-one prime of the ring of
integers of `K`.  For each prime `qq` of `𝓞 L` lying over `Q` let `L_qq` be the `qq`-adic
completion of `L`, viewed as a module over the `Q`-adic completion `K_Q` of `K` through the
continuous algebra map `Commons.RingTheory.Henselian.adicCompletionMap Q (e qq) qq.2.2`.

Then the sum of the local degrees `[L_qq : K_Q]` over all primes `qq` over `Q` is at most the
global degree `[L : K]`. -/
theorem sumFinrank_adicCompletion_le_finrank
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    let e : Q.asIdeal.primesOver (NumberField.RingOfIntegers L) →
        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
      fun qq => IsDedekindDomain.HeightOneSpectrum.mk qq.1 qq.2.1
        (Ideal.ne_bot_of_mem_primesOver (A := NumberField.RingOfIntegers K)
          (B := NumberField.RingOfIntegers L) Q.ne_bot qq.2)
    (∑ qq : Q.asIdeal.primesOver (NumberField.RingOfIntegers L),
        @Module.finrank (Q.adicCompletion K) ((e qq).adicCompletion L) _ _
          (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q (e qq) qq.2.2)).toModule) ≤
      Module.finrank K L := by
  classical
  change (∑ qq : Q.asIdeal.primesOver (𝓞 L),
        @Module.finrank (Q.adicCompletion K) ((sumFinrank_eQ Q qq).adicCompletion L) _ _
          (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q
            (sumFinrank_eQ Q qq) qq.2.2)).toModule) ≤
      Module.finrank K L
  let F := Q.adicCompletion K
  let V := L ⊗[K] F
  let m : Q.asIdeal.primesOver (𝓞 L) → Ideal V :=
    fun qq => sumFinrank_mQ Q (sumFinrank_eQ Q qq) qq.2.2
  have hcop : Pairwise (Function.onFun IsCoprime m) := by
    simpa [m] using (sumFinrank_mQ_pairwise_coprime (K := K) (L := L) Q)
  haveI : Module.Finite F V := sumFinrank_moduleFinite_base (K := K) (L := L) Q
  have hsum : (∑ qq : Q.asIdeal.primesOver (𝓞 L), Module.finrank F (V ⧸ m qq)) ≤
      Module.finrank F V := by
    exact sumFinrank_finrank_sum_quotient_le (A := V) m hcop
  calc
    (∑ qq : Q.asIdeal.primesOver (𝓞 L),
        @Module.finrank (Q.adicCompletion K) ((sumFinrank_eQ Q qq).adicCompletion L) _ _
          (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q
            (sumFinrank_eQ Q qq) qq.2.2)).toModule)
        = ∑ qq : Q.asIdeal.primesOver (𝓞 L), Module.finrank F (V ⧸ m qq) := by
          apply Finset.sum_congr rfl
          intro qq hqq
          exact (sumFinrank_quotient_degree_eq (K := K) (L := L) Q (sumFinrank_eQ Q qq) qq.2.2).symm
    _ ≤ Module.finrank F V := hsum
    _ = Module.finrank K L := sumFinrank_tensorBase_finrank (K := K) (L := L) Q

end Commons.NumberTheory.NumberField.Completion
