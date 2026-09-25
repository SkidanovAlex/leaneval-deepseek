import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon
import Submission.Commons.NumberTheory.NumberField.Completion.sum_finrank_adicCompletion_eq_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_tensor_adicCompletion_prod

open NumberField
open scoped TensorProduct Valued
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum

/-- **Chinese remainder + dimension count, `F`-algebra form.**  Let `F` be a field and `A` a
commutative `F`-algebra which is finite-dimensional as an `F`-vector space.  Let `(B i)_{i ∈ ι}`
be a finite family of `F`-algebras, and let `φ i : A →+* B i` be `F`-linear surjections whose
kernels are pairwise coprime.  If the dimensions match, `∑ᵢ dim B i = dim A`, then the product
map `A → ∏ᵢ B i` is an isomorphism of `F`-algebras.

Surjectivity is the Chinese remainder theorem; injectivity follows by dimension count since the
product map is an `F`-linear surjection between `F`-vector spaces of equal finite dimension. -/
theorem exists_algEquiv_pi_of_coprime_finrank
    {F A : Type*} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    {ι : Type*} [Fintype ι]
    (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)]
    [∀ i, Module.Finite F (B i)]
    (φ : ∀ i, A →+* B i)
    (hlin : ∀ i (f : F) (x : A), φ i (f • x) = f • φ i x)
    (hsurj : ∀ i, Function.Surjective (φ i))
    (hcop : Pairwise fun i j => IsCoprime (RingHom.ker (φ i)) (RingHom.ker (φ j)))
    (hdim : (∑ i, Module.finrank F (B i)) = Module.finrank F A) :
    Nonempty (A ≃ₐ[F] (∀ i, B i)) := by
  classical
  let Φ : A →+* (∀ i, B i) := RingHom.pi φ
  have hΦsurj : Function.Surjective Φ := by
    intro y
    choose a ha using fun i => hsurj i (y i)
    obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal (I := fun i => RingHom.ker (φ i)) hcop a
    refine ⟨r, funext fun i => ?_⟩
    have hz : φ i (r - a i) = 0 := by
      have h := hr i
      rwa [RingHom.mem_ker] at h
    have hsub : φ i r - φ i (a i) = 0 := by rw [← map_sub]; exact hz
    have hthis : φ i r = φ i (a i) := sub_eq_zero.mp hsub
    change φ i r = y i
    rw [hthis, ha i]
  have hΦcomm : ∀ f : F, Φ (algebraMap F A f) = algebraMap F (∀ i, B i) f := by
    intro f
    funext i
    have h1 : algebraMap F A f = f • (1 : A) := by rw [Algebra.smul_def, mul_one]
    rw [h1]
    change φ i (f • (1 : A)) = (algebraMap F (B i)) f
    rw [hlin i f 1, map_one, Algebra.smul_def, mul_one]
  let Φa : A →ₐ[F] (∀ i, B i) := AlgHom.mk Φ hΦcomm
  have hsurjA : Function.Surjective (Φa : A →ₗ[F] (∀ i, B i)) := by
    intro y
    obtain ⟨a, ha⟩ := hΦsurj y
    exact ⟨a, ha⟩
  have hfr : Module.finrank F A = Module.finrank F (∀ i, B i) := by
    rw [Module.finrank_pi_fintype F, hdim]
  have hinj : Function.Injective Φa :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mpr hsurjA
  exact ⟨AlgEquiv.ofBijective Φa ⟨hinj, hsurjA⟩⟩

/-- **`F`-algebra form of the Chinese remainder decomposition of `L ⊗[K] F`.**

Let `L / K` be a finite extension of number fields and let `p` be a finite place of `K`.  With
`F = p.adicCompletion K`, the base change `L ⊗[K] F` is isomorphic as an `F`-algebra to the
product of the completions `L_q` over the primes `q` of `𝓞 L` lying over `p`, each carrying the
`F`-algebra structure induced by `Commons.RingTheory.Henselian.adicCompletionMap`. -/
theorem exists_algEquiv_tensor_adicCompletion_prod (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    letI : ∀ q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) //
        q.asIdeal.LiesOver p.asIdeal},
        Algebra (p.adicCompletion K) (q.1.adicCompletion L) :=
      fun q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap p q.1 q.2)
    letI : Algebra (p.adicCompletion K) (TensorProduct K L (p.adicCompletion K)) :=
      Algebra.TensorProduct.rightAlgebra
    Nonempty ((TensorProduct K L (p.adicCompletion K)) ≃ₐ[p.adicCompletion K]
      ((q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) //
          q.asIdeal.LiesOver p.asIdeal}) → q.1.adicCompletion L)) := by
  classical
  let F := p.adicCompletion K
  let A := TensorProduct K L F
  let ι := {q : IsDedekindDomain.HeightOneSpectrum (𝓞 L) // q.asIdeal.LiesOver p.asIdeal}
  haveI : Fintype ι := Fintype.ofEquiv _ (primesOverEquiv p).symm
  letI : ∀ q : ι, Algebra F (q.1.adicCompletion L) :=
    fun q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap p q.1 q.2)
  letI : ∀ q : ι, Module.Finite F (q.1.adicCompletion L) :=
    fun q => Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion p q.1 q.2
  haveI : Module.Finite F A := by
    haveI : Module.Finite F (F ⊗[K] L) := inferInstance
    exact Module.Finite.equiv (M := F ⊗[K] L) (N := L ⊗[K] F)
      (Commons.LinearAlgebra.Dimension.flipRight K L F).symm
  let φ : ∀ q : ι, A →+* q.1.adicCompletion L := fun q =>
    Classical.choose
      (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon p q.1 q.2)
  have hφ_formula : ∀ (q : ι) (l : L) (f : F),
      φ q (l ⊗ₜ[K] f) = (algebraMap L (q.1.adicCompletion L) l) *
        (Commons.RingTheory.Henselian.adicCompletionMap p q.1 q.2 f) := fun q =>
    (Classical.choose_spec
      (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon p q.1 q.2)).2
  have hφ_surj : ∀ q : ι, Function.Surjective (φ q) := fun q =>
    (Classical.choose_spec
      (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon p q.1 q.2)).1
  have hlin : ∀ q : ι, ∀ (f : F) (x : A), φ q (f • x) = f • (φ q x) := by
    intro q f x
    have h1 : f • x = (1 ⊗ₜ[K] f : A) * x := by
      rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply]
    have h2 : φ q (1 ⊗ₜ[K] f) =
        (Commons.RingTheory.Henselian.adicCompletionMap p q.1 q.2) f := by
      rw [hφ_formula q 1 f, map_one, one_mul]
    rw [h1, map_mul, h2, Algebra.smul_def]
    congr 1
  have hcop : Pairwise fun i j : ι => IsCoprime (RingHom.ker (φ i)) (RingHom.ker (φ j)) := by
    intro i j hij
    have hne : i.1.asIdeal ≠ j.1.asIdeal := by
      intro hIJ
      exact hij (Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext hIJ))
    exact Commons.NumberTheory.NumberField.Completion.adicCompletionMap_kernels_coprime
      p i.1 j.1 i.2 j.2 hne
  have hdim : (∑ q : ι, Module.finrank F (q.1.adicCompletion L)) = Module.finrank F A := by
    have hbase : Module.finrank F A = Module.finrank K L :=
      Commons.LinearAlgebra.Dimension.tensor_field_baseChange_finrank (K := K) (L := L) (F := F)
    rw [hbase, ← Commons.NumberTheory.NumberField.Completion.sum_finrank_adicCompletion_eq_finrank
      (K := K) (L := L) p]
    refine Fintype.sum_equiv (primesOverEquiv p) _ _ ?_
    intro q
    dsimp only
    congr 1
  obtain ⟨e⟩ := exists_algEquiv_pi_of_coprime_finrank (F := F) (A := A) (ι := ι)
    (fun q : ι => q.1.adicCompletion L) φ hlin hφ_surj hcop hdim
  exact ⟨e⟩

end Commons.NumberTheory.NumberField.Completion
