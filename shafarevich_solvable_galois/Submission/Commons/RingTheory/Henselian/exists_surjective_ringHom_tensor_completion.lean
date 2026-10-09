import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers_of_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField
open scoped TensorProduct Valued

noncomputable section
attribute [local instance] Algebra.TensorProduct.rightAlgebra
set_option linter.style.haveILetI false

namespace Commons.RingTheory.Henselian

open IsDedekindDomain.HeightOneSpectrum

theorem exists_surjective_ringHom_tensor_completion
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    ∃ (iF : (Q.adicCompletion K) →+* q.adicCompletion L),
      (∀ k : K, iF (k : Q.adicCompletion K) = algebraMap K L k) ∧
      ∃ φ : (L ⊗[K] Q.adicCompletion K) →+* q.adicCompletion L,
        Function.Surjective φ ∧
        ∀ (l : L) (f : Q.adicCompletion K),
          φ (l ⊗ₜ[K] f) = (algebraMap L (q.adicCompletion L) l) * iF f := by
  let Kv := Q.adicCompletion K
  let Lw := q.adicCompletion L
  let iF : Kv →+* Lw := adicCompletionMap Q q hq
  letI : Algebra Kv Lw := iF.toAlgebra
  haveI : IsScalarTower K Kv Lw := IsScalarTower.of_algebraMap_eq (R := K) (S := Kv) (A := Lw) (by
    intro k
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (S := K) (v := q) (K := L)]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (S := K) (v := Q) (K := K)]
    exact (adicCompletionMap_apply Q q hq k).symm)
  have hcont : Continuous (algebraMap Kv Lw) := by
    change Continuous (iF : Kv → Lw)
    exact adicCompletionMap_continuous Q q hq
  haveI : ContinuousSMul Kv Lw := continuousSMul_of_algebraMap Kv Lw hcont
  haveI : Module.Finite Kv Lw := inferInstance
  -- the K-algebra map L → Lw
  let fAlg : L →ₐ[K] Lw := (Algebra.ofId L Lw).restrictScalars K
  -- alg hom over Kv from Kv ⊗[K] L
  let ψ : (Kv ⊗[K] L) →ₐ[Kv] Lw := AlgHom.liftEquiv K Kv L Lw fAlg
  -- flip to L ⊗[K] Kv
  let φ' : (L ⊗[K] Kv) →ₐ[Kv] Lw :=
    ψ.comp ((Algebra.TensorProduct.commRight (R := K) (S := Kv) (A := L)).symm)
  let φ : (L ⊗[K] Kv) →+* Lw := φ'.toRingHom
  have hφ'_tmul (l : L) (f : Kv) :
      φ' (l ⊗ₜ[K] f) = (algebraMap L Lw l) * iF f := by
    dsimp [φ', ψ, fAlg]
    rw [Algebra.smul_def]
    rw [mul_comm]
    rfl
  have hφ_tmul (l : L) (f : Kv) :
      φ (l ⊗ₜ[K] f) = (algebraMap L Lw l) * iF f := by
    change φ' (l ⊗ₜ[K] f) = (algebraMap L Lw l) * iF f
    exact hφ'_tmul l f
  have hsurj : Function.Surjective (fun x : L ⊗[K] Kv => φ' x) := by
    let R₀ : Submodule Kv Lw := LinearMap.range φ'.toLinearMap
    have hclosed : IsClosed (R₀ : Set Lw) := by
      refine Submodule.closed_of_finiteDimensional (𝕜 := Kv) (E := Lw) R₀
    have hdense : Dense (R₀ : Set Lw) := by
      refine (denseRange_algebraMap (R := 𝓞 L) L q).mono ?_
      rintro x ⟨l, rfl⟩
      change (algebraMap L Lw l) ∈ R₀
      refine LinearMap.mem_range.mpr ?_
      refine ⟨l ⊗ₜ[K] (1 : Kv), ?_⟩
      change φ' (l ⊗ₜ[K] (1 : Kv)) = (algebraMap L Lw l)
      simpa using hφ'_tmul l (1 : Kv)
    have htop : (R₀ : Set Lw) = Set.univ := by
      apply le_antisymm
      · intro x hx; trivial
      · rw [← hclosed.closure_eq]
        exact hdense.closure_eq.ge
    intro y
    have hy : y ∈ (R₀ : Set Lw) := by
      rw [htop]
      trivial
    simpa [R₀] using hy
  refine ⟨iF, ?_, ⟨φ, ?_, ?_⟩⟩
  · intro k
    exact adicCompletionMap_apply Q q hq k
  · change Function.Surjective (fun x : L ⊗[K] Kv => φ' x)
    exact hsurj
  · intro l f
    simpa [Kv, Lw, iF] using hφ_tmul l f

end Commons.RingTheory.Henselian