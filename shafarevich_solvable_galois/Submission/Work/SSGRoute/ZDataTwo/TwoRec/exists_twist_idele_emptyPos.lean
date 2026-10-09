import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass
import Submission.Work.SSGRoute.PinnedTwin.twistIdeleExists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo.TwoRec

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

/-- **The `ρ`-twist is multiplicative.**  For an involutive Galois automorphism `ρ` acting on the
(abelian) group of idèles, the map `x ↦ ρ • x * x⁻¹` is a homomorphism; this is the multiplicativity
identity, spelled out. -/
private lemma twist_mul {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (a b : NK.GlobalCFT.Idele K) :
    (ρ • (a * b)) * (a * b)⁻¹ = ((ρ • a) * a⁻¹) * ((ρ • b) * b⁻¹) := by
  rw [MulDistribMulAction.smul_mul, mul_inv_rev]
  ac_rfl

theorem exists_twist_idele_emptyPos {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) (hA : A ≠ 0)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hne : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮) :
    ∃ (𝔪 : NK.NUV2.RouteB.Modulus K) (x : NK.GlobalCFT.Idele K),
      𝔪.pos = ∅ ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ q) = 𝔪.exps q) ∧
      (𝔪.exps (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) ≠ 0) ∧
      NK.GlobalCFT.IdeleClassGroup.idealClassHom K
        (NK.GlobalCFT.IdeleClassGroup.mk K x) = ClassGroup.mk K (Units.mk0 A hA) ∧
      ρ • x * x⁻¹ ∉ NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪 := by
  classical
  -- The twist witness `u`: an integral idèle whose `ρ`-twist escapes the congruence subgroup,
  -- together with a `ρ`-stable modulus `𝔪` with `𝔪.pos = ∅` and `𝔪.exps (ρ𝔮) ≠ 0`.
  obtain ⟨𝔪, u, hpos, hexp, hqne, hu_int, htwist⟩ :=
    Work.SSGRoute.PinnedTwin.twistIdeleExists (k := k) (K := K) ρ hρ2 𝔮 hne
  -- A base idèle `x₀` of ideal class `[A]`.
  obtain ⟨x₀, hx₀⟩ := NK.GlobalCFT.IdeleClassGroup.idealOf_surjective K (Units.mk0 A hA)
  have hx₀' : NK.GlobalCFT.Idele.idealOf x₀ = A := by
    rw [hx₀, Units.val_mk0]
  have hclass₀ : NK.GlobalCFT.IdeleClassGroup.idealClassHom K
      (NK.GlobalCFT.IdeleClassGroup.mk K x₀) = ClassGroup.mk K (Units.mk0 A hA) := by
    rw [show NK.GlobalCFT.IdeleClassGroup.idealClassHom K
          (NK.GlobalCFT.IdeleClassGroup.mk K x₀)
        = NK.GlobalCFT.IdeleClassGroup.idealClassMap K x₀ from rfl]
    rw [NK.GlobalCFT.IdeleClassGroup.idealClassMap_apply]
    congr 1
    exact Units.ext (by rw [Units.val_mk0, Units.val_mk0]; exact hx₀')
  -- Multiplication by the integral idèle `u` does not change the ideal class.
  have hclass_ker : NK.GlobalCFT.IdeleClassGroup.idealClassHom K
      (NK.GlobalCFT.IdeleClassGroup.mk K u) = 1 := by
    show NK.GlobalCFT.IdeleClassGroup.idealClassMap K u = 1
    exact NK.GlobalCFT.IdeleClassGroup.idealClassMap_eq_one_of_mem_integralIdeles hu_int
  by_cases htw₀ : (ρ • x₀) * x₀⁻¹ ∈
      (NK.GlobalCFT.Idele.principalSubgroup K ⊔ NK.NUV2.RouteB.CongSubgroup K 𝔪)
  · -- The base idèle's twist is already trivial in the congruence quotient: multiply by `u`.
    refine ⟨𝔪, x₀ * u, hpos, hexp, hqne, ?_, ?_⟩
    · have hmul : NK.GlobalCFT.IdeleClassGroup.mk K (x₀ * u)
          = NK.GlobalCFT.IdeleClassGroup.mk K x₀ * NK.GlobalCFT.IdeleClassGroup.mk K u :=
        map_mul _ x₀ u
      rw [hmul, map_mul, hclass₀, hclass_ker, mul_one]
    · intro hmem
      rw [twist_mul ρ x₀ u] at hmem
      exact htwist (by
        have h := Subgroup.mul_mem _
          (Subgroup.inv_mem _ htw₀) hmem
        rwa [inv_mul_cancel_left] at h)
  · -- The base idèle already works.
    exact ⟨𝔪, x₀, hpos, hexp, hqne, hclass₀, htw₀⟩

end Work.SSGRoute.ZDataTwo.TwoRec
