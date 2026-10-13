import Submission.Work.DSG4b.LCF.Basic
import Submission.Work.DSG4b.LCF.Colength
import Submission.Work.DSG4b.LCF.exists_le_pow_mul_of_inf_pow_le
import Submission.Work.DSG4b.LCF.map_lTensor_mul_le_smul_top
import Submission.Work.DSG4b.LCF.mem_range_lTensor_inf_of_lTensor_eq_zero
import Submission.Work.DSG4b.LCF.module_finite_tensor_of_fg

/-!
# The general case of the local criterion of flatness (Stacks 00MK)

Let `R → S` be a local homomorphism of Noetherian local rings and let `M` be a finite `S`-module
such that `Tor₁^R(R/𝔪, M) = 0`, i.e. `M ⊗[R] 𝔪 → M ⊗[R] R` is injective.  Then `M ⊗[R] I → M ⊗[R] R`
is injective for every finitely generated ideal `I`, which by `Module.Flat.iff_lTensor_injective`
means that `M` is flat over `R`.

The argument follows Stacks 00MK: for `n ≫ 0` the chase
`Work.DSG4b.LCF.mem_range_lTensor_inf_of_lTensor_eq_zero` shows that any `ξ` killed by
`M ⊗ I → M ⊗ R` lies in the image of `M ⊗ (I ⊓ 𝔪^n) → M ⊗ I`, and Artin–Rees
(`exists_le_pow_mul_of_inf_pow_le`) together with `map_lTensor_mul_le_smul_top` shows that this
image sits in `𝔪^(n-k) • ⊤`.  Hence `ξ` lies in the `𝔪`-adic intersection of `M ⊗[R] I`, which
vanishes by Krull's intersection theorem, since `M ⊗[R] I` is a finite `S`-module
(`module_finite_tensor_of_fg`) and `𝔪S` is contained in the maximal ideal of `S`.
-/

namespace Work.DSG4b.LCF

open TensorProduct LinearMap

/-- The `I`-adic filtration on an `S`-module is contained in the `I·S`-adic filtration. -/
lemma mem_smul_top_of_mem_smul_top_map {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (I : Ideal R) (n : ℕ)
    {x : N} (hx : x ∈ I ^ n • (⊤ : Submodule R N)) :
    x ∈ (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S N) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
  · rw [← IsScalarTower.algebraMap_smul S a y]
    refine Submodule.smul_mem_smul ?_ trivial
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  · exact Submodule.add_mem _ hx hy

/-- **Local criterion of flatness**, general case.  If `M ⊗[R] 𝔪 → M ⊗[R] R` is injective, then
`M ⊗[R] I → M ⊗[R] R` is injective for every finitely generated ideal `I`. -/
theorem injective_lTensor_subtype_of_fg {R S M : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M]
    (h𝔪 : Function.Injective (LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype))
    (I : Ideal R) (hI : I.FG) :
    Function.Injective (LinearMap.lTensor M (Submodule.subtype I)) := by
  haveI : Module.Finite S (TensorProduct R M I) := module_finite_tensor_of_fg I hI
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro ξ hξ
  rw [LinearMap.mem_ker] at hξ
  obtain ⟨k, hk⟩ := exists_le_pow_mul_of_inf_pow_le I (IsLocalRing.maximalIdeal R)
  -- `ξ` lies in `𝔪 ^ m • ⊤` for every `m`
  have hmem : ∀ m : ℕ,
      ξ ∈ IsLocalRing.maximalIdeal R ^ m • (⊤ : Submodule R (TensorProduct R M I)) := by
    intro m
    have hinj := injective_lTensor_subtype_of_pow_le h𝔪
      (I ⊔ IsLocalRing.maximalIdeal R ^ (m + k)) (m + k) le_sup_right
    have hchase := mem_range_lTensor_inf_of_lTensor_eq_zero I
      (IsLocalRing.maximalIdeal R ^ (m + k)) hinj ξ hξ
    have har' : I ⊓ IsLocalRing.maximalIdeal R ^ (m + k) ≤
        IsLocalRing.maximalIdeal R ^ m * I := by
      have h := hk (m + k) (by omega)
      rwa [show m + k - k = m from by omega] at h
    have hfac : Submodule.inclusion
          (inf_le_left : I ⊓ IsLocalRing.maximalIdeal R ^ (m + k) ≤ I) =
        Submodule.inclusion (Ideal.mul_le_right : IsLocalRing.maximalIdeal R ^ m * I ≤ I) ∘ₗ
          Submodule.inclusion har' := by
      ext x; rfl
    have hle : Submodule.map (LinearMap.lTensor M (Submodule.inclusion
          (inf_le_left : I ⊓ IsLocalRing.maximalIdeal R ^ (m + k) ≤ I))) ⊤ ≤
        IsLocalRing.maximalIdeal R ^ m • (⊤ : Submodule R (TensorProduct R M I)) := by
      rw [Submodule.map_top, hfac, LinearMap.lTensor_comp]
      refine (LinearMap.range_comp_le_range _ _).trans ?_
      simpa [Submodule.map_top] using map_lTensor_mul_le_smul_top
        (IsLocalRing.maximalIdeal R) I m
    exact hle (by simpa [Submodule.map_top] using hchase)
  -- Krull's intersection theorem for the finite `S`-module `M ⊗[R] I`
  have hkrull : (⨅ i : ℕ, ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) ^ i •
      (⊤ : Submodule S (TensorProduct R M I))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _
      ((IsLocalRing.map_maximalIdeal_le (algebraMap R S)).trans
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S)))
  have hzeroS : ξ ∈ (⨅ i : ℕ, ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) ^ i •
      (⊤ : Submodule S (TensorProduct R M I))) := by
    simp only [Submodule.mem_iInf]
    exact fun m => mem_smul_top_of_mem_smul_top_map (IsLocalRing.maximalIdeal R) m (hmem m)
  rw [hkrull] at hzeroS
  exact (Submodule.mem_bot S).mp hzeroS

end Work.DSG4b.LCF
