import Mathlib
import Submission.Work.Kummer.Pairing
import Submission.Work.Kummer.kummerCharacter_eq_one_iff
import Submission.Work.Kummer.kummerCharacter_apply_of_pow_eq
import Submission.Work.Kummer.kummerCharacter_eq_iff_div_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Kummer

open IntermediateField

universe u v

section Fixing

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {ζ : K}

/-- A Kummer character is trivial on the automorphisms fixing the Kummer subfield: the chosen
`n`-th root `kummerRoot a` of `a` lies in `kummerSubfield n K L` by construction. -/
theorem kummerCharacter_eq_one_of_mem_fixingSubgroup (hζ : IsPrimitiveRoot ζ n)
    (a : kummerSubgroup n K L) :
    (kummerSubfield n K L).fixingSubgroup ≤ (kummerCharacter hζ a).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker]
  have hmem : ((kummerRoot a : Lˣ) : L) ∈ kummerSubfield n K L :=
    IntermediateField.subset_adjoin K {x : L | ∃ c : K, x ^ n = algebraMap K L c}
      ⟨((a : Kˣ) : K), kummerRoot_pow_val a⟩
  have hfix : (σ : L ≃ₐ[K] L) (kummerRoot a : L) = (kummerRoot a : L) := by
    have h := hσ
    simp only [IntermediateField.mem_fixingSubgroup_iff] at h
    exact h _ hmem
  have hratio : kummerRatio σ (kummerRoot a) = 1 := by
    apply Units.ext
    rw [kummerRatio_coe, hfix, div_self (Units.ne_zero (kummerRoot a)), Units.val_one]
  have h := map_kummerCharacter_apply hζ a σ
  rw [hratio] at h
  refine Subtype.ext (Units.map_injective (algebraMap K L).injective ?_)
  simpa using h

end Fixing

section Surjective

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {ζ : K}
variable [FiniteDimensional K L] [IsGalois K L]

/-- **Surjectivity of the Kummer pairing.**  For a finite Galois extension `L/K` and a primitive
`n`-th root of unity `ζ ∈ K`, every homomorphism `Gal(L/K) →* μ_n(K)` is the Kummer character of
some `a ∈ Kˣ ∩ (Lˣ)^n`.  The proof is the classical Lagrange-resolvent argument. -/
theorem kummerCharacterHom_surjective_aux (hζ : IsPrimitiveRoot ζ n)
    (χ : Gal(L/K) →* rootsOfUnity n K) :
    ∃ a : kummerSubgroup n K L, kummerCharacter hζ a = χ := by
  classical
  -- Work with `ψ = χ⁻¹`; the resolvent built from `ψ` has ratios `ψ(σ)⁻¹ = χ(σ)`.
  set ψ : Gal(L/K) →* rootsOfUnity n K := χ⁻¹ with hψ
  set w : Gal(L/K) →* Kˣ := (rootsOfUnity n K).subtype.comp ψ with hw
  set c : Gal(L/K) → L := fun σ => algebraMap K L ((w σ : Kˣ) : K) with hc
  have hwpow : ∀ σ : Gal(L/K), (w σ) ^ n = 1 := by
    intro σ
    have h2 : (((ψ σ : rootsOfUnity n K) : Kˣ)) ^ n = 1 :=
      (mem_rootsOfUnity n _).mp (ψ σ).2
    simpa only [hw, MonoidHom.comp_apply, Subgroup.coe_subtype] using h2
  have hc_fix : ∀ (τ σ : Gal(L/K)), (τ : L ≃ₐ[K] L) (c σ) = c σ := by
    intro τ σ
    simp only [hc]
    exact AlgEquiv.commutes τ _
  -- Dedekind's linear independence of the automorphisms shows the resolvent is not identically 0.
  have hli : LinearIndependent L (fun (f : Gal(L/K)) => (f : L → L)) :=
    LinearIndependent.comp (ι' := Gal(L/K)) (linearIndependent_monoidHom L L) (fun f => f)
      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)
  have hc_one : c 1 = 1 := by simp only [hc, map_one w, Units.val_one, map_one]
  have hsum_ne : (∑ σ : Gal(L/K), c σ • (σ : L → L)) ≠ 0 := by
    intro h0
    have h1 := (Fintype.linearIndependent_iff.mp hli) c h0 1
    rw [hc_one] at h1
    exact one_ne_zero h1
  obtain ⟨x, hx⟩ : ∃ x : L, (∑ σ : Gal(L/K), c σ * (σ : L ≃ₐ[K] L) x) ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum_ne (funext fun y => by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h y)
  set R : L := ∑ σ : Gal(L/K), c σ * (σ : L ≃ₐ[K] L) x with hRdef
  have hR0 : R ≠ 0 := by rw [hRdef]; exact hx
  -- The action of `τ` on the resolvent.
  have hτ : ∀ τ : Gal(L/K), (τ : L ≃ₐ[K] L) R = (c τ)⁻¹ * R := by
    intro τ
    have hstep : (τ : L ≃ₐ[K] L) R
        = ∑ σ : Gal(L/K), c (τ⁻¹ * σ) * (σ : L ≃ₐ[K] L) x := by
      rw [hRdef, map_sum]
      refine Fintype.sum_bijective (fun σ : Gal(L/K) => τ * σ) (Group.mulLeft_bijective τ)
        (fun σ : Gal(L/K) => (τ : L ≃ₐ[K] L) (c σ * (σ : L ≃ₐ[K] L) x))
        (fun σ : Gal(L/K) => c (τ⁻¹ * σ) * (σ : L ≃ₐ[K] L) x) ?_
      intro σ
      rw [map_mul, hc_fix, AlgEquiv.mul_apply]
      congr 1
      rw [show τ⁻¹ * (τ * σ) = σ by group]
    rw [hstep]
    have hc2 : ∀ σ : Gal(L/K), c (τ⁻¹ * σ) = (c τ)⁻¹ * c σ := by
      intro σ
      simp only [hc]
      rw [map_mul w, map_inv w, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    have h1 : (∑ σ : Gal(L/K), c (τ⁻¹ * σ) * (σ : L ≃ₐ[K] L) x)
        = ∑ σ : Gal(L/K), (c τ)⁻¹ * (c σ * (σ : L ≃ₐ[K] L) x) := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [hc2 σ, mul_assoc]
    rw [h1, ← Finset.mul_sum, ← hRdef]
  -- `R ^ n` is fixed by `Gal(L/K)`, hence lies in `K`.
  have hcw : ∀ σ : Gal(L/K), (c σ) ^ n = 1 := by
    intro σ
    simp only [hc]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hwpow σ, Units.val_one, map_one]
  have hfixpow : ∀ τ : Gal(L/K), (τ : L ≃ₐ[K] L) (R ^ n) = R ^ n := by
    intro τ
    rw [map_pow, hτ τ, mul_pow, inv_pow, hcw τ, inv_one, one_mul]
  obtain ⟨a, ha⟩ := Set.mem_range.mp
    ((IsGalois.mem_range_algebraMap_iff_fixed (R ^ n)).mpr hfixpow)
  have hRn0 : R ^ n ≠ 0 := pow_ne_zero n hR0
  have ha0 : a ≠ 0 := fun h => hRn0 (by rw [← ha, h, map_zero])
  have hα : ((Units.mk0 R hR0 : Lˣ) : L) ^ n = algebraMap K L ((Units.mk0 a ha0 : Kˣ) : K) := by
    rw [Units.val_mk0, Units.val_mk0]
    exact ha.symm
  have hmem : Units.mk0 a ha0 ∈ kummerSubgroup n K L :=
    ⟨Units.mk0 R hR0, Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0, Units.val_mk0]
      exact ha.symm)⟩
  refine ⟨⟨Units.mk0 a ha0, hmem⟩, ?_⟩
  refine MonoidHom.ext fun σ => Subtype.ext (Units.ext ((algebraMap K L).injective ?_))
  have hχ : (c σ)⁻¹ = algebraMap K L (((χ σ : rootsOfUnity n K) : Kˣ) : K) := by
    have hwσ : w σ = (((χ σ : rootsOfUnity n K) : Kˣ))⁻¹ := by
      have h1 : w σ = ((ψ σ : rootsOfUnity n K) : Kˣ) := by
        simp only [hw, MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [h1, hψ, MonoidHom.inv_apply, Subgroup.coe_inv]
    have h2 : (((w σ : Kˣ)) : K)⁻¹ = ((((χ σ : rootsOfUnity n K) : Kˣ)) : K) := by
      rw [← Units.val_inv_eq_inv_val, hwσ]
      simp
    simp only [hc]
    rw [← map_inv₀, h2]
  calc algebraMap K L ((((kummerCharacter hζ ⟨Units.mk0 a ha0, hmem⟩) σ : rootsOfUnity n K) : Kˣ) : K)
      = ((kummerRatio σ (kummerRoot ⟨Units.mk0 a ha0, hmem⟩) : Lˣ) : L) :=
        kummerCharacter_apply_coe hζ ⟨Units.mk0 a ha0, hmem⟩ σ
    _ = ((kummerRatio σ (Units.mk0 R hR0) : Lˣ) : L) :=
        congrArg (fun x : Lˣ => (x : L))
          (kummerRatio_congr hζ hα (kummerRoot_pow_val ⟨Units.mk0 a ha0, hmem⟩) σ)
    _ = (σ : L ≃ₐ[K] L) R / R := by rw [kummerRatio_coe, Units.val_mk0]
    _ = (c σ)⁻¹ := by rw [hτ σ, mul_div_cancel_right₀ _ hR0]
    _ = algebraMap K L ((((χ σ : rootsOfUnity n K) : Kˣ) : K)) := hχ

end Surjective

/-- **The range of the Kummer character map.**  For a finite Galois extension `L/K` and a primitive
`n`-th root of unity `ζ ∈ K`, the Kummer characters of the elements of `Kˣ ∩ (Lˣ)^n` are exactly
the homomorphisms `Gal(L/K) →* μ_n(K)` that are trivial on the automorphisms fixing the Kummer
subfield `kummerSubfield n K L`. -/
theorem kummerCharacterHom_range {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L] [IsGalois K L]
    (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Set.range (kummerCharacterHom (K := K) (L := L) hζ) =
      {χ : Gal(L/K) →* rootsOfUnity n K | (kummerSubfield n K L).fixingSubgroup ≤ χ.ker} := by
  ext χ
  constructor
  · rintro ⟨a, rfl⟩
    exact kummerCharacter_eq_one_of_mem_fixingSubgroup hζ a
  · intro _
    exact kummerCharacterHom_surjective_aux hζ χ

end Work.Kummer
