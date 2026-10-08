import Submission.Work.CharPrelim.weightSpace_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Linear independence of the weight spaces

For a representation `ρ : Z →* Module.End k V` of a finite abelian group `Z` over a field `k`
in which `|Z|` is invertible, the weight spaces `weightSpace ρ χ` are linearly independent.
The proof uses the projection `charProj ρ χ = (|Z| : k)⁻¹ • ∑ z, (χ z)⁻¹ • ρ z`, which is the
identity on `weightSpace ρ χ` and kills every other weight space.
-/

noncomputable section

open Classical

namespace Work.CharPrelim

variable {k V Z : Type*}

section Proj

variable [Field k] [AddCommGroup V] [Module k V] [CommGroup Z] [Fintype Z]

/-- The character projection is the identity on the weight space of its own character. -/
theorem charProj_apply_of_mem (ρ : Z →* Module.End k V) (χ : Z →* kˣ)
    (hcard : IsUnit ((Nat.card Z : ℕ) : k)) {v : V} (hv : v ∈ weightSpace ρ χ) :
    charProj ρ χ v = v := by
  have hcard0 : ((Nat.card Z : ℕ) : k) ≠ 0 := hcard.ne_zero
  have hval : ∀ z : Z, (χ z : k)⁻¹ * (χ z : k) = 1 := by
    intro z
    rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsum : (∑ z : Z, ((χ z : k)⁻¹) • (ρ z)) v = ((Nat.card Z : ℕ) : k) • v := by
    rw [LinearMap.sum_apply]
    rw [mem_weightSpace] at hv
    calc ∑ z : Z, (((χ z : k)⁻¹) • (ρ z)) v
        = ∑ z : Z, (1 : k) • v := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [LinearMap.smul_apply, hv z, smul_smul, hval z]
      _ = ∑ _z : Z, v := by simp
      _ = ((Nat.card Z : ℕ) : k) • v := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
          exact (Nat.cast_smul_eq_nsmul k (Fintype.card Z) v).symm
  calc charProj ρ χ v
      = ((Nat.card Z : ℕ) : k)⁻¹ • ((∑ z : Z, ((χ z : k)⁻¹) • (ρ z)) v) := by
        rw [charProj, LinearMap.smul_apply]
    _ = ((Nat.card Z : ℕ) : k)⁻¹ • (((Nat.card Z : ℕ) : k) • v) := by rw [hsum]
    _ = v := by rw [smul_smul, inv_mul_cancel₀ hcard0, one_smul]

/-- The character projection kills the weight space of any other character. -/
theorem charProj_apply_of_mem_ne (ρ : Z →* Module.End k V) {χ ψ : Z →* kˣ} (hχψ : χ ≠ ψ)
    {v : V} (hv : v ∈ weightSpace ρ ψ) : charProj ρ χ v = 0 := by
  have hη : (χ⁻¹ * ψ : Z →* kˣ) ≠ 1 := by
    intro h
    apply hχψ
    ext z
    have hz : ((χ⁻¹ * ψ) z : k) = ((1 : Z →* kˣ) z : k) := by rw [h]
    simp only [MonoidHom.mul_apply, MonoidHom.one_apply, MonoidHom.inv_apply,
      Units.val_inv_eq_inv_val, Units.val_mul, Units.val_one] at hz
    calc (χ z : k) = (χ z : k) * 1 := (mul_one _).symm
      _ = (χ z : k) * ((χ z : k)⁻¹ * (ψ z : k)) := by rw [hz]
      _ = (ψ z : k) := by
            rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero (χ z)), one_mul]
  have hsum : ∑ z : Z, ((χ z : k)⁻¹) * (ψ z : k) = 0 := by
    have h := sum_eq_zero_of_ne_one hη
    convert h using 1 with z
    simp [MonoidHom.mul_apply]
  have hproj : (∑ z : Z, ((χ z : k)⁻¹) • (ρ z)) v = 0 := by
    rw [LinearMap.sum_apply]
    rw [mem_weightSpace] at hv
    trans ∑ z : Z, (((χ z : k)⁻¹ * (ψ z : k))) • v
    · refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [LinearMap.smul_apply, hv z, smul_smul]
    · rw [← Finset.sum_smul, hsum, zero_smul]
  rw [charProj, LinearMap.smul_apply, hproj, smul_zero]

end Proj

section Indep

variable [Field k] [CommGroup Z] [Fintype Z] [AddCommGroup V] [Module k V]

/-- **Linear independence of the weight spaces.** -/
theorem weightSpace_indep (ρ : Z →* Module.End k V)
    (hcard : IsUnit ((Nat.card Z : ℕ) : k)) :
    iSupIndep (fun (χ : Z →* kˣ) => weightSpace ρ χ) := by
  rw [iSupIndep_def]
  intro χ
  rw [disjoint_iff_inf_le]
  intro v hv
  rw [Submodule.mem_bot]
  obtain ⟨hvχ, hv'⟩ := Submodule.mem_inf.mp hv
  have h1 : charProj ρ χ v = v := charProj_apply_of_mem ρ χ hcard hvχ
  have h2 : charProj ρ χ v = 0 := by
    have hker : (⨆ ψ : Z →* kˣ, ⨆ (_ : ψ ≠ χ), weightSpace ρ ψ) ≤
        LinearMap.ker (charProj ρ χ) := by
      refine iSup_le (fun ψ => iSup_le (fun hψ => ?_))
      intro w hw
      exact LinearMap.mem_ker.mpr (charProj_apply_of_mem_ne ρ (Ne.symm hψ) hw)
    exact LinearMap.mem_ker.mp (hker hv')
  rw [h1] at h2
  exact h2

end Indep

end Work.CharPrelim
