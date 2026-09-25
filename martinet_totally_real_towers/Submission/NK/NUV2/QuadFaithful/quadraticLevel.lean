import Mathlib
import Submission.NK.NUV2.QuadFaithful.Defs

/-!
# Quadratic levels: identifying them from a square class

If `L₁`, `L₂` are quadratic intermediate fields of an extension `F' / F` and `xᵢ ∈ Lᵢ` generates
`Lᵢ` with `xᵢ ^ 2 = aᵢ ∈ F`, then `a₁ / a₂ ∈ (Fˣ)²` forces `L₁ = L₂`.
-/

namespace NK.NUV2.QuadFaithful

noncomputable section

open scoped Classical

/-- **Index bookkeeping**: if `S ≤ N`, `[Fˣ : S] = 4` and `[Fˣ : N] = 2` then `[N : S] = 2`. -/
theorem relIndex_eq_two_of_index_eq {G : Type*} [Group G] {S N : Subgroup G} (hS : S ≤ N)
    (hSidx : S.index = 4) (hNidx : N.index = 2) : S.relIndex N = 2 := by
  have h := Subgroup.relIndex_mul_index hS
  rw [hSidx, hNidx] at h
  omega

/-- **Two quadratic levels with the same square class coincide.** -/
theorem eq_of_div_mem_sq {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    {L₁ L₂ : IntermediateField F F'} [FiniteDimensional F ↥L₁] [FiniteDimensional F ↥L₂]
    (h₁ : Module.finrank F ↥L₁ = 2) (h₂ : Module.finrank F ↥L₂ = 2)
    {x₁ : ↥L₁} {x₂ : ↥L₂} {a₁ a₂ : Fˣ}
    (hx₁ : x₁ ∉ Set.range (algebraMap F ↥L₁)) (hx₂ : x₂ ∉ Set.range (algebraMap F ↥L₂))
    (hsq₁ : ((x₁ : ↥L₁)) ^ 2 = algebraMap F ↥L₁ (a₁ : F))
    (hsq₂ : ((x₂ : ↥L₂)) ^ 2 = algebraMap F ↥L₂ (a₂ : F))
    (hdiv : a₁ / a₂ ∈ sq F) : L₁ = L₂ := by
  obtain ⟨c, hc⟩ := mem_sq_iff.mp hdiv
  set y₁ : F' := ((x₁ : ↥L₁) : F') with hy₁def
  set y₂ : F' := ((x₂ : ↥L₂) : F') with hy₂def
  set d : F' := algebraMap F F' (c : F) with hddef
  -- squares in `F'`
  have hy₁sq : y₁ ^ 2 = algebraMap F F' (a₁ : F) := by
    rw [hy₁def, ← show ((x₁ ^ 2 : ↥L₁) : F') = ((x₁ : ↥L₁) : F') ^ 2 from rfl, hsq₁,
      IsScalarTower.algebraMap_apply F ↥L₁ F' (a₁ : F)]
    rfl
  have hy₂sq : y₂ ^ 2 = algebraMap F F' (a₂ : F) := by
    rw [hy₂def, ← show ((x₂ ^ 2 : ↥L₂) : F') = ((x₂ : ↥L₂) : F') ^ 2 from rfl, hsq₂,
      IsScalarTower.algebraMap_apply F ↥L₂ F' (a₂ : F)]
    rfl
  have hc' : a₁ = a₂ * c ^ 2 := by rw [hc, mul_comm, div_mul_cancel]
  have hcF : (a₁ : F) = (a₂ : F) * (c : F) ^ 2 := by
    have h := congrArg (fun u : Fˣ => (u : F)) hc'
    simpa [Units.val_mul, Units.val_pow_eq_pow_val] using h
  have hd : algebraMap F F' (a₁ : F) = d ^ 2 * algebraMap F F' (a₂ : F) := by
    rw [hcF, map_mul, map_pow, hddef]
    ring
  have hsquare : y₁ ^ 2 = (y₂ * d) ^ 2 := by
    rw [hy₁sq, hd, ← hy₂sq, mul_pow]
    ring
  have hfac : (y₁ - y₂ * d) * (y₁ + y₂ * d) = 0 := by
    have hz : y₁ ^ 2 - (y₂ * d) ^ 2 = 0 := by rw [hsquare]; ring
    linear_combination hz
  have hy₁L₂ : y₁ ∈ L₂ := by
    have hdmem : d ∈ L₂ := by rw [hddef]; exact L₂.algebraMap_mem (c : F)
    rcases mul_eq_zero.mp hfac with h | h
    · have : y₁ = y₂ * d := sub_eq_zero.mp h
      rw [this]
      exact L₂.mul_mem x₂.2 hdmem
    · have : y₁ = -(y₂ * d) := eq_neg_of_add_eq_zero_left h
      rw [this]
      exact L₂.neg_mem (L₂.mul_mem x₂.2 hdmem)
  have hy₁L₁ : y₁ ∈ L₁ := by rw [hy₁def]; exact x₁.2
  have hy₁not : y₁ ∉ Set.range (algebraMap F F') := by
    rintro ⟨b, hb⟩
    refine hx₁ ⟨b, Subtype.ext ?_⟩
    have h1 : (((algebraMap F ↥L₁) b : ↥L₁) : F') = algebraMap F F' b := rfl
    rw [h1, hb, hy₁def]
  have hle₁ : (IntermediateField.adjoin F {y₁}) ≤ L₁ := IntermediateField.adjoin_simple_le_iff.mpr hy₁L₁
  have hle₂ : (IntermediateField.adjoin F {y₁}) ≤ L₂ := IntermediateField.adjoin_simple_le_iff.mpr hy₁L₂
  have hfin : Module.finrank F ↥((IntermediateField.adjoin F {y₁})) = 2 := by
    have hmono : Module.finrank F ↥((IntermediateField.adjoin F {y₁})) ≤ Module.finrank F ↥L₁ :=
      Submodule.finrank_mono (R := F) (s := ((IntermediateField.adjoin F {y₁})).toSubalgebra.toSubmodule)
        (t := L₁.toSubalgebra.toSubmodule) hle₁
    have hne1 : Module.finrank F ↥((IntermediateField.adjoin F {y₁})) ≠ 1 := by
      intro hone
      have hbot : (IntermediateField.adjoin F {y₁}) = (⊥ : IntermediateField F F') :=
        IntermediateField.finrank_eq_one_iff.mp hone
      have hmem : y₁ ∈ (⊥ : IntermediateField F F') := by
        rw [← hbot]
        exact IntermediateField.mem_adjoin_simple_self F y₁
      exact hy₁not (IntermediateField.mem_bot.mp hmem)
    have hint : IsIntegral F y₁ := by
      have h1 : IsIntegral F (algebraMap F F' (a₁ : F)) := isIntegral_algebraMap
      rw [← hy₁sq] at h1
      exact h1.of_pow (by norm_num)
    haveI : FiniteDimensional F ↥((IntermediateField.adjoin F {y₁})) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hpos : 0 < Module.finrank F ↥((IntermediateField.adjoin F {y₁})) := Module.finrank_pos
    omega
  have he₁ : (IntermediateField.adjoin F {y₁}) = L₁ := IntermediateField.eq_of_le_of_finrank_eq hle₁ (by rw [hfin, h₁])
  have he₂ : (IntermediateField.adjoin F {y₁}) = L₂ := IntermediateField.eq_of_le_of_finrank_eq hle₂ (by rw [hfin, h₂])
  exact he₁.symm.trans he₂

end

end NK.NUV2.QuadFaithful
