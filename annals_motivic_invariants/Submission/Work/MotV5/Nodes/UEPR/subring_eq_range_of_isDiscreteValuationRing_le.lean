import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes.UEPR

/-- Let `R` be a discrete valuation ring with fraction field `Ω`.  Then `R` is a maximal
proper subring of `Ω`: every subring `V ⊆ Ω` containing the image of `R` is either the
image of `R` itself or all of `Ω`.

The proof uses the structure theorem for a DVR: if `ϖ ∈ R` is a uniformizer (i.e.
irreducible) with image `π ∈ Ω`, then every nonzero `x ∈ Ω` is `u • π ^ n` for some unit
`u ∈ Rˣ` and some `n : ℤ` (`IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible`).
Consequently, if `x ∈ V` is not in the image of `R`, the exponent `n` is negative, and
multiplying `x = u π ^ n` by `π ^ m` (`n = -(m+1)`) exhibits `π⁻¹` as a product of
elements of `V`.  A subring containing both the image of `R` and `π⁻¹` is everything,
since `Ω = R[π⁻¹]`. -/
theorem subring_eq_range_of_isDiscreteValuationRing_le {R Ω : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field Ω] [Algebra R Ω] [IsFractionRing R Ω] (V : Subring Ω) (hle : (algebraMap R Ω).range ≤ V) (hne : V ≠ ⊤) : V = (algebraMap R Ω).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let π : Ω := algebraMap R Ω ϖ
  have hπ0 : π ≠ 0 := by
    show algebraMap R Ω ϖ ≠ 0
    intro h
    exact hϖ.ne_zero ((IsFractionRing.injective R Ω) (by simpa using h))
  have hπmem : π ∈ (algebraMap R Ω).range := ⟨ϖ, rfl⟩
  -- Every nonzero element of `Ω` is a unit of `R` times an integral power of `π`.
  have key : ∀ y : Ω, y ≠ 0 → ∃ (n : ℤ) (u : Rˣ), y = algebraMap R Ω (u : R) * π ^ n := by
    intro y hy
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := Ω) hϖ hy
    exact ⟨n, u, by rw [hu, Units.smul_def, Algebra.smul_def]⟩
  -- Step 1: an element of `V` outside the image of `R` forces `π⁻¹ ∈ V`.
  have hstep1 : (∃ x ∈ V, x ∉ (algebraMap R Ω).range) → π⁻¹ ∈ V := by
    rintro ⟨x, hxV, hxr⟩
    have hx0 : x ≠ 0 := by rintro rfl; exact hxr (Subring.zero_mem _)
    obtain ⟨n, u, hu⟩ := key x hx0
    have hu0 : algebraMap R Ω (u : R) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective R Ω)]
      exact Units.ne_zero u
    rcases le_or_gt (0 : ℤ) n with hn | hn
    · -- nonnegative exponent: `x` is in the image of `R`, contradiction
      exfalso
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
      apply hxr
      rw [hu, hm, zpow_natCast]
      exact ⟨(u : R) * ϖ ^ m, by rw [map_mul, map_pow]⟩
    · -- negative exponent: `x * π ^ m = algebraMap u * π⁻¹`
      obtain ⟨m, hm⟩ := Int.eq_negSucc_of_lt_zero hn
      have hxm : x * π ^ m = algebraMap R Ω (u : R) * π⁻¹ := by
        rw [hu, hm, zpow_negSucc, ← inv_pow, pow_succ]
        rw [show (algebraMap R Ω ↑u * ((π⁻¹) ^ m * π⁻¹)) * π ^ m
              = algebraMap R Ω ↑u * ((π⁻¹) ^ m * π ^ m) * π⁻¹ by ring]
        rw [← mul_pow, inv_mul_cancel₀ hπ0, one_pow, mul_one]
      rw [show π⁻¹ = (algebraMap R Ω (u : R))⁻¹ * (x * π ^ m) by
            rw [hxm, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]]
      exact V.mul_mem (hle ⟨((u⁻¹ : Rˣ) : R), map_units_inv (algebraMap R Ω) u⟩)
        (V.mul_mem hxV (V.pow_mem (hle hπmem) m))
  -- Step 2: any subring containing the image of `R` and `π⁻¹` is everything.
  have hstep2 : ∀ (S : Subring Ω), (algebraMap R Ω).range ≤ S → π⁻¹ ∈ S → S = ⊤ := by
    intro S hS hπinv
    rw [Subring.eq_top_iff']
    intro y
    by_cases hy : y = 0
    · rw [hy]; exact S.zero_mem
    obtain ⟨n, u, hu⟩ := key y hy
    rcases le_or_gt (0 : ℤ) n with hn | hn
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
      refine hS ?_
      rw [hu, hm, zpow_natCast]
      exact ⟨(u : R) * ϖ ^ m, by rw [map_mul, map_pow]⟩
    · obtain ⟨m, hm⟩ := Int.eq_negSucc_of_lt_zero hn
      rw [hu, hm, zpow_negSucc, ← inv_pow]
      exact S.mul_mem (hS ⟨(u : R), rfl⟩) (S.pow_mem hπinv (m + 1))
  refine le_antisymm (fun x hxV => ?_) hle
  by_contra hxr
  exact hne (hstep2 V hle (hstep1 ⟨x, hxV, hxr⟩))

end Work.MotV5.Nodes.UEPR
