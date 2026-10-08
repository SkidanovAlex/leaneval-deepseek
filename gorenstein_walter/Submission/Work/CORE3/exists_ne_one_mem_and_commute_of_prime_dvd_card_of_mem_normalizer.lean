import Mathlib

set_option linter.style.haveILetI false

namespace Work.CORE3

/-- The value of the conjugation action of `N(F)` on `F` is `g * x * g⁻¹`. -/
lemma coe_smul_normalizer {G : Type} [Group G] (F : Subgroup G)
    (g : Subgroup.normalizer (F : Set G)) (x : F) :
    ((g • x : F) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl

theorem exists_ne_one_mem_and_commute_of_prime_dvd_card_of_mem_normalizer {G : Type} [Group G]
    [Finite G] {F : Subgroup G} {b : G} {r : ℕ} (hr : r.Prime)
    (hbN : b ∈ Subgroup.normalizer (F : Set G)) (hborder : orderOf b = r)
    (hdvd : r ∣ Nat.card F) : ∃ c ∈ F, c ≠ 1 ∧ b * c = c * b := by
  -- `b` generates a cyclic `r`-group acting on `F` by conjugation.
  haveI : Fact r.Prime := ⟨hr⟩
  have hHle : Subgroup.zpowers b ≤ Subgroup.normalizer (F : Set G) :=
    Subgroup.zpowers_le.mpr hbN
  letI : MulAction (Subgroup.zpowers b) F := MulAction.compHom F (Subgroup.inclusion hHle)
  have hcard : Nat.card (Subgroup.zpowers b) = r := by
    rw [Nat.card_zpowers, hborder]
  have hP : IsPGroup r (Subgroup.zpowers b) := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  -- The identity is a fixed point of the action.
  have ha : (⟨1, F.one_mem⟩ : F) ∈ MulAction.fixedPoints (Subgroup.zpowers b) F := by
    rw [MulAction.mem_fixedPoints]
    intro h
    apply Subtype.ext
    rw [MulAction.compHom_smul_def, coe_smul_normalizer, Subgroup.coe_inclusion]
    simp
  -- Since `r ∣ |F|`, the number of fixed points is a positive multiple of `r`, so there is a
  -- fixed point different from the identity.
  obtain ⟨c, hcfix, hcne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point F hdvd ha
  refine ⟨(c : G), c.2, ?_, ?_⟩
  · intro hcon
    exact hcne (Subtype.ext hcon.symm)
  · -- `b` fixes `c`, i.e. `b * c * b⁻¹ = c`, which is exactly `b * c = c * b`.
    have hb_fix := (MulAction.mem_fixedPoints.mp hcfix) ⟨b, Subgroup.mem_zpowers b⟩
    have hval : b * (c : G) * b⁻¹ = (c : G) := by
      have hh := congrArg Subtype.val hb_fix
      simpa [MulAction.compHom_smul_def, coe_smul_normalizer, Subgroup.coe_inclusion] using hh
    exact mul_inv_eq_iff_eq_mul.mp hval

end Work.CORE3
