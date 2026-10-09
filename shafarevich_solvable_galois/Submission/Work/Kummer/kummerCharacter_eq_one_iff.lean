import Mathlib
import Submission.Work.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


universe u v
namespace Work.Kummer

theorem kummerCharacter_eq_one_iff {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (a : kummerSubgroup n K L) :
    kummerCharacter hζ a = 1 ↔ (a : Kˣ) ∈ nthPowerSubgroup n Kˣ := by
  constructor
  · intro ha
    -- The Kummer character is trivial, so every `σ` fixes the chosen `n`-th root `α` of `a`.
    have hfix : ∀ σ : Gal(L/K), (σ : L ≃ₐ[K] L) (kummerRoot a : L) = (kummerRoot a : L) := by
      intro σ
      have hσ : kummerCharacter hζ a σ = 1 := by rw [ha]; rfl
      have hratio : kummerRatio σ (kummerRoot a) = 1 := by
        have h := map_kummerCharacter_apply hζ a σ
        rw [hσ] at h
        simpa using h.symm
      have h' : algEquivUnitsMap (σ : L ≃ₐ[K] L) (kummerRoot a) = kummerRoot a := by
        have h2 := hratio
        rw [kummerRatio] at h2
        exact div_eq_one.mp h2
      have h3 := congrArg (fun u : Lˣ => (u : L)) h'
      simpa [algEquivUnitsMap_coe] using h3
    -- Hence `α` lies in `K`, and `a = α ^ n` is an `n`-th power in `Kˣ`.
    obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (kummerRoot a : L)).mpr hfix
    have hk0 : k ≠ 0 := by
      intro hk0
      have hz : (kummerRoot a : L) = 0 := by rw [← hk, hk0, map_zero]
      exact Units.ne_zero (kummerRoot a) hz
    refine ⟨Units.mk0 k hk0, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    have hp := kummerRoot_pow_val a
    rw [← hk, ← map_pow] at hp
    exact (algebraMap K L).injective hp
  · intro ha
    -- Conversely an `n`-th power in `Kˣ` is an `n`-th power in `Lˣ`, giving the trivial character.
    refine kummerCharacter_eq_one_of_mem_nthPower hζ ?_
    rw [Subgroup.mem_subgroupOf]
    exact ha

end Work.Kummer
