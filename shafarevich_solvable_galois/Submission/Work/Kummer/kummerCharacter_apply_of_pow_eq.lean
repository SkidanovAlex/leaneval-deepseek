import Mathlib
import Submission.Work.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

theorem kummerCharacter_apply_of_pow_eq {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) {a : Kˣ}
    (ha : a ∈ kummerSubgroup n K L) {α : Lˣ} (hα : (α : L) ^ n = algebraMap K L (a : K))
    (σ : Gal(L/K)) :
    Units.map (algebraMap K L) (((kummerCharacter hζ ⟨a, ha⟩ σ : rootsOfUnity n K)) : Kˣ) =
      kummerRatio σ α := by
  rw [map_kummerCharacter_apply hζ ⟨a, ha⟩ σ]
  exact kummerRatio_congr hζ hα (kummerRoot_pow_val ⟨a, ha⟩) σ

end Work.Kummer
