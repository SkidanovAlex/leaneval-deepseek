import Mathlib
import Submission.Work.Kummer.Pairing
import Submission.Work.Kummer.kummerCharacter_apply_of_pow_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

theorem kummerCharacter_eq_of_kummerRatio_eq {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (χ : Gal(L/K) →* rootsOfUnity n K) (β : Lˣ) (a : Kˣ)
    (hpow : β ^ n = Units.map (algebraMap K L) a)
    (hratio : ∀ σ : Gal(L/K),
      kummerRatio σ β = Units.map (algebraMap K L) ((χ σ : rootsOfUnity n K) : Kˣ)) :
    kummerCharacter hζ ⟨a, ⟨β, hpow⟩⟩ = χ := by
  have hα : ((β : L)) ^ n = algebraMap K L ((a : Kˣ) : K) := by
    have := congrArg (fun u : Lˣ => (u : L)) hpow
    simpa [Units.coe_map] using this
  refine MonoidHom.ext fun σ => ?_
  apply Subtype.ext
  apply Units.map_injective (algebraMap K L).injective
  exact (kummerCharacter_apply_of_pow_eq hζ (⟨β, hpow⟩ : a ∈ kummerSubgroup n K L) hα σ).trans
    (hratio σ)

end Work.Kummer
