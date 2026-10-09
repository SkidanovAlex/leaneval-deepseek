import Mathlib
import Submission.Work.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

/-- `Gal(L/K)` acts on a chosen `n`-th root `α` of `a ∈ Kˣ ∩ (Lˣ)^n` by the Kummer character:
`σ α = χ(σ) · α`, where `χ(σ) = σ α / α ∈ μ_n(K)` viewed as an element of `K`. -/
theorem algEquiv_apply_kummerRoot {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (a : kummerSubgroup n K L)
    (σ : Gal(L/K)) :
    (σ : L ≃ₐ[K] L) (kummerRoot a : L) =
      algebraMap K L (((kummerCharacter hζ a σ : rootsOfUnity n K) : Kˣ) : K) * (kummerRoot a : L) := by
  -- `map_kummerCharacter_apply` says `↑χ(σ) = σ α / α` as units of `L`; evaluate in `L`.
  have h := congrArg (fun u : Lˣ => (u : L)) (map_kummerCharacter_apply hζ a σ)
  rw [kummerRatio_coe, Units.coe_map] at h
  rw [eq_div_iff (Units.ne_zero (kummerRoot a))] at h
  exact h.symm

end Work.Kummer
