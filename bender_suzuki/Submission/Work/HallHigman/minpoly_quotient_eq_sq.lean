import Mathlib
import Submission.Work.HallHigman.minpoly_eq_X_sub_one_sq_of_sq_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

open Polynomial

/-- If an endomorphism `f` satisfies `(f - 1)^2 = 0` but `f ≠ 1`, then its minimal polynomial
over the base field is exactly `(X - 1)^2`.

For the quotient representation the endomorphism `(ρ.quotient W) x` of `M ⧸ W` is the induced
map of `ρ x`.  Since `(ρ x - 1)` is killed by the quotient map `M → M ⧸ W` and `M ⧸ W` is a
quotient of `M`, we get `((ρ.quotient W) x - 1)^2 = 0`; together with the hypothesis
`(ρ.quotient W) x ≠ 1` the general criterion applies. -/
theorem minpoly_quotient_eq_sq {p : ℕ} [Fact p.Prime] {G M : Type*} [Group G]
    [AddCommGroup M] [Module (ZMod p) M] (ρ : Representation (ZMod p) G M)
    (W : Submodule (ZMod p) M) (hW : ∀ g, W ≤ W.comap (ρ g)) (x : G)
    (hsq : (ρ x - 1) ^ 2 = 0) (hne : (Representation.quotient ρ W hW) x ≠ 1) :
    minpoly (ZMod p) ((Representation.quotient ρ W hW) x) = (Polynomial.X - 1) ^ 2 := by
  have hq : (Representation.quotient ρ W hW) x = W.mapQ W (ρ x) (hW x) :=
    Representation.quotient_apply ρ W hW x
  -- The induced map on the quotient intertwines the projection `M → M ⧸ W` with `ρ x - 1`.
  have hmid : (((Representation.quotient ρ W hW) x) - 1).comp W.mkQ = W.mkQ.comp (ρ x - 1) := by
    rw [hq, LinearMap.sub_comp, LinearMap.comp_sub]
    simp only [Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
    rw [Submodule.mapQ_mkQ W W (ρ x)]
  -- Hence `((ρ.quotient W) x - 1)^2` is killed by the (surjective) projection, so it vanishes.
  have hsq' : (((Representation.quotient ρ W hW) x) - 1) ^ 2 = 0 := by
    have key : ((((Representation.quotient ρ W hW) x) - 1) ^ 2).comp W.mkQ = 0 := by
      rw [pow_two, Module.End.mul_eq_comp]
      rw [LinearMap.comp_assoc, hmid]
      rw [← LinearMap.comp_assoc, hmid]
      rw [LinearMap.comp_assoc]
      rw [show (ρ x - 1).comp (ρ x - 1) = (ρ x - 1) ^ 2 by rw [pow_two, Module.End.mul_eq_comp]]
      rw [hsq, LinearMap.comp_zero]
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W z
    have h := LinearMap.congr_fun key v
    rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h
  exact minpoly_eq_X_sub_one_sq_of_sq_eq_zero hsq' hne

end Work.HallHigman
