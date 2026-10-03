import Mathlib
import Submission.Work.ORHughesFree.Rat.WordModel.Defs

namespace Work.ORHughesFree.Rat.WordModel

/-- **`σ ∘ ρ = id` on `Rat(U)`**: the composite of the universal morphism
`ρ : Rat(U) → ℕ[M]` into the word model and the value map `σ : ℕ[M] → Rat(U)` is the identity.

Both `ρ` and `σ` are ring homomorphisms, and `ρ` moreover respects the rational `U`-semiring
structure (`RatU.lift_isHom`), while `σ` does so too because `σ` of a monomial is `Mval`, which is
compatible with the `⋄`-operation on the word model by construction (`letterOf_val`,
`sumVal_toList`).  Hence `σ ∘ ρ` is a morphism of rational `U`-semirings `Rat(U) → Rat(U)`, and by
the uniqueness `RatU.lift_unique` it equals the identity. -/
theorem sigma_rho {U : Type} [Group U] (x : Work.ORHughesFree.RatU U) :
    Work.ORHughesFree.Rat.WordModel.sigma (Work.ORHughesFree.Rat.WordModel.rho x) = x := by
  have hid : IsRationalUSemiringHom (RatU.rational (U := U)) (RatU.rational (U := U))
      (RingHom.id (RatU U)) := ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hcomp : IsRationalUSemiringHom (RatU.rational (U := U)) (RatU.rational (U := U))
      (sigma.comp rho) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      show sigma (rho (RatU.ratOp y)) = RatU.ratOp (sigma (rho y))
      have h1 : rho (RatU.ratOp y) = rS.ratOp (rho y) :=
        (RatU.lift_isHom (S U) rS).map_rat y
      rw [h1]
      change sigma (rSRatOp U (rho y)) = RatU.ratOp (sigma (rho y))
      by_cases hy : sigma (rho y) = 0
      · rw [rSRatOp_of_eq_zero hy, map_zero, hy]
        exact RatU.ratOp_zero.symm
      · rw [rSRatOp_of_ne hy, sigma_letterOf, letterOf_val, sumVal_toList, ← sigma_apply]
    · intro u y
      show sigma (rho (RatU.smul u y)) = RatU.smul u (sigma (rho y))
      have h : rho (RatU.smul u y) = rS.smul u (rho y) :=
        (RatU.lift_isHom (S U) rS).map_smul u y
      rw [h]
      show sigma (rS.smul u (rho y)) = RatU.smul u (sigma (rho y))
      rw [show rS.smul u (rho y) = MonoidAlgebra.single (Mu u) 1 * rho y from rfl,
        map_mul, sigma_single, one_smul, Mval_Mu, RatU.smul_eq_ofGroup_mul]
    · intro y u
      show sigma (rho (RatU.smulRight y u)) = RatU.smulRight (sigma (rho y)) u
      have h : rho (RatU.smulRight y u) = rS.smulRight (rho y) u :=
        (RatU.lift_isHom (S U) rS).map_smulRight y u
      rw [h]
      show sigma (rS.smulRight (rho y) u) = RatU.smulRight (sigma (rho y)) u
      rw [show rS.smulRight (rho y) u = rho y * MonoidAlgebra.single (Mu u) 1 from rfl,
        map_mul, sigma_single, one_smul, Mval_Mu, RatU.smulRight_eq_mul_ofGroup]
  have h1 : sigma.comp rho = RatU.lift (RatU U) (RatU.rational (U := U)) :=
    RatU.lift_unique (RatU U) (RatU.rational (U := U)) _ hcomp
  have h2 : RingHom.id (RatU U) = RatU.lift (RatU U) (RatU.rational (U := U)) :=
    RatU.lift_unique (RatU U) (RatU.rational (U := U)) _ hid
  have h3 : sigma.comp rho = RingHom.id (RatU U) := by rw [h1, ← h2]
  have h4 := congrArg (fun f : RatU U →+* RatU U => f x) h3
  simpa using h4

end Work.ORHughesFree.Rat.WordModel
