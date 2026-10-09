import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H2locFin

/-- **The coinduced module `Coind_U^G M` is finite when `M` is finite and `M` is trivially acted
by `U` (of finite index in `G`).**

Mathematical content: the defining condition of `Coind G U M` is
`f (g * u) = u⁻¹ • f g`; with a trivial `U`-action this says exactly that `f` is constant on
left cosets of `U`, i.e. `f` factors through the finite quotient `G ⧸ U`.  Hence
`Coind G U M ↪ (G ⧸ U → M)`, which is finite because `U` has finite index and `M` is finite. -/
theorem coind_isFinite {G : Type*} [Group G] (U : Subgroup G) (hUn : U.Normal) [U.FiniteIndex]
    (M : Type*) [AddCommGroup M] [Finite M] [DistribMulAction U M]
    (htriv : ∀ (u : U) (m : M), u • m = m) :
    Finite (Work.SSGRoute.PT.Coind G U M) := by
  -- With a trivial `U`-action, the defining relation holds precisely on left cosets.
  have hconst : ∀ (f : Work.SSGRoute.PT.Coind G U M) (g : G) (u : U),
      (f : G → M) (g * (u : G)) = (f : G → M) g := by
    intro f g u
    rw [Work.SSGRoute.PT.Coind.coe_mul f g u, htriv]
  -- Descent of a coinduced function to the finite quotient `G ⧸ U`.
  let Φ : Work.SSGRoute.PT.Coind G U M → (G ⧸ U → M) := fun f =>
    Quotient.lift (fun g => (f : G → M) g) (fun a b hab => by
      have h1 : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b
      have h2 := hconst f a ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩
      rw [h1] at h2
      exact h2.symm)
  have hΦ : ∀ (f : Work.SSGRoute.PT.Coind G U M) (g : G),
      Φ f (Quotient.mk (QuotientGroup.leftRel U) g) = (f : G → M) g := by
    intro f g
    exact Quotient.lift_mk _ _ g
  refine Finite.of_injective Φ ?_
  intro f f' h
  apply Subtype.ext
  funext g
  have h1 := congrFun h (Quotient.mk (QuotientGroup.leftRel U) g)
  rw [hΦ f g, hΦ f' g] at h1
  exact h1

end Work.SSGRoute.H2locFin
