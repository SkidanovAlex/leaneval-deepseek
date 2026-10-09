import Mathlib
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
import Submission.Work.SSGRoute.PTdualControl.h3Exactness
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Functoriality of `H³` in the coefficient module

`Work.SSGRoute.H3Map.mapH3 φ hφ : H³(G,M) →+ H³(G,N)` is the push-forward along an equivariant
additive map `φ : M →+ N` of `G`-modules (`Submission/Work/SSGRoute/PTdualControl/mapH3.lean`).
This file supplies the two functoriality identities that the degree-`3` arguments
(`EulerSymm/h3CoprimeIndex`, the Shapiro/p-Sylow transfer) need and that the tree does not yet
have:

* `mapH3_comp` — `H³(ψ ∘ φ) = H³(ψ) ∘ H³(φ)`;
* `mapH3_id` — `H³(id) = id`.

Both are proved by quotient induction on `H³` (`Work.SSGRoute.H3_induction_on`) together with the
cocycle-level computation `mapH3_H3π`.
-/

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.EulerSymm

/-- **Functoriality of `H³(-)` in the coefficient module.** -/
theorem mapH3_comp {G : Type*} [TopologicalSpace G] [Group G] {M N P : Type*}
    [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]
    [AddCommGroup P] [DistribMulAction G P]
    (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (ψ : N →+ P) (hψ : Work.GroupCohomology.IsEquivariant G ψ) :
    (Work.SSGRoute.H3Map.mapH3 ψ hψ).comp (Work.SSGRoute.H3Map.mapH3 φ hφ)
      = Work.SSGRoute.H3Map.mapH3 (ψ.comp φ) (hψ.comp hφ) := by
  refine AddMonoidHom.ext (fun z => ?_)
  refine Work.SSGRoute.H3_induction_on
    (C := fun w => (Work.SSGRoute.H3Map.mapH3 ψ hψ) (Work.SSGRoute.H3Map.mapH3 φ hφ w)
      = (Work.SSGRoute.H3Map.mapH3 (ψ.comp φ) (hψ.comp hφ)) w) z (fun c => ?_)
  rw [Work.SSGRoute.H3Map.mapH3_H3π φ hφ c,
    Work.SSGRoute.H3Map.mapH3_H3π ψ hψ (Work.SSGRoute.H3Map.mapZ3 φ hφ c),
    Work.SSGRoute.H3Map.mapH3_H3π (ψ.comp φ) (hψ.comp hφ) c]
  have hz : Work.SSGRoute.H3Map.mapZ3 ψ hψ (Work.SSGRoute.H3Map.mapZ3 φ hφ c)
      = Work.SSGRoute.H3Map.mapZ3 (ψ.comp φ) (hψ.comp hφ) c := by
    refine Subtype.ext ?_
    funext q
    rfl
  rw [hz]

/-- **`mapH3` of the identity is the identity.** -/
theorem mapH3_id {G : Type*} [TopologicalSpace G] [Group G] {M : Type*}
    [AddCommGroup M] [DistribMulAction G M] :
    Work.SSGRoute.H3Map.mapH3 (AddMonoidHom.id M) (fun g m => rfl)
      = AddMonoidHom.id (Work.SSGRoute.H3 (M := M) G) := by
  refine AddMonoidHom.ext (fun z => ?_)
  refine Work.SSGRoute.H3_induction_on
    (C := fun w => (Work.SSGRoute.H3Map.mapH3 (AddMonoidHom.id M) (fun g m => rfl)) w = w)
    z (fun c => ?_)
  rw [Work.SSGRoute.H3Map.mapH3_H3π (AddMonoidHom.id M) (fun g m => rfl) c]
  have hz : Work.SSGRoute.H3Map.mapZ3 (AddMonoidHom.id M) (fun g m => rfl) c = c := by
    refine Subtype.ext ?_
    funext q
    rfl
  rw [hz]

end Work.SSGRoute.EulerSymm
