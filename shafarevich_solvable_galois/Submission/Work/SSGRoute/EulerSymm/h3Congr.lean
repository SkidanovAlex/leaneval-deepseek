import Mathlib
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
import Submission.Work.SSGRoute.PTdualControl.h3Exactness
import Submission.Work.SSGRoute.EulerSymm.h3Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Isomorphism invariance of `H³` in the coefficient module

For an equivariant additive isomorphism `e : M ≃+ N` of `G`-modules, `mapH3 e` is an additive
isomorphism `H³(G,M) ≃+ H³(G,N)`.

This is the first component of node **A6(b)** of the H³ plan: once the Sylow-preimage `D_P` is known
to act *trivially* on `μ_p` (equivalently `μ_p ≅ 𝔽_p` as `D_P`-modules), the arithmetic input
`H³(D_P, μ_p) = 0` produced by the Kummer/Brauer argument transports to the *trivial-coefficient*
input `H³(D_P, 𝔽_p) = 0` consumed by the dévissage `EulerSymm/h3Devissage`.

The retraction identities are proved at the **cochain level** (`mapZ3_apply` plus the equivalence
laws `e.symm_apply_apply`/`e.apply_symm_apply` pointwise), which avoids rewriting
`e.symm ∘ e = id` *inside* the proof argument of `mapH3` — the `motive is not type correct`
obstruction.
-/

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.EulerSymm

variable {G : Type*} [TopologicalSpace G] [Group G] {M N : Type*}
  [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]

/-- **`H³` is invariant under an equivariant additive isomorphism of coefficients.** -/
theorem h3AddEquivCongr (e : M ≃+ N) (he : ∀ (g : G) (m : M), e (g • m) = g • e m) :
    Nonempty (Work.SSGRoute.H3 (M := M) G ≃+ Work.SSGRoute.H3 (M := N) G) := by
  have he' : ∀ (g : G) (n : N), e.symm (g • n) = g • e.symm n := by
    intro g n
    refine e.injective ?_
    rw [e.apply_symm_apply, he g (e.symm n), e.apply_symm_apply]
  refine ⟨{ toFun := Work.SSGRoute.H3Map.mapH3 e.toAddMonoidHom he
            invFun := Work.SSGRoute.H3Map.mapH3 e.symm.toAddMonoidHom he'
            left_inv := ?_
            right_inv := ?_
            map_add' := fun x y => (Work.SSGRoute.H3Map.mapH3 e.toAddMonoidHom he).map_add x y }⟩
  · intro x
    refine Work.SSGRoute.H3_induction_on
      (C := fun w => Work.SSGRoute.H3Map.mapH3 e.symm.toAddMonoidHom he'
        (Work.SSGRoute.H3Map.mapH3 e.toAddMonoidHom he w) = w) x (fun c => ?_)
    rw [Work.SSGRoute.H3Map.mapH3_H3π e.toAddMonoidHom he c,
      Work.SSGRoute.H3Map.mapH3_H3π e.symm.toAddMonoidHom he'
        (Work.SSGRoute.H3Map.mapZ3 e.toAddMonoidHom he c)]
    congr 1
    refine Subtype.ext (funext fun p => ?_)
    show e.symm (e ((c : G × G × G → M) p)) = (c : G × G × G → M) p
    rw [AddEquiv.symm_apply_apply]
  · intro x
    refine Work.SSGRoute.H3_induction_on
      (C := fun w => Work.SSGRoute.H3Map.mapH3 e.toAddMonoidHom he
        (Work.SSGRoute.H3Map.mapH3 e.symm.toAddMonoidHom he' w) = w) x (fun c => ?_)
    rw [Work.SSGRoute.H3Map.mapH3_H3π e.symm.toAddMonoidHom he' c,
      Work.SSGRoute.H3Map.mapH3_H3π e.toAddMonoidHom he
        (Work.SSGRoute.H3Map.mapZ3 e.symm.toAddMonoidHom he' c)]
    congr 1
    refine Subtype.ext (funext fun p => ?_)
    show e (e.symm ((c : G × G × G → N) p)) = (c : G × G × G → N) p
    rw [AddEquiv.apply_symm_apply]

end Work.SSGRoute.EulerSymm
