import Mathlib
import Submission.Work.SSGRoute.sha2_defs
import Submission.Work.SSGRoute.range_mapH3_eq_ker_mapH3
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

/-- **Coefficient reduction of `H³`-vanishing to the one-dimensional case.**

If `Γ` acts trivially on a finite `𝔽_p`-module `M` of dimension one — so that `M` is *isomorphic*
to `𝔽_p` as a `Γ`-module, the action being trivial on both sides — then `H³(Γ,M)` is a subsingleton
as soon as the same holds for the trivial module `𝔽_p = Triv p`.

Indeed, an isomorphism `e : M ≃ₗ[𝔽_p] 𝔽_p` of coefficient modules is automatically `Γ`-equivariant
(the action on both sides is trivial), so it induces a map `e_* : H³(Γ,M) → H³(Γ,𝔽_p)` and
`(e⁻¹)_*` is a left inverse of it by the computation rule `mapH3_H3π`; a map with a left inverse is
injective, and a map into a subsingleton out of a type is surjective onto a point, whence the source
is a subsingleton. -/
theorem h3_subsingleton_of_finrank_eq_one {p : ℕ} [Fact p.Prime] {Γ M : Type} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction Γ M] [Finite M] (htriv : ∀ (g : Γ) (m : M), g • m = m)
    (hdim : Module.finrank (ZMod p) M = 1)
    (h : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p) Γ)) :
    Subsingleton (Work.SSGRoute.H3 (M := M) Γ) := by
  -- a one-dimensional `𝔽_p`-module is isomorphic to `𝔽_p`
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one (R := ZMod p) (M := M) hdim
  -- both coefficient isomorphisms are `Γ`-equivariant, the actions being trivial
  have hφ : Work.GroupCohomology.IsEquivariant Γ
      ((e.symm : M →ₗ[ZMod p] ZMod p).toAddMonoidHom) := by
    intro g m
    show e.symm (g • m) = g • e.symm m
    rw [htriv g m]
    rfl
  have hψ : Work.GroupCohomology.IsEquivariant Γ
      ((e : ZMod p →ₗ[ZMod p] M).toAddMonoidHom) := by
    intro g x
    show e (g • x) = g • e x
    rw [htriv g (e x)]
    rfl
  -- `(e⁻¹)_*` is a left inverse of `e_*`, by the computation rule on the classes of cocycles
  have hcomp : ∀ x : Work.SSGRoute.H3 (M := M) Γ,
      Work.SSGRoute.H3Map.mapH3 ((e : ZMod p →ₗ[ZMod p] M).toAddMonoidHom) hψ
        (Work.SSGRoute.H3Map.mapH3 ((e.symm : M →ₗ[ZMod p] ZMod p).toAddMonoidHom) hφ x) = x := by
    intro x
    induction x using Work.SSGRoute.H3Map.H3_induction_on with
    | _ c =>
      rw [Work.SSGRoute.H3Map.mapH3_H3π, Work.SSGRoute.H3Map.mapH3_H3π]
      congr 1
      exact Subtype.ext (funext fun q => by
        rw [Work.SSGRoute.H3Map.mapZ3_apply, Work.SSGRoute.H3Map.mapZ3_apply]
        exact LinearEquiv.apply_symm_apply e (c.1 q))
  refine ⟨fun a b => ?_⟩
  have hab : Work.SSGRoute.H3Map.mapH3 ((e.symm : M →ₗ[ZMod p] ZMod p).toAddMonoidHom) hφ a
      = Work.SSGRoute.H3Map.mapH3 ((e.symm : M →ₗ[ZMod p] ZMod p).toAddMonoidHom) hφ b :=
    h.allEq _ _
  have h1 := congrArg (Work.SSGRoute.H3Map.mapH3 ((e : ZMod p →ₗ[ZMod p] M).toAddMonoidHom) hψ) hab
  rw [hcomp a, hcomp b] at h1
  exact h1

end Work.SSGRoute.PTembedding
