import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.sha1_descent_H1
import Submission.Work.GroupCohomology.H1_zmod_module
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Extension of a functional along the Hasse descent.**

For a number field `k` with algebraic closure `Ω`, a finite Galois extension `K/k` inside `Ω`
and a finite `𝔽_p[Gal(K/k)]`-module `M`, the Hasse descent
`Work.SSGRoute.sha1DescentHom : Ш¹(k,M) →+ H¹(Gal(K/k), M)` is injective
(`Work.SSGRoute.sha1DescentHom_injective`).  Hence any `𝔽_p`-linear functional
`l : Ш¹(k,M) →ₗ 𝔽_p` can be extended along it: after endowing `H¹(Gal(K/k), M)` with the
`𝔽_p`-module structure of `Work.GroupCohomology.H1_zmod_module`, there is
`L : H¹(Gal(K/k), M) →ₗ 𝔽_p` with `L ∘ sha1DescentHom = l`.

The extension exists because `𝔽_p = ZMod p` is a field, so a linear functional defined on the
subspace `range (sha1DescentHom)` extends to the whole space
(`LinearMap.exists_extend`). -/
theorem exists_linearMap_extend_sha1Descent (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (l : Work.SSGRoute.Sha1 p k Ω K M →ₗ[ZMod p] ZMod p) :
    ∃ (inst : Module (ZMod p) (Work.GroupCohomology.H1 (K ≃ₐ[k] K) M)),
      (letI := inst
       ∃ L : Work.GroupCohomology.H1 (K ≃ₐ[k] K) M →ₗ[ZMod p] ZMod p,
         ∀ a : Work.SSGRoute.Sha1 p k Ω K M,
           L ((Work.SSGRoute.sha1DescentHom p k Ω K M).toZModLinearMap p a) = l a) := by
  refine ⟨Work.GroupCohomology.H1zmod.instH1 p (K ≃ₐ[k] K) M, ?_⟩
  -- The `𝔽_p`-module structure on `H¹(Gal(K/k), M)`.
  letI : Module (ZMod p) (Work.GroupCohomology.H1 (K ≃ₐ[k] K) M) :=
    Work.GroupCohomology.H1zmod.instH1 p (K ≃ₐ[k] K) M
  -- The descent, as an `𝔽_p`-linear map.
  let ι : Work.SSGRoute.Sha1 p k Ω K M →ₗ[ZMod p]
      Work.GroupCohomology.H1 (K ≃ₐ[k] K) M :=
    (sha1DescentHom p k Ω K M).toZModLinearMap p
  have hι : Function.Injective ι := by
    intro a b hab
    exact sha1DescentHom_injective p k Ω K M (by simpa [ι] using hab)
  -- Extend the functional `l`, transported along the linear equivalence `Ш¹ ≅ range ι`.
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (p := LinearMap.range ι)
    (l.comp (LinearEquiv.ofInjective ι hι).symm.toLinearMap)
  refine ⟨L, fun a => ?_⟩
  have h1 := LinearMap.congr_fun hL ⟨ι a, LinearMap.mem_range_self ι a⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
  have h3 : (LinearEquiv.ofInjective ι hι).symm ⟨ι a, LinearMap.mem_range_self ι a⟩ = a := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (LinearEquiv.ofInjective_apply (h := hι) ι a).symm
  rw [h1]
  exact congrArg l h3

end Work.SSGRoute
