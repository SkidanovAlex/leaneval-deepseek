import Mathlib
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup
import Submission.NK.NUV2.RouteC.map_norm_eq_zero

open scoped BigOperators
open CategoryTheory

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable {G : Type} [Group G] [Fintype G]

set_option backward.isDefEq.respectTransparency false in
/-- **The upward half of the cyclic criterion, over `ℤ`.**

For `A : Rep ℤ G`, a morphism `φ : trivial ℤ G ℤ ⟶ A` and a class `c ∈ H²(G, ℤ)`: if the element
`φ(1) : A` lies in the image of the norm map `A.norm : A → A`, then `map φ 2 c = 0`.

No cyclicity is needed: this holds for every finite group `G` and every `c`.  The proof factors
`φ` through the *regular representation* `ℤ[G]`, which is acyclic in positive degrees
(`NK.NUV2.RouteC.subsingleton_groupCohomology_leftRegular`): writing `φ(1) = N(x)` and `Ψ` for
the `ℤ[G]`-module map `ℤ[G] ⟶ A`, `σ ↦ ρ_σ x`,

`φ = (tr : ℤ ⟶ ℤ[G], 1 ↦ ∑_σ σ) ≫ Ψ`  (both sides send `1` to `∑_σ ρ_σ x = N(x) = φ(1)`),

and `map tr 2 c = 0` because `H²(G, ℤ[G]) = 0`.

The hypothesis is stated as `∃ x, A.norm.hom x = φ.hom 1` rather than as membership in
`LinearMap.range A.norm.hom.toLinearMap`, because over `ℤ` the two `ℤ`-module structures on `A.V`
(`Rep.hV2` versus `AddCommGroup.toIntModule`) make the `Submodule` form awkward; the two forms are
interchangeable, and the proof below installs a local instance of `Rep.hV2` to work with the linear
maps. -/
theorem map_eq_zero_of_mem_range_norm (A : Rep ℤ G)
    (φ : Rep.trivial ℤ G ℤ ⟶ A) (c : groupCohomology (Rep.trivial ℤ G ℤ) 2)
    (ha : ∃ x : A, A.norm.hom x = φ.hom 1) :
    (groupCohomology.map (MonoidHom.id G) φ 2) c = 0 := by
  classical
  obtain ⟨x, hx⟩ := ha
  letI : Module ℤ A.V := A.hV2
  have hkey : (φ.hom) 1 =
      (Rep.leftRegularHom A x).hom (NK.NUV2.RouteC.leftRegularTrace (G := G)) := by
    have hsum : (Rep.leftRegularHom A x).hom (NK.NUV2.RouteC.leftRegularTrace (G := G))
        = ∑ σ : G, A.ρ σ x := by
      rw [NK.NUV2.RouteC.leftRegularTrace, map_sum]
      exact Finset.sum_congr rfl (fun σ _ => by rw [Rep.leftRegularHom_hom_single]; simp)
    rw [hsum]
    exact hx.symm.trans (NK.NUV2.RouteC.norm_apply_eq_sum A x)
  have hfac : φ = NK.NUV2.RouteC.traceHom (G := G) ≫ Rep.leftRegularHom A x := by
    apply Rep.hom_ext
    rw [Representation.IntertwiningMap.ext_iff]
    apply LinearMap.ext
    intro n
    show (φ.hom.toLinearMap) n
      = (Rep.leftRegularHom A x).hom.toLinearMap
        ((NK.NUV2.RouteC.traceHom (G := G)).hom.toLinearMap n)
    have hlin : (φ.hom.toLinearMap) n = n • (φ.hom.toLinearMap) 1 := by
      simpa using map_zsmul (φ.hom.toLinearMap) n (1 : ℤ)
    rw [hlin, NK.NUV2.RouteC.traceHom_apply, map_zsmul]
    exact congrArg (fun z => n • z) hkey
  have hmap : (groupCohomology.map (MonoidHom.id G) φ 2) c
      = (groupCohomology.map (MonoidHom.id G) (Rep.leftRegularHom A x) 2)
        ((groupCohomology.map (MonoidHom.id G) (NK.NUV2.RouteC.traceHom (G := G)) 2) c) := by
    rw [hfac, groupCohomology.map_id_comp]
    rfl
  haveI : Subsingleton (groupCohomology (Rep.leftRegular ℤ G) 2) :=
    NK.NUV2.RouteC.subsingleton_groupCohomology_leftRegular (G := G) 1
  have h0 : (groupCohomology.map (MonoidHom.id G) (NK.NUV2.RouteC.traceHom (G := G)) 2) c = 0 :=
    Subsingleton.elim _ _
  rw [hmap, h0]
  exact map_zero _

end NK.NUV2.RouteE
