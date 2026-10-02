import Mathlib
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.RelCup
import Submission.Work.Endgame.VkClean.sph3DiscRelCapPairUnimodular
import Submission.Work.Cohomology.Crux.ovlUnimodularAux
import Submission.Work.Cohomology.Crux.vkInternalTransgression
import Submission.Work.Cohomology.Crux.ovlRestrSurjectiveFinal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Lefschetz-duality unimodularity of `(Vk(-2), Mk(-2))` in the capped-world universe

The module reproduces `Work.Cohomology.Crux.vk_relCapPair_unimodular` with a taint-free import
closure.  The three inputs of the original proof are

* the internal Mayer--Vietoris transgression identity
  `Work.Cohomology.Crux.vkInternalTransgression` (taint-free),
* the surjectivity of the overlap restriction
  `Work.Cohomology.Crux.ovlRestrSurjectiveFinal` (taint-free),
* the *sharp* unimodularity of the overlap pairing `Work.Cohomology.Crux.ovlUnimodular`, which is
  tainted through the model theorem `Work.Cohomology.sph3Disc_relCapPair_unimodular`
  (`dualZ` / `prodSphereAux`).

Here the last input is replaced by `ovlUnimodularClean`, obtained by the *same* transport
`Work.Cohomology.Crux.ovlUnimodularOfPairMap` of the model theorem, but of the clean
(`dualZ`/`prodSphereAux`-free) copy of that model theorem in
`Submission/Work/Endgame/VkClean/sph3DiscRelCapPairUnimodular.lean` (which itself is the copy of
`Submission/Work/Cohomology/sph3Disc_relCapPair_unimodular.lean` with its two tainted inputs
replaced by the clean transplants of `Submission/Work/Cohomology/CompatTrans/`).
-/

namespace Work.Endgame

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology Work.Cohomology.Crux

noncomputable section

/-- **Unimodularity of the overlap pairing, in the capped-world-compatible universe.**

This is the clean re-derivation of `Work.Cohomology.Crux.ovlUnimodular`: the overlap
`(vkOvl, vkOvlA) = (U ∩ V, (U ∩ V) ∩ Mk(-2))` of the two chart images of `Vk (-2)` has a relative
homology class in degree `7` whose cap product with the relative cohomology in degree `4` is onto
`H₃(U ∩ V)`.

It is the transport of the model computation `sph3Disc_relCapPair_unimodular` for
`(S³ × D⁴, S³ × S³)` along the map of pairs `vkOvl_model_pair_map`, exactly as in
`Work.Cohomology.Crux.ovlUnimodular`, but using the clean (`dualZ`/`prodSphereAux`-free) copy of the
model theorem. -/
theorem ovlUnimodularClean :
    ∃ w : (relChains vkOvl vkOvlA).homology 7,
      Function.Surjective (fun u : relCohomology ℤ vkOvl vkOvlA 4 =>
        relCapPair vkOvl vkOvlA 4 3 u w) := by
  obtain ⟨f, g, hw, h3, _h3A, h7⟩ := vkOvl_model_pair_map
  exact ovlUnimodularOfPairMap f g hw h3 h7
    Work.Cohomology.sph3Disc_relCapPair_unimodular

/-- **Lefschetz duality for the disc-bundle pair `(Vk(-2), Mk(-2))`, in the
*capped-world-compatible* universe.**

`Vk (-2)` is the total space of Milnor's rank-`4` disc bundle `ξ` over `S⁴` and
`Mk (-2) = S(ξ)` its unit sphere bundle (`∂Vk (-2)`), so `(Vk(-2), Mk(-2))` is a compact oriented
`8`-manifold with boundary.  By Lefschetz duality the cap product with a suitable relative
fundamental class is an isomorphism

`H⁴(Vk(-2), Mk(-2); ℤ) ⟶ H₄(Vk(-2); ℤ)`,

i.e. there is `c ∈ H₈(Vk(-2), Mk(-2); ℤ)` with `u ↦ u ⌢ c` *surjective* (both groups are `ℤ`, so
this is an isomorphism).

This is a verbatim copy of the already-proved `Work.Cohomology.Crux.vk_relCapPair_unimodular`
(`Submission/Work/Cohomology/Crux/vk_relCapPair_unimodular.lean`, 0 sorries), the difference being
only the *import closure*: that file reaches `Submission.Work.Cohomology.dualZ` and
`Submission.Work.Cohomology.prodSphereAux` (through its overlap-sharp input
`Work.Cohomology.Crux.ovlUnimodular` → `Work.Cohomology.sph3Disc_relCapPair_unimodular` →
`sph3Disc_relCapPair_kronH_mixed`/`sphere3DiscPairHomology`), which clash with
`localCohomology` and hence cannot be combined with the capped manifold
`Work.Milnor.cappedSpace`.

**Roadmap.** `vk_relCapPair_unimodular` is proved from three inputs: the transgression identity
`Work.Cohomology.Crux.vkInternalTransgression` (import closure has **0 taints**), the surjectivity
of the overlap restriction `Work.Cohomology.Crux.ovlRestrSurjectiveFinal` (**0 taints**), and the
*sharp* unimodularity of the overlap pairing (`Work.Cohomology.Crux.ovlUnimodular`, tainted).  The
last must be re-derived taint-free here, by redoing the short proofs of
`Work.Cohomology.Crux.ovlUnimodular` *and* of its model input
`Work.Cohomology.sph3Disc_relCapPair_unimodular` with the two tainted inputs of that model theorem
(`sph3Disc_relCapPair_kronH_mixed` and `sphere3DiscPairHomology`) replaced by the *clean
transplants* that already exist in the workspace, `Submission/Work/Cohomology/CompatTrans/` and
`Submission/Work/Cohomology/Compat/` (taint-free copies of `sph3Disc_relCapPair_kronH_mixed`,
`sphere3DiscPairHomology`, `homology_prod_sphere`, `prodSphereStep1/2`, `proj_pair_injective`, ...).
Note that `Submission/Work/Cohomology/Endgame/cruxClean.lean` already redoes the *nonvanishing*
version of the overlap transport taint-free and is a good template.

**Compatibility constraint**: this module and its whole import closure must NOT contain
`Submission.Work.Cohomology.dualZ` or `Submission.Work.Cohomology.prodSphereAux`. -/
theorem vkUnimodularClean :
    ∃ c : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8,
      Function.Surjective (fun u : Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX
        Work.Cohomology.vkPairA 4 =>
        Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 u c) := by
  -- the unimodularity of the overlap pairing (clean universe)
  obtain ⟨w, hw⟩ := ovlUnimodularClean
  -- the Mayer--Vietoris transgression identity for the two-chart cover
  obtain ⟨T₀, U₀, hT, hU, hid⟩ := vkInternalTransgression
  -- the restriction to the overlap is surjective
  have hρ : Function.Surjective ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (relComplexMap ℤ vkOvlA vkPairA (subtypeIncl vkPairX (vkU ∩ vkV))
        (fun x hx => hx)) 4))) := ovlRestrSurjectiveFinal
  obtain ⟨c₀, hc₀⟩ := hT w
  have hc₀' : T₀ c₀ = w := hc₀
  refine ⟨c₀, ?_⟩
  intro y
  obtain ⟨d, hd⟩ := hw (U₀ y)
  have hd' : ((relCapPair vkOvl vkOvlA 4 3) d) w = U₀ y := hd
  obtain ⟨a, ha⟩ := hρ d
  rcases hid a c₀ with h | h
  · refine ⟨a, hU ?_⟩
    rw [h, ha, hc₀', hd']
  · refine ⟨-a, hU ?_⟩
    show U₀ (((relCapPair vkPairX vkPairA 4 4) (-a)) c₀) = U₀ y
    have hneg : ((relCapPair vkPairX vkPairA 4 4) (-a)) c₀
        = - (((relCapPair vkPairX vkPairA 4 4) a) c₀) := by
      rw [map_neg]; rfl
    rw [hneg, map_neg, h, ha, hc₀', hd']
    simp

end

end Work.Endgame
