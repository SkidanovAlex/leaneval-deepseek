import Mathlib
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.Crux.vk_transgression_cap_weak
import Submission.Work.Cohomology.Compat.sph3DiscRelCapPairNeZero

namespace Work.Cohomology.Crux

-- LEMMA: the relative cap product of the disc-bundle pair (Vk(-2), Mk(-2)) in degree (4,4) is
-- non-vanishing: there are a nonzero relative class `u` and a relative class `c` with `u ⌢ c ≠ 0`.
--
-- THIS IS POINCARÉ–LEFSCHEtz DUALITY FOR THE RANK-4 DISC BUNDLE OVER S⁴ IN DEGREE 4.
-- Together with the already-proved, importable bridge
-- `Work.Cohomology.vk_relCup_ne_zero_of_relCapPair_ne_zero : (∃ c, u ⌢ c ≠ 0) → u ⌣ u ≠ 0`
-- it yields the missing "Thom class squares to a nonzero class" input of the whole project.
--
-- *** HARD COMPATIBILITY CONSTRAINT ***
-- This module and its WHOLE import closure must NOT contain
--   `Submission.Work.Cohomology.dualZ`  or  `Submission.Work.Cohomology.prodSphereAux`
-- (each of those two declares a name — `Work.Cohomology.dualZ`, `Work.Cohomology.chainMap_comp'` —
-- that is ALSO declared in `Submission.Work.Cohomology.localCohomology`, so importing them makes
-- the module unusable from the capped-manifold world, which is exactly what it is needed for).
-- If you need a result currently only available under those imports, reproduce it in a NEW file of
-- your own (a `namespace Work.Cohomology.Compat` copy is fine) rather than importing it.
--
-- MATHEMATICAL GUIDANCE.  Vk(-2) is the total space of the rank-4 real vector bundle ξ over S⁴
-- (two charts ℝ⁴×ℍ glued by the clutching (x,y) ↦ (x/‖x‖², û²yû⁻¹)); Mk(-2) = S(ξ) is the unit
-- sphere bundle, and H^n(Vk,Mk) = ℤ for n = 4,8 and 0 otherwise, H_n(Vk) = ℤ for n = 0,4.
-- Available in the compatible world: `Work.Cohomology.cohomologyPairVk` (the relative cohomology
-- groups), `Work.Milnor.homology_Vk`, `Work.Cohomology.RelCapHTransfer`/`RelCap` (the relative cap
-- product and its cycle-level computation rule), `Work.Cohomology.relCapH_kronH_cup`, the
-- Mayer–Vietoris sequences (`MVCohomology`, `MVSequence`, `HomologyPairSequence`,
-- `relMV_shortExact`, `RelMVLes`, `relMV_quasiIso`), `sphere3DiscPairDefs`, the sphere/disc
-- homology files (`sphereHomologyTop/Zero`, `diskPairHomologyTop/Zero`, `two_balls`) and the
-- Alexander–Whitney chain level (`AlexanderWhitney`).  A known workable route: take a cover of Vk
-- by the total spaces over two thickened hemispheres (pieces ≅ trivial bundle over a ball, where
-- the relevant relative groups vanish in the degrees needed), use the relative Mayer–Vietoris
-- sequence of the pair to see u = δ(γ) (transgression of a class γ on the overlap S³×D⁴) and
-- H⁸(Vk,Mk) ≅ H⁷(overlap) ≅ ℤ via the same connecting map, then compute the cup square of that
-- transgression; the answer ±e(ξ) = ±1 is forced (e(ξ) ≠ 0 is free: the zero section gives
-- s_*[S⁴] ≠ 0 and the Kronecker pairing is unimodular).  Equivalent formulations: the Poincaré dual
-- of the Thom class is the zero section (`u ⌢ [W,∂W] = ± s_*[S⁴]`), or u⌣u = ±e(ξ)·ω; either can
-- be proved instead if easier.  Both the statement as written and any of these equivalents are
-- acceptable, PROVIDED the compatibility constraint above is respected.
--
-- PROOF (this is how the lemma is proved here, and the only two inputs are the two compatible,
-- already-proved lemmas named below — the two halves of the Mayer–Vietoris transgression).
-- The two chart images `U = range (vData (-2)).ιX` and `V = range (vData (-2)).ιY` of `Vk (-2)`
-- are open and cover it; their overlap `W = U ∩ V` is homotopy equivalent to `S³ × D⁴` and
-- `W ∩ Mk` to `S³ × S³ = PairAT`, and the relevant (co)homology of the two pieces vanishes in the
-- degrees used.  Consequently
--   * `Work.Cohomology.Crux.vk_transgression_cap_weak` gives a surjective restriction
--     `r : H⁴(Vk,Mk) → H⁴(PairXT,PairAT)`, a surjection `T : H₈(Vk,Mk) → H₇(PairXT,PairAT)`
--     (both groups are ℤ) and an injection `U : H₄(Vk) → H₃(PairXT)`, together with the
--     **transgression identity** `U (u ⌢ c) = ± (r u) ⌢ (T c)` — the naturality of the snake-lemma
--     connecting map under the chain map "cap product with a relative 4-cocycle" (Hatcher's
--     Lemma 3.36).  This is the only place where the two-chart cover of `Vk(-2)` is used.
--   * `Work.Cohomology.Compat.sph3DiscRelCapPairNeZero` is the **overlap witness**: nonzero
--     `u₀ ∈ H⁴(PairXT,PairAT)`, `c₀ ∈ H₇(PairXT,PairAT)` with `u₀ ⌢ c₀ ≠ 0` (Lefschetz duality for
--     the trivial rank-4 disc bundle over S³).
-- Choosing `u` with `r u = u₀` and `c` with `T c = c₀` gives `U (u ⌢ c) = ± u₀ ⌢ c₀ ≠ 0`, hence
-- `u ⌢ c ≠ 0` because `U` is injective, and `u ≠ 0` because `r u = u₀ ≠ 0`.
theorem vk_relCapPair_nonzero :
    ∃ (u : Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4)
      (c : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8),
      u ≠ 0 ∧ (Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 u c) ≠ 0 := by
  -- the transgression identity for the two-chart cover of `Vk (-2)` (with the overlap modelled by
  -- `(S³ × D⁴, S³ × S³)`)
  obtain ⟨r, T, U, hr, hT, hU, hid⟩ := Work.Cohomology.Crux.vk_transgression_cap_weak
  -- the overlap witness
  obtain ⟨u₀, c₀, hu₀, hc₀⟩ := Work.Cohomology.Compat.sph3DiscRelCapPairNeZero
  -- a preimage of `u₀` under the (surjective) restriction `r` and of `c₀` under `T`
  obtain ⟨u, hu⟩ := hr u₀
  obtain ⟨c, hc⟩ := hT c₀
  refine ⟨u, c, ?_, ?_⟩
  · intro h0
    exact hu₀ (by rw [← hu, h0, map_zero])
  · intro hcap
    have h := hid u c
    rw [hcap, map_zero, hc, hu] at h
    rcases h with h | h
    · exact hc₀ h.symm
    · exact hc₀ (neg_eq_zero.mp h.symm)

end Work.Cohomology.Crux
