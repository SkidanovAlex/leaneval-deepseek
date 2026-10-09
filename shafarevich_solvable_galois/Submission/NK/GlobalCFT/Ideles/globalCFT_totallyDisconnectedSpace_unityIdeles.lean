import Mathlib
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.Ideles.globalCFT_unityIdeles_isCompact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unitary idèles of a number field are totally disconnected

For a number field `K`, the group of **unitary idèles** `unityIdeles K` is the product
`∏_{v finite} 𝒪_vˣ` of the local unit groups at the nonarchimedean places, with the archimedean
coordinates pinned to `1`.  It sits inside the idèle group `𝕀 K` as the subgroup

`{x | x v = 1 for v infinite, x v ∈ 𝒪_vˣ for v finite}`.

Here we show that this topological group is totally disconnected — equivalently (and this is how
it is proved) totally separated.  The reason is local: at a *finite* place `q` the local field
`K_q` carries the `q`-adic norm, which is **ultrametric**, so balls in `K_q` are clopen; distinct
points `a ≠ b` of `K_q` are separated by the clopen ball `Metric.ball a (dist a b)`.

The argument therefore never needs any analysis of the restricted product topology beyond the
continuity of the coordinate projections `𝕀 K → K_vˣ` (a general fact about restricted
products, `RestrictedProduct.continuous_eval`): given two distinct unitary idèles `x ≠ y`, some
coordinate differs, and that coordinate must be a *finite* place (the archimedean coordinates of
a unitary idèle are all `1`).  Pulling back a clopen ball along the continuous projection at that
finite place separates `x` from `y` by clopen sets.

## Main results

* `NK.GlobalCFT.Ideles.globalCFT_totallySeparatedSpace_unityIdeles`: the unitary idèles are
  totally separated.
* `NK.GlobalCFT.Ideles.globalCFT_totallyDisconnectedSpace_unityIdeles`: the unitary idèles are
  totally disconnected.
-/

set_option autoImplicit false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Ideles

/-- **The unitary idèles of a number field are totally separated.**

Two distinct unitary idèles `x ≠ y` differ in some coordinate; the archimedean coordinates of a
unitary idèle are all `1`, so the coordinate where they differ lies at a finite place `q`.  The
local field `K_q` is ultrametric, so the ball `Metric.ball x_q (dist x_q y_q)` is clopen in `K_q`
and contains `x_q` but not `y_q`; pulling it back along the continuous projection
`𝕀 K → K_qˣ` (which is continuous by `RestrictedProduct.continuous_eval`) gives a clopen subset
of the unitary idèles containing `x` and not `y`. -/
theorem globalCFT_totallySeparatedSpace_unityIdeles (K : Type*) [Field K] [NumberField K] :
    TotallySeparatedSpace ↥(Idele.unityIdeles K) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  -- Two distinct idèles differ at some place.
  have hne : (x : Idele K) ≠ (y : Idele K) := fun h => hxy (Subtype.ext h)
  have hdiff : ∃ v : Place K, (x : Idele K) v ≠ (y : Idele K) v := by
    by_contra h
    push Not at h
    exact hne (Idele.ext h)
  obtain ⟨v, hv⟩ := hdiff
  -- That place cannot be archimedean: a unitary idèle is `1` there.
  have hfin : Place.IsFinite v := by
    rintro hinf
    exact hv (by rw [(Idele.mem_unityIdeles.mp x.2).1 v hinf,
      (Idele.mem_unityIdeles.mp y.2).1 v hinf])
  obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hfin
  -- The two local components at the finite place `q`.
  set A : Place.localField K (Place.ofFinite q) :=
    ((x : Idele K) (Place.ofFinite q) : Place.localField K (Place.ofFinite q)) with hA
  set B : Place.localField K (Place.ofFinite q) :=
    ((y : Idele K) (Place.ofFinite q) : Place.localField K (Place.ofFinite q)) with hB
  have hAB : A ≠ B := by
    rw [hA, hB]
    exact fun h => hv (Units.ext h)
  -- The projection to the local field at `q` is continuous.
  have hcont : Continuous fun z : ↥(Idele.unityIdeles K) =>
      ((z : Idele K) (Place.ofFinite q) : Place.localField K (Place.ofFinite q)) :=
    Units.continuous_val.comp ((RestrictedProduct.continuous_eval (Place.ofFinite q)).comp
      continuous_subtype_val)
  -- Balls in the ultrametric local field `K_q` are clopen.
  have hcl : IsClopen (Metric.ball A (dist A B)) :=
    IsUltrametricDist.isClopen_ball A _
  refine ⟨(fun z : ↥(Idele.unityIdeles K) =>
      ((z : Idele K) (Place.ofFinite q) : Place.localField K (Place.ofFinite q))) ⁻¹'
      Metric.ball A (dist A B), hcl.preimage hcont, ?_, ?_⟩
  · rw [Set.mem_preimage, ← hA]
    exact Metric.mem_ball_self (dist_pos.mpr hAB)
  · rw [Set.mem_compl_iff, Set.mem_preimage, ← hB]
    simp [Metric.mem_ball, dist_comm]

/-- **The group of unitary idèles of a number field is totally disconnected.**

This is immediate from `globalCFT_totallySeparatedSpace_unityIdeles`, since a totally separated
space is totally disconnected. -/
theorem globalCFT_totallyDisconnectedSpace_unityIdeles (K : Type*) [Field K] [NumberField K] :
    TotallyDisconnectedSpace ↥(Idele.unityIdeles K) :=
  @TotallySeparatedSpace.totallyDisconnectedSpace ↥(Idele.unityIdeles K) _
    (globalCFT_totallySeparatedSpace_unityIdeles K)

end NK.GlobalCFT.Ideles
