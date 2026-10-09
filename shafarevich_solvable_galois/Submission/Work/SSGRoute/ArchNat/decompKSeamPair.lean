import Mathlib
import Submission.Work.SSGRoute.PT.decompK_linked
import Submission.Work.SSGRoute.ArchDictionary.ArchLocalP2Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `D_w = {1, res c}` at the seam place

For the archimedean `p = 2` dictionary the decomposition group of the place linked to the involution
`c` is `⟨res c⟩ ≅ ℤ/2`, i.e. **every** `g ∈ D_w` is `1` or `res c`.  This is the fact that turns
"the two cocycles agree at `d = res c`" into "they agree on `D_w`" (step 6 of the lead's route for
`archPhiSeam_square`, `ARCHP2_PLAN.md` §3), and it is what makes the evaluation at a single element
sufficient.

`Work.SSGRoute.PT.decompK_linked` computes the group as `(zpowers c).map (res k K)`; the rest is
`Subgroup.mem_map` plus `mem_zpowers_eq_one_or_eq` (`ArchDictionary/ArchLocalP2Aux.lean`).

(The conclusion is stated for `(g : ↥K ≃ₐ[k] ↥K)`, as in the consumers: the elements of `decompK` are
coerced from `K ≃ₐ[k] K`.)
-/

namespace Work.SSGRoute.ArchNat

open CategoryTheory SSGRoute.PTExt

/-- **The decomposition group of the seam place is `{1, res c}`.** -/
theorem mem_decompK_seamPlace_pair {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) :
    ∀ g : ↥(SSGRoute.PTExt.decompK (k := k)
        (Work.SSGRoute.ArchDictionary.seamPlace (K := K) φ)),
      g = 1 ∨ ((g : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K c) := by
  intro g
  have hDw : SSGRoute.PTExt.decompK (k := k) (Work.SSGRoute.ArchDictionary.seamPlace (K := K) φ)
      = (Subgroup.zpowers c).map (SSGRoute.res k K) :=
    Work.SSGRoute.PT.decompK_linked k Ω K c hc2 hc1 φ hlink
  have hg : (g : ↥K ≃ₐ[k] ↥K) ∈ (Subgroup.zpowers c).map (SSGRoute.res k K) := by
    rw [← hDw]; exact g.2
  obtain ⟨m, hm, hm'⟩ := Subgroup.mem_map.mp hg
  rcases Work.SSGRoute.ArchDictionary.mem_zpowers_eq_one_or_eq c hc2 hm with h | h
  · left
    refine Subtype.ext ?_
    rw [← hm', h, map_one, OneMemClass.coe_one]
  · right
    rw [← hm', h]

end Work.SSGRoute.ArchNat
