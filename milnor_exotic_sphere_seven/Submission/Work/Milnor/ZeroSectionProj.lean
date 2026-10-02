import Mathlib
import Submission.Work.Milnor.exists_zeroSection
import Submission.Work.Milnor.exists_proj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The zero section is a section of the projection

`Work.Milnor.exists_zeroSection` supplies the zero section `s : S⁴ ⟶ Vk k` of the open disc bundle
`ξ` over `S⁴` (`zeroSection`), pinned chartwise by `s ↑x = ιX (x, 0)` and `s ∞ = ιY (0, 0)`, and
`Work.Milnor.exists_proj` the bundle projection `vBaseMap : Vk k ⟶ S⁴`, pinned by
`vBaseMap (ιX q) = ↑q.1` and `vBaseMap (ιY q) = baseChart2 q.1`.

This file records the identity

  `vBaseMap k (zeroSection k x) = x`   (`vBaseMap_zeroSection`)

which identifies `s` as a *section* of `vBaseMap`, and therefore makes the induced map

  `s_* : H_*(S⁴;ℤ) ⟶ H_*(Vk k;ℤ)`

injective (since `vBaseMap_* ∘ s_* = id`).  In particular the zero section's fundamental class
`[S⁴] ∈ H_4(Vk k;ℤ) ≅ ℤ` is nonzero: the class against which the Thom class of `ξ` is evaluated
(the Euler number), and the class that appears in the self-intersection = Euler class theorem.
-/

set_option backward.isDefEq.respectTransparency false

open Topology

namespace Work.Milnor

noncomputable section

/-- **The zero section is a section of the bundle projection.** -/
theorem vBaseMap_zeroSection (k : ℤ) (x : Submission.Milnor.S4) :
    vBaseMap k (zeroSection k x) = x := by
  induction x using OnePoint.rec with
  | infty =>
      rw [zeroSection_apply_infty, vBaseMap_ιY]
      exact Submission.Milnor.baseChart2_zero
  | coe y => rw [zeroSection_apply_coe, vBaseMap_ιX]

/-- The bundle projection is surjective. -/
theorem vBaseMap_surjective (k : ℤ) : Function.Surjective (vBaseMap k) :=
  fun x => ⟨zeroSection k x, vBaseMap_zeroSection k x⟩

end

end Work.Milnor
