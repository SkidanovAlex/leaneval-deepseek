import Mathlib
import Submission.Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines
import Submission.Work.Kunneth.kunnethCP
import Submission.Work.LerayHirsch.exists_tautSection
import Submission.Work.Whitney.SectionStability

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Work.TangentClasses Work.Thom

/-- **The Chern-root relation, top-class form** (`Work.Gen.chernRoot_twistTop`): for a complex bundle
`Z` of rank `n ≥ 2`, the top Chern class of the twist `ℓ^* ⊗ π^*Z = Hom(ℓ, π^*Z)` over `P(Z)`
vanishes.  The inclusion `ℓ ↪ π^*Z` is a nowhere-zero section of that twist
(`Work.LerayHirsch.exists_tautSection`), so
`c_n(twist) = c_n(σ^*(tautQuotient twist))` with `rank = n-1`
(`Work.Whitney.chernClass_eq_of_nowhereZeroSection`), and a bundle of rank `n-1` has vanishing
degree-`n` Chern class (`Work.Thom.chernClass_succ_of_gt`). -/
theorem chernRoot_twistTop {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] {n : ℕ} (hn : 2 ≤ n)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι) :
    Work.Thom.chernClass n n
      (Work.LerayHirsch.twistCore (Work.Gen.dualLineCore (Work.LerayHirsch.tautLine Z))
        (Work.Thom.bundleComap Z (Work.LerayHirsch.projMap Z))) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨σ, hσ1, _⟩ := Work.LerayHirsch.exists_tautSection (m := k' + 1) Z
  rw [Work.Whitney.chernClass_eq_of_nowhereZeroSection (Work.LerayHirsch.tautTwist Z) σ hσ1
    (k' + 1 + 1)]
  exact Work.Thom.chernClass_succ_of_gt _ (by omega)

end Work.Gen
