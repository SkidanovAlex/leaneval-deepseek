import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.extCor_two_injective_pTorsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Z8

open SSGRoute.PTExt

/-! # Corestriction is injective on `p`-torsion, in terms of `Nat.gcd p _`

`Work.SSGRoute.extCor_two_injective_pTorsion` (`X6` in the E7b design) proves that corestriction
`cor : H²(S, B) → H²(G, B)` is injective on the `p`-torsion *when both `p`-torsion groups have
exactly `p` elements*.

Here we draw the trivial consequences of the case analysis on `p ∣ |S|`:

* `p ∤ |S|`: then `Nat.gcd p |S| = 1`, so the hypothesis `hcardS` says that the `p`-torsion of
  `H²(S, B)` is a singleton; in particular the `p`-torsion element `t` is zero, and nothing about
  corestriction is needed.
* `p ∣ |S|`: since `|S| ∣ |G|`, also `p ∣ |G|`, hence both `Nat.gcd p |S| = p` and
  `Nat.gcd p |G| = p`; now `X6` applies verbatim.

So the statement is a genuine strengthening of `X6` which removes the case distinction from its
consumers. -/

theorem extCor_injective_pTorsion_gcd (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (S : Subgroup G) [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]
    (hSidx : ¬ p ∣ S.index)
    (B : Rep SSGRoute.PTExt.Coeff G)
    (hcardS : Nat.card {x : SSGRoute.PTExt.extH (Rep.res S.subtype B) 2 // p • x = 0}
      = Nat.gcd p (Nat.card S))
    (hcardG : Nat.card {x : SSGRoute.PTExt.extH B 2 // p • x = 0} = Nat.gcd p (Nat.card G))
    (t : SSGRoute.PTExt.extH (Rep.res S.subtype B) 2) (ht : p • t = 0)
    (h0 : Work.SSGRoute.extCor S (SSGRoute.PTExt.unitRep G) B 2 t = 0) : t = 0 := by
  classical
  by_cases hpS : p ∣ Nat.card S
  · -- `p ∣ |S| ≤ |G|`: both `p`-torsions have `p` elements and `X6` applies.
    have hSg : Nat.gcd p (Nat.card S) = p := Nat.gcd_eq_left hpS
    have hpG : p ∣ Nat.card G := dvd_trans hpS (Subgroup.card_subgroup_dvd_card S)
    have hGg : Nat.gcd p (Nat.card G) = p := Nat.gcd_eq_left hpG
    exact Work.SSGRoute.extCor_two_injective_pTorsion p S hSidx B (hcardG.trans hGg)
      (hcardS.trans hSg) t ht h0
  · -- `p ∤ |S|`: the `p`-torsion of `H²(S, B)` is trivial.
    have hcop : Nat.Coprime p (Nat.card S) :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hpS
    have hSg : Nat.gcd p (Nat.card S) = 1 := hcop.gcd_eq_one
    have hsub : Subsingleton {x : SSGRoute.PTExt.extH (Rep.res S.subtype B) 2 // p • x = 0} :=
      (Nat.card_eq_one_iff_unique.mp (hcardS.trans hSg)).1
    have h : (⟨t, ht⟩ : {x : SSGRoute.PTExt.extH (Rep.res S.subtype B) 2 // p • x = 0})
        = ⟨0, by simp⟩ := Subsingleton.elim _ _
    simpa using congrArg Subtype.val h

end Work.SSGRoute.Z8
