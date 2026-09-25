import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt

/-!
# The Golod--Shafarevich criterion in the `ClassFieldTower` vocabulary

`Work.ClassFieldTower.infinite_of_hasMinimalPresentation`: a group that has a
*minimal* presentation by `d` generators and `r` relators with `4 * r ≤ d * d`,
and all of whose finite quotients are `p`-groups (here encoded by the hypothesis
`Finite G → IsPGroup p G`), must be **infinite**.

This is the classical Golod--Shafarevich criterion, and it is the group-theoretic
seam of the chapter `Submission/Work/ClassFieldTower/`: it will be applied to
`G_∅ = Gal(F_∅/F)`, the Galois group of the maximal unramified pro-`2` extension of
an imaginary quadratic field `F`, whose presentation data are supplied by the
arithmetic certificate `GolodShafarevichCertificate` of `Defs.lean`.

The proof is the contrapositive of the finite `p`-group Golod--Shafarevich
inequality `Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt`:

* if `G` were finite then `G` itself would be a finite `p`-group (hypothesis
  `hpro`), and the presentation of `G` by `d` minimal generators and `r` relators
  would force `d * d < 4 * r`, contradicting `hineq : 4 * r ≤ d * d`;
* `G` is nontrivial: otherwise the empty finset generates it, so minimality
  forces `d ≤ 0`, contradicting `hpos : 0 < d`.
-/

set_option linter.style.haveILetI false

open scoped Classical

namespace Work.ClassFieldTower

/-- **The Golod--Shafarevich criterion.** A group with a minimal presentation by
`d` generators and `r` relators satisfying the Golod--Shafarevich inequality
`4 * r ≤ d * d`, all of whose finite quotients are `p`-groups, is infinite. -/
theorem infinite_of_hasMinimalPresentation {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (hpro : Finite G → IsPGroup p G) {d r : ℕ} (hpos : 0 < d)
    (hpres : HasMinimalPresentation G d r) (hineq : 4 * r ≤ d * d) : Infinite G := by
  classical
  obtain ⟨α, hαfin, hαdec, rel, hcard, hrelcard, hiso, hmin⟩ := hpres
  by_contra hinf
  haveI : Finite G := not_infinite_iff_finite.mp hinf
  haveI : Fintype G := Fintype.ofFinite G
  -- `G` is nontrivial, since otherwise the empty set would generate it and
  -- minimality of the generating set would force `d = 0`.
  have hnt : Nontrivial G := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hss
    haveI := hss
    have hcl : Subgroup.closure ((∅ : Finset G) : Set G) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      rw [Subsingleton.elim x 1]
      exact Subgroup.one_mem _
    have h := hmin ∅ hcl
    rw [Finset.card_empty] at h
    exact absurd h (not_le.mpr hpos)
  haveI : Nontrivial G := hnt
  -- The finite `p`-group Golod--Shafarevich inequality applied to `G` itself.
  have hkey : Fintype.card α * Fintype.card α < 4 * rel.card :=
    Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt
      p (hpro inferInstance) rel hiso (fun S hS => by rw [hcard]; exact hmin S hS)
  -- ... contradicts the Golod--Shafarevich inequality `4 * r ≤ d * d`.
  have hno : ¬ (Fintype.card α * Fintype.card α < 4 * rel.card) := by
    rw [hcard, hrelcard]
    exact not_lt.mpr hineq
  exact hno hkey

end Work.ClassFieldTower
