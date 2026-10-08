import Mathlib
import Submission.Work.Coprime.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.Coprime

/-- **Fixed points of a `p`-group acting on a `p`-group are nontrivial.**

Let `A` and `G` be finite `p`-groups with `G` nontrivial, and suppose `A` acts on `G` by group
automorphisms (`MulDistribMulAction`).  Then `C_G(A) = FT.fixedPoints A G` is nontrivial.

Indeed, the number of fixed points of a `p`-group action is congruent to the cardinality of the
acted-on set mod `p` (`IsPGroup.card_modEq_card_fixedPoints`), while `p ∣ |G|` because `G` is a
nontrivial finite `p`-group.  So `p ∣ |C_G(A)|`; since `1` is always fixed, the fixed-point
subgroup contains a non-identity element. -/
theorem fixedPoints_ne_bot_of_isPGroup (A : Type*) {G : Type*} [Group A] [Group G] [Finite A]
    [Finite G] [MulDistribMulAction A G] (p : ℕ) (hp : p.Prime) (hA : IsPGroup p A)
    (hG : IsPGroup p G) (hnt : Nontrivial G) : FT.fixedPoints A G ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p` divides `|G|` because `G` is a nontrivial finite `p`-group.
  have hpG : p ∣ Nat.card G := by
    obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp hnt
    rw [hn]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn0)
  -- The identity is always a fixed point.
  have h1fix : (1 : G) ∈ MulAction.fixedPoints A G := by
    rw [MulAction.mem_fixedPoints]
    intro a
    rw [smul_one]
  -- Hence the fixed-point set has a second element.
  obtain ⟨b, hbfix, hne⟩ :=
    hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point G hpG h1fix
  -- That second element is a non-identity element of `FT.fixedPoints A G`.
  intro hbot
  have hmem : b ∈ FT.fixedPoints A G := FT.mem_fixedPoints.mpr (MulAction.mem_fixedPoints.mp hbfix)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne hmem.symm

end Work.Coprime
