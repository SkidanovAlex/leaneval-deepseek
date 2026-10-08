import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.PGroup

/-- **Fixed points of a `p`-group acting by conjugation on a `p`-subgroup.**

Let `P` and `Q` be finite `p`-subgroups of a group `G` with `P ≤ N_G(Q)` and `Q ≠ ⊥`.
Then `P` acts on `Q` by conjugation, and a standard fixed-point argument for `p`-group actions
(the number of fixed points is congruent to `|Q|` mod `p`, and `|Q|` is divisible by `p`)
produces a non-identity fixed point.  This is exactly the assertion that
`Q ∩ C_G(P)` is nontrivial.

This is the "centralizer of a `p`-subgroup is nontrivial" statement needed throughout the
odd order theorem (compare FT §3, Gorenstein §5.3). -/
theorem inf_centralizer_ne_bot_of_isPGroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (P Q : Subgroup G) [Finite P] [Finite Q] (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hQne : Q ≠ ⊥) (hN : P ≤ Subgroup.normalizer (Q : Set G)) :
    Q ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `P` acts on `Q` by conjugation, through the conjugation action of `N_G(Q)` on `Q`.
  letI : MulAction P Q := MulAction.compHom Q (Subgroup.inclusion hN)
  -- The action is conjugation, computed on the underlying elements of `G`.
  have hsmul_val : ∀ (g : P) (q : Q), ((g • q : Q) : G) = (g : G) * (q : G) * (g : G)⁻¹ :=
    fun g q => rfl
  -- `p` divides `|Q|` because `Q` is a nontrivial finite `p`-group.
  have hpQ : p ∣ Nat.card Q := by
    rcases hQ.card_eq_or_dvd with h1 | hd
    · exact absurd ((Subgroup.card_le_one_iff_eq_bot Q).mp (le_of_eq h1)) hQne
    · exact hd
  -- The identity is always a fixed point of a conjugation action.
  have h1fix : (1 : Q) ∈ MulAction.fixedPoints P Q := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    rw [hsmul_val]
    simp
  -- Hence there is a second fixed point.
  obtain ⟨b, hbfix, hne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point Q hpQ h1fix
  -- A fixed point of the conjugation action lies in the centralizer of `P`.
  have hbcent : (b : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hfix := (MulAction.mem_fixedPoints.mp hbfix) (⟨g, hg⟩ : P)
    have hv : (g : G) * (b : G) * (g : G)⁻¹ = (b : G) := by
      have h2 := congrArg Subtype.val hfix
      rwa [hsmul_val] at h2
    exact mul_inv_eq_iff_eq_mul.mp hv
  -- `b ≠ 1`, so `Q ⊓ C_G(P)` contains a non-identity element.
  intro hbot
  have hmem : (b : G) ∈ Q ⊓ Subgroup.centralizer (P : Set G) := ⟨b.2, hbcent⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne (Subtype.ext hmem.symm)

end Work.PGroup
