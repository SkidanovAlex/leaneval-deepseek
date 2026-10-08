import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.fixedPoints_ne_bot_of_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.LocalPrelim

/-- **An invariant subgroup of order `p`.**

Let the finite `p`-group `Q` act by group automorphisms on the nontrivial finite `p`-group `V`.
Then `V` contains a `Q`-invariant subgroup of order `p`.

Indeed `C_V(Q) = FT.fixedPoints Q V` is nontrivial (fixed points of a `p`-group action on a
`p`-group), hence a nontrivial finite `p`-group, hence contains a subgroup of order `p` by a
special case of Sylow's first theorem.  Any subgroup of `C_V(Q)` is `Q`-invariant, since `Q`
fixes each of its elements. -/
theorem exists_isInvariant_card_eq_prime {Q V : Type*} [Group Q] [Group V] [Finite Q] [Finite V]
    [MulDistribMulAction Q V] {p : ℕ} (hp : p.Prime) (hQ : IsPGroup p Q) (hV : IsPGroup p V)
    (hnt : Nontrivial V) :
    ∃ W : Subgroup V, FT.IsInvariant Q W ∧ Nat.card W = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- The fixed-point subgroup `C_V(Q)` is nontrivial.
  set C : Subgroup V := FT.fixedPoints Q V with hCdef
  have hCne : C ≠ ⊥ := Work.Coprime.fixedPoints_ne_bot_of_isPGroup Q p hp hQ hV hnt
  -- Being a subgroup of a `p`-group, it is a `p`-group.
  have hCpg : IsPGroup p C := hV.to_subgroup C
  have hntC : Nontrivial C := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hCne
  -- A nontrivial finite `p`-group of order `p ^ n` with `n > 0` has order at least `p`.
  obtain ⟨n, hnpos, hn⟩ := (hCpg.nontrivial_iff_card).mp hntC
  have hpC : p ≤ Nat.card C := by
    rw [hn]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hnpos
  -- Sylow's first theorem provides a subgroup of `C` of order `p`.
  obtain ⟨W, hWle, hWcard⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card hp hV (n := 1) (H := C) (by simpa using hpC)
  refine ⟨W, ?_, by simpa using hWcard⟩
  -- `W ≤ C_V(Q)`, so `Q` fixes every element of `W`; in particular `W` is `Q`-invariant.
  refine ⟨fun a => le_antisymm (fun y hy => ?_) (fun y hy => ?_)⟩
  · obtain ⟨x, hx, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists y a W).mp hy
    rw [FT.mem_fixedPoints.mp (hWle hx) a]
    exact hx
  · rw [Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨y, hy, FT.mem_fixedPoints.mp (hWle hy) a⟩

end Work.LocalPrelim
