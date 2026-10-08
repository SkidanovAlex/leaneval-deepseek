import Mathlib
import Submission.Work.L2F.Dihedral.centralizer_sr_subset
import Submission.Work.L2F.Dihedral.zmod_half_of_add_self
import Submission.Work.Dihedral.Defs

/-!
# A dihedral-group centralizer fact

Let `D = DihedralGroup n` with `n` even, `H ≤ D` a subgroup of order at least `8`, and `t ∈ H` an
involution centralizing `H`.  Then `t` is central in `D`:

* if `t = r i` is a rotation, then `i + i = 0`; as `t ≠ 1` this forces `i = n/2`, and `r (n/2)`
  generates `Z(D)` (`DihedralGroup.center_eq_closure_of_even_ne_two`);
* if `t = sr i` is a reflection, then `H ≤ C_D(sr i)`, which is contained in the four-element set
  `{1, r (n/2), sr i, sr (i + n/2)}` (`Work.L2F.Dihedral.centralizer_sr_subset`), so `|H| ≤ 4`,
  contradiction.

This is the group-theoretic core of the case `8 ≤ |S ⊓ M|` of Bender's Lemma 2.7, step 3.
-/

namespace Work.CORE2B

open DihedralGroup

set_option linter.style.haveILetI false

/-- **In a dihedral group with even parameter, an involution central in a subgroup of order at
least `8` is central in the whole group.** -/
theorem dihedral_center_of_large_subgroup {n : ℕ} (hn : Even n) (H : Subgroup (DihedralGroup n))
    (t : DihedralGroup n) (htH : t ∈ H) (ht : orderOf t = 2) (hH : 8 ≤ Nat.card H)
    (hZ : ∀ x ∈ H, x * t = t * x) : ∀ x : DihedralGroup n, x * t = t * x := by
  rcases Work.Dihedral.eq_r_or_sr t with ⟨i, hi⟩ | ⟨i, hi⟩
  · -- rotation case
    have hsq : r i * r i = 1 := by
      rw [← pow_two, ← hi, ← ht]
      exact pow_orderOf_eq_one _
    have hii : i + i = 0 := by
      have h1 : r (i + i) = r (0 : ZMod n) := by
        rw [← DihedralGroup.r_mul_r, hsq, DihedralGroup.r_zero]
      exact DihedralGroup.r.inj h1
    have hi0 : i ≠ 0 := by
      intro h0
      have h2 : orderOf (1 : DihedralGroup n) = 2 := by
        rw [← DihedralGroup.r_zero, ← h0, ← hi]
        exact ht
      rw [orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have hhalf : i = ((n / 2 : ℕ) : ZMod n) :=
      Work.L2F.Dihedral.zmod_half_of_add_self i hii hi0
    have hn2 : n ≠ 2 := by
      intro h
      subst h
      have hle := Subgroup.card_le_card_group H
      rw [DihedralGroup.nat_card] at hle
      omega
    have hcent : r ((n / 2 : ℕ) : ZMod n) ∈ Subgroup.center (DihedralGroup n) := by
      rw [DihedralGroup.center_eq_closure_of_even_ne_two hn hn2]
      exact Subgroup.mem_zpowers _
    intro x
    rw [hi, hhalf]
    exact Subgroup.mem_center_iff.mp hcent x
  · -- reflection case: `H` lies in a four-element set
    subst hi
    have hsub : (H : Set (DihedralGroup n)) ⊆
        ({1, DihedralGroup.r ((n / 2 : ℕ) : ZMod n), DihedralGroup.sr i,
          DihedralGroup.sr (i + ((n / 2 : ℕ) : ZMod n))} : Set (DihedralGroup n)) := by
      intro x hx
      refine Work.L2F.Dihedral.centralizer_sr_subset ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hZ x hx).symm
    have hcard : Nat.card ↥H ≤ 4 := by
      have hb : ({1, DihedralGroup.r ((n / 2 : ℕ) : ZMod n), DihedralGroup.sr i,
          DihedralGroup.sr (i + ((n / 2 : ℕ) : ZMod n))} : Set (DihedralGroup n)).ncard ≤ 4 := by
        calc ({1, DihedralGroup.r ((n / 2 : ℕ) : ZMod n), DihedralGroup.sr i,
              DihedralGroup.sr (i + ((n / 2 : ℕ) : ZMod n))} : Set (DihedralGroup n)).ncard
            ≤ ({DihedralGroup.r ((n / 2 : ℕ) : ZMod n), DihedralGroup.sr i,
                DihedralGroup.sr (i + ((n / 2 : ℕ) : ZMod n))} :
                Set (DihedralGroup n)).ncard + 1 := Set.ncard_insert_le _ _
          _ ≤ (({DihedralGroup.sr i, DihedralGroup.sr (i + ((n / 2 : ℕ) : ZMod n))} :
                Set (DihedralGroup n)).ncard + 1) + 1 := by
              linarith [Set.ncard_insert_le (DihedralGroup.r ((n / 2 : ℕ) : ZMod n))
                ({DihedralGroup.sr i, DihedralGroup.sr (i + ((n / 2 : ℕ) : ZMod n))} :
                  Set (DihedralGroup n))]
          _ ≤ ((({DihedralGroup.sr (i + ((n / 2 : ℕ) : ZMod n))} :
                Set (DihedralGroup n)).ncard + 1) + 1) + 1 := by
              linarith [Set.ncard_insert_le (DihedralGroup.sr i)
                ({DihedralGroup.sr (i + ((n / 2 : ℕ) : ZMod n))} : Set (DihedralGroup n))]
          _ ≤ 4 := by
              rw [Set.ncard_singleton]
      calc Nat.card ↥H ≤ (H : Set (DihedralGroup n)).ncard :=
            (Nat.card_coe_set_eq (H : Set (DihedralGroup n))).le
        _ ≤ ({1, DihedralGroup.r ((n / 2 : ℕ) : ZMod n), DihedralGroup.sr i,
              DihedralGroup.sr (i + ((n / 2 : ℕ) : ZMod n))} :
              Set (DihedralGroup n)).ncard := Set.ncard_le_ncard hsub (by simp)
        _ ≤ 4 := hb
    omega

end Work.CORE2B
