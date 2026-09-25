import Mathlib
import Submission.NK.LocalAnabelian.All

/-!
# The Frattini rank of a commutative group from the order of `C / C^p`

If `C` is a commutative group and `C ⧸ C ^ p` has order `p ^ r` (`p` prime), then `C` has
exactly `(p ^ r - 1) / (p - 1)` subgroups of index `p`, i.e. `HasFrattiniRank p r C`.

The two ingredients are

* every index-`p` subgroup of a commutative group contains the `p`-th powers (its quotient is a
  group of order `p`, which has exponent `p`), so index-`p` subgroups of `C` are in bijection
  with index-`p` subgroups of the elementary abelian `p`-group `C ⧸ C ^ p`;
* the counting of index-`p` subgroups of a finite abelian group of exponent `p`,
  `NK.LocalAnabelian.Counting.natCard_indexP_subgroups_of_exp_p`.
-/

namespace NK.LocalInputs.CommGroupRank

open scoped Classical

/-- Every index-`p` subgroup of a commutative group contains the range of `powMonoidHom p`,
i.e. the subgroup of `p`-th powers. -/
lemma powSubgroup_le_of_index_eq_prime {C : Type*} [CommGroup C] {p : ℕ}
    (K : Subgroup C) (hK : K.index = p) :
    (powMonoidHom p : C →* C).range ≤ K := by
  intro x hx
  rw [MonoidHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  have h := Subgroup.pow_index_mem K y
  rwa [hK] at h

/-- For a commutative group `C` and a prime `p`, index-`p` subgroups of `C` are in bijection
with index-`p` subgroups of `C ⧸ C ^ p`. -/
lemma natCard_indexP_eq_natCard_quot_powSubgroup {C : Type*} [CommGroup C] {p : ℕ} :
    Nat.card {K : Subgroup C // K.index = p} =
      Nat.card {K : Subgroup (C ⧸ (powMonoidHom p : C →* C).range) // K.index = p} := by
  classical
  let Φ : Subgroup C := (powMonoidHom p : C →* C).range
  have hΦle : ∀ K : Subgroup C, K.index = p → Φ ≤ K := fun K hK =>
    powSubgroup_le_of_index_eq_prime K hK
  let f : C →* C ⧸ Φ := QuotientGroup.mk' Φ
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective Φ
  have hker : f.ker = Φ := QuotientGroup.ker_mk' Φ
  refine Nat.card_congr
    { toFun := fun K =>
        ⟨K.1.map f,
          (Subgroup.index_map_eq (H := K.1) hf (hker.trans_le (hΦle K.1 K.2))).trans K.2⟩
      invFun := fun K =>
        ⟨K.1.comap f, (Subgroup.index_comap_of_surjective (H := K.1) hf).trans K.2⟩
      left_inv := fun K =>
        Subtype.ext (Subgroup.comap_map_eq_self (f := f) (H := K.1)
          (hker.trans_le (hΦle K.1 K.2)))
      right_inv := fun K =>
        Subtype.ext (Subgroup.map_comap_eq_self_of_surjective (f := f) hf K.1) }

theorem hasFrattiniRank_of_natCard_quot_powSubgroup {C : Type*} [CommGroup C] {p r : ℕ} (hp : p.Prime)
    (h : Nat.card (C ⧸ (powMonoidHom p : C →* C).range) = p ^ r) :
    NK.LocalAnabelian.HasFrattiniRank p r C := by
  classical
  rw [NK.LocalAnabelian.HasFrattiniRank, NK.LocalAnabelian.numIndexSubgroups,
    natCard_indexP_eq_natCard_quot_powSubgroup]
  have hfin : Finite (C ⧸ (powMonoidHom p : C →* C).range) :=
    Nat.finite_of_card_ne_zero (by rw [h]; exact pow_ne_zero _ hp.ne_zero)
  have hexp : ∀ a : C ⧸ (powMonoidHom p : C →* C).range, a ^ p = 1 := by
    intro a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (powMonoidHom p : C →* C).range a
    show (QuotientGroup.mk' (powMonoidHom p : C →* C).range) x ^ p = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  rw [NK.LocalAnabelian.Counting.natCard_indexP_subgroups_of_exp_p _ p hp hexp, h]

end NK.LocalInputs.CommGroupRank
