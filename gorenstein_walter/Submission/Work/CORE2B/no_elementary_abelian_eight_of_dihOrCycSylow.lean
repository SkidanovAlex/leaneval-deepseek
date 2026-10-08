import Mathlib
import Submission.Work.RED.no_elementary_abelian_eight
import Submission.Work.RED.DihedralFacts

/-!
# No elementary abelian subgroup of order eight when all Sylow 2-subgroups are cyclic or dihedral

If every Sylow 2-subgroup `P` of a finite group `G` is cyclic or isomorphic to a dihedral
group `DihedralGroup n`, then `G` has no subgroup `W` of cardinality `8` all of whose
elements are involutions, i.e. no elementary abelian subgroup of order `8` (equivalently,
the 2-rank of `G` is at most `2`).

A subgroup `W` of order `8 = 2^3` all of whose elements square to `1` is a 2-group, hence is
contained in some Sylow 2-subgroup `P` of `G`.

* If `P` is cyclic, then so is `W` (a subgroup of a cyclic group), so `Nat.card W = 8` would
  force a generator of order `8`, contradicting `x ^ 2 = 1`; quantitatively,
  a finite cyclic group of exponent two has at most two elements.
* If `P ≅ DihedralGroup n`, then pushing `W` along this isomorphism produces a subgroup of
  `DihedralGroup n` with the same properties, impossible by the 2-rank bound for dihedral
  groups (`Work.RED.no_elementary_abelian_eight`, built on `Work.RED.DihedralFactsProp`).
-/

namespace Work.CORE2B

/-- A finite dihedral group has nonzero parameter. -/
private theorem neZero_of_finite_dihedral {n : ℕ} (h : Finite (DihedralGroup n)) : NeZero n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at h
    exact (not_finite_iff_infinite.mpr (inferInstance : Infinite (DihedralGroup 0)) h).elim
  · exact ⟨hn.ne'⟩

/-- A finite cyclic group of exponent two has at most two elements. -/
private theorem natCard_le_two_of_isCyclic_sq {H : Type} [Group H] [Finite H] [IsCyclic H]
    (h : ∀ x : H, x * x = 1) : Nat.card H ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have htop : Subgroup.zpowers g = (⊤ : Subgroup H) := eq_top_iff.mpr fun x _ => hg x
  have hord : orderOf g = Nat.card H := by
    rw [← Nat.card_zpowers g, htop, Subgroup.card_top]
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact h g
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem no_elementary_abelian_eight_of_dihOrCycSylow {G : Type} [Group G] [Finite G]
    (h : ∀ P : Sylow 2 G, IsCyclic P ∨ ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    ¬ ∃ W : Subgroup G, Nat.card W = 8 ∧ ∀ x ∈ W, x ^ 2 = 1 := by
  rintro ⟨W, hWcard, hWsq⟩
  -- `W` has order `8 = 2 ^ 3`, so it is a 2-group and lies in a Sylow 2-subgroup.
  have hWpg : IsPGroup 2 ↥W := IsPGroup.of_card (n := 3) (by rw [hWcard]; norm_num)
  obtain ⟨P, hWP⟩ := hWpg.exists_le_sylow
  rcases h P with hcyc | ⟨n, ⟨e⟩⟩
  · -- `P` is cyclic, hence so is `W`, hence `Nat.card W ≤ 2`.
    haveI : IsCyclic ↥(P : Subgroup G) := hcyc
    haveI : IsCyclic ↥W := Subgroup.isCyclic_of_le hWP
    have h2 : Nat.card ↥W ≤ 2 := natCard_le_two_of_isCyclic_sq fun x => by
      refine Subtype.ext ?_
      simpa [pow_two] using hWsq (x : G) x.2
    omega
  · -- `P ≅ DihedralGroup n`, and dihedral groups have 2-rank at most `2`.
    haveI : NeZero n := neZero_of_finite_dihedral
      (Finite.of_injective (e.symm : DihedralGroup n → ↥(P : Subgroup G)) e.symm.injective)
    exact Work.RED.no_elementary_abelian_eight Work.RED.DihedralFacts e ⟨W, hWcard, hWsq⟩

end Work.CORE2B
