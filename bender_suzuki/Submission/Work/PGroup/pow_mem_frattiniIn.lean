import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

/-!
# Every `p`-th power lies in the Frattini subgroup of a finite `p`-group

For a finite `p`-group `G` the Frattini subgroup `Φ(G) = frattini G` contains the `p`-th power of
every element.  Equivalently `G / Φ(G)` has exponent dividing `p`.

The proof is the classical one: `Φ(G)` is the intersection of the maximal subgroups; a maximal
subgroup `M` of a finite `p`-group is normal (its normalizer is itself, by nilpotency), and `G/M`
has no proper nontrivial subgroups, hence is a simple `p`-group and therefore has order exactly
`p`.  So every `p`-th power dies in `G/M`, i.e. lies in `M`.

The main statement of this file, `Work.PGroup.pow_mem_frattiniIn`, is the statement for a subgroup
`P ≤ G` phrased in terms of `Work.PGroup.frattiniIn`.
-/

namespace Work.PGroup

open scoped Classical Pointwise
open Subgroup

/-- In a finite `p`-group `G`, every `p`-th power lies in the Frattini subgroup `Φ(G)`. -/
theorem pow_mem_frattini {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) (x : G) : x ^ p ∈ frattini G := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent G := IsPGroup.isNilpotent hG
  rw [frattini, Order.radical]
  simp only [Subgroup.mem_iInf, Set.mem_ofPred_eq]
  intro M hM
  -- `M` is maximal, hence normal in the nilpotent group `G`.
  have hMn : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M (Group.normalizerCondition_of_isNilpotent) hM
  haveI := hMn
  -- `G ⧸ M` is nontrivial, since `M ≠ ⊤`.
  have hQnt : Nontrivial (G ⧸ M) := by
    obtain ⟨a, -, ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hM.1)
    exact ⟨QuotientGroup.mk a, 1, fun h => ha ((QuotientGroup.eq_one_iff a).mp h)⟩
  -- `G ⧸ M` has no proper nontrivial subgroups, so it is simple.
  haveI : IsSimpleGroup (G ⧸ M) :=
    (isSimpleGroup_iff (G ⧸ M)).mpr ⟨hQnt, fun H _ =>
      ((QuotientGroup.comapMk'OrderIso M).isSimpleOrder_iff.mpr
        (Set.isSimpleOrder_Ici_iff_isCoatom.mpr hM)).2 H⟩
  have hpQ : IsPGroup p (G ⧸ M) := hG.to_quotient M
  have hnilQ : Group.IsNilpotent (G ⧸ M) := IsPGroup.isNilpotent hpQ
  haveI := hnilQ
  -- A simple `p`-group has order exactly `p`.
  have hq : (Nat.card (G ⧸ M)).Prime := IsSimpleGroup.prime_card
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpQ
  have hcard : Nat.card (G ⧸ M) = p := by
    have hpn : (p ^ n).Prime := hn ▸ hq
    rw [hn, hpn.eq_one_of_pow, pow_one]
  -- hence every `p`-th power is trivial in `G ⧸ M`, i.e. lies in `M`.
  have hxp : ((x : G) : G ⧸ M) ^ p = 1 := by
    haveI : Fintype (G ⧸ M) := Fintype.ofFinite _
    have h := pow_card_eq_one (G := G ⧸ M) (x := (x : G ⧸ M))
    rwa [Fintype.card_eq_nat_card, hcard] at h
  rw [← QuotientGroup.eq_one_iff (x ^ p), QuotientGroup.mk_pow]
  exact hxp

theorem pow_mem_frattiniIn {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (P : Subgroup G)
    [Finite P] (hP : IsPGroup p P) {x : G} (hx : x ∈ P) : x ^ p ∈ Work.PGroup.frattiniIn P := by
  rw [frattiniIn]
  refine Subgroup.mem_map.mpr ⟨(⟨x, hx⟩ : P) ^ p, pow_mem_frattini hp hP ⟨x, hx⟩, ?_⟩
  simp

end Work.PGroup
