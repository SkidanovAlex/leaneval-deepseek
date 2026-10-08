import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.LocalPrelim

open Subgroup

/-- **A nontrivial subgroup of a nilpotent group is not its own commutator with the whole group.**

More precisely: if `G` is nilpotent and `N ≠ ⊥` is a subgroup of `G`, then `N` is not contained
in `⁅N, ⊤⁆`; we exhibit an explicit element of `N` outside `⁅N, ⊤⁆`.

*Proof.* Let `Zᵢ` be the upper central series of `G`, which reaches `⊤` because `G` is nilpotent.
Choose the least `i` with `N ≤ Zᵢ`; this `i` is nonzero (else `N ≤ Z₀ = ⊥`), say `i = j + 1`.
Then `⁅N, ⊤⁆ ≤ ⁅Z_{j+1}, ⊤⁆ ≤ Z_j` by `Subgroup.commutator_upperCentralSeries_top_le`, while
`N ⊄ Z_j` by minimality of `i`.  Any `x ∈ N \ Z_j` therefore avoids `⁅N, ⊤⁆`. -/
lemma exists_notMem_commutator_of_isNilpotent {G : Type*} [Group G] [Group.IsNilpotent G]
    {N : Subgroup G} (hN : N ≠ ⊥) : ∃ x, x ∈ N ∧ x ∉ (⁅N, ⊤⁆ : Subgroup G) := by
  classical
  obtain ⟨c, hc⟩ := Group.IsNilpotent.nilpotent G
  have hne : ∃ n, N ≤ Subgroup.upperCentralSeries G n := ⟨c, by rw [hc]; exact le_top⟩
  set n := Nat.find hne with hn_def
  have hspec : N ≤ Subgroup.upperCentralSeries G n := Nat.find_spec hne
  have hmin : ∀ m, m < n → ¬ N ≤ Subgroup.upperCentralSeries G m :=
    fun m hm => Nat.find_min hne hm
  have hn0 : n ≠ 0 := by
    rintro h0
    apply hN
    have h := hspec
    rw [h0, Subgroup.upperCentralSeries_zero] at h
    exact le_bot_iff.mp h
  obtain ⟨j, hj⟩ : ∃ j, n = j + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn0)).symm⟩
  rw [hj] at hspec
  have hnot : ¬ N ≤ Subgroup.upperCentralSeries G j := by
    rw [hj] at hmin
    exact hmin j (Nat.lt_succ_self j)
  have hle : (⁅N, ⊤⁆ : Subgroup G) ≤ Subgroup.upperCentralSeries G j :=
    le_trans (Subgroup.commutator_mono hspec le_top)
      (Subgroup.commutator_upperCentralSeries_top_le G j)
  have hnot' : ¬ (N : Set G) ⊆ (Subgroup.upperCentralSeries G j : Set G) := by
    intro hs
    exact hnot (SetLike.le_def.mpr (fun x hx => hs hx))
  obtain ⟨x, hxN, hxZ⟩ := Set.not_subset.mp hnot'
  exact ⟨x, hxN, fun hx => hxZ (hle hx)⟩

/-- **Ambient form of `exists_notMem_commutator_of_isNilpotent`.**

Let `P` be a subgroup of `G` whose own group is nilpotent, and let `N ≤ P` have `N ≠ ⊥` (in `G`).
Then some element of `N` lies outside the commutator `⁅N, P⁆`. -/
lemma exists_notMem_commutator_of_isNilpotent_le {G : Type*} [Group G] {P : Subgroup G}
    [Group.IsNilpotent ↥P] {N : Subgroup G} (hNle : N ≤ P) (hN : N ≠ ⊥) :
    ∃ x, x ∈ N ∧ x ∉ (⁅N, P⁆ : Subgroup G) := by
  -- Work inside `↥P`, where `N` corresponds to `N.subgroupOf P`.
  have hN' : N.subgroupOf P ≠ ⊥ := by
    intro h
    apply hN
    have h1 : (N.subgroupOf P).map P.subtype = (⊥ : Subgroup ↥P).map P.subtype := by rw [h]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNle, Subgroup.map_bot] at h1
    exact h1
  obtain ⟨x, hxN', hxcomm⟩ := exists_notMem_commutator_of_isNilpotent (G := ↥P) hN'
  refine ⟨(x : G), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp hxN'
  · -- `⁅N, P⁆` is the image under `P.subtype` of `⁅N.subgroupOf P, ⊤⁆`.
    intro hxP
    have hmap : (⁅N.subgroupOf P, (⊤ : Subgroup ↥P)⁆).map P.subtype = (⁅N, P⁆ : Subgroup G) := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNle]
      congr 1
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmap] at hxP
    rw [Subgroup.mem_map] at hxP
    obtain ⟨y, hycomm, hyx⟩ := hxP
    apply hxcomm
    have : y = x := Subtype.ext hyx
    rwa [this] at hycomm

/-- **A nontrivial `p`-subgroup normalized by a `p`-subgroup is not its own commutator.**

If `B ≠ ⊥` and `A1` are finite `p`-subgroups of `Q` with `A1 ≤ N_Q(B)`, then `⁅B, A1⁆ ≠ B`.
Indeed `P := B ⊔ A1` is a (finite) `p`-group, hence nilpotent; in a nilpotent group a nontrivial
subgroup `B` cannot equal its commutator with the whole group, and `⁅B, A1⁆ = B` would force
`B ≤ ⁅B, P⁆` with `B ∉ ...` contradicted by `exists_notMem_commutator_of_isNilpotent_le`. -/
theorem pgroup_commutator_ne_self {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {B A1 : Subgroup Q} (hB : IsPGroup p B) (hA1 : IsPGroup p A1)
    (hnorm : A1 ≤ Subgroup.normalizer (B : Set Q)) (hBne : B ≠ ⊥) :
    ⁅B, A1⁆ ≠ B := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `B ⊔ A1` is a finite `p`-group, hence nilpotent.
  have hPp : IsPGroup p ↥(B ⊔ A1) := IsPGroup.to_sup_of_normal_left' hB hA1 hnorm
  haveI : Finite ↥(B ⊔ A1) := Subtype.finite
  haveI : Group.IsNilpotent ↥(B ⊔ A1) := IsPGroup.isNilpotent hPp
  obtain ⟨x, hxN, hxcomm⟩ :=
    exists_notMem_commutator_of_isNilpotent_le (P := B ⊔ A1) le_sup_left hBne
  intro h
  apply hxcomm
  -- `x ∈ B = ⁅B, A1⁆ ≤ ⁅B, B ⊔ A1⁆`, contradicting `x ∉ ⁅B, B ⊔ A1⁆`.
  have hx : x ∈ ⁅B, A1⁆ := by rw [h]; exact hxN
  exact Subgroup.commutator_mono le_rfl le_sup_right hx

end Work.LocalPrelim
