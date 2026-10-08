import Mathlib
import Submission.Work.DSTR.Defs

namespace Work.DSTR

set_option linter.style.haveILetI false

open Subgroup

/-- A perfect group has no normal subgroup of index two: an index-`2` subgroup `N` is normal and
the quotient `G ⧸ N` has order `2`, hence is cyclic (so commutative), so `⁅G, G⁆ ≤ N`.  But
`G` is perfect, i.e. `⁅G, G⁆ = ⊤`, forcing `N = ⊤` and index `1`. -/
lemma index_ne_two_of_isPerfect {G : Type*} [Group G] (hperf : Group.IsPerfect G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hidx
  haveI := hN
  have hcard : Nat.card (G ⧸ N) = 2 := by
    rw [← Subgroup.index_eq_card N, hidx]
  haveI : IsCyclic (G ⧸ N) := isCyclic_of_prime_card (p := 2) hcard
  have hcomm : IsMulCommutative (G ⧸ N) := IsCyclic.isMulCommutative
  have hle : commutator G ≤ N := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have htop : commutator G = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [htop] at hle
  have hNtop : N = ⊤ := top_le_iff.mp hle
  rw [hNtop, Subgroup.index_top] at hidx
  exact absurd hidx (by norm_num)

/-- A noncyclic group isomorphic to `DihedralGroup n` has `n ≥ 2`: `DihedralGroup 1` is cyclic of
order `2` (and `DihedralGroup 0` is infinite, so cannot be isomorphic to a finite group). -/
lemma two_le_of_noncyclic_dihedral_iso {S : Type*} [Group S] [Finite S] (n : ℕ)
    (e : S ≃* DihedralGroup n) (hnc : ¬ IsCyclic S) : 2 ≤ n := by
  by_contra h
  have hn : n ≤ 1 := by omega
  interval_cases n
  · have hcard : Nat.card S = 2 * 0 := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hpos : 0 < Nat.card S := Nat.card_pos
    omega
  · exact hnc ((e.isCyclic).mpr (DihedralGroup.isCyclic_iff.mpr rfl))

/-- **`LayerOneInvClassProp`** (design3 §9, Core3 §4; consumed by CORE4): the normal quasisimple subgroup `E` of a D-group has one class of involutions (under conjugation by `E`).  `E` is perfect, so it has no normal subgroup of index `2`; `h4` gives a noncyclic Sylow 2 of `E` which `h1` makes dihedral of order `>= 4`, and `hfus` (Gorenstein 7.7 / FUS) applies to `E`. -/
theorem layerOneInvClass (h1 : Work.GW2.DihOrCycHeredProp)
    (h4 : Work.GW2.QuasisimpleSylowProp) (hfus : Work.GW2.InvolutionFusionProp) :
    Work.GW2.LayerOneInvClassProp := by
  intro X _ _ hFT hsy E _hnormal hQ x hx y hy hx2 hy2
  -- `DS1` (`h1`) transfers the Sylow 2-shape of `X` to the subgroup `E`.
  have hsyE : Work.GW2.DihOrCycSylow ↥E := (h1 X hsy).1 E
  -- Pick a Sylow 2-subgroup of `E`; `DS4` (`h4`) makes it noncyclic.
  let S : Sylow 2 ↥E := Classical.choice (Sylow.nonempty (p := 2) (G := ↥E))
  have hnc : ¬ IsCyclic (S : Subgroup ↥E) := h4 X hFT E hQ S
  rcases hsyE S with hcyc | ⟨n, ⟨e⟩⟩
  · exact absurd hcyc hnc
  · -- The Sylow 2-subgroup is dihedral of order `≥ 4`.
    have hn2 : 2 ≤ n := two_le_of_noncyclic_dihedral_iso n e hnc
    -- `E` is quasisimple, hence perfect, hence has no normal subgroup of index `2`.
    have hnoN : ∀ N : Subgroup ↥E, N.Normal → N.index ≠ 2 :=
      index_ne_two_of_isPerfect (Subgroup.isPerfect_iff.mpr hQ.1)
    -- FUS: all involutions of `E` are conjugate in `E`.
    have hconj : IsConj (⟨x, hx⟩ : ↥E) ⟨y, hy⟩ :=
      (hfus ↥E S n hn2 ⟨e⟩ hnoN).1 ⟨x, hx⟩ ⟨y, hy⟩
        (by rw [← Subgroup.orderOf_coe]; exact hx2)
        (by rw [← Subgroup.orderOf_coe]; exact hy2)
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    exact ⟨(g : X), g.2, by simpa using congrArg Subtype.val hg⟩

end Work.DSTR
