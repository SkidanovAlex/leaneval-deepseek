import Mathlib
import Submission.Work.ZJB.Step1.Defs
import Submission.Work.ZJB2.sylowInConj
import Submission.OddOrder.GroupTheory.ThompsonSubgroupAbelian

/-!
# `ZJB2`, leaf `br`: `(C_p)` inside `M` from `(C_p)` for the group `↥M`

Glauberman 1968, Theorem B induction (p. 1125): the induction hypothesis is available for the
*group* `↥M`, in the paper's own convention (`SatisfiesCpPaper p ↥M`), whereas Theorem 5.1 works
"inside `G`" and needs the same condition for the subgroup `M ⊆ G` (`CpIn p M`) with the Sylow
subgroup `T ≤ M`, the subset `W ⊆ T` and the conjugating element `g ∈ M` all living in `G`.

This file proves the transport `CpInOfSatisfiesProp`:

  `SatisfiesCpPaper p ↥M  ⟹  CpIn p M`.

Everything is pushed through the inclusion `M.subtype : ↥M →* G`:

* a maximal `p`-subgroup `T ≤ M` of `M` is `S.subgroupOf M` for the Sylow `S` of `↥M` given by
  `ZJB2.subgroupOfIsSylow` (mirror of `Sylow`-conjugacy in `↥M`);
* `Z(J(·))` travels across an injective homomorphism
  (`map_ZJ_subtype`, via `thompsonJAbelian_map_of_injective` and
  `map_centralizer_inf_of_disjoint_ker`);
* `N(·)` travels by `Subgroup.le_normalizer_map`, `C(·)` elementwise.
-/

namespace Work.ZJB2.Step1

open Subgroup Work.ZJB

/-- `J(·)` (the join of the maximal-order abelian subgroups) is covariant under an injective
homomorphism; here specialised to a subgroup inclusion `↥K ↪ G`.  (`Work.GW2.thompsonJ` is the
odd-order library's `Subgroup.thompsonJAbelian`.) -/
theorem thompsonJ_map_subtype {G : Type*} [Group G] (K : Subgroup G) (P : Subgroup ↥K) :
    (Work.GW2.thompsonJ P).map K.subtype = Work.GW2.thompsonJ (P.map K.subtype) := by
  rw [Work.GW2.thompsonJ_eq_thompsonJAbelian, Work.GW2.thompsonJ_eq_thompsonJAbelian]
  exact (Subgroup.thompsonJAbelian_map_of_injective K.subtype_injective P).symm

/-- **The image of `Z(J(P))` under a subgroup inclusion is `Z(J(P))` of the image.**  This is
`Z(J(·))` as a characteristic functor restricted to injective maps: combine the covariance of
`J` with `Subgroup.map_centralizer_inf_of_disjoint_ker` (whose disjointness hypothesis is
automatic since `K.subtype` is injective). -/
theorem map_ZJ_subtype {G : Type*} [Group G] (K : Subgroup G) (P : Subgroup ↥K) :
    (Work.GW2.ZJ P).map K.subtype = Work.GW2.ZJ (P.map K.subtype) := by
  have hJ := thompsonJ_map_subtype K P
  have hker : K.subtype.ker = ⊥ := (MonoidHom.ker_eq_bot_iff K.subtype).mpr K.subtype_injective
  have hc := Subgroup.map_centralizer_inf_of_disjoint_ker (f := K.subtype)
    (J := Work.GW2.thompsonJ P) (by rw [hker]; exact disjoint_bot_right)
  rw [Work.GW2.ZJ, inf_comm, hc, hJ, Work.GW2.ZJ, inf_comm]

/-- **Theorem B induction hypothesis, transported into the ambient group.**  If the group `↥M`
satisfies the paper's `(C_p)` for every one of its Sylow `p`-subgroups, then the same condition
holds for `M` regarded as a subgroup of `G`: for every maximal `p`-subgroup `T ≤ M`, every
nonempty `W ⊆ T` and every `g ∈ M` with `W^g ⊆ T` (i.e. `g⁻¹ w g ∈ T` for `w ∈ W`), one has
`g = c * n` with `c ∈ M ∩ C_G(W)` and `n ∈ M ∩ N_G(Z(J(T)))`. -/
theorem cpInOfSatisfiesProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.CpInOfSatisfiesProp p G := by
  intro M hsat T hT W hWne hWT g hgM hconj
  -- `S` is the Sylow `p`-subgroup of `↥M` cutting out `T` inside `M`.
  let S : Sylow p ↥M := Work.ZJB2.subgroupOfIsSylow hT
  have hS : (S : Subgroup ↥M) = T.subgroupOf M := Work.ZJB2.subgroupOfIsSylow_coe hT
  have hCp := hsat S
  -- `W`, viewed inside `↥M`.
  set W' : Set ↥M := M.subtype ⁻¹' W with hW'def
  have hW'ne : W'.Nonempty := by
    obtain ⟨w, hw⟩ := hWne
    exact ⟨⟨w, hT.1 (hWT hw)⟩, hw⟩
  have hW'S : W' ⊆ (S : Set ↥M) := by
    intro x hx
    change x ∈ (S : Subgroup ↥M)
    rw [hS, Subgroup.mem_subgroupOf]
    exact hWT hx
  have hconj' : ∀ w ∈ W', (⟨g, hgM⟩ : ↥M)⁻¹ * w * ⟨g, hgM⟩ ∈ (S : Subgroup ↥M) := by
    intro w hw
    rw [hS, Subgroup.mem_subgroupOf]
    simpa using hconj (M.subtype w) hw
  -- `(C_p)` in `↥M`.
  obtain ⟨c, n, hc, hn, hcn⟩ := hCp W' hW'ne hW'S ⟨g, hgM⟩ hconj'
  -- `Z(J(·))` transports along `M.subtype`.
  have hZJmap : (Work.GW2.ZJ (S : Subgroup ↥M)).map M.subtype = Work.GW2.ZJ T := by
    rw [hS, map_ZJ_subtype M (T.subgroupOf M), Subgroup.map_subgroupOf_eq_of_le hT.1]
  -- `n ∈ N(Z(J(T)))` in `G`.
  have hnG : (n : G) ∈ Subgroup.normalizer (Work.GW2.ZJ T : Set G) := by
    have h1 : (n : G) ∈ Subgroup.map M.subtype
        (Subgroup.normalizer (Work.GW2.ZJ (S : Subgroup ↥M) : Set ↥M)) :=
      Subgroup.mem_map_of_mem M.subtype hn
    have h2 := Subgroup.le_normalizer_map (f := M.subtype)
      (H := Work.GW2.ZJ (S : Subgroup ↥M)) h1
    rwa [hZJmap] at h2
  -- `c ∈ C_G(W)`.
  have hcG : (c : G) ∈ Subgroup.centralizer W := by
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro w hw
    have hwM : w ∈ M := hT.1 (hWT hw)
    have := hc ⟨w, hwM⟩ hw
    simpa using congrArg (M.subtype) this
  -- `g = c * n` in `G`.
  have hgn : g = (c : G) * (n : G) := by
    have := congrArg (M.subtype) hcn
    simpa using this
  exact ⟨(c : G), (n : G), c.2, hcG, n.2, hnG, hgn⟩

end Work.ZJB2.Step1
