import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.conj_subgroupOf_inf
import Submission.Work.PSU3.StageA.involution_mem_inf_of_odd_index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs

/-- The cardinality of `H.subgroupOf K` equals the cardinality of `H ⊓ K`. -/
theorem natCard_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.subgroupOf_map_subtype H K]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective (H.subgroupOf K) K.subtype K.subtype_injective).toEquiv

/-- A divisor of an odd number is odd. -/
theorem odd_of_dvd {m n : ℕ} (h : m ∣ n) (hn : Odd n) : Odd m := by
  rw [← Nat.not_even_iff_odd] at hn ⊢
  intro hm
  exact hn (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hm).trans h))

/-- **Bender–Suzuki, Stage A.**  If `M` is strongly embedded in `G` and `L ◁ G` has odd index,
then `M ∩ L` is strongly embedded in `L`.

The mathematical content is the classical observation that every involution of `G` lies in
every normal subgroup of odd index: an element of order `2` maps to an element of order `≤ 2`
in `G/L`, a group of odd order, hence to `1`.  So `M ∩ L` still has even order, and for
`g ∈ L \ M` the two-point stabiliser `(M ∩ L) ∩ (M ∩ L)^g` is a subgroup of `M ∩ M^g`, which
has odd order by strong embeddedness of `M`. -/
theorem oddIndexStrongEmbedded {G : Type} [Group G] [Finite G] {L M : Subgroup G}
    (hLn : L.Normal) (hLodd : Odd L.index)
    (hM : LeanEval.GroupTheory.Defs.IsStronglyEmbedded M) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((M ⊓ L).subgroupOf L) := by
  obtain ⟨hMne, hMeven, hModd⟩ := hM
  -- An involution of `G` lying in `M ∩ L`.
  obtain ⟨t, htML, ht2⟩ :=
    involution_mem_inf_of_odd_index (N := L) (H := M) hLn hLodd hMeven
  have htM : t ∈ M := (Subgroup.mem_inf.mp htML).1
  have htL : t ∈ L := (Subgroup.mem_inf.mp htML).2
  have hEvenL : Even (Nat.card L) := by
    rw [even_iff_two_dvd]
    have hord : orderOf (⟨t, htL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk, ht2]
    rw [← hord]; exact orderOf_dvd_natCard _
  have hEvenA : Even (Nat.card ↥(M ⊓ L)) := by
    rw [even_iff_two_dvd]
    have hord : orderOf (⟨t, htML⟩ : ↥(M ⊓ L)) = 2 := by rw [Subgroup.orderOf_mk, ht2]
    rw [← hord]; exact orderOf_dvd_natCard _
  -- `M ∩ L` is proper in `L`: otherwise `L ≤ M`, and applying strong embeddedness of `M`
  -- to some `g ∉ M` would force `|M ∩ M^g|` to be both even (it contains `L`) and odd.
  have hKne : (M ⊓ L).subgroupOf L ≠ ⊤ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_top, le_inf_iff]
    rintro ⟨hLM, -⟩
    have hex : ∃ g : G, g ∉ M := by
      by_contra hcon
      apply hMne
      rw [← top_le_iff]
      intro g _
      by_contra hg
      exact hcon ⟨g, hg⟩
    obtain ⟨g, hg⟩ := hex
    have hLleMg : L ≤ M.map (MulAut.conj g).toMonoidHom := by
      have hfix : L.map (MulAut.conj g).toMonoidHom = L :=
        Subgroup.normal_iff_map_conj_eq.mp hLn g
      rw [← hfix]
      exact Subgroup.map_mono hLM
    have hle : L ≤ M ⊓ M.map (MulAut.conj g).toMonoidHom := le_inf hLM hLleMg
    have hdvd : Nat.card L ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom) :=
      Subgroup.card_dvd_of_le hle
    have hEven : Even (Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom)) :=
      even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hEvenL).trans hdvd)
    exact (Nat.not_even_iff_odd.mpr (hModd g hg)) hEven
  have hKeven : Even (Nat.card ↥((M ⊓ L).subgroupOf L)) := by
    rw [natCard_subgroupOf, inf_eq_left.mpr (inf_le_right : M ⊓ L ≤ L)]
    exact hEvenA
  refine ⟨hKne, hKeven, ?_⟩
  -- Two-point stabilisers inside `L` are subgroups of the corresponding ones inside `G`.
  intro g hg
  have hgG : (g : G) ∉ M := by
    intro h
    exact hg (by rw [Subgroup.mem_subgroupOf]; exact ⟨h, g.2⟩)
  have hodd := hModd (g : G) hgG
  have hcard : Nat.card ↥((M ⊓ L).subgroupOf L ⊓
        ((M ⊓ L).subgroupOf L).map (MulAut.conj g).toMonoidHom)
      = Nat.card ↥((M ⊓ L) ⊓ (M ⊓ L).map (MulAut.conj (g : G)).toMonoidHom) := by
    rw [conj_subgroupOf_inf (inf_le_right : M ⊓ L ≤ L) g, natCard_subgroupOf]
    rw [inf_eq_left.mpr
      (inf_le_left.trans inf_le_right :
        (M ⊓ L) ⊓ (M ⊓ L).map (MulAut.conj (g : G)).toMonoidHom ≤ L)]
  rw [hcard]
  exact odd_of_dvd (Subgroup.card_dvd_of_le (le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans (Subgroup.map_mono inf_le_left)))) hodd

end Work.PSU3.StageA
