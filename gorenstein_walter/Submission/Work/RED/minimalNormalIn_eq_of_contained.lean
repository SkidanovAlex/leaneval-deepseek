import Mathlib
import Submission.Work.RED.Basic
import Submission.Work.RED.MinimalNormalFacts
import Submission.Work.RED.exists_sixteen_of_two_fourGroups
import Submission.Work.RED.no_elementary_abelian_sixteen

/-!
# RED: a minimal normal subgroup of `N` containing a four-group is all of `N`

This is the field `RedFacts.eqOfContained` of the RED blueprint (`NOTES_RED.md` §4): if `N` is a
minimal normal subgroup of `G`, `K` is a minimal normal subgroup of `↥N` containing a four-group
`V`, and the Sylow 2-subgroups of `G` are dihedral, then `K = N`.

Suppose `K ≠ N`.  Then `K` is not normal in `G` -- otherwise the minimality of `N` would force
`K = N` -- so for some `g` the conjugate `Kᵍ` differs from `K`.  By `Work.RED.MNF.conj_minimal`
it is again minimal normal in `N`, hence (`MinimalNormalFactsProp.commute_of_minimalNormalIn`)
`K ⊓ Kᵍ = ⊥` and `K`, `Kᵍ` commute elementwise.  Then `V` and `Vᵍ` are two commuting four-groups
meeting trivially, so `Work.RED.exists_sixteen_of_two_fourGroups` produces an elementary abelian
subgroup of order `16` in `G`; it is a 2-group, so it embeds into a Sylow 2-subgroup of `G`, i.e.
into `DihedralGroup n`, contradicting the 2-rank bound
`DihedralFactsProp.elementary_abelian_card_le_four` (`Work.RED.no_elementary_abelian_sixteen`).
-/

namespace Work.RED

open Subgroup

theorem minimalNormalIn_eq_of_contained
    (hmin : Work.RED.GW2.MinimalNormalFactsProp) (hdi : Work.RED.GW2.DihedralFactsProp)
    {G : Type} [Group G] [Finite G] (N K : Subgroup G) (hN : Work.RED.GW2.IsMinimalNormal N)
    (hK : Work.RED.GW2.IsMinimalNormalIn N K)
    (hV : ∃ V : Subgroup G, V ≤ K ∧ Work.RED.GW2.IsFourGroup V)
    {n : ℕ} [NeZero n] {P : Sylow 2 G} (e : ↥(P : Subgroup G) ≃* DihedralGroup n) (hn : 2 ≤ n) :
    K = N := by
  by_contra hKN_ne
  have hKNle : K ≤ N := hK.le
  -- If `K` were normal in `G`, minimality of `N` would give `K = N`.
  have hKnotNormal : ¬ K.Normal := by
    intro hKnorm
    exact hKN_ne (Work.RED.GW2.IsMinimalNormal.eq_of_le hN hKnorm hK.ne_bot hKNle)
  -- Hence some conjugate of `K` differs from `K`.
  obtain ⟨g, hg⟩ : ∃ g : G, K.map (MulAut.conj g) ≠ K := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hKnotNormal (Subgroup.normal_iff_map_conj_eq.mpr hc)
  -- `Kᵍ` is again a minimal normal subgroup of `N`, distinct from `K`.
  have hKg : Work.RED.GW2.IsMinimalNormalIn N (K.map (MulAut.conj g)) :=
    Work.RED.MNF.conj_minimal hN hK g
  have hcommKV :=
    hmin.commute_of_minimalNormalIn G N K (K.map (MulAut.conj g)) hN hK hKg (Ne.symm hg)
  -- The conjugate of the four-group lies in `Kᵍ` and is again a four-group.
  obtain ⟨V, hVK, hV4⟩ := hV
  set V₂ : Subgroup G := V.map (MulAut.conj g) with hV₂def
  have hV₂le : V₂ ≤ K.map (MulAut.conj g) := by
    rw [hV₂def]; exact Subgroup.map_mono hVK
  have hV₂4 : Work.RED.GW2.IsFourGroup V₂ := by
    rw [hV₂def]
    exact (Work.RED.GW2.isFourGroup_map_iff (MulAut.conj g) V).2 hV4
  -- `V` and `Vᵍ` meet trivially (both inside `K` and `Kᵍ`, whose intersection is trivial).
  have hdisj : V ⊓ V₂ = ⊥ := by
    apply le_bot_iff.mp
    calc V ⊓ V₂ ≤ K ⊓ K.map (MulAut.conj g) :=
          le_inf (le_trans inf_le_left hVK) (le_trans inf_le_right hV₂le)
      _ = ⊥ := hcommKV.1
  have hcommV : ∀ x ∈ V, ∀ y ∈ V₂, x * y = y * x :=
    fun x hx y hy => hcommKV.2 x (hVK hx) y (hV₂le hy)
  -- Two commuting four-groups with trivial intersection give an elementary abelian group of
  -- order `16`, which cannot exist inside `G`.
  obtain ⟨W, hWcard, hWsq⟩ := exists_sixteen_of_two_fourGroups hV4 hV₂4 hdisj hcommV
  exact no_elementary_abelian_sixteen hdi e ⟨W, hWcard, hWsq⟩

end Work.RED
