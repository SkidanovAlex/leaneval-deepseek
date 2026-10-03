import Mathlib
import Submission.Work.PlanarSC.exists_pos_le_dist_of_isCompact_of_isClosed
import Submission.Work.PlanarSC.not_isPreconnected_infty_meets

/-!
# A compact gap around a compact complementary component

For a domain `Ω ⊆ ℂ`, a compact connected component `K` of `Ωᶜ` and `a ∈ K`, we produce a compact
set `S` with `a ∈ S ⊆ Ωᶜ` at positive distance from `Ωᶜ ∖ S`.

We work in `X := ↑ '' Ωᶜ ∪ {∞} ⊆ OnePoint ℂ`, a compact `T₂` space (it is the complement of the
open set `↑ '' Ω`).  The delegated lemma `not_isPreconnected_infty_meets` shows that no preconnected
`L ⊆ X` can contain both `a` and `∞`; hence `∞` is not in the component of `a` in the compact space
`X`.  Mathlib's `connectedComponent_eq_iInter_isClopen` then produces a clopen `U ∋ a` in `X` with
`∞ ∉ U`.  Writing `U` in terms of open subsets `W`, `V` of `OnePoint ℂ`,
`U = ↑ ⁻¹' W` and `U = (↑ ⁻¹' V)ᶜ`, the set `S := ↑ ⁻¹' (↑ '' U)` is
`Ωᶜ ∩ ↑ ⁻¹' W` (so `Ωᶜ ∖ S` is closed) and it is contained in a closed ball of `ℂ` (because
`↑ ⁻¹' V` contains a neighbourhood of `∞`), hence compact.  It is at positive distance from
`Ωᶜ ∖ S` by `exists_pos_le_dist_of_isCompact_of_isClosed`.
-/

namespace Work.PlanarSC

open Set Metric

theorem exists_compact_gap_of_component {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {K : Set ℂ} (hKcpt : IsCompact K) (hKconn : IsConnected K) (hKsub : K ⊆ Ωᶜ)
    (hKmax : ∀ S : Set ℂ, IsPreconnected S → K ⊆ S → S ⊆ Ωᶜ → S = K) {a : ℂ} (haK : a ∈ K) :
    ∃ S : Set ℂ, IsCompact S ∧ a ∈ S ∧ S ⊆ Ωᶜ ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ Ωᶜ, s' ∉ S → δ ≤ dist s s' := by
  classical
  -- The compact space `X = ↑ '' Ωᶜ ∪ {∞}`.
  set X : Set (OnePoint ℂ) := ((↑) '' Ωᶜ) ∪ {OnePoint.infty} with hXdef
  have hXcompl : Xᶜ = ((↑) '' Ω : Set (OnePoint ℂ)) := by
    rw [hXdef]
    ext z
    constructor
    · intro hz
      cases z with
      | infty => exact absurd (Or.inr rfl) hz
      | coe w =>
        refine ⟨w, ?_, rfl⟩
        by_contra hw
        exact hz (Or.inl ⟨w, hw, rfl⟩)
    · rintro ⟨w, hw, rfl⟩
      rintro (⟨w', hw', hww⟩ | hww)
      · have h2 : w ∈ Ωᶜ := by rwa [OnePoint.coe_injective hww] at hw'
        exact h2 hw
      · exact OnePoint.coe_ne_infty w hww
  have hXclosed : IsClosed X :=
    isOpen_compl_iff.mp (hXcompl ▸ OnePoint.isOpen_image_coe.mpr hΩo)
  haveI : CompactSpace ↥X := isCompact_iff_compactSpace.mp hXclosed.isCompact
  have haX : (a : OnePoint ℂ) ∈ X := Or.inl ⟨a, hKsub haK, rfl⟩
  have hinfX : (OnePoint.infty : OnePoint ℂ) ∈ X := Or.inr rfl
  set aX : ↥X := ⟨(a : OnePoint ℂ), haX⟩ with haXdef
  -- The crux: `∞` is not in the component of `a` in `X`.
  have hinfComp : (⟨OnePoint.infty, hinfX⟩ : ↥X) ∉ connectedComponent aX := by
    intro hmem
    refine not_isPreconnected_infty_meets hΩo hΩc hKcpt hKconn hKsub hKmax haK
      ⟨Subtype.val '' connectedComponent aX, ?_, ?_, ?_, ?_⟩
    · exact isPreconnected_connectedComponent.image Subtype.val
        continuous_subtype_val.continuousOn
    · exact ⟨aX, mem_connectedComponent, rfl⟩
    · exact ⟨⟨OnePoint.infty, hinfX⟩, hmem, rfl⟩
    · rintro z ⟨u, -, rfl⟩
      exact u.2
  -- Quasicomponent theorem: a clopen neighbourhood `U` of `a` in `X` missing `∞`.
  rw [connectedComponent_eq_iInter_isClopen aX] at hinfComp
  simp only [Set.mem_iInter, not_forall] at hinfComp
  obtain ⟨⟨U, hUclop, haU⟩, hUinf⟩ := hinfComp
  -- Descriptions of `U` by open subsets of `OnePoint ℂ`.
  obtain ⟨W, hWopen, hWU⟩ : ∃ W : Set (OnePoint ℂ), IsOpen W ∧ Subtype.val ⁻¹' W = U :=
    isOpen_induced_iff.mp hUclop.isOpen
  obtain ⟨V, hVopen, hVU⟩ : ∃ V : Set (OnePoint ℂ), IsOpen V ∧ U = (Subtype.val ⁻¹' V)ᶜ := by
    obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hUclop.isClosed.isOpen_compl
    exact ⟨V, hV, by rw [hVU, compl_compl]⟩
  set Ut : Set (OnePoint ℂ) := Subtype.val '' U with hUtdef
  have hinfV : (OnePoint.infty : OnePoint ℂ) ∈ V := by
    have h : (⟨OnePoint.infty, hinfX⟩ : ↥X) ∈ Subtype.val ⁻¹' V := by
      by_contra hc
      exact hUinf (hVU ▸ hc)
    exact h
  have hUtclosed : IsClosed Ut := by
    have hUtV : Ut = X ∩ Vᶜ := by
      rw [hUtdef]
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨u.2, fun huv => ?_⟩
        rw [hVU] at hu
        exact hu huv
      · rintro ⟨hzX, hzV⟩
        refine ⟨⟨z, hzX⟩, ?_, rfl⟩
        rw [hVU]
        exact hzV
    rw [hUtV]
    exact hXclosed.inter hVopen.isClosed_compl
  -- The candidate set `S`.
  set S : Set ℂ := ((↑) : ℂ → OnePoint ℂ) ⁻¹' Ut with hSdef
  have hSclosed : IsClosed S := hUtclosed.preimage OnePoint.continuous_coe
  have hSsub : S ⊆ Ωᶜ := by
    rintro z ⟨u, hu, huz⟩
    have hzX : (z : OnePoint ℂ) ∈ X := by rw [← huz]; exact u.2
    rcases (show (z : OnePoint ℂ) ∈ ((↑) '' Ωᶜ) ∪ {OnePoint.infty} from hXdef ▸ hzX) with
      ⟨w, hw, hwz⟩ | hz
    · rwa [OnePoint.coe_injective hwz] at hw
    · exfalso
      have huz' : u = (⟨OnePoint.infty, hinfX⟩ : ↥X) := Subtype.ext (huz.trans hz)
      exact hUinf (huz' ▸ hu)
  -- `S` is bounded: `↑ ⁻¹' V` contains a neighbourhood of `∞`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, S ⊆ Metric.closedBall (0 : ℂ) R := by
    obtain ⟨s, hs, hsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp (hVopen.mem_nhds hinfV)
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hs.2.isBounded
    refine ⟨R, fun z hz => ?_⟩
    by_contra hzc
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hzc
    have hzs : z ∈ sᶜ := fun hzs =>
      absurd (hR hzs) (by rw [Metric.mem_closedBall, dist_zero_right]; exact not_le.mpr hzc)
    have hzV : (z : OnePoint ℂ) ∈ V := hsub (Or.inl ⟨z, hzs, rfl⟩)
    obtain ⟨u, hu, huz⟩ := hz
    have huinV : (u : OnePoint ℂ) ∈ V := by rw [huz]; exact hzV
    rw [hVU] at hu
    exact hu huinV
  have hScpt : IsCompact S :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hSclosed hR
  -- `S` is relatively open in `Ωᶜ`, so `Ωᶜ ∖ S` is closed.
  have hSW : S = Ωᶜ ∩ (((↑) : ℂ → OnePoint ℂ) ⁻¹' W) := by
    ext z
    constructor
    · rintro ⟨u, hu, huz⟩
      refine ⟨hSsub ⟨u, hu, huz⟩, ?_⟩
      have huW : u ∈ Subtype.val ⁻¹' W := hWU ▸ hu
      change (z : OnePoint ℂ) ∈ W
      rw [← huz]
      exact huW
    · rintro ⟨hzΩ, hzW⟩
      exact ⟨⟨(z : OnePoint ℂ), Or.inl ⟨z, hzΩ, rfl⟩⟩, hWU ▸ hzW, rfl⟩
  have hBclosed : IsClosed (Ωᶜ \ S) := by
    have hEq : Ωᶜ \ S = Ωᶜ ∩ (((↑) : ℂ → OnePoint ℂ) ⁻¹' W)ᶜ := by
      rw [hSW]
      ext z
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    rw [hEq]
    exact hΩo.isClosed_compl.inter (hWopen.preimage OnePoint.continuous_coe).isClosed_compl
  refine ⟨S, hScpt, ⟨aX, haU, rfl⟩, hSsub, ?_⟩
  obtain ⟨δ, hδ, hg⟩ := exists_pos_le_dist_of_isCompact_of_isClosed hScpt hBclosed (by
    rw [Set.disjoint_left]
    rintro z hzS hzB
    exact hzB.2 hzS)
  exact ⟨δ, hδ, fun s hs s' hs' hs'S => hg s hs s' ⟨hs', hs'S⟩⟩

end Work.PlanarSC
