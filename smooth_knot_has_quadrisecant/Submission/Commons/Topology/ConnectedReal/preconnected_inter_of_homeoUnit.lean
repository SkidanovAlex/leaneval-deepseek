import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Commons.Topology.ConnectedReal.preconnected_inter_of_isOpen

open Set

namespace Commons.Topology.ConnectedReal

/-- The open real interval `(lo,hi)` as a type (`{t : ℝ // t ∈ Set.Ioo lo hi}`),
with the subspace topology from ℝ. -/
abbrev OpenRealInterval (lo hi : ℝ) : Type := {t : ℝ // t ∈ Set.Ioo lo hi}

/-- In the type `OpenRealInterval lo hi`, the intersection of two open preconnected
sets with a nonempty intersection is again preconnected.  Proof: the inclusion of
the interval into ℝ is an open embedding (the interval is open in ℝ); push both
sets into ℝ, apply the ℝ fact `preconnected_inter_of_isOpen`, then pull
preconnectedness back along the embedding. -/
lemma preconnected_inter_of_isOpen_interval {lo hi : ℝ} {s t : Set (OpenRealInterval lo hi)}
    (hs_open : IsOpen s) (ht_open : IsOpen t)
    (hs : IsPreconnected s) (ht : IsPreconnected t)
    (hne : (s ∩ t).Nonempty) : IsPreconnected (s ∩ t) := by
  classical
  let v : OpenRealInterval lo hi → ℝ := fun y => (y : ℝ)
  have hv_ind : Topology.IsInducing v := by
    change Topology.IsInducing (Subtype.val : {t : ℝ // t ∈ Set.Ioo lo hi} → ℝ)
    exact Topology.IsInducing.subtypeVal (Y := ℝ) (t := Set.Ioo lo hi)
  have hv_inj : Function.Injective v := by
    change Function.Injective (Subtype.val : {t : ℝ // t ∈ Set.Ioo lo hi} → ℝ)
    exact (Subtype.val_injective : Function.Injective
      (Subtype.val : {t : ℝ // t ∈ Set.Ioo lo hi} → ℝ))
  have hIoo_open : IsOpen (Set.Ioo lo hi : Set ℝ) := isOpen_Ioo (α := ℝ)
  have hv_openMap : IsOpenMap v := by
    simpa [v] using (IsOpen.isOpenMap_subtype_val (s := (Set.Ioo lo hi : Set ℝ)) hIoo_open)
  have hs_im_open : IsOpen (v '' s) := hv_openMap s hs_open
  have ht_im_open : IsOpen (v '' t) := hv_openMap t ht_open
  have hs_im_pre : IsPreconnected (v '' s) := by
    exact (Topology.IsInducing.isPreconnected_image (f := v) (s := s) hv_ind).2 hs
  have ht_im_pre : IsPreconnected (v '' t) := by
    exact (Topology.IsInducing.isPreconnected_image (f := v) (s := t) hv_ind).2 ht
  have hne_im : ((v '' s) ∩ (v '' t)).Nonempty := by
    rcases hne with ⟨a, has, hat⟩
    exact ⟨v a, mem_image_of_mem v has, mem_image_of_mem v hat⟩
  have hpre_im : IsPreconnected ((v '' s) ∩ (v '' t)) :=
    preconnected_inter_of_isOpen hs_im_open ht_im_open hs_im_pre ht_im_pre hne_im
  have hinter_eq : v '' (s ∩ t) = (v '' s) ∩ (v '' t) := Set.image_inter hv_inj
  have hpre_sit_im : IsPreconnected (v '' (s ∩ t)) := by
    simpa [hinter_eq] using hpre_im
  exact (Topology.IsInducing.isPreconnected_image (f := v) (s := s ∩ t) hv_ind).1 hpre_sit_im

/-- If a region `Ω` of `X` is homeomorphic to the open real interval `(0,1)`, then
the intersection of two open preconnected subsets of `Ω` with nonempty
intersection is preconnected.  Proof: transport the two sets into the interval via
the homeomorphism, apply `preconnected_inter_of_isOpen_interval` there, and
transport back (openness and preconnectedness are preserved by homeomorphisms and
by the subspace inclusion of `Ω` into `X`). -/
lemma preconnected_inter_of_homeoUnit {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (e : {x : X // x ∈ Ω} ≃ₜ OpenRealInterval 0 1)
    {s t : Set X} (hs_open : IsOpen s) (ht_open : IsOpen t)
    (hssub : s ⊆ Ω) (htsub : t ⊆ Ω)
    (hs : IsPreconnected s) (ht : IsPreconnected t)
    (hne : (s ∩ t).Nonempty) : IsPreconnected (s ∩ t) := by
  classical
  let π : {x : X // x ∈ Ω} → X := fun z => (z : X)
  let S : Set {x : X // x ∈ Ω} := π ⁻¹' s
  let T : Set {x : X // x ∈ Ω} := π ⁻¹' t
  have hπ_ind : Topology.IsInducing π := by
    simpa [π] using (Topology.IsInducing.subtypeVal (Y := X) (t := Ω))
  have hπ_cont : Continuous π := by
    simpa [π] using (continuous_subtype_val : Continuous (Subtype.val : {x : X // x ∈ Ω} → X))
  have hS_open : IsOpen S := by
    dsimp [S, π]
    exact hs_open.preimage hπ_cont
  have hT_open : IsOpen T := by
    dsimp [T, π]
    exact ht_open.preimage hπ_cont
  have hS_eq : π '' S = s := by
    ext x
    constructor
    · rintro ⟨z, hzS, hzx⟩
      rw [← hzx]
      simpa [S, π] using hzS
    · intro hx
      refine ⟨⟨x, hssub hx⟩, ?_, rfl⟩
      simpa [S, π] using hx
  have hT_eq : π '' T = t := by
    ext x
    constructor
    · rintro ⟨z, hzT, hzx⟩
      rw [← hzx]
      simpa [T, π] using hzT
    · intro hx
      refine ⟨⟨x, htsub hx⟩, ?_, rfl⟩
      simpa [T, π] using hx
  have hS_pre : IsPreconnected S := by
    have hsπ : IsPreconnected (π '' S) := by simpa [hS_eq] using hs
    exact (Topology.IsInducing.isPreconnected_image (f := π) (s := S) hπ_ind).1 hsπ
  have hT_pre : IsPreconnected T := by
    have htπ : IsPreconnected (π '' T) := by simpa [hT_eq] using ht
    exact (Topology.IsInducing.isPreconnected_image (f := π) (s := T) hπ_ind).1 htπ
  have hneST : (S ∩ T).Nonempty := by
    rcases hne with ⟨x, hxs, hxt⟩
    refine ⟨⟨x, hssub hxs⟩, ?_, ?_⟩
    · simpa [S, π] using hxs
    · simpa [T, π] using hxt
  let A : Set (OpenRealInterval 0 1) := e '' S
  let B : Set (OpenRealInterval 0 1) := e '' T
  have hA_open : IsOpen A := by
    have hEq : e '' S = e.symm ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hzS, hzy⟩
        rw [← hzy]
        simpa [S, π] using hzS
      · intro hy
        refine ⟨e.symm y, hy, ?_⟩
        exact e.apply_symm_apply y
    dsimp [A]
    rw [hEq]
    exact hS_open.preimage e.symm.continuous
  have hB_open : IsOpen B := by
    have hEq : e '' T = e.symm ⁻¹' T := by
      ext y
      constructor
      · rintro ⟨z, hzT, hzy⟩
        rw [← hzy]
        simpa [T, π] using hzT
      · intro hy
        refine ⟨e.symm y, hy, ?_⟩
        exact e.apply_symm_apply y
    dsimp [B]
    rw [hEq]
    exact hT_open.preimage e.symm.continuous
  have hA_pre : IsPreconnected A := by
    dsimp [A]
    exact hS_pre.image e (e.continuous.continuousOn)
  have hB_pre : IsPreconnected B := by
    dsimp [B]
    exact hT_pre.image e (e.continuous.continuousOn)
  have hneAB : (A ∩ B).Nonempty := by
    rcases hneST with ⟨z, hzS, hzT⟩
    refine ⟨e z, ?_, ?_⟩
    · exact mem_image_of_mem e hzS
    · exact mem_image_of_mem e hzT
  have hAB_pre : IsPreconnected (A ∩ B) :=
    preconnected_inter_of_isOpen_interval (s := A) (t := B) hA_open hB_open hA_pre hB_pre hneAB
  have hST_pre : IsPreconnected (S ∩ T) := by
    have hpre_img : IsPreconnected (e '' (S ∩ T)) := by
      have hinter : e '' (S ∩ T) = (e '' S) ∩ (e '' T) := Set.image_inter e.injective
      simpa [A, B, hinter] using hAB_pre
    exact (Topology.IsInducing.isPreconnected_image (f := e) (s := S ∩ T) e.isInducing).1 hpre_img
  have hπST : π '' (S ∩ T) = s ∩ t := by
    ext x
    constructor
    · rintro ⟨z, hzST, hzx⟩
      rw [← hzx]
      simpa [S, T, π] using hzST
    · intro hx
      refine ⟨⟨x, hssub hx.1⟩, ?_, rfl⟩
      constructor
      · simpa [S, π] using hx.1
      · simpa [T, π] using hx.2
  have hπpre : IsPreconnected (π '' (S ∩ T)) := hST_pre.image π (hπ_cont.continuousOn)
  simpa [hπST] using hπpre

end Commons.Topology.ConnectedReal