import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.CompletePartialOrder

open Set Metric
open scoped Topology

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.Topology.Plane

noncomputable section

/-! ### Auxiliary topology: boundary bumping

We need the classical *boundary bumping theorem* in the following form: if `L` is a continuum
in `ℂ`, `A ⊆ L` is closed, nonempty and proper, and `x ∈ A`, then the connected component of `x`
in `A` meets the frontier of `A`.  The proof goes through the fact that in a compact Hausdorff
space connected components are quasi-components (intersections of clopen sets). -/

/-- Auxiliary form of boundary bumping: in a compact Hausdorff space, if the connected component
of `x` in a closed set `A` is contained in the interior of `A`, then there is a clopen set `W`
with `x ∈ W ⊆ interior A`. -/
theorem exists_isClopen_subset_interior {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {A : Set X} (hA : IsClosed A) {x : X} (hx : x ∈ A)
    (hsub : connectedComponentIn A x ⊆ interior A) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ W ⊆ interior A := by
  classical
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  set U : Set A := Subtype.val ⁻¹' (interior A) with hU
  have hUopen : IsOpen U := isOpen_interior.preimage continuous_subtype_val
  set xA : A := ⟨x, hx⟩ with hxA
  have hCsub : connectedComponent xA ⊆ U := by
    intro y hy
    show (y : X) ∈ interior A
    apply hsub
    rw [connectedComponentIn_eq_image hx]
    exact ⟨y, hy, rfl⟩
  set F : {Z : Set A // IsClopen Z ∧ xA ∈ Z} → Set A := fun Z => (Z : Set A) \ U with hF
  have hFclosed : ∀ Z, IsClosed (F Z) := fun Z => Z.2.1.1.sdiff hUopen
  have hFempty : (⋂ Z, F Z) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    have hyU : y ∉ U := (Set.mem_iInter.mp hy ⟨univ, isClopen_univ, mem_univ xA⟩).2
    have hyC : y ∈ connectedComponent xA := by
      rw [connectedComponent_eq_iInter_isClopen xA]
      exact Set.mem_iInter.mpr fun Z => (Set.mem_iInter.mp hy Z).1
    exact hyU (hCsub hyC)
  have hst : (univ ∩ ⋂ Z, F Z) = ∅ := by rw [hFempty, inter_empty]
  obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed F hFclosed
    (Set.disjoint_iff_inter_eq_empty.mpr hst)
  replace hu := Set.disjoint_iff_inter_eq_empty.mp hu
  have hu' : (⋂ Z ∈ u, F Z) = ∅ := by simpa using hu
  refine ⟨Subtype.val '' (⋂ Z ∈ u, (Z : Set A)), ?_, ?_, ?_⟩
  · have hcl : IsClopen (⋂ Z ∈ u, (Z : Set A)) :=
      u.finite_toSet.isClopen_biInter (fun Z _ => Z.2.1)
    refine ⟨?_, ?_⟩
    · obtain ⟨Fs, hFs, hFW⟩ := isClosed_induced_iff.mp hcl.1
      rw [show Subtype.val '' (⋂ Z ∈ u, (Z : Set A)) = Fs ∩ A by
        rw [← hFW, Subtype.image_preimage_coe, inter_comm]]
      exact hFs.inter hA
    · obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hcl.2
      have hWint : Subtype.val '' (⋂ Z ∈ u, (Z : Set A)) ⊆ interior A := by
        rintro y ⟨z, hz, rfl⟩
        by_contra hzc
        have hmem : z ∈ (⋂ Z ∈ u, F Z) :=
          Set.mem_iInter₂.mpr (fun Z hZ => ⟨Set.mem_iInter₂.mp hz Z hZ, hzc⟩)
        rw [hu'] at hmem
        exact hmem
      have hOA : O ∩ A = Subtype.val '' (⋂ Z ∈ u, (Z : Set A)) := by
        rw [← hOW, Subtype.image_preimage_coe, inter_comm]
      have hWsub' : O ∩ A ⊆ interior A := by rw [hOA]; exact hWint
      rw [show Subtype.val '' (⋂ Z ∈ u, (Z : Set A)) = O ∩ interior A by
        rw [← hOA]
        exact Set.Subset.antisymm (fun z hz => ⟨hz.1, hWsub' hz⟩)
          (fun z hz => ⟨hz.1, interior_subset hz.2⟩)]
      exact hO.inter isOpen_interior
  · exact ⟨xA, Set.mem_iInter₂.mpr (fun Z _ => Z.2.2), rfl⟩
  · rintro y ⟨z, hz, rfl⟩
    by_contra hzc
    have hmem : z ∈ (⋂ Z ∈ u, F Z) :=
      Set.mem_iInter₂.mpr (fun Z hZ => ⟨Set.mem_iInter₂.mp hz Z hZ, hzc⟩)
    rw [hu'] at hmem
    exact hmem

/-- **Boundary bumping (closed version).** In a compact connected Hausdorff space, a component of
a proper nonempty closed set meets the frontier of that set. -/
theorem boundary_bumping_closed_abs {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ConnectedSpace X] {A : Set X} (hA : IsClosed A) (_hAne : A.Nonempty) (hAne' : A ≠ univ)
    {x : X} (hx : x ∈ A) :
    (connectedComponentIn A x ∩ frontier A).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hsub : connectedComponentIn A x ⊆ interior A := by
    intro y hy
    rw [interior_eq_compl_closure_compl, Set.mem_compl_iff]
    intro hycl
    have hmem : y ∈ connectedComponentIn A x ∩ frontier A := by
      refine ⟨hy, ?_⟩
      rw [frontier_eq_closure_inter_closure, hA.closure_eq]
      exact ⟨connectedComponentIn_subset A x hy, hycl⟩
    rw [hempty] at hmem
    exact hmem
  obtain ⟨W, hWcl, hxW, hWsub⟩ := exists_isClopen_subset_interior hA hx hsub
  have hWne : W ≠ ∅ := fun h => by rw [h] at hxW; exact Set.notMem_empty x hxW
  have hWnu : W ≠ univ := by
    intro h
    have h1 : (univ : Set X) ⊆ A := by
      rw [← h]
      exact hWsub.trans interior_subset
    exact hAne' (eq_univ_of_univ_subset h1)
  rcases isClopen_iff.mp hWcl with h | h
  · exact hWne h
  · exact hWnu h

/-! ### The disk model of the one-point compactification -/

/-- The disk-model map `z ↦ z / (1 + ‖z‖)`, a homeomorphism `ℂ ≃ ball 0 1`. -/
noncomputable def demb (z : ℂ) : ℂ := z / (((1 : ℝ) + ‖z‖ : ℝ) : ℂ)

/-- The inverse of `demb` on the open unit disk: `w ↦ w / (1 - ‖w‖)`. -/
noncomputable def dembInv (w : ℂ) : ℂ := w / (((1 : ℝ) - ‖w‖ : ℝ) : ℂ)

lemma norm_ofReal_eq_abs' (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

lemma demb_norm (z : ℂ) : ‖demb z‖ = ‖z‖ / (1 + ‖z‖) := by
  rw [demb, norm_div, norm_ofReal_eq_abs', abs_of_nonneg (by positivity)]

lemma demb_norm_lt_one (z : ℂ) : ‖demb z‖ < 1 := by
  rw [demb_norm, div_lt_one (by positivity)]
  linarith [norm_nonneg z]

lemma demb_zero : demb (0 : ℂ) = 0 := by simp [demb]

lemma dembInv_zero : dembInv (0 : ℂ) = 0 := by simp [dembInv]

lemma norm_dembInv {w : ℂ} (hw : ‖w‖ < 1) : ‖dembInv w‖ = ‖w‖ / (1 - ‖w‖) := by
  rw [dembInv, norm_div, norm_ofReal_eq_abs', abs_of_nonneg (by linarith)]

lemma dembInv_demb (z : ℂ) : dembInv (demb z) = z := by
  have hne : (1 + ‖z‖ : ℝ) ≠ 0 := by positivity
  rw [dembInv, demb_norm]
  have h1 : (1 - ‖z‖ / (1 + ‖z‖) : ℝ) = 1 / (1 + ‖z‖) := by
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]; ring
  rw [h1, demb]
  have h2 : (((1 : ℝ) + ‖z‖ : ℝ) : ℂ) * (((1 / (1 + ‖z‖) : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div, mul_inv_cancel₀ hne]; simp
  rw [div_div, h2, div_one]

lemma demb_dembInv {w : ℂ} (hw : ‖w‖ < 1) : demb (dembInv w) = w := by
  have hne : (1 - ‖w‖ : ℝ) ≠ 0 := by linarith
  have hnorm : ‖dembInv w‖ = ‖w‖ / (1 - ‖w‖) := norm_dembInv hw
  rw [demb, hnorm]
  have h1 : (1 + ‖w‖ / (1 - ‖w‖) : ℝ) = 1 / (1 - ‖w‖) := by
    rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]; ring
  rw [h1, dembInv]
  have h2 : (((1 : ℝ) - ‖w‖ : ℝ) : ℂ) * (((1 / (1 - ‖w‖) : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, one_div, mul_inv_cancel₀ hne]; simp
  rw [div_div, h2, div_one]

lemma continuous_demb : Continuous demb := by
  unfold demb
  refine Continuous.div₀ continuous_id ?_ ?_
  · exact Complex.continuous_ofReal.comp (continuous_const.add continuous_norm)
  · intro z
    exact_mod_cast (by positivity : (1 + ‖z‖ : ℝ) ≠ 0)

lemma continuousOn_dembInv : ContinuousOn dembInv (Metric.ball (0 : ℂ) 1) := by
  unfold dembInv
  refine ContinuousOn.div₀ continuousOn_id ?_ ?_
  · exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_norm)).continuousOn
  · intro w hw
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
    exact_mod_cast (by linarith : (1 - ‖w‖ : ℝ) ≠ 0)

/-! ### The transport step -/

/-- **Disk-model pullback (compact form), a form of the boundary bumping theorem:** if `K ⊆ ℂ` is
closed, `0 < ρ < 1`, and `L ⊆ ℂ` is a compact preconnected set containing `0`, contained in
`(fun z => z / (1 + ‖z‖)) '' K ∪ {w | ‖w‖ = 1}` (the image of `K` in the disk model of the
one-point compactification of `ℂ`, together with the "circle at infinity"), and meeting the circle
of radius `ρ`, then the connected component of `0` in `K` meets the circle of radius
`ρ / (1 - ρ)`. -/
theorem disk_model_pullback_compact {K : Set ℂ} (hK : IsClosed K) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) {L : Set ℂ} (hLpc : IsPreconnected L) (hLc : IsCompact L) (h0L : (0 : ℂ) ∈ L)
    (hsub : L ⊆ (fun z : ℂ => z / (((1 : ℝ) + ‖z‖ : ℝ) : ℂ)) '' K ∪ Metric.sphere (0 : ℂ) 1)
    (hmeet : (L ∩ Metric.sphere (0 : ℂ) ρ).Nonempty) :
    ∃ z : ℂ, ‖z‖ = ρ / (1 - ρ) ∧ z ∈ connectedComponentIn K (0 : ℂ) := by
  classical
  have hsub' : L ⊆ demb '' K ∪ Metric.sphere (0 : ℂ) 1 := hsub
  set A : Set ℂ := L ∩ Metric.closedBall (0 : ℂ) ρ with hAdef
  have hAclosed : IsClosed A := hLc.isClosed.inter Metric.isClosed_closedBall
  have hAsub : A ⊆ L := inter_subset_left
  have hAball : A ⊆ Metric.ball (0 : ℂ) 1 := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖w‖ ≤ ρ := by
      have := hw.2; rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    linarith
  have h0A : (0 : ℂ) ∈ A :=
    ⟨h0L, by rw [Metric.mem_closedBall, dist_zero_right]; simpa using hρ.le⟩
  haveI : CompactSpace ↥L := isCompact_iff_compactSpace.mp hLc
  haveI : ConnectedSpace ↥L := isConnected_iff_connectedSpace.mp ⟨⟨0, h0L⟩, hLpc⟩
  set A' : Set ↥L := Subtype.val ⁻¹' A with hA'set
  have hA'closed : IsClosed A' := hAclosed.preimage continuous_subtype_val
  have hxA' : (⟨0, h0L⟩ : ↥L) ∈ A' := h0A
  set P' : Set ℂ := Subtype.val '' (connectedComponentIn A' (⟨0, h0L⟩ : ↥L)) with hP'def
  have hP'sub : P' ⊆ A := by
    rintro y ⟨z, hz, rfl⟩
    exact connectedComponentIn_subset A' _ hz
  have hP'pc : IsPreconnected P' :=
    isPreconnected_connectedComponentIn.image Subtype.val continuous_subtype_val.continuousOn
  have h0P' : (0 : ℂ) ∈ P' := ⟨⟨0, h0L⟩, mem_connectedComponentIn hxA', rfl⟩
  -- find a point of `P'` on the circle of radius `ρ`
  have hkey : ∃ p ∈ P', ‖p‖ = ρ := by
    rcases eq_or_ne A L with hAL | hAL
    · -- `A = L`: then `P'` is all of `L`
      have hA'univ : A' = univ := by
        rw [hA'set, hAL]
        exact Set.eq_univ_of_forall (fun z => z.2)
      have hcomp : connectedComponentIn A' (⟨0, h0L⟩ : ↥L) = univ := by
        rw [hA'univ, connectedComponentIn_univ]
        exact PreconnectedSpace.connectedComponent_eq_univ _
      obtain ⟨p, hpL, hpS⟩ := hmeet
      rw [Metric.mem_sphere, dist_zero_right] at hpS
      exact ⟨p, by rw [hP'def, hcomp]; exact ⟨⟨p, hpL⟩, trivial, rfl⟩, hpS⟩
    · -- `A ≠ L`: use boundary bumping
      have hA'ne : A' ≠ univ := by
        intro h
        apply hAL
        refine Set.Subset.antisymm hAsub (fun z hzL => ?_)
        have hz : (⟨z, hzL⟩ : ↥L) ∈ A' := by rw [h]; trivial
        exact hz
      obtain ⟨z', hz'⟩ :=
        boundary_bumping_closed_abs hA'closed ⟨⟨0, h0L⟩, hxA'⟩ hA'ne hxA'
      obtain ⟨hz'C, hz'fr⟩ := hz'
      have hz'A : (z' : ℂ) ∈ A := connectedComponentIn_subset A' _ hz'C
      have hle : ‖(z' : ℂ)‖ ≤ ρ := by
        have := hz'A.2; rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
      have hge : ρ ≤ ‖(z' : ℂ)‖ := by
        have h2 : z' ∈ closure (A'ᶜ) := by
          have h := hz'fr
          rw [frontier_eq_closure_inter_closure] at h
          exact h.2
        have h4 : (z' : ℂ) ∈ Subtype.val '' closure (A'ᶜ) := ⟨z', h2, rfl⟩
        have h5 : Subtype.val '' (A'ᶜ) = L \ A := by
          ext y
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨z.2, fun h => hz h⟩
          · rintro ⟨hyL, hyA⟩
            exact ⟨⟨y, hyL⟩, (fun h => hyA h), rfl⟩
        have h6 : Subtype.val '' closure (A'ᶜ) ⊆ closure (Subtype.val '' A'ᶜ) :=
          image_closure_subset_closure_image continuous_subtype_val
        rw [h5] at h6
        have hcl : (z' : ℂ) ∈ closure (L \ A) := h6 h4
        have hLsub : L \ A ⊆ {w : ℂ | ρ ≤ ‖w‖} := by
          intro w hw
          have hwL : w ∈ L := hw.1
          have hwA : w ∉ Metric.closedBall (0 : ℂ) ρ := fun h => hw.2 ⟨hwL, h⟩
          rw [Metric.mem_closedBall, dist_zero_right, not_le] at hwA
          exact hwA.le
        exact closure_minimal hLsub (isClosed_Ici.preimage continuous_norm) hcl
      exact ⟨(z' : ℂ), ⟨z', hz'C, rfl⟩, le_antisymm hle hge⟩
  obtain ⟨p, hpP', hpρ⟩ := hkey
  refine ⟨dembInv p, ?_, ?_⟩
  · rw [norm_dembInv (by have := hAball (hP'sub hpP'); rwa [Metric.mem_ball, dist_zero_right] at this),
      hpρ]
  · have hWK : dembInv '' P' ⊆ K := by
      rintro u ⟨w, hw, rfl⟩
      have hwf : w ∈ demb '' K ∪ Metric.sphere (0 : ℂ) 1 := hsub' (hAsub (hP'sub hw))
      rcases hwf with hf | hs
      · obtain ⟨z, hzK, rfl⟩ := hf
        rwa [dembInv_demb]
      · rw [Metric.mem_sphere, dist_zero_right] at hs
        have hb := hAball (hP'sub hw)
        rw [Metric.mem_ball, dist_zero_right] at hb
        linarith
    have hWpc : IsPreconnected (dembInv '' P') :=
      hP'pc.image dembInv
        (continuousOn_dembInv.mono (fun w hw => hAball (hP'sub hw)))
    have h0W : (0 : ℂ) ∈ dembInv '' P' := ⟨0, h0P', by rw [dembInv_zero]⟩
    exact (hWpc.subset_connectedComponentIn h0W hWK) ⟨p, hpP', rfl⟩

end

end Commons.Topology.Plane