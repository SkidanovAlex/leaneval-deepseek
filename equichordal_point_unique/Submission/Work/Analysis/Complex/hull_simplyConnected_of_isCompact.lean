import Mathlib
import Submission.Work.SimplyConnected.Plane
import Submission.UnifHelpers

open Set Metric
open scoped Topology Manifold ContDiff

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Analysis.Complex

/-- A nonempty convex subset of `ℂ` is simply connected. -/
theorem isSimplyConnected_of_convex {s : Set ℂ} (hs : Convex ℝ s) (hne : s.Nonempty) :
    IsSimplyConnected s := by
  haveI : ContractibleSpace ↥s := hs.contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible _

/-- A nonempty open ball of `ℂ` is simply connected. -/
theorem isSimplyConnected_ball {c : ℂ} {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (Metric.ball c r) :=
  isSimplyConnected_of_convex (convex_ball c r) ⟨c, by simpa [Metric.mem_ball] using hr⟩

/-- A compact subset of `ℂ` is contained in an open ball. -/
theorem exists_ball_superset_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧ K ⊆ Metric.ball c ρ := by
  rcases hK.isBounded.subset_ball (0 : ℂ) with ⟨ρ, hsub⟩
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨0, 1, one_pos, by simp [h]⟩
  · obtain ⟨x, hx⟩ := hne
    have hx' : x ∈ Metric.ball (0 : ℂ) ρ := hsub hx
    rw [Metric.mem_ball, dist_zero_right] at hx'
    exact ⟨0, ρ, lt_of_le_of_lt (norm_nonneg x) hx', hsub⟩

/-- A nonempty open subset of `ℂ` which is not all of `ℂ` is not compact. -/
theorem not_compactSpace_of_isOpen_ne_univ {W : Set ℂ} (hW : IsOpen W) (hne : W.Nonempty)
    (hlt : W ≠ Set.univ) : ¬ CompactSpace ↥W := by
  intro hc
  have hcomp : IsCompact W := by
    have h1 : IsCompact (Set.univ : Set ↥W) := isCompact_univ
    have h2 := h1.image (continuous_subtype_val : Continuous (Subtype.val : ↥W → ℂ))
    simpa using h2
  have hcl : IsClosed W := hcomp.isClosed
  have := IsClopen.eq_univ (s := W) ⟨hcl, hW⟩ hne
  exact hlt this

/-- The image of a relatively open subset of an open set is open in `ℂ`. -/
theorem isOpen_image_subtype_val {U : Set ℂ} (hU : IsOpen U) {S : Set ↥U} (hS : IsOpen S) :
    IsOpen (Subtype.val '' S) := by
  simpa using hS.trans hU

/-- Simple connectivity transfers across the inclusion of an open set. -/
theorem isSimplyConnected_image_subtype_val {U : Set ℂ} {S : Set ↥U} :
    IsSimplyConnected (Subtype.val '' S) ↔ IsSimplyConnected S :=
  Topology.IsEmbedding.isSimplyConnected_image Topology.IsEmbedding.subtypeVal

theorem hull_simplyConnected_of_isCompact {C W : Set ℂ} (hC : IsCompact C) (hW : IsOpen W) (hWsc : IsSimplyConnected W) (hCW : C ⊆ W) :
    ∃ U : Set ℂ, IsOpen U ∧ C ⊆ U ∧ U ⊆ W ∧ Bornology.IsBounded U ∧ IsSimplyConnected U ∧ U.Nonempty := by
  classical
  rcases C.eq_empty_or_nonempty with h0 | hne
  · -- `C = ∅`: a small ball inside `W`
    subst h0
    obtain ⟨x, hx⟩ := hWsc.nonempty
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hW x hx
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    refine ⟨Metric.ball x (ε / 2), Metric.isOpen_ball, empty_subset _, ?_, ?_, ?_,
      ⟨x, by simp [Metric.mem_ball, hε2]⟩⟩
    · intro y hy
      exact hsub (Metric.ball_subset_ball (by linarith) hy)
    · exact Metric.isBounded_ball
    · exact isSimplyConnected_ball hε2
  · by_cases hWuniv : W = Set.univ
    · -- `W = ℂ`: a large ball
      subst hWuniv
      obtain ⟨c, ρ, hρ, hsub⟩ := exists_ball_superset_of_isCompact hC
      refine ⟨Metric.ball c (ρ + 1), Metric.isOpen_ball, ?_, subset_univ _, ?_, ?_, ?_⟩
      · exact hsub.trans (Metric.ball_subset_ball (by linarith))
      · exact Metric.isBounded_ball
      · exact isSimplyConnected_ball (by linarith)
      · exact ⟨c, by simp [Metric.mem_ball]; linarith⟩
    · -- main case: `W ≠ ℂ`
      let U : TopologicalSpace.Opens ℂ := ⟨W, hW⟩
      haveI hsc : SimplyConnectedSpace ↥U := hWsc
      haveI hLPC : LocallyPathConnectedSpace ↥U := hW.locallyPathConnectedSpace
      haveI hConn : ConnectedSpace ↥U := pathConnectedSpace_iff_connectedSpace.mp inferInstance
      have hnc : ¬ CompactSpace ↥U := by
        intro hc
        have hcomp : IsCompact W := by
          have h1 : IsCompact (Set.univ : Set ↥U) := isCompact_univ
          have h2 := h1.image (continuous_subtype_val : Continuous (Subtype.val : ↥U → ℂ))
          simpa [U] using h2
        have hcl : IsClosed W := hcomp.isClosed
        have := IsClopen.eq_univ (s := W) ⟨hcl, hW⟩ hWsc.nonempty
        exact hWuniv this
      have hhol : Submission.HolomorphicOnX (Subtype.val : ↥U → ℂ) Set.univ := by
        intro x _
        have hev := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) (U := U) (x := x)
        have hpt : (chartAt ℂ ((x : ↥U) : ℂ)) ((x : ↥U) : ℂ) = (chartAt ℂ x) x := rfl
        rw [hpt] at hev
        have hid : (Subtype.val ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 ((chartAt ℂ x) x)]
            (↑(OpenPartialHomeomorph.refl ℂ) : ℂ → ℂ) := by
          simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm] using hev.symm
        exact (analyticAt_id (z := (chartAt ℂ x) x)).congr hid.symm
      -- compactness of the preimage of `C` in `↥U`
      have hKc : IsCompact (Subtype.val ⁻¹' C : Set ↥U) :=
        (Topology.IsInducing.isCompact_preimage_iff (Topology.IsInducing.subtypeVal (t := W))
          (by simpa [U] using hCW)).mpr (by simpa [U] using hC)
      rcases Work.SC.uniformization_of_simplyConnected_of_injective_into_plane (X := ↥U) hnc hhol
        Subtype.val_injective with hcase | hcase
      · -- target `ℂ` --------------------------------------------------------
        obtain ⟨e⟩ := hcase
        obtain ⟨c, ρ, hρ, hsub⟩ := exists_ball_superset_of_isCompact (hKc.image e.continuous)
        refine ⟨Subtype.val '' (e.symm '' Metric.ball c ρ), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact isOpen_image_subtype_val hW (e.toHomeomorph.symm.isOpenMap _ Metric.isOpen_ball)
        · rintro z hz
          have hzU : z ∈ U := hCW hz
          refine ⟨⟨z, hzU⟩, ⟨e ⟨z, hzU⟩, hsub ⟨⟨z, hzU⟩, hz, rfl⟩, ?_⟩, rfl⟩
          exact e.symm_apply_apply ⟨z, hzU⟩
        · rintro z ⟨x, -, rfl⟩
          exact x.2
        · have h1 : Bornology.IsBounded ((Subtype.val ∘ e.symm) '' Metric.closedBall c ρ) :=
            ((isCompact_closedBall c ρ).image
              (continuous_subtype_val.comp e.symm.continuous)).isBounded
          refine h1.subset ?_
          rintro z ⟨x, ⟨s, hs, rfl⟩, rfl⟩
          exact ⟨s, Metric.ball_subset_closedBall hs, rfl⟩
        · have h1 : IsSimplyConnected (e.symm '' Metric.ball c ρ) := by
            simpa using (Homeomorph.isSimplyConnected_image e.toHomeomorph.symm (s := Metric.ball c ρ)).mpr
              (isSimplyConnected_ball hρ)
          rw [isSimplyConnected_image_subtype_val]
          exact h1
        · exact ⟨Subtype.val (e.symm c), ⟨e.symm c, ⟨c, by simp [Metric.mem_ball, hρ], rfl⟩, rfl⟩⟩
      · -- target `UpperHalfPlane` ----------------------------------------
        obtain ⟨e⟩ := hcase
        obtain ⟨d⟩ := Submission.Helpers.upperHalfPlane_equiv_openSubset
        set e' : ↥U ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯
            Submission.Helpers.HPlaneOpen := e.trans d with he'def
        -- the compact image in the open upper half plane, viewed in `ℂ`
        have himg : IsCompact (Subtype.val '' (e' '' (Subtype.val ⁻¹' C : Set ↥U))) :=
          (hKc.image e'.continuous).image continuous_subtype_val
        have hneimg : (Subtype.val '' (e' '' (Subtype.val ⁻¹' C : Set ↥U))).Nonempty := by
          obtain ⟨z₀, hz₀⟩ := hne
          exact ⟨_, ⟨e' ⟨z₀, hCW hz₀⟩, ⟨_, hz₀, rfl⟩, rfl⟩⟩
        -- a level and a radius in `ℂ`
        obtain ⟨t, ht, htim⟩ : ∃ t : ℝ, 0 < t ∧
            ∀ z : ℂ, z ∈ Subtype.val '' (e' '' (Subtype.val ⁻¹' C : Set ↥U)) → t < z.im := by
          obtain ⟨w, hw, hmin⟩ := himg.exists_isMinOn hneimg Complex.continuous_im.continuousOn
          have hpos : 0 < w.im := by
            obtain ⟨y, hy, rfl⟩ := hw
            obtain ⟨u, -, rfl⟩ := hy
            exact (e' u).2
          refine ⟨w.im / 2, half_pos hpos, fun z hz => ?_⟩
          have hle : w.im ≤ z.im := hmin hz
          linarith
        obtain ⟨c₀, ρ, hρ, hrad₀⟩ := exists_ball_superset_of_isCompact himg
        have hrad : ∀ z : ℂ, z ∈ Subtype.val '' (e' '' (Subtype.val ⁻¹' C : Set ↥U)) →
            z ∈ Metric.ball c₀ ρ := fun z hz => hrad₀ hz
        set S : Set ℂ := {z : ℂ | t < z.im} ∩ Metric.ball c₀ ρ with hSdef
        set Sc : Set ℂ := {z : ℂ | t ≤ z.im} ∩ Metric.closedBall c₀ ρ with hScdef
        have hSsub : S ⊆ (Submission.Helpers.HPlaneOpen : Set ℂ) := by
          intro z hz
          rw [hSdef] at hz
          have hz1 : t < z.im := hz.1
          have : 0 < z.im := lt_trans ht hz1
          simpa [Submission.Helpers.HPlaneOpen, UpperHalfPlane.upperHalfPlaneSet] using this
        have hScsub : Sc ⊆ (Submission.Helpers.HPlaneOpen : Set ℂ) := by
          intro z hz
          rw [hScdef] at hz
          have : 0 < z.im := lt_of_lt_of_le ht hz.1
          simpa [Submission.Helpers.HPlaneOpen, UpperHalfPlane.upperHalfPlaneSet] using this
        set V : Set ↥Submission.Helpers.HPlaneOpen :=
          {w | ((w : Submission.Helpers.HPlaneOpen) : ℂ) ∈ S} with hVdef
        set Vc : Set ↥Submission.Helpers.HPlaneOpen :=
          {w | ((w : Submission.Helpers.HPlaneOpen) : ℂ) ∈ Sc} with hVcdef
        have hVeq : (Subtype.val '' V : Set ℂ) = S := by
          ext z
          constructor
          · rintro ⟨w, hw, rfl⟩
            exact hw
          · intro hz
            exact ⟨⟨z, hSsub hz⟩, hz, rfl⟩
        have hVceq : (Subtype.val '' Vc : Set ℂ) = Sc := by
          ext z
          constructor
          · rintro ⟨w, hw, rfl⟩
            exact hw
          · intro hz
            exact ⟨⟨z, hScsub hz⟩, hz, rfl⟩
        have hVsubVc : V ⊆ Vc := by
          intro w hw
          rw [hVdef] at hw
          rw [hVcdef]
          exact ⟨le_of_lt (show t < ((w : Submission.Helpers.HPlaneOpen) : ℂ).im from hw.1),
            Metric.ball_subset_closedBall hw.2⟩
        have hKsubS : e' '' (Subtype.val ⁻¹' C : Set ↥U) ⊆ V := by
          rintro v ⟨y, hy, rfl⟩
          rw [hVdef, hSdef]
          exact ⟨htim _ ⟨e' y, ⟨y, hy, rfl⟩, rfl⟩, hrad _ ⟨e' y, ⟨y, hy, rfl⟩, rfl⟩⟩
        refine ⟨Subtype.val '' (e'.symm '' V), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- open
          refine isOpen_image_subtype_val hW (e'.toHomeomorph.symm.isOpenMap _ ?_)
          rw [hVdef, hSdef]
          exact ((isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball).preimage
            continuous_subtype_val
        · -- `C ⊆ U`
          rintro z hz
          have hzU : z ∈ U := hCW hz
          refine ⟨⟨z, hzU⟩, ⟨e' ⟨z, hzU⟩, hKsubS ⟨⟨z, hzU⟩, hz, rfl⟩, ?_⟩, rfl⟩
          exact e'.symm_apply_apply ⟨z, hzU⟩
        · rintro z ⟨x, -, rfl⟩
          exact x.2
        · -- bounded
          have hSccomp : IsCompact Sc := by
            rw [hScdef]
            exact Metric.isCompact_iff_isClosed_bounded.mpr
              ⟨(isClosed_le continuous_const Complex.continuous_im).inter Metric.isClosed_closedBall,
                Bornology.IsBounded.subset Metric.isBounded_closedBall (fun z hz => hz.2)⟩
          have hVccomp : IsCompact Vc := by
            rw [Topology.IsEmbedding.isCompact_iff
              (f := (Subtype.val : ↥Submission.Helpers.HPlaneOpen → ℂ))
              Topology.IsEmbedding.subtypeVal, hVceq]
            exact hSccomp
          have h1 : Bornology.IsBounded ((Subtype.val ∘ e'.symm) '' Vc) :=
            (hVccomp.image (continuous_subtype_val.comp e'.symm.continuous)).isBounded
          refine h1.subset ?_
          rintro z ⟨x, ⟨v, hv, rfl⟩, rfl⟩
          exact ⟨v, hVsubVc hv, rfl⟩
        · -- simple connectivity: the image of `V` is convex
          have hst : Convex ℝ {z : ℂ | t < z.im} := convex_halfSpace_im_gt t
          have hconvS : Convex ℝ S := by
            rw [hSdef]
            exact hst.inter (convex_ball c₀ ρ)
          have hne2 : (Subtype.val '' V : Set ℂ).Nonempty := by
            obtain ⟨z, hz⟩ := hneimg
            exact ⟨z, by rw [hVeq]; exact ⟨htim z hz, hrad z hz⟩⟩
          have h2 : IsSimplyConnected (Subtype.val '' V : Set ℂ) :=
            isSimplyConnected_of_convex (by rw [hVeq]; exact hconvS) hne2
          have h1 : IsSimplyConnected V := isSimplyConnected_image_subtype_val.mp h2
          have h3 : IsSimplyConnected (e'.symm '' V) := by
            simpa using (Homeomorph.isSimplyConnected_image e'.toHomeomorph.symm (s := V)).mpr h1
          rw [isSimplyConnected_image_subtype_val]
          exact h3
        · -- nonempty
          obtain ⟨y₀, hy₀⟩ := hne
          refine ⟨Subtype.val (e'.symm (e' ⟨y₀, hCW hy₀⟩)), ?_⟩
          exact ⟨e'.symm (e' ⟨y₀, hCW hy₀⟩),
            ⟨e' ⟨y₀, hCW hy₀⟩, hKsubS ⟨⟨y₀, hCW hy₀⟩, hy₀, rfl⟩, rfl⟩, rfl⟩

end Work.Analysis.Complex
