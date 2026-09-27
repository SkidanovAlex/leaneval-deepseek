import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Sheet
import Submission.Work.EQ.UnivCover.Topology
import Submission.Work.EQ.UnivCover.UC_segPt_mem_sheet

/-!
# The universal cover is path connected

The initial-segment points `UC.segPt γ t` give a continuous path from the base point to the class
of `γ`; hence the universal cover of a path connected space is path connected.
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology
open Work.EQ.UnivCover

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- **The universal cover is path connected.** -/
theorem UC_pathConnectedSpace [PathConnectedSpace X] (hB : HasDiscBasis X) :
    PathConnectedSpace (UC x₀) := by
  -- A general extensionality for the (dependent) pairs forming the cover.
  have ext_cast : ∀ {e₁ e₂ : UC x₀} (h : e₁.pt = e₂.pt),
      e₁.cls.cast rfl h.symm = e₂.cls → e₁ = e₂ := by
    rintro ⟨p₁, c₁⟩ ⟨p₂, c₂⟩ h hc
    rw [UC.mk.injEq]
    exact ⟨h, (Path.Homotopic.Quotient.cast_heq rfl h.symm).symm.trans (heq_of_eq hc)⟩
  -- the segment map is continuous
  have hcont : ∀ {x : X} (γ : Path x₀ x), Continuous (UC.segPt (γ := γ)) := by
    intro x γ
    rw [(UC_isTopologicalBasis_basis (x₀ := x₀) hB).continuous_iff]
    rintro S ⟨e, V, hV, heV, rfl⟩
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have htV : γ t ∈ V := ht.1
    obtain ⟨W, hW, htW, hWV⟩ := hB (γ t) V hV.isOpen htV
    have hmem : γ ⁻¹' W ∈ 𝓝 t :=
      γ.continuous.continuousAt.preimage_mem_nhds (hW.isOpen.mem_nhds htW)
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hmem
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hε) fun u hu => ?_
    have hsub : Set.uIcc t u ⊆ γ ⁻¹' W := by
      intro v hv
      have hdist : dist v t ≤ dist u t := by
        rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
        rcases le_total t u with htu | hut
        · have h1 : t ≤ v := by
            have h := hv.1
            rwa [min_eq_left htu] at h
          have h2 : v ≤ u := by
            have h := hv.2
            rwa [max_eq_right htu] at h
          have h1' : (t : ℝ) ≤ (v : ℝ) := by exact_mod_cast h1
          have h2' : (v : ℝ) ≤ (u : ℝ) := by exact_mod_cast h2
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · have h1 : u ≤ v := by
            have h := hv.1
            rwa [min_eq_right hut] at h
          have h2 : v ≤ t := by
            have h := hv.2
            rwa [max_eq_left hut] at h
          have h1' : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast h1
          have h2' : (v : ℝ) ≤ (t : ℝ) := by exact_mod_cast h2
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
      exact hεW (lt_of_le_of_lt hdist hu)
    exact UC_sheet_trans ht (UC_segPt_mem_sheet γ t u hsub) hWV
  -- the initial and final points of the segment path
  have hend0 : ∀ {x : X} (γ : Path x₀ x), UC.segPt γ 0 = UC.base x₀ := by
    intro x γ
    refine ext_cast γ.source ?_
    change (Path.Homotopic.Quotient.mk (segTo γ 0)).cast rfl γ.source.symm
      = Path.Homotopic.Quotient.refl x₀
    have hpath : (segTo γ 0).cast rfl γ.source.symm = Path.refl x₀ := by
      ext s
      change γ (s * (0 : unitInterval)) = x₀
      rw [show s * (0 : unitInterval) = 0 from Subtype.ext (by simp)]
      exact γ.source
    rw [← Path.Homotopic.Quotient.mk_cast, hpath, Path.Homotopic.Quotient.mk_refl]
  have hend1 : ∀ {x : X} (γ : Path x₀ x),
      UC.segPt γ 1 = (⟨x, Path.Homotopic.Quotient.mk γ⟩ : UC x₀) := by
    intro x γ
    refine ext_cast γ.target ?_
    change (Path.Homotopic.Quotient.mk (segTo γ 1)).cast rfl γ.target.symm
      = Path.Homotopic.Quotient.mk γ
    have hpath : (segTo γ 1).cast rfl γ.target.symm = γ := by
      ext s
      change γ (s * (1 : unitInterval)) = γ s
      rw [show s * (1 : unitInterval) = s from Subtype.ext (by simp)]
    rw [← Path.Homotopic.Quotient.mk_cast, hpath]
  -- every point is joined to the base point
  have hjoined : ∀ e : UC x₀, Joined (UC.base x₀) e := by
    rintro ⟨x, q⟩
    obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective q
    refine ⟨⟨⟨fun t => UC.segPt γ t, hcont γ⟩, hend0 γ, ?_⟩⟩
    show UC.segPt γ 1 = (⟨x, q⟩ : UC x₀)
    rw [hend1 γ, hγ]
  exact ⟨⟨UC.base x₀⟩, fun e₁ e₂ => (hjoined e₁).symm.trans (hjoined e₂)⟩

end Work.EQ.UnivCover
