import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.HornCov.isCoveringMapOn_of_sections
import Submission.Work.HornCov.deriv_varphi_ne_zero_of_notMem_critOrbit
import Submission.Work.HornVarphi.isLocalHomeomorphOn_of_deriv_ne_zero
import Submission.Work.HornVarphi.exists_ball_subset_diff_critOrbit

/-!
# `sheet_varphi`: `φ` is a covering over a ball off the postcritical set

`Work.HornCov.sheet_varphi` — the "one sheet" form of Shishikura's Claim B: if `z ∈ B` is not on
the forward critical orbit then a whole ball `ball z r ⊆ B` around `z` is evenly covered by
`φ` restricted to each of the two components `B̃ᵘ, B̃ˡ = BuOf d B, BlOf d B` of `φ⁻¹(B)`.

Route.
* `exists_ball_subset_diff_critOrbit` produces `r₀ > 0` with `ball z r₀ ⊆ B` and
  `ball z r₀ ∩ critOrbit = ∅`; `HornVarphiStatement` produces `r₁ > 0` with `ball z r₁ ⊆ B`
  together with holomorphic local sections of `φ` over `ball z r₁` through every point of
  `BuOf ∪ BlOf` that maps into the ball.
* The radius `r = min r₀ r₁` works: the local homeomorphism `IsLocalHomeomorphOn` for
  `φ|BuOf` and `φ|BlOf` on the preimage of `ball z r` comes from the inverse function theorem
  (`isLocalHomeomorphOn_of_deriv_ne_zero`) fed by `deriv φ w ≠ 0` off `φ⁻¹(critOrbit)`
  (`deriv_varphi_ne_zero_of_notMem_critOrbit`).
* Sections: given `x ∈ BuOf` over the ball, the section `σ` supplied by `HornVarphiStatement`
  maps the (preconnected) ball into `BuOf ∪ BlOf` and meets `BuOf` (at `σ (φ x) = x`), while
  `BuOf, BlOf` are disjoint open sets, so `σ '' ball ⊆ BuOf` (`image_subset_left_of_section`).
* Finally `isCoveringMapOn_of_sections` converts "local homeomorphism + a continuous section
  through every point of the preimage" into `IsCoveringMapOn` over the preconnected base.

The statement is unchanged from the version requested by the HORN assembly.
-/

namespace Work.HornCov

open Set Topology
open MandelDim

/-- A preconnected set which is contained in the union of two disjoint open sets and meets the
first of them lies in the first. -/
theorem preconnected_subset_left_of_subset_union {C C' s : Set ℂ} (hC : IsOpen C) (hC' : IsOpen C')
    (hdisj : Disjoint C C') (hconn : IsPreconnected s) (hsub : s ⊆ C ∪ C')
    (hmeet : (s ∩ C).Nonempty) : s ⊆ C := by
  rcases hconn.subset_or_subset hC hC' hdisj hsub with h | h
  · exact h
  · obtain ⟨x, ⟨xs, xC⟩⟩ := hmeet
    exact absurd (h xs) (Set.disjoint_left.mp hdisj xC)

/-- If `φ` has a continuous section `σ` over a preconnected `S`, `σ` maps `S` into `C ∪ C'` with
`C, C'` disjoint open, and `σ (φ w) = w` for a point `w ∈ C` with `φ w ∈ S`, then `σ` maps `S`
into `C` — the sheet of a section through a point of `C` stays in `C`. -/
theorem image_subset_left_of_section {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {C C' : Set ℂ} (hCopen : IsOpen C) (hC'open : IsOpen C') (hdisj : Disjoint C C')
    {S : Set ℂ} (hSconn : IsPreconnected S) {w : ℂ} (hw : w ∈ C) (hwS : d.φ w ∈ S)
    {σ : ℂ → ℂ} (hσmaps : MapsTo σ S (C ∪ C'))
    (hσcont : ContinuousOn σ S) (hσw : σ (d.φ w) = w) :
    σ '' S ⊆ C := by
  refine preconnected_subset_left_of_subset_union hCopen hC'open hdisj (hSconn.image σ hσcont) ?_ ?_
  · rw [Set.image_subset_iff]; intro u hu; exact hσmaps hu
  · exact ⟨σ (d.φ w), ⟨⟨d.φ w, hwS, rfl⟩, by rw [hσw]; exact hw⟩⟩

/-- `φ` is a local homeomorphism on the part of an open `U ⊆ BuOf ∪ BlOf` lying over a set `S`
which avoids the critical orbit.  (Consequence of the inverse function theorem applied to
`deriv φ w ≠ 0`, `deriv_varphi_ne_zero_of_notMem_critOrbit`.) -/
theorem isLocalHomeomorphOn_varphi_of_open_subset {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hTopo : MandelDim.HornTopoStatement) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) {U : Set ℂ} (hUopen : IsOpen U)
    (hU : U ⊆ MandelDim.BuOf d B ∪ MandelDim.BlOf d B) {S : Set ℂ}
    (hScrit : Disjoint S (MandelDim.critOrbit f₀ c)) :
    IsLocalHomeomorphOn (fun w : ↥U => d.φ w) ((fun w : ↥U => d.φ w) ⁻¹' S) := by
  obtain ⟨-, -, -, -, -, -, hsubDE⟩ := hTopo f₀ D₀ B c d hsetup
  have hUφ : U ⊆ d.Dφ := fun w hw => (hsubDE (hU hw)).1
  have hdiff : DifferentiableOn ℂ d.φ U := d.φ_holo.mono hUφ
  refine (Work.HornVarphi.isLocalHomeomorphOn_of_deriv_ne_zero hUopen hdiff
    {z : ℂ | d.φ z ∈ MandelDim.critOrbit f₀ c} ?_).mono ?_
  · intro z hz hznc
    exact deriv_varphi_ne_zero_of_notMem_critOrbit hTopo d hsetup (hU hz) hznc
  · intro z hz hmem
    exact Set.disjoint_left.mp hScrit hz hmem

theorem sheet_varphi (hTopo : MandelDim.HornTopoStatement) (hVarphi : MandelDim.HornVarphiStatement) (hSC : MandelDim.HornSCStatement) (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) (z : ℂ) (hzB : z ∈ B) (hzc : z ∉ MandelDim.critOrbit f₀ c) : ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ B ∧ IsCoveringMapOn (fun w : ↥(MandelDim.BuOf d B) => d.φ w) (Metric.ball z r) ∧ IsCoveringMapOn (fun w : ↥(MandelDim.BlOf d B) => d.φ w) (Metric.ball z r) := by
  -- the ball off the critical orbit
  obtain ⟨r₀, hr₀pos, hr₀B, hr₀nc⟩ := Work.HornVarphi.exists_ball_subset_diff_critOrbit hsetup hzB hzc
  -- the ball of Claim B with its holomorphic local sections
  obtain ⟨r₁, hr₁pos, -, hsec₁⟩ := hVarphi f₀ D₀ B c d hsetup z hzB hzc
  obtain ⟨hBuOpen, hBlOpen, -, -, -, -, -⟩ := hTopo f₀ D₀ B c d hsetup
  obtain ⟨-, -, hdisj⟩ := hSC f₀ D₀ B c d hsetup
  have hSsub₁ : Metric.ball z (min r₀ r₁) ⊆ Metric.ball z r₁ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hSsub₀ : Metric.ball z (min r₀ r₁) ⊆ Metric.ball z r₀ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hrpos : 0 < min r₀ r₁ := lt_min hr₀pos hr₁pos
  have hSB : Metric.ball z (min r₀ r₁) ⊆ B := hSsub₀.trans hr₀B
  have hScrit : Disjoint (Metric.ball z (min r₀ r₁)) (MandelDim.critOrbit f₀ c) := by
    rw [Set.disjoint_left]
    intro x hx hxc
    exact hr₀nc x (hSsub₀ hx) hxc
  have hpc : IsPreconnected (Metric.ball z (min r₀ r₁)) := (convex_ball z _).isPreconnected
  refine ⟨min r₀ r₁, hrpos, hSB, ?_, ?_⟩
  · -- the upper component
    refine isCoveringMapOn_of_sections Metric.isOpen_ball hpc ?_ ?_
    · exact isLocalHomeomorphOn_varphi_of_open_subset hTopo d hsetup hBuOpen
        subset_union_left hScrit
    · intro x hx
      obtain ⟨σ, hσdiff, hσmaps, hσφ, hσx⟩ := hsec₁ x (Or.inl x.2) (hSsub₁ hx)
      have himg : σ '' Metric.ball z (min r₀ r₁) ⊆ MandelDim.BuOf d B :=
        image_subset_left_of_section d hBuOpen hBlOpen hdisj hpc x.2 hx
          (hσmaps.mono hSsub₁ Subset.rfl) (hσdiff.continuousOn.mono hSsub₁) hσx
      have hcont : Continuous (fun u : ↥(Metric.ball z (min r₀ r₁)) => σ u) :=
        (hσdiff.continuousOn.mono hSsub₁).domRestrict
      exact ⟨fun u => ⟨σ u, himg ⟨u, u.2, rfl⟩⟩,
        hcont.subtype_mk (fun u => himg ⟨u, u.2, rfl⟩),
        (fun u => hσφ u (hSsub₁ u.2)), Subtype.ext hσx⟩
  · -- the lower component
    refine isCoveringMapOn_of_sections Metric.isOpen_ball hpc ?_ ?_
    · exact isLocalHomeomorphOn_varphi_of_open_subset hTopo d hsetup hBlOpen
        subset_union_right hScrit
    · intro x hx
      obtain ⟨σ, hσdiff, hσmaps, hσφ, hσx⟩ := hsec₁ x (Or.inr x.2) (hSsub₁ hx)
      have himg : σ '' Metric.ball z (min r₀ r₁) ⊆ MandelDim.BlOf d B :=
        image_subset_left_of_section d hBlOpen hBuOpen hdisj.symm hpc x.2 hx
          (hσmaps.mono hSsub₁ (by rw [Set.union_comm])) (hσdiff.continuousOn.mono hSsub₁) hσx
      have hcont : Continuous (fun u : ↥(Metric.ball z (min r₀ r₁)) => σ u) :=
        (hσdiff.continuousOn.mono hSsub₁).domRestrict
      exact ⟨fun u => ⟨σ u, himg ⟨u, u.2, rfl⟩⟩,
        hcont.subtype_mk (fun u => himg ⟨u, u.2, rfl⟩),
        (fun u => hσφ u (hSsub₁ u.2)), Subtype.ext hσx⟩

end Work.HornCov
