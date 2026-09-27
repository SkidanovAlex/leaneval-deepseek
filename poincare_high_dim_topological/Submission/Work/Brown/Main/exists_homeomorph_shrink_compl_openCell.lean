import Mathlib
import Submission.Work.Brown.Basic
import Submission.Work.Brown.Cellular.exists_isOpenCell_neighborhood
import Submission.Work.Brown.Cell.exists_homeomorph_image_compact_subset_open

/-!
# Shrinking a closed set with open-cell complement into a small ball

Let `K ⊆ 𝕊ⁿ` be closed with `Kᶜ ≅ ℝⁿ`, let `W ⊇ K` be open and let `ε > 0`.  Then there is a
homeomorphism `h'` of `𝕊ⁿ`, the identity outside `W`, which carries `K` into a ball of radius `ε`.

The proof is a "pinch" argument.  Choose an open `n`-cell `W'` with `K ⊆ W' ⊆ W`
(`Work.Brown.Cellular.exists_isOpenCell_neighborhood`) and a chart `φ : ℝⁿ ≅ W'`.  The compact
set `L = φ⁻¹(K) ⊆ ℝⁿ` is moved into a tiny ball by a homeomorphism `σ` of `ℝⁿ` which is the
identity outside a large ball (`Work.Brown.Cell.exists_homeomorph_image_compact_subset_open`).
Because `σ` is the identity near the ends of the open cell, the conjugate `φ σ φ⁻¹` of `W'`
extends by the identity on `𝕊ⁿ ∖ W'` (the required neighbourhood of the boundary exists since
`φ` of a compact ball is closed in `𝕊ⁿ`).  The resulting self-map of the compact space `𝕊ⁿ` is
a continuous bijection, hence a homeomorphism, and it does the job.
-/

namespace Work.Brown.Main

open Set Metric

theorem exists_homeomorph_shrink_compl_openCell {n : ℕ} {K : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)} (hK : IsClosed K) (h : ↥(Kᶜ : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) ≃ₜ PL.E n) {W : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)} (hW : IsOpen W) (hKW : K ⊆ W) {ε : ℝ} (hε : 0 < ε) : ∃ (h' : ↥(Metric.sphere (0 : PL.E (n + 1)) 1) ≃ₜ ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) (x₀ : ↥(Metric.sphere (0 : PL.E (n + 1)) 1)), (∀ y, y ∉ W → h' y = y) ∧ h' '' K ⊆ Metric.ball x₀ ε := by
  classical
  let S := ↥(Metric.sphere (0 : PL.E (n + 1)) 1)
  haveI : CompactSpace S :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : PL.E (n + 1)) 1)
  -- (1) an open cell neighbourhood `W'` of `K` inside `W`
  obtain ⟨W', hW'open, hKW', hW'W, ⟨e⟩⟩ :=
    Work.Brown.Cellular.exists_isOpenCell_neighborhood hK ⟨h⟩ hW hKW
  -- (2) the chart `φ : ℝⁿ → 𝕊ⁿ` with range `W'`
  let φ : PL.E n → S := fun y => ((e.symm y : ↥W') : S)
  have hφcont : Continuous φ := continuous_subtype_val.comp e.symm.continuous
  have hφmem : ∀ y, φ y ∈ W' := fun y => (e.symm y).2
  -- (3) a tiny ball `A = ball 0 r` whose `φ`-image lies in `ball (φ 0) ε`
  obtain ⟨r, hr0, hrball⟩ : ∃ r : ℝ, 0 < r ∧ φ '' Metric.ball (0 : PL.E n) r ⊆ Metric.ball (φ 0) ε := by
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hφcont.continuousAt ε hε
    exact ⟨δ, hδ0, fun _ ⟨y, hy, hyz⟩ => hyz ▸ hδ hy⟩
  -- (4) `L = φ⁻¹(K)` is compact
  let L : Set (PL.E n) := e '' (Subtype.val ⁻¹' K : Set ↥W')
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK.isCompact
  have hLcompact : IsCompact L := by
    have hCcompact : IsCompact (Subtype.val ⁻¹' K : Set ↥W') := by
      have hset : (Subtype.val ⁻¹' K : Set ↥W')
          = (fun x : ↥K => (⟨(x : S), hKW' x.2⟩ : ↥W')) '' Set.univ := by
        ext x
        constructor
        · intro hx; exact ⟨⟨(x : S), hx⟩, trivial, Subtype.ext rfl⟩
        · rintro ⟨y, -, hyx⟩; rw [← hyx]; exact y.2
      rw [hset]
      exact isCompact_univ.image (continuous_subtype_val.subtype_mk (fun x => hKW' x.2))
    exact hCcompact.image e.continuous
  -- (5) the squeezing homeomorphism `σ` of `ℝⁿ`, identity outside a large ball
  obtain ⟨σ, hσL, R, hσfix⟩ := Work.Brown.Cell.exists_homeomorph_image_compact_subset_open
    (K := L) (A := Metric.ball (0 : PL.E n) r) hLcompact Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self hr0⟩
  let R₁ : ℝ := max R 1
  have hR₁pos : 0 < R₁ := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hσfix' : ∀ x : PL.E n, R₁ ≤ ‖x‖ → σ x = x :=
    fun x hx => hσfix x (le_trans (le_max_left R 1) hx)
  -- (6) the closed set `C = φ '' closedBall 0 R₁`
  let C : Set S := φ '' Metric.closedBall (0 : PL.E n) R₁
  have hCclosed : IsClosed C := (isCompact_closedBall (0 : PL.E n) R₁).image hφcont |>.isClosed
  have hCsub : C ⊆ W' := by rintro z ⟨y, -, rfl⟩; exact (e.symm y).2
  -- (7) the candidate self-map of `𝕊ⁿ`
  let h' : S → S := fun x => if hx : x ∈ W' then φ (σ (e ⟨x, hx⟩)) else x
  have h'_mem : ∀ (x : S) (hx : x ∈ W'), h' x = φ (σ (e ⟨x, hx⟩)) := by
    intro x hx
    simp only [h']
    rw [dif_pos hx]
  have h'_notmem : ∀ (x : S) (hx : x ∉ W'), h' x = x := by
    intro x hx
    simp only [h']
    rw [dif_neg hx]
  -- (8) continuity of `h'`
  have hGcont : Continuous (fun x : ↥W' => φ (σ (e x))) :=
    hφcont.comp (σ.continuous.comp e.continuous)
  have hcontW' : ContinuousOn h' W' := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : W'.domRestrict h' = fun x : ↥W' => φ (σ (e x)) := by
      funext x
      rw [Set.domRestrict_apply]
      exact h'_mem (x : S) x.2
    rw [this]
    exact hGcont
  let O : Set S := Cᶜ
  have hOopen : IsOpen O := hCclosed.isOpen_compl
  have hfixO : ∀ x ∈ O, h' x = x := by
    intro x hx
    by_cases hxW : x ∈ W'
    · rw [h'_mem x hxW]
      have hy : R₁ ≤ ‖e ⟨x, hxW⟩‖ := by
        by_contra hlt
        rw [not_le] at hlt
        exact hx ⟨e ⟨x, hxW⟩, by
            rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hlt, by simp [φ]⟩
      rw [hσfix' _ hy]
      simp [φ]
    · exact h'_notmem x hxW
  have hcontO : ContinuousOn h' O :=
    (continuous_id.continuousOn).congr (fun x hx => hfixO x hx)
  have hcov : W' ∪ O = Set.univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    by_cases hx : x ∈ W'
    · exact Or.inl hx
    · refine Or.inr (fun hxC => hx ?_)
      obtain ⟨y, -, hyx⟩ := hxC
      exact hyx ▸ hφmem y
  have hcont : Continuous h' := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ W'
    · exact (hW'open.continuousOn_iff.mp hcontW') hx
    · have hxO : x ∈ O := (by rw [hcov]; trivial : x ∈ W' ∪ O).resolve_left hx
      exact (hOopen.continuousOn_iff.mp hcontO) hxO
  -- (9) `h'` is bijective
  have hinj : Function.Injective h' := by
    intro x y hxy
    by_cases hx : x ∈ W' <;> by_cases hy : y ∈ W'
    · rw [h'_mem x hx, h'_mem y hy] at hxy
      have h2 : (e.symm (σ (e ⟨x, hx⟩)) : ↥W') = (e.symm (σ (e ⟨y, hy⟩)) : ↥W') :=
        Subtype.ext hxy
      have h1 : σ (e ⟨x, hx⟩) = σ (e ⟨y, hy⟩) := by
        simpa using congrArg (fun z : ↥W' => (e z : PL.E n)) h2
      exact Subtype.ext_iff.mp (e.injective (σ.injective h1))
    · rw [h'_mem x hx, h'_notmem y hy] at hxy
      exact absurd (hxy ▸ hφmem (σ (e ⟨x, hx⟩))) hy
    · rw [h'_notmem x hx, h'_mem y hy] at hxy
      exact absurd (hxy.symm ▸ hφmem (σ (e ⟨y, hy⟩))) hx
    · rw [h'_notmem x hx, h'_notmem y hy] at hxy
      exact hxy
  have hsurj : Function.Surjective h' := by
    intro z
    by_cases hz : z ∈ W'
    · refine ⟨((e.symm (σ.symm (e ⟨z, hz⟩)) : ↥W') : S), ?_⟩
      have hsub : ((e.symm (σ.symm (e ⟨z, hz⟩)) : ↥W') : S) ∈ W' := (e.symm _).2
      rw [h'_mem _ hsub]
      have hkey : (⟨((e.symm (σ.symm (e ⟨z, hz⟩)) : ↥W') : S), hsub⟩ : ↥W')
          = e.symm (σ.symm (e ⟨z, hz⟩)) := Subtype.ext rfl
      rw [hkey]
      simp [φ]
    · exact ⟨z, h'_notmem z hz⟩
  -- (10) assemble the homeomorphism
  let E : S ≃ S := Equiv.ofBijective h' ⟨hinj, hsurj⟩
  let H : S ≃ₜ S := Continuous.homeoOfEquivCompactToT2 (f := E) hcont
  refine ⟨H, φ 0, ?_, ?_⟩
  · intro y hy
    have hyW : y ∉ W' := fun hy' => hy (hW'W hy')
    change H y = y
    rw [show H y = h' y from rfl]
    exact h'_notmem y hyW
  · rintro z ⟨p, hp, rfl⟩
    change H p ∈ Metric.ball (φ 0) ε
    rw [show H p = h' p from rfl]
    have hpW : p ∈ W' := hKW' hp
    rw [h'_mem p hpW]
    have heL : e ⟨p, hpW⟩ ∈ L := ⟨⟨p, hpW⟩, hp, rfl⟩
    have hσmem : σ (e ⟨p, hpW⟩) ∈ Metric.ball (0 : PL.E n) r := hσL ⟨e ⟨p, hpW⟩, heL, rfl⟩
    exact hrball ⟨σ (e ⟨p, hpW⟩), hσmem, rfl⟩

end Work.Brown.Main
