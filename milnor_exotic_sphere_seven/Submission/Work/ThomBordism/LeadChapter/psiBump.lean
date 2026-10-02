import Mathlib
import Submission.Work.ThomBordism.LeadChapter.bdryAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A continuous bump function subordinate to a half-space chart

For an open partial homeomorphism `ψ : W → EuclideanHalfSpace (n+1)` of a Hausdorff space `W`
whose target contains the closed `r`-ball around `ψ y`, and `0 < ρ < r`, we produce a continuous
function `χ : W → ℝ` with values in `[0,1]` which is `1` on the `ψ`-preimage of the closed
`ρ`-ball around `ψ y` and `0` outside the `ψ`-preimage of the closed `r`-ball around `ψ y`.

The function is the naive one, `χ z = bump (‖ψ z - ψ y‖)` inside the chart source and `0` outside;
the only point needing care is that the set of points of the source whose image lies in the closed
`r`-ball is *closed* in `W` (it is the image of a compact set under `ψ.symm`), so that `χ` is
continuous also at the boundary of the chart source.
-/

namespace Work.ThomBordism.LeadChapter

open Set Metric Filter
open scoped Topology

set_option linter.unusedVariables false

theorem psiBump (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1))) {y : W} (hyψ : y ∈ ψ.source)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hball : ∀ z : EuclideanHalfSpace (n + 1), dist z.1 (ψ y).1 ≤ r → z ∈ ψ.target) :
    ∃ χ : W → ℝ, Continuous χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ z, z ∈ ψ.symm '' {v : EuclideanHalfSpace (n + 1) | dist v.1 (ψ y).1 ≤ ρ} →
        χ z = 1) ∧
      (∀ z, z ∉ ψ.symm '' {v : EuclideanHalfSpace (n + 1) | dist v.1 (ψ y).1 ≤ r} →
        χ z = 0) := by
  classical
  let c : EuclideanSpace ℝ (Fin (n + 1)) := (ψ y).1
  let bump : ℝ → ℝ := fun t => max 0 (min 1 ((r - t) / (r - ρ)))
  have hden : (0 : ℝ) < r - ρ := by linarith
  have hbump_cont : Continuous bump := by
    have h1 : Continuous (fun t : ℝ => (r - t) / (r - ρ)) :=
      (continuous_const.sub continuous_id).div_const _
    exact continuous_const.max (continuous_const.min h1)
  have hbump_one : ∀ t ≤ ρ, bump t = 1 := by
    intro t ht
    have h1 : 1 ≤ (r - t) / (r - ρ) := by
      rw [le_div_iff₀ hden]; linarith
    simp only [bump, min_eq_left h1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
  have hbump_zero : ∀ t, r ≤ t → bump t = 0 := by
    intro t ht
    have h1 : (r - t) / (r - ρ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hden)
    simp only [bump, min_eq_right (le_trans h1 (by norm_num : (0 : ℝ) ≤ 1)), max_eq_left h1]
  have hbump_nonneg : ∀ t, 0 ≤ bump t := fun t => by
    simp only [bump]; exact le_max_left _ _
  have hbump_le_one : ∀ t, bump t ≤ 1 := fun t => by
    simp only [bump]; exact max_le (by norm_num) (min_le_left _ _)
  -- the closed `r`-ball in the model space is compact, so the corresponding set in `W` is closed
  have hKsub : {v : EuclideanHalfSpace (n + 1) | dist v.1 c ≤ r} ⊆ ψ.target := by
    intro v hv
    exact hball v hv
  have hKcomp : IsCompact {v : EuclideanHalfSpace (n + 1) | dist v.1 c ≤ r} := by
    rw [Subtype.isCompact_iff]
    have himg : (Subtype.val '' {v : EuclideanHalfSpace (n + 1) | dist v.1 c ≤ r}
        : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
        {x | 0 ≤ x 0} ∩ Metric.closedBall c r := by
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.2, hv⟩
      · rintro ⟨hx, hv⟩
        exact ⟨⟨x, hx⟩, hv, rfl⟩
    rw [himg]
    refine (isCompact_closedBall c r).of_isClosed_subset ?_ inter_subset_right
    exact (isClosed_Ici.preimage (f := fun x : EuclideanSpace ℝ (Fin (n + 1)) => x 0)
      (by fun_prop)).inter isClosed_closedBall
  have hBclosed : IsClosed (ψ.symm '' {v : EuclideanHalfSpace (n + 1) | dist v.1 c ≤ r}) :=
    (hKcomp.image_of_continuousOn (ψ.continuousOn_symm.mono hKsub)).isClosed
  have hBsub : ψ.symm '' {v : EuclideanHalfSpace (n + 1) | dist v.1 c ≤ r} ⊆ ψ.source := by
    rintro z ⟨v, hv, rfl⟩
    exact ψ.map_target (hKsub hv)
  refine ⟨(fun z => if z ∈ ψ.source then bump (dist (ψ z).1 c) else 0),
    ?hcont, ?hbnd, ?hone, ?hzero⟩
  · rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ ψ.source
    · have hψ : ContinuousAt (fun w => ψ w) z :=
        ψ.continuousOn_toFun.continuousAt (ψ.open_source.mem_nhds hz)
      have hg : Continuous (fun v : EuclideanHalfSpace (n + 1) => bump (dist v.1 c)) :=
        hbump_cont.comp (continuous_subtype_val.dist continuous_const)
      refine (hg.continuousAt.comp hψ).congr ?_
      filter_upwards [ψ.open_source.mem_nhds hz] with w hw
      simp only [hw, if_true, Function.comp_apply]
    · have hmem : (ψ.symm '' {v : EuclideanHalfSpace (n + 1) | dist v.1 c ≤ r})ᶜ ∈ 𝓝 z :=
        hBclosed.isOpen_compl.mem_nhds (fun h => hz (hBsub h))
      refine (continuousAt_const : ContinuousAt (fun _ : W => (0 : ℝ)) z).congr ?_
      filter_upwards [hmem] with w hw
      by_cases hw' : w ∈ ψ.source
      · simp only [hw', if_true]
        have hle : r ≤ dist (ψ w).1 c := by
          by_contra hlt
          rw [not_le] at hlt
          exact hw ⟨ψ w, le_of_lt hlt, ψ.left_inv hw'⟩
        rw [hbump_zero _ hle]
      · simp only [hw', if_false]
  · intro z
    by_cases hz : z ∈ ψ.source
    · simp only [hz, if_true]
      exact ⟨hbump_nonneg _, hbump_le_one _⟩
    · simp only [hz, if_false]
      exact ⟨le_refl 0, by norm_num⟩
  · intro z hz
    rcases hz with ⟨v, hv, rfl⟩
    have hvt : v ∈ ψ.target := hball v (le_trans hv (le_of_lt hρr))
    have hsrc : ψ.symm v ∈ ψ.source := ψ.map_target hvt
    have hval : ψ (ψ.symm v) = v := ψ.right_inv hvt
    simp only [hsrc, if_true, hval]
    exact hbump_one _ hv
  · intro z hz
    by_cases hzs : z ∈ ψ.source
    · simp only [hzs, if_true]
      have hle : r ≤ dist (ψ z).1 c := by
        by_contra hlt
        rw [not_le] at hlt
        exact hz ⟨ψ z, le_of_lt hlt, ψ.left_inv hzs⟩
      rw [hbump_zero _ hle]
    · simp only [hzs, if_false]

end Work.ThomBordism.LeadChapter
