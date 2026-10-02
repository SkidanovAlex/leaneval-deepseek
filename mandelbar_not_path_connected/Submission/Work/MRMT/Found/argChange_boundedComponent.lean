import Mathlib
import Submission.Work.MRMT.QC.plane_surjective
import Submission.Work.MRMT.Found.hasArgChange_sub_of_norm_gt
import Submission.Work.MRMT.Found.hasArgChange_sub_iff_of_norm_lt
import Submission.Work.MRMT.Found.hasArgChange_inj
import Submission.Commons.Topology.Jordan.frontier_connectedComponentIn_subset

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A loop with non-zero argument change bounds a component of its complement

For a closed loop `γ : ℝ → ℂ` that never vanishes and whose argument change is `2πk` with
`k ≠ 0`, the connected component of `0` in the complement of (the image of) `γ` is bounded:
this is the fact that a loop of non-zero winding number around `0` separates `0` from
infinity.

The proof does not use any homotopy theory.  Instead we use that the argument change of the
loop `γ - w` is *locally constant* in `w` on the complement of the (compact) image of `γ`
(`hasArgChange_sub_iff_of_norm_lt`), and that it is `0` for `w` outside a ball containing the image
(`hasArgChange_sub_of_norm_gt`).  Hence the set `W` of points `w` where `γ - w` has argument change `0`
is both open and closed in the complement, so it contains every preconnected subset of the
complement containing a point of `W`.  If the component of `0` were unbounded it would meet
the far-away region, hence would be contained in `W`, giving argument change `0` for `γ`
itself — contradicting `k ≠ 0` by uniqueness of the argument change (`hasArgChange_inj`).

The main theorem `Work.MRMT.Found.argChange_boundedComponent` records this in the exact form
requested downstream: the component `D` is open and bounded, its frontier is contained in the
image of `γ`, and it contains every preconnected set in the complement that contains `0`.
-/

noncomputable section

open Set Metric
open scoped Topology

namespace Work.MRMT.Found

/-- **The bounded component.**  If `γ` is a continuous loop with `γ 1 = γ 0` that never
vanishes and has argument change `2πk` with `k ≠ 0`, then the connected component of `0` in
the complement of the image `γ '' [0,1]` is bounded. -/
theorem argChange_aux_bounded {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hloop : γ 1 = γ 0) (h0 : ∀ t, γ t ≠ 0) {k : ℤ} (hk : k ≠ 0)
    (hac : Work.MRMT.QC.HasArgChange γ k) :
    Bornology.IsBounded (connectedComponentIn ((γ '' Set.Icc (0 : ℝ) 1)ᶜ) 0) := by
  classical
  set K : Set ℂ := γ '' Set.Icc (0 : ℝ) 1 with hK
  set U : Set ℂ := Kᶜ with hU
  have hUopen : IsOpen U := (isCompact_Icc.image_of_continuousOn hγ).isClosed.isOpen_compl
  have hKmem : ∀ w : ℂ, w ∈ K ↔ ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t = w := by
    intro w
    rw [hK]
    exact mem_image γ (Set.Icc (0 : ℝ) 1) w
  have hUmem : ∀ w : ℂ, w ∈ U ↔ w ∉ K := by
    intro w
    rw [hU]
    exact Iff.rfl
  have h0U : (0 : ℂ) ∈ U := by
    rw [hUmem]
    intro hK0
    obtain ⟨t, ht, htz⟩ := (hKmem 0).mp hK0
    exact h0 t htz
  set D : Set ℂ := connectedComponentIn U 0 with hD
  -- a bound `M` for the loop
  obtain ⟨t₁, ht₁, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, by norm_num⟩ (hγ.norm)
  set M : ℝ := ‖γ t₁‖ with hMdef
  have hMb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖γ t‖ ≤ M := fun t ht => hmax ht
  -- the set of parameters where the argument change of `γ - w` vanishes
  set W : Set ℂ := {w : ℂ | w ∈ U ∧ Work.MRMT.QC.HasArgChange (fun t => γ t - w) 0} with hW
  have hfar : ∀ w : ℂ, M < ‖w‖ → w ∈ W := by
    refine fun w hw => ⟨?_, hasArgChange_sub_of_norm_gt hγ hloop hMb hw⟩
    rw [hUmem]
    intro hwK
    obtain ⟨t, ht, htz⟩ := (hKmem w).mp hwK
    have hle : ‖γ t‖ ≤ M := hMb t ht
    have hw' : M < ‖γ t‖ := by rw [htz]; exact hw
    linarith
  -- local structure of `W` and of its complement in `U`
  have hloc : ∀ x ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ U ∧
      ∀ w' ∈ Metric.ball x ρ,
        (Work.MRMT.QC.HasArgChange (fun t => γ t - w') 0 ↔
         Work.MRMT.QC.HasArgChange (fun t => γ t - x) 0) := by
    intro x hx
    have hxne : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t - x ≠ 0 := by
      intro t ht h
      exact ((hUmem x).mp hx) ((hKmem x).mpr ⟨t, ht, sub_eq_zero.mp h⟩)
    obtain ⟨δ, hδ, hδiff⟩ := hasArgChange_sub_iff_of_norm_lt hγ hloop hxne
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hUopen x hx
    refine ⟨min δ ε, lt_min hδ hε, ?_, ?_⟩
    · intro y hy
      exact hεU (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _)))
    · intro y hy
      have h1 : ‖y - x‖ < min δ ε := by
        rw [← Complex.dist_eq]
        exact Metric.mem_ball.mp hy
      exact hδiff y (lt_of_lt_of_le h1 (min_le_left _ _))
  have hWopen : IsOpen W := by
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨ρ, hρ, hρU, hρiff⟩ := hloc x hx.1
    exact ⟨ρ, hρ, fun y hy => ⟨hρU hy, (hρiff y hy).mpr hx.2⟩⟩
  have hWcop : IsOpen (U \ W) := by
    rw [Metric.isOpen_iff]
    intro x hx
    have hxU : x ∈ U := hx.1
    have hxW : ¬ Work.MRMT.QC.HasArgChange (fun t => γ t - x) 0 := fun h => hx.2 ⟨hxU, h⟩
    obtain ⟨ρ, hρ, hρU, hρiff⟩ := hloc x hxU
    exact ⟨ρ, hρ, fun y hy => ⟨hρU hy, fun hyW => hxW ((hρiff y hy).mp hyW.2)⟩⟩
  -- `D` is preconnected and contained in the union `W ∪ (U \ W)`
  have hDpre : IsPreconnected D := by rw [hD]; exact isPreconnected_connectedComponentIn
  have hDsub : D ⊆ U := by rw [hD]; exact connectedComponentIn_subset U 0
  have hDunion : D ⊆ W ∪ (U \ W) := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr ⟨hDsub hx, hxW⟩
  by_contra hbdd
  -- an unbounded component meets the far away region
  have hunb : ∃ w ∈ D, M < ‖w‖ := by
    by_contra hc
    push Not at hc
    exact hbdd ((Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr ⟨M, fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hc x hx⟩)
  obtain ⟨w, hwD, hwM⟩ := hunb
  have hwW : w ∈ W := hfar w hwM
  have hDW : D ⊆ W := by
    rcases hDpre.subset_or_subset (u := W) (v := U \ W) hWopen hWcop disjoint_sdiff_right
      hDunion with h | h
    · exact h
    · exact absurd hwW (h hwD).2
  have h0W : (0 : ℂ) ∈ W := hDW (by rw [hD]; exact mem_connectedComponentIn h0U)
  have h0ac : Work.MRMT.QC.HasArgChange γ 0 :=
    Work.MRMT.QC.hasArgChange_congr h0W.2 (fun t => by simp)
  exact hk (hasArgChange_inj (fun t _ => h0 t) hac h0ac)

/-- **The frontier of the component of `0` lies in the image of `γ`.**  For an open set `U` and
a point `x`, the frontier of the connected component of `x` in `U` is contained in the
complement of `U`. -/
theorem argChange_aux_frontier {U : Set ℂ} (hU : IsOpen U) (x : ℂ) :
    frontier (connectedComponentIn U x) ⊆ Uᶜ := by
  have h := Commons.Topology.Jordan.frontier_connectedComponentIn_subset (S := Uᶜ)
    hU.isClosed_compl x
  simp only [compl_compl] at h
  intro z hz
  rw [frontier] at hz
  exact h z hz.1 hz.2

/-- **Mandelbar / multicorn foundation: a loop with non-zero argument change bounds a
component of its complement.**

If `γ : ℝ → ℂ` is a continuous loop (`γ 1 = γ 0`) that never vanishes and has argument change
`2πk` with `k ≠ 0`, then there is an open bounded set `D` whose frontier is contained in the
image of `γ`, with `0 ∈ D`, and which contains *every* preconnected subset of the complement
of the image of `γ` that contains `0`.

`D` is the connected component of `0` in the complement of the compact curve
`γ '' [0,1]`.  It is open because the complement of the compact set `γ '' [0,1]` is open in
the locally connected space `ℂ`; its frontier is contained in `γ '' [0,1] ⊆ range γ`; it is
bounded by `argChange_aux_bounded`; and it contains every preconnected `E` in the complement
of `range γ` containing `0`, because such an `E` is a preconnected subset of the complement of
`γ '' [0,1]` containing `0`. -/
theorem argChange_boundedComponent {γ : ℝ → ℂ} (hγ : Continuous γ) (hloop : γ 1 = γ 0)
    (h0 : ∀ t, γ t ≠ 0) {k : ℤ} (hk : k ≠ 0) (hac : Work.MRMT.QC.HasArgChange γ k) :
    ∃ D : Set ℂ, IsOpen D ∧ Bornology.IsBounded D ∧ frontier D ⊆ Set.range γ ∧ (0 : ℂ) ∈ D ∧
      ∀ E : Set ℂ, IsPreconnected E → E ⊆ (Set.range γ)ᶜ → (0 : ℂ) ∈ E → E ⊆ D := by
  classical
  set K : Set ℂ := γ '' Set.Icc (0 : ℝ) 1 with hK
  set U : Set ℂ := Kᶜ with hU
  have hUopen : IsOpen U := (isCompact_Icc.image_of_continuousOn hγ.continuousOn).isClosed.isOpen_compl
  have hKmem : ∀ w : ℂ, w ∈ K ↔ ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t = w := by
    intro w
    rw [hK]
    exact mem_image γ (Set.Icc (0 : ℝ) 1) w
  have hUmem : ∀ w : ℂ, w ∈ U ↔ w ∉ K := by
    intro w
    rw [hU]
    exact Iff.rfl
  have h0U : (0 : ℂ) ∈ U := by
    rw [hUmem]
    intro hK0
    obtain ⟨t, ht, htz⟩ := (hKmem 0).mp hK0
    exact h0 t htz
  set D : Set ℂ := connectedComponentIn U 0 with hD
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hD]; exact hUopen.connectedComponentIn
  · rw [hD, hU, hK]
    exact argChange_aux_bounded hγ.continuousOn hloop h0 hk hac
  · intro z hz
    have hz' : z ∈ frontier (connectedComponentIn U 0) := by rwa [hD] at hz
    have hzU : z ∈ Uᶜ := argChange_aux_frontier hUopen 0 hz'
    have hzK : z ∈ K := by
      by_contra hzK
      exact hzU ((hUmem z).mpr hzK)
    obtain ⟨t, ht, htz⟩ := (hKmem z).mp hzK
    exact ⟨t, htz⟩
  · rw [hD]; exact mem_connectedComponentIn h0U
  · intro E hEpre hEsub hE0
    rw [hD]
    refine hEpre.subset_connectedComponentIn hE0 ?_
    intro z hz
    rw [hUmem]
    intro hzK
    obtain ⟨t, ht, htz⟩ := (hKmem z).mp hzK
    exact hEsub hz ⟨t, htz⟩

end Work.MRMT.Found
