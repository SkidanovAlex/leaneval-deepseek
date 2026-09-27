import Mathlib
import Submission.Work.Drive.N2Lead.exists_arcLift
import Submission.Work.Drive.N2Lead.pinSetup
import Submission.Work.Drive.N2Lead.pinComplex

/-!
# Lifting a *continuous* arc in one component of a level to the parameter of the component

`Work.Drive.N2Lead.exists_continuous_arcLift` is `Work.Drive.N2Lead.exists_arcLift` with the
smoothness and immersion hypotheses on `α` replaced by bare continuity on the (open preconnected)
parameter set `J ⊆ ℝ`.

Only the *existence of local pieces* used the smoothness of `α`, and it used it only through the
continuity of the composite `φ ∘ α` (`φ` a local phase of the immersed component curve `L.γ i`).
So the proof here is the same local-to-global gluing of anchored pieces as in `exists_arcLift.lean`
(`Work.Drive.N2Lead.exists_continuous_lift`, which is stated for an *arbitrary* local-piece datum),
fed with a continuity-only version of the local piece:
`Work.Drive.N2Lead.exists_local_piece_of_continuous` below.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

local notation "Cinf" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) Cinf M] [T2Space M]

/-- **A local piece of the lift (continuity only).**  Given a parameter `t` of the component curve
over `α w` and only *continuity* of `α` on the open `J`, there is a relatively open interval piece
`V ∋ w` of `J` on which `α` is lifted by the continuous expression `φ ∘ α`, anchored at `t`
(`φ` a local phase of the immersed curve `L.γ i`).

This is `Work.Drive.N2Lead.exists_local_piece_of` with `ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) Cinf α` weakened to
`ContinuousOn α J`: the smooth proof used the smoothness of `α` only through
`hα.continuous` / `hα.continuousOn`. -/
lemma exists_local_piece_of_continuous {f : M → ℝ} {b : ℝ} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f b n) (i : Fin n)
    {α : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hαc : ContinuousOn α J) (hJα : ∀ w ∈ J, α w ∈ Set.range (L.γ i))
    (w : ℝ) (hw : w ∈ J) (t : ℝ) (ht : L.γ i t = α w) :
    ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
      ContinuousOn τ_V V ∧ (∀ u ∈ V, L.γ i (τ_V u) = α u) ∧ τ_V w = t := by
  have himm : ∀ s : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) s 1 ≠ 0 :=
    fun s => mfderiv_γ_ne_zero L i s
  obtain ⟨U, φ, hUopen, htU, hφsm, δ, hδpos, hφ⟩ :=
    Work.Drive.N2C.exists_localPhase_of_immersed_curve (L.γ i) (L.sm i) himm t
  obtain ⟨W, hWopen, htW, hW⟩ :=
    exists_local_rightInverse (L.sm i).continuous (L.per i) (L.modOne i) t hδpos hφ
  have hWUopen : IsOpen (W ∩ U) := hWopen.inter hUopen
  have htWU : L.γ i t ∈ W ∩ U := ⟨htW, htU⟩
  -- continuity of `α` at `w` (`J` is a neighbourhood of `w`) makes the preimage of `W ∩ U` one
  have hpre : α ⁻¹' (W ∩ U) ∈ 𝓝 w :=
    (ContinuousOn.continuousAt hαc (hJ.mem_nhds hw)).preimage_mem_nhds
      (hWUopen.mem_nhds (by rw [← ht]; exact htWU))
  obtain ⟨ε₂, hε₂pos, hε₂sub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.isOpen_iff.mp hJ w hw
  have hεpos : 0 < min ε₁ ε₂ := lt_min hε₁pos hε₂pos
  refine ⟨J ∩ Ioo (w - min ε₁ ε₂) (w + min ε₁ ε₂), fun u => φ (α u), inter_subset_left,
    hJ.inter isOpen_Ioo, ?_, ⟨hw, by rw [mem_Ioo]; exact ⟨by linarith, by linarith⟩⟩,
    ?_, ?_, ?_⟩
  · exact (convex_iff_ordConnected.mpr hJc.ordConnected).ordConnected.inter
      (convex_Ioo _ _).ordConnected
  · -- continuity of the local lift `φ ∘ α` on `V`
    refine ContinuousOn.comp (t := W ∩ U)
      (hφsm.continuousOn.mono inter_subset_right) (hαc.mono inter_subset_left) (fun u hu => ?_)
    have hub : u ∈ Metric.ball w (min ε₁ ε₂) := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [(mem_Ioo.mp hu.2).1], by linarith [(mem_Ioo.mp hu.2).2]⟩
    exact hε₂sub (Metric.ball_subset_ball (min_le_right ε₁ ε₂) hub)
  · -- the local lift really lifts
    intro u hu
    have hub : u ∈ Metric.ball w (min ε₁ ε₂) := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [(mem_Ioo.mp hu.2).1], by linarith [(mem_Ioo.mp hu.2).2]⟩
    exact hW (α u) (hε₂sub (Metric.ball_subset_ball (min_le_right ε₁ ε₂) hub)).1 (hJα u hu.1)
  · -- and takes the value `t` at `w`
    change φ (α w) = t
    rw [← ht]
    exact hφ t ⟨by linarith [hδpos], by linarith [hδpos]⟩

open scoped Manifold ContDiff in
/-- **A continuous arc in the range of one component curve lifts to a continuous parameter.**  This
is `Work.Drive.N2Lead.exists_arcLift` with the smoothness and immersion hypotheses on `α` replaced
by bare continuity: the local pieces of the lift are `φ ∘ α` (`φ` a local phase of the smooth
immersed curve `L.γ i`), and they glue to a global continuous lift along the preconnected `J`. -/
theorem exists_continuous_arcLift {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n) (i : Fin n)
    {α : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (hαc : ContinuousOn α J) (hJα : ∀ w ∈ J, α w ∈ Set.range (L.γ i)) :
    ∃ τ : ℝ → ℝ, ContinuousOn τ J ∧ ∀ w ∈ J, L.γ i (τ w) = α w := by
  have hpiece : ∀ (w : ℝ) (hw : w ∈ J) (t : ℝ), L.γ i t = α w →
      ∃ (V : Set ℝ) (τ_V : ℝ → ℝ), V ⊆ J ∧ IsOpen V ∧ V.OrdConnected ∧ w ∈ V ∧
        ContinuousOn τ_V V ∧ (∀ u ∈ V, L.γ i (τ_V u) = α u) ∧ τ_V w = t :=
    fun w hw t ht => exists_local_piece_of_continuous L i hJ hJc hαc hJα w hw t ht
  exact exists_continuous_lift hJ hJc hJα (L.modOne i) (L.per i) hpiece

end Work.Drive.N2Lead
