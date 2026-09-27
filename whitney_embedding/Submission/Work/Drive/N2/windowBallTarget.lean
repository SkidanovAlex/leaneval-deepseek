import Mathlib
import Submission.Work.Drive.N2.windowDatum

/-!
# The ball of radius `ρ i` of a model chart lies in the chart's target

The lead's design note (`N2Lead/NOTES_LEAD_windowBase.md` §2, `ball_subset_target`) records this as
one of the engines of the window construction: for the chart `φ i` of a `WindowDatum` at a critical
point, the *whole* ball of radius `ρ i` around `0` is contained in `(φ i).target`, so that the point
`(φ i).symm w` is defined — and lies in `C i` — for every `w` of norm `< ρ i`.  It is needed for
`Λ ≠ ∅`, for the forced arcs (whose points are given in chart coordinates), and for the surjectivity
row of L-F.

The proof is the closedness of the chart tube.  Put

* `K := (φ i) '' closure (C i)` — compact (the image of the compact `closure (C i)` under the
  continuous-on-`source` chart), hence closed in the chart space;

then the set `A := {s ∈ [0,1] | s • w ∈ (φ i).target}` equals `Icc 0 1 ∩ (s ↦ s • w) ⁻¹' K`
(the point `s • w` of the target has norm `≤ ‖w‖ < ρ i`, so its inverse image lies in `C i` by
`hCop`), hence is closed.  It contains `0`, so its supremum `t` lies in it; if `t < 1`, the openness
of the target gives a larger element of `A`, contradiction — so `1 ∈ A` and `w ∈ target`.

Everything happens in the chart space `ℝ²` (which is Hausdorff), so **no `T2Space` hypothesis on `M`
is needed**.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

section

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **The chart ball of radius `ρ i` is inside the chart's target.** -/
theorem windowBall_subset_target {f : M → ℝ} {p : M} (D : WindowDatum f p) (i : Fin D.N)
    {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ < D.ρ i) :
    w ∈ (D.φ i).target := by
  have hKc : IsCompact ((D.φ i) '' closure (D.C i)) :=
    (D.hCcl i).1.image_of_continuousOn ((D.hφ i).continuousOn.mono (D.hCcl i).2)
  have hScl : IsClosed ((fun s : ℝ => s • w) ⁻¹' ((D.φ i) '' closure (D.C i))) :=
    hKc.isClosed.preimage (continuous_id.smul continuous_const)
  set A : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ s • w ∈ (D.φ i).target} with hA
  have hAeq : A = Set.Icc (0 : ℝ) 1 ∩
      (fun s : ℝ => s • w) ⁻¹' ((D.φ i) '' closure (D.C i)) := by
    ext s
    constructor
    · rintro ⟨hsI, hst⟩
      have hy : (D.φ i).symm (s • w) ∈ (D.φ i).source := (D.φ i).map_target hst
      have hlt : ‖s • w‖ < D.ρ i := by
        have hs1 : |s| ≤ 1 := by
          rw [abs_le]; exact ⟨by linarith [hsI.1], hsI.2⟩
        calc ‖s • w‖ = |s| * ‖w‖ := norm_smul s w
          _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
          _ = ‖w‖ := one_mul _
          _ < D.ρ i := hw
      have hyC : (D.φ i).symm (s • w) ∈ D.C i :=
        D.hCop i ⟨hy, by rwa [(D.φ i).right_inv hst]⟩
      exact ⟨hsI, ⟨(D.φ i).symm (s • w), subset_closure hyC, (D.φ i).right_inv hst⟩⟩
    · rintro ⟨hsI, y, hy, hysw⟩
      refine ⟨hsI, ?_⟩
      have hysw' : D.φ i y = s • w := hysw
      rw [← hysw']
      exact (D.φ i).map_source ((D.hCcl i).2 hy)
  have hAclosed : IsClosed A := by
    rw [hAeq]
    exact isClosed_Icc.inter hScl
  have h0A : (0 : ℝ) ∈ A := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [zero_smul]
    exact D.hcen i ▸ (D.φ i).map_source (D.hsrc i)
  have hbdd : BddAbove A := ⟨1, fun s hs => hs.1.2⟩
  have hsupA : sSup A ∈ A := hAclosed.csSup_mem ⟨0, h0A⟩ hbdd
  have hsup_le : sSup A ≤ 1 := hsupA.1.2
  have hsup_eq : sSup A = 1 := by
    by_contra hne
    have hlt : sSup A < 1 := lt_of_le_of_ne hsup_le hne
    have hpos : 0 < 1 - sSup A := by linarith
    have hmem : (D.φ i).target ∈ 𝓝 ((sSup A) • w) :=
      (D.φ i).open_target.mem_nhds hsupA.2
    have hev : ∀ᶠ s in 𝓝 (sSup A), s • w ∈ (D.φ i).target :=
      ((continuous_id.smul continuous_const).continuousAt) hmem
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hev
    set δ : ℝ := min (1 - sSup A) ε / 2 with hδ
    have hminpos : 0 < min (1 - sSup A) ε := lt_min hpos hεpos
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hδlt : δ < min (1 - sSup A) ε := by rw [hδ]; linarith
    have hδ1 : δ < 1 - sSup A := lt_of_lt_of_le hδlt (min_le_left _ _)
    have hδε : δ < ε := lt_of_lt_of_le hδlt (min_le_right _ _)
    have hs0 : 0 ≤ sSup A := hsupA.1.1
    have hsA : (sSup A + δ) ∈ A := by
      refine ⟨⟨by linarith [hs0, hδpos], by linarith [hδ1]⟩, ?_⟩
      refine hε ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have := le_csSup hbdd hsA
    linarith
  have := hsupA.2
  rw [hsup_eq, one_smul] at this
  exact this

/-- The ball version: `Metric.ball 0 (ρ i) ⊆ (φ i).target`. -/
theorem windowBall_target_subset {f : M → ℝ} {p : M} (D : WindowDatum f p) (i : Fin D.N) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (D.ρ i) ⊆ (D.φ i).target := by
  intro w hw
  refine windowBall_subset_target D i ?_
  simpa [Metric.mem_ball, dist_eq_norm] using hw

/-- The inverse image of a point of the `ρ i`-ball lies in the chart's source. -/
theorem windowBall_symm_mem_source {f : M → ℝ} {p : M} (D : WindowDatum f p) (i : Fin D.N)
    {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ < D.ρ i) :
    (D.φ i).symm w ∈ (D.φ i).source :=
  (D.φ i).map_target (windowBall_subset_target D i hw)

/-- The inverse image of a point of the `ρ i`-ball lies in the chart's region `C i` (this is the
form the forced arcs consume: the entry points of the chart are points of `C i`). -/
theorem windowBall_symm_mem_C {f : M → ℝ} {p : M} (D : WindowDatum f p) (i : Fin D.N)
    {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ < D.ρ i) :
    (D.φ i).symm w ∈ D.C i :=
  D.hCop i ⟨windowBall_symm_mem_source D i hw,
    by rw [(D.φ i).right_inv (windowBall_subset_target D i hw)]; exact hw⟩

/-- The chart inverts its own inverse on the `ρ i`-ball. -/
theorem windowBall_symm_apply {f : M → ℝ} {p : M} (D : WindowDatum f p) (i : Fin D.N)
    {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ < D.ρ i) :
    D.φ i ((D.φ i).symm w) = w :=
  (D.φ i).right_inv (windowBall_subset_target D i hw)

end

end Work.Drive.N2
