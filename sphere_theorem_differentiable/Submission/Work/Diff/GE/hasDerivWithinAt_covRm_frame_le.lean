import Mathlib
import Submission.Work.Diff.GE.MovingFrame.FrameRule
import Submission.Work.Diff.GE.MovingFrame.covRm5_contMultilinear_bound
import Submission.Work.Diff.GE.MovingFrame.tendsto_multilinear_apply
import Submission.Work.Diff.GE.EvolB.Fix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Work.Diff.GE.MovingFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The model-space structure on the fibres

`TangentSpace I x` is a type synonym for the model space `E`, which type class inference does not
unfold; the instances below (the model-space structure, as in
`Mathlib.Geometry.Manifold.Riemannian.Basic` and `Submission/Work/Diff/GE/exists_ON_frame_family`)
make it available.  They agree definitionally with the structures induced by any `RiemannianBundle`
instance, so they introduce no ambiguity. -/

noncomputable scoped instance instTangentSpaceNAG (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

noncomputable scoped instance instTangentSpaceNS (x : M) : NormedSpace ℝ (TangentSpace I x) :=
  inferInstanceAs (NormedSpace ℝ E)

noncomputable scoped instance instTangentSpaceFD (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- **The evolution estimate for the components of `∇Rm` in a moving orthonormal frame.**

Let `G` be a Ricci flow on `[0,T)`, `t ∈ [0,T)`, `x : M`, and let `s ↦ e s` be a family of frames at
`x` which is orthonormal for `G s` near `t` and differentiable at `t` with derivative `edot`, whose
size is controlled by the curvature: `|edot i|²_{G t} ≤ K |Rm|²`.  Then each component of `∇Rm` in
the moving frame is differentiable in `s` and its derivative is bounded by the corresponding
component of the rough Laplacian `Δ∇Rm` plus `C (1+K) |Rm| |∇Rm|`.

The `(1+K)` accounts for the derivative of the frame vectors; the need for the `K`-term is why the
frame has to be chosen `Ric`-compatible (Uhlenbeck). -/
theorem hasDerivWithinAt_covRm_frame_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
        (edot : Fin (Module.finrank ℝ E) → TangentSpace I x) (K : ℝ), 0 ≤ K →
        (∀ᶠ s in 𝓝[Set.Ico 0 T] t, IsONFrame (G s) x (e s)) →
        (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) →
        (∀ i, (G t).inner x (edot i) (edot i) ≤ K * rmNormSq (G t) x) →
        ∀ m i j k l : Fin (Module.finrank ℝ E), ∃ D : ℝ,
          HasDerivWithinAt
            (fun s ↦ covRm (G s) x (e s m) (e s i) (e s j) (e s k) (e s l)) D (Set.Ico 0 T) t ∧
          D ≤ Work.Diff.GE.lapCovRmAt (G t) x (e t m) (e t i) (e t j) (e t k) (e t l)
              + C * (1 + K) * Real.sqrt (rmNormSq (G t) x)
                  * Real.sqrt (dRmNormSq (G t) x) := by
  obtain ⟨C₀, hC₀0, hFIX⟩ := Work.Diff.GE.EvolB.hasDerivWithinAt_covRm_le_B (I := I) (M := M) hLC hLV
  refine ⟨C₀ + 5, by linarith, ?_⟩
  intro G T hRic t ht x e edot K hK hON hed hKb m i j k l
  -- `∇Rm` bundled as a continuous multilinear form of the five tangent vectors
  have hAex : ∀ g : SMet I M,
      ∃ A : ContinuousMultilinearMap ℝ (fun _ : Fin 5 => TangentSpace I x) ℝ,
        (∀ w : Fin 5 → TangentSpace I x, A w = covRm5 g x w) ∧
        (∀ w : Fin 5 → TangentSpace I x, |A w| ≤ dRmNorm g x * argNorms g x w) :=
    fun g =>
      Work.Diff.GE.MovingFrame.Work.Diff.GE.MovingFrame.covRm5_contMultilinear_bound hLC g x
  choose A hA using hAex
  have hAeval : ∀ (g : SMet I M) (w : Fin 5 → TangentSpace I x), A g w = covRm5 g x w :=
    fun g w => (hA g).1 w
  have hAbound : ∀ (g : SMet I M) (w : Fin 5 → TangentSpace I x),
      |A g w| ≤ dRmNorm g x * argNorms g x w := fun g w => (hA g).2 w
  -- the generic value-limit lemma for a convergent family of multilinear forms
  have hApply : ∀ (Φ : ℝ → MultilinearMap ℝ (fun _ : Fin 5 => TangentSpace I x) ℝ)
      (L : (Fin 5 → TangentSpace I x) → ℝ) (u : ℝ → Fin 5 → TangentSpace I x)
      (u₀ : Fin 5 → TangentSpace I x) {l : Filter ℝ},
      (∀ w : Fin 5 → TangentSpace I x, Tendsto (fun s => Φ s w) l (𝓝 (L w))) →
        Tendsto u l (𝓝 u₀) → Tendsto (fun s => Φ s (u s)) l (𝓝 (L u₀)) :=
    fun Φ L u u₀ l => tendsto_multilinear_apply (V := TangentSpace I x) (l := l) Φ L u u₀
  -- the fixed-vector estimate, in the `covRm5`/`lapCovRmAt5`/`argNorms` vocabulary
  have hFix : ∀ w : Fin 5 → TangentSpace I x,
      ∃ D : ℝ, HasDerivWithinAt (fun s ↦ covRm5 (G s) x w) D (Set.Ico 0 T) t ∧
        D ≤ lapCovRmAt5 (G t) x w
          + C₀ * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * argNorms (G t) x w := by
    intro w
    obtain ⟨D, hD, hDb⟩ := hFIX G T hRic t ht x (w 0) (w 1) (w 2) (w 3) (w 4)
    refine ⟨D, ?_, ?_⟩
    · simpa only [covRm5] using hD
    · refine le_trans hDb ?_
      have hprod : lapCovRmAt5 (G t) x w
            + C₀ * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
                * argNorms (G t) x w
          = lapCovRmAt (G t) x (w 0) (w 1) (w 2) (w 3) (w 4)
            + C₀ * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
                * (Real.sqrt ((G t).inner x (w 0) (w 0))
                  * Real.sqrt ((G t).inner x (w 1) (w 1))
                  * Real.sqrt ((G t).inner x (w 2) (w 2))
                  * Real.sqrt ((G t).inner x (w 3) (w 3))
                  * Real.sqrt ((G t).inner x (w 4) (w 4))) := by
        rw [lapCovRmAt5, argNorms, Fin.prod_univ_five]
      rw [hprod]
  exact frame_of_fixed (I := I) hLC G T t hRic ht x e edot K hK hON hed hKb C₀ hC₀0
    A hAeval hAbound hApply hFix m i j k l

end Work.Diff.GE
