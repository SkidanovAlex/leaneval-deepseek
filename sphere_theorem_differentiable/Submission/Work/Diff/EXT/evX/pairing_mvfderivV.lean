import Mathlib
import Submission.Work.Diff.EXT.reactBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evX

/-! Scoped instances on the fibers of a Riemannian bundle live in the `Bundle` scope, so `inner`
on a tangent space (the same object as `g.inner`) needs this open. -/
open Bundle

/-- **Metric compatibility against the pairing with a `g`-parallel field.**  For a smooth metric `g`
with smooth Levi-Civita connection (`hLC`), a frame family `e` that is `g`-parallel at `y`
(`hgeo : ∇(e i) = 0` at `y`) and smooth fields `P`, `X`, the derivative of the pairing
`z ↦ ⟪e i z, P z⟫_g` at `y` in direction `X y` is the pairing of `e i y` with `∇_{X y} P`:
the term `⟪∇_{X y} e i, P y⟫` vanishes by `hgeo` and the second term is the Leibniz rule of
`IsMetricCompatible (lcOf g)`. -/
theorem pairing_mvfderivV
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (P : Work.Diff.EXT.TField (I := I) (M := M))
    (hP : Work.Diff.GE.SmoothFieldT (I := I) (M := M) P)
    (X : Work.Diff.EXT.TField (I := I) (M := M))
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (i : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun z => g.inner z (e i z) (P z)) y (X y)
      = g.inner y (e i y) (Work.Diff.EXT.dirF g P X y) := by
  -- Work with the metric `g` as the instance metric on the fibers, so that `g.inner = inner ℝ`
  -- and `lcOf g` is Mathlib's Levi-Civita connection of that instance metric (`LCSmooth`).
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible (Submission.Diff.lcOf g) :=
    (hLC g).2.2
  -- the Leibniz rule `X⟪e i, P⟫ = ⟪∇_X e i, P⟫ + ⟪e i, ∇_X P⟫`
  have hm := hmet (e i) P (he i) hP y (X y)
  -- the first term vanishes because `∇(e i) = 0` at `y`
  have hz : Submission.Diff.lcOf g (e i) y (X y) = 0 := by rw [hgeo i]; rfl
  change mvfderiv I (fun z : M => inner ℝ (e i z) (P z)) y (X y)
      = inner ℝ (e i y) (Submission.Diff.lcOf g P y (X y))
  rw [hm, hz]
  simp

end Work.Diff.EXT.evX
