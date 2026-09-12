import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.RingTheory.Finiteness.Prod

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise BigOperators

namespace Commons.Analysis.MeasureTheory

/-- The `ℝ`-axis `{x | x.ofLp.2 = 0}` inside `WithLp 2 (ℝ × W)`, as a linear subspace. -/
private def axisSub (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] :
    Submodule ℝ (WithLp 2 (ℝ × W)) where
  carrier := {x : WithLp 2 (ℝ × W) | x.ofLp.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x.ofLp.2 = 0 at hx
    change y.ofLp.2 = 0 at hy
    rw [WithLp.ofLp_snd] at hx hy
    change (x + y).ofLp.2 = 0
    simp [hx, hy]
  smul_mem' := by
    intro a x hx
    change x.ofLp.2 = 0 at hx
    rw [WithLp.ofLp_snd] at hx
    change (a • x).ofLp.2 = 0
    simp [hx]

/-- The axis is a proper subspace when `W` is nontrivial. -/
private lemma axisSub_ne_top (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [Nontrivial W] : axisSub W ≠ ⊤ := by
  intro htop
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  let x : WithLp 2 (ℝ × W) := WithLp.toLp 2 (0, w)
  have hx : x ∈ axisSub W := by
    rw [htop]
    simp
  change x.ofLp.2 = 0 at hx
  have hxval : x.ofLp.2 = w := by simp [x]
  rw [hxval] at hx
  exact hw hx

lemma sphere_coordinate_poles_null
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] :
    (MeasureTheory.volume.toSphere : MeasureTheory.Measure
        (Metric.sphere (0 : WithLp 2 (ℝ × W)) 1))
      {θ : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1 |
        ((θ : WithLp 2 (ℝ × W)).ofLp.2 : W) = 0} = 0 := by
  let P : Set (Metric.sphere (0 : WithLp 2 (ℝ × W)) 1) :=
    {θ : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1 | ((θ : WithLp 2 (ℝ × W)).ofLp.2 : W) = 0}
  change (MeasureTheory.volume.toSphere : MeasureTheory.Measure
      (Metric.sphere (0 : WithLp 2 (ℝ × W)) 1)) P = 0
  -- measurability of P (as the preimage of the axis, which is closed)
  have hSmeas : MeasurableSet (Metric.sphere (0 : WithLp 2 (ℝ × W)) 1 : Set (WithLp 2 (ℝ × W))) :=
    isClosed_sphere.measurableSet
  have hemb : MeasurableEmbedding
      (Subtype.val : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1 → WithLp 2 (ℝ × W)) :=
    MeasurableEmbedding.subtype_coe hSmeas
  have haxism : MeasurableSet (axisSub W : Set (WithLp 2 (ℝ × W))) :=
    (Submodule.closed_of_finiteDimensional (axisSub W)).measurableSet
  have hPmeas : MeasurableSet P := by
    have hpre : P = (Subtype.val : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1 → WithLp 2 (ℝ × W)) ⁻¹'
        (axisSub W : Set (WithLp 2 (ℝ × W))) := by
      ext θ
      constructor
      · intro h; exact h
      · intro h; exact h
    rw [hpre]
    exact hemb.measurable haxism
  -- the cone over the poles is contained in the axis (which has zero volume)
  have hCsub : Ioo (0 : ℝ) 1 •
        ((Subtype.val : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1 → WithLp 2 (ℝ × W)) '' P) ⊆
      (axisSub W : Set (WithLp 2 (ℝ × W))) := by
    intro z hz
    rw [Set.mem_smul] at hz
    rcases hz with ⟨r, hr, y, hy, rfl⟩
    rcases hy with ⟨θ, hθ, rfl⟩
    exact (axisSub W).smul_mem r (by
      change (θ : WithLp 2 (ℝ × W)).ofLp.2 = 0
      exact hθ)
  have haxisvol : volume (axisSub W : Set (WithLp 2 (ℝ × W))) = 0 := by
    exact Measure.addHaar_submodule (μ := (volume : Measure (WithLp 2 (ℝ × W))))
      (s := axisSub W) (axisSub_ne_top W)
  have hCvol : volume (Ioo (0 : ℝ) 1 •
        ((Subtype.val : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1 → WithLp 2 (ℝ × W)) '' P)) = 0 := by
    refine le_antisymm ?_ zero_le
    simpa [haxisvol] using (measure_mono hCsub : volume (Ioo (0 : ℝ) 1 •
        ((Subtype.val : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1 → WithLp 2 (ℝ × W)) '' P)) ≤
      volume (axisSub W : Set (WithLp 2 (ℝ × W))))
  -- apply the defining formula for the sphere measure
  rw [Measure.toSphere_apply' (μ := (volume : Measure (WithLp 2 (ℝ × W)))) (s := P) hPmeas]
  simp [hCvol]

end Commons.Analysis.MeasureTheory