import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.MeasureTheory.interval_density_integral_tau

open Set Filter MeasureTheory Measure
open scoped ENNReal NNReal

noncomputable section

namespace Commons.Analysis.MeasureTheory

/-- `Measure.comap` along the subtype inclusion of a measurable set is s-finite
whenever the original measure is. -/
private lemma sfinite_comap_subtype {α} [MeasurableSpace α] {s : Set α} (hs : MeasurableSet s)
    {μ : Measure α} [SFinite μ] : SFinite (μ.comap (Subtype.val : s → α)) := by
  let m : ℕ → Measure s := fun n => (sfiniteSeq μ n).comap (Subtype.val : s → α)
  have hfin : ∀ n, IsFiniteMeasure (m n) := by
    intro n; dsimp [m]; infer_instance
  have hsum : μ.comap (Subtype.val : s → α) = Measure.sum m := by
    ext A hA
    rw [Measure.sum_apply _ hA]
    simp_rw [m]
    rw [show (fun n : ℕ => (sfiniteSeq μ n).comap (Subtype.val : s → α) A) =
        fun n : ℕ => (sfiniteSeq μ n) ((Subtype.val : s → α) '' A) by
          funext n
          exact comap_subtype_coe_apply hs (sfiniteSeq μ n) A]
    rw [← Measure.sum_apply_of_countable]
    rw [sum_sfiniteSeq]
    exact comap_subtype_coe_apply hs μ A
  exact ⟨m, hfin, hsum⟩

lemma sphere_coordinate_cylinder
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] (F : ℝ → ℝ) :
    let E := WithLp 2 (ℝ × W)
    let SW := Metric.sphere (0 : W) 1
    let expo : ℝ := (((Module.finrank ℝ W : ℝ) - 2) / 2)
    let rho : ℝ → ℝ := fun t => (1 - t ^ 2) ^ expo
    let It := {t : ℝ // t ∈ Set.Ioo (-1) 1}
    let tau : MeasureTheory.Measure ℝ :=
      (MeasureTheory.volume.restrict (Set.Ioo (-1) 1)).withDensity
        (fun t => ENNReal.ofReal (rho t))
    let cylμ : MeasureTheory.Measure (It × SW) :=
      (tau.comap (Subtype.val : It → ℝ)).prod (MeasureTheory.volume.toSphere)
    (∫ q : It × SW, F q.1.1 ∂cylμ) =
    (∫ t : ℝ in Set.Ioo (-1) 1,
      (∫ ω : SW, F t * rho t ∂MeasureTheory.volume.toSphere)) := by
  let SW : Set W := Metric.sphere (0 : W) 1
  let expo : ℝ := (((Module.finrank ℝ W : ℝ) - 2) / 2)
  let rho : ℝ → ℝ := fun t => (1 - t ^ 2) ^ expo
  let It : Type := {t : ℝ // t ∈ Set.Ioo (-1) 1}
  let tau : Measure ℝ :=
      (volume.restrict (Set.Ioo (-1) 1)).withDensity (fun t => ENNReal.ofReal (rho t))
  let σW : Measure (Metric.sphere (0 : W) 1) := volume.toSphere
  let cW : ℝ := σW.real univ
  change (∫ q : It × Metric.sphere (0 : W) 1, F q.1.1
      ∂((tau.comap (Subtype.val : It → ℝ)).prod σW)) =
    (∫ t : ℝ in Set.Ioo (-1) 1,
      (∫ ω : Metric.sphere (0 : W) 1, F t * rho t ∂σW))
  let μIt : Measure It := tau.comap (Subtype.val : It → ℝ)
  haveI : SFinite μIt := by
    dsimp [μIt]
    simpa [It] using
      (sfinite_comap_subtype (s := (Set.Ioo (-1 : ℝ) 1)) (hs := measurableSet_Ioo) (μ := tau))
  -- LHS: first integrate out the sphere factor (integrand independent of ω),
  -- routing through the swapped product so that s-finiteness of the sphere measure
  -- (finite, automatic) and of `μIt` (proved above) suffice.
  have hprod : (∫ q : It × Metric.sphere (0 : W) 1, F q.1.1 ∂(μIt.prod σW)) =
      cW * (∫ t : It, F (t : ℝ) ∂μIt) := by
    let f : Metric.sphere (0 : W) 1 × It → ℝ := fun w => F ((w.2 : It) : ℝ)
    have hsw := integral_prod_swap (α := Metric.sphere (0 : W) 1) (β := It) (μ := σW) (ν := μIt)
      (f := f)
    have hleft : (∫ q : It × Metric.sphere (0 : W) 1, F q.1.1 ∂(μIt.prod σW)) =
        ∫ q : It × Metric.sphere (0 : W) 1, f q.swap ∂(μIt.prod σW) := by
      apply integral_congr_ae
      filter_upwards with q
      rfl
    have hright : (∫ z : Metric.sphere (0 : W) 1 × It, f z ∂(σW.prod μIt)) =
        σW.real univ • (∫ t : It, F (t : ℝ) ∂μIt) := by
      have hsn := integral_fun_snd (μ := σW) (ν := μIt)
        (f := fun t : It => F (t : ℝ))
      calc
        (∫ z : Metric.sphere (0 : W) 1 × It, f z ∂(σW.prod μIt))
            = ∫ z : Metric.sphere (0 : W) 1 × It, (fun t : It => F (t : ℝ)) z.2
                ∂(σW.prod μIt) := by
              apply integral_congr_ae
              filter_upwards with z
              rfl
        _ = σW.real univ • (∫ t : It, F (t : ℝ) ∂μIt) := hsn
    calc
      (∫ q : It × Metric.sphere (0 : W) 1, F q.1.1 ∂(μIt.prod σW))
          = ∫ q : It × Metric.sphere (0 : W) 1, f q.swap ∂(μIt.prod σW) := hleft
      _ = ∫ z : Metric.sphere (0 : W) 1 × It, f z ∂(σW.prod μIt) := hsw
      _ = σW.real univ • (∫ t : It, F (t : ℝ) ∂μIt) := hright
      _ = cW * (∫ t : It, F (t : ℝ) ∂μIt) := by
          simp [cW, smul_eq_mul]
  -- τ-comap integral equals density-weighted Lebesgue integral over the interval
  have htau : (∫ t : It, F (t : ℝ) ∂μIt) =
      ∫ t : ℝ in Set.Ioo (-1) 1, F t * rho t := by
    dsimp [μIt]
    simpa [It, tau, rho, expo] using
      (interval_density_integral_tau (W := W) (F := F))
  -- RHS: inner integral over the sphere of the constant (in ω) integrand
  have hin : ∀ t : ℝ, (∫ ω : Metric.sphere (0 : W) 1, F t * rho t ∂σW) = (F t * rho t) * cW := by
    intro t
    rw [integral_const]
    simp [cW, smul_eq_mul]
    ring
  have hRHS : (∫ t : ℝ in Set.Ioo (-1) 1,
      (∫ ω : Metric.sphere (0 : W) 1, F t * rho t ∂σW)) =
      cW * (∫ t : ℝ in Set.Ioo (-1) 1, F t * rho t) := by
    calc
      (∫ t : ℝ in Set.Ioo (-1) 1,
          (∫ ω : Metric.sphere (0 : W) 1, F t * rho t ∂σW))
          = ∫ t : ℝ in Set.Ioo (-1) 1, (F t * rho t) * cW := by
            apply setIntegral_congr_fun measurableSet_Ioo ?_
            intro t ht
            exact hin t
      _ = (∫ t : ℝ in Set.Ioo (-1) 1, F t * rho t) * cW := by
            simpa using (integral_mul_const (μ := volume.restrict (Set.Ioo (-1 : ℝ) 1))
              (r := cW) (f := fun t : ℝ => F t * rho t))
      _ = cW * (∫ t : ℝ in Set.Ioo (-1) 1, F t * rho t) := by ring
  calc
    (∫ q : It × Metric.sphere (0 : W) 1, F q.1.1 ∂(μIt.prod σW))
        = cW * (∫ t : ℝ in Set.Ioo (-1) 1, F t * rho t) := by
            rw [hprod, htau]
    _ = (∫ t : ℝ in Set.Ioo (-1) 1,
        (∫ ω : Metric.sphere (0 : W) 1, F t * rho t ∂σW)) := by
            rw [← hRHS]

end Commons.Analysis.MeasureTheory