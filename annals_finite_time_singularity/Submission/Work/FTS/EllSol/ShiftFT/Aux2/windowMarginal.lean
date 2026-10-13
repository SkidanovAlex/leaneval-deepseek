import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.marginal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.EllSol.ShiftFT.Aux2

/-- Window/marginal Fubini–monotonicity, the `≤`-analogue of `marginal`'s `marginal_aux`.

Let `f` be jointly integrable on `μ.prod ν` and nonnegative there.  For any measurable `A`
the marginal `y ↦ ∫ x in A, f x y ∂μ` is `ν`-integrable, and its integral is at most the
joint integral: restricting the inner integration to the measurable window `A` can only
decrease the value, by monotonicity of the integral in the domain for nonnegative
integrands.  (The indicator `1_{A × univ}` is applied to `f` and Fubini is used twice.) -/
private theorem window_le_aux {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {A : Set α} (hA : MeasurableSet A) (f : α → β → ℝ)
    (hf : Integrable (fun p : α × β => f p.1 p.2) (μ.prod ν))
    (h0 : 0 ≤ᵐ[μ.prod ν] fun p : α × β => f p.1 p.2) :
    Integrable (fun y => ∫ x in A, f x y ∂μ) ν ∧
      ∫ y, (∫ x in A, f x y ∂μ) ∂ν ≤ ∫ p, f p.1 p.2 ∂(μ.prod ν) := by
  classical
  set F : α × β → ℝ := fun p => f p.1 p.2 with hF
  set F' : α × β → ℝ := (A ×ˢ Set.univ).indicator F with hF'
  have hAsm : MeasurableSet (A ×ˢ (Set.univ : Set β)) := hA.prod MeasurableSet.univ
  have hF_int : Integrable F (μ.prod ν) := hf
  have hF'_int : Integrable F' (μ.prod ν) := by
    refine Integrable.mono' hF_int.norm (hF_int.aestronglyMeasurable.indicator hAsm) ?_
    filter_upwards with p
    rw [hF', Set.indicator_apply]
    split_ifs with hp
    · exact le_rfl
    · simp
  have hkey : ∀ (x : α) (y : β), F' (x, y) = A.indicator (fun x => f x y) x := by
    intro x y
    by_cases h : x ∈ A
    · rw [hF', Set.indicator_of_mem (show (x, y) ∈ A ×ˢ (Set.univ : Set β) from ⟨h, Set.mem_univ _⟩),
        hF, Set.indicator_of_mem h]
    · rw [hF', Set.indicator_of_notMem (show (x, y) ∉ A ×ˢ (Set.univ : Set β) from fun hp => h hp.1),
        Set.indicator_of_notMem h]
  have hfun : (fun y => ∫ x, F' (x, y) ∂μ) = fun y => ∫ x in A, f x y ∂μ := by
    funext y
    rw [← integral_indicator hA]
    exact integral_congr_ae (Eventually.of_forall fun x => hkey x y)
  constructor
  · have h1 : Integrable (fun y => ∫ x, F' (x, y) ∂μ) ν := hF'_int.integral_prod_right
    rwa [hfun] at h1
  · have hprod' : ∫ p, F' p ∂(μ.prod ν) = ∫ y, ∫ x, F' (x, y) ∂μ ∂ν :=
      integral_prod_symm F' hF'_int
    have hEq : ∫ y, (∫ x, F' (x, y) ∂μ) ∂ν = ∫ y, (∫ x in A, f x y ∂μ) ∂ν := by
      rw [hfun]
    have hle : F' ≤ᵐ[μ.prod ν] F := by
      filter_upwards [h0] with p hp
      rw [hF', Set.indicator_apply]
      split_ifs with h
      · rfl
      · exact hp
    have hmono : ∫ p, F' p ∂(μ.prod ν) ≤ ∫ p, F p ∂(μ.prod ν) :=
      integral_mono_ae hF'_int hF_int hle
    calc ∫ y, (∫ x in A, f x y ∂μ) ∂ν
        = ∫ y, (∫ x, F' (x, y) ∂μ) ∂ν := hEq.symm
      _ = ∫ p, F' p ∂(μ.prod ν) := hprod'.symm
      _ ≤ ∫ p, F p ∂(μ.prod ν) := hmono
      _ = ∫ p, f p.1 p.2 ∂(μ.prod ν) := by rw [hF]

theorem windowMarginal (b N : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hJ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.Integrable (fun θ => (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (Work.Spaces.pz u s θ - b * u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    ∧ (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (Work.Spaces.pz u s θ - b * u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
      ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2 := by
  classical
  have _ := hu
  -- The product measure `volume.prod (volume.restrict Iθ)` is the volume of `univ ×ˢ Iθ`.
  have hmeas : (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ) :
      MeasureTheory.Measure (ℝ × ℝ)) = MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have h := MeasureTheory.Measure.prod_restrict (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (Set.univ : Set ℝ) Work.Spaces.Iθ
    rw [MeasureTheory.Measure.restrict_univ] at h
    exact h
  -- Joint integrability of the shifted square against `wE`.
  have hf : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ) :
        MeasureTheory.Measure (ℝ × ℝ)) := by
    rw [hmeas]
    exact hJ
  -- The integrand is nonnegative on the strip (as `wE ≥ 0` on `Iθ`).
  have h0 : 0 ≤ᵐ[(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ) :
        MeasureTheory.Measure (ℝ × ℝ))]
      (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2) := by
    rw [hmeas]
    refine (MeasureTheory.ae_restrict_iff' ?_).2 (Filter.Eventually.of_forall ?_)
    · exact MeasurableSet.univ.prod measurableSet_Icc
    · intro p hp
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)
  -- `wE θ` is a constant for the inner (`s`-)integration.
  have hinner : ∀ θ : ℝ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (Work.Spaces.pz u s θ - b * u s θ) ^ 2 * Work.FTS.EllSol.FlatFT.wE θ)
      = (∫ s in Set.Icc (-(2 * N)) (2 * N), (Work.Spaces.pz u s θ - b * u s θ) ^ 2)
        * Work.FTS.EllSol.FlatFT.wE θ := fun θ => integral_mul_const _ _
  obtain ⟨hInt, hineq⟩ := window_le_aux
    (μ := MeasureTheory.volume) (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (A := Set.Icc (-(2 * N)) (2 * N)) measurableSet_Icc
    (fun s θ => (Work.Spaces.pz u s θ - b * u s θ) ^ 2 * Work.FTS.EllSol.FlatFT.wE θ) hf h0
  refine ⟨hInt.congr (Filter.Eventually.of_forall hinner), ?_⟩
  calc (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (Work.Spaces.pz u s θ - b * u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ s in Set.Icc (-(2 * N)) (2 * N),
          (Work.Spaces.pz u s θ - b * u s θ) ^ 2 * Work.FTS.EllSol.FlatFT.wE θ := by
        apply integral_congr_ae
        filter_upwards with θ
        exact (hinner θ).symm
    _ ≤ ∫ p, (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2
          ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ) :
            MeasureTheory.Measure (ℝ × ℝ)) := hineq
    _ = ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2 := by
        rw [hmeas]

end Work.FTS.EllSol.ShiftFT.Aux2
