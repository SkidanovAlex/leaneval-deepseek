import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower
import Submission.Work.BourgainPlan.IonescuWainger.mz_square_function_finsupp

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal BigOperators

set_option maxHeartbeats 1000000

/-- The `enorm` of a complex number is the real absolute value, as an `ℝ≥0∞`. -/
lemma mzSqfun_enorm_complex (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by simp

/-- Every function on `ℤ` is a.e. measurable for the counting measure. -/
lemma mzSqfun_aemeasurable_count (f : ℤ → ℂ) : AEMeasurable f Measure.count := by
  measurability

/-- For `q > 0`, the `q`-th power of the `eLpNorm` with exponent `ENNReal.ofReal q` is the
`lintegral` of the `q`-th power of the `enorm`. -/
lemma mzSqfun_eLpNorm_rpow {q : ℝ} (hq : 0 < q) {α : Type*} [MeasurableSpace α]
    {β : Type*} [TopologicalSpace β] [ENorm β] (f : α → β) (μ : Measure α)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal q) μ ^ q = ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
  have h0 : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq)
  have htop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 htop hf, ENNReal.toReal_ofReal (le_of_lt hq),
    one_div]
  exact ENNReal.rpow_inv_rpow hq.ne' _

/-- Marcinkiewicz–Zygmund / Khintchine square-function lemma (MST arXiv:1512.07518 Lemma 2.30, scalar case), in the shape consumed by the Rademacher–Menshov reduction of the level-`s` maximal function: if every signed combination `Σ_i ε_i (S i g)` of a finite family of `ℂ`-linear Fourier-multiplier operators on finitely supported sequences is `ℓᵖ`-bounded with constant `A`, then the square function `(Σ_i ‖S i g m‖²)^{1/2}` is `ℓᵖ`-bounded by `C·A`, uniformly in the (finite) index type and in the family. -/
theorem mz_finsupp_sqfun {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (S : ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (A : ℝ), 0 ≤ A →
      (∀ ε : ι → Bool, ∀ g : ℤ →₀ ℂ,
        MeasureTheory.eLpNorm (fun m : ℤ => ∑ i : ι, (if ε i then (1 : ℂ) else -1) * (S i g m))
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal A * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p)
              MeasureTheory.Measure.count) →
      ∀ g : ℤ →₀ ℂ,
        MeasureTheory.eLpNorm (fun m : ℤ => ENNReal.ofReal
            (Real.sqrt (∑ i : ι, ‖S i g m‖ ^ 2))) (ENNReal.ofReal p)
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * A) * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p)
              MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := Work.BourgainPlan.IonescuWainger.mz_square_function_finsupp p hp
  refine ⟨C ^ (1/p), Real.rpow_pos_of_pos hCpos _, ?_⟩
  intro ι _ _ S A hA hS g
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hppos : 0 ≤ p := le_of_lt hp0
  have h1p : 0 ≤ 1/p := div_nonneg zero_le_one hppos
  have hofp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  have hofptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hppos
  -- ## The signed-combination hypothesis, in `lintegral` form
  have hT : ∀ (ε : ι → Bool) (f : ℤ →₀ ℂ),
      ∫⁻ y, ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) * S i f y‖ₑ ^ p ∂Measure.count
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ y, ‖(f : ℤ → ℂ) y‖ₑ ^ p ∂Measure.count := by
    intro ε f
    have hh := hS ε f
    have h2 := ENNReal.rpow_le_rpow hh hppos
    rw [mzSqfun_eLpNorm_rpow hp0 _ _ (AEStronglyMeasurable.of_discrete (α := ℤ))] at h2
    rw [ENNReal.mul_rpow_of_nonneg _ _ hppos, ENNReal.ofReal_rpow_of_nonneg hA hppos,
      mzSqfun_eLpNorm_rpow hp0 _ _ (AEStronglyMeasurable.of_discrete (α := ℤ))] at h2
    simpa using h2
  -- ## Universe lowering: replace the index type `ι` by `Fin (Fintype.card ι)`
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hT' : ∀ (ε : Fin (Fintype.card ι) → Bool) (f : ℤ →₀ ℂ),
      ∫⁻ y, ‖∑ k : Fin (Fintype.card ι), (if ε k then (1 : ℂ) else -1)
          * ((S (e.symm k)) : (ℤ →₀ ℂ) → (ℤ → ℂ)) f y‖ₑ ^ p ∂Measure.count
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ y, ‖(f : ℤ → ℂ) y‖ₑ ^ p ∂Measure.count := by
    intro ε f
    have h := hT (fun i => ε (e i)) f
    have hfun : (fun y : ℤ => ‖∑ k : Fin (Fintype.card ι), (if ε k then (1 : ℂ) else -1)
          * ((S (e.symm k)) : (ℤ →₀ ℂ) → (ℤ → ℂ)) f y‖ₑ ^ p)
        = fun y : ℤ => ‖∑ i : ι, (if ε (e i) then (1 : ℂ) else -1) * S i f y‖ₑ ^ p := by
      funext y
      have hsum : (∑ k : Fin (Fintype.card ι), (if ε k then (1 : ℂ) else -1)
            * ((S (e.symm k)) : (ℤ →₀ ℂ) → (ℤ → ℂ)) f y)
          = ∑ i : ι, (if ε (e i) then (1 : ℂ) else -1) * S i f y := by
        rw [← Equiv.sum_comp e (fun k : Fin (Fintype.card ι) => (if ε k then (1 : ℂ) else -1)
            * ((S (e.symm k)) : (ℤ →₀ ℂ) → (ℤ → ℂ)) f y)]
        exact Finset.sum_congr rfl fun i _ => by simp
      rw [hsum]
    rw [hfun]
    exact h
  -- ## Marcinkiewicz–Zygmund for the reindexed family
  have hMZ : (∫⁻ y : ℤ, (∑ k : Fin (Fintype.card ι), ∑ t : Unit,
        ‖((S (e.symm k)) : (ℤ →₀ ℂ) → (ℤ → ℂ)) ((fun _ : Unit => g) t) y‖ₑ ^ (2:ℝ)) ^ (p/2)
        ∂Measure.count)
      ≤ ENNReal.ofReal (C * A ^ p) * ∫⁻ y : ℤ, (∑ t : Unit,
        ‖(((fun _ : Unit => g) t) : ℤ → ℂ) y‖ₑ ^ (2:ℝ)) ^ (p/2) ∂Measure.count :=
    hC (κ := Unit) (fun k => ((S (e.symm k)) : (ℤ →₀ ℂ) → (ℤ → ℂ)))
      (fun k => ⟨fun x y => map_add (S (e.symm k)) x y, fun c x => map_smul (S (e.symm k)) c x⟩)
      (fun _ f => mzSqfun_aemeasurable_count _) A hA hT' (fun _ : Unit => g)
  -- ## Reindexing the square function back to `ι`
  have hPi : (∫⁻ y : ℤ, (∑ k : Fin (Fintype.card ι), ∑ t : Unit,
        ‖((S (e.symm k)) : (ℤ →₀ ℂ) → (ℤ → ℂ)) ((fun _ : Unit => g) t) y‖ₑ ^ (2:ℝ)) ^ (p/2)
        ∂Measure.count)
      = ∫⁻ y : ℤ, (∑ i : ι, ‖S i g y‖ₑ ^ (2:ℝ)) ^ (p/2) ∂Measure.count := by
    apply lintegral_congr
    intro y
    have h1 : (∑ k : Fin (Fintype.card ι), ∑ t : Unit,
          ‖((S (e.symm k)) : (ℤ →₀ ℂ) → (ℤ → ℂ)) ((fun _ : Unit => g) t) y‖ₑ ^ (2:ℝ))
        = ∑ k : Fin (Fintype.card ι), ‖S (e.symm k) g y‖ₑ ^ (2:ℝ) := by simp
    rw [h1, ← Equiv.sum_comp e (fun k : Fin (Fintype.card ι) => ‖S (e.symm k) g y‖ₑ ^ (2:ℝ))]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by simp
  have hQi : (∫⁻ y : ℤ, (∑ t : Unit,
        ‖(((fun _ : Unit => g) t) : ℤ → ℂ) y‖ₑ ^ (2:ℝ)) ^ (p/2) ∂Measure.count)
      = ∫⁻ y : ℤ, ‖(g : ℤ → ℂ) y‖ₑ ^ p ∂Measure.count := by
    apply lintegral_congr
    intro y
    have h1 : (∑ t : Unit, ‖(((fun _ : Unit => g) t) : ℤ → ℂ) y‖ₑ ^ (2:ℝ))
        = ‖(g : ℤ → ℂ) y‖ₑ ^ (2:ℝ) := by simp
    rw [h1, ← ENNReal.rpow_mul _ 2 (p/2)]
    congr 1
    ring
  have hMZ' : (∫⁻ y : ℤ, (∑ i : ι, ‖S i g y‖ₑ ^ (2:ℝ)) ^ (p/2) ∂Measure.count)
      ≤ ENNReal.ofReal (C * A ^ p) * ∫⁻ y : ℤ, ‖(g : ℤ → ℂ) y‖ₑ ^ p ∂Measure.count := by
    rw [← hPi, ← hQi]
    exact hMZ
  -- ## The square function, in `lintegral` form
  have hpoint : ∀ m : ℤ, ‖ENNReal.ofReal (Real.sqrt (∑ i : ι, ‖S i g m‖ ^ 2))‖ₑ ^ p
      = (∑ i : ι, ‖S i g m‖ₑ ^ (2:ℝ)) ^ (p/2) := by
    intro m
    rw [enorm_eq_self]
    have ht : 0 ≤ ∑ i : ι, ‖S i g m‖ ^ 2 := by positivity
    have hsumpow : (Real.sqrt (∑ i : ι, ‖S i g m‖ ^ 2)) ^ p
        = (∑ i : ι, ‖S i g m‖ ^ 2) ^ (p/2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht (1/2) p]
      congr 1
      ring
    have hsum : ENNReal.ofReal (∑ i : ι, ‖S i g m‖ ^ 2) = ∑ i : ι, ‖S i g m‖ₑ ^ (2:ℝ) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      exact Finset.sum_congr rfl fun i _ => by
        rw [mzSqfun_enorm_complex, ENNReal.ofReal_pow (norm_nonneg _) 2, ENNReal.rpow_two]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hppos, hsumpow,
      ← ENNReal.ofReal_rpow_of_nonneg ht (by linarith : 0 ≤ p/2), hsum]
  have hmain : eLpNorm (fun m : ℤ => ENNReal.ofReal (Real.sqrt (∑ i : ι, ‖S i g m‖ ^ 2)))
        (ENNReal.ofReal p) Measure.count
      = (∫⁻ m : ℤ, (∑ i : ι, ‖S i g m‖ₑ ^ (2:ℝ)) ^ (p/2) ∂Measure.count) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hofp0 hofptop AEStronglyMeasurable.of_discrete, htoReal]
    congr 1
    exact lintegral_congr hpoint
  have hg : eLpNorm (⇑g) (ENNReal.ofReal p) Measure.count
      = (∫⁻ m : ℤ, ‖(g : ℤ → ℂ) m‖ₑ ^ p ∂Measure.count) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hofp0 hofptop AEStronglyMeasurable.of_discrete, htoReal]
  have hconst : (ENNReal.ofReal (C * A ^ p)) ^ (1/p) = ENNReal.ofReal (C ^ (1/p) * A) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (le_of_lt hCpos) (Real.rpow_nonneg hA p)) h1p]
    congr 1
    rw [Real.mul_rpow (le_of_lt hCpos) (Real.rpow_nonneg hA p), ← Real.rpow_mul hA p (1/p),
      mul_one_div_cancel hp0.ne', Real.rpow_one]
  rw [hmain, hg]
  calc ((∫⁻ m : ℤ, (∑ i : ι, ‖S i g m‖ₑ ^ (2:ℝ)) ^ (p/2) ∂Measure.count) ^ (1/p))
      ≤ (ENNReal.ofReal (C * A ^ p)
          * ∫⁻ m : ℤ, ‖(g : ℤ → ℂ) m‖ₑ ^ p ∂Measure.count) ^ (1/p) :=
        ENNReal.rpow_le_rpow hMZ' h1p
    _ = (ENNReal.ofReal (C * A ^ p)) ^ (1/p)
          * (∫⁻ m : ℤ, ‖(g : ℤ → ℂ) m‖ₑ ^ p ∂Measure.count) ^ (1/p) :=
        ENNReal.mul_rpow_of_nonneg _ _ h1p
    _ = ENNReal.ofReal (C ^ (1/p) * A)
          * (∫⁻ m : ℤ, ‖(g : ℤ → ℂ) m‖ₑ ^ p ∂Measure.count) ^ (1/p) := by
        rw [hconst]

end Work.BourgainPlan.Maximal
