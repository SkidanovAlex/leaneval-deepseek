import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.oscillation_reduction
import Submission.Work.BourgainPlan.Oscillation.discAvg_eq_fourier

/-!
# The `ℕ → ℤ` transfer of the oscillation functional

`oscFunctional` is the block-oscillation functional of the polynomial averages `discAvg P N g`
on `ℕ`; `oscZ` is the same functional for an abstract family of operators on `ℤ`.  Bourgain's
circle-method argument produces its estimate for the Fourier-integral operator `polyWeylOp` on
`ℤ`, so the two must be compared.

This file proves that comparison.  On the nose,

`discAvg P N g n = polyWeylOp P (liftZC g) (liftFinset s) N (n : ℤ)`  for every `n : ℕ`

(`discAvg_eq_polyWeylOp`), both sides being the `n`-th Fourier coefficient of the product of the
Weyl kernel with the finite Fourier series of `g`.  Consequently the `ℕ`-integral of the block
supremum is bounded by the `ℤ`-integral of the corresponding block supremum of `polyWeylOp`,
which is `oscFunctional_le_oscZ_weyl`.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

open Work.BourgainPlan.Maximal

/-! ## Elementary norm computations -/

/-- `‖z‖ₑ = ofReal ‖z‖` for a complex number. -/
lemma enorm_complex_eq_ofReal_norm (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  simp [enorm_eq_nnnorm]

/-- `‖r‖ₑ = ofReal ‖r‖` for a real number. -/
lemma enorm_real_eq_ofReal_norm (r : ℝ) : ‖r‖ₑ = ENNReal.ofReal ‖r‖ :=
  (ofReal_norm (x := r)).symm

/-- The norm of a real number seen as a complex number is its absolute value. -/
lemma norm_ofReal_eq_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- The `ℝ`-enorm of a difference of reals equals the `ℂ`-enorm of the difference of the
complexified terms. -/
lemma enorm_real_sub_eq (a b : ℝ) : ‖a - b‖ₑ = ‖(a : ℂ) - (b : ℂ)‖ₑ := by
  rw [enorm_real_eq_ofReal_norm, enorm_complex_eq_ofReal_norm,
    show (a : ℂ) - (b : ℂ) = ((a - b : ℝ) : ℂ) by push_cast; ring,
    norm_ofReal_eq_abs, Real.norm_eq_abs]

/-! ## The conjugate Weyl kernel -/

/-- Conjugate form of the Weyl kernel (needed because `polyWeylOp` uses the conjugate kernel). -/
lemma conj_polyWeylKernel' (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) :
    starRingEnd ℂ (polyWeylKernel P N θ)
      = ((N : ℂ))⁻¹ * ∑ i ∈ Finset.range N,
          Complex.exp (-(2 * Real.pi * Complex.I * (((P.eval (i : ℤ) : ℤ) : ℝ) * θ))) := by
  rw [polyWeylKernel, map_mul, map_sum]
  congr 1
  · rw [map_inv₀, Complex.conj_ofReal]
    push_cast
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring

/-- The middle Fourier sum over the transported support `liftFinset s` collapses onto the
original sum over `s`. -/
lemma sum_liftFinset (g : ℕ → ℝ) (s : Finset ℕ) (θ : ℝ) :
    (∑ j ∈ liftFinset s,
        liftZC g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
      = ∑ m ∈ s, (g m : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)) := by
  have hinj : Set.InjOn (fun n : ℕ => (n : ℤ)) (↑s) := fun x _ y _ h => Int.ofNat_injective h
  rw [liftFinset, Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [liftZC_of_nonneg g (Int.natCast_nonneg m), Int.toNat_natCast]
  congr 1

/-! ## The pointwise identity -/

/-- **The discrete polynomial average is the Weyl-kernel operator on `ℤ`.**  Both sides are the
`n`-th Fourier coefficient of the product of the conjugated Weyl kernel with the finite Fourier
series of `g` (`discAvg_eq_fourier` on the left, the definition of `polyWeylOp` on the right). -/
lemma discAvg_eq_polyWeylOp (P : Polynomial ℤ) (hP : Submission.BourgainPlan.NonnegOnNat P)
    (N : ℕ) (g : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n, n ∉ s → g n = 0) (n : ℕ) :
    (Submission.BourgainPlan.discAvg P N g n : ℂ)
      = polyWeylOp P (liftZC g) (liftFinset s) N (n : ℤ) := by
  rw [discAvg_eq_fourier P hP N g s hs n, polyWeylOp]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only []
  rw [conj_polyWeylKernel', sum_liftFinset]
  push_cast
  ring

/-! ## The transfer of the oscillation functional -/

/-- **The `ℕ → ℤ` transfer.**  The block-oscillation functional of the polynomial averages on
`ℕ` is dominated by the block-oscillation functional of the Weyl-kernel operators on `ℤ`, at the
lacunary scales `⌊ρ^i⌋`.  The pointwise identity `discAvg_eq_polyWeylOp` identifies the
integrands on the nonnegative integers, and the `ℤ`-integral of a nonnegative function dominates
the `ℕ`-integral (`lintegral_count` + `ENNReal.tsum_comp_le_tsum_of_injective`). -/
theorem oscFunctional_le_oscZ_weyl (P : Polynomial ℤ)
    (hP : Submission.BourgainPlan.NonnegOnNat P)
    (ρ : ℝ) (J : ℕ) (k : ℕ → ℕ) (g : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∀ n, n ∉ s → g n = 0) :
    Work.BourgainPlan.Oscillation.oscFunctional P ρ J k g
      ≤ Work.BourgainPlan.Oscillation.oscZ (fun i x =>
          Work.BourgainPlan.Oscillation.polyWeylOp P
            (Work.BourgainPlan.Oscillation.liftZC g)
            (Work.BourgainPlan.Oscillation.liftFinset s)
            (Work.BourgainPlan.Oscillation.lacScale ρ i) x) J k := by
  have key : ∀ (N : ℕ) (a : ℕ),
      (Submission.BourgainPlan.discAvg P N g a : ℂ)
        = polyWeylOp P (liftZC g) (liftFinset s) N (a : ℤ) :=
    fun N a => discAvg_eq_polyWeylOp P hP N g s hs a
  rw [oscFunctional, oscZ]
  simp only [lacScale]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [lintegral_count]
  rw [lintegral_count]
  refine (tsum_congr (fun a => ?_)).trans_le
    (ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ => (n : ℤ))
      Int.ofNat_injective _)
  have hsup : (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖Submission.BourgainPlan.discAvg P ⌊ρ ^ i⌋₊ g a
          - Submission.BourgainPlan.discAvg P ⌊ρ ^ k j⌋₊ g a‖ₑ)
      = (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖polyWeylOp P (liftZC g) (liftFinset s) ⌊ρ ^ i⌋₊ (a : ℤ)
          - polyWeylOp P (liftZC g) (liftFinset s) ⌊ρ ^ k j⌋₊ (a : ℤ)‖ₑ) := by
    apply iSup_congr; intro i
    apply iSup_congr; intro _
    rw [enorm_real_sub_eq, key ⌊ρ ^ i⌋₊ a, key ⌊ρ ^ k j⌋₊ a]
  rw [hsup]

end

end Work.BourgainPlan.Oscillation
