import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.kernelExpandedAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.block3Row2_expanded`

The **third block, second row** of the expanded `Q₂` pair row: the honest pair kernel
`Σ_k pinQ_k(w)·conj(pinQ_k y)` of the row is replaced by its four-term lattice expansion
`K1exp v μ N (fun _ => 1) w y` (`Work.BoseBoxFock.pinQ_kernel_one`).

The row is a *single-slot* row (`Σ_{j : Fin n}`, one coordinate update), so the passage is:

* the finite sum `Σ_k` is moved inside the *double* iterated integral
  (`Work.BoseBoxFock.sum_mul_iterated_double_eq`, whose integrability input is supplied here by
  `integrable_state_double`);
* the pointwise kernel identity `Σ_k pinQ_k(w)·conj(pinQ_k y) = K1exp … (fun _ => 1) w y`
  (`Work.BoseBoxFock.pinQ_kernel_one`) is then applied under the integral.

The real scalar `E.mu·E.W1 0` factors out of the `Σ_k` and re-enters through
`MeasureTheory.integral_const_mul`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option maxHeartbeats 1000000

/-! ## 1. The `L¹` criterion on the double box product -/

/-- A measurable integrand which is everywhere bounded and vanishes off
`boxPow n ℓ ×ˢ boxL ℓ` is integrable for the product measure `vXn n ⊗ volume`. -/
theorem integrable_on_box2 {n : ℕ} {ℓ : ℝ} {f : Xn n × Ω → ℂ}
    (hfm : AEStronglyMeasurable f ((vXn n).prod (volume : Measure Ω))) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C)
    (hsupp : ∀ z, z ∉ Work.MB.boxPow n ℓ ×ˢ boxL ℓ → f z = 0) :
    Integrable f ((vXn n).prod (volume : Measure Ω)) :=
  Work.MB.integrable_of_bdd_of_support
    ((Work.MB.measurableSet_boxPow n ℓ).prod (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ))
    (by
      rw [MeasureTheory.Measure.prod_prod]
      exact ENNReal.mul_ne_top (Work.MB.volume_boxPow_lt_top n ℓ) (kernelFormAux_boxL_ne_top ℓ))
    hfm hC hsupp

/-! ## 2. The canonical single-slot integrand -/

/-- **The canonical double integrand is integrable on the product space.**  For measurable,
everywhere bounded `α`, `β` and a measurable state `Θ` supported in the `n`-particle box
`boxPow n ℓ`, the function `z ↦ conj Θ(z.1)·α(z.1)·β(z.2)·Θ(z.1[i↦z.2])` is `L¹` for
`vXn n ⊗ volume`.

The support of the integrand is contained in `boxPow n ℓ ×ˢ boxL ℓ`: the factor `conj Θ(z.1)`
carries the `x`-support, and if `z.2 ∉ boxL ℓ` then the coordinate-`i` update of `z.1` leaves the
box, so `Θ` vanishes there. -/
theorem integrable_state_double {n : ℕ} {ℓ : ℝ} {Θ α : Xn n → ℂ} {β : Ω → ℂ} {i : Fin n}
    {Cα Cβ CΘ : ℝ} (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hCΘ : 0 ≤ CΘ)
    (hαm : Measurable α) (hαb : ∀ x, ‖α x‖ ≤ Cα)
    (hβm : Measurable β) (hβb : ∀ z, ‖β z‖ ≤ Cβ)
    (hΘm : Measurable Θ) (hΘb : ∀ z, ‖Θ z‖ ≤ CΘ)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) :
    Integrable (fun z : Xn n × Ω =>
      (starRingEnd ℂ) (Θ z.1) * α z.1 * β z.2 * Θ (Function.update z.1 i z.2))
      ((vXn n).prod (volume : Measure Ω)) := by
  refine integrable_on_box2 (ℓ := ℓ) ?_ (C := CΘ * Cα * Cβ * CΘ) ?_ ?_
  · have hupd : Measurable (fun z : Xn n × Ω => Function.update z.1 i z.2) := by
      rw [measurable_pi_iff]
      intro m
      have hpt : ∀ z : Xn n × Ω,
          Function.update z.1 i z.2 m = if m = i then z.2 else z.1 m := by
        intro z
        simp only [Function.update_apply]
      simp only [hpt]
      split_ifs
      · exact measurable_snd
      · exact (measurable_pi_apply m).comp measurable_fst
    have hm : Measurable (fun z : Xn n × Ω =>
        (starRingEnd ℂ) (Θ z.1) * α z.1 * β z.2 * Θ (Function.update z.1 i z.2)) :=
      ((((Complex.continuous_conj.measurable.comp (hΘm.comp measurable_fst)).mul
        (hαm.comp measurable_fst)).mul (hβm.comp measurable_snd)).mul (hΘm.comp hupd))
    exact hm.aestronglyMeasurable
  · intro z
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj]
    gcongr
    · exact hΘb z.1
    · exact hαb z.1
    · exact hβb z.2
    · exact hΘb _
  · intro z hz
    by_cases h1 : z.1 ∈ Work.MB.boxPow n ℓ
    · by_cases h2 : z.2 ∈ boxL ℓ
      · exact absurd (show z ∈ Work.MB.boxPow n ℓ ×ˢ boxL ℓ from ⟨h1, h2⟩) hz
      · have hz0 : Θ (Function.update z.1 i z.2) = 0 := by
          by_contra hne
          have hmem := (Work.MB.mem_boxPow_iff.mp (hΘs (Function.mem_support.mpr hne))) i
          rw [Function.update_self] at hmem
          exact h2 hmem
        simp [hz0]
    · have hz0 : (starRingEnd ℂ) (Θ z.1) = 0 := by
        rw [show Θ z.1 = 0 from Function.notMem_support.mp (fun h => h1 (hΘs h))]
        simp
      simp [hz0]

/-! ## 3. The pointwise kernel identity in the row's shape -/

/-- `Σ_k A·pinQ_k(w)·conj(pinQ_k y)·D = A·K1exp (fun _ => 1) w y·D`: the kernel identity
`Work.BoseBoxFock.pinQ_kernel_one` with the common factors `A`, `D` moved outside the finite
sum. -/
theorem sum_mul_pinQ_kernel {N : ℕ} {v : Ω → ℝ} {μ : ℝ} (A D : ℂ) (w y : Ω) :
    (∑ k : Lab N, A * pinQ v μ N k w * (starRingEnd ℂ) (pinQ v μ N k y) * D)
      = A * K1exp v μ N (fun _ : Lab N => (1 : ℝ)) w y * D := by
  have h1 : (∑ k : Lab N, A * pinQ v μ N k w * (starRingEnd ℂ) (pinQ v μ N k y) * D)
      = A * (∑ k : Lab N, pinQ v μ N k w * (starRingEnd ℂ) (pinQ v μ N k y)) * D := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h1, pinQ_kernel_one]

/-! ## 4. The row -/

theorem block3Row2_expanded {n N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (E : Work.BoseB7.Q3Env (Work.BoseBoxFock.Lab N))
    (Theta : Work.BoseDict.Xn n → ℂ) (hΘm : Measurable Theta)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ)) :
    (∑ k : Work.BoseBoxFock.Lab N,
        (E.mu * E.W1 0) •
          (∑ j : Fin n,
            ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinQ v μ N k (x j)
                * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k y)
                * Theta (Function.update x j y)))
      = (E.mu * E.W1 0) •
          (∑ j : Fin n,
            ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Theta x)
                * Work.BoseBoxFock.K1exp v μ N
                    (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)) (x j) y
                * Theta (Function.update x j y)) := by
  classical
  obtain ⟨C0, hC0⟩ := hΘb
  have hCΘ : 0 ≤ max C0 0 := le_max_right _ _
  have hΘb' : ∀ z, ‖Theta z‖ ≤ max C0 0 := fun z => (hC0 z).trans (le_max_left _ _)
  -- ### the integrability of every summand
  have hInt : ∀ (k : Lab N) (j : Fin n),
      Integrable (fun z : Xn n × Ω =>
        (starRingEnd ℂ) (Theta z.1) * pinQ v μ N k (z.1 j)
          * (starRingEnd ℂ) (pinQ v μ N k z.2) * Theta (Function.update z.1 j z.2))
        ((vXn n).prod (volume : Measure Ω)) := by
    intro k j
    obtain ⟨Ck, hCk0, hCk⟩ := pinQ_bdd v μ N k
    exact integrable_state_double (ℓ := ellH v μ) (Θ := Theta)
      (α := fun x : Xn n => pinQ v μ N k (x j))
      (β := fun y : Ω => (starRingEnd ℂ) (pinQ v μ N k y)) (i := j)
      (Cα := Ck) (Cβ := Ck) (CΘ := max C0 0) hCk0 hCk0 hCΘ
      ((pinQ_measurable v μ N k).comp (measurable_pi_apply j)) (fun x => hCk (x j))
      (Complex.continuous_conj.measurable.comp (pinQ_measurable v μ N k))
      (fun y => by rw [Complex.norm_conj]; exact hCk y) hΘm hΘb' hΘs
  -- ### the finite-sum / double-integral exchange
  have key := sum_mul_iterated_double_eq (n := n) (s := Finset.univ)
    (c := fun _ : Lab N => (((E.mu * E.W1 0 : ℝ)) : ℂ))
    (B := fun (k : Lab N) (j : Fin n) (x : Xn n) (y : Ω) =>
      (starRingEnd ℂ) (Theta x) * pinQ v μ N k (x j)
        * (starRingEnd ℂ) (pinQ v μ N k y) * Theta (Function.update x j y))
    (fun k j _ => hInt k j)
  simp only [Complex.real_smul]
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← integral_double_const_mul]
  refine integral_double_congr_of_forall (fun x y => ?_)
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_mul_pinQ_kernel]

end Work.BoseBoxFock
