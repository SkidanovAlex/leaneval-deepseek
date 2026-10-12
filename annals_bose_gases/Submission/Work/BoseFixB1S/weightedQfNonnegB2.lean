import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.PQIdentAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.weightedQfNonnegB2` — fibre-weighted positivity of `Yᵢ = m + Σ_{j≠i}Pⱼ`

The fibre-weighted positivity of the per-slot operator `Yᵢ := m + Σ_{j≠i} Pⱼ`: writing
`Pⱼ = Work.UBBInputs8.boxPInd volA A j`,

    ⟨Ψ, fib(xᵢ)·YᵢΨ⟩ = m‖fib(xᵢ)^{1/2}Ψ‖² + Σ_{j≠i}‖Pⱼ(fib(xᵢ)^{1/2}Ψ)‖² ≥ 0 .

`Pⱼ` commutes with the multiplication `fib(xᵢ)^{1/2}` for `j ≠ i` (`boxPInd_smulF`), and
`∫ g·Pⱼg = ∫ (Pⱼg)²` for bounded `g` on the box (self-adjointness `boxPIndSelfAdjoint`
together with idempotence `boxPInd_idempotent`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `Pⱼ` commutes with multiplication by a function of the *other* slot (`i ≠ j`). -/
theorem boxPInd_smulF {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    {ψ : E3 → ℝ} {g : X N → ℝ} (x : X N) :
    Work.UBBInputs8.boxPInd volA A j (fun w : X N => ψ (w i) * g w) x
      = ψ (x i) * Work.UBBInputs8.boxPInd volA A j g x := by
  have hupd : ∀ z : E3, (Function.update x j z) i = x i := by
    intro z
    rw [Function.update_apply, if_neg hij]
  simp only [Work.UBBInputs8.boxPInd]
  have hcongr : (∫ z in A, (fun w : X N => ψ (w i) * g w) (Function.update x j z))
      = ∫ z in A, ψ (x i) * g (Function.update x j z) := by
    apply integral_congr_ae
    filter_upwards with z
    show ψ ((Function.update x j z) i) * g (Function.update x j z)
        = ψ (x i) * g (Function.update x j z)
    rw [hupd z]
  rw [hcongr, MeasureTheory.integral_const_mul]
  ring

theorem weightedQfNonnegB2 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfibm : Measurable fib) (hfib : 0 ≤ fib) {Cf : ℝ}
    (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, fib z ≤ Cf)
    {m : ℝ} (hm : 0 ≤ m) {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ CΨ) :
    0 ≤ ∫ x in Submission.BoseGases.abox N ℓ, fib (x i) * Ψ x
        * (m * Ψ x + ∑ j ∈ Finset.univ.erase i,
            Work.UBBInputs8.boxPInd volA A j Ψ x) := by
  set g : X N → ℝ := fun x => Real.sqrt (fib (x i)) * Ψ x with hgdef
  -- boundedness/measurability of `fib` and `g` on the box
  have hfibAbs : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ max Cf 0 := by
    intro z hz
    rw [abs_of_nonneg (hfib z)]
    exact le_trans (hfibb z hz) (le_max_left Cf (0:ℝ))
  have hfab : ∀ x ∈ Submission.BoseGases.abox N ℓ, |fib (x i)| ≤ max Cf 0 :=
    fun x hx => hfibAbs (x i) (hx i)
  have hgm : Measurable g := ((hfibm.comp (measurable_pi_apply i)).sqrt).mul hΨm
  have hgb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |g x| ≤ Real.sqrt (max Cf 0) * CΨ := by
    intro x hx
    have h1 : Real.sqrt (fib (x i)) ≤ Real.sqrt (max Cf 0) :=
      Real.sqrt_le_sqrt (le_trans (hfibb (x i) (hx i)) (le_max_left Cf (0:ℝ)))
    calc |g x| = Real.sqrt (fib (x i)) * |Ψ x| := by
          rw [hgdef]
          show |Real.sqrt (fib (x i)) * Ψ x| = Real.sqrt (fib (x i)) * |Ψ x|
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (max Cf 0) * CΨ :=
          mul_le_mul h1 (hΨb x hx) (abs_nonneg _) (Real.sqrt_nonneg _)
  -- the weighted cross term is the square norm of `Pⱼ g`
  have hcross : ∀ j ∈ Finset.univ.erase i,
      (∫ x in Submission.BoseGases.abox N ℓ, fib (x i) * Ψ x
          * Work.UBBInputs8.boxPInd volA A j Ψ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A j g x) ^ 2 := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hcom : ∀ x : X N, Work.UBBInputs8.boxPInd volA A j g x
        = Real.sqrt (fib (x i)) * Work.UBBInputs8.boxPInd volA A j Ψ x := by
      intro x
      show Work.UBBInputs8.boxPInd volA A j
          (fun w : X N => Real.sqrt (fib (w i)) * Ψ w) x
        = Real.sqrt (fib (x i)) * Work.UBBInputs8.boxPInd volA A j Ψ x
      exact boxPInd_smulF (N := N) volA A (i := i) (j := j) (Ne.symm hji)
        (ψ := fun z => Real.sqrt (fib z)) (g := Ψ) x
    -- step 1: the weighted form is the `g`-pairing
    have h1 : (∫ x in Submission.BoseGases.abox N ℓ, fib (x i) * Ψ x
          * Work.UBBInputs8.boxPInd volA A j Ψ x)
        = ∫ x in Submission.BoseGases.abox N ℓ, g x * Work.UBBInputs8.boxPInd volA A j g x := by
      apply integral_congr_ae
      filter_upwards with x
      have hpt : fib (x i) * Ψ x * Work.UBBInputs8.boxPInd volA A j Ψ x
          = g x * (Real.sqrt (fib (x i)) * Work.UBBInputs8.boxPInd volA A j Ψ x) := by
        rw [show g x = Real.sqrt (fib (x i)) * Ψ x from rfl]
        conv_lhs => rw [← Real.sq_sqrt (hfib (x i))]
        ring
      rw [hcom x]
      exact hpt
    -- step 2: `∫ g·Pⱼg = ∫ (Pⱼg)²` (self-adjointness + idempotence)
    have hidem : ∀ x : X N, Work.UBBInputs8.boxPInd volA A j
          (Work.UBBInputs8.boxPInd volA A j g) x = Work.UBBInputs8.boxPInd volA A j g x :=
      fun x => boxPInd_idempotent hℓ hvol hA hvolA hAc j g x
    have hsa := boxPIndSelfAdjoint hℓ hvol hA hvolA hAc j (Φ := g)
      (Ψ := Work.UBBInputs8.boxPInd volA A j g) hgm hgb
      (measurable_boxPInd volA A hA j hgm)
      (abs_boxPInd_le hℓ hvol hA hvolA hAc j hgb)
    have h2 : (∫ x in Submission.BoseGases.abox N ℓ, g x
          * Work.UBBInputs8.boxPInd volA A j g x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A j g x) ^ 2 := by
      have h2a : (∫ x in Submission.BoseGases.abox N ℓ, g x
            * Work.UBBInputs8.boxPInd volA A j g x)
          = ∫ x in Submission.BoseGases.abox N ℓ, g x
              * Work.UBBInputs8.boxPInd volA A j
                  (Work.UBBInputs8.boxPInd volA A j g) x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hidem x]
      rw [h2a, ← hsa]
      apply integral_congr_ae
      filter_upwards with x
      rw [sq]
    exact h1.trans h2
  -- split and assemble
  have hsplit : ∀ x : X N, fib (x i) * Ψ x
      * (m * Ψ x + ∑ j ∈ Finset.univ.erase i, Work.UBBInputs8.boxPInd volA A j Ψ x)
      = m * (fib (x i) * (Ψ x * Ψ x))
        + ∑ j ∈ Finset.univ.erase i,
            fib (x i) * Ψ x * Work.UBBInputs8.boxPInd volA A j Ψ x := by
    intro x
    rw [mul_add, Finset.mul_sum]
    congr 1; ring
  rw [show (∫ x in Submission.BoseGases.abox N ℓ, fib (x i) * Ψ x
        * (m * Ψ x + ∑ j ∈ Finset.univ.erase i, Work.UBBInputs8.boxPInd volA A j Ψ x))
      = ∫ x in Submission.BoseGases.abox N ℓ, (m * (fib (x i) * (Ψ x * Ψ x))
          + ∑ j ∈ Finset.univ.erase i, fib (x i) * Ψ x
              * Work.UBBInputs8.boxPInd volA A j Ψ x) from
      integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  have hfibsq : IntegrableOn (fun x : X N => fib (x i) * (Ψ x * Ψ x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ (hfibm.comp (measurable_pi_apply i)) (hΨm.mul hΨm)
      hfab (by
        intro x hx
        rw [abs_mul]
        exact mul_le_mul (hΨb x hx) (hΨb x hx) (abs_nonneg _) (le_trans (abs_nonneg _) (hΨb x hx)))
  have hterm : ∀ j ∈ Finset.univ.erase i, IntegrableOn
      (fun x : X N => fib (x i) * Ψ x * Work.UBBInputs8.boxPInd volA A j Ψ x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := fun j _ =>
    integrableOn_mul_of_bound (N := N) hℓ
      ((hfibm.comp (measurable_pi_apply i)).mul hΨm)
      (measurable_boxPInd volA A hA j hΨm)
      (Cf := max Cf 0 * CΨ) (Cg := CΨ)
      (by
        intro x hx
        rw [abs_mul]
        exact mul_le_mul (hfab x hx) (hΨb x hx) (abs_nonneg _) (le_max_right Cf 0))
      (abs_boxPInd_le hℓ hvol hA hvolA hAc j hΨb)
  rw [MeasureTheory.integral_add (hfibsq.const_mul m)
      (MeasureTheory.integrable_finsetSum _ hterm)]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ hterm]
  refine add_nonneg (mul_nonneg hm ?_) ?_
  · exact MeasureTheory.integral_nonneg fun x => mul_nonneg (hfib (x i)) (mul_self_nonneg _)
  · refine Finset.sum_nonneg fun j hj => ?_
    rw [hcross j hj]
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _

end Work.BoseFixB1S
