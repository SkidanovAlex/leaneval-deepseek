import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3FibreQ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3V2.slotForm_slice`

The **slice (fibre) form** of the block-III one-slot pairing

    `⟨Θ, w_j · (w_j)^* Θ⟩ = ∫_{x'} conj(∫_u conj(w u) Θ(x'[j↦u])) · (∫_u conj(w u) Θ(x'[j↦u]))`,

i.e. the version of the `PB3FibreQ` Part-1 identity (`Work.BoseBoxFock.fibre_part1`) in which the
integrability of the pairing integrand is *derived* from the hypotheses on the state `Θ` and the
weight `w` rather than assumed.

The mathematical content is the integrability lemma `slotForm_integrable`; the hypothesis that
`Function.support Θ ⊆ abox n ℓ` (a box of finite measure) is what makes it work: it makes the
inner `u`-integral a genuine Bochner integral (the integrand `u ↦ conj (w u) * Θ (x[j↦u])` is
supported in the bounded cube `acube ℓ`), and it makes the outer integrand supported in `abox n ℓ`.
No integrability or decay of `w` is needed — only boundedness and a.e. strong measurability.

`sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PB3V2

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option autoImplicit false

/-! ## 1. The elementary box facts -/

/-- A state supported in the box vanishes outside it. -/
lemma theta_zero_of_notMem_abox {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ}
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) {x : Xn n}
    (hx : x ∉ Submission.BoseGases.abox n ℓ) : Θ x = 0 :=
  Function.notMem_support.mp (fun h => hx (hΘs h))

/-- If a configuration with slot `j` replaced by `u` lies in the `n`-particle box, then `u` lies in
the one-particle cube. -/
lemma update_mem_acube_of_mem_abox {n : ℕ} {ℓ : ℝ} (j : Fin n) (x : Xn n) (u : E3)
    (h : Function.update x j u ∈ Submission.BoseGases.abox n ℓ) :
    u ∈ Submission.BoseGases.acube ℓ := by
  have h' := (Submission.BoseGases.mem_abox_iff n ℓ (Function.update x j u)).mp h j
  rwa [Function.update_self] at h'

/-- Consequently the `u ↦ Θ (x[j ↦ u])` fibre vanishes outside the one-particle cube. -/
lemma fibre_update_eq_zero {n : ℕ} {ℓ : ℝ} (j : Fin n) {Θ : Xn n → ℂ}
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) (x : Xn n) {u : E3}
    (hu : u ∉ Submission.BoseGases.acube ℓ) : Θ (Function.update x j u) = 0 :=
  theta_zero_of_notMem_abox hΘs (fun h => hu (update_mem_acube_of_mem_abox j x u h))

/-! ## 2. Finiteness of the volume of the cubes for *every* `ℓ` -/

/-- The centred cube of side `ℓ` is contained in the one of side `|ℓ|`. -/
lemma acube_subset_abs (ℓ : ℝ) :
    Submission.BoseGases.acube ℓ ⊆ Submission.BoseGases.acube |ℓ| := by
  intro y hy
  rw [Submission.BoseGases.mem_acube_iff] at hy ⊢
  intro m
  exact Set.Icc_subset_Icc (by linarith [neg_le_neg (le_abs_self ℓ)])
    (by linarith [le_abs_self ℓ]) (hy m)

/-- The `n`-particle box of side `ℓ` is contained in the one of side `|ℓ|`. -/
lemma abox_subset_abs (n : ℕ) (ℓ : ℝ) :
    Submission.BoseGases.abox n ℓ ⊆ Submission.BoseGases.abox n |ℓ| := by
  intro x hx
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro i
  exact acube_subset_abs ℓ (hx i)

/-- The `n`-particle box has finite volume, for every real `ℓ` (not only `0 ≤ ℓ`). -/
lemma abox_lt_top' (n : ℕ) (ℓ : ℝ) :
    (volume : Measure (Xn n)) (Submission.BoseGases.abox n ℓ) < ⊤ :=
  lt_of_le_of_lt (measure_mono (abox_subset_abs n ℓ))
    (Submission.BoseGases.abox_lt_top n |ℓ| (abs_nonneg ℓ))

/-- The one-particle cube has finite volume, for every real `ℓ`. -/
lemma acube_lt_top' (ℓ : ℝ) : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
  lt_of_le_of_lt (measure_mono (acube_subset_abs ℓ))
    (Submission.BoseGases.acube_lt_top |ℓ| (abs_nonneg ℓ))

/-! ## 3. The integrability of the slot pairing -/

/-- **Integrability of the slot-`j` rank-one pairing.**  A measurable state `Θ`, everywhere bounded
and supported in the box `abox n ℓ`, and a bounded a.e. strongly measurable weight `w`, give an
integrable pairing integrand.  The support hypothesis supplies both integrabilities: of the inner
`u`-integral (through `fibre_update_eq_zero`, the integrand being supported in the cube
`acube ℓ`) and of the outer integrand (supported in the box `abox n ℓ`, of finite volume). -/
lemma slotForm_integrable {n : ℕ} (j : Fin n) {ℓ : ℝ} {Θ : Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    {w : E3 → ℂ}
    (hwm : MeasureTheory.AEStronglyMeasurable w
      (MeasureTheory.volume : MeasureTheory.Measure E3))
    (hwb : ∃ C : ℝ, ∀ u, ‖w u‖ ≤ C) :
    Integrable (fun x : Xn n => (starRingEnd ℂ) (Θ x)
      * (w (x j) * (∫ u : E3, (starRingEnd ℂ) (w u) * Θ (Function.update x j u))))
      (MeasureTheory.volume : MeasureTheory.Measure (Xn n)) := by
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨Cw, hCw⟩ := hwb
  -- the non-negative bounds actually used
  let a : ℝ := max CΘ 0
  let b : ℝ := max Cw 0
  have ha : 0 ≤ a := le_max_right _ _
  have hbp : 0 ≤ b := le_max_right _ _
  have hΘa : ∀ x, ‖Θ x‖ ≤ a := fun x => le_trans (hCΘ x) (le_max_left _ _)
  have hwa : ∀ u, ‖w u‖ ≤ b := fun u => le_trans (hCw u) (le_max_left _ _)
  -- the volume of the one-particle cube and the pointwise bound `B`
  let V : ℝ := MeasureTheory.Measure.real (volume : Measure E3) (Submission.BoseGases.acube ℓ)
  have hV : 0 ≤ V := by
    show 0 ≤ MeasureTheory.Measure.real (volume : Measure E3) (Submission.BoseGases.acube ℓ)
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_nonneg
  let B : ℝ := a * (b * (b * (a * V)))
  have hB : 0 ≤ B := by
    show 0 ≤ a * (b * (b * (a * V)))
    exact mul_nonneg ha (mul_nonneg hbp (mul_nonneg hbp (mul_nonneg ha hV)))
  -- the inner `u`-integral is uniformly bounded
  have hIbound : ∀ x : Xn n,
      ‖∫ u : E3, (starRingEnd ℂ) (w u) * Θ (Function.update x j u)‖ ≤ b * a * V := by
    intro x
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Submission.BoseGases.acube ℓ)
      (f := fun u : E3 => (starRingEnd ℂ) (w u) * Θ (Function.update x j u))
      (fun u hu => by rw [fibre_update_eq_zero j hΘs x hu, mul_zero])]
    exact norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3))
      (s := Submission.BoseGases.acube ℓ)
      (f := fun u : E3 => (starRingEnd ℂ) (w u) * Θ (Function.update x j u))
      (C := b * a) (acube_lt_top' ℓ) (fun u _ => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hwa u) (hΘa _) (norm_nonneg _) hbp)
  -- the pointwise bound of the pairing integrand
  have hf_bound : ∀ x : Xn n,
      ‖(starRingEnd ℂ) (Θ x)
        * (w (x j) * (∫ u : E3, (starRingEnd ℂ) (w u) * Θ (Function.update x j u)))‖ ≤ B := by
    intro x
    show ‖(starRingEnd ℂ) (Θ x)
        * (w (x j) * (∫ u : E3, (starRingEnd ℂ) (w u) * Θ (Function.update x j u)))‖
      ≤ a * (b * (b * (a * V)))
    rw [norm_mul, Complex.norm_conj, norm_mul]
    exact mul_le_mul (hΘa x) (mul_le_mul (hwa _) (by simpa only [mul_assoc] using hIbound x)
      (norm_nonneg _) hbp) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ha
  -- the pairing integrand is supported in the box
  have hsupp : Function.support (fun x : Xn n => (starRingEnd ℂ) (Θ x)
      * (w (x j) * (∫ u : E3, (starRingEnd ℂ) (w u) * Θ (Function.update x j u))))
      ⊆ Submission.BoseGases.abox n ℓ := by
    intro x hx
    by_contra hxc
    exact (Function.mem_support.mp hx)
      (by rw [theta_zero_of_notMem_abox hΘs hxc, map_zero, zero_mul])
  -- a.e. strong measurability of the pairing integrand
  have hfaesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Xn n => (starRingEnd ℂ) (Θ x)
        * (w (x j) * (∫ u : E3, (starRingEnd ℂ) (w u) * Θ (Function.update x j u))))
      (volume : Measure (Xn n)) := by
    have h1 : AEStronglyMeasurable (fun x : Xn n => (starRingEnd ℂ) (Θ x)) volume :=
      Complex.continuous_conj.comp_aestronglyMeasurable hΘm.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : Xn n => w (x j)) volume :=
      hwm.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure E3)) j)
    have h3 : AEStronglyMeasurable
        (fun x : Xn n => ∫ u : E3, (starRingEnd ℂ) (w u) * Θ (Function.update x j u))
        (volume : Measure (Xn n)) := by
      refine AEStronglyMeasurable.integral_prod_right' (μ := (volume : Measure (Xn n)))
        (ν := (volume : Measure E3))
        (f := fun p : Xn n × E3 => (starRingEnd ℂ) (w p.2) * Θ (Function.update p.1 j p.2)) ?_
      exact ((Complex.continuous_conj.comp_aestronglyMeasurable
          (hwm.comp_quasiMeasurePreserving
            (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Xn n)))
              (ν := (volume : Measure E3))))).mul
        (hΘm.comp (continuous_update j).measurable).aestronglyMeasurable)
    exact h1.mul (h2.mul h3)
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset
    (μ := (volume : Measure (Xn n))) (s := Submission.BoseGases.abox n ℓ)
    (f := fun x : Xn n => (starRingEnd ℂ) (Θ x)
      * (w (x j) * (∫ u : E3, (starRingEnd ℂ) (w u) * Θ (Function.update x j u))))
    hsupp).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound (abox_lt_top' n ℓ) hfaesm.restrict B
    (Filter.Eventually.of_forall hf_bound)

/-! ## 4. The slice form -/

theorem slotForm_slice {n : ℕ} (j : Fin n) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    {w : EuclideanSpace ℝ (Fin 3) → ℂ} (hwm : MeasureTheory.AEStronglyMeasurable w (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (hwb : ∃ C : ℝ, ∀ u, ‖w u‖ ≤ C) :
    (∫ x : Work.BoseDict.Xn n, (starRingEnd ℂ) (Θ x)
        * (w (x j) * (∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (w u) * Θ (Function.update x j u))))
      = ∫ x' : {k : Fin n // k ≠ j} → EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (w u)
              * Θ (Work.BoseBoxFock.insertCoord j u x'))
            * (∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (w u)
                * Θ (Work.BoseBoxFock.insertCoord j u x')) :=
  Work.BoseBoxFock.fibre_part1 j (slotForm_integrable j hΘm hΘb hΘs hwm hwb)

end Work.BoseBoxFock.PB3V2
