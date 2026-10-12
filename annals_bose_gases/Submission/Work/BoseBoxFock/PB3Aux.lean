import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.abox_slice_peel
import Submission.Work.BoseBoxFock.pinQFinite_bessel
import Submission.Work.BoseBoxFock.slotMean_fibre_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3Aux` — the elementary layers of the block-III first half

Helpers for `Work.BoseBoxFock.PB3FirstHalf`: the constant-weight kernel expansion
(`K1exp_one_eq`), the orthogonality of the slot mean with the complementary slot against an
invariant weight (`aQC_mul_invariant_orth` / `invariant_mul_aQC_orth`), the resulting square
identity on the box (`box_sum_sq`), and the measurability/boundedness bookkeeping for the box
restriction of a `BoxState`.
-/

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The constant-weight kernel expansion -/

/-- **The block-III kernel at the constant weight `1`** is the rank-one kernel of the pinned
modes: `K1exp v μ N 1 w y = Σ_k pinQ_k w · conj (pinQ_k y)`. -/
theorem K1exp_one_eq {v : E3 → ℝ} {μ : ℝ} (N : ℕ) (w y : E3) :
    K1exp v μ N (fun _ : Lab N => (1 : ℝ)) w y
      = ∑ k : Lab N, pinQ v μ N k w * (starRingEnd ℂ) (pinQ v μ N k y) := by
  unfold K1exp
  rw [← pinQ_kernel_expansion (v := v) (μ := μ) (N := N)
    (fun _ : Lab N => (1 : ℝ)) w y]
  exact Finset.sum_congr rfl fun k _ => by simp

/-! ## 2. Orthogonality of the slot mean against an invariant weight -/

variable {n : ℕ} {ℓ : ℝ}

/-- The slot mean of an a.e. bounded, a.e. strongly measurable state is integrable on the box. -/
theorem integrableOn_aPC_of_bound (hℓ : 0 < ℓ) (i : Fin n) {g : Xn n → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (gm : AEStronglyMeasurable g (volume : Measure (Xn n)))
    (gb : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖g x‖ ≤ C) :
    IntegrableOn (aPC ℓ i g) (Submission.BoseGases.abox n ℓ) volume :=
  integrableOn_of_aesm_bound hℓ (aPC_aesm_full ℓ i gm) (aPC_ae_bound_full ℓ hℓ i hC gb)

/-- **The complementary slot is orthogonal to any weight constant in the slot** (first order):
`∫_{abox} aQC ℓ i g · h = 0` for `h (x[i↦u]) = h x`. -/
theorem aQC_mul_invariant_orth (hℓ : 0 < ℓ) (i : Fin n) {g h : Xn n → ℂ} {Cg Ch : ℝ}
    (hCg : 0 ≤ Cg) (hCh : 0 ≤ Ch)
    (gm : AEStronglyMeasurable g (volume : Measure (Xn n)))
    (gb : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖g x‖ ≤ Cg)
    (hm : AEStronglyMeasurable h (volume : Measure (Xn n)))
    (hh : ∀ x (u : E3), h (Function.update x i u) = h x)
    (hb : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖h x‖ ≤ Ch) :
    ∫ x in Submission.BoseGases.abox n ℓ, aQC ℓ i g x * h x = 0 := by
  have h1 : IntegrableOn (fun x => g x * h x) (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_of_aesm_bound hℓ (gm.mul hm) (by
      filter_upwards [gb, hb] with x hx1 hx2
      rw [norm_mul]; exact mul_le_mul hx1 hx2 (norm_nonneg _) hCg)
  have h2 : IntegrableOn (fun x => aPC ℓ i g x * h x) (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_of_aesm_bound hℓ ((aPC_aesm_full ℓ i gm).mul hm) (by
      filter_upwards [aPC_ae_bound_full ℓ hℓ i hCg gb, hb] with x hx1 hx2
      rw [norm_mul]; exact mul_le_mul hx1 hx2 (norm_nonneg _) hCg)
  -- the symmetry hypothesis in the other order
  have h3 : IntegrableOn (fun x => g x * aPC ℓ i h x) (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_of_aesm_bound hℓ (gm.mul (aPC_aesm_full ℓ i hm)) (by
      filter_upwards [gb, aPC_ae_bound_full ℓ hℓ i hCh hb] with x hx1 hx2
      rw [norm_mul]; exact mul_le_mul hx1 hx2 (norm_nonneg _) hCg)
  have hsym := aPC_sym_box (ℓ := ℓ) i (Φ := g) (Ψ := h) h2 h3
  rw [aPC_of_invariant hℓ i hh] at hsym
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, aQC ℓ i g x * h x)
      = ∫ x in Submission.BoseGases.abox n ℓ, (g x * h x - aPC ℓ i g x * h x) from by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [aQC_apply]; ring]
  rw [integral_sub h1 h2, hsym, sub_self]

/-- **The complementary slot is orthogonal to any weight constant in the slot** (second order):
`∫_{abox} h · aQC ℓ i g = 0` for `h (x[i↦u]) = h x`. -/
theorem invariant_mul_aQC_orth (hℓ : 0 < ℓ) (i : Fin n) {g h : Xn n → ℂ} {Cg Ch : ℝ}
    (hCg : 0 ≤ Cg) (hCh : 0 ≤ Ch)
    (gm : AEStronglyMeasurable g (volume : Measure (Xn n)))
    (gb : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖g x‖ ≤ Cg)
    (hm : AEStronglyMeasurable h (volume : Measure (Xn n)))
    (hh : ∀ x (u : E3), h (Function.update x i u) = h x)
    (hb : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖h x‖ ≤ Ch) :
    ∫ x in Submission.BoseGases.abox n ℓ, h x * aQC ℓ i g x = 0 := by
  have h1 : IntegrableOn (fun x => h x * g x) (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_of_aesm_bound hℓ (hm.mul gm) (by
      filter_upwards [hb, gb] with x hx1 hx2
      rw [norm_mul]; exact mul_le_mul hx1 hx2 (norm_nonneg _) hCh)
  have h2 : IntegrableOn (fun x => h x * aPC ℓ i g x) (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_of_aesm_bound hℓ (hm.mul (aPC_aesm_full ℓ i gm)) (by
      filter_upwards [hb, aPC_ae_bound_full ℓ hℓ i hCg gb] with x hx1 hx2
      rw [norm_mul]; exact mul_le_mul hx1 hx2 (norm_nonneg _) hCh)
  have h3 : IntegrableOn (fun x => aPC ℓ i h x * g x) (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_of_aesm_bound hℓ ((aPC_aesm_full ℓ i hm).mul gm) (by
      filter_upwards [aPC_ae_bound_full ℓ hℓ i hCh hb, gb] with x hx1 hx2
      rw [norm_mul]; exact mul_le_mul hx1 hx2 (norm_nonneg _) hCh)
  have hsym := aPC_sym_box (ℓ := ℓ) i (Φ := h) (Ψ := g) h3 h2
  rw [aPC_of_invariant hℓ i hh] at hsym
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, h x * aQC ℓ i g x)
      = ∫ x in Submission.BoseGases.abox n ℓ, (h x * g x - h x * aPC ℓ i g x) from by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [aQC_apply]; ring]
  rw [integral_sub h1 h2, hsym, sub_self]

/-- **The square identity of the slot mean**: for a.e. bounded, a.e. strongly measurable `B`,

    `∫_{abox} conj B · aPC ℓ i B = ∫_{abox} ‖aPC ℓ i B‖²`,

i.e. `aQC ℓ i B` is orthogonal to the range of `aPC ℓ i`. -/
theorem box_sum_sq (hℓ : 0 < ℓ) (i : Fin n) {B : Xn n → ℂ} {CB : ℝ}
    (hCB : 0 ≤ CB) (Bm : AEStronglyMeasurable B (volume : Measure (Xn n)))
    (Bb : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖B x‖ ≤ CB) :
    ∫ x in Submission.BoseGases.abox n ℓ, (starRingEnd ℂ) (B x) * aPC ℓ i B x
      = ∫ x in Submission.BoseGases.abox n ℓ, ((Complex.normSq (aPC ℓ i B x) : ℝ) : ℂ) := by
  have hPb : ∀ᵐ x ∂(volume : Measure (Xn n)), ‖aPC ℓ i B x‖ ≤ CB :=
    aPC_ae_bound_full ℓ hℓ i hCB Bb
  have hPBm : AEStronglyMeasurable (aPC ℓ i B) (volume : Measure (Xn n)) :=
    aPC_aesm_full ℓ i Bm
  have h2 : IntegrableOn (fun x => (starRingEnd ℂ) (aPC ℓ i B x) * aPC ℓ i B x)
      (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_aesm_bound hℓ (hPBm.star.mul hPBm) (C := CB * CB) ?_
    filter_upwards [hPb] with x hx
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hx hx (norm_nonneg _) hCB
  have h3 : IntegrableOn (fun x => (starRingEnd ℂ) (aPC ℓ i B x) * aQC ℓ i B x)
      (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_aesm_bound hℓ (hPBm.star.mul (Bm.sub hPBm))
      (C := CB * (CB + CB)) ?_
    filter_upwards [hPb, Bb] with x hx1 hx2
    rw [norm_mul, Complex.norm_conj, aQC_apply]
    exact mul_le_mul hx1 (le_trans (norm_sub_le _ _) (add_le_add hx2 hx1))
      (norm_nonneg _) hCB
  have horth : ∫ x in Submission.BoseGases.abox n ℓ,
      (starRingEnd ℂ) (aPC ℓ i B x) * aQC ℓ i B x = 0 :=
    invariant_mul_aQC_orth hℓ i hCB hCB Bm Bb hPBm.star
      (fun x u => by rw [aPC_const_in_coord])
      (by filter_upwards [hPb] with x hx; rw [Complex.norm_conj]; exact hx)
  have hsplit : ∫ x in Submission.BoseGases.abox n ℓ,
      (starRingEnd ℂ) (aPC ℓ i B x) * B x
      = ∫ x in Submission.BoseGases.abox n ℓ, ((Complex.normSq (aPC ℓ i B x) : ℝ) : ℂ) := by
    rw [show (∫ x in Submission.BoseGases.abox n ℓ, (starRingEnd ℂ) (aPC ℓ i B x) * B x)
        = ∫ x in Submission.BoseGases.abox n ℓ,
            ((starRingEnd ℂ) (aPC ℓ i B x) * aPC ℓ i B x
              + (starRingEnd ℂ) (aPC ℓ i B x) * aQC ℓ i B x) from by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [aQC_apply]; ring]
    rw [integral_add h2 h3, horth, add_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.normSq_eq_conj_mul_self]
  -- the symmetry `∫ conj B · aPC B = ∫ conj (aPC B) · B`
  have h1 : IntegrableOn (fun x => (starRingEnd ℂ) (B x) * aPC ℓ i B x)
      (Submission.BoseGases.abox n ℓ) volume := by
    refine integrableOn_of_aesm_bound hℓ (Bm.star.mul hPBm) (C := CB * CB) ?_
    filter_upwards [Bb, hPb] with x hx1 hx2
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hx1 hx2 (norm_nonneg _) hCB
  have h6 : IntegrableOn (fun x => aPC ℓ i (fun y => (starRingEnd ℂ) (B y)) x * B x)
      (Submission.BoseGases.abox n ℓ) volume := by
    rw [aPC_conj]
    refine integrableOn_of_aesm_bound hℓ (hPBm.star.mul Bm) (C := CB * CB) ?_
    filter_upwards [hPb, Bb] with x hx1 hx2
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hx1 hx2 (norm_nonneg _) hCB
  have hsym := aPC_sym_box (ℓ := ℓ) i (Φ := fun y => (starRingEnd ℂ) (B y)) (Ψ := B) h6 h1
  rw [aPC_conj] at hsym
  rw [← hsym, hsplit]

/-! ## 3. Measurability, bounds and support of the box restriction -/

/-- The box restriction, with the indicator taken complex-valued. -/
theorem boxRestrictC_eq_indicator {n : ℕ} (ℓ : ℝ) (Φ : Xn n → ℝ) :
    boxRestrictC ℓ Φ = fun x => ((Φ x : ℝ) : ℂ) *
      (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℂ)) x := by
  funext x
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · simp [boxRestrictC, Set.indicator_of_mem hx]
  · simp [boxRestrictC, Set.indicator_of_notMem hx]

/-- `aPC ℓ i Ψ` is measurable for measurable `Ψ`. -/
theorem aPC_measurable' {n : ℕ} {ℓ : ℝ} (i : Fin n) {Ψ : Xn n → ℂ} (hΨ : Measurable Ψ) :
    Measurable (aPC ℓ i Ψ) := by
  have hj : StronglyMeasurable (fun p : Xn n × E3 => Ψ (Function.update p.1 i p.2)) :=
    hΨ.stronglyMeasurable.comp_measurable (by fun_prop)
  have hint : StronglyMeasurable (fun x : Xn n =>
      ∫ y : E3, Ψ (Function.update x i y)
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    StronglyMeasurable.integral_prod_right hj
  have hfun : aPC ℓ i Ψ = fun x : Xn n => ((1 / ℓ ^ 3 : ℝ) : ℂ) *
      ∫ y : E3, Ψ (Function.update x i y)
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
    funext x
    rfl
  rw [hfun]
  exact (hint.const_mul _).measurable

/-- The box restriction of a continuous real state is measurable. -/
theorem boxRestrictC_measurable' {n : ℕ} (ℓ : ℝ) {Φ : Xn n → ℝ} (hΦ : Continuous Φ) :
    Measurable (boxRestrictC ℓ Φ) := by
  simp only [boxRestrictC_eq_indicator]
  exact ((Complex.continuous_ofReal.measurable.comp hΦ.measurable)).mul
    (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ))

/-- The box restriction of a continuous real state is bounded, with a nonnegative bound. -/
theorem boxRestrictC_bound' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Xn n → ℝ}
    (hΦ : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖boxRestrictC ℓ Φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  simp only [boxRestrictC_eq_indicator]
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · simp only [Set.indicator_of_mem hx, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (hC x hx) (le_max_left _ _)
  · simp only [Set.indicator_of_notMem hx, mul_zero, norm_zero]
    exact le_max_right _ _

/-- The box restriction is supported in the box. -/
theorem boxRestrictC_support' {n : ℕ} (ℓ : ℝ) (Φ : Xn n → ℝ) :
    Function.support (boxRestrictC ℓ Φ) ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra h
  refine hx ?_
  simp only [boxRestrictC_eq_indicator, Set.indicator_of_notMem h, mul_zero]

/-- On the box, the box restriction is the complexification of the state. -/
theorem boxRestrictC_apply_of_mem {n : ℕ} (ℓ : ℝ) (Φ : Xn n → ℝ) {x : Xn n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) := by
  simp only [boxRestrictC_eq_indicator, Set.indicator_of_mem hx, Pi.one_apply, mul_one]

/-- On the box, the complex slot mean of the box restriction is the complexification of the real
slot mean. -/
theorem boxRestrictC_aPC_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ : Xn n → ℝ}
    (hΦ : Continuous Φ) {x : Xn n} (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    aPC ℓ i (boxRestrictC ℓ Φ) x = ((Submission.BoseGases.aP ℓ i Φ x : ℝ) : ℂ) := by
  have h1 : (∫ y in Submission.BoseGases.acube ℓ,
        boxRestrictC ℓ Φ (Function.update x i y))
      = ∫ y in Submission.BoseGases.acube ℓ,
        ((Φ (Function.update x i y) : ℝ) : ℂ) :=
    MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun y hy => boxRestrictC_apply_of_mem ℓ Φ
        (Submission.BoseGases.update_mem_abox i hx hy))
  have h2 : (∫ y in Submission.BoseGases.acube ℓ,
        ((Φ (Function.update x i y) : ℝ) : ℂ))
      = ((∫ y in Submission.BoseGases.acube ℓ, Φ (Function.update x i y) : ℝ) : ℂ) :=
    integral_ofReal
  rw [aPC, h1, h2, Submission.BoseGases.aP]
  push_cast
  ring

/-- On the box, the complex complementary slot of the box restriction is the complexification of
the real complementary slot. -/
theorem boxRestrictC_aQC_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ : Xn n → ℝ}
    (hΦ : Continuous Φ) {x : Xn n} (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    aQC ℓ i (boxRestrictC ℓ Φ) x = ((Submission.BoseGases.aQ ℓ i Φ x : ℝ) : ℂ) := by
  rw [aQC_apply, boxRestrictC_apply_of_mem ℓ Φ hx, boxRestrictC_aPC_eq hℓ i hΦ hx,
    Submission.BoseGases.aQ]
  push_cast
  ring

/-! ## 4. The Bessel bound for the slot-`j` fibre -/

/-- Replacing a slot twice by the same slot is the same as replacing it once. -/
theorem pb3_update_update_self {n : ℕ} (x : Xn n) (j : Fin n) (u y : E3) :
    Function.update (Function.update x j u) j y = Function.update x j y := by
  funext k
  by_cases hk : k = j <;> simp [Function.update_apply, hk]

/-- **Bessel for the slot-`j` fibre**: the finite pinQ frame sum at the fibre
`u ↦ Ψ (x[j ↦ u])` is bounded by the `χ²`-weighted mass of its box projection.  The hypothesis is
the vanishing of the *fibre* off the box (weaker than `support Ψ ⊆ abox`). -/
theorem bessel_fibre {n N : ℕ} {v : E3 → ℝ} {μ : ℝ} (j : Fin n) (x : Xn n)
    {Ψ : Xn n → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨs : ∀ u : E3, u ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) →
      Ψ (Function.update x j u) = 0) :
    ∑ k : Lab N, ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
        * Ψ (Function.update x j u)‖ ^ 2
      ≤ ∫ u : E3, (Submission.BoseGases.chiScale (ellH v μ) u) ^ 2
          * ‖aQC (ellH v μ) j Ψ (Function.update x j u)‖ ^ 2 := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  set F : E3 → ℂ := fun u => Ψ (Function.update x j u) with hF
  have hFm : Measurable F := hΨm.comp (by fun_prop)
  have hFb : ∃ C : ℝ, ∀ u, ‖F u‖ ≤ C := by
    obtain ⟨C, hC⟩ := hΨb; exact ⟨C, fun u => hC _⟩
  have hFs : Function.support F ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
    intro u hu
    by_contra hcon
    rw [Function.mem_support] at hu
    exact hu (hΨs u hcon)
  have hbess := pinQFinite_bessel (v := v) (μ := μ) N hFm hFb hFs
  refine le_trans hbess (le_of_eq ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hpt : mf (ellH v μ) F u = aQC (ellH v μ) j Ψ (Function.update x j u) := by
    rw [mf, aQC_apply, aPC]
    rw [corpusBox_boxL_eq_acube hℓ]
    have hint : (∫ y in Submission.BoseGases.acube (ellH v μ), Ψ (Function.update x j y))
        = ∫ y in Submission.BoseGases.acube (ellH v μ),
            Ψ (Function.update (Function.update x j u) j y) := by
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable _)
        (fun y _ => ?_)
      rw [pb3_update_update_self]
    rw [hF, hint]
    norm_num
  simp only [hpt]

end

end Work.BoseBoxFock
