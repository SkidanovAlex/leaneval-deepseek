import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.weakAux
import Submission.Work.BoseFixB1S.PiCoordMeanL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.fibreMean_sq_integral_le`

The squared *unnormalised* fibre mean over the centred cube `acube ℓ`, integrated over the
`m`-particle box, is bounded by `ℓ³` times the `L²`-mass of the state on the `(m+1)`-particle box:

    ∫_{r ∈ abox m ℓ} (∫_{w ∈ acube ℓ} |f (kcInsN m j (w, r))|)² ≤ ℓ³ · ∫_{x ∈ abox (m+1) ℓ} f² .

The insertion `kcInsN m j : kcE3 × X m ≃ᵐ X (m+1)` is measure preserving and its preimage of the
`(m+1)`-particle box is the product of the one-particle cube and the `m`-particle box
(`peel_slot_abox`'s geometry), so the statement is the unnormalised fibre Cauchy–Schwarz on the
product measure `(volume ↾ acube ℓ) ⊗ (volume ↾ abox m ℓ)` transported back across `kcInsN`.

The proof is the unreduced twin of `Work.BoseFixB1S.fibreMean_sq_le`: the pointwise fibre
Cauchy–Schwarz `Work.BoseFixB1S.sq_integral_le_measure_mul_integral_sq` (Hölder, `p = q = 2`) at
a.e. `r`, integrated and evaluated by `integral_prod_symm`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseBoxFock.PCFU

/-- **Unnormalised fibre-mean square bound.**  For `H ∈ L²(ν ⊗ ρ)` the *unnormalised* fibre
integral `y ↦ ∫_ν H(·, y)` is square integrable and

    ∫_ρ (∫_ν H(·, y))² ≤ V · ∫_{ν ⊗ ρ} H² ,      V = (ν univ).toReal .

This is the unnormalised twin of `Work.BoseFixB1S.fibreMean_sq_le` (which carries the
`(1/V)`-normalised fibre mean and the constant `1/V`). -/
private theorem fibreMean_sq_le_unnorm {α : Type*} [MeasurableSpace α] {β : Type*}
    [MeasurableSpace β] (ν : Measure α) [IsFiniteMeasure ν] (ρ : Measure β) [IsFiniteMeasure ρ]
    {V : ℝ} (hV : (ν Set.univ).toReal = V) (H : α × β → ℝ)
    (hHm : AEStronglyMeasurable H (ν.prod ρ))
    (hH2 : Integrable (fun p => (H p) ^ 2) (ν.prod ρ)) :
    ∫ y, (∫ z, H (z, y) ∂ν) ^ 2 ∂ρ ≤ V * ∫ p, (H p) ^ 2 ∂(ν.prod ρ) := by
  have hV0 : 0 ≤ V := by rw [← hV]; exact ENNReal.toReal_nonneg
  have hFibMeas : AEStronglyMeasurable (fun y : β => ∫ z : α, H (z, y) ∂ν) ρ := by
    have h := hHm.prod_swap
    simpa using h.integral_prod_right'
  have hIntFib : Integrable (fun y : β => ∫ z : α, (H (z, y)) ^ 2 ∂ν) ρ := by
    have h := hH2.integral_norm_prod_right
    refine h.congr ?_
    filter_upwards with y
    apply integral_congr_ae
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hbound : ∀ᵐ y ∂ρ, (∫ z : α, H (z, y) ∂ν) ^ 2 ≤ V * ∫ z : α, (H (z, y)) ^ 2 ∂ν := by
    filter_upwards [hHm.prodMk_right, hH2.prod_left_ae] with y hsm hint
    have hcs := Work.BoseFixB1S.sq_integral_le_measure_mul_integral_sq hsm hint
    rwa [hV] at hcs
  have hInt : Integrable (fun y : β => (∫ z : α, H (z, y) ∂ν) ^ 2) ρ := by
    refine Integrable.mono' (hIntFib.const_mul V) (hFibMeas.pow 2) ?_
    filter_upwards [hbound] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hy
  calc ∫ y, (∫ z : α, H (z, y) ∂ν) ^ 2 ∂ρ
      ≤ ∫ y, V * (∫ z : α, (H (z, y)) ^ 2 ∂ν) ∂ρ :=
        integral_mono_ae hInt (hIntFib.const_mul V) hbound
    _ = V * ∫ y, (∫ z : α, (H (z, y)) ^ 2 ∂ν) ∂ρ := integral_const_mul V _
    _ = V * ∫ p, (H p) ^ 2 ∂(ν.prod ρ) := by
        rw [integral_prod_symm (fun p => (H p) ^ 2) hH2]

theorem fibreMean_sq_integral_le {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin (m + 1))
    {f : Submission.BoseGases.X (m + 1) → ℝ} {C : ℝ} (hC : 0 ≤ C) (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ C) :
    ∫ r : Submission.BoseGases.X m,
        (∫ w in Submission.BoseGases.acube ℓ,
            |f (Submission.BoseGases.kcInsN m j (w, r))|) ^ 2
      ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m ℓ))
    ≤ ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (f x) ^ 2 := by
  classical
  let ν : Measure (EuclideanSpace ℝ (Fin 3)) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ)
  let ρ : Measure (Submission.BoseGases.X m) :=
    (MeasureTheory.volume : Measure (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m ℓ)
  have hνuniv : ν Set.univ = ENNReal.ofReal (ℓ ^ 3) := by
    show (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ) Set.univ = ENNReal.ofReal (ℓ ^ 3)
    rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
  haveI hνfin : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact ENNReal.ofReal_lt_top⟩
  have hρuniv : ρ Set.univ = ENNReal.ofReal ((ℓ ^ 3) ^ m) := by
    show (MeasureTheory.volume : Measure (Submission.BoseGases.X m)).restrict
      (Submission.BoseGases.abox m ℓ) Set.univ = ENNReal.ofReal ((ℓ ^ 3) ^ m)
    rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume m ℓ hℓ.le]
  haveI hρfin : IsFiniteMeasure ρ := ⟨by rw [hρuniv]; exact ENNReal.ofReal_lt_top⟩
  have hV : (ν Set.univ).toReal = ℓ ^ 3 := by
    rw [hνuniv, ENNReal.toReal_ofReal (by positivity)]
  let H : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X m → ℝ :=
    fun p => |f (Submission.BoseGases.kcInsN m j p)|
  have hHmeas : Measurable H := by
    show Measurable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X m =>
      |f (Submission.BoseGases.kcInsN m j p)|)
    exact continuous_abs.measurable.comp (hfm.comp (Submission.BoseGases.kcInsN m j).measurable)
  have hH2 : Integrable (fun p => (H p) ^ 2) (ν.prod ρ) := by
    haveI : IsFiniteMeasure (ν.prod ρ) := inferInstance
    refine Integrable.mono' (integrable_const (C ^ 2)) (hHmeas.aestronglyMeasurable.pow 2) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc (H p) ^ 2 = |f (Submission.BoseGases.kcInsN m j p)| ^ 2 := rfl
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hfb _) 2
  have hkey := fibreMean_sq_le_unnorm ν ρ hV H hHmeas.aestronglyMeasurable hH2
  -- the measure preserving `kcInsN` change of variables
  have hpre : (Submission.BoseGases.kcInsN m j) ⁻¹' (Submission.BoseGases.abox (m + 1) ℓ)
      = Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox m ℓ := by
    ext p
    obtain ⟨y, r⟩ := p
    simp only [Set.mem_preimage, Set.mem_prod, Submission.BoseGases.mem_abox_iff]
    constructor
    · intro hp
      exact ⟨by simpa [Submission.BoseGases.kc_insN_apply_same] using hp j,
        fun i => by simpa [Submission.BoseGases.kc_insN_apply_succ] using hp (j.succAbove i)⟩
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = j
      · subst hi
        simpa [Submission.BoseGases.kc_insN_apply_same] using h1
      · rcases Fin.exists_succAbove_eq hi with ⟨i', hi'⟩
        rw [← hi']
        simpa [Submission.BoseGases.kc_insN_apply_succ] using h2 i'
  have hvol : (MeasureTheory.volume :
        Measure (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox m ℓ) = ν.prod ρ := by
    show (MeasureTheory.volume :
        Measure (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox m ℓ) =
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m ℓ))
    rw [Measure.volume_eq_prod (EuclideanSpace ℝ (Fin 3)) (Submission.BoseGases.X m),
      ← Measure.prod_restrict]
  have hmp : MeasurePreserving (Submission.BoseGases.kcInsN m j) (ν.prod ρ)
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) ℓ)) := by
    have h1 := (Submission.BoseGases.kc_mp_insN m j).restrict_preimage_emb
      (Submission.BoseGases.kcInsN m j).measurableEmbedding
      (Submission.BoseGases.abox (m + 1) ℓ)
    rw [hpre, hvol] at h1
    exact h1
  have htrans : ∫ p, (H p) ^ 2 ∂(ν.prod ρ)
      = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (f x) ^ 2 := by
    calc ∫ p, (H p) ^ 2 ∂(ν.prod ρ)
        = ∫ p, (f (Submission.BoseGases.kcInsN m j p)) ^ 2 ∂(ν.prod ρ) := by
          apply integral_congr_ae
          filter_upwards with p
          show |f (Submission.BoseGases.kcInsN m j p)| ^ 2
            = (f (Submission.BoseGases.kcInsN m j p)) ^ 2
          rw [sq_abs]
      _ = ∫ x, (f x) ^ 2 ∂((MeasureTheory.volume :
              Measure (Submission.BoseGases.X (m + 1))).restrict
            (Submission.BoseGases.abox (m + 1) ℓ)) :=
          hmp.integral_comp (Submission.BoseGases.kcInsN m j).measurableEmbedding
            (fun x => (f x) ^ 2)
      _ = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (f x) ^ 2 := rfl
  have hkey' : ∫ y, (∫ z, H (z, y) ∂ν) ^ 2 ∂ρ
      ≤ ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (f x) ^ 2 := by
    rw [← htrans]
    exact hkey
  exact hkey'

end Work.BoseBoxFock.PCFU
