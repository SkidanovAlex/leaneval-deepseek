import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 1600000

/-- **The assembly of the flat-count Jensen** from its four ingredient facts (see the module
docstring). -/
theorem boxFlatSqJensen_of_pieces
    (hOneFlat : ∀ {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
      {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
      (hAc : A ⊆ acube ℓ) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ} (hΦc : Continuous Φ),
      (∫ x in abox (n + 1) ℓ, (UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = ∫ x in abox (n + 1) ℓ, Φ x * UBBInputs8.boxPInd volA A i Φ x)
    (hPairFlat : ∀ {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
      {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
      (hAc : A ⊆ acube ℓ) (i : Fin (p + 2)) (j' : Fin (p + 1)) {Φ : X (p + 2) → ℝ}
      (hΦc : Continuous Φ),
      (∫ x in abox (p + 2) ℓ, (UBBInputs8.boxPInd volA A i
          (UBBInputs8.boxPInd volA A (i.succAbove j') Φ) x) ^ 2)
        = ∫ x in abox (p + 2) ℓ, UBBInputs8.boxPInd volA A i Φ x
            * UBBInputs8.boxPInd volA A (i.succAbove j') Φ x)
    (hCS : ∀ {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : X N → ℝ} (hfm : Measurable f)
      (hgm : Measurable g) {Cf Cg : ℝ}
      (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ Cf) (hgb : ∀ x ∈ abox N ℓ, |g x| ≤ Cg),
      (∫ x in abox N ℓ, f x * g x) ^ 2
        ≤ (∫ x in abox N ℓ, (f x) ^ 2) * (∫ x in abox N ℓ, (g x) ^ 2))
    (hSplit : ∀ {n : ℕ} (d : Fin (n + 1) → ℝ) (f : Fin (n + 1) → Fin (n + 1) → ℝ),
      (∑ p : Fin (n + 1) × Fin (n + 1), (if p.1 = p.2 then d p.1 else f p.1 p.2))
        = (∑ i, d i) + ∑ p ∈ pairSet (n + 1), f p.1 p.2)
    {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    boxFlatCount volA ℓ A Φ ^ 2
        - boxFlatCount volA ℓ A Φ * (∫ x in abox N ℓ, (Φ x) ^ 2)
      ≤ (∫ x in abox N ℓ, (Φ x) ^ 2) * boxPairCount volA ℓ A Φ := by
  cases N with
  | zero =>
      simp [boxFlatCount, boxPairCount, pairSet]
  | succ n =>
      -- a bound for `Φ` on the (compact) box
      obtain ⟨C, hC⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
        (s := abox (n + 1) ℓ) (f := Φ) hΦc.continuousOn
      have hC0 : 0 ≤ C := le_trans (norm_nonneg (Φ 0)) (hC 0 (zero_mem_abox (N := n + 1) hℓ.le))
      have hbΦ : ∀ x ∈ abox (n + 1) ℓ, |Φ x| ≤ C := fun x hx => by
        simpa [Real.norm_eq_abs] using hC x hx
      have hΦm : Measurable Φ := hΦc.measurable
      -- measurability and boundedness of the box projections
      have hm : ∀ i : Fin (n + 1), Measurable (UBBInputs8.boxPInd volA A i Φ) :=
        fun i => measurable_boxPInd volA A hA i hΦm
      have hb : ∀ i : Fin (n + 1), ∀ x ∈ abox (n + 1) ℓ,
          |UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
        fun i => abs_boxPInd_le (N := n + 1) hℓ hvol hA hvolA hAc i hbΦ
      -- the flat sum `Λ Φ = Σᵢ Pᵢ Φ`
      set G : X (n + 1) → ℝ := fun x => ∑ i : Fin (n + 1), UBBInputs8.boxPInd volA A i Φ x
        with hG
      have hGm : Measurable G := by
        rw [hG]
        exact Finset.measurable_sum Finset.univ (fun i _ => hm i)
      have hGb : ∀ x ∈ abox (n + 1) ℓ, |G x| ≤ ((n : ℝ) + 1) * C := by
        intro x hx
        rw [hG]
        have h1 : |∑ i : Fin (n + 1), UBBInputs8.boxPInd volA A i Φ x|
            ≤ ∑ i : Fin (n + 1), |UBBInputs8.boxPInd volA A i Φ x| :=
          Finset.abs_sum_le_sum_abs _ _
        have h2 : (∑ i : Fin (n + 1), |UBBInputs8.boxPInd volA A i Φ x|)
            ≤ ∑ _i : Fin (n + 1), C := Finset.sum_le_sum (fun i _ => hb i x hx)
        have h3 : (∑ _i : Fin (n + 1), C) = ((n : ℝ) + 1) * C := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
        linarith
      -- integrability of the products appearing in the two linearity steps
      have hint_Φi : ∀ i : Fin (n + 1),
          IntegrableOn (fun x : X (n + 1) => Φ x * UBBInputs8.boxPInd volA A i Φ x)
            (abox (n + 1) ℓ) volume :=
        fun i => integrableOn_mul_of_bound hℓ hΦm (hm i) hbΦ (hb i)
      have hint_ij : ∀ i j : Fin (n + 1),
          IntegrableOn (fun x : X (n + 1) => UBBInputs8.boxPInd volA A i Φ x
            * UBBInputs8.boxPInd volA A j Φ x) (abox (n + 1) ℓ) volume :=
        fun i j => integrableOn_mul_of_bound hℓ (hm i) (hm j) (hb i) (hb j)
      -- the ordered-pair identity, in the (index-free) form needed by the case split below
      have hPairGen : ∀ i j : Fin (n + 1), i ≠ j →
          (∫ x in abox (n + 1) ℓ, UBBInputs8.boxPInd volA A i Φ x
              * UBBInputs8.boxPInd volA A j Φ x)
            = ∫ x in abox (n + 1) ℓ,
                (UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x) ^ 2 := by
        intro i j hij
        cases n with
        | zero => exact absurd (Fin.ext (by omega)) hij
        | succ m =>
            obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
            rw [← hj']
            exact (hPairFlat (p := m) hℓ hvol hA hvolA hAc i j' hΦc).symm
      -- (1) the flat count is `⟨Φ, ΛΦ⟩`
      have hS : boxFlatCount volA ℓ A Φ = ∫ x in abox (n + 1) ℓ, Φ x * G x := by
        have h1 : boxFlatCount volA ℓ A Φ
            = ∑ i : Fin (n + 1),
                ∫ x in abox (n + 1) ℓ, Φ x * UBBInputs8.boxPInd volA A i Φ x := by
          rw [boxFlatCount]
          exact Finset.sum_congr rfl (fun i _ => hOneFlat hℓ hvol hA hvolA hAc i hΦc)
        rw [h1, ← MeasureTheory.integral_finsetSum (s := Finset.univ)
          (f := fun i : Fin (n + 1) => fun x : X (n + 1) =>
            Φ x * UBBInputs8.boxPInd volA A i Φ x)
          (μ := (volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ))]
        · apply integral_congr_ae
          filter_upwards with x
          rw [hG, Finset.mul_sum]
        · intro i _
          exact hint_Φi i
      -- (2) `∫ (ΛΦ)²` expanded over ordered pairs
      have hG2 : (∫ x in abox (n + 1) ℓ, (G x) ^ 2)
          = boxFlatCount volA ℓ A Φ + boxPairCount volA ℓ A Φ := by
        have h1 : (∫ x in abox (n + 1) ℓ, (G x) ^ 2)
            = ∑ q : Fin (n + 1) × Fin (n + 1),
                ∫ x in abox (n + 1) ℓ, UBBInputs8.boxPInd volA A q.1 Φ x
                  * UBBInputs8.boxPInd volA A q.2 Φ x := by
          rw [← MeasureTheory.integral_finsetSum (s := Finset.univ)
            (f := fun q : Fin (n + 1) × Fin (n + 1) => fun x : X (n + 1) =>
              UBBInputs8.boxPInd volA A q.1 Φ x * UBBInputs8.boxPInd volA A q.2 Φ x)
            (μ := (volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ))]
          · apply integral_congr_ae
            filter_upwards with x
            rw [hG, pow_two, Finset.sum_mul_sum]
            -- `(Σᵢ Pᵢ)(Σⱼ Pⱼ) = Σᵢ Σⱼ Pᵢ Pⱼ` vs the double sum over ordered pairs
            rw [← Finset.univ_product_univ, ← Finset.sum_product']
          · intro q _
            exact hint_ij q.1 q.2
        have h2 : (∑ q : Fin (n + 1) × Fin (n + 1),
                ∫ x in abox (n + 1) ℓ, UBBInputs8.boxPInd volA A q.1 Φ x
                  * UBBInputs8.boxPInd volA A q.2 Φ x)
            = ∑ q : Fin (n + 1) × Fin (n + 1),
                (if q.1 = q.2 then
                    (∫ x in abox (n + 1) ℓ, (UBBInputs8.boxPInd volA A q.1 Φ x) ^ 2)
                  else
                    (∫ x in abox (n + 1) ℓ,
                      (UBBInputs8.boxPInd volA A q.1
                        (UBBInputs8.boxPInd volA A q.2 Φ) x) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases hq : q.1 = q.2
          · rw [if_pos hq, hq]
            apply integral_congr_ae
            filter_upwards with x
            ring
          · rw [if_neg hq]
            exact hPairGen q.1 q.2 hq
        have h3 := hSplit (n := n)
          (d := fun i : Fin (n + 1) =>
            ∫ x in abox (n + 1) ℓ, (UBBInputs8.boxPInd volA A i Φ x) ^ 2)
          (f := fun i j : Fin (n + 1) =>
            ∫ x in abox (n + 1) ℓ,
              (UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
        rw [h1, h2, h3, boxFlatCount, boxPairCount]
      -- (3) Cauchy–Schwarz and the conclusion
      have hCS' := hCS (ℓ := ℓ) hℓ (f := fun x : X (n + 1) => Φ x) (g := G) hΦm hGm hbΦ hGb
      have hmain : (boxFlatCount volA ℓ A Φ) ^ 2
          ≤ (∫ x in abox (n + 1) ℓ, (Φ x) ^ 2)
            * (boxFlatCount volA ℓ A Φ + boxPairCount volA ℓ A Φ) := by
        rw [← hS, hG2] at hCS'
        exact hCS'
      nlinarith [hmain]

theorem boxFlatSqJensen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
      ≤ (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
          * Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
  have hfin : (volume : Measure (X N)) (abox N ℓ) < ∞ := abox_lt_top N ℓ hℓ.le
  haveI : IsFiniteMeasure ((volume : Measure (X N)).restrict (abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (Φ 0)) (hC 0 (zero_mem_abox (N := N) hℓ.le))
  have hbΦ : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  have hΦm : Measurable Φ := hΦc.measurable
  have hm : ∀ i : Fin N, Measurable (UBBInputs8.boxPInd volA A i Φ) :=
    fun i => measurable_boxPInd volA A hA i hΦm
  have hb : ∀ i : Fin N, ∀ x ∈ abox N ℓ, |UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    fun i => abs_boxPInd_le (N := N) hℓ hvol hA hvolA hAc i hbΦ
  -- the flat sum `Λ Φ = Σᵢ Pᵢ Φ`
  set G : X N → ℝ := fun x => ∑ i : Fin N, UBBInputs8.boxPInd volA A i Φ x with hG
  have hGm : Measurable G := by
    rw [hG]
    exact Finset.measurable_sum Finset.univ (fun i _ => hm i)
  have hGb : ∀ x ∈ abox N ℓ, |G x| ≤ (N : ℝ) * C := by
    intro x hx
    rw [hG]
    calc |∑ i : Fin N, UBBInputs8.boxPInd volA A i Φ x|
        ≤ ∑ i : Fin N, |UBBInputs8.boxPInd volA A i Φ x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hb i x hx)
      _ = (N : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- integrability of the products appearing in the two linearity steps
  have hint_Φi : ∀ i : Fin N,
      IntegrableOn (fun x : X N => Φ x * UBBInputs8.boxPInd volA A i Φ x)
        (abox N ℓ) volume :=
    fun i => integrableOn_mul_of_bound hℓ hΦm (hm i) hbΦ (hb i)
  have hint_ij : ∀ i j : Fin N,
      IntegrableOn (fun x : X N => UBBInputs8.boxPInd volA A i Φ x
        * UBBInputs8.boxPInd volA A j Φ x) (abox N ℓ) volume :=
    fun i j => integrableOn_mul_of_bound hℓ (hm i) (hm j) (hb i) (hb j)
  -- (1) the flat count is `⟨Φ, ΛΦ⟩`  (`Q0C.one_self_N`)
  have hS : boxFlatCount volA ℓ A Φ = ∫ x in abox N ℓ, Φ x * G x := by
    have h1 : boxFlatCount volA ℓ A Φ
        = ∑ i : Fin N, ∫ x in abox N ℓ, Φ x * UBBInputs8.boxPInd volA A i Φ x := by
      rw [boxFlatCount]
      exact Finset.sum_congr rfl (fun i _ =>
        (Q0C.one_self_N (volA := volA) hℓ hvol hA hvolA hAc i hΦc).symm)
    rw [h1, ← MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun i : Fin N => fun x : X N => Φ x * UBBInputs8.boxPInd volA A i Φ x)
      (μ := (volume : Measure (X N)).restrict (abox N ℓ))]
    · apply integral_congr_ae
      filter_upwards with x
      rw [hG, Finset.mul_sum]
    · intro i _
      exact hint_Φi i
  -- (2) `∫ (ΛΦ)²`, expanded over ordered pairs and split into flat + pair counts
  have hG2 : (∫ x in abox N ℓ, (G x) ^ 2)
      = boxFlatCount volA ℓ A Φ + boxPairCount volA ℓ A Φ := by
    have h1 : (∫ x in abox N ℓ, (G x) ^ 2)
        = ∑ q : Fin N × Fin N, ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A q.1 Φ x
            * UBBInputs8.boxPInd volA A q.2 Φ x := by
      rw [← MeasureTheory.integral_finsetSum (s := Finset.univ)
        (f := fun q : Fin N × Fin N => fun x : X N =>
          UBBInputs8.boxPInd volA A q.1 Φ x * UBBInputs8.boxPInd volA A q.2 Φ x)
        (μ := (volume : Measure (X N)).restrict (abox N ℓ))]
      · apply integral_congr_ae
        filter_upwards with x
        rw [hG, pow_two, Finset.sum_mul_sum, ← Finset.univ_product_univ,
          ← Finset.sum_product']
      · intro q _
        exact hint_ij q.1 q.2
    have h2 : (∑ q : Fin N × Fin N, ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A q.1 Φ x
            * UBBInputs8.boxPInd volA A q.2 Φ x)
        = (∑ i : Fin N, ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A i Φ x
              * UBBInputs8.boxPInd volA A i Φ x)
          + ∑ p ∈ pairSet N, ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A p.1 Φ x
              * UBBInputs8.boxPInd volA A p.2 Φ x := by
      rw [show (∑ q : Fin N × Fin N, ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A q.1 Φ x
              * UBBInputs8.boxPInd volA A q.2 Φ x)
          = ∑ i : Fin N, ∑ j : Fin N, ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A i Φ x
              * UBBInputs8.boxPInd volA A j Φ x from by
        rw [← Finset.univ_product_univ, ← Finset.sum_product']]
      exact Q0C.sum_univ_univ_eq (fun i j : Fin N =>
        ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A i Φ x
          * UBBInputs8.boxPInd volA A j Φ x)
    have h3 : (∑ i : Fin N, ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A i Φ x
            * UBBInputs8.boxPInd volA A i Φ x) = boxFlatCount volA ℓ A Φ := by
      rw [boxFlatCount]
      exact Finset.sum_congr rfl (fun i _ => by
        apply integral_congr_ae
        filter_upwards with x
        ring)
    have h4 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A p.1 Φ x
            * UBBInputs8.boxPInd volA A p.2 Φ x) = boxPairCount volA ℓ A Φ := by
      rw [boxPairCount]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      exact Q0C.pair_mixed_N (volA := volA) hℓ hvol hA hvolA hAc
        (Finset.mem_filter.mp hp).2 hΦc
    rw [h1, h2, h3, h4]
  -- (3) Cauchy–Schwarz and the conclusion
  have hCS := Q0C.integral_mul_sq_le (μ := (volume : Measure (X N)).restrict (abox N ℓ))
    (f := Φ) (g := G) (Cf := C) (Cg := (N : ℝ) * C)
    hΦm.aestronglyMeasurable hGm.aestronglyMeasurable
    (by
      rw [ae_restrict_iff' (abox_measurable N ℓ)]
      exact ae_of_all _ (fun x hx => hbΦ x hx))
    (by
      rw [ae_restrict_iff' (abox_measurable N ℓ)]
      exact ae_of_all _ (fun x hx => hGb x hx))
  rw [← hS, hG2] at hCS
  nlinarith [hCS]

end Work.BoseFixB1S
