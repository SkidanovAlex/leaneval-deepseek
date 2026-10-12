import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Up.FlatZeroRows
import Submission.Work.BoseFixB1S.integral_sq_le_measure_mul_integral_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped BigOperators ENNReal Real Topology

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## 1. The bump sup-bound, re-proved in a clash-free cone -/

/-- `|χ_{B(u)}| ≤ chiSupAbs · chiSmallDecay M`; the `BoseFixB1Up/flatPairAux` copy of this lemma
is on the other side of the `Work.BoseFixB1S.boxQInd_eq` import clash, so it is re-proved here. -/
theorem chiSmallB_abs_le_chisup {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u z : E3) :
    |chiSmallB M ℓ d u z| ≤ chiSupAbs * chiSmallDecay M := by
  have h1 : |chiScale ℓ z| ≤ chiSupAbs := chiScale_abs_le_sup ℓ z
  have h2 : |chiSmall M ((ℓ * d)⁻¹ • z - u)| ≤ chiSmallDecay M :=
    chiSmall_decay_coord_le_decay hM _
  rw [chiSmallB, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) chiSupAbs_nonneg

/-! ## 2. The unconditional Cauchy–Schwarz of the flat pair-condensate -/

/-- **The smooth Cauchy–Schwarz of the flat branch.**  For every (continuous) box state, with
`S = ∫Φ²Σᵢχ(xᵢ)²` and `g = Σᵢχ(xᵢ)²`,

    S² ≤ (∫Φ²)·(∫Φ²·g²) .

This is `(∫ Φ·(Φg))² ≤ (∫Φ²)·(∫(Φg)²)`.  **No flatness (and no peel) is used.** -/
theorem flatSmoothCSRaw {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) {n : ℕ}
    {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox n ℓ, Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) ^ 2
      ≤ (∫ x in abox n ℓ, Φ x ^ 2)
        * ∫ x in abox n ℓ,
            Φ x ^ 2 * (∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) ^ 2 := by
  classical
  set ν : Measure (X n) := volume.restrict (abox n ℓ) with hν
  haveI hfin : IsFiniteMeasure ν :=
    ⟨by rw [hν, Measure.restrict_apply_univ]; exact abox_lt_top n ℓ hℓ.le⟩
  set g : X n → ℝ := fun x => ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2 with hg
  have hgcont : Continuous g :=
    continuous_finsetSum _ (fun i _ =>
      (((Work.BoseFixB1.continuous_chiSmallB M ℓ d u).comp (continuous_apply i))).pow 2)
  obtain ⟨CΦ, hCΦ⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  obtain ⟨Cg, hCg⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hgcont.continuousOn
  have hbddΦ : ∀ᵐ x ∂ν, |Φ x| ≤ CΦ := by
    rw [hν, MeasureTheory.ae_restrict_iff' (abox_compact n hℓ).isClosed.measurableSet]
    exact Filter.Eventually.of_forall (fun x hx => by
      simpa [Real.norm_eq_abs] using hCΦ x hx)
  have hbddG : ∀ᵐ x ∂ν, |Φ x * g x| ≤ CΦ * Cg := by
    rw [hν, MeasureTheory.ae_restrict_iff' (abox_compact n hℓ).isClosed.measurableSet]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [abs_mul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hCΦ x hx)
      (by simpa [Real.norm_eq_abs] using hCg x hx) (abs_nonneg _)
      (le_trans (abs_nonneg (Φ x)) (by simpa [Real.norm_eq_abs] using hCΦ x hx))
  have hmemΦ : MemLp (fun x : X n => Φ x) 2 ν :=
    MemLp.of_bound hΦc.aestronglyMeasurable CΦ (by
      filter_upwards [hbddΦ] with x hx
      simpa [Real.norm_eq_abs] using hx)
  have hmemG : MemLp (fun x : X n => Φ x * g x) 2 ν :=
    MemLp.of_bound (hΦc.mul hgcont).aestronglyMeasurable (CΦ * Cg) (by
      filter_upwards [hbddG] with x hx
      simpa [Real.norm_eq_abs] using hx)
  have key := integral_mul_sq_le_of_memLp hmemΦ hmemG
  rw [hν] at key
  have h1 : (∫ x, Φ x * (Φ x * g x) ∂(volume.restrict (abox n ℓ)))
      = ∫ x in abox n ℓ, Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hg]; ring
  have h2 : (∫ x, (Φ x * g x) ^ 2 ∂(volume.restrict (abox n ℓ)))
      = ∫ x in abox n ℓ,
          Φ x ^ 2 * (∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hg]; ring
  have h3 : (∫ x, Φ x ^ 2 ∂(volume.restrict (abox n ℓ))) = ∫ x in abox n ℓ, Φ x ^ 2 := rfl
  rw [h1, h2, h3] at key
  exact key

/-! ## 3. The finite-sum expansion of the pair-condensate square -/

/-- **The expansion** `∫Φ²(Σᵢχ(xᵢ)²)² = Σᵢ∫Φ²χ(xᵢ)⁴ + ΣᵢΣ_{j≠i}∫Φ²χ(xᵢ)²χ(xⱼ)²`. -/
theorem flatSqExpand {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) {n : ℕ}
    {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox n ℓ, Φ x ^ 2 * (∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) ^ 2)
      = (∑ i : Fin n, ∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
        + ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
            ∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2
              * chiSmallB M ℓ d u (x j) ^ 2 := by
  classical
  have hcont (i : Fin n) : Continuous (fun x : X n => chiSmallB M ℓ d u (x i)) :=
    (Work.BoseFixB1.continuous_chiSmallB M ℓ d u).comp (continuous_apply i)
  have hpt : ∀ x : X n, Φ x ^ 2 * (∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) ^ 2
      = ∑ i : Fin n, ((Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
          + ∑ j ∈ (Finset.univ.erase i),
              Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2 * chiSmallB M ℓ d u (x j) ^ 2) := by
    intro x
    set a : Fin n → ℝ := fun i => chiSmallB M ℓ d u (x i) ^ 2 with ha
    have h0 : (∑ i : Fin n, a i) * (∑ i : Fin n, a i) = ∑ i : Fin n, ∑ j : Fin n, a i * a j := by
      have h := Finset.sum_mul_sum (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin n))
        a a
      simpa using h
    have hexp : (∑ i : Fin n, a i) ^ 2
        = ∑ i : Fin n, (a i * a i + ∑ j ∈ (Finset.univ.erase i), a i * a j) := by
      calc (∑ i : Fin n, a i) ^ 2 = (∑ i : Fin n, a i) * (∑ i : Fin n, a i) := by rw [sq]
        _ = ∑ i : Fin n, ∑ j : Fin n, a i * a j := h0
        _ = ∑ i : Fin n, (a i * a i + ∑ j ∈ (Finset.univ.erase i), a i * a j) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
    rw [hexp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_add, Finset.mul_sum]
    congr 1
    · simp only [ha]; ring
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [ha]; ring
  have hInt (i : Fin n) :
      IntegrableOn (fun x : X n => (Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
          + ∑ j ∈ (Finset.univ.erase i),
              Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2 * chiSmallB M ℓ d u (x j) ^ 2)
        (abox n ℓ) := by
    refine ContinuousOn.integrableOn_compact (abox_compact n hℓ) (Continuous.continuousOn ?_)
    refine Continuous.add ?_ ?_
    · exact (hΦc.pow 2).mul ((hcont i).pow 4)
    · refine continuous_finsetSum _ (fun j _ => ?_)
      exact ((hΦc.pow 2).mul ((hcont i).pow 2)).mul ((hcont j).pow 2)
  have hstep1 : (∫ x in abox n ℓ, Φ x ^ 2 * (∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) ^ 2)
      = ∑ i : Fin n, ∫ x in abox n ℓ, ((Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
          + ∑ j ∈ (Finset.univ.erase i),
              Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2 * chiSmallB M ℓ d u (x j) ^ 2) := by
    rw [show (∫ x in abox n ℓ, Φ x ^ 2 * (∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) ^ 2)
        = ∫ x in abox n ℓ, ∑ i : Fin n, ((Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
            + ∑ j ∈ (Finset.univ.erase i),
                Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2 * chiSmallB M ℓ d u (x j) ^ 2) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_finsetSum _ (fun i _ => hInt i)
  have hstep2 (i : Fin n) :
      (∫ x in abox n ℓ, ((Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
          + ∑ j ∈ (Finset.univ.erase i),
              Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2 * chiSmallB M ℓ d u (x j) ^ 2))
        = (∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
          + ∑ j ∈ (Finset.univ.erase i),
              ∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2
                * chiSmallB M ℓ d u (x j) ^ 2 := by
    have hA : IntegrableOn (fun x : X n =>
        Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4) (abox n ℓ) :=
      ContinuousOn.integrableOn_compact (abox_compact n hℓ)
        ((hΦc.pow 2).mul ((hcont i).pow 4)).continuousOn
    have hB : IntegrableOn (fun x : X n => ∑ j ∈ (Finset.univ.erase i),
        Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2 * chiSmallB M ℓ d u (x j) ^ 2) (abox n ℓ) :=
      integrable_finsetSum _ (fun j _ =>
        ContinuousOn.integrableOn_compact (abox_compact n hℓ)
          (((hΦc.pow 2).mul ((hcont i).pow 2)).mul ((hcont j).pow 2)).continuousOn)
    rw [MeasureTheory.integral_add hA hB]
    rw [show (∫ a in abox n ℓ, ∑ j ∈ (Finset.univ.erase i),
          Φ a ^ 2 * chiSmallB M ℓ d u (a i) ^ 2 * chiSmallB M ℓ d u (a j) ^ 2)
        = ∑ j ∈ (Finset.univ.erase i),
            ∫ a in abox n ℓ, Φ a ^ 2 * chiSmallB M ℓ d u (a i) ^ 2
              * chiSmallB M ℓ d u (a j) ^ 2 from
      MeasureTheory.integral_finsetSum (Finset.univ.erase i) (fun j _ =>
        ContinuousOn.integrableOn_compact (abox_compact n hℓ)
          (((hΦc.pow 2).mul ((hcont i).pow 2)).mul ((hcont j).pow 2)).continuousOn)]
  rw [hstep1]
  have hsum : (∑ i : Fin n, ∫ x in abox n ℓ, ((Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
        + ∑ j ∈ (Finset.univ.erase i),
            Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2 * chiSmallB M ℓ d u (x j) ^ 2))
      = ∑ i : Fin n, ((∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
          + ∑ j ∈ (Finset.univ.erase i),
              ∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2
                * chiSmallB M ℓ d u (x j) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => hstep2 i)
  rw [hsum, Finset.sum_add_distrib]

/-! ## 4. The diagonal count bound -/

/-- **The diagonal count bound, unconditionally**: with `Cχ := chiSupAbs·chiSmallDecay M`,

    Σᵢ∫Φ²χ(xᵢ)⁴ ≤ Cχ²·∫Φ²Σᵢχ(xᵢ)² .

(Pointwise `χ⁴ ≤ Cχ²·χ²`, integrated over the box.) -/
theorem flatD_le_chisup_mul_S {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) {n : ℕ}
    {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin n, ∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
      ≤ (chiSupAbs * chiSmallDecay M) ^ 2
          * ∫ x in abox n ℓ, Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2 := by
  classical
  have hcont (i : Fin n) : Continuous (fun x : X n => chiSmallB M ℓ d u (x i)) :=
    (Work.BoseFixB1.continuous_chiSmallB M ℓ d u).comp (continuous_apply i)
  have hpt : ∀ x : X n, (∑ i : Fin n, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
      ≤ (chiSupAbs * chiSmallDecay M) ^ 2
          * (Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) := by
    intro x
    have hb2 (i : Fin n) :
        Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4
          ≤ (chiSupAbs * chiSmallDecay M) ^ 2
              * (Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2) := by
      have hb := chiSmallB_abs_le_chisup (M := M) hM ℓ d u (x i)
      have h2 : (chiSmallB M ℓ d u (x i)) ^ 2 ≤ (chiSupAbs * chiSmallDecay M) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have h4 : (chiSmallB M ℓ d u (x i)) ^ 4
          ≤ (chiSupAbs * chiSmallDecay M) ^ 2 * (chiSmallB M ℓ d u (x i)) ^ 2 := by
        rw [show (chiSmallB M ℓ d u (x i)) ^ 4
            = (chiSmallB M ℓ d u (x i)) ^ 2 * (chiSmallB M ℓ d u (x i)) ^ 2 from by ring]
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg (chiSmallB M ℓ d u (x i)))
      calc Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4
          ≤ Φ x ^ 2 * ((chiSupAbs * chiSmallDecay M) ^ 2
              * (chiSmallB M ℓ d u (x i)) ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
        _ = (chiSupAbs * chiSmallDecay M) ^ 2
              * (Φ x ^ 2 * (chiSmallB M ℓ d u (x i)) ^ 2) := by ring
    calc (∑ i : Fin n, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
        ≤ ∑ i : Fin n, (chiSupAbs * chiSmallDecay M) ^ 2
            * (Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hb2 i)
      _ = (chiSupAbs * chiSmallDecay M) ^ 2
            * (Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hSumEq : (∫ x in abox n ℓ, ∑ i : Fin n, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
      = ∑ i : Fin n, ∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4 := by
    exact integral_finsetSum _ (fun i _ =>
      ContinuousOn.integrableOn_compact (abox_compact n hℓ)
        ((hΦc.pow 2).mul ((hcont i).pow 4)).continuousOn)
  have hIntL : IntegrableOn (fun x : X n =>
      ∑ i : Fin n, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4) (abox n ℓ) :=
    integrable_finsetSum _ (fun i _ =>
      ContinuousOn.integrableOn_compact (abox_compact n hℓ)
        ((hΦc.pow 2).mul ((hcont i).pow 4)).continuousOn)
  have hIntR : IntegrableOn (fun x : X n =>
      (chiSupAbs * chiSmallDecay M) ^ 2
        * (Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2)) (abox n ℓ) :=
    ContinuousOn.integrableOn_compact (abox_compact n hℓ) (Continuous.continuousOn
      (continuous_const.mul ((hΦc.pow 2).mul
        (continuous_finsetSum _ (fun i _ => (hcont i).pow 2)))))
  rw [← hSumEq]
  calc (∫ x in abox n ℓ, ∑ i : Fin n, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4)
      ≤ ∫ x in abox n ℓ, (chiSupAbs * chiSmallDecay M) ^ 2
          * (Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2) :=
        integral_mono hIntL hIntR hpt
    _ = (chiSupAbs * chiSmallDecay M) ^ 2
          * ∫ x in abox n ℓ, Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2 :=
        integral_const_mul _ _

/-! ## 5. The exactly-flat arithmetic at a free rate -/

/-- **`flatZeroOmega_le` at a free rate `δ ≥ 0`.**  The exactly-flat arithmetic
(`Work.BoseFixB1.Up.flatZeroOmega_le`) is stated with the box-volume rate `1/|B(u)|`; the state
facts that feed it (the `Y`-row and the diagonal bound) are true, however, at *any* rate `δ ≥ 0`
for which the `Y`-row holds — and the unconditional Cauchy–Schwarz route of this module supplies
`δ = Cχ²/κ`.  The statement below is the instantiation of the proved lemma at `A := δ⁻¹`: the
`τ/|B|`-term becomes `δτ` and the payers `W₂μ/|B| + 3W₂/(5|B|²)` become `W₂μδ + (3/5)W₂δ²`. -/
theorem flatOmegaDeltaB1 {μ W₁ W₂ κ τ Y Dn Cχ c₁ δ : ℝ}
    (hμ : 0 < μ) (hW₁ : 0 ≤ W₁) (hW : W₁ ≤ W₂) (hW₂ : 0 ≤ W₂) (hδ : 0 < δ) (hτ : 0 ≤ τ)
    (hκ : 0 ≤ κ) (hCχ : 0 ≤ Cχ) (hDnn : 0 ≤ Dn) (hDnle : Dn ≤ Cχ ^ 2 * τ / κ)
    (hc₁ : 0 < c₁) (hc₁4 : c₁ ≤ 1 / 4) (hc₁8 : 8 * c₁ * W₁ ≤ W₂)
    (hY : τ ^ 2 - δ * τ ≤ Y) :
    c₁ * W₁ * (μ * (τ - μ) ^ 2 / (τ + μ)) + μ * W₁ * τ - (1 / 2) * μ ^ 2 * W₁
      + (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * Dn
      + (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2 - (1 / 2) * W₂) * Y
      - (4 * c₁ * W₁ * μ ^ 2 / (τ + μ) ^ 2) * τ ^ 2
      ≤ W₂ * μ * δ + 8 * c₁ * W₁ * Cχ ^ 2 * μ / κ + (3 / 5) * W₂ * δ ^ 2
        + c₁ * W₁ * Cχ ^ 2 * μ / κ := by
  have hδinv : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
  have hY' : τ ^ 2 - τ / δ⁻¹ ≤ Y := by
    rw [div_inv_eq_mul, mul_comm]
    exact hY
  have h := Work.BoseFixB1.Up.flatZeroOmega_le (μ := μ) (W₁ := W₁) (W₂ := W₂) (κ := κ)
    (A := δ⁻¹) (τ := τ) (Y := Y) (Dn := Dn) (Cχ := Cχ) (c₁ := c₁)
    hμ hW₁ hW hW₂ hδinv hτ hκ hCχ hDnn hDnle hc₁ hc₁4 hc₁8 hY'
  have e1 : W₂ * μ / δ⁻¹ = W₂ * μ * δ := by rw [div_inv_eq_mul]
  have e2 : 3 * W₂ / (5 * δ⁻¹ ^ 2) = (3 / 5) * W₂ * δ ^ 2 := by
    rw [inv_pow]
    field_simp
  rw [e1, e2] at h
  linarith [h]

/-! ## 6. The unconditional `Y`-row -/

/-- **The pair-condensate (`Y`) row, for *every* box state.**
With `κ = chiMass M ℓ d u`, `N = ∫_{abox}Φ²`, `S = ∫Φ²Σᵢχ(xᵢ)²`, `X = ΣᵢΣ_{j≠i}∫Φ²χ(xᵢ)²χ(xⱼ)²`
and `Cχ = chiSupAbs·chiSmallDecay M`,

    (S/(κN))² − (Cχ²/κ)·(S/(κN)) ≤ (κ⁻²·X)/N .

(The peeled form `Work.BoseFixB1Up.flatPairJensen` is `(S/(κN))² − (S/(κN))/|B(u)| ≤ (κ⁻²X)/N`
but requires the exact flatness of `Φ`; here the rate is `Cχ²/κ` instead of `1/|B(u)|` and **no
state hypothesis is used beyond `κ > 0`, `N > 0`**.) -/
theorem flatXpJensenRaw {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) {n : ℕ}
    {Φ : X n → ℝ} (hΦc : Continuous Φ)
    (hκpos : 0 < Work.SmallBoxSliding.chiMass M ℓ d u)
    (hNpos : 0 < ∫ x in abox n ℓ, Φ x ^ 2) :
    ((∫ x in abox n ℓ, Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2)
          / (Work.SmallBoxSliding.chiMass M ℓ d u * ∫ x in abox n ℓ, Φ x ^ 2)) ^ 2
      - ((∫ x in abox n ℓ, Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2)
          / (Work.SmallBoxSliding.chiMass M ℓ d u * ∫ x in abox n ℓ, Φ x ^ 2))
          * ((chiSupAbs * chiSmallDecay M) ^ 2 / Work.SmallBoxSliding.chiMass M ℓ d u)
      ≤ ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹ ^ 2
            * ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
                ∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2
                  * chiSmallB M ℓ d u (x j) ^ 2)
          / ∫ x in abox n ℓ, Φ x ^ 2 := by
  classical
  set κ : ℝ := Work.SmallBoxSliding.chiMass M ℓ d u with hκ
  set N : ℝ := ∫ x in abox n ℓ, Φ x ^ 2 with hN
  set S : ℝ := ∫ x in abox n ℓ, Φ x ^ 2 * ∑ i : Fin n, chiSmallB M ℓ d u (x i) ^ 2 with hS
  set D : ℝ := ∑ i : Fin n, ∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 4 with hD
  set X : ℝ := ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
      ∫ x in abox n ℓ, Φ x ^ 2 * chiSmallB M ℓ d u (x i) ^ 2
        * chiSmallB M ℓ d u (x j) ^ 2 with hX
  set Cχ : ℝ := chiSupAbs * chiSmallDecay M with hCχ
  have hκpos' : 0 < κ := by rw [hκ]; exact hκpos
  have hNpos' : 0 < N := by rw [hN]; exact hNpos
  have hCS := flatSmoothCSRaw (M := M) (d := d) hM hℓ u hΦc
  have hexp := flatSqExpand (M := M) (d := d) hM hℓ u hΦc
  rw [← hD, ← hX] at hexp
  rw [← hS, ← hN, hexp] at hCS
  have hDle := flatD_le_chisup_mul_S (M := M) (d := d) hM hℓ u hΦc
  rw [← hS, ← hD, ← hCχ] at hDle
  have hkey : S ^ 2 ≤ N * (Cχ ^ 2 * S + X) := by nlinarith [hCS, hDle]
  have h1 : S ^ 2 / N ≤ Cχ ^ 2 * S + X := by
    rw [div_le_iff₀ hNpos']; linarith [hkey]
  have h2 : S ^ 2 / N - Cχ ^ 2 * S ≤ X := by linarith [h1]
  have hκ2N : (0 : ℝ) < κ ^ 2 * N := mul_pos (pow_pos hκpos' 2) hNpos'
  have h3 : (S ^ 2 / N - Cχ ^ 2 * S) / (κ ^ 2 * N) ≤ X / (κ ^ 2 * N) :=
    div_le_div_of_nonneg_right h2 hκ2N.le
  have hid : (S / (κ * N)) ^ 2 - (S / (κ * N)) * (Cχ ^ 2 / κ)
      = (S ^ 2 / N - Cχ ^ 2 * S) / (κ ^ 2 * N) := by
    have hκN : κ * N ≠ 0 := ne_of_gt (mul_pos hκpos' hNpos')
    have hκne : κ ≠ 0 := ne_of_gt hκpos'
    field_simp
  have hid2 : (κ⁻¹ ^ 2 * X) / N = X / (κ ^ 2 * N) := by
    have hNne : N ≠ 0 := ne_of_gt hNpos'
    field_simp
  rw [hid, hid2]
  exact h3

/-! ## 7. The `Y`-row at FS's parameters -/

/-- **The pair-condensate row at FS's parameters, for *every* box state of the sliding box.**
`flatTau` is the smooth density, `flatXp` the pair-condensate count and `chiMass` the cutoff mass;
`Cχ = chiSupAbs·chiSmallDecay M` is the (fixed) bump constant.  **No flatness hypothesis.** -/
theorem flatTauJensenAllB1 {v : E3 → ℝ} {μ : ℝ} {n : ℕ} {u : E3}
    {Φ : X n → ℝ} (hΦc : Continuous Φ)
    (hℓ : 0 < Work.BoseFixB1.pL v μ)
    (hκpos : 0 < Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u)
    (hNpos : 0 < Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) Φ) :
    (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u Φ) ^ 2
      - (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u Φ)
          * ((chiSupAbs * chiSmallDecay (Work.BoseFixB1.pM v μ)) ^ 2
              / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
      ≤ Work.BoseFixB1.Up.flatXp v μ Φ u
          / Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) Φ := by
  have hMb : 1 ≤ Work.BoseFixB1.pM v μ := by
    rw [Work.BoseFixB1.pM, Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have h := flatXpJensenRaw (M := Work.BoseFixB1.pM v μ) hMb (ℓ := Work.BoseFixB1.pL v μ)
    (d := Work.BoseFixB1.pD v μ) hℓ u hΦc hκpos hNpos
  simpa only [Work.BoseFixB1.flatTau, Work.BoseFixB1.flatScountB, Work.BoseFixB1.nCountB,
    Work.BoseFixB1.Up.flatXp, Work.BoseFixB1.flatMass] using h

/-- **The same `Y`-row in the `normB` vocabulary**, i.e. in exactly the shape the flat-branch
ledger (`Work.BoseFixB1S.perBoxF_of_ledger_sharp`, `Up.perBoxF_of_ledger_kin`) consumes it:
`flatMass (pL v μ) Φ` *is* `normB v μ n Φ` (both are `∫_{abox n (pL v μ)} Φ²`). -/
theorem flatTauJensenNormB {v : E3 → ℝ} {μ : ℝ} {n : ℕ} {u : E3}
    {Φ : X n → ℝ} (hΦc : Continuous Φ)
    (hℓ : 0 < Work.BoseFixB1.pL v μ)
    (hκpos : 0 < Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u)
    (hNpos : 0 < Work.BoseBoxFix.normB v μ n Φ) :
    (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u Φ) ^ 2
      - (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u Φ)
          * ((chiSupAbs * chiSmallDecay (Work.BoseFixB1.pM v μ)) ^ 2
              / Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
      ≤ Work.BoseFixB1.Up.flatXp v μ Φ u / Work.BoseBoxFix.normB v μ n Φ := by
  have h := flatTauJensenAllB1 (v := v) (μ := μ) (n := n) (u := u) (Φ := Φ) hΦc hℓ hκpos
    (by simpa only [Work.BoseFixB1.flatMass, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
        using hNpos)
  simpa only [Work.BoseFixB1.flatMass, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] using h

end Work.BoseFixB1S
