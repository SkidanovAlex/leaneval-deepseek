import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Quant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.yMass_two_le_cnPlus`

At `N = 2`, on the single pair `(0,1)` and with the *unweighted* box integral, the `4Q`-bracket
remainder `Y := q4B ℓ (omC ω) Φ (0,1) − ω(x₀−x₁)·P₀P₁Φ` is bounded by the excited count:

    ∫_{abox 2 ℓ} Y² ≤ 14·cnPlus ℓ Φ .

The proof is the pointwise algebra of `Y` (`Y = Q₁Q₀Φ + ω·(P₁Q₀Φ + Q₁P₀Φ)`, the `P₁P₀ = P₀P₁`
term cancelling), the a.e. bound `0 ≤ ω(x₀−x₁) ≤ 1` (transported from the hypotheses on `ω` by
`ae_pair_pullback`), the elementary square bound `(a + w·s)² ≤ 2a² + 4b² + 4c²` for
`0 ≤ w ≤ 1`, and the two projection contractions `∫(QᵢΨ)² ≤ ∫Ψ²` (`integral_aQ_sq_le`) and
`∫(PᵢΨ)² ≤ ∫Ψ²` (`aP_sq_le`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

theorem yMass_two_le_cnPlus {ℓ : ℝ} (hℓ : 0 < ℓ)
    {ω : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hω0 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))), 0 ≤ ω x)
    (hω1 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))), ω x ≤ 1)
    {Φ : Submission.BoseGases.X 2 → ℝ} (hΦc : Continuous Φ) :
    ∫ x in Submission.BoseGases.abox 2 ℓ,
      (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (0, 1) x
        - ω (x 0 - x 1) * Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x) ^ 2
      ≤ 14 * Submission.BoseGases.cnPlus ℓ Φ := by
  classical
  -- ## continuity of the individual pieces
  have hQ0c : Continuous (Submission.BoseGases.aQ ℓ 0 Φ) :=
    Submission.BoseGases.aQ_continuous hℓ 0 hΦc
  have hQ1c : Continuous (Submission.BoseGases.aQ ℓ 1 Φ) :=
    Submission.BoseGases.aQ_continuous hℓ 1 hΦc
  have hQQc : Continuous (fun x : Submission.BoseGases.X 2 =>
      Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) :=
    Submission.BoseGases.aQ_continuous hℓ 1 hQ0c
  have hPQc : Continuous (fun x : Submission.BoseGases.X 2 =>
      Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) :=
    Submission.BoseGases.aP_continuous hℓ 1 hQ0c
  have hQPc : Continuous (fun x : Submission.BoseGases.X 2 =>
      Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) :=
    Submission.BoseGases.aQ_continuous hℓ 1 (Submission.BoseGases.aP_continuous hℓ 0 hΦc)
  -- ## the pointwise decomposition of `Y`
  have hdecomp : ∀ x : Submission.BoseGases.X 2,
      Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (0, 1) x
        - ω (x 0 - x 1) * Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x
      = Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
        + ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
            + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) := by
    intro x
    have hcomm := Submission.BoseGases.aP_comm hℓ (1 : Fin 2) (0 : Fin 2) (Φ := Φ) hΦc x
    simp only [Submission.BoseGases.q4B, Submission.BoseGases.omC]
    rw [hcomm]
    ring
  -- ## the a.e. bound on the coupling `ω(x₀−x₁)`
  have hW : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)),
      0 ≤ ω (x 0 - x 1) ∧ ω (x 0 - x 1) ≤ 1 :=
    Submission.BoseGases.ae_pair_pullback hℓ (i := (0 : Fin 2)) (j := 1) (by decide)
      (hω0.and hω1)
  -- ## the elementary square bound, a.e.
  have hle : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)),
      (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
        + ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
            + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x)) ^ 2
      ≤ 2 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
        + 4 * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
        + 4 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2 := by
    filter_upwards [hW] with x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hw2 : (ω (x 0 - x 1)) ^ 2 ≤ 1 := by nlinarith
    have hs1 : (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
          + ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x)) ^ 2
        ≤ 2 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
          + 2 * (ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x)) ^ 2 := by
      nlinarith [sq_nonneg (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
        - ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
            + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x))]
    have hs2 : (ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x)) ^ 2
        ≤ (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2 := by
      nlinarith [sq_nonneg (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x), hw2]
    have hs3 : (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2
        ≤ 2 * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
          + 2 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2 := by
      nlinarith [sq_nonneg (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              - Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x)]
    linarith
  -- ## integrability of the comparison integrand
  have hQQint : Integrable (fun x : Submission.BoseGases.X 2 =>
        (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hQQc.pow 2)
  have hPQint : Integrable (fun x : Submission.BoseGases.X 2 =>
        (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hPQc.pow 2)
  have hQPint : Integrable (fun x : Submission.BoseGases.X 2 =>
        (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hQPc.pow 2)
  have hGint : Integrable (fun x : Submission.BoseGases.X 2 =>
        2 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
        + 4 * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
        + 4 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ)) :=
    ((hQQint.const_mul 2).add (hPQint.const_mul 4)).add (hQPint.const_mul 4)
  -- ## the two contractions against `cnPlus`
  have hcnPlus : Submission.BoseGases.cnPlus ℓ Φ
      = (∫ x in Submission.BoseGases.abox 2 ℓ, (Submission.BoseGases.aQ ℓ 0 Φ x) ^ 2)
        + (∫ x in Submission.BoseGases.abox 2 ℓ, (Submission.BoseGases.aQ ℓ 1 Φ x) ^ 2) := by
    rw [Submission.BoseGases.cnPlus, Fin.sum_univ_two]
  have hcn0 : (∫ x in Submission.BoseGases.abox 2 ℓ, (Submission.BoseGases.aQ ℓ 0 Φ x) ^ 2)
      ≤ Submission.BoseGases.cnPlus ℓ Φ := by
    have hnn : (0 : ℝ) ≤
        ∫ x in Submission.BoseGases.abox 2 ℓ, (Submission.BoseGases.aQ ℓ 1 Φ x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    rw [hcnPlus]; linarith
  have hcn1 : (∫ x in Submission.BoseGases.abox 2 ℓ, (Submission.BoseGases.aQ ℓ 1 Φ x) ^ 2)
      ≤ Submission.BoseGases.cnPlus ℓ Φ := by
    have hnn : (0 : ℝ) ≤
        ∫ x in Submission.BoseGases.abox 2 ℓ, (Submission.BoseGases.aQ ℓ 0 Φ x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    rw [hcnPlus]; linarith
  have hQQle : (∫ x in Submission.BoseGases.abox 2 ℓ,
        (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2)
      ≤ Submission.BoseGases.cnPlus ℓ Φ :=
    le_trans (Submission.BoseGases.integral_aQ_sq_le hℓ 1 hQ0c) hcn0
  have hPQle : (∫ x in Submission.BoseGases.abox 2 ℓ,
        (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2)
      ≤ Submission.BoseGases.cnPlus ℓ Φ :=
    le_trans (Submission.BoseGases.aP_sq_le hℓ 1 hQ0c) hcn0
  have hQP_eq : (∫ x in Submission.BoseGases.abox 2 ℓ,
        (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2)
      = (∫ x in Submission.BoseGases.abox 2 ℓ,
        (Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aQ ℓ 1 Φ) x) ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2
      = (Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aQ ℓ 1 Φ) x) ^ 2
    rw [Submission.BoseGases.aP_aQ_comm hℓ (show (0 : Fin 2) ≠ 1 by decide) (Φ := Φ) hΦc x]
  have hQPle : (∫ x in Submission.BoseGases.abox 2 ℓ,
        (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2)
      ≤ Submission.BoseGases.cnPlus ℓ Φ :=
    calc (∫ x in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2)
        = (∫ x in Submission.BoseGases.abox 2 ℓ,
          (Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aQ ℓ 1 Φ) x) ^ 2) := hQP_eq
      _ ≤ (∫ x in Submission.BoseGases.abox 2 ℓ, (Submission.BoseGases.aQ ℓ 1 Φ x) ^ 2) :=
          Submission.BoseGases.aP_sq_le hℓ 0 hQ1c
      _ ≤ Submission.BoseGases.cnPlus ℓ Φ := hcn1
  -- ## the comparison integral, evaluated
  have hsplit : (∫ x in Submission.BoseGases.abox 2 ℓ,
        (2 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
          + 4 * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
          + 4 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2))
      = 2 * (∫ x in Submission.BoseGases.abox 2 ℓ,
            (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2)
        + 4 * (∫ x in Submission.BoseGases.abox 2 ℓ,
            (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2)
        + 4 * (∫ x in Submission.BoseGases.abox 2 ℓ,
            (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2) := by
    rw [MeasureTheory.integral_add
          (f := fun x : Submission.BoseGases.X 2 =>
            2 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
              + 4 * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2)
          (g := fun x : Submission.BoseGases.X 2 =>
            4 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2)
          ((hQQint.const_mul 2).add (hPQint.const_mul 4)) (hQPint.const_mul 4),
      MeasureTheory.integral_add
          (f := fun x : Submission.BoseGases.X 2 =>
            2 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2)
          (g := fun x : Submission.BoseGases.X 2 =>
            4 * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2)
          (hQQint.const_mul 2) (hPQint.const_mul 4),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  have hcnnn : (0 : ℝ) ≤ Submission.BoseGases.cnPlus ℓ Φ := Work.BoseFixB3.cnPlus_nonneg Φ
  have hGle : (∫ x in Submission.BoseGases.abox 2 ℓ,
        (2 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
          + 4 * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x) ^ 2
          + 4 * (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x) ^ 2))
      ≤ 14 * Submission.BoseGases.cnPlus ℓ Φ := by
    rw [hsplit]
    linarith [hQQle, hPQle, hQPle, hcnnn]
  -- ## replace `Y²` by the decomposed square, then compare
  have hcongr : (∫ x in Submission.BoseGases.abox 2 ℓ,
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (0, 1) x
          - ω (x 0 - x 1) * Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox 2 ℓ,
        (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
          + ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x)) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC ω) Φ (0, 1) x
          - ω (x 0 - x 1) * Submission.BoseGases.aP ℓ 0 (Submission.BoseGases.aP ℓ 1 Φ) x) ^ 2
      = (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
          + ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x)) ^ 2
    rw [hdecomp x]
  rw [hcongr]
  by_cases hint : Integrable (fun x : Submission.BoseGases.X 2 =>
      (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
        + ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
            + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x)) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox 2 ℓ))
  · exact le_trans (integral_mono_ae hint hGint hle) hGle
  · have h0 : (∫ x in Submission.BoseGases.abox 2 ℓ,
        (Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
          + ω (x 0 - x 1) * (Submission.BoseGases.aP ℓ 1 (Submission.BoseGases.aQ ℓ 0 Φ) x
              + Submission.BoseGases.aQ ℓ 1 (Submission.BoseGases.aP ℓ 0 Φ) x)) ^ 2) = 0 :=
      MeasureTheory.integral_undef hint
    rw [h0]
    linarith [hcnnn]

end Work.BoseFixB3.CS.Pieces
