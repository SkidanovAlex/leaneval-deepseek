import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.WB.cs_weight_int
import Submission.Work.BoseFixB1.WB.peel_aP_g
import Submission.Work.BoseFixB1.WB.pq_arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.pq_split_meas` — the `P/Q`-split with a.e.-measurable `g`

FS's `P/Q`-split of the one-body term `∫_Λ Φ² Σᵢ g(xᵢ)` of `thm:aprioriHLambda`
step 4 (`Submission/Work/BoseFixB1/WB/Defs.lean`, item "the `P/Q`-split"): with
`Pᵢ = aP ℓ i` the mean over the centred box in slot `i` and `Qᵢ = 1 − Pᵢ`,

  `(1−ε)(Tvol/ℓ³)Σᵢ‖PᵢΦ‖² − (1+ε⁻¹)KU Σᵢ‖QᵢΦ‖²
      ≤ ∫ Φ² Σᵢ g(xᵢ) ≤ (1+ε)(Tvol/ℓ³)Σᵢ‖PᵢΦ‖² + (1+ε⁻¹)KU Σᵢ‖QᵢΦ‖²`

for `0 ≤ g ≤ KU` with `∫_{Λ(ℓ)} g = Tvol`.

The per-slot content: writing `Φ = PᵢΦ + QᵢΦ` in slot `i` and using that `PᵢΦ`
does not depend on the value of slot `i` (so that the exact identity
`∫ (PᵢΦ)² g(xᵢ) = (Tvol/ℓ³)∫(PᵢΦ)²` holds, `peel_aP_g`), the cross term is
controlled by the weighted Cauchy–Schwarz inequality (`cs_weight_int`) and
`∫(QᵢΦ)² g(xᵢ) ≤ KU ∫(QᵢΦ)²`; the `ε`-bookkeeping is `pq_arith`.

This file is the a.e.-measurable version of `WB.pq_split` (the extra hypotheses
`hgm`, `hint` are what the peel needs).
-/

namespace Work.BoseFixB1.WB

open MeasureTheory
open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## Measurability of a coordinate -/

/-- A single coordinate of `X N` is quasi-measure-preserving for Lebesgue measure. -/
lemma qmp_coord_X {N : ℕ} (i : Fin N) :
    Measure.QuasiMeasurePreserving (fun x : X N => x i)
      (MeasureTheory.volume : Measure (X N))
      (MeasureTheory.volume : Measure ℝ³) := by
  have h := Measure.quasiMeasurePreserving_eval
    (fun _ : Fin N => (MeasureTheory.volume : Measure ℝ³)) i
  rw [← MeasureTheory.volume_pi] at h
  exact h

/-- The coordinate function `x ↦ g (x i)` is a.e. strongly measurable on the box. -/
lemma aestronglyMeasurable_coord {N : ℕ} (ℓ : ℝ) (i : Fin N) {g : ℝ³ → ℝ}
    (hgm : AEMeasurable g (MeasureTheory.volume : Measure ℝ³)) :
    AEStronglyMeasurable (fun x : X N => g (x i))
      ((MeasureTheory.volume : Measure (X N)).restrict (abox N ℓ)) :=
  ((hgm.comp_quasiMeasurePreserving (qmp_coord_X i)).restrict).aestronglyMeasurable

/-! ## Integrability of `F x · g (x i)` for bounded measurable `F` -/

lemma integrableOn_mul_coord_g {n : ℕ} {ℓ KU : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1))
    {g : ℝ³ → ℝ} (hgm : AEMeasurable g (MeasureTheory.volume : Measure ℝ³))
    (hg : ∀ z : ℝ³, 0 ≤ g z) (hKU : ∀ z : ℝ³, g z ≤ KU)
    {F : X (n + 1) → ℝ}
    (hFm : AEStronglyMeasurable F
      ((MeasureTheory.volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)))
    {C : ℝ} (hC0 : 0 ≤ C) (hFb : ∀ x ∈ abox (n + 1) ℓ, |F x| ≤ C) :
    IntegrableOn (fun x => F x * g (x i)) (abox (n + 1) ℓ) MeasureTheory.volume := by
  have hKU0 : 0 ≤ KU := le_trans (hg 0) (hKU 0)
  refine IntegrableOn.of_bound (abox_lt_top (n + 1) ℓ hℓ.le) ?_ (C * KU) ?_
  · exact hFm.mul (aestronglyMeasurable_coord ℓ i hgm)
  · rw [ae_restrict_iff' (abox_measurable (n + 1) ℓ)]
    refine ae_of_all _ (fun x hx => ?_)
    have h2 : |g (x i)| ≤ KU := abs_le.mpr ⟨by linarith [hg (x i)], hKU (x i)⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hFb x hx) h2 (abs_nonneg _) hC0

/-! ## Elementary absolute-value bounds -/

lemma sq_le_sq_of_abs_le {a B : ℝ} (h : |a| ≤ B) : a ^ 2 ≤ B ^ 2 := by
  rw [← sq_abs a]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

lemma abs_mul_le_mul' {a b B C : ℝ} (h1 : |a| ≤ B) (h2 : |b| ≤ C) :
    |a * b| ≤ B * C := by
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)

lemma abs_sq_le {a B : ℝ} (h : |a| ≤ B) : |a ^ 2| ≤ B ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq_of_abs_le h

/-! ## The per-slot bound -/

theorem slot_bound {n : ℕ} {ℓ Tvol KU ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) (i : Fin (n + 1))
    {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ)
    {g : ℝ³ → ℝ} (hgm : AEMeasurable g MeasureTheory.volume)
    (hint : IntegrableOn g (acube ℓ) MeasureTheory.volume)
    (hg : ∀ z : ℝ³, 0 ≤ g z) (hTvol : (∫ z in acube ℓ, g z) = Tvol)
    (hKU : ∀ z : ℝ³, g z ≤ KU) :
    ((∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i))
        ≤ (1 + ε) * (Tvol / ℓ ^ 3) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
          + (1 + ε⁻¹) * KU * (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2))
      ∧ ((1 - ε) * (Tvol / ℓ ^ 3) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
          - (1 + ε⁻¹) * KU * (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2)
        ≤ ∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i)) := by
  have hKU0 : 0 ≤ KU := le_trans (hg 0) (hKU 0)
  -- bounds of `Φ` and of its sector projections on the box
  obtain ⟨B, hB⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
    (s := abox (n + 1) ℓ) (f := Φ) hΦ.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (Φ 0)) (hB 0 (zero_mem_abox hℓ.le))
  have hΦB : ∀ x ∈ abox (n + 1) ℓ, |Φ x| ≤ B :=
    fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
  have hPb : ∀ x ∈ abox (n + 1) ℓ, |aP ℓ i Φ x| ≤ B := aP_abs_le hℓ i hΦ hB0 hΦB
  have hQb : ∀ x ∈ abox (n + 1) ℓ, |aQ ℓ i Φ x| ≤ 2 * B := by
    intro x hx
    have h1 := hΦB x hx
    have h2 := hPb x hx
    have h3 : |Φ x - aP ℓ i Φ x| ≤ |Φ x| + |aP ℓ i Φ x| := by
      simpa using norm_sub_le (Φ x) (aP ℓ i Φ x)
    have haQ : aQ ℓ i Φ x = Φ x - aP ℓ i Φ x := rfl
    rw [haQ]
    linarith
  -- integrability of the relevant products
  have hIntP : IntegrableOn (fun x => (aP ℓ i Φ x) ^ 2 * g (x i)) (abox (n + 1) ℓ)
      MeasureTheory.volume :=
    integrableOn_mul_coord_g hℓ i hgm hg hKU
      ((integrableOn_sq_aP hℓ i hΦ).aestronglyMeasurable) (sq_nonneg B)
      (fun x hx => abs_sq_le (hPb x hx))
  have hIntQ : IntegrableOn (fun x => (aQ ℓ i Φ x) ^ 2 * g (x i)) (abox (n + 1) ℓ)
      MeasureTheory.volume :=
    integrableOn_mul_coord_g hℓ i hgm hg hKU
      ((integrableOn_sq_aQ hℓ i hΦ).aestronglyMeasurable) (sq_nonneg (2 * B))
      (fun x hx => abs_sq_le (hQb x hx))
  have haPAE : AEStronglyMeasurable (fun x : X (n + 1) => aP ℓ i Φ x)
      ((MeasureTheory.volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) :=
    aP_aestronglyMeasurable hℓ i hΦ
  have haQAE := (hΦ.aestronglyMeasurable.restrict).sub haPAE
  have hIntPQ : IntegrableOn (fun x => (aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i))
      (abox (n + 1) ℓ) MeasureTheory.volume :=
    integrableOn_mul_coord_g hℓ i hgm hg hKU (haPAE.mul haQAE)
      (mul_nonneg hB0 (by linarith))
      (fun x hx => abs_mul_le_mul' (hPb x hx) (hQb x hx))
  have hIntG : IntegrableOn (fun x => (Φ x) ^ 2 * g (x i)) (abox (n + 1) ℓ)
      MeasureTheory.volume :=
    integrableOn_mul_coord_g hℓ i hgm hg hKU
      (hΦ.aestronglyMeasurable.restrict.pow 2) (sq_nonneg B)
      (fun x hx => abs_sq_le (hΦB x hx))
  have hIntP2 : IntegrableOn
      (fun x => (aP ℓ i Φ x) ^ 2 * g (x i) + 2 * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i)))
      (abox (n + 1) ℓ) MeasureTheory.volume :=
    hIntP.add (hIntPQ.const_mul 2)
  have hIntQ2 : IntegrableOn (fun x => (aQ ℓ i Φ x) ^ 2) (abox (n + 1) ℓ)
      MeasureTheory.volume := integrableOn_sq_aQ hℓ i hΦ
  -- the exact peel identity for the `P` part
  have hpeel : (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i))
      = (Tvol / ℓ ^ 3) * ∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 :=
    peel_aP_g hℓ i hΦ hgm hint hg hTvol hKU
  -- the weighted Cauchy--Schwarz bound on the cross term
  have hCS : |∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i)|
      ≤ Real.sqrt (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i))
        * Real.sqrt (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 * g (x i)) :=
    cs_weight_int ((MeasureTheory.volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ))
      (w := fun x => g (x i)) (f := fun x => aP ℓ i Φ x) (h := fun x => aQ ℓ i Φ x)
      (ae_of_all _ (fun x => hg (x i))) hIntP hIntQ hIntPQ
  -- monotonicity of the `Q` part
  have hKs : IntegrableOn (fun x => (aQ ℓ i Φ x) ^ 2 * KU) (abox (n + 1) ℓ)
      MeasureTheory.volume := hIntQ2.mul_const KU
  have hT3le : (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 * g (x i))
      ≤ KU * ∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 := by
    have hmono := setIntegral_mono_on hIntQ hKs (abox_measurable (n + 1) ℓ)
      (fun x hx => by
        have h1 : g (x i) ≤ KU := hKU (x i)
        nlinarith [sq_nonneg (aQ ℓ i Φ x)])
    rw [MeasureTheory.integral_mul_const] at hmono
    linarith
  -- nonnegativity
  have hT1nn : 0 ≤ ∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hg (x i))
  have hT3nn : 0 ≤ ∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 * g (x i) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hg (x i))
  have hQnn : 0 ≤ ∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  -- the splitting `Φ² = (PᵢΦ)² + 2 PᵢΦ QᵢΦ + (QᵢΦ)²`
  have hGsplit : (∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i))
      = (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i))
        + 2 * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i))
        + (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 * g (x i)) := by
    have hpt : ∀ x : X (n + 1),
        (Φ x) ^ 2 * g (x i) = (aP ℓ i Φ x) ^ 2 * g (x i)
            + 2 * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i))
            + (aQ ℓ i Φ x) ^ 2 * g (x i) := by
      intro x
      have h : Φ x = aP ℓ i Φ x + aQ ℓ i Φ x := by
        unfold aQ
        ring
      rw [h]
      ring
    calc (∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i))
        = ∫ x in abox (n + 1) ℓ, ((aP ℓ i Φ x) ^ 2 * g (x i)
            + 2 * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i))
            + (aQ ℓ i Φ x) ^ 2 * g (x i)) :=
          setIntegral_congr_fun (abox_measurable (n + 1) ℓ) (fun x _ => hpt x)
      _ = (∫ x in abox (n + 1) ℓ, ((aP ℓ i Φ x) ^ 2 * g (x i)
              + 2 * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i))))
            + (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 * g (x i)) := by
          rw [MeasureTheory.integral_add hIntP2 hIntQ]
      _ = ((∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i))
              + (∫ x in abox (n + 1) ℓ, 2 * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i))))
            + (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 * g (x i)) := by
          rw [MeasureTheory.integral_add hIntP (hIntPQ.const_mul 2)]
      _ = ((∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i))
              + 2 * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i)))
            + (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 * g (x i)) := by
          rw [MeasureTheory.integral_const_mul]
      _ = _ := rfl
  -- the `ε`-bookkeeping
  obtain ⟨hup, hlow⟩ := pq_arith (A := ∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i))
    (B := KU * ∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2)
    (T := ∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2 * g (x i))
    (C := ∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * g (x i))
    (ε := ε) hT1nn (mul_nonneg hKU0 hQnn) hT3nn hT3le hε hCS
  have e1 : (1 + ε) * (Tvol / ℓ ^ 3) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
      = (1 + ε) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i)) := by
    rw [hpeel]
    ring
  have e1' : (1 - ε) * (Tvol / ℓ ^ 3) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
      = (1 - ε) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i)) := by
    rw [hpeel]
    ring
  have e2 : (1 + ε⁻¹) * KU * (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2)
      = (1 + ε⁻¹) * (KU * ∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2) := by
    ring
  constructor
  · rw [hGsplit, e1, e2]
    exact hup
  · rw [hGsplit, e1', e2]
    exact hlow

/-! ## The main theorem -/

theorem pq_split_meas {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ)
    {g : ℝ³ → ℝ} {Tvol KU ε : ℝ} (hε : 0 < ε)
    (hgm : AEMeasurable g MeasureTheory.volume)
    (hint : MeasureTheory.IntegrableOn g (Submission.BoseGases.acube ℓ))
    (hg : ∀ z : ℝ³, 0 ≤ g z) (hTvol : (∫ z in Submission.BoseGases.acube ℓ, g z) = Tvol)
    (hKU : ∀ z : ℝ³, g z ≤ KU) :
    ((∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, g (x i)))
        ≤ (1 + ε) * (Tvol / ℓ ^ 3)
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
          + (1 + ε⁻¹) * KU
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2))
      ∧ ((1 - ε) * (Tvol / ℓ ^ 3)
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
          - (1 + ε⁻¹) * KU
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, g (x i))) := by
  rcases N with _ | n
  · constructor <;> simp
  · have hslot : ∀ i : Fin (n + 1),
        ((∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i))
            ≤ (1 + ε) * (Tvol / ℓ ^ 3) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
              + (1 + ε⁻¹) * KU * (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2))
          ∧ ((1 - ε) * (Tvol / ℓ ^ 3) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
              - (1 + ε⁻¹) * KU * (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2)
            ≤ ∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i)) :=
      fun i => slot_bound hℓ hε i hΦ hgm hint hg hTvol hKU
    obtain ⟨B, hB⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
      (s := abox (n + 1) ℓ) (f := Φ) hΦ.continuousOn
    have hB0 : 0 ≤ B := le_trans (norm_nonneg (Φ 0)) (hB 0 (zero_mem_abox hℓ.le))
    have hΦB : ∀ x ∈ abox (n + 1) ℓ, |Φ x| ≤ B :=
      fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
    have hGsum : (∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * (∑ i : Fin (n + 1), g (x i)))
        = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i) := by
      calc (∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * (∑ i : Fin (n + 1), g (x i)))
          = ∫ x in abox (n + 1) ℓ, (∑ i : Fin (n + 1), (Φ x) ^ 2 * g (x i)) := by
            apply setIntegral_congr_fun (abox_measurable (n + 1) ℓ)
            intro x _
            simp only [Finset.mul_sum]
        _ = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i) := by
            rw [MeasureTheory.integral_finsetSum]
            intro i _
            exact integrableOn_mul_coord_g hℓ i hgm hg hKU
              (hΦ.aestronglyMeasurable.restrict.pow 2) (sq_nonneg B)
              (fun x hx => abs_sq_le (hΦB x hx))
    constructor
    · rw [hGsum]
      calc ∑ i : Fin (n + 1), ∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i)
          ≤ ∑ i : Fin (n + 1), ((1 + ε) * (Tvol / ℓ ^ 3) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
              + (1 + ε⁻¹) * KU * (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2)) :=
            Finset.sum_le_sum (fun i _ => (hslot i).1)
        _ = (1 + ε) * (Tvol / ℓ ^ 3)
              * (∑ i : Fin (n + 1), ∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
            + (1 + ε⁻¹) * KU
              * (∑ i : Fin (n + 1), ∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    · rw [hGsum]
      calc (1 - ε) * (Tvol / ℓ ^ 3)
              * (∑ i : Fin (n + 1), ∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
            - (1 + ε⁻¹) * KU
              * (∑ i : Fin (n + 1), ∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2)
          = ∑ i : Fin (n + 1), ((1 - ε) * (Tvol / ℓ ^ 3) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
              - (1 + ε⁻¹) * KU * (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2)) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ ∑ i : Fin (n + 1), ∫ x in abox (n + 1) ℓ, (Φ x) ^ 2 * g (x i) :=
            Finset.sum_le_sum (fun i _ => (hslot i).2)

end Work.BoseFixB1.WB
