import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.Pieces.CS_pair_hyps_of_integrable
import Submission.Work.BoseFixB3.CS.Pieces.ae_bounded_q4B_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.CS_box_hyps_of_integrable`

The **last five conjuncts** of `Pieces.CS_side_hyps` (the integrability over
`volume.restrict (abox n ℓ)` of the `4Q`-square, the double-`Q` mass, the two `(PQ+QP)`-masses
and the `q4B − ω·P₁P₂Φ` square), *with the missing standing hypothesis*
`MeasureTheory.Integrable v` added.

Each conjunct is `IntegrableOn (fun x ↦ (f x)^2 * wLoc ℓ v 0 (x p.1) (x p.2)) (abox n ℓ)`, with
`f` a slot expression that is either continuous in `x` (hence bounded on the compact box
`abox n ℓ`) or the `q4B`-combination, for which `Pieces.ae_bounded_q4B_abox` supplies both
a.e.-strong-measurability and an a.e. bound (via `0 ≤ w₀ ≤ 1` a.e.,
`Submission.BoseGases.scattering_bounds_ae`, pulled back by
`Submission.BoseGases.ae_pair_pullback`).  The passage from `wLoc ℓ · 0` to `wPair ℓ ·`
(`wLoc_zero_eq_wPair'`) reduces each conjunct to the corpus's
`Submission.BoseGases.integrableOn_bounded_mul_wPair_sub_abox`, which is exactly the a.e.-bounded-factor
version of the statement.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `|a - b| ≤ |a| + |b|` (the triangle inequality in the form used below). -/
private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
  · linarith [le_abs_self a, neg_abs_le b]
  · linarith [le_abs_self b, neg_abs_le a]

/-- `IntegrableOn` of `(f ^ 2) * wLoc ℓ v 0` over the box, from an a.e.-measurable, a.e.-bounded
`f` and an integrable numerator `v` supported in `ball 0 R` under the dilute regime. -/
lemma integrableOn_sq_mul_wLoc {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {v : E3 → ℝ}
    (hv_int : MeasureTheory.Integrable v) (hsuppv : ∀ z : E3, R ≤ ‖z‖ → v z = 0)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {p : Fin n × Fin n} (hpne : p.1 ≠ p.2) {f : Submission.BoseGases.X n → ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)), |f x| ≤ B) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (f x) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  have key := Submission.BoseGases.integrableOn_bounded_mul_wPair_sub_abox (N := n) (ℓ := ℓ) (R := R) hℓ
    (g := fun x : Submission.BoseGases.X n => (f x) ^ 2) hv_int hsuppv hRℓ p.1 p.2 hpne (hm.pow 2)
    (B := B * B) (mul_nonneg hB hB) ?_
  · have hAB : (fun x : Submission.BoseGases.X n => (f x) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
        = fun x : Submission.BoseGases.X n => (f x) ^ 2 * Submission.BoseGases.wPair ℓ v (x p.1) (x p.2) := by
      funext x
      rw [wLoc_zero_eq_wPair']
    rw [hAB]
    exact key
  · filter_upwards [hb] with x hx
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs, pow_two]
    exact mul_self_le_mul_self (abs_nonneg (f x)) hx

/-- The continuous case of `integrableOn_sq_mul_wLoc`: the bound on the compact box is automatic. -/
lemma integrableOn_sq_mul_wLoc_of_continuous {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {v : E3 → ℝ}
    (hv_int : MeasureTheory.Integrable v) (hsuppv : ∀ z : E3, R ≤ ‖z‖ → v z = 0)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {p : Fin n × Fin n} (hpne : p.1 ≠ p.2) {f : Submission.BoseGases.X n → ℝ} (hf : Continuous f) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (f x) ^ 2 * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := f) hf.continuousOn
  have hB0 : 0 ≤ B := by
    have h0 := hB (0 : Submission.BoseGases.X n) (Submission.BoseGases.zero_mem_abox hℓ.le)
    have := norm_nonneg (f (0 : Submission.BoseGases.X n))
    linarith
  refine integrableOn_sq_mul_wLoc hℓ hv_int hsuppv hRℓ hpne hf.aestronglyMeasurable hB0 ?_
  rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
  exact ae_of_all _ (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx)

/-- **The five box conjuncts of `CS_side_hyps` under `Integrable v`** (the last five conjuncts
of the target, verbatim). -/
theorem CS_box_hyps_of_integrable {v : E3 → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv_int : MeasureTheory.Integrable v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : E3 → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
          * (Classical.choose h (x p.1 - x p.2)) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
            - Classical.choose h (x p.1 - x p.2)
              * Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) ∧
    (∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) := by
  classical
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  have hsuppv : ∀ z : E3, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
  obtain ⟨hw0, hw1⟩ :=
    Submission.BoseGases.scattering_bounds_ae hR hv hvrad hv_supp hrad hw
  have hwmeas : MeasureTheory.AEStronglyMeasurable (Classical.choose h) MeasureTheory.volume :=
    hw.lhs_integrable.aestronglyMeasurable
  -- abbreviations for the slot expressions
  set w₀ : E3 → ℝ := Classical.choose h with hw₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (3) the `4Q`-square
    intro p hp
    obtain ⟨-, hpne⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hqmeas, Bq, hBq0, hqbnd⟩ :=
      ae_bounded_q4B_abox hv hvrad R hR hv_supp hav h hℓ hΦc hp
    exact integrableOn_sq_mul_wLoc hℓ hv_int hsuppv hRℓ hpne hqmeas hBq0 hqbnd
  · -- (4) the double-`Q` mass
    intro p hp
    obtain ⟨-, hpne⟩ := Finset.mem_filter.mp hp
    exact integrableOn_sq_mul_wLoc_of_continuous hℓ hv_int hsuppv hRℓ hpne
      (Submission.BoseGases.aQ_continuous hℓ p.2
        (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc))
  · -- (5) the `(PQ+QP)`-mass with the `ω²` weight
    intro p hp
    obtain ⟨-, hpne⟩ := Finset.mem_filter.mp hp
    have hcont : Continuous (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
          + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) :=
      (Submission.BoseGases.aP_continuous hℓ p.2
        (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc)).add
        (Submission.BoseGases.aQ_continuous hℓ p.2
          (Submission.BoseGases.aP_continuous hℓ p.1 hΦc))
    have hwmeas' : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X n => w₀ (x p.1 - x p.2))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
      simpa [hw₀] using
        (Submission.BoseGases.w0_diff_aem hℓ hpne hw.lhs_integrable (N := n) :
          MeasureTheory.AEStronglyMeasurable
            (fun x : Submission.BoseGases.X n => Classical.choose h (x p.1 - x p.2))
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)))
    have hwbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
        |w₀ (x p.1 - x p.2)| ≤ 1 := by
      have h0 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
          0 ≤ w₀ (x p.1 - x p.2) := by
        simpa [hw₀] using Submission.BoseGases.ae_pair_pullback hℓ hpne hw0
      have h1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
          w₀ (x p.1 - x p.2) ≤ 1 := by
        simpa [hw₀] using Submission.BoseGases.ae_pair_pullback hℓ hpne hw1
      filter_upwards [h0, h1] with x hx0 hx1
      rw [abs_of_nonneg hx0]; exact hx1
    obtain ⟨Bc, hBc⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox n ℓ) (f := fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
          + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) hcont.continuousOn
    have hBc0 : 0 ≤ Bc := by
      have h0 := hBc (0 : Submission.BoseGases.X n) (Submission.BoseGases.zero_mem_abox hℓ.le)
      have := norm_nonneg (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)
        (0 : Submission.BoseGases.X n) + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) (0 : Submission.BoseGases.X n))
      linarith
    have hbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
        |(Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)
          * w₀ (x p.1 - x p.2)| ≤ Bc * 1 := by
      have hcb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
          |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| ≤ Bc := by
        rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
        exact ae_of_all _ (fun x hx => by simpa [Real.norm_eq_abs] using hBc x hx)
      filter_upwards [hcb, hwbnd] with x hx1 hx2
      rw [abs_mul]
      exact mul_le_mul hx1 hx2 (abs_nonneg _) hBc0
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X n => (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)
          * w₀ (x p.1 - x p.2))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      hcont.aestronglyMeasurable.mul hwmeas'
    have key := integrableOn_sq_mul_wLoc hℓ hv_int hsuppv hRℓ hpne hmeas
      (mul_nonneg hBc0 zero_le_one) hbnd
    have hAB : (fun x : Submission.BoseGases.X n =>
          (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
              + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x) ^ 2
            * (Classical.choose h (x p.1 - x p.2)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
        = fun x : Submission.BoseGases.X n =>
          ((Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
              + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)
            * w₀ (x p.1 - x p.2)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2) := by
      funext x; ring
    rw [hAB]
    exact key
  · -- (6) the `q4B − ω·P₁P₂Φ` square
    intro p hp
    obtain ⟨-, hpne⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hqmeas, Bq, hBq0, hqbnd⟩ :=
      ae_bounded_q4B_abox hv hvrad R hR hv_supp hav h hℓ hΦc hp
    have hPc : Continuous (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) :=
      Submission.BoseGases.aP_continuous hℓ p.1
        (Submission.BoseGases.aP_continuous hℓ p.2 hΦc)
    have hwmeas' : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X n => w₀ (x p.1 - x p.2))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
      simpa [hw₀] using
        (Submission.BoseGases.w0_diff_aem hℓ hpne hw.lhs_integrable (N := n) :
          MeasureTheory.AEStronglyMeasurable
            (fun x : Submission.BoseGases.X n => Classical.choose h (x p.1 - x p.2))
            (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)))
    have hwbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
        |w₀ (x p.1 - x p.2)| ≤ 1 := by
      have h0 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
          0 ≤ w₀ (x p.1 - x p.2) := by
        simpa [hw₀] using Submission.BoseGases.ae_pair_pullback hℓ hpne hw0
      have h1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
          w₀ (x p.1 - x p.2) ≤ 1 := by
        simpa [hw₀] using Submission.BoseGases.ae_pair_pullback hℓ hpne hw1
      filter_upwards [h0, h1] with x hx0 hx1
      rw [abs_of_nonneg hx0]; exact hx1
    obtain ⟨Bp, hBp⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox n ℓ)
      (f := fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x)
      hPc.continuousOn
    have hBp0 : 0 ≤ Bp := by
      have h0 := hBp (0 : Submission.BoseGases.X n) (Submission.BoseGases.zero_mem_abox hℓ.le)
      have := norm_nonneg
        (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) (0 : Submission.BoseGases.X n))
      linarith
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X n =>
          Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
            - w₀ (x p.1 - x p.2)
              * Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      hqmeas.sub (hwmeas'.mul hPc.aestronglyMeasurable)
    have hbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
        |Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
            - w₀ (x p.1 - x p.2)
              * Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x| ≤ Bq + 1 * Bp := by
      have hpb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
          |Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x| ≤ Bp := by
        rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
        exact ae_of_all _ (fun x hx => by simpa [Real.norm_eq_abs] using hBp x hx)
      filter_upwards [hqbnd, hwbnd, hpb] with x hx1 hx2 hx3
      calc |Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
              - w₀ (x p.1 - x p.2)
                * Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x|
          ≤ |Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x|
            + |w₀ (x p.1 - x p.2)
                * Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x| :=
            abs_sub_le_abs_add_abs _ _
        _ = |Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x|
            + |w₀ (x p.1 - x p.2)|
              * |Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x| := by
            rw [abs_mul]
        _ ≤ Bq + 1 * Bp := by
            have h2 : |w₀ (x p.1 - x p.2)|
                * |Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x| ≤ 1 * Bp :=
              mul_le_mul hx2 hx3 (abs_nonneg _) zero_le_one
            linarith
    exact integrableOn_sq_mul_wLoc hℓ hv_int hsuppv hRℓ hpne hmeas
      (by linarith) hbnd
  · -- (7) the `(PQ+QP)`-mass
    intro p hp
    obtain ⟨-, hpne⟩ := Finset.mem_filter.mp hp
    exact integrableOn_sq_mul_wLoc_of_continuous hℓ hv_int hsuppv hRℓ hpne
      ((Submission.BoseGases.aP_continuous hℓ p.2
        (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc)).add
        (Submission.BoseGases.aQ_continuous hℓ p.2
          (Submission.BoseGases.aP_continuous hℓ p.1 hΦc)))

end

end Work.BoseFixB3.CS.Pieces
