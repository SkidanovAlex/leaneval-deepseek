/-
# `Npair6BWork/rowAux` — the shared engines for the `A·D_z f` row

Self-contained tools for `Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowDzFlatTight`:

* the product measure `PM = (volume|Iz).prod (volume|Iθ)` and its a.e. open-quadrant facts;
* the leaf weights expressed as canonical weights (`leafEta = canonW η`, `leafOne = canonW 0`,
  `leafGam = canonW γ`) and the resulting comparisons `ρ ≤ canonW γ`, `ρ ≤ canonW η` (for
  `a = 0`), `0 ≤ ρ`;
* a.e. strong measurability of `SmoothOpen` fields, their slots, `canonW` and the leaf weights;
* the two engines `val_le_HkSq` (weighted `L²`-value of a dominated slot) and
  `rowSummand_core` (sup on the middle factor + weighted `L²`-values of the two outer factors);
* the pointwise Leibniz majorant of `D_z^bD_θ^a (A · D_z f)`;
* `slotPairing` as a product-measure integral (Fubini);
* monotonicity of `HkIntegrand`/`HkMem` in the order;
* the flat coefficient bound `CoefTh 1 A ≤ K1` as a pointwise bound.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.GoodOpenBase
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.H2.RegQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdzBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option autoImplicit false

/-- The product measure `dz ⊗ dθ` on `Iz × Iθ`. -/
abbrev PM : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The open quadrant is conull for `PM`. -/
theorem ae_PM_Q0 : ∀ᵐ p ∂PM,
    0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 := by
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[(volume : MeasureTheory.Measure (ℝ × ℝ))] (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [PM, MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_of_forall_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet
    (fun p hp => hp)

/-- A property holding on the open quadrant holds a.e. for `PM`. -/
theorem ae_of_forall_Qd {P : ℝ × ℝ → Prop}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → P (z, θ)) : ∀ᵐ p ∂PM, P p := by
  filter_upwards [ae_PM_Q0] with p hp
  exact h p.1 p.2 hp.1 hp.2.1 hp.2.2

/-- A function `C^∞` on the open quadrant is a.e. strongly measurable for `PM`. -/
theorem aesm_of_smoothOpen {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) PM :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hF 1).continuousOn)

/-- A mixed derivative of an `SmoothOpen` field is a.e. strongly measurable for `PM`. -/
theorem aesm_mixed {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (j i : ℕ) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) PM :=
  aesm_of_smoothOpen (hF.mixed j i)

/-- The canonical slot weight is a.e. strongly measurable for `PM`. -/
theorem aesm_canonW (q : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2) PM :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.TransportS.SlotT2.continuousOn_canonW q)

/-- The leaf weights as canonical weights. -/
theorem leafEta_eq_canonW :
    Work.FTS.TransportS.leafEta
      = Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta := rfl

theorem leafGam_eq_canonW (α : ℝ) :
    Work.FTS.TransportS.leafGam α
      = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) := rfl

theorem leafOne_eq_canonW_zero :
    Work.FTS.TransportS.leafOne = Work.FTS.TransportS.SlotT2.canonW 0 := by
  funext z θ
  rw [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW, neg_zero,
    Real.rpow_zero, mul_one]

/-- A leaf weight is a.e. strongly measurable for `PM`. -/
theorem aesm_leafW {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : Work.FTS.TransportS.IsLeafW α a ρ) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2) PM := by
  rcases h with h1 | h2 | ⟨_, h3⟩
  · rw [h1]; exact aesm_canonW _
  · rw [h2, leafOne_eq_canonW_zero]; exact aesm_canonW 0
  · rw [h3]; exact aesm_canonW _

/-- `slotPairing` as an integral against the product measure (Fubini). -/
theorem slotPairing_eq_prod {ρv u v : ℝ → ℝ → ℝ} (a b : ℕ)
    (h : MeasureTheory.Integrable (Function.uncurry
      (fun z θ => ρv z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a v z θ)) PM) :
    Work.FTS.TransportS.slotPairing ρv a b u v
      = ∫ p, ρv p.1 p.2 * Work.Spaces.mixed b a u p.1 p.2
          * Work.Spaces.mixed b a v p.1 p.2 ∂PM := by
  rw [Work.FTS.TransportS.slotPairing]
  exact (MeasureTheory.integral_prod _ h).symm

/-! ## The leaf weights against the canonical weights -/

theorem leafW_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ := by
  intro z θ _ hθ hθ2
  have hσ : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rcases h with rfl | rfl | ⟨_, rfl⟩
  · exact Work.FTS.TransportS.leafEta_nonneg hσ
  · exact Work.FTS.TransportS.leafOne_nonneg z θ
  · exact Work.FTS.TransportS.leafGam_nonneg α hσ

/-- Every leaf weight is dominated by the `γ`-weight on the open quadrant. -/
theorem leafW_le_canonW_gam {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
  have hη : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  have h0 : (0 : ℝ) ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  intro z θ _ hθ hθ2
  rcases h with h1 | h2 | ⟨_, h3⟩
  · rw [h1, leafEta_eq_canonW]
    exact Work.FTS.TransportS.T2Sup.canonW_le_of_le hη hθ hθ2
  · rw [h2, leafOne_eq_canonW_zero]
    exact Work.FTS.TransportS.T2Sup.canonW_le_of_le h0 hθ hθ2
  · rw [h3, leafGam_eq_canonW]

/-- For a pure slot (`a = 0`) every leaf weight is dominated by the `η`-weight. -/
theorem leafW_le_canonW_eta {α : ℝ} {ρ : ℝ → ℝ → ℝ}
    (h : Work.FTS.TransportS.IsLeafW α 0 ρ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ := by
  intro z θ _ hθ hθ2
  rcases h with h1 | h2 | ⟨h3, _⟩
  · rw [h1, leafEta_eq_canonW]
  · rw [h2, leafOne_eq_canonW_zero]
    exact Work.FTS.TransportS.T2Sup.canonW_le_of_le Work.Spaces.eta_nonneg hθ hθ2
  · exact absurd h3 (by omega)

/-! ## The engines -/

/-- **The `L²`-value engine.**  A pointwise domination of a nonnegative density by
`HkIntegrand α k f` gives integrability and the value bound. -/
theorem val_le_HkSq {α : ℝ} {k : ℕ} {f ρv X : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    (hρnn : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρv z θ)
    (hdom : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρv z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ρv p.1 p.2 * (X p.1 p.2) ^ 2) PM) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => ρv p.1 p.2 * (X p.1 p.2) ^ 2) PM ∧
      ∫ p, ρv p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM ≤ Work.Spaces.HkSq α k f := by
  obtain ⟨hintH, hvalH⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.rowA_HkIntegrand_prodIntegrable
      (α := α) (k := k) (F := f) hsm hmem
  have hpt : ∀ᵐ p ∂PM, ρv p.1 p.2 * (X p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f p.1 p.2 := by
    filter_upwards [ae_PM_Q0] with p hp
    exact hdom p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hnn : ∀ᵐ p ∂PM, 0 ≤ ρv p.1 p.2 * (X p.1 p.2) ^ 2 := by
    filter_upwards [ae_PM_Q0] with p hp
    exact mul_nonneg (hρnn p.1 p.2 hp.1 hp.2.1 hp.2.2) (sq_nonneg _)
  have hptn : ∀ᵐ p ∂PM, ‖ρv p.1 p.2 * (X p.1 p.2) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α k f p.1 p.2 := by
    filter_upwards [hpt, hnn] with p hp hnnp
    rw [Real.norm_of_nonneg hnnp]; exact hp
  have hint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρv p.1 p.2 * (X p.1 p.2) ^ 2) PM :=
    hintH.mono' hmeas hptn
  exact ⟨hint, le_trans (integral_mono_ae hint hintH hpt) (le_of_eq hvalH)⟩

/-- **Two-weight Cauchy–Schwarz in `L²(PM)`.** -/
theorem cs_sqrt {ρ₁ ρ₂ X Z : ℝ → ℝ → ℝ}
    (hρ₁nn : ∀ᵐ p ∂PM, 0 ≤ ρ₁ p.1 p.2) (hρ₂nn : ∀ᵐ p ∂PM, 0 ≤ ρ₂ p.1 p.2)
    (hI1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2) PM)
    (hI2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2) PM)
    (hm1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)) PM)
    (hm2 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) PM) :
    (∫ p, Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
        * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2) ∂PM)
      ≤ Real.sqrt (∫ p, ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM)
        * Real.sqrt (∫ p, ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 ∂PM) := by
  have hf2 : (fun p : ℝ × ℝ => (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)) ^ (2 : ℝ))
      =ᵐ[PM] fun p => ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 := by
    filter_upwards [hρ₁nn] with p hp
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg hp (sq_nonneg _))]
  have hg2 : (fun p : ℝ × ℝ => (Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) ^ (2 : ℝ))
      =ᵐ[PM] fun p => ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 := by
    filter_upwards [hρ₂nn] with p hp
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg hp (sq_nonneg _))]
  have hf2n : (fun p : ℝ × ℝ => (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)) ^ 2)
      =ᵐ[PM] fun p => ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 := by
    filter_upwards [hρ₁nn] with p hp
    exact Real.sq_sqrt (mul_nonneg hp (sq_nonneg _))
  have hg2n : (fun p : ℝ × ℝ => (Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) ^ 2)
      =ᵐ[PM] fun p => ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 := by
    filter_upwards [hρ₂nn] with p hp
    exact Real.sq_sqrt (mul_nonneg hp (sq_nonneg _))
  have hfmem : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)) (ENNReal.ofReal 2) PM := by
    rw [ENNReal.ofReal_ofNat]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hm1).mpr (hI1.congr hf2n.symm)
  have hgmem : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) (ENNReal.ofReal 2) PM := by
    rw [ENNReal.ofReal_ofNat]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hm2).mpr (hI2.congr hg2n.symm)
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := PM) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun p => Real.sqrt_nonneg _)
    (Eventually.of_forall fun p => Real.sqrt_nonneg _) hfmem hgmem
  have hL : (∫ p, (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)) ^ (2 : ℝ) ∂PM)
      = ∫ p, ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM :=
    MeasureTheory.integral_congr_ae hf2
  have hR : (∫ p, (Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) ^ (2 : ℝ) ∂PM)
      = ∫ p, ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 ∂PM :=
    MeasureTheory.integral_congr_ae hg2
  calc (∫ p, Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
        * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2) ∂PM)
      ≤ (∫ p, (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)) ^ (2 : ℝ) ∂PM) ^ (1 / (2 : ℝ))
        * (∫ p, (Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) ^ (2 : ℝ) ∂PM) ^ (1 / (2 : ℝ)) :=
        hholder
    _ = Real.sqrt (∫ p, ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM)
        * Real.sqrt (∫ p, ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 ∂PM) := by
        rw [hL, hR, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-- **The sup-and-pair engine.** -/
theorem rowSummand_core {α KY AX AZ : ℝ} {f X Y Z ρv ρ₁ ρ₂ : ℝ → ℝ → ℝ}
    (hKY0 : 0 ≤ KY) (hAX0 : 0 ≤ AX) (hAZ0 : 0 ≤ AZ)
    (hρnn : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρv z θ)
    (hI1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2) PM)
    (hI2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2) PM)
    (hv1 : ∫ p, ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM ≤ AX)
    (hv2 : ∫ p, ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 ∂PM ≤ AZ)
    (hρ₁nn : ∀ᵐ p ∂PM, 0 ≤ ρ₁ p.1 p.2) (hρ₂nn : ∀ᵐ p ∂PM, 0 ≤ ρ₂ p.1 p.2)
    (hm1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)) PM)
    (hm2 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) PM)
    (hρm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρv p.1 p.2) PM)
    (hXm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2) PM)
    (hYm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Y p.1 p.2) PM)
    (hZm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Z p.1 p.2) PM)
    (hpt : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |ρv z θ * X z θ * Y z θ * Z z θ| ≤ KY * (Real.sqrt (ρ₁ z θ * (X z θ) ^ 2)
        * Real.sqrt (ρ₂ z θ * (Z z θ) ^ 2))) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) PM ∧
      |∫ p, ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂PM|
        ≤ KY * (Real.sqrt AX * Real.sqrt AZ) := by
  have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ => KY *
      (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
        * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2))) PM := by
    have hprod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
          * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) PM := by
      have hle : ∀ᵐ p ∂PM, Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
            * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)
          ≤ (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 + ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2) / 2 := by
        filter_upwards [hρ₁nn, hρ₂nn] with p h1 h2
        have h := two_mul_le_add_sq (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2))
          (Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2))
        have e1 : (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)) ^ 2
            = ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 := Real.sq_sqrt (mul_nonneg h1 (sq_nonneg _))
        have e2 : (Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) ^ 2
            = ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 := Real.sq_sqrt (mul_nonneg h2 (sq_nonneg _))
        rw [e1, e2] at h
        linarith
      refine MeasureTheory.Integrable.mono' ((hI1.add hI2).const_mul (1 / 2))
        (hm1.mul hm2) ?_
      filter_upwards [hle] with p hp
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      simp only [Pi.add_apply]
      linarith [hp]
    exact hprod.const_mul KY
  have hFm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) PM :=
    ((hρm.mul hXm).mul hYm).mul hZm
  have hptae : ∀ᵐ p ∂PM, ‖ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2‖
      ≤ KY * (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
        * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) := by
    filter_upwards [ae_PM_Q0] with p hp
    rw [Real.norm_eq_abs]
    exact hpt p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) PM :=
    hmaj.mono' hFm hptae
  refine ⟨hInt, ?_⟩
  have hstep1 : |∫ p, ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂PM|
      ≤ ∫ p, |ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ∂PM := by
    simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
      (fun p : ℝ × ℝ => ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2)
  have hstep2 : (∫ p, |ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ∂PM)
      ≤ ∫ p, KY * (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
          * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) ∂PM := by
    refine integral_mono_ae hInt.abs hmaj ?_
    filter_upwards [ae_PM_Q0] with p hp
    exact hpt p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hstep3 : (∫ p, KY * (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
        * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) ∂PM)
      = KY * ∫ p, Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
        * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2) ∂PM :=
    MeasureTheory.integral_const_mul KY _
  have hstep4 : (∫ p, Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
        * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2) ∂PM)
      ≤ Real.sqrt (∫ p, ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM)
        * Real.sqrt (∫ p, ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 ∂PM) :=
    cs_sqrt hρ₁nn hρ₂nn hI1 hI2 hm1 hm2
  have hstep5 : Real.sqrt (∫ p, ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM)
        * Real.sqrt (∫ p, ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 ∂PM)
      ≤ Real.sqrt AX * Real.sqrt AZ :=
    mul_le_mul (Real.sqrt_le_sqrt hv1) (Real.sqrt_le_sqrt hv2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc |∫ p, ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂PM|
      ≤ ∫ p, |ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ∂PM := hstep1
    _ ≤ ∫ p, KY * (Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
          * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2)) ∂PM := hstep2
    _ = KY * ∫ p, Real.sqrt (ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2)
          * Real.sqrt (ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2) ∂PM := hstep3
    _ ≤ KY * (Real.sqrt (∫ p, ρ₁ p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM)
          * Real.sqrt (∫ p, ρ₂ p.1 p.2 * (Z p.1 p.2) ^ 2 ∂PM)) :=
        mul_le_mul_of_nonneg_left hstep4 hKY0
    _ ≤ KY * (Real.sqrt AX * Real.sqrt AZ) := mul_le_mul_of_nonneg_left hstep5 hKY0

/-! ## The pointwise Leibniz majorant -/

/-- Pointwise triangle inequality on the Leibniz expansion of `D_z^bD_θ^a (A · D_z f)`. -/
theorem abs_mixed_Dz_le_sum {A f ρv : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.SmoothOpen A) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (a b : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hρ : 0 ≤ ρv z θ) :
    ρv z θ * |Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρv z θ * |Work.Spaces.mixed b₁ a₁ A z θ
                * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) f z θ|
                * |Work.Spaces.mixed b a f z θ|) := by
  have hX := Work.FTS.TransportS.mixed_mul_Dz_open b a A f hA hf z θ hz hθ0 hθ1
  have habs : |Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ|
      ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (|Work.Spaces.mixed b₁ a₁ A z θ|
                * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) f z θ|) := by
    rw [hX]
    calc |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ A z θ
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) f z θ)|
        ≤ ∑ a₁ ∈ Finset.range (a + 1),
            |∑ b₁ ∈ Finset.range (b + 1),
              ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * (Work.Spaces.mixed b₁ a₁ A z θ
                    * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) f z θ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ A z θ
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) f z θ)| :=
          Finset.sum_le_sum fun a₁ _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (|Work.Spaces.mixed b₁ a₁ A z θ|
                  * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) f z θ|) := by
          refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
          rw [abs_mul, abs_mul, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose a₁ : ℝ)),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose b₁ : ℝ))]
          try ring
  calc ρv z θ * |Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        * Work.Spaces.mixed b a f z θ|
      = ρv z θ * |Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ|
        * |Work.Spaces.mixed b a f z θ| := by rw [abs_mul]; ring
    _ ≤ ρv z θ * (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (|Work.Spaces.mixed b₁ a₁ A z θ|
                * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) f z θ|))
        * |Work.Spaces.mixed b a f z θ| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hρ) (abs_nonneg _)
    _ = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρv z θ * |Work.Spaces.mixed b₁ a₁ A z θ
                * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) f z θ|
                * |Work.Spaces.mixed b a f z θ|) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        rw [abs_mul]
        ring

/-! ## Monotonicity of `HkIntegrand` and `HkMem` in the order -/

/-- `HkIntegrand` is monotone in the order. -/
theorem HkIntegrand_mono_le (α : ℝ) {l k : ℕ} (hlk : l ≤ k) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α l f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  unfold Work.Spaces.HkIntegrand
  have hsub : Finset.range (l + 1) ⊆ Finset.range (k + 1) :=
    Finset.range_subset_range.mpr (Nat.succ_le_succ hlk)
  refine add_le_add ?_ ?_
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
  · have inner : ∀ i ∈ Finset.range (l + 1),
        (∑ j ∈ Finset.range (l + 1), (if 1 ≤ i ∧ i + j ≤ l then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ j ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      intro i _
      refine le_trans (Finset.sum_le_sum (fun j _ => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun j _ _ => by split_ifs <;> simp only [sq_nonneg, le_refl]))
      by_cases hc : 1 ≤ i ∧ i + j ≤ l
      · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
      · rw [if_neg hc]; split_ifs <;> simp only [sq_nonneg, le_refl]
    exact le_trans (Finset.sum_le_sum inner) (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => Finset.sum_nonneg (fun j _ => by split_ifs <;>
        simp only [sq_nonneg, le_refl])))

/-- `HkMem` is monotone in the order (open-quadrant class). -/
theorem HkMem_mono_le {α : ℝ} {l k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hlk : l ≤ k) (h : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α l f :=
  Work.FTS.LocData.HkMem_of_majorant α l (hf.continuousOn_HkIntegrand α l) h.1 h.2
    (fun z _ θ _ => HkIntegrand_mono_le α hlk f z θ)

/-! ## The pointwise flat coefficient bound -/

theorem supAbsO_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.H2.supAbsO g := by
  rw [Work.FTS.H2.supAbsO]
  by_cases h : BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2
    ∧ y = |g z θ|}
  · refine le_trans (abs_nonneg (g 1 (Real.pi / 4))) (le_csSup h ?_)
    exact ⟨1, one_pos, Real.pi / 4, by linarith [Real.pi_pos], by linarith [Real.pi_pos], rfl⟩
  · rw [csSup_of_not_bddAbove h, Real.sSup_def]
    simp

/-- Every term of `CoefTh 1 A` is dominated by the whole sum. -/
theorem supAbsO_pth_le_CoefTh {A : ℝ → ℝ → ℝ} {b i : ℕ} (hbi : b + i ≤ 1) :
    Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth A))
      ≤ Work.FTS.VocabO.CoefTh 1 A := by
  rw [Work.FTS.VocabO.CoefTh]
  have hb' : b ∈ Finset.range 2 := Finset.mem_range.mpr (by omega)
  have hi' : i ∈ Finset.range 2 := Finset.mem_range.mpr (by omega)
  have hinner : (Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth A)))
      ≤ ∑ i' ∈ Finset.range 2,
          (if b + i' ≤ 1 then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth A))
            else 0) := by
    have h1 : Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth A))
        ≤ (if b + i ≤ 1 then
            Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth A)) else 0) :=
      le_of_eq (if_pos hbi).symm
    refine le_trans h1 (Finset.single_le_sum (f := fun i' =>
      if b + i' ≤ 1 then Work.FTS.H2.supAbsO (Work.Spaces.mixed b i' (Work.Spaces.pth A))
        else 0) (fun i' _ => ?_) hi')
    by_cases hc : b + i' ≤ 1
    · rw [if_pos hc]; exact supAbsO_nonneg _
    · rw [if_neg hc]
  refine le_trans hinner ?_
  refine Finset.single_le_sum (f := fun b' => ∑ i' ∈ Finset.range 2,
    if b' + i' ≤ 1 then Work.FTS.H2.supAbsO (Work.Spaces.mixed b' i' (Work.Spaces.pth A))
      else 0) (fun b' _ => Finset.sum_nonneg (fun i' _ => ?_)) hb'
  by_cases hc : b' + i' ≤ 1
  · rw [if_pos hc]; exact supAbsO_nonneg _
  · rw [if_neg hc]

/-- **The flat bound `CoefTh 1 A ≤ K1` is a pointwise bound** on the first mixed derivatives
of `∂_θA`. -/
theorem coefTh_pointwise {A : ℝ → ℝ → ℝ} {K1 : ℝ}
    (hmem : Work.FTS.VocabO.CoefThMem 1 A) (hle : Work.FTS.VocabO.CoefTh 1 A ≤ K1) :
    ∀ b i : ℕ, b + i ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b i (Work.Spaces.pth A) z θ| ≤ K1 := by
  intro b i hbi z θ hz hθ hθ2
  obtain ⟨K, hK⟩ := hmem b i hbi
  exact le_trans (Work.FTS.H2.le_supAbsO hz hθ hθ2 hK)
    (le_trans (supAbsO_pth_le_CoefTh hbi) hle)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
