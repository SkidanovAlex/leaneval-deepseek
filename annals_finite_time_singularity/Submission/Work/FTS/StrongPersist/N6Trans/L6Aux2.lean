/-
Copyright: work module for the Elgindi finite-time singularity project.

# Level-six auxiliary: general slot domination and the weighted slot Cauchy–Schwarz

* `canonW_slot_le_HkGen` — the slot domination at an arbitrary order `k` (dispatcher over the
  proved `Work.FTS.TransportS.T2Sup.canonW_mul_z_le_gen` / `canonW_mul_mixed_le_gen`);
* `sqrt_slot_mul` — the square-root algebra `√(canonW q₁ X²)·√(canonW q₂ Y²)
  = canonW ((q₁+q₂)/2) |X| |Y|`;
* `cs2_mixed_le` — the two-dimensional weighted Cauchy–Schwarz for two `mixed`-slots of the
  same smooth honest datum `g`,

  `∫_z∫_θ canonW ((q₁+q₂)/2) |D_z^{j₁}D_θ^{i₁}g| |D_z^{j₂}D_θ^{i₂}g| ≤ HkSq α 6 g`,

  obtained by applying `Work.FTS.TransportS.SlotT2.cs_sqrt_le` once in `θ` (at every `z`),
  and then monotonicity against `z ↦ ∫_θ HkIntegrand α 6 g z θ`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.SlotT2.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_mono cs_sqrt_le)

/-- A single canonical slot is dominated by `HkIntegrand α k g`, at an arbitrary order `k`. -/
theorem canonW_slot_le_HkGen {α : ℝ} {g : ℝ → ℝ → ℝ} {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {k j i : ℕ} (hi : i = 0 → q ≤ Work.Spaces.eta)
    (hij : i + j ≤ k) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  rcases eq_or_ne i 0 with hi0 | hine
  · subst hi0
    simpa only [Work.Spaces.mixed_zero_right] using
      Work.FTS.TransportS.T2Sup.canonW_mul_z_le_gen α g hq0 k (hi rfl) hθ j (by omega)
  · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_gen α g hq0 k hqγ hθ j i
      (Nat.one_le_iff_ne_zero.mpr hine) hij

/-! ## The square-root algebra of the slot weights -/

/-- `√(canonW q₁ z θ · X²) · √(canonW q₂ z θ · Y²)
= canonW ((q₁+q₂)/2) z θ · |X| · |Y|` on `Iθ`, for `q₁, q₂ > 0`. -/
theorem sqrt_slot_mul {z θ q₁ q₂ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h1 : 0 < q₁) (h2 : 0 < q₂)
    (X Y : ℝ) :
    Real.sqrt (canonW q₁ z θ * X ^ 2) * Real.sqrt (canonW q₂ z θ * Y ^ 2)
      = canonW ((q₁ + q₂) / 2) z θ * |X| * |Y| := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
  have hw : 0 ≤ Work.Spaces.w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs1 : Real.sqrt (canonW q₁ z θ * X ^ 2)
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(q₁ / 2)) * |X| := by
    rw [show canonW q₁ z θ * X ^ 2
        = (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(q₁ / 2)) * X) ^ 2 from by
      rw [canonW, ← Work.FTS.TransportS.sq_rpow_neg_half hs0 q₁]
      ring]
    rw [Real.sqrt_sq_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw,
      abs_of_nonneg (Real.rpow_nonneg hs0 _)]
  have hs2 : Real.sqrt (canonW q₂ z θ * Y ^ 2)
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(q₂ / 2)) * |Y| := by
    rw [show canonW q₂ z θ * Y ^ 2
        = (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(q₂ / 2)) * Y) ^ 2 from by
      rw [canonW, ← Work.FTS.TransportS.sq_rpow_neg_half hs0 q₂]
      ring]
    rw [Real.sqrt_sq_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw,
      abs_of_nonneg (Real.rpow_nonneg hs0 _)]
  rw [hs1, hs2]
  have hfac : Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(q₁ / 2)) * |X|
        * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(q₂ / 2)) * |Y|)
      = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(q₁ / 2))
          * (Real.sin (2 * θ)) ^ (-(q₂ / 2))) * (|X| * |Y|) := by ring
  rw [hfac, canonW]
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs]
    have hq1 : -(q₁ / 2) ≠ 0 := by intro hh; linarith [h1]
    have hq2 : -(q₂ / 2) ≠ 0 := by intro hh; linarith [h2]
    have hq12 : -((q₁ + q₂) / 2) ≠ 0 := by intro hh; linarith [h1, h2]
    rw [Real.zero_rpow hq1, Real.zero_rpow hq2, Real.zero_rpow hq12]
    ring
  · have hrpow : (Real.sin (2 * θ)) ^ (-(q₁ / 2)) * (Real.sin (2 * θ)) ^ (-(q₂ / 2))
        = (Real.sin (2 * θ)) ^ (-((q₁ + q₂) / 2)) := by
      rw [← Real.rpow_add hs]
      congr 1
      ring
    rw [hrpow]
    ring

/-! ## Measurability of the slot slices -/

/-- The `θ`-slice at `z > 0` of a `canonW`-weighted slot is a.e. strongly measurable. -/
theorem aesm_canonW_mixed_slice {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (q : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable
      (fun θ => canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _
    ((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
      ((hsg.mixed j i).continuousOn.pow 2)) hz

/-- The joint `canonW`-weighted slot integrand is a.e. strongly measurable for the product of
the two restricted Lebesgue measures. -/
theorem aesm_canonW_mixed_prod {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (q : ℝ) (j i : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => canonW q p.1 p.2 * (Work.Spaces.mixed j i g p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    ((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
      ((hsg.mixed j i).continuousOn.pow 2))

/-! ## The two-dimensional weighted Cauchy–Schwarz -/

/-- **The weighted slot Cauchy–Schwarz at level six.**  For two `mixed`-slots of the same
smooth honest datum `g`, priced with the exponents `q₁` resp. `q₂`,

  `∫_z∫_θ canonW ((q₁+q₂)/2) · |D_z^{j₁}D_θ^{i₁}g| · |D_z^{j₂}D_θ^{i₂}g| ≤ HkSq α 6 g`. -/
theorem cs2_mixed_le {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 6 g)
    {q₁ q₂ : ℝ} (hq₁0 : 0 < q₁) (hq₂0 : 0 < q₂)
    (hγ₁ : q₁ ≤ Work.Spaces.gam α) (hγ₂ : q₂ ≤ Work.Spaces.gam α)
    {j₁ i₁ j₂ i₂ : ℕ} (h1 : i₁ + j₁ ≤ 6) (h2 : i₂ + j₂ ≤ 6)
    (hi₁ : i₁ = 0 → q₁ ≤ Work.Spaces.eta) (hi₂ : i₂ = 0 → q₂ ≤ Work.Spaces.eta) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW ((q₁ + q₂) / 2) z θ
          * |Work.Spaces.mixed j₁ i₁ g z θ| * |Work.Spaces.mixed j₂ i₂ g z θ|)
      ≤ Work.Spaces.HkSq α 6 g := by
  classical
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set Y₁ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed j₁ i₁ g z θ with hY₁
  set Y₂ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed j₂ i₂ g z θ with hY₂
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ with hF
  have hFnn : ∀ z, 0 ≤ F z := fun z =>
    MeasureTheory.setIntegral_nonneg hIθm (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
  have hFint : IntegrableOn F Work.Spaces.Iz := hmem.2
  have hdom₁ : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      canonW q₁ z θ * (Y₁ z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := fun z θ hθ =>
    canonW_slot_le_HkGen (α := α) (g := g) (k := 6) hq₁0 hγ₁ hi₁ h1 hθ
  have hdom₂ : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      canonW q₂ z θ * (Y₂ z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := fun z θ hθ =>
    canonW_slot_le_HkGen (α := α) (g := g) (k := 6) hq₂0 hγ₂ hi₂ h2 hθ
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, canonW ((q₁ + q₂) / 2) z θ * |Y₁ z θ| * |Y₂ z θ|) ≤ F z := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have hzero : (fun θ => canonW ((q₁ + q₂) / 2) 0 θ * |Y₁ 0 θ| * |Y₂ 0 θ|)
          = fun _ => (0 : ℝ) := by
        funext θ
        have hc : canonW ((q₁ + q₂) / 2) 0 θ = 0 := by simp [canonW, Work.Spaces.w]
        rw [hc]; ring
      rw [hzero, MeasureTheory.integral_zero]
      exact hFnn 0
    · set A : ℝ → ℝ := fun θ =>
        if θ ∈ Work.Spaces.Iθ then canonW q₁ z θ * (Y₁ z θ) ^ 2 else 0 with hA
      set B : ℝ → ℝ := fun θ =>
        if θ ∈ Work.Spaces.Iθ then canonW q₂ z θ * (Y₂ z θ) ^ 2 else 0 with hB
      have hAnn : ∀ x, 0 ≤ A x := by
        intro x
        by_cases hx : x ∈ Work.Spaces.Iθ
        · rw [show A x = canonW q₁ z x * (Y₁ z x) ^ 2 from by simp [hA, hx]]
          exact mul_nonneg (canonW_nonneg hx) (sq_nonneg _)
        · rw [show A x = 0 from by simp [hA, hx]]
      have hBnn : ∀ x, 0 ≤ B x := by
        intro x
        by_cases hx : x ∈ Work.Spaces.Iθ
        · rw [show B x = canonW q₂ z x * (Y₂ z x) ^ 2 from by simp [hB, hx]]
          exact mul_nonneg (canonW_nonneg hx) (sq_nonneg _)
        · rw [show B x = 0 from by simp [hB, hx]]
      have hAae : A =ᵐ[volume.restrict Work.Spaces.Iθ]
          fun θ => canonW q₁ z θ * (Y₁ z θ) ^ 2 :=
        MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => by simp [hA, hθ])
      have hBae : B =ᵐ[volume.restrict Work.Spaces.Iθ]
          fun θ => canonW q₂ z θ * (Y₂ z θ) ^ 2 :=
        MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => by simp [hB, hθ])
      have hraw₁ : IntegrableOn (fun θ => canonW q₁ z θ * (Y₁ z θ) ^ 2) Work.Spaces.Iθ :=
        Integrable.mono' (hmem.1 z hz) (aesm_canonW_mixed_slice (α := α) hsg q₁ j₁ i₁ hz0)
          (MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => by
            rw [Real.norm_of_nonneg (mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))]
            exact hdom₁ z θ hθ))
      have hraw₂ : IntegrableOn (fun θ => canonW q₂ z θ * (Y₂ z θ) ^ 2) Work.Spaces.Iθ :=
        Integrable.mono' (hmem.1 z hz) (aesm_canonW_mixed_slice (α := α) hsg q₂ j₂ i₂ hz0)
          (MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => by
            rw [Real.norm_of_nonneg (mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))]
            exact hdom₂ z θ hθ))
      have hAint : IntegrableOn A Work.Spaces.Iθ := hraw₁.congr hAae.symm
      have hBint : IntegrableOn B Work.Spaces.Iθ := hraw₂.congr hBae.symm
      have hCS := cs_sqrt_le hAint hBint hAnn hBnn
      have hcongr : (∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) * Real.sqrt (B θ))
          = ∫ θ in Work.Spaces.Iθ,
              canonW ((q₁ + q₂) / 2) z θ * |Y₁ z θ| * |Y₂ z θ| := by
        refine MeasureTheory.setIntegral_congr_fun hIθm fun θ hθ => ?_
        have hAθ : A θ = canonW q₁ z θ * (Y₁ z θ) ^ 2 := by simp [hA, hθ]
        have hBθ : B θ = canonW q₂ z θ * (Y₂ z θ) ^ 2 := by simp [hB, hθ]
        rw [hAθ, hBθ]
        exact sqrt_slot_mul hθ hq₁0 hq₂0 (Y₁ z θ) (Y₂ z θ)
      have hAle : (∫ θ in Work.Spaces.Iθ, A θ) ≤ F z := by
        rw [show (∫ θ in Work.Spaces.Iθ, A θ)
            = ∫ θ in Work.Spaces.Iθ, canonW q₁ z θ * (Y₁ z θ) ^ 2 from
          MeasureTheory.setIntegral_congr_fun hIθm (fun θ hθ => by simp [hA, hθ])]
        exact MeasureTheory.integral_mono_ae hraw₁ (hmem.1 z hz)
          (MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => hdom₁ z θ hθ))
      have hBle : (∫ θ in Work.Spaces.Iθ, B θ) ≤ F z := by
        rw [show (∫ θ in Work.Spaces.Iθ, B θ)
            = ∫ θ in Work.Spaces.Iθ, canonW q₂ z θ * (Y₂ z θ) ^ 2 from
          MeasureTheory.setIntegral_congr_fun hIθm (fun θ hθ => by simp [hB, hθ])]
        exact MeasureTheory.integral_mono_ae hraw₂ (hmem.1 z hz)
          (MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => hdom₂ z θ hθ))
      have hAn : 0 ≤ ∫ θ in Work.Spaces.Iθ, A θ :=
        MeasureTheory.setIntegral_nonneg hIθm (fun θ _ => hAnn θ)
      have hBn : 0 ≤ ∫ θ in Work.Spaces.Iθ, B θ :=
        MeasureTheory.setIntegral_nonneg hIθm (fun θ _ => hBnn θ)
      calc (∫ θ in Work.Spaces.Iθ, canonW ((q₁ + q₂) / 2) z θ * |Y₁ z θ| * |Y₂ z θ|)
          = ∫ θ in Work.Spaces.Iθ, Real.sqrt (A θ) * Real.sqrt (B θ) := hcongr.symm
        _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A θ)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, B θ) := hCS
        _ ≤ Real.sqrt (F z) * Real.sqrt (F z) :=
            mul_le_mul (Real.sqrt_le_sqrt hAle) (Real.sqrt_le_sqrt hBle)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = F z := Real.mul_self_sqrt (hFnn z)
  have h0 : ∀ z ∈ Work.Spaces.Iz,
      0 ≤ (∫ θ in Work.Spaces.Iθ,
        canonW ((q₁ + q₂) / 2) z θ * |Y₁ z θ| * |Y₂ z θ|) := fun z _ =>
    MeasureTheory.setIntegral_nonneg hIθm (fun θ hθ =>
      mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _)) (abs_nonneg _))
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem hIzm h0) hFint
    (MeasureTheory.ae_restrict_of_forall_mem hIzm hpt)) ?_
  rw [hF]
  exact le_of_eq rfl

end Work.FTS.StrongPersist.N6Trans
