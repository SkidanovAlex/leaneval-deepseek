import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `CoefTh` is nonnegative: every summand is a supremum of absolute values. -/
private theorem coefTh_nonneg_aux (l : ℕ) (A : ℝ → ℝ → ℝ) :
    0 ≤ Work.FTS.VocabO.CoefTh l A := by
  rw [Work.FTS.VocabO.CoefTh]
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs with h
  · exact supAbsO_nonneg _
  · exact le_rfl

/-- **Leibniz summand, coefficient slot `a₁ ≥ 1` of total order `a₁ + b₁ ≥ 3`.**

`X := mixed b₁ a₁ A`, `Y := mixed (b+1-b₁) (a-a₁) f`, `Z := mixed b a f`; here `X` and `Z` are mixed slots
(`1 ≤ a₁`, `1 ≤ a`), so both are `γ`-priced.

* The middle factor has order `a+b+1-(a₁+b₁) ≤ 4`, so `|Y| ≤ C₃α^{-1/2}HkNorm α 6 f`
  (`T1SixAux.supSix`, from `SmoothOpen f`, `HkMem α 6 f`) when `a₁ + b₁ ≤ 4`;
* and when `a₁+b₁ ≥ 5` its order is `≤ 2`, so instead `|Y| ≤ C α^{-1/2}M`: `√15·Xn α f ≤ √15 M`
  (`T2SupB2.mixed_pointwise_le_Xn` if `a₁ < a`, mixed) resp. `C/√(γ-1)·Xn α f` (`TransportS.sup_dz_le_hk`
  if `a₁ = a`, pure, with `HkMem α 4 f` from `HkMem_mono_le`).
* Cauchy–Schwarz with the single weight `ρ` gives `∫ρ|X||Z| ≤ √(∫ρX²)·√(∫ρZ²)`, where
  `∫ρX² ≤ HkSq α 4 A ≤ K4²` for `a₁+b₁ ≤ 4` and `≤ HkSq α 6 A ≤ K6²` for `a₁+b₁ ≤ 6`
  (`val_le_HkSq` + `canonW_mul_mixed_le_of_le`), and `∫ρZ² ≤ HkSq α 6 f`.
* Hence `|∫ρXYZ| ≤ C α^{-1/2}K4·HkSq α 6 f` (`p ≤ 4`) resp. `C α^{-1/2}M·K6·HkNorm α 6 f` (`p ≥ 5`); both
  are `≤ C'α^{-4}·T` for `T := (1+K0+K4+K1)(1+M)(1+HkSq α 6 f) + (K4+K6)(1+M)(1+HkNorm α 6 f)`
  (`K4·HkSq ≤ T`, `M·K6·HkNorm ≤ T`, `α^{-1/2} ≤ α^{-4}`). -/
theorem rowSumA1Big : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ → 1 ≤ a₁ → a₁ ≤ a → b₁ ≤ b →
      3 ≤ a₁ + b₁ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(4 : ℝ))
            * ((1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨Cdz, hCdz, hdz⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Csup, hCsup, hsup⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.supSix
  obtain ⟨Cmp, hCmp, hmp⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  have hsq10 : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  have hmax0 : 0 ≤ max Cmp (Cdz * Real.sqrt 10) := le_trans hCmp.le (le_max_left _ _)
  have hCpos : 0 < Csup + max Cmp (Cdz * Real.sqrt 10) + 1 := by linarith
  refine ⟨Csup + max Cmp (Cdz * Real.sqrt 10) + 1, hCpos, ?_⟩
  intro α hαIoc A f K0 K4 K6 K1 M a b a₁ b₁ ρ hcoef hctmem hctle hdat hab hleaf ha1 ha1a hb1b hp3
  obtain ⟨hα0, hα1⟩ := hαIoc
  have ha : 1 ≤ a := le_trans ha1 ha1a
  -- the inverse powers of `α`
  have hαinv0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hαinv1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  have hα4pos : (0 : ℝ) < α ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hα0 _
  have hαinvle : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  -- nonnegativity of every price
  have hK0 : 0 ≤ K0 := le_trans (abs_nonneg (A 1 (Real.pi / 4)))
    (hcoef.val 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hK1 : 0 ≤ K1 := le_trans (coefTh_nonneg_aux 1 A) hctle
  have hM : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hQ6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hN6 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hNQ : Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f = Work.Spaces.HkSq α 6 f := by
    rw [← pow_two]; exact Real.sq_sqrt hQ6
  have hmem4 : Work.Spaces.HkMem α 4 f := HkMem_mono_le hdat.sm (by norm_num) hdat.h6
  -- the target bracket
  set T : ℝ := (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) with hT
  have hA1 : 0 ≤ (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hA2 : 0 ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hTnn : 0 ≤ T := by rw [hT]; exact add_nonneg hA1 hA2
  have hT1 : K4 * Work.Spaces.HkSq α 6 f ≤ T := by
    rw [hT]
    have h1 : K4 * Work.Spaces.HkSq α 6 f
        ≤ (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
      have hK4le : K4 ≤ (1 + K0 + K4 + K1) := by linarith
      have hQle : Work.Spaces.HkSq α 6 f
          ≤ (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
        by nlinarith [hQ6, hM, mul_nonneg hM hQ6]
      calc K4 * Work.Spaces.HkSq α 6 f
          ≤ (1 + K0 + K4 + K1) * Work.Spaces.HkSq α 6 f :=
            mul_le_mul_of_nonneg_right hK4le hQ6
        _ ≤ (1 + K0 + K4 + K1) * ((1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_left hQle (by linarith)
        _ = (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by ring
    exact le_trans h1 (le_add_of_nonneg_right hA2)
  have hT2 : M * K6 * Work.Spaces.HkNorm α 6 f ≤ T := by
    rw [hT]
    have h1 : M * K6 * Work.Spaces.HkNorm α 6 f
        ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
      have hMN : M * Work.Spaces.HkNorm α 6 f
          ≤ (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
        by nlinarith [hM, hN6, mul_nonneg hM hN6]
      have hK6le : K6 ≤ K4 + K6 := by linarith
      have hnn : 0 ≤ (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
        mul_nonneg (by linarith) (by linarith)
      calc M * K6 * Work.Spaces.HkNorm α 6 f
          = K6 * (M * Work.Spaces.HkNorm α 6 f) := by ring
        _ ≤ K6 * ((1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
            mul_le_mul_of_nonneg_left hMN hK6
        _ ≤ (K4 + K6) * ((1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
            mul_le_mul_of_nonneg_right hK6le hnn
        _ = (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by ring
    exact le_trans h1 (le_add_of_nonneg_left hA1)
  -- the common final step
  have hstep : ∀ (Kc B : ℝ), 0 ≤ Kc → 0 ≤ B → B ≤ T →
      Kc ≤ Csup + max Cmp (Cdz * Real.sqrt 10) + 1 →
      Kc * α ^ (-(1 / 2 : ℝ)) * B
        ≤ (Csup + max Cmp (Cdz * Real.sqrt 10) + 1) * α ^ (-(4 : ℝ)) * T := by
    intro Kc B hKc hB hBT hKcC
    have hα4 : (0 : ℝ) ≤ α ^ (-(4 : ℝ)) := hα4pos.le
    calc Kc * α ^ (-(1 / 2 : ℝ)) * B
        ≤ Kc * α ^ (-(4 : ℝ)) * B := by
          refine mul_le_mul_of_nonneg_right ?_ hB
          exact mul_le_mul_of_nonneg_left hαinvle hKc
      _ ≤ Kc * α ^ (-(4 : ℝ)) * T :=
          mul_le_mul_of_nonneg_left hBT (mul_nonneg hKc hα4)
      _ ≤ (Csup + max Cmp (Cdz * Real.sqrt 10) + 1) * α ^ (-(4 : ℝ)) * T :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKcC hα4) hTnn
  -- the three slots
  set XA : ℝ → ℝ → ℝ := Work.Spaces.mixed b₁ a₁ A with hXA
  set Yf : ℝ → ℝ → ℝ := Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f with hYf
  set Zf : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f with hZf
  let cW : ℝ → ℝ → ℝ := Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α)
  have hcW : cW = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) := rfl
  have hcWnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ cW z θ :=
    fun _ _ _ hθ hθ2 => Work.FTS.TransportS.SlotT2.canonW_nonneg ⟨hθ.le, hθ2.le⟩
  -- a.e. strong measurability of the four factors
  have haeX : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => XA p.1 p.2) PM := by
    rw [hXA]; exact aesm_mixed hcoef.sm b₁ a₁
  have haeY : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Yf p.1 p.2) PM := by
    rw [hYf]; exact aesm_mixed hdat.sm (b + 1 - b₁) (a - a₁)
  have haeZ : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Zf p.1 p.2) PM := by
    rw [hZf]; exact aesm_mixed hdat.sm b a
  have haeW : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => cW p.1 p.2) PM := by
    rw [hcW]; exact aesm_canonW (Work.Spaces.gam α)
  have hmeasX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => cW p.1 p.2 * (XA p.1 p.2) ^ 2) PM :=
    (haeW.mul (haeX.mul haeX)).congr
      (Filter.Eventually.of_forall (fun p => by simp only [Pi.mul_apply, pow_two]))
  have hmeasZ : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => cW p.1 p.2 * (Zf p.1 p.2) ^ 2) PM :=
    (haeW.mul (haeZ.mul haeZ)).congr
      (Filter.Eventually.of_forall (fun p => by simp only [Pi.mul_apply, pow_two]))
  -- the `Z`-slot energy (independent of the case split)
  have hdomZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      cW z θ * (Zf z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ _ hθ hθ2
    have h := Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α)
      (q := Work.Spaces.gam α) (g := f) 6 le_rfl (z := z) (θ := θ) hθ hθ2
      (j := b) (i := a) ha hab
    rw [hZf]
    simpa only [hcW] using h
  have hAZ := val_le_HkSq (α := α) (k := 6) (f := f) (ρv := cW) (X := Zf)
    hdat.sm hdat.h6 hcWnn hdomZ hmeasZ
  -- **the engine**: a sup bound on the middle factor and the two weighted `L²`-values
  have hmain : ∀ (KY AX AZ : ℝ), 0 ≤ KY → 0 ≤ AX → 0 ≤ AZ →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Yf z θ| ≤ KY) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => cW p.1 p.2 * (XA p.1 p.2) ^ 2) PM →
      (∫ p, cW p.1 p.2 * (XA p.1 p.2) ^ 2 ∂PM) ≤ AX →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => cW p.1 p.2 * (Zf p.1 p.2) ^ 2) PM →
      (∫ p, cW p.1 p.2 * (Zf p.1 p.2) ^ 2 ∂PM) ≤ AZ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * XA p.1 p.2 * Yf p.1 p.2
          * Zf p.1 p.2) PM ∧
        |∫ p, ρ p.1 p.2 * XA p.1 p.2 * Yf p.1 p.2 * Zf p.1 p.2 ∂PM|
          ≤ KY * (Real.sqrt AX * Real.sqrt AZ) := by
    intro KY AX AZ hKY0 hAX0 hAZ0 hYsup hI1 hv1 hI2 hv2
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |ρ z θ * XA z θ * Yf z θ * Zf z θ|
          ≤ KY * (Real.sqrt (cW z θ * (XA z θ) ^ 2)
              * Real.sqrt (cW z θ * (Zf z θ) ^ 2)) := by
      intro z θ hz hθ hθ2
      have hρle : ρ z θ ≤ cW z θ := leafW_le_canonW_gam hα0 hleaf z θ hz hθ hθ2
      have hρnn : 0 ≤ ρ z θ := leafW_nonneg hleaf z θ hz hθ hθ2
      have hcnn : 0 ≤ cW z θ := hcWnn z θ hz hθ hθ2
      have hY := hYsup z θ hz hθ hθ2
      have hroot : Real.sqrt (cW z θ) * Real.sqrt (cW z θ) = cW z θ := by
        have h := Real.sq_sqrt hcnn
        rwa [pow_two] at h
      have hkey : Real.sqrt (cW z θ * (XA z θ) ^ 2) * Real.sqrt (cW z θ * (Zf z θ) ^ 2)
          = cW z θ * |XA z θ| * |Zf z θ| := by
        rw [Real.sqrt_mul hcnn, Real.sqrt_mul hcnn, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
        conv_rhs => rw [← hroot]
        ring
      rw [hkey, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
      calc ρ z θ * |XA z θ| * |Yf z θ| * |Zf z θ|
          ≤ cW z θ * |XA z θ| * KY * |Zf z θ| := by gcongr
        _ = KY * (cW z θ * |XA z θ| * |Zf z θ|) := by ring
    have hm1 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Real.sqrt (cW p.1 p.2 * (XA p.1 p.2) ^ 2)) PM :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hmeasX
    have hm2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Real.sqrt (cW p.1 p.2 * (Zf p.1 p.2) ^ 2)) PM :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hmeasZ
    obtain ⟨hInt, hbd⟩ := rowSummand_core (α := α) (KY := KY) (AX := AX) (AZ := AZ)
      (f := fun _ _ => (0 : ℝ)) (X := XA) (Y := Yf) (Z := Zf) (ρv := ρ) (ρ₁ := cW) (ρ₂ := cW)
      hKY0 hAX0 hAZ0 (leafW_nonneg hleaf) hI1 hI2 hv1 hv2
      (ae_of_forall_Qd hcWnn) (ae_of_forall_Qd hcWnn) hm1 hm2
      (aesm_leafW hleaf) haeX haeY haeZ hpt
    exact ⟨hInt, hbd⟩
  by_cases hple4 : a₁ + b₁ ≤ 4
  · -- **Case `a₁ + b₁ ≤ 4`**: the middle factor has order `≤ 4`.
    have hq4 : (a - a₁) + (b + 1 - b₁) ≤ 4 := by omega
    have hsupY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Yf z θ| ≤ Csup * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f := by
      intro z θ hz hθ hθ2
      have h1 := hsup α f hα0 hα1 hdat.sm hdat.h6 (b + 1 - b₁) (a - a₁) hq4 z θ hz hθ hθ2
      rw [hYf]
      exact h1
    have hdomA4 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        cW z θ * (XA z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 A z θ := by
      intro z θ _ hθ hθ2
      have h := Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α)
        (q := Work.Spaces.gam α) (g := A) 4 le_rfl (z := z) (θ := θ) hθ hθ2
        (j := b₁) (i := a₁) ha1 hple4
      rw [hXA]
      simpa only [hcW] using h
    have hAX := val_le_HkSq (α := α) (k := 4) (f := A) (ρv := cW) (X := XA)
      hcoef.sm hcoef.h4 hcWnn hdomA4 hmeasX
    obtain ⟨hint, hbd⟩ := hmain (Csup * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
      (Work.Spaces.HkSq α 4 A) (Work.Spaces.HkSq α 6 f)
      (mul_nonneg (mul_nonneg hCsup.le hαinv0) hN6)
      (Work.Spaces.HkSq_nonneg α 4 A) hQ6 hsupY hAX.1 hAX.2 hAZ.1 hAZ.2
    refine ⟨hint, ?_⟩
    refine le_trans hbd ?_
    have hcaseA : (Csup * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
          * (Real.sqrt (Work.Spaces.HkSq α 4 A) * Real.sqrt (Work.Spaces.HkSq α 6 f))
        ≤ Csup * α ^ (-(1 / 2 : ℝ)) * (K4 * Work.Spaces.HkSq α 6 f) := by
      calc (Csup * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
            * (Real.sqrt (Work.Spaces.HkSq α 4 A) * Real.sqrt (Work.Spaces.HkSq α 6 f))
          = (Csup * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
              * (Work.Spaces.HkNorm α 4 A * Work.Spaces.HkNorm α 6 f) := rfl
        _ ≤ (Csup * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
              * (K4 * Work.Spaces.HkNorm α 6 f) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (mul_nonneg hCsup.le hαinv0) hN6)
            exact mul_le_mul_of_nonneg_right hcoef.n4 hN6
        _ = Csup * α ^ (-(1 / 2 : ℝ)) * (K4 * Work.Spaces.HkSq α 6 f) := by
            rw [← hNQ]; ring
    exact le_trans hcaseA (hstep Csup (K4 * Work.Spaces.HkSq α 6 f) hCsup.le
      (mul_nonneg hK4 hQ6) hT1 (by have := le_max_left Cmp (Cdz * Real.sqrt 10); linarith))
  · -- **Case `5 ≤ a₁ + b₁`**: the middle factor has order `≤ 2`.
    have hp5 : 5 ≤ a₁ + b₁ := by omega
    have hq2 : (a - a₁) + (b + 1 - b₁) ≤ 2 := by omega
    have hsupY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Yf z θ| ≤ max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * M := by
      intro z θ hz hθ hθ2
      rw [hYf]
      by_cases halta : a₁ < a
      · have hi : 1 ≤ a - a₁ := by omega
        have h1 := hmp α f hα0 hα1 hdat.sm hmem4 (b + 1 - b₁) (a - a₁) hi hq2 z θ hz hθ hθ2
        have hMle : M ≤ α ^ (-(1 / 2 : ℝ)) * M := by
          simpa using mul_le_mul_of_nonneg_right hαinv1 hM
        calc |Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ|
            ≤ Cmp * Work.FTS.Nonlin.Xn α f := h1
          _ ≤ Cmp * M := mul_le_mul_of_nonneg_left hdat.bdd hCmp.le
          _ ≤ max Cmp (Cdz * Real.sqrt 10) * M :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hM
          _ ≤ max Cmp (Cdz * Real.sqrt 10) * (α ^ (-(1 / 2 : ℝ)) * M) :=
              mul_le_mul_of_nonneg_left hMle hmax0
          _ = max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * M := by ring
      · have haz : a - a₁ = 0 := by omega
        have hb2 : b + 1 - b₁ ≤ 2 := by omega
        have h1 := hdz α f hα0 hα1 hdat.sm hmem4 (b + 1 - b₁) hb2 z θ hz hθ hθ2
        have hfac : Cdz / Real.sqrt (Work.Spaces.gam α - 1)
            = Cdz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
          have hinv : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hα0.le]
          rw [Work.Spaces.gam_sub_one α, Real.sqrt_div hα0.le, div_div_eq_mul_div,
            div_eq_mul_inv, hinv]
        rw [haz, Work.Spaces.mixed_zero_right]
        calc |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
            ≤ Cdz / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := h1
          _ = Cdz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f := by rw [hfac]
          _ ≤ Cdz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M :=
              mul_le_mul_of_nonneg_left hdat.bdd
                (mul_nonneg (mul_nonneg hCdz.le hsq10) hαinv0)
          _ ≤ max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * M :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_right _ _) hαinv0) hM
    have hp6 : a₁ + b₁ ≤ 6 := by omega
    have hdomA6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        cW z θ * (XA z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 A z θ := by
      intro z θ _ hθ hθ2
      have h := Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α)
        (q := Work.Spaces.gam α) (g := A) 6 le_rfl (z := z) (θ := θ) hθ hθ2
        (j := b₁) (i := a₁) ha1 hp6
      rw [hXA]
      simpa only [hcW] using h
    have hAX6 := val_le_HkSq (α := α) (k := 6) (f := A) (ρv := cW) (X := XA)
      hcoef.sm hcoef.h6 hcWnn hdomA6 hmeasX
    obtain ⟨hint, hbd⟩ := hmain (max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * M)
      (Work.Spaces.HkSq α 6 A) (Work.Spaces.HkSq α 6 f)
      (mul_nonneg (mul_nonneg hmax0 hαinv0) hM)
      (Work.Spaces.HkSq_nonneg α 6 A) hQ6 hsupY hAX6.1 hAX6.2 hAZ.1 hAZ.2
    refine ⟨hint, ?_⟩
    refine le_trans hbd ?_
    have hcaseB : (max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * M)
          * (Real.sqrt (Work.Spaces.HkSq α 6 A) * Real.sqrt (Work.Spaces.HkSq α 6 f))
        ≤ max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ))
            * (M * K6 * Work.Spaces.HkNorm α 6 f) := by
      calc (max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * M)
            * (Real.sqrt (Work.Spaces.HkSq α 6 A) * Real.sqrt (Work.Spaces.HkSq α 6 f))
          = (max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * M)
              * (Work.Spaces.HkNorm α 6 A * Work.Spaces.HkNorm α 6 f) := rfl
        _ ≤ (max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ)) * M)
              * (K6 * Work.Spaces.HkNorm α 6 f) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (mul_nonneg hmax0 hαinv0) hM)
            exact mul_le_mul_of_nonneg_right hcoef.n6 hN6
        _ = max Cmp (Cdz * Real.sqrt 10) * α ^ (-(1 / 2 : ℝ))
              * (M * K6 * Work.Spaces.HkNorm α 6 f) := by ring
    exact le_trans hcaseB (hstep (max Cmp (Cdz * Real.sqrt 10))
      (M * K6 * Work.Spaces.HkNorm α 6 f) hmax0 (mul_nonneg (mul_nonneg hM hK6) hN6) hT2
      (by have := le_max_right Cmp (Cdz * Real.sqrt 10); linarith))

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
