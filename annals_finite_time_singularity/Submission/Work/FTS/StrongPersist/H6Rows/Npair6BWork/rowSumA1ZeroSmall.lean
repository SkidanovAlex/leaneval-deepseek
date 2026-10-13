import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-- **Leibniz summand with a pure coefficient slot (`a₁ = 0`), radial order `b₁ ≤ 4`, mixed datum `1 ≤ a`,
`b₁ ≤ b`.**

`X := D_z^{b₁}A`, `Y := mixed (b+1-b₁) a f`, `Z := mixed b a f`, both `f`-slots mixed (`a ≥ 1`) and of order
`≤ 6` (`ord Z = a+b ≤ 6`, `ord Y = a+b+1-b₁ ≤ 6` by the non-flux hypothesis `¬(b₁ = 0 ∧ a+b = 6)` and
`b₁ ≤ b`).

* `b₁ ≤ 2`: `|D_z^{b₁}A| ≤ Cα^{-1/2}(K0+K4)` pointwise (`CoefData.val` at `b₁ = 0`, `TransportS.sup_dz_le_hk`
  at `b₁ = 1,2`, with `Xn α A = HkNorm α 4 A`), and `∫ρ|Y||Z| ≤ HkSq α 6 f` (Cauchy–Schwarz with the same
  weight `ρ ≤ canonW (gam α)`; each weighted square is a mixed slot of `HkIntegrand α 6 f`).
* `3 ≤ b₁ ≤ 4`: `|D_z^{b₁}A| ≤ C₃α^{-1/2}K6` (`T1SixAux.supSix` applied to `A` with `(b,a) = (b₁,0)`,
  `HkMem α 6 A`), and `∫ρ|Y||Z| ≤ M·HkNorm α 6 f` because `ord Y = a+b+1-b₁ ≤ 4` (using `b₁ ≤ b`) gives
  `∫ρY² ≤ HkSq α 4 f ≤ M²` (a mixed slot of `HkIntegrand α 4 f`), while `∫ρZ² ≤ HkSq α 6 f`.

Assemble with `Npair6BWork.rowSummand_core`/`val_le_HkSq`, `canonW_mul_z_le_of_le`,
`canonW_mul_mixed_le_of_le`, `leafW_le_canonW_gam`, `aesm_mixed`, `HkMem_mono_le`. -/
theorem rowSumA1ZeroSmall : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (a b b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ → 1 ≤ a → b₁ ≤ 4 → b₁ ≤ b →
      ¬ (b₁ = 0 ∧ a + b = 6) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.DzIter b₁ A p.1 p.2
          * Work.Spaces.mixed (b + 1 - b₁) a f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
            * Work.Spaces.mixed (b + 1 - b₁) a f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f
               + M * K6 * Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨Cdz, hCdz, hdz⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Csup, hCsup, hsup⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.supSix
  have hsq10 : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  refine ⟨Cdz * Real.sqrt 10 + Csup + 1, by positivity, ?_⟩
  intro α hα A f K0 K4 K6 K1 M a b b₁ ρ hcoef hctmem hctle hdat hab hleaf ha hb1le4 hb1leb hflux
  obtain ⟨hα0, hα1⟩ := hα
  -- the inverse power of `α`
  have hαinv0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hαinv1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  -- nonnegativity of every price
  have hK0 : 0 ≤ K0 :=
    le_trans (abs_nonneg _) (hcoef.val 1 (Real.pi / 4) one_pos
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hM : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hQ4 : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hQ6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hN6 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  -- the two `f`-slots and the common weight
  let cW : ℝ → ℝ → ℝ := Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α)
  have hcW : cW = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) := rfl
  set Xf : ℝ → ℝ → ℝ := Work.Spaces.mixed (b + 1 - b₁) a f with hXf
  set Zf : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f with hZf
  let Yf : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.DzIter b₁ A z θ
  have hYf : Yf = fun z θ => Work.Spaces.DzIter b₁ A z θ := rfl
  have hcWnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ cW z θ :=
    fun _ _ _ hθ hθ2 => Work.FTS.TransportS.SlotT2.canonW_nonneg ⟨hθ.le, hθ2.le⟩
  -- a.e. strong measurability of the five factors
  have haeX : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Xf p.1 p.2) PM := by
    rw [hXf]; exact aesm_mixed hdat.sm (b + 1 - b₁) a
  have haeZ : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Zf p.1 p.2) PM := by
    rw [hZf]; exact aesm_mixed hdat.sm b a
  have haeW : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => cW p.1 p.2) PM :=
    aesm_canonW (Work.Spaces.gam α)
  have haeY : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Yf p.1 p.2) PM :=
    aesm_of_smoothOpen (hcoef.sm.DzIter b₁)
  have hmeasX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => cW p.1 p.2 * (Xf p.1 p.2) ^ 2) PM :=
    (haeW.mul (haeX.mul haeX)).congr
      (Filter.Eventually.of_forall (fun p => by simp only [Pi.mul_apply, pow_two]))
  have hmeasZ : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => cW p.1 p.2 * (Zf p.1 p.2) ^ 2) PM :=
    (haeW.mul (haeZ.mul haeZ)).congr
      (Filter.Eventually.of_forall (fun p => by simp only [Pi.mul_apply, pow_two]))
  -- order bookkeeping
  have hordX6 : a + (b + 1 - b₁) ≤ 6 := by omega
  -- the `Z`-slot energy (independent of the case split)
  have hdomZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      cW z θ * (Zf z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ _ hθ hθ2
    have h := Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α)
      (q := Work.Spaces.gam α) (g := f) 6 le_rfl (z := z) (θ := θ) hθ hθ2
      (j := b) (i := a) ha hab
    simpa only [hcW, hZf] using h
  have hAZ := val_le_HkSq (α := α) (k := 6) (f := f) (ρv := cW) (X := Zf)
    hdat.sm hdat.h6 hcWnn hdomZ hmeasZ
  -- **the engine**: a sup bound on the coefficient slot and the two weighted `L²`-values
  have hmain : ∀ (KX AX AZ : ℝ), 0 ≤ KX → 0 ≤ AX → 0 ≤ AZ →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter b₁ A z θ| ≤ KX) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => cW p.1 p.2 * (Xf p.1 p.2) ^ 2) PM →
      (∫ p, cW p.1 p.2 * (Xf p.1 p.2) ^ 2 ∂PM) ≤ AX →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => cW p.1 p.2 * (Zf p.1 p.2) ^ 2) PM →
      (∫ p, cW p.1 p.2 * (Zf p.1 p.2) ^ 2 ∂PM) ≤ AZ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
          * Xf p.1 p.2 * Zf p.1 p.2) PM ∧
        |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2 * Xf p.1 p.2 * Zf p.1 p.2 ∂PM|
          ≤ KX * (Real.sqrt AX * Real.sqrt AZ) := by
    intro KX AX AZ hKX0 hAX0 hAZ0 hYsup hI1 hv1 hI2 hv2
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |ρ z θ * Xf z θ * Work.Spaces.DzIter b₁ A z θ * Zf z θ|
          ≤ KX * (Real.sqrt (cW z θ * (Xf z θ) ^ 2)
              * Real.sqrt (cW z θ * (Zf z θ) ^ 2)) := by
      intro z θ hz hθ hθ2
      have hρle : ρ z θ ≤ cW z θ := by
        rw [hcW]; exact leafW_le_canonW_gam hα0 hleaf z θ hz hθ hθ2
      have hρnn : 0 ≤ ρ z θ := leafW_nonneg hleaf z θ hz hθ hθ2
      have hcnn : 0 ≤ cW z θ := hcWnn z θ hz hθ hθ2
      have hY := hYsup z θ hz hθ hθ2
      have hroot : Real.sqrt (cW z θ) * Real.sqrt (cW z θ) = cW z θ := by
        have h := Real.sq_sqrt hcnn
        rwa [pow_two] at h
      have hkey : Real.sqrt (cW z θ * (Xf z θ) ^ 2) * Real.sqrt (cW z θ * (Zf z θ) ^ 2)
          = cW z θ * |Xf z θ| * |Zf z θ| := by
        rw [Real.sqrt_mul hcnn, Real.sqrt_mul hcnn, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
        conv_rhs => rw [← hroot]
        ring
      rw [hkey, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
      calc ρ z θ * |Xf z θ| * |Work.Spaces.DzIter b₁ A z θ| * |Zf z θ|
          ≤ cW z θ * |Xf z θ| * KX * |Zf z θ| := by gcongr
        _ = KX * (cW z θ * |Xf z θ| * |Zf z θ|) := by ring
    have hm1 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Real.sqrt (cW p.1 p.2 * (Xf p.1 p.2) ^ 2)) PM :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hmeasX
    have hm2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Real.sqrt (cW p.1 p.2 * (Zf p.1 p.2) ^ 2)) PM :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hmeasZ
    obtain ⟨hInt, hbd⟩ := rowSummand_core (α := α) (KY := KX) (AX := AX) (AZ := AZ)
      (f := fun _ _ => (0 : ℝ)) (X := Xf) (Y := Yf) (Z := Zf)
      (ρv := ρ) (ρ₁ := cW) (ρ₂ := cW)
      hKX0 hAX0 hAZ0 (leafW_nonneg hleaf) hI1 hI2 hv1 hv2
      (ae_of_forall_Qd hcWnn) (ae_of_forall_Qd hcWnn) hm1 hm2
      (aesm_leafW hleaf) haeX haeY haeZ hpt
    have hswap : ∀ p : ℝ × ℝ, ρ p.1 p.2 * Xf p.1 p.2 * Yf p.1 p.2 * Zf p.1 p.2
        = ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2 * Xf p.1 p.2 * Zf p.1 p.2 := by
      intro p
      simp only [hYf]
      ring
    refine ⟨hInt.congr (Filter.Eventually.of_forall hswap), ?_⟩
    have heq : (∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2 * Xf p.1 p.2
          * Zf p.1 p.2 ∂PM)
        = ∫ p, ρ p.1 p.2 * Xf p.1 p.2 * Yf p.1 p.2 * Zf p.1 p.2 ∂PM :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => (hswap p).symm))
    rw [heq]
    exact hbd
  by_cases hb2 : b₁ ≤ 2
  · -- **Case `b₁ ≤ 2`**: the coefficient slot is bounded by `C α^{-1/2}(K0+K4)`
    have hsupA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter b₁ A z θ|
          ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
      intro z θ hz hθ hθ2
      rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
      · subst h0
        have h1 : |A z θ| ≤ K0 := hcoef.val z θ hz hθ hθ2
        have h2 : (1 : ℝ) ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) := by
          have h3 : (1 : ℝ) ≤ Cdz * Real.sqrt 10 + 1 := by nlinarith [hCdz, hsq10]
          exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1)
            (mul_le_mul h3 hαinv1 (by norm_num) (by linarith))
        calc |Work.Spaces.DzIter 0 A z θ| = |A z θ| := by rw [Work.Spaces.DzIter_zero]
          _ ≤ K0 := h1
          _ ≤ 1 * (K0 + K4) := by rw [one_mul]; linarith
          _ ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
              mul_le_mul_of_nonneg_right h2 (by linarith)
      · have hdz1 := hdz α A hα0 hα1 hcoef.sm hcoef.h4 b₁ hb2 z θ hz hθ hθ2
        have hfac : Cdz / Real.sqrt (Work.Spaces.gam α - 1)
            = Cdz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
          have hinv : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hα0.le]
          rw [Work.Spaces.gam_sub_one α, Real.sqrt_div hα0.le, div_div_eq_mul_div,
            div_eq_mul_inv, hinv]
        calc |Work.Spaces.DzIter b₁ A z θ|
            ≤ Cdz / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A := hdz1
          _ ≤ Cdz / Real.sqrt (Work.Spaces.gam α - 1) * K4 :=
              mul_le_mul_of_nonneg_left hcoef.n4 (div_nonneg hCdz.le (Real.sqrt_nonneg _))
          _ = Cdz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4 := by rw [hfac]
          _ ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
              have hstep : Cdz * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4
                  ≤ (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * K4 := by
                refine mul_le_mul_of_nonneg_right ?_ hK4
                exact mul_le_mul_of_nonneg_right (by linarith) hαinv0
              refine le_trans hstep ?_
              exact mul_le_mul_of_nonneg_left (by linarith)
                (mul_nonneg (by nlinarith [hCdz, hsq10]) hαinv0)
    have hdomX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        cW z θ * (Xf z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      intro z θ _ hθ hθ2
      have h := Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α)
        (q := Work.Spaces.gam α) (g := f) 6 le_rfl (z := z) (θ := θ) hθ hθ2
        (j := b + 1 - b₁) (i := a) ha hordX6
      simpa only [hcW, hXf] using h
    have hAX := val_le_HkSq (α := α) (k := 6) (f := f) (ρv := cW) (X := Xf)
      hdat.sm hdat.h6 hcWnn hdomX hmeasX
    obtain ⟨hIntA, hbdA⟩ := hmain ((Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
      (Work.Spaces.HkSq α 6 f) (Work.Spaces.HkSq α 6 f)
      (mul_nonneg (mul_nonneg (by nlinarith [hCdz, hsq10]) hαinv0)
        (by linarith : (0 : ℝ) ≤ K0 + K4)) hQ6 hQ6 hsupA hAX.1 hAX.2 hAZ.1 hAZ.2
    refine ⟨hIntA, ?_⟩
    have hsq : Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 f)
        = Work.Spaces.HkSq α 6 f := by
      rw [← pow_two]; exact Real.sq_sqrt hQ6
    rw [hsq] at hbdA
    refine le_trans hbdA ?_
    have hK04 : 0 ≤ K0 + K4 := by linarith
    have hmonoA : (K0 + K4) * Work.Spaces.HkSq α 6 f
        ≤ (K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f := by
      have h := mul_nonneg (mul_nonneg hM hK6) hN6
      linarith
    have hfac1 : (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4)
        ≤ (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
      refine mul_le_mul_of_nonneg_right ?_ hK04
      exact mul_le_mul_of_nonneg_right (by linarith) hαinv0
    calc (Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * Work.Spaces.HkSq α 6 f
        = ((Cdz * Real.sqrt 10 + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
            * Work.Spaces.HkSq α 6 f := rfl
      _ ≤ ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
            * Work.Spaces.HkSq α 6 f := mul_le_mul_of_nonneg_right hfac1 hQ6
      _ = ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left hmonoA
            (mul_nonneg (by nlinarith [hCdz, hCsup, hsq10]) hαinv0)
      _ = (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) := by ring
  · -- **Case `3 ≤ b₁`**: the coefficient slot is bounded by `C α^{-1/2}K6`
    have h3 : 3 ≤ b₁ := by omega
    have hordX4 : a + (b + 1 - b₁) ≤ 4 := by omega
    have hsupB : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter b₁ A z θ| ≤ Csup * α ^ (-(1 / 2 : ℝ)) * K6 := by
      intro z θ hz hθ hθ2
      have h1 := hsup α A hα0 hα1 hcoef.sm hcoef.h6 b₁ 0 (by omega) z θ hz hθ hθ2
      rw [Work.Spaces.mixed_zero_right] at h1
      calc |Work.Spaces.DzIter b₁ A z θ|
          ≤ Csup * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A := h1
        _ ≤ Csup * α ^ (-(1 / 2 : ℝ)) * K6 :=
            mul_le_mul_of_nonneg_left hcoef.n6 (mul_nonneg hCsup.le hαinv0)
    have hmem4 : Work.Spaces.HkMem α 4 f := HkMem_mono_le hdat.sm (by norm_num) hdat.h6
    have hdomX4 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        cW z θ * (Xf z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      intro z θ _ hθ hθ2
      have h := Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le (α := α)
        (q := Work.Spaces.gam α) (g := f) 4 le_rfl (z := z) (θ := θ) hθ hθ2
        (j := b + 1 - b₁) (i := a) ha hordX4
      simpa only [hcW, hXf] using h
    have hAX := val_le_HkSq (α := α) (k := 4) (f := f) (ρv := cW) (X := Xf)
      hdat.sm hmem4 hcWnn hdomX4 hmeasX
    obtain ⟨hIntB, hbdB⟩ := hmain (Csup * α ^ (-(1 / 2 : ℝ)) * K6) (Work.Spaces.HkSq α 4 f)
      (Work.Spaces.HkSq α 6 f) (mul_nonneg (mul_nonneg hCsup.le hαinv0) hK6) hQ4 hQ6
      hsupB hAX.1 hAX.2 hAZ.1 hAZ.2
    refine ⟨hIntB, ?_⟩
    have hstep : Csup * α ^ (-(1 / 2 : ℝ)) * K6 * (M * Work.Spaces.HkNorm α 6 f)
        ≤ (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ))
          * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) := by
      have hC : Csup * α ^ (-(1 / 2 : ℝ))
          ≤ (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hCdz, hsq10]) hαinv0
      have hMKN : 0 ≤ M * K6 * Work.Spaces.HkNorm α 6 f := mul_nonneg (mul_nonneg hM hK6) hN6
      have hmonoB : M * K6 * Work.Spaces.HkNorm α 6 f
          ≤ (K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f := by
        have h := mul_nonneg (by linarith : (0 : ℝ) ≤ K0 + K4) hQ6
        linarith
      calc Csup * α ^ (-(1 / 2 : ℝ)) * K6 * (M * Work.Spaces.HkNorm α 6 f)
          = (Csup * α ^ (-(1 / 2 : ℝ))) * (M * K6 * Work.Spaces.HkNorm α 6 f) := by ring
        _ ≤ ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)))
              * (M * K6 * Work.Spaces.HkNorm α 6 f) := mul_le_mul_of_nonneg_right hC hMKN
        _ ≤ ((Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ)))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) :=
            mul_le_mul_of_nonneg_left hmonoB
              (mul_nonneg (by nlinarith [hCdz, hCsup, hsq10]) hαinv0)
        _ = (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) := by
            ring
    refine le_trans hbdB ?_
    calc Csup * α ^ (-(1 / 2 : ℝ)) * K6
          * (Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 6 f))
        = Csup * α ^ (-(1 / 2 : ℝ)) * K6
          * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) := rfl
      _ ≤ Csup * α ^ (-(1 / 2 : ℝ)) * K6 * (M * Work.Spaces.HkNorm α 6 f) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg hCsup.le hαinv0) hK6)
          exact mul_le_mul hdat.bdd le_rfl hN6 hM
      _ ≤ (Cdz * Real.sqrt 10 + Csup + 1) * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f + M * K6 * Work.Spaces.HkNorm α 6 f) := hstep

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
