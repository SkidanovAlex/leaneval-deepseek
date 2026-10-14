import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumGamSin
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open Work.FTS.StrongPersist.H6Rows.Npair6BWork (PM aesm_mixed aesm_leafW val_le_HkSq)

set_option autoImplicit false
set_option maxHeartbeats 3200000




end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumA1Small =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option autoImplicit false

/-- **Leibniz summand, coefficient slot of angular order `a₁ ≥ 1` and total order `a₁ + b₁ ≤ 2`, other than the
`σ`-gain case.**

`X := mixed b₁ a₁ A`, `Y := mixed (b+1-b₁) (a-a₁) f`, `Z := mixed b a f`.

* `|X| ≤ √15·Xn α A ≤ √15·K4` pointwise (`T2SupB2.mixed_pointwise_le_Xn`, `1 ≤ a₁`, `a₁+b₁ ≤ 2`, from
  `SmoothOpen A` and `HkMem α 4 A`).
* `∫ρ|Y||Z| ≤ HkSq α 6 f`: Cauchy–Schwarz with the single weight `ρ` (`cs_sqrt`), where
  `ρY² ≤ HkIntegrand α 6 f` pointwise because either `a₁ < a` (`Y` is mixed of order
  `a+b+1-a₁-b₁ ≤ 6`, `ρ ≤ canonW (gam α)`) or `a₁ = a` (`Y = D_z^{b+1-b₁} f` is pure of order `≤ 6` and
  `ρ ≠ leafGam α` gives `ρ ≤ canonW η`, while `ρZ² ≤ canonW (gam α)Z² ≤ HkIntegrand α 6 f`).
* Hence `|∫ρXYZ| ≤ sup|X|·∫ρ|Y||Z| ≤ √15·K4·HkSq α 6 f ≤ C α^{-4}·T` with
  `T := (1+K0+K4+K1)(1+M)(1+HkSq α 6 f) + (K4+K6)(1+M)(1+HkNorm α 6 f)`
  (since `K4·HkSq ≤ T` and `α^{-4} ≥ 1`).

Integrability via `Integrable.mono'` from the majorant `√15K4·ρ|Y||Z| ≤ √15K4·(ρY²+ρZ²)/2`
(`val_le_HkSq` for each of the two slots). -/

-- Proof as formalised (the pointwise `AM–GM` route, which packages the two `val_le_HkSq`
-- slots into a single integrability argument): the pointwise pairing bound
-- `ρ|Y||Z| ≤ HkIntegrand α 6 f` (the two slot dominations plus `2ab ≤ a²+b²`) is the
-- delegated lemma `Npair6BWork.rowA1SmallPair`; combined with `|X| ≤ Cx·Xn α A ≤ Cx·K4` it
-- gives `|ρXYZ| ≤ Cx·K4·HkIntegrand α 6 f` on the open quadrant, whence `Integrable` and
-- `|∫ ρXYZ| ≤ Cx·K4·HkSq α 6 f` by `abs_integral_le_pointwise`.  The final real-arithmetic
-- step is `K4·HkSq α 6 f ≤ T` (`K4 ≤ 1+K0+K4+K1`, `1 ≤ 1+M`, `HkSq ≤ 1+HkSq`) together with
-- `1 ≤ α^{-4}`.
theorem rowSumA1Small : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ → 1 ≤ a₁ → a₁ ≤ a → b₁ ≤ b →
      a₁ + b₁ ≤ 2 → ¬ (a₁ = a ∧ ρ = Work.FTS.TransportS.leafGam α) →
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
  obtain ⟨Cx, hCxpos, hCx⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨Cx + 4, by linarith, ?_⟩
  intro α hα A f K0 K4 K6 K1 M a b a₁ b₁ ρ hcoef hctmem hctle hdat hab hleaf ha₁ ha₁a hb₁ hab₁ hne
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the nonnegativity of the six finiteness constants
  have hXnA : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α A := Work.Spaces.HkNorm_nonneg α 4 A
  have hK4 : (0 : ℝ) ≤ K4 := le_trans hXnA hcoef.n4
  have hK6 : (0 : ℝ) ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hM0 : (0 : ℝ) ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hK0 : (0 : ℝ) ≤ K0 :=
    le_trans (abs_nonneg (A 1 (Real.pi / 4)))
      (hcoef.val 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hK1 : (0 : ℝ) ≤ K1 := le_trans (coefTh_nonneg 1 A) hctle
  -- the pointwise bound on the coefficient slot `X`
  have hXb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b₁ a₁ A z θ| ≤ Cx * K4 := by
    intro z θ hz hθ hθ2
    exact le_trans (hCx α A hα0 hα1 hcoef.sm hcoef.h4 b₁ a₁ ha₁ hab₁ z θ hz hθ hθ2)
      (mul_le_mul_of_nonneg_left hcoef.n4 hCxpos.le)
  -- the pointwise bound on the whole summand
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |ρ z θ * Work.Spaces.mixed b₁ a₁ A z θ
        * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ * Work.Spaces.mixed b a f z θ|
      ≤ (Cx * K4) * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ hθ2
    have hρnn : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz hθ hθ2
    have hpair : ρ z θ * |Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ|
          * |Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      rowA1SmallPair (f := f) hα0 hleaf ha₁ ha₁a hb₁ hab₁ hab hne z θ hz hθ hθ2
    have hXX := hXb z θ hz hθ hθ2
    calc |ρ z θ * Work.Spaces.mixed b₁ a₁ A z θ
          * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ * Work.Spaces.mixed b a f z θ|
        = ρ z θ * |Work.Spaces.mixed b₁ a₁ A z θ|
            * |Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ|
            * |Work.Spaces.mixed b a f z θ| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
      _ ≤ ρ z θ * (Cx * K4)
            * |Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ|
            * |Work.Spaces.mixed b a f z θ| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hXX hρnn) (abs_nonneg _)) (abs_nonneg _)
      _ = (Cx * K4) * (ρ z θ * |Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ|
            * |Work.Spaces.mixed b a f z θ|) := by ring
      _ ≤ (Cx * K4) * Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul_of_nonneg_left hpair (mul_nonneg hCxpos.le hK4)
  -- a.e. strong measurability of the summand
  have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b₁ a₁ A p.1 p.2
      * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) PM :=
    (((aesm_leafW hleaf).mul (aesm_mixed hcoef.sm b₁ a₁)).mul
      (aesm_mixed hdat.sm (b + 1 - b₁) (a - a₁))).mul (aesm_mixed hdat.sm b a)
  obtain ⟨hint, hbound⟩ := abs_integral_le_pointwise (M := Cx * K4)
    (F := fun z θ => ρ z θ * Work.Spaces.mixed b₁ a₁ A z θ
      * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ * Work.Spaces.mixed b a f z θ)
    hdat.sm hdat.h6 (mul_nonneg hCxpos.le hK4) haesm hpt
  refine ⟨hint, ?_⟩
  -- the final real arithmetic
  have hs : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hn : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hA : (1 : ℝ) ≤ α ^ (-(4 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(4 : ℝ) ≤ 0 by norm_num)
    rw [Real.rpow_zero] at h
    exact h
  set T : ℝ := (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) with hTdef
  have hB1 : K4 * Work.Spaces.HkSq α 6 f
      ≤ (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    have h2 : K4 ≤ 1 + K0 + K4 + K1 := by linarith
    have h3 : (1 : ℝ) ≤ 1 + M := by linarith
    have h1 : (0 : ℝ) ≤ 1 + K0 + K4 + K1 := by linarith
    have hstep : K4 * 1 ≤ (1 + K0 + K4 + K1) * (1 + M) := mul_le_mul h2 h3 (by norm_num) h1
    have hstep2 : K4 * Work.Spaces.HkSq α 6 f
        ≤ ((1 + K0 + K4 + K1) * (1 + M)) * Work.Spaces.HkSq α 6 f := by
      have := mul_le_mul_of_nonneg_right hstep hs
      linarith [this]
    have hstep3 : ((1 + K0 + K4 + K1) * (1 + M)) * Work.Spaces.HkSq α 6 f
        ≤ ((1 + K0 + K4 + K1) * (1 + M)) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg h1 (by linarith))
    calc K4 * Work.Spaces.HkSq α 6 f
        ≤ ((1 + K0 + K4 + K1) * (1 + M)) * Work.Spaces.HkSq α 6 f := hstep2
      _ ≤ ((1 + K0 + K4 + K1) * (1 + M)) * (1 + Work.Spaces.HkSq α 6 f) := hstep3
      _ = (1 + K0 + K4 + K1) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by ring
  have hB2nn : (0 : ℝ) ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hT : K4 * Work.Spaces.HkSq α 6 f ≤ T := by
    rw [hTdef]
    exact le_trans hB1 (le_add_of_nonneg_right hB2nn)
  have hTnn : (0 : ℝ) ≤ T := le_trans (mul_nonneg hK4 hs) hT
  calc |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      = |∫ p, (fun z θ => ρ z θ * Work.Spaces.mixed b₁ a₁ A z θ
          * Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ
          * Work.Spaces.mixed b a f z θ) p.1 p.2 ∂PM| := rfl
    _ ≤ Cx * K4 * Work.Spaces.HkSq α 6 f := hbound
    _ = Cx * (K4 * Work.Spaces.HkSq α 6 f) := by ring
    _ ≤ Cx * T := mul_le_mul_of_nonneg_left hT hCxpos.le
    _ ≤ Cx * (α ^ (-(4 : ℝ)) * T) := by
        refine mul_le_mul_of_nonneg_left ?_ hCxpos.le
        calc T = 1 * T := by ring
          _ ≤ α ^ (-(4 : ℝ)) * T := mul_le_mul_of_nonneg_right hA hTnn
    _ ≤ (Cx + 4) * (α ^ (-(4 : ℝ)) * T) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.rpow_nonneg hα0.le _) hTnn)
        linarith
    _ = (Cx + 4) * α ^ (-(4 : ℝ)) * T := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
