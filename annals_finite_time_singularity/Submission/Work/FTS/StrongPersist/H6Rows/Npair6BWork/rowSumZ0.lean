import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.StarPkg6Fields
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsRLX/Defs.lean` — the interface of the `EpsRHSPLipXProof` development

* `Wp ρ ε u = Pz (Jeps ρ ε u)`: the projected-mollified profile at which the scheme's elliptic
  layer is evaluated.
* `ProfileData α C₀ B ε ρ u`: the bundle of hypotheses the target
  (`Work.FTS.StrongEps.EpsRHSPLipXProof`) assumes on a single admissible datum `u`.

Everything else (the product tools, the term-by-term bounds, the assembly) lives in the sibling
modules of this directory.
-/

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The projected-mollified profile `W_u = Pz (J_ε u)` at which the whole right-hand side of the
projected scheme is evaluated. -/
noncomputable def Wp (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (u : Fn) : Fn :=
  Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)

/-- The modulation block `-μ̄·AK + N_*` of the scheme's right-hand side at a single profile `W`
(all modulation constants evaluated at `W`, `Φ = Φs + E W`). -/
noncomputable def muBlock (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) : Fn := fun z θ =>
  -(Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
      (Work.Construction.N α (Work.Construction.Ftot α W)
        (fun z θ => Φs z θ + E W z θ))) * Work.Construction.AK α z θ
  + Work.Construction.Nstar
      (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
        (Work.Construction.N α (Work.Construction.Ftot α W)
          (fun z θ => Φs z θ + E W z θ)) W)
      (Work.Construction.lamfun
        (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
          (Work.Construction.N α (Work.Construction.Ftot α W)
            (fun z θ => Φs z θ + E W z θ)) W))
      W z θ

/-- **The datum of one admissible profile** of the projected `ε`-scheme: exactly the hypotheses
the target assumes at a single `(τ, u)`. -/
structure ProfileData (α C₀ B ε : ℝ) (ρ : ℝ × ℝ → ℝ) (u : Fn) : Prop where
  /-- open-quadrant smoothness of the datum -/
  smo : Work.FTS.EllipticEst.SmoothOpen u
  /-- honest `ℋ⁶`-membership -/
  hkmem : Work.Spaces.HkMem α 6 u
  /-- the `ℋ⁶`-size bound -/
  hknorm : Work.Spaces.HkNorm α 6 u ≤ B
  /-- the projected-mollified profile is of class `C` -/
  cls : Work.FTS.ClassC.ClassC α (Wp ρ ε u)
  /-- the small-ball bound on the projected-mollified profile -/
  xn : Work.FTS.Nonlin.Xn α (Wp ρ ε u) ≤ C₀ * α ^ 2

end Work.FTS.StrongEps.EpsRLX
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumA1Big =====
section

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
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumZ0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-- `√(a · b²) = √a · |b|` for `a ≥ 0`. -/
private theorem sqrt_mul_sq_eq {a b : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (a * b ^ 2) = Real.sqrt a * |b| := by
  rw [Real.sqrt_mul ha, Real.sqrt_sq_eq_abs]

/-- **The pointwise integral engine (absolute-value form).**  A pointwise domination of `|F|`
by `M · HkIntegrand α 6 g` on the open quadrant gives integrability of `F` against the product
measure and the bound `|∫ F| ≤ M · HkSq α 6 g`. -/
private theorem abs_integral_le_pointwise_prv {α M : ℝ} {F g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmemg : Work.Spaces.HkMem α 6 g) (hM : 0 ≤ M)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) PM)
    (hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ M * Work.Spaces.HkIntegrand α 6 g z θ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2) PM ∧
      |∫ p, F p.1 p.2 ∂PM| ≤ M * Work.Spaces.HkSq α 6 g := by
  obtain ⟨hint, hle⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise hg hmemg hM haesm hpt
  obtain ⟨-, hle2⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise hg hmemg hM haesm.neg
      (fun z θ hz hθ hθ2 => by rw [abs_neg]; exact hpt z θ hz hθ hθ2)
  rw [MeasureTheory.integral_neg] at hle2
  exact ⟨hint, abs_le.mpr ⟨by linarith, hle⟩⟩

/-- **The sup-and-pair engine, with the pointwise domination discharged.**  If the middle
factor `Y` is bounded by `KY` and the two outer factors `X`, `Z` carry the common weight `ρv`
(`≥ 0`) with weighted energies bounded by `AX`, `AZ`, then the triple pairing is integrable
and bounded by `KY · (√AX · √AZ)`. -/
private theorem rowCS {α KY AX AZ : ℝ} {X Y Z ρv : ℝ → ℝ → ℝ}
    (hKY0 : 0 ≤ KY) (hAX0 : 0 ≤ AX) (hAZ0 : 0 ≤ AZ)
    (hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρv z θ)
    (hI1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρv p.1 p.2 * (X p.1 p.2) ^ 2) PM)
    (hv1 : ∫ p, ρv p.1 p.2 * (X p.1 p.2) ^ 2 ∂PM ≤ AX)
    (hI2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρv p.1 p.2 * (Z p.1 p.2) ^ 2) PM)
    (hv2 : ∫ p, ρv p.1 p.2 * (Z p.1 p.2) ^ 2 ∂PM ≤ AZ)
    (hm1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (ρv p.1 p.2 * (X p.1 p.2) ^ 2)) PM)
    (hm2 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (ρv p.1 p.2 * (Z p.1 p.2) ^ 2)) PM)
    (hρm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρv p.1 p.2) PM)
    (hXm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2) PM)
    (hYm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Y p.1 p.2) PM)
    (hZm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Z p.1 p.2) PM)
    (hYb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Y z θ| ≤ KY) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) PM ∧
      |∫ p, ρv p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂PM|
        ≤ KY * (Real.sqrt AX * Real.sqrt AZ) := by
  have hρae : ∀ᵐ p ∂PM, 0 ≤ ρv p.1 p.2 :=
    ae_of_forall_Qd (fun z θ hz hθ hθ2 => hρnn z θ hz hθ hθ2)
  refine rowSummand_core (α := α) (f := fun _ _ => (0 : ℝ)) hKY0 hAX0 hAZ0 hρnn
    hI1 hI2 hv1 hv2 hρae hρae hm1 hm2 hρm hXm hYm hZm ?_
  intro z θ hz hθ hθ2
  have hρg := hρnn z θ hz hθ hθ2
  have hY := hYb z θ hz hθ hθ2
  have hs1 : Real.sqrt (ρv z θ * X z θ ^ 2) = Real.sqrt (ρv z θ) * |X z θ| :=
    sqrt_mul_sq_eq hρg
  have hs2 : Real.sqrt (ρv z θ * Z z θ ^ 2) = Real.sqrt (ρv z θ) * |Z z θ| :=
    sqrt_mul_sq_eq hρg
  have hρsq : Real.sqrt (ρv z θ) * Real.sqrt (ρv z θ) = ρv z θ := Real.mul_self_sqrt hρg
  have hXnn : 0 ≤ |X z θ| := abs_nonneg _
  have hZnn : 0 ≤ |Z z θ| := abs_nonneg _
  calc |ρv z θ * X z θ * Y z θ * Z z θ|
      = ρv z θ * |X z θ| * |Y z θ| * |Z z θ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρg]
    _ ≤ KY * (ρv z θ * |X z θ| * |Z z θ|) := by
        have hkey : ρv z θ * |X z θ| * |Y z θ| * |Z z θ|
            = |Y z θ| * (ρv z θ * |X z θ| * |Z z θ|) := by ring
        rw [hkey]
        exact mul_le_mul_of_nonneg_right hY
          (mul_nonneg (mul_nonneg hρg hXnn) hZnn)
    _ = KY * (Real.sqrt (ρv z θ * X z θ ^ 2) * Real.sqrt (ρv z θ * Z z θ ^ 2)) := by
        rw [hs1, hs2]
        have hkey : (Real.sqrt (ρv z θ) * |X z θ|) * (Real.sqrt (ρv z θ) * |Z z θ|)
            = ρv z θ * |X z θ| * |Z z θ| := by
          rw [show (Real.sqrt (ρv z θ) * |X z θ|) * (Real.sqrt (ρv z θ) * |Z z θ|)
              = (Real.sqrt (ρv z θ) * Real.sqrt (ρv z θ)) * (|X z θ| * |Z z θ|) from by ring,
            hρsq]
          ring
        rw [hkey]

/-- **Leibniz summand with `a = a₁ = 0` (all three factors pure in `θ`), non-flux.**

`X := D_z^{b₁}A`, `Y := D_z^{b+1-b₁} f`, `Z := D_z^b f`, and `ρ ≤ canonW η` (a pure slot: `IsLeafW α 0 ρ`
only allows `leafEta`/`leafOne`).

* `b₁ ≤ 2`: `|D_z^{b₁}A| ≤ Cα^{-1/2}(K0+K4)` (`CoefData.val` for `b₁ = 0`, `sup_dz_le_hk` for `b₁ = 1,2`) and
  `∫ρ|Y||Z| ≤ HkSq α 6 f` (Cauchy–Schwarz at the `η`-weight; `ord Y = b+1-b₁ ≤ 6` and `ord Z = b ≤ 6` by
  the non-flux hypothesis `¬(b₁ = 0 ∧ b = 6)`).
* `3 ≤ b₁ ≤ 4`: `|D_z^b₁A| ≤ C₃α^{-1/2}K6` (`supSix` with `(b,a) = (b₁,0)`, honestly `HkMem α 6 A`), then
  `∫ρ|X||Z| ≤ K4·HkNorm α 6 f` (using `∫ρX² ≤ HkSq α 4 A ≤ K4²` for `b₁ ≤ 4` and `∫ρZ² ≤ HkSq α 6 f`), and
  `|Y| ≤ C₃α^{-1/2}HkNorm α 6 f` (`ord Y = b+1-b₁ ≤ 4`); overall `Cα^{-1/2}K4·HkSq α 6 f`.
* `5 ≤ b₁ ≤ 6`: `∫ρX² ≤ HkSq α 6 A ≤ K6²`, `∫ρZ² ≤ HkSq α 6 f` and `|Y| ≤ C/√(γ-1)·M` pointwise
  (`ord Y = b+1-b₁ ≤ 2`, a pure slot, `DatData.bdd`), giving `Cα^{-1/2}M·K6·HkNorm α 6 f`.

Assemble with `Npair6BWork.rowSummand_core`/`val_le_HkSq`, `canonW_mul_z_le_of_le`, `canonW_le_of_le`,
`leafW_le_canonW_eta`, `leafW_nonneg`, `aesm_mixed`, `aesm_canonW`. -/
theorem rowSumZ0 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (b b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      b ≤ 6 → Work.FTS.TransportS.IsLeafW α 0 ρ → b₁ ≤ b →
      ¬ (b₁ = 0 ∧ b = 6) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.DzIter b₁ A p.1 p.2
          * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
          * Work.Spaces.DzIter b f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
            * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
            * Work.Spaces.DzIter b f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f
               + M * K6 * Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨Csup, hCsup0, hsup⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨C6, hC60, h6sup⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.supSix
  refine ⟨max (max (Csup * Real.sqrt 10) 1) C6, ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_left _ _))
  intro α hα A f K0 K4 K6 K1 M b b₁ ρ hcoef hctmem hctle hdat hb hleaf hb1 hnf
  obtain ⟨hα0, hα1⟩ := hα
  -- ## the hypotheses' consequences
  have hK0 : 0 ≤ K0 := by
    have h := hcoef.val 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hHk6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hHkn6 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hαinv0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hα0 _).le
  have hαinv1 : 1 ≤ α ^ (-(1 / 2 : ℝ)) :=
    Work.FTS.StrongPersist.N6Trans.SixAux.one_le_alpha_rpow_neg_half hα0 hα1
  have hlam' : (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
    simpa only [one_div] using
      Work.FTS.StrongPersist.N6Trans.SixAux.one_div_sqrt_gam_sub_one hα0
  -- ## the leaf weight
  have hρnn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ ρ z θ :=
    leafW_nonneg hleaf
  have hρη : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ :=
    leafW_le_canonW_eta hleaf
  have hρm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2) PM :=
    aesm_leafW hleaf
  have hηgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  -- ## the index bounds
  have hY6 : b + 1 - b₁ ≤ 6 := by
    rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
    · subst h0
      have hb6 : b ≠ 6 := fun h6 => hnf ⟨rfl, h6⟩
      omega
    · omega
  -- ## the constant comparisons
  have hCsupCX : Csup * Real.sqrt 10 ≤ max (Csup * Real.sqrt 10) 1 := le_max_left _ _
  have hone : (1 : ℝ) ≤ max (max (Csup * Real.sqrt 10) 1) C6 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hC0 : (0 : ℝ) ≤ max (max (Csup * Real.sqrt 10) 1) C6 :=
    le_trans (by norm_num) hone
  have hCX1 : (1 : ℝ) ≤ max (Csup * Real.sqrt 10) 1 := le_max_right _ _
  have hCsup10nn : 0 ≤ Csup * Real.sqrt 10 := mul_nonneg hCsup0.le (Real.sqrt_nonneg 10)
  rcases lt_or_ge b₁ 3 with hb13 | hb13
  · -- ## Case 1: `b₁ ≤ 2`
    have hb12 : b₁ ≤ 2 := by omega
    have hXb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.DzIter b₁ A z θ|
          ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
      intro z θ hz hθ hθ2
      rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
      · subst h0
        have h1 : |Work.Spaces.DzIter 0 A z θ| ≤ K0 := by
          simpa only [Work.Spaces.DzIter_zero] using hcoef.val z θ hz hθ hθ2
        have h2 : K0 + K4 ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) := by
          have h3 : (1 : ℝ) ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) := by
            calc (1 : ℝ) = 1 * 1 := by ring
              _ ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) :=
                  mul_le_mul hCX1 hαinv1 (by norm_num)
                    (le_trans (by norm_num) hCX1)
          calc K0 + K4 = 1 * (K0 + K4) := by ring
            _ ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
                mul_le_mul_of_nonneg_right h3 (by linarith)
        exact le_trans h1 (le_trans (le_add_of_nonneg_right hK4) h2)
      · have hsupb := hsup α A hα0 hα1 hcoef.sm hcoef.h4 b₁ hb12 z θ hz hθ hθ2
        calc |Work.Spaces.DzIter b₁ A z θ|
            ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α A := hsupb
          _ = Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α A := by
              rw [div_eq_mul_inv, hlam']; ring
          _ ≤ Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * K4 :=
              mul_le_mul_of_nonneg_left hcoef.n4 (mul_nonneg hCsup10nn hαinv0)
          _ ≤ Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hK0)
                (mul_nonneg hCsup10nn hαinv0)
          _ ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsupCX hαinv0)
                (by linarith)
    have hFm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.DzIter b₁ A p.1 p.2
        * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
        * Work.Spaces.DzIter b f p.1 p.2) PM :=
      (((hρm.mul (aesm_of_smoothOpen (hcoef.sm.DzIter b₁))).mul
        (aesm_of_smoothOpen (hdat.sm.DzIter (b + 1 - b₁)))).mul
        (aesm_of_smoothOpen (hdat.sm.DzIter b)))
    have hMY0 : 0 ≤ max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) :=
      mul_nonneg (mul_nonneg (le_trans (by norm_num) hCX1) hαinv0) (by linarith)
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |ρ z θ * Work.Spaces.DzIter b₁ A z θ
          * Work.Spaces.DzIter (b + 1 - b₁) f z θ * Work.Spaces.DzIter b f z θ|
          ≤ (max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
            * Work.Spaces.HkIntegrand α 6 f z θ := by
      intro z θ hz hθ hθ2
      have hX := hXb z θ hz hθ hθ2
      have hρ0 := hρnn z θ hz hθ hθ2
      have hzI : z ∈ Work.Spaces.Iz := hz.le
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
      have hpair := Work.FTS.StrongPersist.N6Trans.canonW_pair_le6 (α := α) (g := f)
        (q := Work.Spaces.eta) (j := b + 1 - b₁) (i := 0) (b := b) (a := 0)
        Work.Spaces.eta_pos hηgam (fun _ => le_rfl) (fun _ => le_rfl)
        (by omega) (by omega) hzI hθI
      have hpair' : ρ z θ * |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
            * |Work.Spaces.DzIter b f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        refine le_trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (abs_nonneg _))
          (abs_nonneg _)) ?_
        simpa only [Work.Spaces.mixed_zero_right] using hpair
      calc |ρ z θ * Work.Spaces.DzIter b₁ A z θ
            * Work.Spaces.DzIter (b + 1 - b₁) f z θ * Work.Spaces.DzIter b f z θ|
          = |Work.Spaces.DzIter b₁ A z θ| * (ρ z θ
              * |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
              * |Work.Spaces.DzIter b f z θ|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρ0]; ring
        _ ≤ (max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
              * (ρ z θ * |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
                * |Work.Spaces.DzIter b f z θ|) :=
            mul_le_mul_of_nonneg_right hX
              (mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _))
        _ ≤ (max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
              * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_le_mul_of_nonneg_left hpair' hMY0
    obtain ⟨hint, hbd⟩ := abs_integral_le_pointwise_prv hdat.sm hdat.h6 hMY0 hFm hpt
    refine ⟨hint, ?_⟩
    calc |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
            * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
            * Work.Spaces.DzIter b f p.1 p.2 ∂PM|
        ≤ (max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4))
            * Work.Spaces.HkSq α 6 f := hbd
      _ = max (Csup * Real.sqrt 10) 1 * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hαinv0) ?_
          · exact le_max_left _ _
          · exact mul_nonneg (by linarith) hHk6
      _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
            * ((K0 + K4) * Work.Spaces.HkSq α 6 f
              + M * K6 * Work.Spaces.HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg hM0 hK6) hHkn6)) (mul_nonneg hC0 hαinv0)
  · rcases lt_or_ge b₁ 5 with hb15 | hb15
    · -- ## Case 2: `3 ≤ b₁ ≤ 4`
      have hb14 : b₁ ≤ 4 := by omega
      have hj4 : b + 1 - b₁ ≤ 4 := by omega
      have hYb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
            ≤ C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f := by
        intro z θ hz hθ hθ2
        have h := h6sup α f hα0 hα1 hdat.sm hdat.h6 (b + 1 - b₁) 0 (by omega) z θ hz hθ hθ2
        simpa only [Work.Spaces.mixed_zero_right] using h
      have hKY0 : 0 ≤ C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f :=
        mul_nonneg (mul_nonneg hC60.le hαinv0) hHkn6
      have hdom1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * (Work.Spaces.DzIter b₁ A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 A z θ := by
        intro z θ hz hθ hθ2
        refine le_trans (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (sq_nonneg _)) ?_
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := Work.Spaces.eta)
          (g := A) (z := z) (θ := θ) 4 le_rfl hθ hθ2 hb14
      have hmeas1 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.DzIter b₁ A p.1 p.2) ^ 2) PM :=
        hρm.mul ((aesm_of_smoothOpen (hcoef.sm.DzIter b₁)).pow 2)
      have hdom2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * (Work.Spaces.DzIter b f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        intro z θ hz hθ hθ2
        refine le_trans (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (sq_nonneg _)) ?_
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := Work.Spaces.eta)
          (g := f) (z := z) (θ := θ) 6 le_rfl hθ hθ2 hb
      have hmeas2 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.DzIter b f p.1 p.2) ^ 2) PM :=
        hρm.mul ((aesm_of_smoothOpen (hdat.sm.DzIter b)).pow 2)
      obtain ⟨hI1, hv1⟩ := val_le_HkSq (α := α) (k := 4) (f := A) (ρv := ρ)
        (X := fun z θ => Work.Spaces.DzIter b₁ A z θ) hcoef.sm hcoef.h4 hρnn hdom1 hmeas1
      obtain ⟨hI2, hv2⟩ := val_le_HkSq (α := α) (k := 6) (f := f) (ρv := ρ)
        (X := fun z θ => Work.Spaces.DzIter b f z θ) hdat.sm hdat.h6 hρnn hdom2 hmeas2
      obtain ⟨hint, hbd⟩ := rowCS (α := α) (KY := C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
        (AX := Work.Spaces.HkSq α 4 A) (AZ := Work.Spaces.HkSq α 6 f)
        (X := fun z θ => Work.Spaces.DzIter b₁ A z θ)
        (Y := fun z θ => Work.Spaces.DzIter (b + 1 - b₁) f z θ)
        (Z := fun z θ => Work.Spaces.DzIter b f z θ) (ρv := ρ)
        hKY0 (Work.Spaces.HkSq_nonneg α 4 A) hHk6 hρnn hI1 hv1 hI2 hv2
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas1)
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas2)
        hρm (aesm_of_smoothOpen (hcoef.sm.DzIter b₁))
        (aesm_of_smoothOpen (hdat.sm.DzIter (b + 1 - b₁)))
        (aesm_of_smoothOpen (hdat.sm.DzIter b)) hYb
      refine ⟨hint, ?_⟩
      have hN4 : Real.sqrt (Work.Spaces.HkSq α 4 A) ≤ K4 := hcoef.n4
      have hAZsq : Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 f)
          = Work.Spaces.HkSq α 6 f := Real.mul_self_sqrt hHk6
      calc |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
              * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
              * Work.Spaces.DzIter b f p.1 p.2 ∂PM|
          ≤ (C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
              * (Real.sqrt (Work.Spaces.HkSq α 4 A) * Real.sqrt (Work.Spaces.HkSq α 6 f)) := hbd
        _ ≤ (C6 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f)
              * (K4 * Real.sqrt (Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hN4 (Real.sqrt_nonneg _)) hKY0
        _ = C6 * α ^ (-(1 / 2 : ℝ)) * K4
              * (Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 f)) := by
            rw [Work.Spaces.HkNorm]; ring
        _ = C6 * α ^ (-(1 / 2 : ℝ)) * K4 * Work.Spaces.HkSq α 6 f := by rw [hAZsq]
        _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f) := by
            rw [show C6 * α ^ (-(1 / 2 : ℝ)) * K4 * Work.Spaces.HkSq α 6 f
                = C6 * α ^ (-(1 / 2 : ℝ)) * (K4 * Work.Spaces.HkSq α 6 f) by ring]
            refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) hαinv0)
              (mul_le_mul_of_nonneg_right (by linarith) hHk6)
              (mul_nonneg hK4 hHk6) (mul_nonneg hC0 hαinv0)
        _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f
                + M * K6 * Work.Spaces.HkNorm α 6 f) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
              (mul_nonneg (mul_nonneg hM0 hK6) hHkn6)) (mul_nonneg hC0 hαinv0)
    · -- ## Case 3: `5 ≤ b₁`
      have hj2 : b + 1 - b₁ ≤ 2 := by omega
      have hb16 : b₁ ≤ 6 := by omega
      have hYb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
            ≤ Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M := by
        intro z θ hz hθ hθ2
        have h := hsup α f hα0 hα1 hdat.sm
          (HkMem_mono_le hdat.sm (by norm_num) hdat.h6) (b + 1 - b₁) hj2 z θ hz hθ hθ2
        have hcnn : 0 ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) :=
          div_nonneg hCsup0.le (Real.sqrt_nonneg _)
        calc |Work.Spaces.DzIter (b + 1 - b₁) f z θ|
            ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := h
          _ ≤ Csup / Real.sqrt (Work.Spaces.gam α - 1) * M :=
              mul_le_mul_of_nonneg_left hdat.bdd hcnn
          _ = Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M := by
              rw [div_eq_mul_inv, hlam']; ring
      have hKY0 : 0 ≤ Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M :=
        mul_nonneg (mul_nonneg hCsup10nn hαinv0) hM0
      have hdom1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * (Work.Spaces.DzIter b₁ A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 A z θ := by
        intro z θ hz hθ hθ2
        refine le_trans (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (sq_nonneg _)) ?_
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := Work.Spaces.eta)
          (g := A) (z := z) (θ := θ) 6 le_rfl hθ hθ2 hb16
      have hmeas1 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.DzIter b₁ A p.1 p.2) ^ 2) PM :=
        hρm.mul ((aesm_of_smoothOpen (hcoef.sm.DzIter b₁)).pow 2)
      have hdom2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          ρ z θ * (Work.Spaces.DzIter b f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        intro z θ hz hθ hθ2
        refine le_trans (mul_le_mul_of_nonneg_right (hρη z θ hz hθ hθ2) (sq_nonneg _)) ?_
        exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le (α := α) (q := Work.Spaces.eta)
          (g := f) (z := z) (θ := θ) 6 le_rfl hθ hθ2 hb
      have hmeas2 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => ρ p.1 p.2 * (Work.Spaces.DzIter b f p.1 p.2) ^ 2) PM :=
        hρm.mul ((aesm_of_smoothOpen (hdat.sm.DzIter b)).pow 2)
      obtain ⟨hI1, hv1⟩ := val_le_HkSq (α := α) (k := 6) (f := A) (ρv := ρ)
        (X := fun z θ => Work.Spaces.DzIter b₁ A z θ) hcoef.sm hcoef.h6 hρnn hdom1 hmeas1
      obtain ⟨hI2, hv2⟩ := val_le_HkSq (α := α) (k := 6) (f := f) (ρv := ρ)
        (X := fun z θ => Work.Spaces.DzIter b f z θ) hdat.sm hdat.h6 hρnn hdom2 hmeas2
      obtain ⟨hint, hbd⟩ := rowCS (α := α) (KY := Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M)
        (AX := Work.Spaces.HkSq α 6 A) (AZ := Work.Spaces.HkSq α 6 f)
        (X := fun z θ => Work.Spaces.DzIter b₁ A z θ)
        (Y := fun z θ => Work.Spaces.DzIter (b + 1 - b₁) f z θ)
        (Z := fun z θ => Work.Spaces.DzIter b f z θ) (ρv := ρ)
        hKY0 (Work.Spaces.HkSq_nonneg α 6 A) hHk6 hρnn hI1 hv1 hI2 hv2
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas1)
        (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas2)
        hρm (aesm_of_smoothOpen (hcoef.sm.DzIter b₁))
        (aesm_of_smoothOpen (hdat.sm.DzIter (b + 1 - b₁)))
        (aesm_of_smoothOpen (hdat.sm.DzIter b)) hYb
      refine ⟨hint, ?_⟩
      have hN6 : Real.sqrt (Work.Spaces.HkSq α 6 A) ≤ K6 := hcoef.n6
      calc |∫ p, ρ p.1 p.2 * Work.Spaces.DzIter b₁ A p.1 p.2
              * Work.Spaces.DzIter (b + 1 - b₁) f p.1 p.2
              * Work.Spaces.DzIter b f p.1 p.2 ∂PM|
          ≤ (Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M)
              * (Real.sqrt (Work.Spaces.HkSq α 6 A) * Real.sqrt (Work.Spaces.HkSq α 6 f)) := hbd
        _ ≤ (Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M)
              * (K6 * Real.sqrt (Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hN6 (Real.sqrt_nonneg _)) hKY0
        _ = Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
              * (M * K6 * Real.sqrt (Work.Spaces.HkSq α 6 f)) := by
            show Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * M
                * (K6 * Real.sqrt (Work.Spaces.HkSq α 6 f)) = _
            ring
        _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
              * (M * K6 * Work.Spaces.HkNorm α 6 f) := by
            have hle : Csup * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
                ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right
                (le_trans hCsupCX (le_max_left _ _)) hαinv0
            exact mul_le_mul_of_nonneg_right hle
              (mul_nonneg (mul_nonneg hM0 hK6) hHkn6)
        _ ≤ max (max (Csup * Real.sqrt 10) 1) C6 * α ^ (-(1 / 2 : ℝ))
              * ((K0 + K4) * Work.Spaces.HkSq α 6 f
                + M * K6 * Work.Spaces.HkNorm α 6 f) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 hαinv0)
            exact le_add_of_nonneg_left (mul_nonneg (by linarith) hHk6)

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
