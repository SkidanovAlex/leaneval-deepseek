import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.lowCountBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.countWindowUnif_of_aprioriUnif` — the `J`-uniform count window

**Target.**  From the *uniform* a-priori interface `Work.BoseFixB1S.AprioriUnif v h`
(FS `eq:aprioriRn+` at one `(ε₀, C)` shared by every threshold `J ≤ K_B³`) deduce the
particle-count bound

    n ≤ C μ ℓ³        (ℓ = sideAt μ (a v))

for **every** threshold `J ≤ K_B³` of FS `eq:aprioriPsi`, with **one** constant `C`.

## Why the statement is not the on-disk `Work.BoseFixB1B.lowCountBound`

`Work.BoseFixB1B.lowCountBound` states the same bound for a *fixed* `J ≥ lhyC` and obtains it
from `Work.BoseFixB1.WindowBridge v h J`, whose constant is hidden behind an `∃`.  A `J`-indexed
window bridge cannot be composed into the `∀ J` form demanded here: the counting consequence
needs a *single* `C` for all `J ≤ K_B³`, and `IsLowB` is *monotone* in `J`
(`Work.BoseFixB1S.isLowB_mono`), so the worst case is `J = K_B³(μ)` — a `μ`-dependent threshold
that no fixed-`J` statement can absorb.

## The route (both steps proved in this file)

1. **The window bridge, uniformly in `J`** (`Work.BoseFixB1.windowBridgeUnif_holds`, below).
   This is the re-run of `Work.BoseFixB1.windowBridge_holds` at *exposed* constants: that proof
   never uses its hypothesis `lhyC ≤ J` and touches `J` only through the a-priori bounds, whose
   constant (`C_A`) and threshold (`ε_A`) are `J`-free by `AprioriUnif`.  Hence feeding the
   uniform interface yields `|n − μℓ³| ≤ wbCfin C_A C₁ · nWindow` with the *same* `wbCfin C_A C₁`
   for all `J`.  All the analytic work is delegated to the (sorry-free, axiom-clean) lemmas of
   `Submission/Work/BoseFixB1/WB/`, exactly as in `windowBridge_holds`; the body below is that
   proof with `hAineq μ …` replaced by `hAunif J μ …`.
2. **From the window to the count** (`countWindowUnif_of_bridgeHelper`): the window factor
   `K_B^{3/2}K_ℓ(μa³)^{1/4}` is `≤ 1/2` on a diluteness window
   (`Work.BoseFixB1B.nWindow_le_half_mu_side_cube`), so `nWindow ≤ ½μℓ³` and
   `|n − μℓ³| ≤ (C/2)μℓ³` give `n ≤ (1 + C/2)μℓ³`.

The `∃ ε₀ C` of the target is `ε₀ = min εw (min εF 1)`, `C = 1 + Cw/2`, both independent of `J`
and `μ`.  (`AprioriUnif v h` is a hypothesis of the target; the open `sorry` of
`Work.BoseFixB1S.LowCountWindowAllJ` itself is *not* used anywhere below.)
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

/-! ## 0. The private helpers of `windowBridge_holds`, re-stated in this module -/

/-- `(x^{3/2})^2 = x^3` for `x ≥ 0`. -/
private lemma sq_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast (x ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hx]
  norm_num

/-- `(y^{1/4})^2 = y^{1/2}` for `y ≥ 0`. -/
private lemma sq_rpow_quarter {y : ℝ} (hy : 0 ≤ y) :
    (y ^ (1 / 4 : ℝ)) ^ 2 = y ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_natCast (y ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hy]
  norm_num

/-- Upper `ε`-split: from the state count `I = s·(nb·W)` and the split inequality
`I ≤ (1+ε)(W/ℓ³)(N·nb − n₊) + (1+ε⁻¹)KU·n₊`, the normalised form. -/
private lemma split_up_arith {nb ℓ W s ε KU nP I N : ℝ} (hnb : 0 < nb) (hW : 0 < W)
    (hℓ : 0 < ℓ) (hs : s * (nb * W) = I)
    (h : I ≤ (1 + ε) * (W / ℓ ^ 3) * (N * nb - nP) + (1 + ε⁻¹) * KU * nP) :
    s ≤ (1 + ε) * (N - nP / nb) / ℓ ^ 3 + (1 + ε⁻¹) * (KU / W) * (nP / nb) := by
  have hnbW : 0 < nb * W := mul_pos hnb hW
  have hs' : s = I / (nb * W) := (eq_div_iff (ne_of_gt hnbW)).mpr hs
  rw [hs', div_le_iff₀ hnbW]
  have hid : ((1 + ε) * (N - nP / nb) / ℓ ^ 3 + (1 + ε⁻¹) * (KU / W) * (nP / nb)) * (nb * W)
      = (1 + ε) * (W / ℓ ^ 3) * (N * nb - nP) + (1 + ε⁻¹) * KU * nP := by
    field_simp
  rw [hid]
  exact h

/-- Lower `ε`-split: the mirror image of `split_up_arith`. -/
private lemma split_lo_arith {nb ℓ W s ε KU nP I N : ℝ} (hnb : 0 < nb) (hW : 0 < W)
    (hℓ : 0 < ℓ) (hs : s * (nb * W) = I)
    (h : (1 - ε) * (W / ℓ ^ 3) * (N * nb - nP) - (1 + ε⁻¹) * KU * nP ≤ I) :
    (1 - ε) * (N - nP / nb) / ℓ ^ 3 - (1 + ε⁻¹) * (KU / W) * (nP / nb) ≤ s := by
  have hnbW : 0 < nb * W := mul_pos hnb hW
  have hs' : s = I / (nb * W) := (eq_div_iff (ne_of_gt hnbW)).mpr hs
  rw [hs', le_div_iff₀ hnbW]
  have hid : ((1 - ε) * (N - nP / nb) / ℓ ^ 3 - (1 + ε⁻¹) * (KU / W) * (nP / nb)) * (nb * W)
      = (1 - ε) * (W / ℓ ^ 3) * (N * nb - nP) - (1 + ε⁻¹) * KU * nP := by
    field_simp
  rw [hid]
  exact h

/-! ## 1. The particle window, uniformly in the threshold `J`

Same proof as `Work.BoseFixB1.windowBridge_holds`, with the a-priori interface
`AprioriUnif` (a single `(ε₀, C_A)` for all `J ≤ K_B³`) in place of the `J`-indexed
`AprioriHLambdaIneq`, and with the (unused) hypothesis `lhyC ≤ J` dropped.  The output
constant `wbCfin C_A C₁` is therefore independent of `J`. -/

theorem windowBridgeUnif_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hA : Work.BoseFixB1S.AprioriUnif v h) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ (J : ℝ) (μ : ℝ), Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            |(n : ℝ) - μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3|
              ≤ C * Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
                  (_root_.BoseGases.a v) := by
  obtain ⟨C_A, ε_A, hCA1, hεA, hAunif⟩ := hA
  have hCApos : 0 < C_A := lt_of_lt_of_le one_pos hCA1
  -- the pointwise localised-mass bound
  obtain ⟨C₁₀, hC₁₀, hmassU₀⟩ :=
    Work.BoseFixB1.WB.mass_upper (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR (M := mValue)
      (by norm_num [Work.BoseBox.mValue])
  set C₁ : ℝ := max C₁₀ 1 with hC₁def
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₁0 : 0 ≤ C₁ := le_of_lt hC₁pos
  -- the regime threshold
  obtain ⟨ε_R, hε_R, hregime⟩ :=
    Work.BoseFixB1.WB.window_regime (v := v) (R := R) (C₁ := C₁) (C_A := C_A) hav hR hC₁pos hCApos
  refine ⟨wbCfin C_A C₁, min ε_A (min ε_R 1), wbCfin_nonneg (le_of_lt hCApos) hC₁0,
    lt_min hεA (lt_min hε_R one_pos), ?_⟩
  intro J μ hAdm hJK n Φ hNB hlow
  have hAdmA : Adm v ε_A μ := Adm.mono hAdm (min_le_left _ _)
  have hAdmR : Adm v ε_R μ :=
    Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht1 : μ * (a v) ^ 3 ≤ 1 :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hRchiR0, hRd16, hM3, _ht1', hεhalf, hKB, hθ, hcomp⟩ := hregime μ hAdmR
  have hμ : 0 < μ := hAdm.1
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := le_trans (by norm_num : 1 ≤ 3) hM3
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hAdm
  have ha0 : 0 ≤ a v := le_of_lt hav
  have hKBpos : 0 < (paramsAt μ (a v)).KB := paramsAt_KB_pos hAdm
  have ht0 : 0 < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hKB0 : 0 ≤ (paramsAt μ (a v)).KB := le_of_lt hKBpos
  -- the pointwise mass bound at this `μ`
  have hmassU : ∀ u : ℝ³, wbMass v h μ u
      ≤ C₁ * a v * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
    intro u
    have h1 := hmassU₀ hℓ hd hRd16 hRchiR0 u
    calc wbMass v h μ u
        = w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := rfl
      _ ≤ C₁₀ * a v * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := h1
      _ ≤ C₁ * a v * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
          have h2 : C₁₀ * a v ≤ C₁ * a v := mul_le_mul_of_nonneg_right (le_max_left _ _) ha0
          exact mul_le_mul_of_nonneg_right h2 (chiMass_nonneg _ _ _ _)
  have hmassL : ∀ u : ℝ³, 0 ≤ wbMass v h μ u := wbMass_nonneg hv hvrad hv_supp hR hM1 hℓ hd
  -- the total localised mass
  have htotal_raw := Work.BoseFixB1.WB.mass_total2 (v := v) (h := h) (R0 := R)
    (M := (paramsAt μ (a v)).M) hv_supp hR ha0 hM3 hℓ hd hRd16
    (Submission.BoseGases.chiR0_pos) hRchiR0 (fun x hx => chiR0_half x hx)
  have hπC : 0 < 8 * Real.pi * a v * (sideAt μ (a v)) ^ 3 := by positivity
  have htotal : 8 * Real.pi * a v * (sideAt μ (a v)) ^ 3 * (3 / 4)
      ≤ ∫ u : ℝ³, wbMass v h μ u := by
    have h2 : |(∫ u : ℝ³, wbMass v h μ u)
        - 8 * Real.pi * a v * (sideAt μ (a v)) ^ 3|
        ≤ (1 / 4) * (8 * Real.pi * a v * (sideAt μ (a v)) ^ 3) := by
      refine le_trans htotal_raw ?_
      have h4 : Submission.BoseGases.convDevC (paramsAt μ (a v)).M
          * (R / sideAt μ (a v)) ^ 2 ≤ 1 / 4 := hθ
      nlinarith [h4, hπC]
    have h3 := (abs_le.mp h2).1
    linarith
  -- `W` is bounded below
  have hWlow := Work.BoseFixB1.WB.wbW_lower (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ hav hM1 hℓ hd
    hC₁pos hmassU htotal hcomp
  have hWpos : 0 < wbW v h μ := lt_of_lt_of_le (by positivity) hWlow
  -- Jensen, integrated
  have hJi := Work.BoseFixB1.WB.jensen_integrated (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ hav
    hM1 hℓ hd Φ
  set Cnst : ℝ := C_A * μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
    * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) with hCnstdef
  have hJb : (∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
        wbMass v h μ u * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)) ≤ Cnst := by
    have h1 : RPsi v h μ (Φ : X n → ℝ) ≤ Cnst * normB v μ n (Φ : X n → ℝ) := by
      simpa only [hCnstdef, mul_assoc] using (hAunif J μ hAdmA hJK n Φ hlow).2.1
    rw [mul_comm] at h1
    exact le_of_mul_le_mul_left (le_trans hJi h1) hNB
  -- the Cauchy–Schwarz step
  have hCS := Work.BoseFixB1.WB.cs_apply (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ hav hM1 hℓ hd
    hC₁pos hmassU htotal Φ hNB
  set s : ℝ := wbSig v h μ n (Φ : X n → ℝ) / wbW v h μ with hsdef
  have hs0 : 0 ≤ s :=
    div_nonneg (wbSig_nonneg hv hvrad hv_supp hR hM1 hℓ hd _) (le_of_lt hWpos)
  set γ : ℝ := (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ) with hγdef
  have hγ0 : 0 ≤ γ := by rw [hγdef]; positivity
  have hγ2 : γ ^ 2 = (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
    rw [hγdef, mul_pow, sq_rpow_three_halves hKB0, sq_rpow_quarter (le_of_lt ht0)]
  have hsW : wbSig v h μ n (Φ : X n → ℝ) = s * wbW v h μ := by
    rw [hsdef]
    field_simp
  have hCS' : wbW v h μ * |s - μ| ≤ Real.sqrt Cnst
      * Real.sqrt (wbW v h μ * (1 + s / μ)) := by
    have h3 : wbW v h μ + wbSig v h μ n (Φ : X n → ℝ) / μ = wbW v h μ * (1 + s / μ) := by
      rw [hsW]; ring
    have h1 : wbW v h μ * |s - μ| = |wbSig v h μ n (Φ : X n → ℝ) - μ * wbW v h μ| := by
      have h' : |wbSig v h μ n (Φ : X n → ℝ) - μ * wbW v h μ| = wbW v h μ * |s - μ| := by
        rw [hsW, ← sub_mul, abs_mul, abs_of_pos hWpos]
        ring
      exact h'.symm
    rw [h1]
    refine le_trans hCS ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hJb) (Real.sqrt_le_sqrt (le_of_eq h3))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hCnst0 : 0 ≤ Cnst := by
    rw [hCnstdef]
    positivity
  have hbound : Cnst ≤ (C_A / Real.pi) * wbW v h μ * μ ^ 2 * γ ^ 2 := by
    have heq : Cnst = (C_A / Real.pi) * μ ^ 2 * γ ^ 2
        * (Real.pi * a v * (sideAt μ (a v)) ^ 3) := by
      rw [hCnstdef, hγ2]
      field_simp
    rw [heq]
    have hnn : 0 ≤ (C_A / Real.pi) * μ ^ 2 * γ ^ 2 :=
      mul_nonneg (mul_nonneg (div_nonneg (le_of_lt hCApos) (le_of_lt Real.pi_pos))
        (sq_nonneg μ)) (sq_nonneg γ)
    calc (C_A / Real.pi) * μ ^ 2 * γ ^ 2 * (Real.pi * a v * (sideAt μ (a v)) ^ 3)
        ≤ (C_A / Real.pi) * μ ^ 2 * γ ^ 2 * wbW v h μ := mul_le_mul_of_nonneg_left hWlow hnn
      _ = (C_A / Real.pi) * wbW v h μ * μ ^ 2 * γ ^ 2 := by ring
  have hβ0 : 0 ≤ C_A / Real.pi := div_nonneg (le_of_lt hCApos) (le_of_lt Real.pi_pos)
  have hsmall : 3 * (C_A / Real.pi) * γ ^ 2 ≤ 1 := by
    rw [hγ2]
    have h1 : 3 * C_A
        * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) ≤ Real.pi := by
      have h := hKB
      rw [le_div_iff₀ (show (0 : ℝ) < 3 * C_A by linarith)] at h
      calc 3 * C_A * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          = ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) * (3 * C_A) := by ring
        _ ≤ Real.pi := h
    have h2 : 3 * (C_A / Real.pi)
        * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        = (3 * C_A * ((paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)))
          / Real.pi := by
      field_simp
    rw [h2, div_le_iff₀ Real.pi_pos]
    simpa using h1
  have hs : |s - μ| ≤ Real.sqrt (3 * (C_A / Real.pi)) * μ * γ :=
    Work.BoseFixB1.WB.cs_regime hWpos hμ hCnst0 hs0 hγ0 hβ0 hCS' hbound hsmall
  -- the `U`-facts and the `P/Q` split
  obtain ⟨hUint, hUle⟩ := Work.BoseFixB1.WB.U_facts (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ
    hM1 hℓ hd hC₁0 hmassU
  obtain ⟨hUmeas, -⟩ := Work.BoseFixB1.WB.wbU_aemeasurable (v := v) (h := h) (R0 := R) hv_supp hR hM1 hℓ hd
  set KU : ℝ := C₁ * a v * chiSupAbs ^ 2 with hKUdef
  have hKU0 : 0 ≤ KU := by rw [hKUdef]; positivity
  have hUnn : ∀ z : ℝ³, 0 ≤ wbU v h μ z := wbU_nonneg hv hvrad hv_supp hR hM1 hℓ hd
  have hUintOn : IntegrableOn (wbU v h μ) (acube (sideAt μ (a v))) := by
    refine IntegrableOn.of_bound ((acube_compact hℓ).measure_lt_top) hUmeas.restrict KU ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hUnn z, hKU0], hUle z⟩
  have hεpos : 0 < wbEps v μ := by
    rw [wbEps]
    have h1 : 0 < (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hKBpos _
    have h2 : 0 < (paramsAt μ (a v)).Kl := adm_Kl_pos hAdm
    have h3 : 0 < (μ * (a v) ^ 3) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht0 _
    positivity
  have hpq := Work.BoseFixB1.WB.pq_split_meas (ε := wbEps v μ) hℓ Φ.contDiff.continuous hεpos
    hUmeas.aemeasurable hUintOn hUnn hUint hUle
  have hsig : wbSig v h μ n (Φ : X n → ℝ)
      = (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 * ∑ i, wbU v h μ (x i))
        / normB v μ n (Φ : X n → ℝ) :=
    Work.BoseFixB1.WB.sig_eq (v := v) (h := h) (μ := μ) (n := n) hmassU hmassL Φ
  have hpSum := pSum_eq (n := n) (ℓ := sideAt μ (a v)) hℓ Φ.contDiff.continuous
  have hqSum : (∑ i : Fin n, ∫ x in abox n (sideAt μ (a v)), (aQ (sideAt μ (a v)) i
      (Φ : X n → ℝ) x) ^ 2) = cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := qSum_eq _
  have hIeq : s * (normB v μ n (Φ : X n → ℝ) * wbW v h μ)
      = ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 * ∑ i, wbU v h μ (x i) := by
    rw [hsdef, hsig]
    field_simp
  -- the two split inequalities
  have hsplit_up : s ≤ (1 + wbEps v μ) * ((n : ℝ) - cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        / normB v μ n (Φ : X n → ℝ)) / (sideAt μ (a v)) ^ 3
      + (1 + (wbEps v μ)⁻¹) * (KU / wbW v h μ)
          * (cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ)) := by
    have hsp := hpq.1
    rw [hpSum, hqSum] at hsp
    exact split_up_arith (nb := normB v μ n (Φ : X n → ℝ)) (ℓ := sideAt μ (a v))
      (W := wbW v h μ) (s := s) (ε := wbEps v μ) (KU := KU)
      (nP := cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
      (I := ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 * ∑ i, wbU v h μ (x i))
      (N := (n : ℝ)) hNB hWpos hℓ hIeq hsp
  have hsplit_lo : (1 - wbEps v μ) * ((n : ℝ) - cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        / normB v μ n (Φ : X n → ℝ)) / (sideAt μ (a v)) ^ 3
      - (1 + (wbEps v μ)⁻¹) * (KU / wbW v h μ)
          * (cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ)) ≤ s := by
    have hsp := hpq.2
    rw [hpSum, hqSum] at hsp
    exact split_lo_arith (nb := normB v μ n (Φ : X n → ℝ)) (ℓ := sideAt μ (a v))
      (W := wbW v h μ) (s := s) (ε := wbEps v μ) (KU := KU)
      (nP := cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
      (I := ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 * ∑ i, wbU v h μ (x i))
      (N := (n : ℝ)) hNB hWpos hℓ hIeq hsp
  -- the `A₀` cap from the a-priori `n₊`-bound
  have hbpos : 0 < (paramsAt μ (a v)).b := paramsAt_b_pos μ (a v)
  have hKℓ2 : μ * a v * (sideAt μ (a v)) ^ 2 = (paramsAt μ (a v)).Kl ^ 2 :=
    mu_mul_a_mul_ell_sq μ (a v) hμ hav
  have hA0nn : 0 ≤ cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ) :=
    div_nonneg (by
      rw [cnPlus]
      exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _) (le_of_lt hNB)
  have hA0cap : cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ)
      ≤ (2 * C_A / bValue) * μ * (sideAt μ (a v)) ^ 3 * (wbEps v μ) ^ 2 := by
    have hεsq : (wbEps v μ) ^ 2 = (paramsAt μ (a v)).KB ^ 3 * (paramsAt μ (a v)).Kl ^ 2
        * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
      rw [wbEps, mul_pow, mul_pow, sq_rpow_three_halves hKB0, sq_rpow_quarter (le_of_lt ht0)]
    have hcn : (paramsAt μ (a v)).b * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ Cnst * normB v μ n (Φ : X n → ℝ) * (2 * (sideAt μ (a v)) ^ 2) := by
      have h1 := (hAunif J μ hAdmA hJK n Φ hlow).2.2
      rw [div_mul_eq_mul_div,
        div_le_iff₀ (show (0 : ℝ) < 2 * (sideAt μ (a v)) ^ 2 by positivity)] at h1
      linarith [h1]
    have hgoal2 : Cnst * normB v μ n (Φ : X n → ℝ) * (2 * (sideAt μ (a v)) ^ 2)
          / (paramsAt μ (a v)).b
        = (2 * C_A / bValue) * μ * (sideAt μ (a v)) ^ 3 * (wbEps v μ) ^ 2
          * normB v μ n (Φ : X n → ℝ) := by
      rw [hCnstdef, paramsAt_b_eq μ (a v), hεsq, ← hKℓ2]
      field_simp
    have hdiv : cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ Cnst * normB v μ n (Φ : X n → ℝ) * (2 * (sideAt μ (a v)) ^ 2)
          / (paramsAt μ (a v)).b := by
      rw [le_div_iff₀ hbpos]
      calc cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) * (paramsAt μ (a v)).b
          = (paramsAt μ (a v)).b * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by ring
        _ ≤ Cnst * normB v μ n (Φ : X n → ℝ) * (2 * (sideAt μ (a v)) ^ 2) := hcn
    rw [div_le_iff₀ hNB, ← hgoal2]
    exact hdiv
  -- the `KU/W` bound
  have hKUW : KU / wbW v h μ ≤ (C₁ * chiSupAbs ^ 2 / Real.pi) / (sideAt μ (a v)) ^ 3 := by
    rw [div_le_div_iff₀ hWpos (pow_pos hℓ 3)]
    have hc : 0 ≤ C₁ * chiSupAbs ^ 2 / Real.pi :=
      div_nonneg (mul_nonneg hC₁0 (sq_nonneg _)) (le_of_lt Real.pi_pos)
    have hkey : KU * (sideAt μ (a v)) ^ 3
        = (C₁ * chiSupAbs ^ 2 / Real.pi) * (Real.pi * a v * (sideAt μ (a v)) ^ 3) := by
      rw [hKUdef]
      field_simp
    calc KU * (sideAt μ (a v)) ^ 3
        = (C₁ * chiSupAbs ^ 2 / Real.pi) * (Real.pi * a v * (sideAt μ (a v)) ^ 3) := hkey
      _ ≤ (C₁ * chiSupAbs ^ 2 / Real.pi) * wbW v h μ := mul_le_mul_of_nonneg_left hWlow hc
  -- `γ ≤ ε`
  have hγle : γ ≤ wbEps v μ := by
    have hKl1 : 1 ≤ (paramsAt μ (a v)).Kl := one_le_Kl hμ hav ht1
    have hfac : 0 ≤ (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ) :=
      mul_nonneg (Real.rpow_nonneg hKB0 _) (Real.rpow_nonneg (le_of_lt ht0) _)
    rw [hγdef, wbEps]
    calc (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ)
        ≤ (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ)
            * (paramsAt μ (a v)).Kl := by
          simpa using mul_le_mul_of_nonneg_left hKl1 hfac
      _ = (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (paramsAt μ (a v)).Kl
            * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ) := by ring
  -- the final `ε`-split
  have hC₂0 : 0 ≤ C₁ * chiSupAbs ^ 2 / Real.pi :=
    div_nonneg (mul_nonneg hC₁0 (sq_nonneg _)) (le_of_lt Real.pi_pos)
  have hfinal := Work.BoseFixB1.WB.final_arith_exp (μ := μ) (ℓ := sideAt μ (a v)) (W := wbW v h μ) (s := s)
    (C_A := C_A) (ε := wbEps v μ) (γ := γ) (C₁ := Real.sqrt (3 * (C_A / Real.pi)))
    (C₂ := C₁ * chiSupAbs ^ 2 / Real.pi) (KU := KU) (n := n)
    (A₀ := cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) / normB v μ n (Φ : X n → ℝ))
    hμ hℓ hWpos hεpos hεhalf hγ0 hγle (le_of_lt hCApos) hA0nn
    (Real.sqrt_nonneg _) hC₂0 hA0cap hs hKUW
  have hfin := hfinal hsplit_up hsplit_lo
  -- conclusion: `nWindow = wbEps·μℓ³`
  rw [show nWindow (paramsAt μ (a v)) μ (a v) = wbEps v μ * (μ * sideAt μ (a v) ^ 3)
      from nWindow_eq_wbEps,
    show wbCfin C_A C₁ = 2 + 2 * Real.sqrt (3 * (C_A / Real.pi))
      + 4 * (C₁ * chiSupAbs ^ 2 / Real.pi) * (2 * C_A / bValue) + 2 * C_A / bValue from rfl]
  calc |(n : ℝ) - μ * (sideAt μ (a v)) ^ 3|
      ≤ (2 + 2 * Real.sqrt (3 * (C_A / Real.pi))
          + 4 * (C₁ * chiSupAbs ^ 2 / Real.pi) * (2 * C_A / bValue) + 2 * C_A / bValue)
          * μ * (sideAt μ (a v)) ^ 3 * (wbEps v μ) := hfin
    _ = (2 + 2 * Real.sqrt (3 * (C_A / Real.pi))
          + 4 * (C₁ * chiSupAbs ^ 2 / Real.pi) * (2 * C_A / bValue) + 2 * C_A / bValue)
          * (wbEps v μ * (μ * (sideAt μ (a v)) ^ 3)) := by ring


end Work.BoseFixB1

namespace Work.BoseFixB1S

/-! ## 2. From the uniform window to the particle count -/

theorem countWindowUnif_of_bridgeHelper {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} (hav : 0 < _root_.BoseGases.a v)
    (hW : ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ (J : ℝ) (μ : ℝ), Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            |(n : ℝ) - μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3|
              ≤ C * Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
                  (_root_.BoseGases.a v)) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ (J : ℝ), ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
  obtain ⟨Cw, εw, hCw0, hεw, hWb⟩ := hW
  obtain ⟨εF, hεF, hF⟩ := Work.BoseFixB1B.nWindow_le_half_mu_side_cube (v := v) hav
  refine ⟨min εw (min εF 1), 1 + Cw / 2, lt_min hεw (lt_min hεF one_pos),
    by linarith, ?_⟩
  intro J μ hAdm hJK n Φ hpos hlow
  have hμ : 0 < μ := hAdm.1
  have hεw' : min εw (min εF 1) ≤ εw := min_le_left _ _
  have hεF' : min εw (min εF 1) ≤ εF := le_trans (min_le_right _ _) (min_le_left _ _)
  have hAdmW : Work.BoseBoxFix.Adm v εw μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 hεw', hAdm.2.2⟩
  have hwin := hWb J μ hAdmW hJK n Φ hpos hlow
  have hfac : Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
        (_root_.BoseGases.a v)
      ≤ (1 / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) :=
    hF μ hμ (le_trans hAdm.2.1 hεF')
  have hb2 : Cw * Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
        (_root_.BoseGases.a v)
      ≤ Cw * ((1 / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)) :=
    mul_le_mul_of_nonneg_left hfac hCw0
  have hb3 : Cw * ((1 / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3))
      = (Cw / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by ring
  have hmain : |(n : ℝ) - μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3|
      ≤ (Cw / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) :=
    le_trans hwin (le_trans hb2 (le_of_eq hb3))
  have hn : (n : ℝ)
      ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        + (Cw / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
    have := (abs_le.mp hmain).2
    linarith
  calc (n : ℝ)
      ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        + (Cw / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := hn
    _ = (1 + Cw / 2) * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by ring

/-! ## 3. The requested lemma -/

theorem countWindowUnif_of_aprioriUnif {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hA : Work.BoseFixB1S.AprioriUnif v h) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ (J : ℝ), ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
  countWindowUnif_of_bridgeHelper (v := v) (h := h) hav
    (Work.BoseFixB1.windowBridgeUnif_holds h hv hv1 hvrad hR hv_supp hav hA)

end Work.BoseFixB1S
