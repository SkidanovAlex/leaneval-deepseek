import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.U_facts
import Submission.Work.BoseFixB1.WB.cs_apply
import Submission.Work.BoseFixB1.WB.cs_regime
import Submission.Work.BoseFixB1.WB.final_arith_exp
import Submission.Work.BoseFixB1.WB.jensen_integrated
import Submission.Work.BoseFixB1.WB.mass_total2
import Submission.Work.BoseFixB1.WB.mass_upper
import Submission.Work.BoseFixB1.WB.pq_split_meas
import Submission.Work.BoseFixB1.WB.sig_eq
import Submission.Work.BoseFixB1.WB.wbW_lower
import Submission.Work.BoseFixB1.WB.window_regime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.windowBridge_holds` — FS `thm:aprioriHLambda` step 4

The particle window: from the a-priori inequality `AprioriHLambdaIneq` (FS
`eq:aprioriRn+`, bounding the remainder `R_Ψ` and the excited count `n₊`) to
`WindowBridge` (`|n − μℓ³| ≤ C·nWindow` for low box states).

The chain is FS's: **Jensen** (`WB.jensen_dens`, `WB.jensen_integrated`) bounds
`∫_{I₋} wmass·F(dens)`, **Cauchy–Schwarz** (`WB.cs_apply`) turns it into a bound
on the signed `u`-moment of the density, the state count is recovered from that
moment by the `U`-identity (`WB.sig_eq`) plus the **`P/Q`-split**
(`WB.pq_split_meas`), and the final `ε`-split (`WB.final_arith_exp`) converts the
result into `|n − μℓ³| ≤ C·μℓ³·K_B^{3/2}K_ℓ(μa³)^{1/4} = C·nWindow`.  The two
kernel facts used are `WB.mass_upper` (`wmass ≤ C(a v)·chiMass`) and
`WB.mass_total2` (`∫_u wmass = 8π(a v)ℓ³`), feeding `WB.wbW_lower` (`W ≥ π a ℓ³`)
and the pointwise bound `WB.U_facts` on FS's `U`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 0. Elementary `rpow` identities used by the two dictionaries -/

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

/-! ## 1. Pure arithmetic: the two `ε`-splits, cleared of denominators -/

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

/-! ## 2. The window constant -/

/-- The explicit window constant produced by the final `ε`-split, as a function
of the a-priori constant `C_A` and the mass constant `C₁`. -/
def wbCfin (C_A C₁ : ℝ) : ℝ :=
  2 + 2 * Real.sqrt (3 * (C_A / Real.pi))
    + 4 * (C₁ * chiSupAbs ^ 2 / Real.pi) * (2 * C_A / bValue) + 2 * C_A / bValue

theorem wbCfin_nonneg {C_A C₁ : ℝ} (hA : 0 ≤ C_A) (h₁ : 0 ≤ C₁) : 0 ≤ wbCfin C_A C₁ := by
  unfold wbCfin
  have hb : 0 < bValue := by norm_num [bValue]
  have hχ : 0 ≤ chiSupAbs ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (C₁ * chiSupAbs ^ 2 / Real.pi) :=
    div_nonneg (mul_nonneg h₁ hχ) (le_of_lt Real.pi_pos)
  have h4 : 0 ≤ 4 * (C₁ * chiSupAbs ^ 2 / Real.pi) * (2 * C_A / bValue) :=
    mul_nonneg (mul_nonneg (by norm_num) h2) (div_nonneg (by linarith) (le_of_lt hb))
  have h3 : 0 ≤ 2 * C_A / bValue := div_nonneg (by linarith) (le_of_lt hb)
  have h1 : 0 ≤ 2 + 2 * Real.sqrt (3 * (C_A / Real.pi)) := by
    have := Real.sqrt_nonneg (3 * (C_A / Real.pi))
    linarith
  linarith

/-- `wbSig ≥ 0` (the integrand `wmass·dens` is nonnegative). -/
lemma wbSig_nonneg {v : ℝ³ → ℝ} {h : ScatSol v} {R0 : ℝ} (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0)
    (hR0 : 0 < R0) {μ : ℝ} (hM : 1 ≤ (paramsAt μ (a v)).M) (hℓ : 0 < sideAt μ (a v))
    (hd : 0 < (paramsAt μ (a v)).d) {n : ℕ} (Φ : X n → ℝ) : 0 ≤ wbSig v h μ n Φ := by
  refine integral_nonneg fun u => ?_
  exact mul_nonneg (wbMass_nonneg hv hvrad hv_supp hR0 hM hℓ hd u) (wbDens_nonneg Φ u)

/-! ## 3. The main theorem -/

theorem windowBridge_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    (hA : Work.BoseFixB1.AprioriHLambdaIneq v h J) : Work.BoseFixB1.WindowBridge v h J := by
  obtain ⟨C_A, ε_A, hCA1, hεA, hAineq⟩ := hA
  have hCApos : 0 < C_A := lt_of_lt_of_le one_pos hCA1
  -- the pointwise localised-mass bound
  obtain ⟨C₁₀, hC₁₀, hmassU₀⟩ :=
    WB.mass_upper (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR (M := mValue)
      (by norm_num [Work.BoseBox.mValue])
  set C₁ : ℝ := max C₁₀ 1 with hC₁def
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₁0 : 0 ≤ C₁ := le_of_lt hC₁pos
  -- the regime threshold
  obtain ⟨ε_R, hε_R, hregime⟩ :=
    WB.window_regime (v := v) (R := R) (C₁ := C₁) (C_A := C_A) hav hR hC₁pos hCApos
  refine ⟨wbCfin C_A C₁, min ε_A (min ε_R 1), wbCfin_nonneg (le_of_lt hCApos) hC₁0,
    lt_min hεA (lt_min hε_R one_pos), ?_⟩
  intro μ hAdm hJK n Φ hNB hlow
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
  have htotal_raw := WB.mass_total2 (v := v) (h := h) (R0 := R)
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
  have hWlow := WB.wbW_lower (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ hav hM1 hℓ hd
    hC₁pos hmassU htotal hcomp
  have hWpos : 0 < wbW v h μ := lt_of_lt_of_le (by positivity) hWlow
  -- Jensen, integrated
  have hJi := WB.jensen_integrated (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ hav
    hM1 hℓ hd Φ
  set Cnst : ℝ := C_A * μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
    * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) with hCnstdef
  have hJb : (∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
        wbMass v h μ u * psiWeight 1 μ (wbDens v h μ n (Φ : X n → ℝ) u)) ≤ Cnst := by
    have h1 : RPsi v h μ (Φ : X n → ℝ) ≤ Cnst * normB v μ n (Φ : X n → ℝ) := by
      simpa only [hCnstdef] using (hAineq μ hAdmA hJK n Φ hlow).2.1
    rw [mul_comm] at h1
    exact le_of_mul_le_mul_left (le_trans hJi h1) hNB
  -- the Cauchy–Schwarz step
  have hCS := WB.cs_apply (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ hav hM1 hℓ hd
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
    WB.cs_regime hWpos hμ hCnst0 hs0 hγ0 hβ0 hCS' hbound hsmall
  -- the `U`-facts and the `P/Q` split
  obtain ⟨hUint, hUle⟩ := WB.U_facts (v := v) (h := h) (R0 := R) hv hvrad hv_supp hR hμ
    hM1 hℓ hd hC₁0 hmassU
  obtain ⟨hUmeas, -⟩ := WB.wbU_aemeasurable (v := v) (h := h) (R0 := R) hv_supp hR hM1 hℓ hd
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
  have hpq := WB.pq_split_meas (ε := wbEps v μ) hℓ Φ.contDiff.continuous hεpos
    hUmeas.aemeasurable hUintOn hUnn hUint hUle
  have hsig : wbSig v h μ n (Φ : X n → ℝ)
      = (∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 * ∑ i, wbU v h μ (x i))
        / normB v μ n (Φ : X n → ℝ) :=
    WB.sig_eq (v := v) (h := h) (μ := μ) (n := n) hmassU hmassL Φ
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
      have h1 := (hAineq μ hAdmA hJK n Φ hlow).2.2
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
  have hfinal := WB.final_arith_exp (μ := μ) (ℓ := sideAt μ (a v)) (W := wbW v h μ) (s := s)
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
