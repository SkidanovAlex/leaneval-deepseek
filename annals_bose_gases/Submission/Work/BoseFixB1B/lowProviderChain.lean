import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1B.lowCountBound
import Submission.Work.BoseFixB1B.perBoxIntegratedLow
import Submission.Work.BoseFixB1B.trimInteriorOfPerBoxFLow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.lowProviderChain` — the CORRECTED chain of
# `Work.BoseFixB1B.lowCountBound`

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

## What is proved here

The frozen node `Work.BoseFixB1B.lowCountBound` is `Work.BoseFixB1B.lowCountBound_of_lowProviders`
below, **modulo the two statements `PerBoxFLow`/`OffGoodCrudeLow` of
`Submission/Work/BoseFixB1B/lowProviderDefs.lean`** — that is, modulo FS `thm:smallbox` for low
states on the good set (`Work.BoseFixB1B.perBoxF_of_branches` + the flat arm) and FS `eq:badset`
on the complement.  The chain is

    lowCountBound  ⟸  lowCountBound_of_windowBridge        (this file, arithmetic)
                   ⟸  aprioriHLambdaIneqLow_of_collected    (this file, FS's arithmetic)
                   ⟸  CollectedLow v h J                    (this file, the collection)
                   ⟸  {PerBoxFLow, OffGoodCrudeLow}         (FS `thm:smallbox` + `eq:badset`)
                   (+)  SlidingB                            (`Work.BoseFixB1B.slidingB_holds_from_assembly`, PROVED)
                   (+)  WindowBridge v h J                  (`Work.BoseFixB1B.windowBridgeLow`)

* `collectedLow_of_providers` — the corrected collected per-box bound, from the two providers.  It
  is the *sound* replacement of `Work.BoseFixB1B.smallBoxCollectedC_of_inputs`, whose provider
  `Work.BoseFixB1.PerBoxF` is required for *all* states and is therefore FALSE (so that file's
  statement is vacuous and must not be consumed); here the provider is required only for low states
  of positive box norm, which is FS's setting (`eq:aprioriPsi`).
* `aprioriHLambdaIneqLow_of_collected` — FS `eq:aprioriRn+` from `SlidingB` (proved) and the
  collected bound, verbatim the arithmetic of `aprioriHLambdaIneq_from_slidingB`.
* `lowCountBound_of_windowBridge` — the frozen conclusion from `WindowBridge v h J`.
* `perBoxFLow_of_branches` — the two providers from the corpus's branch split (thin + gap + flat):
  the single remaining analytic obligation is exactly the FLAT branch for **low** states
  (`Work.BoseFixB1B.flatBranchLowB`).

Everything here is `sorry`-free and rests only on `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The collection arithmetic (verbatim from `Work.BoseFixB1S.collectedUnifOfPerBox`) -/

/-- **The collection arithmetic.**  Given FS's three numeric inputs at `κ = K_B³(μ(a v)³)^{1/2}`
(the `8π`-mass law, the integrated per-box bound with the `½μ²·∬w₁` background, and the trim),
the target's inequality `c·R ≤ I' + A(1 + Cκ)‖Φ‖²` follows with `A = 4πμ²(a v)ℓ³` and
`C := C₂ + (C₁+C₃)/(4π)`. -/
private lemma arith_absorb {a ℓ KB t μ nB I I' R W Cp Cm Ct c : ℝ}
    (hπ : 0 < Real.pi) (hnB : 0 ≤ nB) (hμ : 0 < μ) (ha : 0 ≤ a) (hℓ : 0 ≤ ℓ)
    (hW : W ≤ 8 * Real.pi * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t))
    (hcore : c * R ≤ I + (1 / 2) * μ ^ 2 * W * nB
        + Cp * (μ ^ 2 * a * ℓ ^ 3 * KB ^ 3 * t) * nB)
    (htrim : I ≤ I' + Ct * (μ ^ 2 * a * ℓ ^ 3 * KB ^ 3 * t) * nB) :
    c * R ≤ I' + 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        * (1 + (Cm + (Cp + Ct) / (4 * Real.pi)) * KB ^ 3 * t) * nB := by
  have hf : 0 ≤ (1 / 2) * μ ^ 2 := by positivity
  have h1 : (1 / 2) * μ ^ 2 * W * nB
      ≤ (1 / 2) * μ ^ 2 * (8 * Real.pi * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t)) * nB :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hf) hnB
  have h2 : (1 / 2) * μ ^ 2 * (8 * Real.pi * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t)) * nB
      = 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t) * nB := by ring
  have h5 : 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * (1 + Cm * KB ^ 3 * t) * nB
        + Cp * (μ ^ 2 * a * ℓ ^ 3 * KB ^ 3 * t) * nB
        + Ct * (μ ^ 2 * a * ℓ ^ 3 * KB ^ 3 * t) * nB
      = 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        * (1 + (Cm + (Cp + Ct) / (4 * Real.pi)) * KB ^ 3 * t) * nB := by
    have hπ' : Real.pi ≠ 0 := ne_of_gt hπ
    field_simp
    ring
  linarith [hcore, htrim, h1, h2.le, h5.le]

/-! ## 2. The collected per-box bound from the two low-state providers -/

/-- **FS `thm:smallbox` collected, from the two true providers** (`PerBoxFLow` on the good set and
`OffGoodCrudeLow` off it, both for low states of positive box norm). -/
theorem collectedLow_of_providers {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    (hper : ∃ εw c₁ Cper : ℝ, 0 < εw ∧ 0 < c₁ ∧ 0 ≤ Cper ∧ PerBoxFLow v h R J c₁ Cper εw)
    (hbad : ∃ εf Cbad : ℝ, 0 < εf ∧ 0 ≤ Cbad ∧ OffGoodCrudeLow v h J Cbad εf) :
    CollectedLow v h J := by
  obtain ⟨εw, cw, Cw, hεw, hcw, hCw, hper0⟩ := hper
  obtain ⟨εf, Cf, hεf, hCf, hbad0⟩ := hbad
  -- FS `eq:appw1sliding`: the `I₋`-mass law for the localised one-body kernel
  obtain ⟨εm, Cm, hεm, hCm, hW⟩ :=
    Work.BoseFixB1B.w1MassB_integral_le_holds (v := v) h hv hv1 hvrad hR hv_supp hav
  -- the provider on the interior, from the provider on the good set
  have hperI : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
          0 < normB v μ n (Φ : X n → ℝ) →
          IsLowB v h J μ n Φ →
          ∀ u : E3,
            u ∈ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
            PerBoxF v h R c₁ C μ n Φ u :=
    ⟨εw, cw, Cw, hεw, hcw, hCw, fun μ hAdm hJK n Φ hN hlow u hu =>
      hper0 μ hAdm hJK n Φ hN hlow u
        (Work.SmallBoxSliding.interiorSet_subset_goodSet (Work.BoseFixB1.adm_mu_pos hAdm) hu)⟩
  -- the integrated per-box bound on the interior
  obtain ⟨εp, cp, Cp, hεp, hcp, hcp1, hCp, hcore⟩ :=
    perBoxIntegratedLow (v := v) h hv hv1 hvrad hR hv_supp hav hperI
  -- the trim `∫_{I₋} ≤ ∫_{ℝ³} + cost`
  obtain ⟨εt, Ct, hεt, hCt, htrim⟩ :=
    trimInteriorOfPerBoxFLow (v := v) h hv hv1 hvrad hR hv_supp hav
      (ε₁ := εw) (c₁ := cw) (C₁ := Cw) hεw hcw hCw
      (fun μ hAdm hJK n Φ hN hlow u hu => hper0 μ hAdm hJK n Φ hN hlow u hu)
      (ε₂ := εf) (C₂ := Cf) hεf hCf
      (fun μ hAdm hJK n Φ hN hlow u _hu hu' => hbad0 μ hAdm hJK n Φ hN hlow u hu')
  refine ⟨min εp (min εm εt), Cm + (Cp + Ct) / (4 * Real.pi), cp,
    lt_min hεp (lt_min hεm hεt), ?_, hcp, ?_⟩
  · have hnum : 0 ≤ Cp + Ct := by linarith
    have hdiv : 0 ≤ (Cp + Ct) / (4 * Real.pi) := div_nonneg hnum (by positivity)
    linarith
  · intro μ hAdm hJK n Φ hN hlow
    have hAdmp : Adm v εp μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
    have hAdm₂ : Adm v εm μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    have hAdm₃ : Adm v εt μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
    have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
    have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
    have hℓ : 0 ≤ sideAt μ (_root_.BoseGases.a v) :=
      le_of_lt (Work.BoseFixB1.adm_ell_pos hAdm)
    have hnB : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
    have hM1 : 1 ≤ (paramsAt μ (_root_.BoseGases.a v)).M := by
      rw [Work.BoseFixB1.M_eq_mValue]
      norm_num [Work.BoseBox.mValue]
    have hdn : 0 < (paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
    refine ⟨Work.BoseFixB1.rPsiB_nonneg (v := v) (h := h) (μ := μ)
      (M := (paramsAt μ (_root_.BoseGases.a v)).M) (c := 1)
      (ℓ := sideAt μ (_root_.BoseGases.a v)) (d := (paramsAt μ (_root_.BoseGases.a v)).d)
      (n := n) hv hv1 hvrad hR hv_supp hμ hM1 (by norm_num)
      (Work.BoseFixB1.adm_ell_pos hAdm) hdn (Φ : X n → ℝ), ?_⟩
    have hass := arith_absorb (a := _root_.BoseGases.a v)
      (ℓ := sideAt μ (_root_.BoseGases.a v))
      (KB := (paramsAt μ (_root_.BoseGases.a v)).KB)
      (t := (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
      (c := cp) (Cm := Cm) (Cp := Cp) (Ct := Ct)
      (μ := μ) (nB := normB v μ n (Φ : X n → ℝ))
      Real.pi_pos hnB hμ ha hℓ (hW μ hAdm₂)
      (hcore μ hAdmp hJK n Φ hN hlow) (htrim μ hAdm₃ hJK n Φ hN hlow)
    simpa only [mul_assoc] using hass

/-! ## 3. FS `eq:aprioriRn+` (restricted) from `SlidingB` and the collected bound -/

/-- **FS `eq:aprioriRn+`** for the low-state class: the arithmetic of
`Work.BoseFixB1B.aprioriHLambdaIneq_from_slidingB` run against the *corrected* collected bound
`CollectedLow` (and the PROVED sliding localisation `Work.BoseFixB1B.slidingB_holds_from_assembly`).

Write `A := 4πμ²(a v)ℓ³`, `κ := K_B³(μ(a v)³)^{1/2}`, `N := ‖Φ‖²`, `W := wordB`,
`I := ∫_u sbWord`, `Q := (b/2ℓ²)⟨n₊⟩`, `R := R_Ψ`.  The two inputs are `Q + C_S⁻¹I ≤ W`
(`SlidingB`) and `c R ≤ I + A(1 + C_C κ)N` (`CollectedLow`), and the low-state hypothesis is
`W ≤ −A(1 − J√(μ(a v)³))N` with `J√(μ(a v)³) ≤ κ`. -/
theorem aprioriHLambdaIneqLow_of_collected {v : E3 → ℝ} (h : ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) (hcoll : CollectedLow v h J) :
    AprioriHLambdaIneqLow v h J := by
  obtain ⟨εS, CS, hCS1, hεS, hS'⟩ :=
    Work.BoseFixB1B.slidingB_holds_from_assembly h hv1 hvrad hR hv_supp hav
  obtain ⟨εC, CC, c, hεC, hCC0, hc0, hC'⟩ := hcoll
  have hCS0 : 0 ≤ CS := by linarith
  refine ⟨4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1), min εS (min εC 1),
    ?_, ?_, ?_⟩
  · have h2 : 0 ≤ CS + CC := by linarith
    have h3 : 0 ≤ 1 + CC := by linarith
    have hX1 : 1 ≤ (CS + CC) / c + (CS + CC) + (1 + CC) + 1 := by
      have h1 : 0 ≤ (CS + CC) / c := div_nonneg h2 hc0.le
      linarith
    have hpi1 : 1 ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [hX1, hpi1]
  · exact lt_min hεS (lt_min hεC one_pos)
  · intro μ hAdm hJK n Φ hN hlow
    have hμ : 0 < μ := hAdm.1
    have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
    have hℓ : 0 < sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
    have hKB0 : 0 ≤ (paramsAt μ (_root_.BoseGases.a v)).KB :=
      le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
    have hb0 : 0 < (paramsAt μ (_root_.BoseGases.a v)).b :=
      Work.BoseFixB1.paramsAt_b_pos μ (_root_.BoseGases.a v)
    have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos ha 3)
    have hsq0 : 0 ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
    have hN0 : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
    have hcn0 : 0 ≤ cnPlus (sideAt μ (_root_.BoseGases.a v)) (Φ : X n → ℝ) :=
      Submission.BoseGases.cnPlus_nonneg
    have hAdmS : Adm v εS μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
    have hAdmC : Adm v εC μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    obtain ⟨hRnn, hCapp⟩ := hC' μ hAdmC hJK n Φ hN hlow
    have hSapp := hS' μ hAdmS n Φ
    -- abbreviations
    set A : ℝ := 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v)
      * (sideAt μ (_root_.BoseGases.a v)) ^ 3 with hA
    set κ : ℝ := (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) with hk
    set N : ℝ := normB v μ n (Φ : X n → ℝ) with hNdef
    set W : ℝ := wordB v h μ n (Φ : X n → ℝ) with hWdef
    set I : ℝ := ∫ u : E3, sbWord h μ u (Φ : X n → ℝ) with hI
    set Q : ℝ := ((paramsAt μ (_root_.BoseGases.a v)).b
        / (2 * (sideAt μ (_root_.BoseGases.a v)) ^ 2))
        * cnPlus (sideAt μ (_root_.BoseGases.a v)) (Φ : X n → ℝ) with hQ
    set Rr : ℝ := RPsi v h μ (Φ : X n → ℝ) with hRr
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    have hk0 : 0 ≤ κ := by rw [hk]; exact mul_nonneg (pow_nonneg hKB0 3) hsq0
    have hQ0 : 0 ≤ Q := by
      rw [hQ]
      exact mul_nonneg (div_nonneg hb0.le (by positivity)) hcn0
    -- the low-state bound
    have hlow' : W ≤ -(A * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) * N := by
      have hh := (Work.BoseFixB1.isLowB_iff (J := J) (μ := μ) ha).mp hlow
      rw [Real.sqrt_eq_rpow] at hh
      simpa only [hWdef, hNdef, hA] using hh
    -- the sliding bound, in the multiplied form
    have h1 : CS * Q + I ≤ CS * W := by
      have hmul : CS * (Q + (1 / CS) * I) ≤ CS * W :=
        mul_le_mul_of_nonneg_left (by
          simpa only [← hQ, ← hI, ← hWdef] using hSapp) hCS0
      have heq : CS * (Q + (1 / CS) * I) = CS * Q + I := by
        field_simp
      rw [heq] at hmul
      exact hmul
    -- the per-box collected bound
    have h2 : c * Rr ≤ I + A * (1 + CC * κ) * N := by
      have hid : A * (1 + CC * κ) * N
          = 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v)
            * (sideAt μ (_root_.BoseGases.a v)) ^ 3
            * (1 + CC * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * N := by rw [hA, hk]; ring
      simpa only [← hI, ← hRr, ← hNdef, hid] using hCapp
    -- `J√(μa³) ≤ κ`
    have hJt : J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ≤ κ := by
      rw [hk]
      exact mul_le_mul_of_nonneg_right hJK hsq0
    -- the combined bound
    have hcomb : c * Rr + CS * Q ≤ A * (CS + CC) * κ * N := by
      have h5 : CS * W ≤ CS * (-(A * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3)
          ^ (1 / 2 : ℝ))) * N) := mul_le_mul_of_nonneg_left hlow' hCS0
      have h6 : CS * (J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) ≤ CS * κ :=
        mul_le_mul_of_nonneg_left hJt hCS0
      have h6' : CS * (J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * (A * N)
          ≤ CS * κ * (A * N) := mul_le_mul_of_nonneg_right h6 (mul_nonneg hA0 hN0)
      have h4 : CS * (-(A * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) * N)
          = -(CS * (A * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * N)) := by
        ring
      rw [h4] at h5
      have hexp : -(CS * (A * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * N))
          = -(CS * A * N)
            + CS * (J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * (A * N) := by
        ring
      rw [hexp] at h5
      have h7 : c * Rr + CS * Q ≤ CS * W + A * (1 + CC * κ) * N := by linarith [h1, h2]
      have h9 : CS * W ≤ -(CS * A * N) + CS * κ * (A * N) := by linarith [h5, h6']
      have hfac : A * N * (1 - CS) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hA0 hN0) (by linarith)
      have h8 : CS * W + A * (1 + CC * κ) * N ≤ A * (CS + CC) * κ * N := by
        nlinarith [h9, hfac]
      linarith [h7, h8]
    refine ⟨hRnn, ?_, ?_⟩
    · -- `R_Ψ ≤ C·μ²(a v)ℓ³K_B³(μa³)^{1/2}‖Φ‖²`
      have hAkN : A * (CS + CC) * κ * N
          = 4 * Real.pi * (CS + CC) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by
        rw [hA, hk]; ring
      have hRpart : c * Rr ≤ 4 * Real.pi * (CS + CC) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by
        have hh := hcomb
        rw [hAkN] at hh
        linarith [hh, mul_nonneg hCS0 hQ0]
      have hstep : Rr = (1 / c) * (c * Rr) := by field_simp
      have hRle : Rr ≤ (4 * Real.pi * ((CS + CC) / c)) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by
        rw [hstep]
        calc (1 / c) * (c * Rr)
            ≤ (1 / c) * (4 * Real.pi * (CS + CC) * (μ ^ 2 * (_root_.BoseGases.a v)
                * (sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N)) :=
              mul_le_mul_of_nonneg_left hRpart (by positivity)
          _ = (4 * Real.pi * ((CS + CC) / c)) * (μ ^ 2 * (_root_.BoseGases.a v)
                * (sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by ring
      have hCge : 4 * Real.pi * ((CS + CC) / c)
          ≤ 4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1) := by
        have h1 : 0 ≤ (CS + CC) / c := div_nonneg (by linarith) hc0.le
        have h2 : 0 ≤ CS + CC := by linarith
        have h3 : 0 ≤ 1 + CC := by linarith
        nlinarith [Real.pi_pos, h1, h2, h3]
      have hM0 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N := by positivity
      calc Rr ≤ (4 * Real.pi * ((CS + CC) / c)) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := hRle
        _ ≤ (4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1))
              * (μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) :=
              mul_le_mul_of_nonneg_right hCge hM0
        _ = 4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1)
              * μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N := by ring
    · -- `(b/2ℓ²)⟨n₊⟩ ≤ C·μ²(a v)ℓ³K_B³(μa³)^{1/2}‖Φ‖²`
      have hAkN : A * (CS + CC) * κ * N
          = 4 * Real.pi * (CS + CC) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by
        rw [hA, hk]; ring
      have hQle : Q ≤ CS * Q := by nlinarith [hCS1, hQ0]
      have hM0 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N := by positivity
      have hCge : 4 * Real.pi * (CS + CC)
          ≤ 4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1) := by
        have h1 : 0 ≤ (CS + CC) / c := div_nonneg (by linarith) hc0.le
        have h2 : 0 ≤ CS + CC := by linarith
        have h3 : 0 ≤ 1 + CC := by linarith
        nlinarith [Real.pi_pos, h1, h2, h3]
      calc Q ≤ CS * Q := hQle
        _ ≤ c * Rr + CS * Q := by
              have : 0 ≤ c * Rr := mul_nonneg hc0.le hRnn
              linarith
        _ ≤ A * (CS + CC) * κ * N := hcomb
        _ = 4 * Real.pi * (CS + CC) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := hAkN
        _ ≤ (4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1))
              * (μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) :=
              mul_le_mul_of_nonneg_right hCge hM0
        _ = 4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1)
              * μ ^ 2 * (_root_.BoseGases.a v)
              * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N := by ring

/-! ## 4. The frozen conclusion from the window bridge -/

/-- **The frozen node's conclusion** from the corpus's (proved) window bridge
`Work.BoseFixB1.WindowBridge v h J` and the smallness of the window factor. -/
theorem lowCountBound_of_windowBridge {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    (hJ : Work.UBB.lhyC ≤ J) (hW : Work.BoseFixB1.WindowBridge v h J) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Adm v ε₀ μ →
        J ≤ (paramsAt μ (a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
          0 < normB v μ n (Φ : X n → ℝ) →
          IsLowB v h J μ n Φ →
            (n : ℝ) ≤ C * μ * (sideAt μ (a v)) ^ 3 := by
  obtain ⟨Cw, εw, hCw0, hεw, hWb⟩ := hW
  obtain ⟨εF, hεF, hF⟩ := nWindow_le_half_mu_side_cube (v := v) hav
  refine ⟨min εw (min εF 1), 1 + Cw / 2,
    lt_min hεw (lt_min hεF one_pos), by linarith, ?_⟩
  intro μ hAdm hJK n Φ hpos hlow
  have hμ : 0 < μ := hAdm.1
  have hεw' : min εw (min εF 1) ≤ εw := min_le_left _ _
  have hεF' : min εw (min εF 1) ≤ εF := le_trans (min_le_right _ _) (min_le_left _ _)
  have hAdmW : Adm v εw μ := ⟨hAdm.1, le_trans hAdm.2.1 hεw', hAdm.2.2⟩
  have hwin := hWb μ hAdmW hJK n Φ hpos hlow
  have hfac : nWindow (paramsAt μ (a v)) μ (a v)
      ≤ (1 / 2) * (μ * (sideAt μ (a v)) ^ 3) :=
    hF μ hμ (le_trans hAdm.2.1 hεF')
  have hb2 : Cw * nWindow (paramsAt μ (a v)) μ (a v)
      ≤ Cw * ((1 / 2) * (μ * (sideAt μ (a v)) ^ 3)) :=
    mul_le_mul_of_nonneg_left hfac hCw0
  have hb3 : Cw * ((1 / 2) * (μ * (sideAt μ (a v)) ^ 3))
      = (Cw / 2) * (μ * (sideAt μ (a v)) ^ 3) := by ring
  have hmain : |(n : ℝ) - μ * (sideAt μ (a v)) ^ 3|
      ≤ (Cw / 2) * (μ * (sideAt μ (a v)) ^ 3) :=
    le_trans hwin (le_trans hb2 (le_of_eq hb3))
  have hn : (n : ℝ)
      ≤ μ * (sideAt μ (a v)) ^ 3
        + (Cw / 2) * (μ * (sideAt μ (a v)) ^ 3) := by
    have := (abs_le.mp hmain).2
    linarith
  calc (n : ℝ)
      ≤ μ * (sideAt μ (a v)) ^ 3
        + (Cw / 2) * (μ * (sideAt μ (a v)) ^ 3) := hn
    _ = (1 + Cw / 2) * μ * (sideAt μ (a v)) ^ 3 := by ring

end Work.BoseFixB1B
