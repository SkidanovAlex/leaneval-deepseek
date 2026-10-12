import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1.smallBoxCollectedC_holds
import Submission.Work.BoseFixB1B.kineticHalfAssembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.aprioriFromSliding` — FS `eq:aprioriRn+` from `SlidingB`

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

`Work.BoseFixB1B.slidingB_holds_from_assembly` proves FS `eq:BSsliding2`
(`Work.BoseFixB1.SlidingB`) inside this directory.  This file re-derives the a-priori inequality
`Work.BoseFixB1.AprioriHLambdaIneq` (FS `thm:aprioriHLambda`) from it **and** from the per-box
remainder bound `Work.BoseFixB1.smallBoxCollectedC_holds`, with its own (much simpler) constant
arithmetic — the colleague's `aprioriHLambdaIneq_holds` does the same but goes through
`Work.BoseFixB1.slidingB_holds`.

The arithmetic.  Write `A := 4πμ²(a v)ℓ³`, `κ := K_B³(μ(a v)³)^{1/2}`, `N := ‖Φ‖²`,
`W := wordB`, `I := ∫_u sbWord`, `Q := (b/2ℓ²)⟨n₊⟩`, `R := R_Ψ`.  The two inputs are

* `Q + C_S⁻¹ I ≤ W` (`SlidingB`, with `C_S = C ≥ 1`), i.e. `C_S Q + I ≤ C_S W`;
* `c R ≤ I + A(1 + C_C κ)N` (`smallBoxCollectedC_holds`, `0 < c`);

and the low-state hypothesis is `W ≤ −A(1 − J√(μ(a v)³))N` with `J√(μ(a v)³) ≤ κ`.  Hence

    cR + C_S Q ≤ C_S W + A(1 + C_C κ)N ≤ A N (1 − C_S + C_S J√(μ(a v)³) + C_C κ)
               ≤ A N (C_S κ + C_C κ) = A(C_S + C_C)κN ,

and then `Q ≤ C_S Q ≤ A(C_S+C_C)κN` (as `Q ≥ 0`, `C_S ≥ 1`) and
`R ≤ A(C_S+C_C)κN/c`.  Taking `C := 4π((C_S+C_C)/c + (C_S+C_C) + (1+C_C) + 1)` gives both bounds
in the exact shape of `AprioriHLambdaIneq`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **FS `eq:aprioriRn+`** (the a-priori bounds of `thm:aprioriHLambda`) from the sliding
localisation `Work.BoseFixB1.SlidingB` (proved in this directory) and the per-box remainder bound
`Work.BoseFixB1.smallBoxCollectedC_holds`. -/
theorem aprioriHLambdaIneq_from_slidingB {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    Work.BoseFixB1.AprioriHLambdaIneq v h J := by
  obtain ⟨εS, CS, hCS1, hεS, hS'⟩ :=
    Work.BoseFixB1B.slidingB_holds_from_assembly h hv1 hvrad hR hv_supp hav
  obtain ⟨εC, CC, c, hεC, hCC0, hc0, hC'⟩ :=
    Work.BoseFixB1.smallBoxCollectedC_holds h hv hv1 hvrad hR hv_supp hav hJ
  have hCS0 : 0 ≤ CS := by linarith
  have hCSne : CS ≠ 0 := by linarith
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
  · intro μ hAdm hJK n Φ hlow
    have hμ : 0 < μ := hAdm.1
    have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
    have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
    have hKB0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
      le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
    have hb0 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b :=
      Work.BoseFixB1.paramsAt_b_pos μ (_root_.BoseGases.a v)
    have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos ha 3)
    have hsq0 : 0 ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
    have hN0 : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := Work.BoseFixB1.normB_nonneg _
    have hcn0 : 0 ≤ Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Φ : Submission.BoseGases.X n → ℝ) := Submission.BoseGases.cnPlus_nonneg
    have hAdmS : Work.BoseBoxFix.Adm v εS μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
    have hAdmC : Work.BoseBoxFix.Adm v εC μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    obtain ⟨hRnn, hCapp⟩ := hC' μ hAdmC hJK n Φ hlow
    have hSapp := hS' μ hAdmS n Φ
    -- abbreviations
    set A : ℝ := 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v)
      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 with hA
    set κ : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) with hk
    set N : ℝ := Work.BoseBoxFix.normB v μ n Φ with hN
    set W : ℝ := Work.BoseBoxFix.wordB v h μ n Φ with hW
    set I : ℝ := ∫ u : E3, Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      with hI
    set Q : ℝ := ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
        / (2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 2))
        * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ) with hQ
    set Rr : ℝ := Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) with hRr
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    have hk0 : 0 ≤ κ := by rw [hk]; exact mul_nonneg (pow_nonneg hKB0 3) hsq0
    have hQ0 : 0 ≤ Q := by
      rw [hQ]
      exact mul_nonneg (div_nonneg hb0.le (by positivity)) hcn0
    -- the low-state bound
    have hlow' : W ≤ -(A * (1 - J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) * N := by
      have hh := (Work.BoseFixB1.isLowB_iff (J := J) (μ := μ) ha).mp hlow
      rw [Real.sqrt_eq_rpow] at hh
      simpa only [hW, hN, hA] using hh
    -- the sliding bound, in the multiplied form
    have hslide : Q + (1 / CS) * I ≤ W := by
      simpa only [← hQ, ← hI, ← hW] using hSapp
    have h1 : CS * Q + I ≤ CS * W := by
      have hmul : CS * (Q + (1 / CS) * I) ≤ CS * W := mul_le_mul_of_nonneg_left hslide hCS0
      have heq : CS * (Q + (1 / CS) * I) = CS * Q + I := by
        field_simp
        try ring
      rw [heq] at hmul
      exact hmul
    -- the per-box bound
    have h2 : c * Rr ≤ I + A * (1 + CC * κ) * N := by
      have hid : A * (1 + CC * κ) * N
          = 4 * Real.pi * μ ^ 2 * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
            * (1 + CC * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * N := by rw [hA, hk]; ring
      simpa only [← hI, ← hRr, hid] using hCapp
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
          = -(CS * A * N) + CS * (J * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * (A * N) := by
        ring
      rw [hexp] at h5
      have h7 : c * Rr + CS * Q ≤ CS * W + A * (1 + CC * κ) * N := by linarith [h1, h2]
      have h9 : CS * W ≤ -(CS * A * N) + CS * κ * (A * N) := by linarith [h5, h6']
      have hfac : A * N * (1 - CS) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hA0 hN0) (by linarith)
      have h8 : CS * W + A * (1 + CC * κ) * N ≤ A * (CS + CC) * κ * N := by
        nlinarith [h9, hfac]
      linarith [h7, h8]
    -- the two conclusions
    refine ⟨hRnn, ?_, ?_⟩
    · -- `R_Ψ ≤ C·μ²(a v)ℓ³K_B³(μa³)^{1/2}‖Φ‖²`
      have hAkN : A * (CS + CC) * κ * N
          = 4 * Real.pi * (CS + CC) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by
        rw [hA, hk]; ring
      have hRpart : c * Rr ≤ 4 * Real.pi * (CS + CC) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by
        have hh := hcomb
        rw [hAkN] at hh
        linarith [hh, mul_nonneg hCS0 hQ0]
      have hstep : Rr = (1 / c) * (c * Rr) := by field_simp
      have hRle : Rr ≤ (4 * Real.pi * ((CS + CC) / c)) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by
        rw [hstep]
        calc (1 / c) * (c * Rr)
            ≤ (1 / c) * (4 * Real.pi * (CS + CC) * (μ ^ 2 * (_root_.BoseGases.a v)
                * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N)) :=
              mul_le_mul_of_nonneg_left hRpart (by positivity)
          _ = (4 * Real.pi * ((CS + CC) / c)) * (μ ^ 2 * (_root_.BoseGases.a v)
                * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by ring
      have hCge : 4 * Real.pi * ((CS + CC) / c)
          ≤ 4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1) := by
        have h1 : 0 ≤ (CS + CC) / c := div_nonneg (by linarith) hc0.le
        have h2 : 0 ≤ CS + CC := by linarith
        have h3 : 0 ≤ 1 + CC := by linarith
        nlinarith [Real.pi_pos, h1, h2, h3]
      have hM0 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N := by positivity
      calc Rr ≤ (4 * Real.pi * ((CS + CC) / c)) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := hRle
        _ ≤ (4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1))
              * (μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) :=
              mul_le_mul_of_nonneg_right hCge hM0
        _ = 4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1)
              * μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N := by ring
    · -- `(b/2ℓ²)⟨n₊⟩ ≤ C·μ²(a v)ℓ³K_B³(μa³)^{1/2}‖Φ‖²`
      have hAkN : A * (CS + CC) * κ * N
          = 4 * Real.pi * (CS + CC) * (μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := by
        rw [hA, hk]; ring
      have hQle : Q ≤ CS * Q := by nlinarith [hCS1, hQ0]
      have hM0 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
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
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) := hAkN
        _ ≤ (4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1))
              * (μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N) :=
              mul_le_mul_of_nonneg_right hCge hM0
        _ = 4 * Real.pi * ((CS + CC) / c + (CS + CC) + (1 + CC) + 1)
              * μ ^ 2 * (_root_.BoseGases.a v)
              * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) * N := by ring

end Work.BoseFixB1B
