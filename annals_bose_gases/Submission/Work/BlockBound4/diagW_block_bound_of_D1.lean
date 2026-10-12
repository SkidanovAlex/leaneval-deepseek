import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BlockBound4.D1Input
import Submission.Work.BlockBound4.diagWEnergy_smul
import Submission.Work.BlockBound4.diagW_cS1_pos_chain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# R3b — the `eB`-level FAITHFUL block bound (`thm:smallbox`'s block shape)

The clone of `Work.SmallBoxA0.kinP_block_bound` at the faithful word
`diagWWord s c₀ cgap = cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)`: the
`eB`-infimum of `diagWEnergy` over the corpus's trial space `CSBox (n+1) s`
satisfies FS's tight block shape

    diagWeB n s μ v h c₀ cgap
      ≥ (¼((N̂/s³)−μ)² − ½μ²)·8π(av)s³ − (272π+40)·μ²(av)s³·Γ − (272π+40)·μ(av) ,

`Γ := d4Gamma R0 s K_B μ v`, `N̂ = n+1`.

Three branches per state (as in the template):
1. `cS1 = 0` — the fully excited state: `qZeroArith` + the crude one-body
   bound `qLHSword_chosen_lower` + the `ε_T`-gap term `cgap·n₊ ≥ n₊/(36s²)`;
2. `cS1 > 0`, at least two particles — the chain `diagW_cS1_pos_chain` fed by
   the bundle's D1 rung `DiagWD1BoxData.hD1` (R1's conclusion) and the
   potential-side summary, the `∬w₂`-slack, the `Corr` bound and the regimes;
3. `cS1 > 0`, one particle — the same chain at `m = Bq = Eq = ηq = 0`, where
   `q4PairWord` vanishes (`pairSet 1 = ∅`) and `pDiagForm ≥ 0`.

The rung of this theorem is EXACTLY the field `hD1` of the bundle —
FS's `lm:appbogolubov` at the faithful word — and the module
`diagW_block_bound.lean` discharges it from R1
(`diagW_lm_appbogolubov_explicitC`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BlockBound4

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## Elementary facts -/

/-- At `N ≤ 1` particles the four-body pairing word `q4PairWord` has no pair to
sum over (`pairSet N = ∅`). -/
theorem q4PairWord_eq_zero_of_le_one {N : ℕ} (hN : N ≤ 1) {s : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (Φ : X N → ℝ) :
    q4PairWord (ℓ := s) (v := v) h (Φ := Φ) = 0 := by
  unfold q4PairWord
  rw [show pairSet N = ∅ from by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine hp (Fin.ext ?_)
    have h1 : p.1.val = 0 := by have := p.1.isLt; omega
    have h2 : p.2.val = 0 := by have := p.2.isLt; omega
    omega]
  simp

/-- The faithful word's kinetic part is nonnegative. -/
theorem pDiagForm_nonneg' (s : ℝ) (hs : 0 < s) (F : ℝ → ℝ) (hF : ∀ r, 0 ≤ F r)
    {N : ℕ} (Ψ : X N → ℝ) : 0 ≤ pDiagForm s F Ψ :=
  Work.KinPSuperadd.pDiagForm_nonneg hs F hF Ψ

/-- FS's error shape `Γ` is nonnegative. -/
theorem d4Gamma_nonneg {R0 s K_B μ : ℝ} {v : ℝ³ → ℝ} (hKB : 0 < K_B)
    (hμ : 0 ≤ μ) (hav : 0 ≤ a v) : 0 ≤ d4Gamma R0 s K_B μ v := by
  unfold d4Gamma Work.SmallBoxA0.kinPGamma
  refine add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hKB) 3) ?_)
  exact Real.rpow_nonneg (mul_nonneg hμ (pow_nonneg hav 3)) (1 / 2)

/-! ## The `eB`-level theorem -/

/-- **R3b — the faithful block bound at the `eB` level, conditional on the D1
rung carried by the bundle.** -/
theorem diagW_block_bound_of_D1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : DiagWD1BoxData,
      ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - C * D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
        - C * D.μ * (a D.v)
      ≤ diagWeB D.n D.s D.μ D.v D.h D.c₀ D.cgap := by
  classical
  refine ⟨272 * π + 40, by positivity, ?_⟩
  intro D
  have hav : 0 ≤ a D.v := le_of_lt D.hav
  have hμnn : 0 ≤ D.μ := le_of_lt D.hμ
  have hper : ∀ W : CSBox (D.n + 1) D.s,
      ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
        - (272 * π + 40) * D.μ * (a D.v)
      ≤ (diagWEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
            (W : X (D.n + 1) → ℝ)) /
        (∫ x in abox (D.n + 1) D.s, ((W : X (D.n + 1) → ℝ) x) ^ 2) := by
    intro W
    let Ph : X (D.n + 1) → ℝ := W
    let I : ℝ := ∫ x in abox (D.n + 1) D.s, (Ph x) ^ 2
    have hIpos : 0 < I := by simpa [I, Ph] using W.sq_pos
    have hIne : I ≠ 0 := ne_of_gt hIpos
    let k : ℝ := (Real.sqrt I)⁻¹
    have hk2 : k ^ 2 = I⁻¹ := by
      dsimp [k]
      have hsq : (Real.sqrt I) ^ 2 = I := Real.sq_sqrt (le_of_lt hIpos)
      calc ((Real.sqrt I)⁻¹) ^ 2 = ((Real.sqrt I) ^ 2)⁻¹ := by rw [← inv_pow]
        _ = I⁻¹ := by rw [hsq]
    have hPhc : ContDiff ℝ ∞ Ph := W.contDiff
    have hΨc : ContDiff ℝ ∞ (k • Ph) := hPhc.const_smul k
    have hnorm1 : (∫ x in abox (D.n + 1) D.s, ((k • Ph) x) ^ 2) = 1 := by
      rw [abox_integral_sq_smul]
      rw [hk2]
      field_simp [hIne]
      simp [I]
    have hstate : ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2
            - (1 / 2 : ℝ) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
        - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
        - (272 * π + 40) * D.μ * (a D.v)
        ≤ diagWEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
            (k • Ph) := by
      by_cases hS : 0 < cS1 D.s (k • Ph)
      · have hcorr : 2 * (1 / D.s ^ 3) * Work.SmallBoxA0.CorrWord D.s D.h (k • Ph)
            ≤ (1 / (72 * D.s ^ 2)) * cnPlus D.s (k • Ph) + 36 * π * (a D.v) * D.μ := by
          have hbound := Work.SmallBoxA0.corr_sqrt_bound_all (N := D.n + 1) (s := D.s) (R := D.R0)
            (v := D.v) D.hs D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h D.hRs
            hΨc.continuous hnorm1
          have h := Work.SmallBoxA0.corr_linear_of_sqrt (N := D.n + 1) (s := D.s) (μ := D.μ)
            (CorrC := 32 * π * chiSup ^ 2 * ((((D.n + 1 : ℕ) : ℝ)) + 1)) (v := D.v)
            D.h D.hs hav (by positivity) hΨc.continuous hnorm1 D.hcorrreg hbound
          simpa only [one_div] using h
        by_cases hn : 1 ≤ D.n
        · -- at least two particles: the D1 rung
          set X : ℝ := (((D.n + 1 : ℕ) : ℝ) + 1) * (((D.n + 1 : ℕ) : ℝ)) with hXdef
          have hXnn : 0 ≤ X := by rw [hXdef]; positivity
          have hm2 : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hXnn
          have hQ : -((1 / 2) * (1 + d4Eta D.Ct D.R0 D.s D.c₀ D.v)
                * (g0w0Mass (v := D.v) D.h) * (Real.sqrt X) ^ 2 * (1 / D.s ^ 3))
              - d4Bracket D.Ct D.n D.s D.c₀ D.v
              - d4BogErr D.Ct D.n D.s D.v * cnPlus D.s (k • Ph)
              ≤ pDiagForm D.s (fsKinCoeff D.c₀) (k • Ph)
                + q4PairWord (ℓ := D.s) (v := D.v) D.h (Φ := k • Ph) := by
            have h := D.hD1 D.n hn (k • Ph) hΨc hnorm1
            unfold d4MassCoeff at h
            rw [hm2, hXdef]
            simp only [one_div]
            ring_nf at h ⊢
            exact h
          have heta : -((1 / 2) * d4Eta D.Ct D.R0 D.s D.c₀ D.v * (g0w0Mass (v := D.v) D.h)
                * (Real.sqrt X) ^ 2 * (1 / D.s ^ 3))
              ≥ -(D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
                + D.μ * (a D.v)) := by
            have h := Work.SmallBoxA0.eta_mass_le_mul (N := D.n + 1) (s := D.s) (μ := D.μ)
              (η := d4Eta D.Ct D.R0 D.s D.c₀ D.v)
              (D := g0w0Mass (v := D.v) D.h)
              (G := d4Gamma D.R0 D.s D.K_B D.μ D.v) (a := a D.v)
              D.hs (g0w0Mass_nonneg (v := D.v) (R := D.R0) D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h)
              D.hD D.hη
            rw [hm2, hXdef]
            simp only [one_div]
            ring_nf at h ⊢
            exact h
          have hm : (Real.sqrt X) ^ 2 ≤ ((((D.n + 1 : ℕ) : ℝ)) + 1) ^ 2 := by
            rw [hm2, hXdef]
            have hNn : (0 : ℝ) ≤ (((D.n + 1 : ℕ) : ℝ)) := by positivity
            nlinarith [hNn]
          exact diagW_cS1_pos_chain (ηq := d4Eta D.Ct D.R0 D.s D.c₀ D.v)
            (m := Real.sqrt X)
            (Bq := d4Bracket D.Ct D.n D.s D.c₀ D.v) (Eq := d4BogErr D.Ct D.n D.s D.v)
            D.h D.hs D.hμ D.hR0 D.hKB D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.hRs D.hμs D.hc0
            hΨc hnorm1 D.hwin hS D.hD D.hbox hcorr D.hbracket heta hQ (le_refl _) hm
        · -- one particle: the chain with `m = Bq = Eq = ηq = 0`
          have hn0 : D.n = 0 := by omega
          have hq4 : q4PairWord (ℓ := D.s) (v := D.v) D.h (Φ := k • Ph) = 0 :=
            q4PairWord_eq_zero_of_le_one (N := D.n + 1) (by omega) D.h (k • Ph)
          have hkP : 0 ≤ pDiagForm D.s (fsKinCoeff D.c₀) (k • Ph) :=
            pDiagForm_nonneg' D.s D.hs (fsKinCoeff D.c₀) (fsKinCoeff_nonneg D.c₀) (k • Ph)
          have hG' : 0 ≤ d4Gamma D.R0 D.s D.K_B D.μ D.v :=
            d4Gamma_nonneg (v := D.v) D.hKB hμnn hav
          have hQ : -((1 / 2 : ℝ) * (1 + 0) * (g0w0Mass (v := D.v) D.h) * (0 : ℝ) ^ 2
                * (1 / D.s ^ 3)) - 0 - 0 * cnPlus D.s (k • Ph)
              ≤ pDiagForm D.s (fsKinCoeff D.c₀) (k • Ph)
                + q4PairWord (ℓ := D.s) (v := D.v) D.h (Φ := k • Ph) := by
            rw [hq4]
            have hz : -((1 / 2 : ℝ) * (1 + 0) * (g0w0Mass (v := D.v) D.h) * (0 : ℝ) ^ 2
                * (1 / D.s ^ 3)) = 0 := by ring
            rw [hz]
            linarith [hkP]
          have hm : (0 : ℝ) ^ 2 ≤ ((((D.n + 1 : ℕ) : ℝ)) + 1) ^ 2 := by
            have hh : (0 : ℝ) ≤ ((((D.n + 1 : ℕ) : ℝ)) + 1) := by positivity
            nlinarith [hh]
          have heta : -((1 / 2 : ℝ) * (0 : ℝ) * (g0w0Mass (v := D.v) D.h) * (0 : ℝ) ^ 2
                * (1 / D.s ^ 3))
              ≥ -(D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
                + D.μ * (a D.v)) := by
            have hz : -((1 / 2 : ℝ) * (0 : ℝ) * (g0w0Mass (v := D.v) D.h) * (0 : ℝ) ^ 2
                * (1 / D.s ^ 3)) = 0 := by ring
            rw [hz]
            have hnn' : 0 ≤ D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
                + D.μ * (a D.v) := by
              have h1 : (0 : ℝ) ≤ D.μ ^ 2 := sq_nonneg D.μ
              have h2 : (0 : ℝ) ≤ D.s ^ 3 := pow_nonneg (le_of_lt D.hs) 3
              exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 hav) h2) hG')
                (mul_nonneg hμnn hav)
            linarith [hnn']
          have hbr : (0 : ℝ) ≤ (88 * π + 39) * (a D.v) * D.μ := by
            have h := mul_nonneg (mul_nonneg (by nlinarith [Real.pi_pos] : (0 : ℝ) ≤ 88 * π + 39) hav) hμnn
            linarith [h]
          have hEq : (0 : ℝ) ≤ d4BogErr D.Ct D.n D.s D.v := by
            unfold d4BogErr Work.SmallBoxA0.kinPBogErr
            exact mul_nonneg (mul_nonneg (d4C_nonneg D.Ct) hav)
              (div_nonneg (by positivity) (pow_nonneg (le_of_lt D.hs) 3))
          exact diagW_cS1_pos_chain (n := D.n) (ηq := 0) (m := 0) (Bq := 0) (Eq := 0)
            D.h D.hs D.hμ D.hR0 D.hKB D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.hRs D.hμs D.hc0
            hΨc hnorm1 D.hwin hS D.hD D.hbox hcorr hbr heta hQ hEq hm
      · -- the fully excited state: `cS1 = 0`
        have hz : cS1 D.s (k • Ph) = 0 := le_antisymm (le_of_not_gt hS) cS1_nonneg
        have h1 := cnPlus_add_cS1 (N := D.n + 1) D.hs hΨc.continuous
        rw [hnorm1, mul_one] at h1
        have hcP : cnPlus D.s (k • Ph) = (((D.n + 1 : ℕ) : ℝ)) := by linarith [h1, hz]
        have hqar := Work.SmallBoxA0.qZeroArith (N := D.n + 1) (s := D.s) (μ := D.μ) (a := a D.v) (q := chiSup ^ 2)
          D.hs D.hμ hav (sq_nonneg chiSup) D.hwin D.hchi
        have hqL := qLHSword_chosen_lower (N := D.n + 1) (s := D.s) (R := D.R0) (μ := D.μ) (v := D.v)
          D.hR0 D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.h D.hs D.hRs hμnn hΨc
        rw [hnorm1, mul_one] at hqL
        have hsbox : sboxC (D.n + 1) D.μ D.v
            = D.μ * (((D.n + 1 : ℕ) : ℝ)) * (16 * π * chiSup ^ 2 * (a D.v)) := by
          rw [sboxC]; ring
        rw [hsbox] at hqL
        have hkP : 0 ≤ pDiagForm D.s (fsKinCoeff D.c₀) (k • Ph) :=
          pDiagForm_nonneg' D.s D.hs (fsKinCoeff D.c₀) (fsKinCoeff_nonneg D.c₀) (k • Ph)
        have hG : 0 ≤ d4Gamma D.R0 D.s D.K_B D.μ D.v := d4Gamma_nonneg (v := D.v) D.hKB hμnn hav
        have hNnn : (0 : ℝ) ≤ (((D.n + 1 : ℕ) : ℝ)) := by positivity
        have hcN : (((D.n + 1 : ℕ) : ℝ)) / (36 * D.s ^ 2)
            ≤ D.cgap * (((D.n + 1 : ℕ) : ℝ)) := by
          have hcg : (36 * D.s ^ 2)⁻¹ ≤ D.cgap := by simpa [one_div] using D.hcgap
          rw [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_right hcg hNnn
        have hT : (0 : ℝ) ≤ (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3
            * d4Gamma D.R0 D.s D.K_B D.μ D.v + (272 * π + 40) * D.μ * (a D.v) := by
          have h1 : (0 : ℝ) ≤ D.μ ^ 2 := sq_nonneg D.μ
          have h2 : (0 : ℝ) ≤ D.s ^ 3 := pow_nonneg (le_of_lt D.hs) 3
          have h3 : (0 : ℝ) ≤ D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v :=
            mul_nonneg (mul_nonneg (mul_nonneg h1 hav) h2) hG
          have h4 : (0 : ℝ) ≤ D.μ * (a D.v) := mul_nonneg hμnn hav
          nlinarith [h3, h4, Real.pi_pos]
        rw [diagWEnergy_eq, diagWWord_apply, hcP]
        have hsub : ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2
              - (1 / 2 : ℝ) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
            ≤ D.cgap * cnPlus D.s (k • Ph) + pDiagForm D.s (fsKinCoeff D.c₀) (k • Ph)
              + qLHSword (N := D.n + 1) D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h))
                  (k • Ph) := by
          rw [hcP]
          nlinarith [hqar, hqL, hkP, hcN]
        linarith [hsub, hT]
    have hE : diagWEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
          (k • Ph)
        = diagWEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap Ph / I := by
      have hsmul := diagWEnergy_smul (n := D.n) (s := D.s) (μ := D.μ)
        (w := wPairC D.s D.v) (w1 := wPairC D.s (g0 D.v D.h)) (c₀ := D.c₀) (cgap := D.cgap)
        (Φ := Ph) k
      rw [hsmul, hk2]
      field_simp [hIne]
    calc ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2
            - (1 / 2 : ℝ) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
        - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3 * d4Gamma D.R0 D.s D.K_B D.μ D.v
        - (272 * π + 40) * D.μ * (a D.v)
        ≤ diagWEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
            (k • Ph) := hstate
      _ = diagWEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap Ph / I := hE
      _ = (diagWEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
            (W : X (D.n + 1) → ℝ)) /
          (∫ x in abox (D.n + 1) D.s, ((W : X (D.n + 1) → ℝ) x) ^ 2) := by rfl
  have hne : Nonempty (CSBox (D.n + 1) D.s) := nonempty_CSBox (D.n + 1) D.hs
  rw [diagWeB]
  apply le_ciInf (ι := CSBox (D.n + 1) D.s)
  exact hper

end Work.BlockBound4
