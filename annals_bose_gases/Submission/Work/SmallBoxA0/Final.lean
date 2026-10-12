import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.pot_sharp_summary
import Submission.Work.SmallBoxSuperadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed-`n` smallbox block bound — the SESSION-285 assembly
(Work.SmallBoxA0, step 4)

**SUPERSEDED (SESSION-286).**  This module's `state_block_bound_of_inputs`
uses the SESSION-285 shape of the Bogoliubov input
(`hBog : ½(1+η)·D·(N̂+1)²/ℓ³ + … ≤ kinWord + q4PairWord`), which is FALSE for
`η ≥ 0` (the constant state has `kinWord = q4PairWord = n₊ = 0`), so its
hypothesis set is empty in the intended regime.  The CORRECTED assembly —
same potential-side inputs, Bogoliubov input with the sharp mass term
NEGATIVE and the kinetic gap `n₊/(36ℓ²)` available — is
`Work.SmallBoxA0.state_block_bound_of_inputs_sharp` in
`Submission/Work/SmallBoxA0/Assembly.lean`, and that is what
`Submission.Work.SmallBoxBlockBound` uses.  This module is kept because
`CorrWord`, `totNCoeff`, `DSquare_arith`, `DSquare_cancellation'` and
`g0w0Mass_le_av` are still part of the closure.

This module performs the last step of the potential-side assembly: from the
proved sharp summary `pot_sharp_summary`, the D-square cancellation
(`cS2 ≥ cS1²−cS1` + `cS1 = N̂−n₊`), the regime `potNCoeff μ (av) ≤ 1/(72ℓ²)` and
the kinetic gap, the per-state block shape follows from TWO explicit inputs:

* `hCorr` — the bound on the `Corr` residue of `q1_w1line_scalar_split`
  (`2ℓ⁻³Corr ≥ −n₊/(72ℓ²) − 36π(av)μ`).  This is the ONE genuinely missing
  analytic ingredient of the corpus's route: `Corr` is bilinear in the
  condensate and excited parts, so this linear-in-`n₊` shape needs the FS
  operator-`√` factorisation of `(n₀/V − μ)`; see the area `README.md`.
* `hBog` — the kinetic + Bogolubov bookkeeping: the kinetic word plus the
  `A₂ = q4PairWord` pairing pays for the Bogolubov mass
  `½(1+η)·D·(N̂+1)²/ℓ³`, for the total `n₊`-coefficient `TNC` of the sharp
  chain AND for the `(av)μ`-budget `272π(av)μ`.  This is exactly the
  conclusion of `SmallBoxD1Final.lm_appbogolubov_pWord_holds` combined with
  the kinetic bridge `kinPWord ≤ kinWord` of the sibling area
  `SmallBoxBridge`, plus the gap absorption
  (`Regime.kinWord_absorbs_potNCoeff`).
* `hη` — the regime relation controlling the Bogolubov loss factor `η`
  (`½η·D·(N̂+1)²/ℓ³ ≤ Cμ²(av)ℓ³Γ + Cμ(av)`); this is FS's
  `eq:appdellsassumption` in the form the error bracket `Γ` needs.

## The two skeletons

`state_block_bound_of_inputs` is `SmallBoxBlockBound.smallbox_state_block_bound`
with the universal constant `C` exposed and the two residual inputs above; the
`eB`-level version is obtained by the normalisation pattern of
`Crude.eB_block_bound_large_Gamma`.  To CLOSE the skeleton unconditionally one
must (a) discharge `hCorr` (the operator-`√` step), (b) discharge `hBog` from
D1 + the bridge, and (c) add the regime fields of `hreg`/`hη` to
`BlockBoxData`/`BlockStateData` — they are NOT implied by the current lists.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The `Corr` residue of `Q3Q4Peel.q1_w1line_scalar_split`:
`Σ_i ∫ (P_iΦ)·f₁(x_i)·(Σ_k Q_k Q_i Φ)`, `f₁ := w1Fibre(wPairC(g₀))`. -/
noncomputable def CorrWord {N : ℕ} (ℓ : ℝ) {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ,
    (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
      (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)

/-- The total `n₊`-coefficient absorbed in the final assembly:
`potNCoeff μ (av) + 72π(av)μ + ℓ⁻²/72`. -/
noncomputable def totNCoeff (ℓ μ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  potNCoeff μ (a v) + 72 * π * (a v) * μ + 1 / (72 * ℓ ^ 2)

/-- **Pure-real D-square cancellation** (the arithmetic core): for
`1 ≤ N̄`, `N̄/ℓ³ ≤ 9μ`, `0 ≤ D ≤ k`, `S₂ ≥ (N̄−P)² − (N̄−P)`, `0 ≤ P`,

    ½ℓ⁻³D·S₂ ≥ ½D(N̄+1)²ℓ⁻³ − 9μk·P − 25μk . -/
lemma DSquare_arith {ℓ μ k D S₂ N P : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ) (hk : 0 ≤ k)
    (hDnn : 0 ≤ D) (hPnn : 0 ≤ P) (hN1 : 1 ≤ N) (hDk : D ≤ k)
    (hwin : N / ℓ ^ 3 ≤ 9 * μ) (hS₂ : (N - P) ^ 2 - (N - P) ≤ S₂) :
    (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * D * S₂
      ≥ (1 / 2 : ℝ) * D * ((N + 1) ^ 2) * (ℓ ^ 3)⁻¹ - (9 * μ * k) * P - 25 * μ * k := by
  have hℓ3 : 0 < ℓ ^ 3 := by positivity
  have hNle : N ≤ 9 * μ * ℓ ^ 3 := (div_le_iff₀ hℓ3).mp hwin
  have hNinv : N * (ℓ ^ 3)⁻¹ ≤ 9 * μ := by
    calc N * (ℓ ^ 3)⁻¹ ≤ (9 * μ * ℓ ^ 3) * (ℓ ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right hNle (by positivity)
      _ = 9 * μ := by field_simp [ne_of_gt hℓ3]
  have hlinv : (ℓ ^ 3)⁻¹ ≤ 9 * μ := by
    calc (ℓ ^ 3)⁻¹ = 1 * (ℓ ^ 3)⁻¹ := by ring
      _ ≤ (9 * μ * ℓ ^ 3) * (ℓ ^ 3)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_trans hN1 hNle) (by positivity)
      _ = 9 * μ := by field_simp [ne_of_gt hℓ3]
  have hcoef : (0 : ℝ) ≤ (1 / 2) * (ℓ ^ 3)⁻¹ * D := by positivity
  have h1 : (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * D * ((N - P) ^ 2 - (N - P))
      ≤ (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * D * S₂ := by
    have h' := mul_le_mul_of_nonneg_left hS₂ hcoef
    linarith [h']
  have hA1 : D * (N * (ℓ ^ 3)⁻¹) ≤ k * (9 * μ) := by
    have h0 : (0 : ℝ) ≤ N * (ℓ ^ 3)⁻¹ := by positivity
    have h2 := mul_le_mul_of_nonneg_right hDk h0
    have h3 := mul_le_mul_of_nonneg_left hNinv hk
    linarith [h2, h3]
  have hA : D * (ℓ ^ 3)⁻¹ * (N * P) ≤ 9 * μ * k * P := by
    have h2 := mul_le_mul_of_nonneg_right hA1 hPnn
    linarith [h2]
  have hB : D * (ℓ ^ 3)⁻¹ * N ≤ 9 * μ * k := by
    have h0 : D * (N * (ℓ ^ 3)⁻¹) = D * (ℓ ^ 3)⁻¹ * N := by ring
    linarith [hA1, h0.symm.le, h0.le]
  have hC : D * (ℓ ^ 3)⁻¹ ≤ 9 * μ * k := by
    have h2 := mul_le_mul_of_nonneg_right hDk (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹)
    have h3 := mul_le_mul_of_nonneg_left hlinv hk
    linarith [h2, h3]
  nlinarith [h1, hA, hB, hC, hPnn, hDnn, hk, hμ, sq_nonneg ((N : ℝ) - P), sq_nonneg P,
    sq_nonneg (N + 1)]

/-- **The D-square cancellation**: the `∬w₂`-slack `½ℓ⁻³D·cS2` dominates the
Bogolubov mass `½D(N̂+1)²/ℓ³` up to `n₊`/`(av)μ`-terms (instance of
`DSquare_arith`). -/
theorem DSquare_cancellation' {N : ℕ} {ℓ μ R : ℝ} {v : ℝ³ → ℝ} (hN : 1 ≤ N)
    (hℓ : 0 < ℓ) (hμ : 0 < μ) (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    (hwin : (N : ℝ) / ℓ ^ 3 ≤ 9 * μ)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * a v) :
    (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 ℓ Φ
      ≥ (1 / 2 : ℝ) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (ℓ ^ 3)⁻¹
        - (72 * π * a v * μ) * cnPlus ℓ Φ - 200 * π * a v * μ := by
  classical
  have hcS2₀ := cS2_ge_sq_sub_self (N := N) (ℓ := ℓ) hℓ hΦc hnorm
  have hS := cS1_eq_nat_sub_cnPlus hℓ hΦc hnorm
  have hcS2 : ((N : ℝ) - cnPlus ℓ Φ) ^ 2 - ((N : ℝ) - cnPlus ℓ Φ) ≤ cS2 ℓ Φ := by
    rw [← hS]
    simpa [sq] using hcS2₀
  have hDnn : 0 ≤ g0w0Mass (v := v) h :=
    g0w0Mass_nonneg (v := v) (R := R) hR hv_nonneg hvrad hv_supp h
  have hPnn : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hann : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have harith := DSquare_arith (ℓ := ℓ) (μ := μ) (k := 8 * π * a v)
    (D := g0w0Mass (v := v) h) (S₂ := cS2 ℓ Φ) (N := (N : ℝ)) (P := cnPlus ℓ Φ)
    hℓ (le_of_lt hμ) (by positivity) hDnn hPnn hN1 hD hwin hcS2
  have hcast : (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 ℓ Φ
      ≥ (1 / 2 : ℝ) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (ℓ ^ 3)⁻¹
        - (9 * μ * (8 * π * a v)) * cnPlus ℓ Φ - 25 * μ * (8 * π * a v) := harith
  have hc1 : (9 * μ * (8 * π * a v)) = 72 * π * a v * μ := by ring
  have hc2 : (25 * μ * (8 * π * a v)) = 200 * π * a v * μ := by ring
  rw [hc1, hc2] at hcast
  exact hcast

/-- **THE FINAL ASSEMBLY (per state).**  From

* the proved sharp summary `pot_sharp_summary`,
* the proved D-square cancellation (`DSquare_cancellation'`),
* the Corr residue bound (`hCorr : 2ℓ⁻³CorrWord ≤ n₊/(72ℓ²) + 36π(av)μ`, the ONE
  missing analytic ingredient — note this is an UPPER bound on `2ℓ⁻³Corr`,
  since `Corr` appears with a MINUS sign in the summary),
* the kinetic + Bogolubov input (`hBog`),
* the Bogolubov loss-factor regime relation (`hη`),
* the gap regime (`hreg`, the condition under which `hBog` is dischargeable),

the per-state block shape of `SmallBoxBlockBound.smallbox_state_block_bound`
holds with the displayed universal constant `C`:

    sboxE(Φ) ≥ (¼(x−μ)² − ½μ²)·8π(av)s³ − C·μ²(av)s³·Γ − C·μ(av) ,

`x := N̂/s³`, `Γ := (R0/s)² + K_B³(μ(av)³)^{1/2}`.

This is the exact reduction of the skeleton to the residuals: discharging
`hCorr` and `hBog` (from D1 + the kinetic bridge) and adding `hreg`/`hη` to
the data bundle closes `smallbox_state_block_bound`; the normalisation
pattern of `Crude.eB_block_bound_large_Gamma` then gives
`smallbox_block_bound`. -/
theorem state_block_bound_of_inputs {N : ℕ} {s μ R0 K_B η C : ℝ} {v : ℝ³ → ℝ}
    (hN : 1 ≤ N) (hs : 0 < s) (hμ : 0 < μ) (hR0 : 0 < R0) (hKB : 0 < K_B)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R0 ≤ s * chiR0)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hwin : (N : ℝ) / s ^ 3 ≤ 9 * μ)
    (hSc1 : 0 < cS1 s Φ)
    (hC : 0 ≤ C)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * a v)
    (hreg : totNCoeff s μ v ≤ 1 / (36 * s ^ 2))
    (hη : (1 / 2) * |η| * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        ≤ C * μ ^ 2 * (a v) * s ^ 3
            * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          + C * μ * (a v))
    (hC36 : 36 * π ≤ C)
    (hCorr : 2 * (s ^ 3)⁻¹ * CorrWord s h Φ
        ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
    (hBog : (1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
          + totNCoeff s μ v * cnPlus s Φ + 272 * π * (a v) * μ
        ≤ kinWord N s Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)) :
    (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
      - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
      - C * μ ^ 2 * (a v) * s ^ 3
          * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      - C * μ * (a v)
    ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  classical
  have hsum := pot_sharp_summary (N := N) (ℓ := s) (μ := μ) hs hμ hv_nonneg hvrad hv_memL1
    hR0 hv_supp h hRs hΦc hnorm hwin hSc1
  have hDsq := DSquare_cancellation' (N := N) (ℓ := s) (μ := μ) (R := R0) (v := v)
    hN hs hμ hR0 hv_nonneg hvrad hv_supp h hΦc hnorm hwin hD
  have hsum' : (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        + (1 / 2 : ℝ) * (s ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 s Φ
        + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
        - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ
        - 2 * (s ^ 3)⁻¹ * CorrWord s h Φ
      ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    simpa [CorrWord] using hsum
  have htot : totNCoeff s μ v
      = potNCoeff μ (a v) + 72 * π * (a v) * μ + 1 / (72 * s ^ 2) := by
    rw [totNCoeff]
  -- (keep `totNCoeff` unexpanded; `hsplit` expands it where needed)
  have hDnn : 0 ≤ g0w0Mass (v := v) h :=
    g0w0Mass_nonneg (v := v) (R := R0) hR0 hv_nonneg hvrad hv_supp h
  have hDsqnn : 0 ≤ (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by positivity
  have heta : (1 / 2) * η * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
      ≥ - (1 / 2) * |η| * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by
    have h1 : -|η| ≤ η := neg_abs_le η
    have h2 : -|η| * ((g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹)
        ≤ η * ((g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹) :=
      mul_le_mul_of_nonneg_right h1 hDsqnn
    linarith [h2]
  rw [show sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ
      = kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ from rfl]
  have hμann : 0 ≤ a v := (av_bounds_weak hR0 hv_nonneg hvrad hv_supp h).1
  have hDD : (0 : ℝ) ≤ (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by
    positivity
  have hA1 : (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        + (1 / 2 : ℝ) * (s ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 s Φ
        + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
        - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ
        - 2 * (s ^ 3)⁻¹ * CorrWord s h Φ
      ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    simpa only [CorrWord] using hsum'
  have hA2 := hBog
  have hA3 := hDsq
  have hA4 : - (2 * (s ^ 3)⁻¹ * CorrWord s h Φ)
      ≥ - ((1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ) := by linarith [hCorr]
  -- the η-decomposition
  have hexp2 : (1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
      = (1 / 2) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        + (1 / 2) * η * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by ring
  have hcomb : ((1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
          - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
          - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ
          - 2 * (s ^ 3)⁻¹ * CorrWord s h Φ)
        + ((1 / 2) * (1 + η) * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
          + totNCoeff s μ v * cnPlus s Φ + 272 * π * (a v) * μ)
      ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ + kinWord N s Φ := by
    have hcS2nn : 0 ≤ cS2 s Φ := cS2_nonneg
    have hDc : (0 : ℝ) ≤ (1 / 2 : ℝ) * (s ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 s Φ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hDnn) hcS2nn
    linarith [hA1, hA2, hDc]
  have _ := hA3
  have hfin : (1 / 4 : ℝ) * (((N : ℝ) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        + (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        + (1 / 2) * η * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
      ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ + kinWord N s Φ := by
    have hcS2nn : 0 ≤ cS2 s Φ := cS2_nonneg
    have hDc : (0 : ℝ) ≤ (g0w0Mass (v := v) h) * cS2 s Φ := mul_nonneg hDnn hcS2nn
    have hsplit : totNCoeff s μ v * cnPlus s Φ
        = potNCoeff μ (a v) * cnPlus s Φ + 72 * π * (a v) * μ * cnPlus s Φ
          + (1 / (72 * s ^ 2)) * cnPlus s Φ := by rw [htot]; ring
    nlinarith [hcomb, hA3, hA4, hexp2, hsplit, hDc, hDD]
  have hstep2 : - (C * μ ^ 2 * (a v) * s ^ 3
          * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * μ * (a v))
      ≤ (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        + (1 / 2) * η * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by
    have heta' : - ((1 / 2) * |η| * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹)
        ≤ (1 / 2) * η * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹ := by
      linarith [heta]
    have hη' : - (C * μ ^ 2 * (a v) * s ^ 3
          * ((R0 / s) ^ 2 + K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * μ * (a v))
        ≤ - ((1 / 2) * |η| * (g0w0Mass (v := v) h) * (((N : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹) := by
      linarith [hη]
    linarith [heta', hη', hDD]
  linarith [hfin, hstep2]


/-- **`g0w0Mass ≤ 8π(av)`** (the `D ≤ 8π(av)` input of the D-square cancellation),
from `chosen_gomega_integral_bounds`. -/
lemma g0w0Mass_le_av {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    g0w0Mass (v := v) h ≤ 8 * π * a v := by
  have hb := (chosen_gomega_integral_bounds (v := v) (R := R) hR hv_nonneg hvrad hv_supp h).2
  dsimp [g0w0Mass, g0]
  exact hb

end Work.SmallBoxA0
