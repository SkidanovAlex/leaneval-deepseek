import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.EBPerState
import Submission.Work.SmallBoxA0.KinPDefs
import Submission.Work.SmallBoxA0.lm_appbogolubov_pWord_explicitC
import Submission.Work.SmallBoxA0.qLHSword_zero_case
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SmallBoxA0.kinP_block_bound` — the `eB`-level `kinPWord` block bound

The `eB`-infimum level of `Submission/Work/SmallBoxA0/kinP_state_block.lean`: the
`kinPWord`-small-box energy `kinPEnergy` (D1's kinetic word, no Bogoliubov residual
field in `KinPBoxData`) satisfies FS's tight block shape

    eB ≥ (¼((N̂/s³)−μ)² − ½μ²)·8π(av)s³ − C·μ²(av)s³·Γ − C·μ(av),   Γ := kinPGamma,

with the universal constant `C := 272π + 40`.

The proof is the standard two-part structure of `SmallBoxBlockBound.smallbox_block_bound`:

* **per state** (an arbitrary `CSBox (n+1) s` element, normalised by the quadratic
  homogeneity `kinPEnergy_smul` of the energy): three branches
  1. `cS1 = 0` — the fully excited state: `qZeroArith` + the crude one-body bound
     (`qLHSword_chosen_lower`) + the `ε_T`-gap term `cgap·n₊ ≥ n₊/(36s²)` (`hcgap`);
  2. `cS1 > 0`, at least two particles — the refined chain `kinP_cS1_pos_chain`
     fed by D1 (`lm_appbogolubov_pWord_explicitC`, the PROVED rung) in its
     pure-pairing form `hQ` (no `cgap` on the kinetic side), the `∬w₂`-slack, the
     linear `Corr` bound and the loss-factor regime `hη`;
  3. `cS1 > 0`, one particle — the same chain at `m = Bq = Eq = ηq = 0`, where
     `q4PairWord` vanishes (`pairSet 1 = ∅`) and `kinPWord ≥ 0`;
* **infimum**: `le_ciInf` over the nonempty `CSBox (n+1) s`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary helpers -/

/-- At `N ≤ 1` particles the four-body pairing word `q4PairWord` has no pair to sum
over (`pairSet N = ∅`). -/
private lemma q4PairWord_eq_zero_of_le_one {N : ℕ} (hN : N ≤ 1) {s : ℝ} {v : ℝ³ → ℝ}
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

/-- The D1 constant `d1C Ct` is nonnegative. -/
private lemma d1C_nonneg (Ct : ℝ) : 0 ≤ d1C Ct := by
  unfold d1C Submission.BoseGases.d1TargetC
  exact le_trans (by positivity : (0 : ℝ) ≤ 6 * (2 * Real.pi) ^ 3) (le_max_left _ _)

/-- The FS error shape `Γ` is nonnegative. -/
private lemma kinPGamma_nonneg {R0 s K_B μ : ℝ} {v : ℝ³ → ℝ} (hKB : 0 < K_B)
    (hμ : 0 ≤ μ) (hav : 0 ≤ a v) :
    0 ≤ kinPGamma R0 s K_B μ v := by
  unfold kinPGamma
  refine add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hKB) 3) ?_)
  exact Real.rpow_nonneg (mul_nonneg hμ (pow_nonneg hav 3)) (1 / 2)

/-! ## The `cS1 > 0` chain -/

/-- **The `cS1 > 0` chain.**  From the potential summary `pot_sharp_summary`, the
`∬w₂`-slack `cs2_mass_slack`, the linear `Corr` bound, and a Bogoliubov-type lower
bound on `kinPWord + q4PairWord` of the pure-pairing shape

    `−½(1+η)·D·m²/s³ − B − E·n₊ ≤ kinPWord + q4PairWord`

(with `m² ≤ (N̂+1)²`, `E ≤ kinPBogErr`), the per-state `kinPWord`-block shape follows.
The mass deficit `½D((N̂+1)² − m²)/s³` is nonnegative and is simply discarded; the
`ε_T`-gap term `cgap·n₊` of the energy pays the potential-side `n₊`-remainder via
`hbox`. -/
private lemma kinP_cS1_pos_chain {n : ℕ} {s μ R0 K_B Ct c0 cgap ηq m Bq Eq : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hμ : 0 < μ) (hR0 : 0 < R0) (hKB : 0 < K_B)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (hRs : R0 ≤ s * chiR0) (hμs : 1 ≤ μ * s ^ 3) (hc0 : 0 < c0)
    {Φ : X (n + 1) → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox (n + 1) s, (Φ x) ^ 2) = 1)
    (hwin : (((n + 1 : ℕ) : ℝ)) / s ^ 3 ≤ 9 * μ)
    (hSc1 : 0 < cS1 s Φ)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * (a v))
    (hbox : totNCoeff s μ v + kinPBogErr Ct n s v ≤ cgap)
    (hCorr : 2 * (s ^ 3)⁻¹ * CorrWord s h Φ ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
    (hbr : Bq ≤ (88 * π + 39) * (a v) * μ)
    (heta : -((1 / 2) * ηq * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹)
        ≥ -(μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v + μ * (a v)))
    (hQ : -((1 / 2) * (1 + ηq) * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹)
        - Bq - Eq * cnPlus s Φ
        ≤ kinPWord s c0 Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ))
    (hEq : Eq ≤ kinPBogErr Ct n s v)
    (hm : m ^ 2 ≤ ((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) :
    ((1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
      - (272 * π + 40) * μ ^ 2 * (a v) * s ^ 3 * kinPGamma R0 s K_B μ v
      - (272 * π + 40) * μ * (a v)
    ≤ kinPEnergy n s μ (wPairC s v) (wPairC s (g0 v h)) c0 cgap Φ := by
  classical
  set G : ℝ := kinPGamma R0 s K_B μ v with hGdef
  rw [hGdef] at heta
  have hav : 0 ≤ a v := (av_bounds_weak hR0 hv_nonneg hvrad hv_supp h).1
  have hDnn : 0 ≤ g0w0Mass (v := v) h :=
    g0w0Mass_nonneg (v := v) (R := R0) hR0 hv_nonneg hvrad hv_supp h
  have hnn : 0 ≤ cnPlus s Φ := cnPlus_nonneg
  have hμnn : 0 ≤ μ := le_of_lt hμ
  have hs3i : (0 : ℝ) ≤ (s ^ 3)⁻¹ := by positivity
  have hGnn : 0 ≤ G := by
    rw [hGdef]; exact kinPGamma_nonneg (s := s) (μ := μ) (v := v) hKB hμnn hav
  -- the potential side
  have hpot : (1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        + (1 / 2) * (s ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 s Φ
        + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
        - potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ
        - 2 * (s ^ 3)⁻¹ * CorrWord s h Φ
      ≤ qLHSword (N := n + 1) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    simpa [CorrWord] using pot_sharp_summary (N := n + 1) (ℓ := s) (μ := μ) hs hμ hv_nonneg hvrad
      hv_memL1 hR0 hv_supp h hRs hΦc.continuous hnorm hwin hSc1
  -- the `∬w₂`-slack
  have hslack := cs2_mass_slack (N := n + 1) (s := s) (μ := μ)
    (D := g0w0Mass (v := v) h) (v := v) hs hμ hDnn hD hav hμs hwin hΦc.continuous hnorm
  -- the linear `Corr` bound
  have hcorr : -((1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
      ≤ -(2 * (s ^ 3)⁻¹ * CorrWord s h Φ) := by linarith [hCorr]
  -- the mass bookkeeping: the deficit `m² → (N̂+1)²` is a nonnegative surplus
  have hsurplus : 0 ≤ (1 / 2) * (g0w0Mass (v := v) h)
      * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2 - m ^ 2) * (s ^ 3)⁻¹ := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hDnn) ?_) hs3i
    linarith [hm]
  have hsplit : (1 / 2) * (g0w0Mass (v := v) h) * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹
      - (1 / 2) * (1 + ηq) * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹
      = (1 / 2) * (g0w0Mass (v := v) h) * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2 - m ^ 2) * (s ^ 3)⁻¹
        - (1 / 2) * ηq * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹ := by ring
  have hmass : (1 / 2) * (g0w0Mass (v := v) h) * (((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) * (s ^ 3)⁻¹
        - (1 / 2) * (1 + ηq) * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹
      ≥ -(μ ^ 2 * (a v) * s ^ 3 * G + μ * (a v)) := by
    rw [hsplit]; linarith [hsurplus, heta]
  -- the `n₊`-coefficient bookkeeping
  have hnf : 0 ≤ (cgap - kinPBogErr Ct n s v) * cnPlus s Φ - (1 / (72 * s ^ 2)) * cnPlus s Φ
      - potNCoeff μ (a v) * cnPlus s Φ - 72 * π * (a v) * μ * cnPlus s Φ := by
    have h0 : potNCoeff μ (a v) + 72 * π * (a v) * μ + 1 / (72 * s ^ 2) + kinPBogErr Ct n s v ≤ cgap := by
      rw [totNCoeff] at hbox
      linarith [hbox]
    nlinarith [h0, hnn]
  have hEeq : 0 ≤ (kinPBogErr Ct n s v - Eq) * cnPlus s Φ := by
    refine mul_nonneg ?_ hnn; linarith [hEq]
  -- arithmetic facts
  have hCpos : (0 : ℝ) ≤ 272 * π + 40 := by positivity
  have hC1 : (1 : ℝ) ≤ 272 * π + 40 := by nlinarith [Real.pi_pos]
  have hX : 0 ≤ μ ^ 2 * (a v) * s ^ 3 * G := by
    have h1 : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
    have h2 : (0 : ℝ) ≤ s ^ 3 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hav) h2) hGnn
  have hY : 0 ≤ μ * (a v) := mul_nonneg hμnn hav
  -- the assembly
  rw [kinPEnergy]
  have key : (1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        - (272 * π + 40) * μ ^ 2 * (a v) * s ^ 3 * G - (272 * π + 40) * μ * (a v)
      ≤ cgap * cnPlus s Φ + kinPWord s c0 Φ
        + qLHSword (N := n + 1) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    nlinarith [hpot, hslack, hcorr, hQ, hbr, hmass, hnf, hEeq, hX, hY, hC1, hDnn, hnn]
  have heq : ((1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
        * (8 * π * (a v) * s ^ 3)
      = (1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3) := by ring
  rw [heq]
  exact key

/-! ## The `eB`-level theorem -/

theorem kinP_block_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : KinPBoxData,
      ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - C * D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v
        - C * D.μ * (a D.v)
      ≤ kinPeB D.n D.s D.μ D.v D.h D.c₀ D.cgap := by
  classical
  refine ⟨272 * π + 40, by positivity, ?_⟩
  intro D
  have hav : 0 ≤ a D.v := le_of_lt D.hav
  have hμnn : 0 ≤ D.μ := le_of_lt D.hμ
  have hspos : 0 < D.s := D.hs
  have hμpos : 0 < D.μ := D.hμ
  have hper : ∀ W : CSBox (D.n + 1) D.s,
      ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2 - (1 / 2 : ℝ) * D.μ ^ 2)
            * (8 * π * (a D.v) * D.s ^ 3)
        - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v
        - (272 * π + 40) * D.μ * (a D.v)
      ≤ (kinPEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
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
    -- the per-state bound at the normalised state `k • Ph`
    have hstate : ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2
            - (1 / 2 : ℝ) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
        - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v
        - (272 * π + 40) * D.μ * (a D.v)
        ≤ kinPEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
            (k • Ph) := by
      by_cases hS : 0 < cS1 D.s (k • Ph)
      · have hcorr : 2 * (D.s ^ 3)⁻¹ * CorrWord D.s D.h (k • Ph)
            ≤ (1 / (72 * D.s ^ 2)) * cnPlus D.s (k • Ph) + 36 * π * (a D.v) * D.μ := by
          have hbound := corr_sqrt_bound_all (N := D.n + 1) (s := D.s) (R := D.R0) (v := D.v)
            D.hs D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h D.hRs hΨc.continuous hnorm1
          exact corr_linear_of_sqrt (N := D.n + 1) (s := D.s) (μ := D.μ)
            (CorrC := 32 * π * chiSup ^ 2 * ((((D.n + 1 : ℕ) : ℝ)) + 1)) (v := D.v)
            D.h D.hs hav (by positivity) hΨc.continuous hnorm1 D.hcorrreg hbound
        by_cases hn : 1 ≤ D.n
        · -- at least two particles: D1 + the chain
          obtain ⟨C1, hC1eq, _hC1nn, hD1⟩ := lm_appbogolubov_pWord_explicitC (N := D.n) (s := D.s)
            (c0 := D.c₀) (Ct := D.Ct) D.hs D.hc0 D.hv_nonneg D.hvrad D.hv_memL1 D.hR0 D.hv_supp
            D.h D.hRs hn D.hav D.hdil D.hWfin D.hCt D.hNewton
          have hD1' := hD1 (k • Ph) hΨc hnorm1
          rw [hC1eq] at hD1'
          have hQ : -((1 / 2) * (1 + kinPeta D.Ct D.R0 D.s D.c₀ D.v)
                * (g0w0Mass (v := D.v) D.h) * ((D.n : ℝ) + 1) ^ 2 * (D.s ^ 3)⁻¹)
              - kinPBracket D.Ct D.n D.s D.c₀ D.v
              - kinPBogErr D.Ct D.n D.s D.v * cnPlus D.s (k • Ph)
              ≤ kinPWord D.s D.c₀ (k • Ph)
                + q4PairWord (ℓ := D.s) (v := D.v) D.h (Φ := k • Ph) := by
            unfold kinPeta kinPBracket kinPBogErr d1C
            rw [div_eq_mul_inv] at hD1'
            ring_nf at hD1' ⊢
            linarith [hD1']
          have hcast : (((D.n + 1 : ℕ) : ℝ)) = (D.n : ℝ) + 1 := by push_cast; ring
          have hm : ((D.n : ℝ) + 1) ^ 2 ≤ ((((D.n + 1 : ℕ) : ℝ)) + 1) ^ 2 := by
            rw [hcast]
            have hnn : (0 : ℝ) ≤ (D.n : ℝ) := by positivity
            nlinarith [hnn]
          have hηsq : (1 / 2) * |kinPeta D.Ct D.R0 D.s D.c₀ D.v| * (8 * π * (a D.v))
                * ((D.n : ℝ) + 1) ^ 2 * (D.s ^ 3)⁻¹
              ≤ D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v
                + D.μ * (a D.v) := by
            have hf : (0 : ℝ) ≤ (1 / 2) * |kinPeta D.Ct D.R0 D.s D.c₀ D.v| * (8 * π * (a D.v)) := by
              positivity
            have h2 := mul_le_mul_of_nonneg_left hm hf
            have h3 := mul_le_mul_of_nonneg_right h2
              (by positivity : (0 : ℝ) ≤ (D.s ^ 3)⁻¹)
            linarith [h3, D.hη]
          have heta : -((1 / 2) * kinPeta D.Ct D.R0 D.s D.c₀ D.v * (g0w0Mass (v := D.v) D.h)
                * ((D.n : ℝ) + 1) ^ 2 * (D.s ^ 3)⁻¹)
              ≥ -(D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v
                + D.μ * (a D.v)) :=
            eta_mass_le (N := D.n) (s := D.s) (μ := D.μ) (η := kinPeta D.Ct D.R0 D.s D.c₀ D.v)
              (D := g0w0Mass (v := D.v) D.h) (G := kinPGamma D.R0 D.s D.K_B D.μ D.v) (a := a D.v)
              D.hs (g0w0Mass_nonneg (v := D.v) (R := D.R0) D.hR0 D.hv_nonneg D.hvrad D.hv_supp D.h)
              D.hD hηsq
          exact kinP_cS1_pos_chain (ηq := kinPeta D.Ct D.R0 D.s D.c₀ D.v) (m := (D.n : ℝ) + 1)
            (Bq := kinPBracket D.Ct D.n D.s D.c₀ D.v) (Eq := kinPBogErr D.Ct D.n D.s D.v)
            D.h D.hs D.hμ D.hR0 D.hKB D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.hRs D.hμs D.hc0
            hΨc hnorm1 D.hwin hS D.hD D.hbox hcorr D.hbracket heta hQ (le_refl _) hm
        · -- one particle: the chain with `m = Bq = Eq = ηq = 0`
          have hn0 : D.n = 0 := by omega
          have hq4 : q4PairWord (ℓ := D.s) (v := D.v) D.h (Φ := k • Ph) = 0 :=
            q4PairWord_eq_zero_of_le_one (N := D.n + 1) (by omega) D.h (k • Ph)
          have hkP : 0 ≤ kinPWord D.s D.c₀ (k • Ph) := kinPWord_nonneg D.hs (k • Ph)
          have hG' : 0 ≤ kinPGamma D.R0 D.s D.K_B D.μ D.v := kinPGamma_nonneg (v := D.v) D.hKB hμnn hav
          have hQ : -((1 / 2 : ℝ) * (1 + 0) * (g0w0Mass (v := D.v) D.h) * (0 : ℝ) ^ 2
                * (D.s ^ 3)⁻¹) - 0 - 0 * cnPlus D.s (k • Ph)
              ≤ kinPWord D.s D.c₀ (k • Ph)
                + q4PairWord (ℓ := D.s) (v := D.v) D.h (Φ := k • Ph) := by
            rw [hq4]; linarith [hkP]
          have hm : (0 : ℝ) ^ 2 ≤ ((((D.n + 1 : ℕ) : ℝ)) + 1) ^ 2 := by
            have hh : (0 : ℝ) ≤ ((((D.n + 1 : ℕ) : ℝ)) + 1) := by positivity
            nlinarith [hh]
          have heta : -((1 / 2 : ℝ) * (0 : ℝ) * (g0w0Mass (v := D.v) D.h) * (0 : ℝ) ^ 2
                * (D.s ^ 3)⁻¹)
              ≥ -(D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v
                + D.μ * (a D.v)) := by
            have hnn' : 0 ≤ D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v
                + D.μ * (a D.v) := by
              have h1 : (0 : ℝ) ≤ D.μ ^ 2 := sq_nonneg D.μ
              have h2 : (0 : ℝ) ≤ D.s ^ 3 := by positivity
              exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 hav) h2) hG')
                (mul_nonneg hμnn hav)
            linarith [hnn']
          have hbr : (0 : ℝ) ≤ (88 * π + 39) * (a D.v) * D.μ := by
            have h := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 88 * π + 39) hav) hμnn
            linarith [h]
          have hEq : (0 : ℝ) ≤ kinPBogErr D.Ct D.n D.s D.v := by
            rw [kinPBogErr]
            exact mul_nonneg (mul_nonneg (d1C_nonneg D.Ct) hav)
              (div_nonneg (by positivity) (by positivity))
          exact kinP_cS1_pos_chain (n := D.n) (ηq := 0) (m := 0) (Bq := 0) (Eq := 0)
            D.h D.hs D.hμ D.hR0 D.hKB D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.hRs D.hμs D.hc0
            hΨc hnorm1 D.hwin hS D.hD D.hbox hcorr hbr heta hQ hEq hm
      · -- the fully excited state: `cS1 = 0`
        have hz : cS1 D.s (k • Ph) = 0 := le_antisymm (le_of_not_gt hS) cS1_nonneg
        have h1 := cnPlus_add_cS1 (N := D.n + 1) D.hs hΨc.continuous
        rw [hnorm1, mul_one] at h1
        have hcP : cnPlus D.s (k • Ph) = (((D.n + 1 : ℕ) : ℝ)) := by linarith [h1, hz]
        have hqar := qZeroArith (N := D.n + 1) (s := D.s) (μ := D.μ) (a := a D.v) (q := chiSup ^ 2)
          D.hs D.hμ hav (sq_nonneg chiSup) D.hwin D.hchi
        have hqL := qLHSword_chosen_lower (N := D.n + 1) (s := D.s) (R := D.R0) (μ := D.μ) (v := D.v)
          D.hR0 D.hv_nonneg D.hvrad D.hv_memL1 D.hv_supp D.h D.hs D.hRs hμnn hΨc
        rw [hnorm1, mul_one] at hqL
        have hsbox : sboxC (D.n + 1) D.μ D.v
            = D.μ * (((D.n + 1 : ℕ) : ℝ)) * (16 * π * chiSup ^ 2 * (a D.v)) := by
          rw [sboxC]; ring
        rw [hsbox] at hqL
        have hkP : 0 ≤ kinPWord D.s D.c₀ (k • Ph) := kinPWord_nonneg D.hs (k • Ph)
        have hG : 0 ≤ kinPGamma D.R0 D.s D.K_B D.μ D.v := kinPGamma_nonneg (v := D.v) D.hKB hμnn hav
        have hNnn : (0 : ℝ) ≤ (((D.n + 1 : ℕ) : ℝ)) := by positivity
        have hcN : (((D.n + 1 : ℕ) : ℝ)) / (36 * D.s ^ 2)
            ≤ D.cgap * (((D.n + 1 : ℕ) : ℝ)) := by
          have hcg : (36 * D.s ^ 2)⁻¹ ≤ D.cgap := by simpa [one_div] using D.hcgap
          rw [div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_right hcg hNnn
        have hT : (0 : ℝ) ≤ (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3
            * kinPGamma D.R0 D.s D.K_B D.μ D.v + (272 * π + 40) * D.μ * (a D.v) := by
          have h1 : (0 : ℝ) ≤ D.μ ^ 2 := sq_nonneg D.μ
          have h2 : (0 : ℝ) ≤ D.s ^ 3 := by positivity
          have h3 : (0 : ℝ) ≤ D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v :=
            mul_nonneg (mul_nonneg (mul_nonneg h1 hav) h2) hG
          have h4 : (0 : ℝ) ≤ D.μ * (a D.v) := mul_nonneg hμnn hav
          nlinarith [h3, h4, Real.pi_pos]
        rw [kinPEnergy, hcP]
        have hsub : ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2
              - (1 / 2 : ℝ) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
            ≤ D.cgap * (((D.n + 1 : ℕ) : ℝ)) + kinPWord D.s D.c₀ (k • Ph)
              + qLHSword (N := D.n + 1) D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h))
                  (k • Ph) := by
          nlinarith [hqar, hqL, hkP, hcN]
        linarith [hsub, hT]
    have hE : kinPEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
          (k • Ph)
        = kinPEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap Ph / I := by
      have hsmul := kinPEnergy_smul (n := D.n) (s := D.s) (μ := D.μ)
        (w := wPairC D.s D.v) (w1 := wPairC D.s (g0 D.v D.h)) (c₀ := D.c₀) (cgap := D.cgap)
        hPhc k
      rw [hsmul, hk2]
      field_simp [hIne]
    calc ((1 / 4 : ℝ) * (((((D.n + 1 : ℕ) : ℝ)) / D.s ^ 3) - D.μ) ^ 2
            - (1 / 2 : ℝ) * D.μ ^ 2) * (8 * π * (a D.v) * D.s ^ 3)
        - (272 * π + 40) * D.μ ^ 2 * (a D.v) * D.s ^ 3 * kinPGamma D.R0 D.s D.K_B D.μ D.v
        - (272 * π + 40) * D.μ * (a D.v)
        ≤ kinPEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
            (k • Ph) := hstate
      _ = kinPEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap Ph / I := hE
      _ = (kinPEnergy D.n D.s D.μ (wPairC D.s D.v) (wPairC D.s (g0 D.v D.h)) D.c₀ D.cgap
            (W : X (D.n + 1) → ℝ)) /
          (∫ x in abox (D.n + 1) D.s, ((W : X (D.n + 1) → ℝ) x) ^ 2) := by rfl
  haveI : Nonempty (CSBox (D.n + 1) D.s) := nonempty_CSBox (D.n + 1) D.hs
  rw [kinPeB]
  apply le_ciInf (ι := CSBox (D.n + 1) D.s)
  exact hper

end Work.SmallBoxA0
