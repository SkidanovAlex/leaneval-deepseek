import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BlockBound4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BlockBound4

open Submission BoseGases
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## A helper (local copy, so this module is self-contained) -/

/-- FS's error shape `Γ` is nonnegative. -/
theorem d4Gamma_nonneg_aux {R0 s K_B μ : ℝ} {v : ℝ³ → ℝ} (hKB : 0 < K_B)
    (hμ : 0 ≤ μ) (hav : 0 ≤ a v) : 0 ≤ d4Gamma R0 s K_B μ v := by
  unfold d4Gamma Work.SmallBoxA0.kinPGamma
  refine add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hKB) 3) ?_)
  exact Real.rpow_nonneg (mul_nonneg hμ (pow_nonneg hav 3)) (1 / 2)

/-- **R3a — the `cS1 > 0` chain at the FAITHFUL energy (with FS's `ε_T`-gap term).**

The verbatim `linarith` chain of the private `Work.SmallBoxA0.kinP_cS1_pos_chain`
(`Submission/Work/SmallBoxA0/kinP_block_bound.lean`), with the `kinPWord` atom
replaced by `pDiagForm s (fsKinCoeff c0)` and the energy `kinPEnergy` replaced by
the faithful `diagWEnergy` (`cgap·cnPlus + pDiagForm s (fsKinCoeff c₀) + qLHSword`).

It consumes the pure-pairing form of the Bogoliubov rung
`−(1/2)(1+ηq)·D·m²/s³ − Bq − Eq·n₊ ≤ pDiagForm + q4PairWord` with `m² ≤ (N̂+1)²`
— in particular NO `cgap` on the kinetic side — and the `ε_T`-gap term `cgap·n₊`
pays the potential-side `n₊`-remainder via the regime
`hbox : totNCoeff + D1's n₊-coefficient ≤ cgap`. The mass deficit
`½D((N̂+1)² − m²)/s³` is nonnegative and discarded. -/
theorem diagW_cS1_pos_chain {n : ℕ} {s μ R0 K_B Ct c0 cgap ηq m Bq Eq : ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hμ : 0 < μ) (hR0 : 0 < R0) (hKB : 0 < K_B)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hRs : R0 ≤ s * chiR0) (hμs : 1 ≤ μ * s ^ 3) (hc0 : 0 < c0)
    {Φ : X (n + 1) → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox (n + 1) s, (Φ x) ^ 2) = 1)
    (hwin : (((n + 1 : ℕ) : ℝ)) / s ^ 3 ≤ 9 * μ)
    (hSc1 : 0 < cS1 s Φ)
    (hD : g0w0Mass (v := v) h ≤ 8 * π * (a v))
    (hbox : Work.SmallBoxA0.totNCoeff s μ v + Work.SmallBoxA0.kinPBogErr Ct n s v ≤ cgap)
    (hCorr : 2 * (1 / s ^ 3) * Work.SmallBoxA0.CorrWord s h Φ
        ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
    (hbr : Bq ≤ (88 * π + 39) * (a v) * μ)
    (heta : -((1 / 2) * ηq * (g0w0Mass (v := v) h) * m ^ 2 * (1 / s ^ 3))
        ≥ -(μ ^ 2 * (a v) * s ^ 3 * d4Gamma R0 s K_B μ v + μ * (a v)))
    (hQ : -((1 / 2) * (1 + ηq) * (g0w0Mass (v := v) h) * m ^ 2 * (1 / s ^ 3))
        - Bq - Eq * cnPlus s Φ
        ≤ pDiagForm s (fsKinCoeff c0) Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ))
    (hEq : Eq ≤ Work.SmallBoxA0.kinPBogErr Ct n s v)
    (hm : m ^ 2 ≤ ((((n + 1 : ℕ) : ℝ)) + 1) ^ 2) :
    ((1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
      - (272 * π + 40) * μ ^ 2 * (a v) * s ^ 3 * d4Gamma R0 s K_B μ v
      - (272 * π + 40) * μ * (a v)
    ≤ diagWEnergy n s μ (wPairC s v) (wPairC s (g0 v h)) c0 cgap Φ := by
  classical
  set G : ℝ := d4Gamma R0 s K_B μ v with hGdef
  have hav : 0 ≤ a v := (av_bounds_weak hR0 hv_nonneg hvrad hv_supp h).1
  have hDnn : 0 ≤ g0w0Mass (v := v) h :=
    Work.SmallBoxA0.g0w0Mass_nonneg (v := v) (R := R0) hR0 hv_nonneg hvrad hv_supp h
  have hnn : 0 ≤ cnPlus s Φ := cnPlus_nonneg
  have hμnn : 0 ≤ μ := le_of_lt hμ
  have hs3i : (0 : ℝ) ≤ (s ^ 3)⁻¹ := by positivity
  have hGnn : 0 ≤ G := by
    rw [hGdef]; exact d4Gamma_nonneg_aux (v := v) hKB hμnn hav
  -- normalise the `1/s³` occurrences to `(s³)⁻¹` and the `d4Gamma` atom to `G`
  have heta' : -((1 / 2) * ηq * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹)
      ≥ -(μ ^ 2 * (a v) * s ^ 3 * G + μ * (a v)) := by
    have hh := heta
    rw [show (1 : ℝ) / s ^ 3 = (s ^ 3)⁻¹ from one_div _] at hh
    exact hh
  have hQ' : -((1 / 2) * (1 + ηq) * (g0w0Mass (v := v) h) * m ^ 2 * (s ^ 3)⁻¹)
        - Bq - Eq * cnPlus s Φ
      ≤ pDiagForm s (fsKinCoeff c0) Φ + q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
    have hh := hQ
    rw [show (1 : ℝ) / s ^ 3 = (s ^ 3)⁻¹ from one_div _] at hh
    exact hh
  have hCorr' : 2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
      ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ := by
    have hh := hCorr
    rw [show (1 : ℝ) / s ^ 3 = (s ^ 3)⁻¹ from one_div _] at hh
    exact hh
  -- the potential side
  have hpot : (1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        + (1 / 2) * (s ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 s Φ
        + q4PairWord (ℓ := s) (v := v) h (Φ := Φ)
        - Work.SmallBoxA0.potNCoeff μ (a v) * cnPlus s Φ - 36 * π * (a v) * μ
        - 2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
      ≤ qLHSword (N := n + 1) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    simpa [Work.SmallBoxA0.CorrWord] using Work.SmallBoxA0.pot_sharp_summary (N := n + 1)
      (ℓ := s) (μ := μ) hs hμ hv_nonneg hvrad hv_memL1 hR0 hv_supp h hRs hΦc.continuous hnorm
      hwin hSc1
  -- the `∬w₂`-slack
  have hslack := Work.SmallBoxA0.cs2_mass_slack (N := n + 1) (s := s) (μ := μ)
    (D := g0w0Mass (v := v) h) (v := v) hs hμ hDnn hD hav hμs hwin hΦc.continuous hnorm
  -- the linear `Corr` bound
  have hcorr : -((1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ)
      ≤ -(2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ) := by linarith [hCorr']
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
    rw [hsplit]; linarith [hsurplus, heta']
  -- the `n₊`-coefficient bookkeeping
  have hnf : 0 ≤ (cgap - Work.SmallBoxA0.kinPBogErr Ct n s v) * cnPlus s Φ
      - (1 / (72 * s ^ 2)) * cnPlus s Φ
      - Work.SmallBoxA0.potNCoeff μ (a v) * cnPlus s Φ - 72 * π * (a v) * μ * cnPlus s Φ := by
    have h0 : Work.SmallBoxA0.potNCoeff μ (a v) + 72 * π * (a v) * μ + 1 / (72 * s ^ 2)
        + Work.SmallBoxA0.kinPBogErr Ct n s v ≤ cgap := by
      rw [Work.SmallBoxA0.totNCoeff] at hbox
      linarith [hbox]
    nlinarith [h0, hnn]
  have hEeq : 0 ≤ (Work.SmallBoxA0.kinPBogErr Ct n s v - Eq) * cnPlus s Φ := by
    refine mul_nonneg ?_ hnn; linarith [hEq]
  -- arithmetic facts
  have hC1 : (1 : ℝ) ≤ 272 * π + 40 := by nlinarith [Real.pi_pos]
  have hX : 0 ≤ μ ^ 2 * (a v) * s ^ 3 * G := by
    have h1 : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
    have h2 : (0 : ℝ) ≤ s ^ 3 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hav) h2) hGnn
  have hY : 0 ≤ μ * (a v) := mul_nonneg hμnn hav
  -- the assembly
  rw [diagWEnergy, Work.KinPSuperadd.diagKinPEnergy, Work.KinPSuperadd.diagSlotWord]
  have key : (1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3)
        - (272 * π + 40) * μ ^ 2 * (a v) * s ^ 3 * G - (272 * π + 40) * μ * (a v)
      ≤ cgap * cnPlus s Φ + pDiagForm s (fsKinCoeff c0) Φ
        + qLHSword (N := n + 1) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    nlinarith [hpot, hslack, hcorr, hQ', hbr, hmass, hnf, hEeq, hX, hY, hC1, hDnn, hnn,
      Real.pi_pos]
  have heq : ((1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
        * (8 * π * (a v) * s ^ 3)
      = (1 / 4 : ℝ) * (((((n + 1 : ℕ) : ℝ)) / s ^ 3) - μ) ^ 2 * (8 * π * (a v) * s ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * s ^ 3) := by ring
  rw [heq]
  exact key

end Work.BlockBound4
