/-
# Cauchy–Schwarz for the `ℋ¹` inner product `H1IP` in the interior class `RegQ α 1`

`RegQ α 1 f = SmoothQuad f ∧ HkMem α 1 f ∧ BdryTraces α 1 f`, where `SmoothQuad` is genuine
`C^∞` on the open quadrant `(0,∞) × (0,π/2)` — the class of the localised data of the route.
This is the `RegQ`-analogue of `Work.FTS.CoercivityStep.Base.H1IP_cs`, which is stated in the
(useless-for-the-route) *analytic* class `HkReg = SmoothNbhd ∧ HkMem`.

The proof is the same: the four weighted pairings of

  `H1IP α f g = 10 (D_z f, D_z g)_{w²/sin^η} + 10¹⁰ (f,g)_{w²/sin^η}
                 + 10¹⁷ (f,g)_{w²} + 10²¹ (D_θ f, D_θ g)_{w²/sin^γ}`

are each rewritten as the `L²` pairing of two of the four *blocks*

  `Xeta f = f·w/√(sin 2θ^η)`, `XetaDz f = D_z f·w/√(sin 2θ^η)`,
  `XgamDth α f = D_θ f·W`, `Xw f = f·w`,

and bounded by Cauchy–Schwarz (`cs_place_Q`) against the `L²`-norms of the blocks, each of
which is dominated by `HkSq α 1 f` (`L2Sq_blocks_le_HkSq`).  The block bookkeeping — `L²`
membership and a.e. strong measurability, both from continuity on the open quadrant rather than
from analyticity — is `block_calc_Q`.

All three ingredients are proved in the sibling modules of this directory; the present file
contains only the assembly of the four pairings and the arithmetic of the constants
(`10 + 10¹⁰ + 10¹⁷ + 10²¹ ≤ 10²²` and `HkNorm = √HkSq`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.H1IPAddDefs
import Submission.Work.Coercivity.Xeta_mul_eq
import Submission.Work.Coercivity.XetaDz_mul_eq
import Submission.Work.Coercivity.XgamDth_mul_eq
import Submission.Work.Coercivity.holder_two_mul
import Submission.Work.Coercivity.integrable_sqrt_mul_sqrt
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.CoercivityFix.Assembly.cs_place_Q
import Submission.Work.FTS.CoercivityFix.Assembly.block_calc_Q
import Submission.Work.FTS.CoercivityFix.Assembly.L2Sq_blocks_le_HkSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The triangle inequality for four terms -/

private theorem abs_add_four (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The main theorem -/

theorem H1IP_cs_Q : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → ∀ f g : ℝ → ℝ → ℝ,
    Work.FTS.Nonlin.RegQ α 1 f → Work.FTS.Nonlin.RegQ α 1 g →
    |Work.Coercivity.H1IP α f g|
      ≤ C * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g := by
  refine ⟨(10 : ℝ) ^ 22, by norm_num, ?_⟩
  intro α hα f g hf hg
  obtain ⟨hqf, hmf, _⟩ := hf
  obtain ⟨hqg, hmg, _⟩ := hg
  obtain ⟨hLeta_f, hsleta_f, hpleta_f, hLetaDz_f, hsletaDz_f, hpletaDz_f,
    hLgam_f, hslgam_f, hplgam_f, hLw_f, hslw_f, hplw_f⟩ := block_calc_Q α hqf hmf
  obtain ⟨hLeta_g, hsleta_g, hpleta_g, hLetaDz_g, hsletaDz_g, hpletaDz_g,
    hLgam_g, hslgam_g, hplgam_g, hLw_g, hslw_g, hplw_g⟩ := block_calc_Q α hqg hmg
  obtain ⟨hSqEta_f, hSqEtaDz_f, hSqGam_f, hSqW_f⟩ := L2Sq_blocks_le_HkSq α hmf
  obtain ⟨hSqEta_g, hSqEtaDz_g, hSqGam_g, hSqW_g⟩ := L2Sq_blocks_le_HkSq α hmg
  set Y : ℝ := Real.sqrt (Work.Spaces.HkSq α 1 f) * Real.sqrt (Work.Spaces.HkSq α 1 g)
    with hYdef
  have hYnn : 0 ≤ Y := by
    rw [hYdef]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## Term 1: the `D_z`-pairing with weight `w²·sin(2θ)^{-η}`
  have hT1 :
      |Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ Y := by
    rw [hYdef]
    have hwip : Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f)
        (Work.Spaces.Dz g)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.XetaDz f z θ * Work.Coercivity.XetaDz g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Work.Coercivity.XetaDz_mul_eq f g z θ hθ).symm
    rw [hwip]
    refine le_trans (cs_place_Q (Work.Coercivity.XetaDz f) (Work.Coercivity.XetaDz g)
      hLetaDz_f hLetaDz_g hsletaDz_f hsletaDz_g hpletaDz_f hpletaDz_g) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hSqEtaDz_f) (Real.sqrt_le_sqrt hSqEtaDz_g)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## Term 2: the `L²`-pairing with weight `w²·sin(2θ)^{-η}`
  have hT2 : |Work.Coercivity.wip Work.Coercivity.lamEta f g| ≤ Y := by
    rw [hYdef]
    have hwip : Work.Coercivity.wip Work.Coercivity.lamEta f g
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.Xeta f z θ * Work.Coercivity.Xeta g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Work.Coercivity.Xeta_mul_eq f g z θ hθ).symm
    rw [hwip]
    refine le_trans (cs_place_Q (Work.Coercivity.Xeta f) (Work.Coercivity.Xeta g)
      hLeta_f hLeta_g hsleta_f hsleta_g hpleta_f hpleta_g) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hSqEta_f) (Real.sqrt_le_sqrt hSqEta_g)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## Term 3: the plain `w²`-pairing
  have hT3 : |Work.Coercivity.wip Work.Coercivity.lamW f g| ≤ Y := by
    rw [hYdef]
    have hwip : Work.Coercivity.wip Work.Coercivity.lamW f g
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.Xw f z θ * Work.Coercivity.Xw g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      simp only [Work.Coercivity.Xw, Work.Coercivity.lamW]
      ring
    rw [hwip]
    refine le_trans (cs_place_Q (Work.Coercivity.Xw f) (Work.Coercivity.Xw g)
      hLw_f hLw_g hslw_f hslw_g hplw_f hplw_g) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hSqW_f) (Real.sqrt_le_sqrt hSqW_g)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## Term 4: the `D_θ`-pairing with weight `w²·sin(2θ)^{-γ}`
  have hT4 :
      |Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
        (Work.Spaces.Dth g)| ≤ Y := by
    rw [hYdef]
    have hwip : Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
        (Work.Spaces.Dth g)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.XgamDth α f z θ * Work.Coercivity.XgamDth α g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Work.Coercivity.XgamDth_mul_eq α f g z θ hθ).symm
    rw [hwip]
    refine le_trans (cs_place_Q (Work.Coercivity.XgamDth α f) (Work.Coercivity.XgamDth α g)
      hLgam_f hLgam_g hslgam_f hslgam_g hplgam_f hplgam_g) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hSqGam_f) (Real.sqrt_le_sqrt hSqGam_g)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## The triangle inequality for the four terms of `H1IP`
  have h10 : (0 : ℝ) ≤ 10 := by norm_num
  have habs : |Work.Coercivity.H1IP α f g|
      ≤ 10 * |Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        + 10 ^ 10 * |Work.Coercivity.wip Work.Coercivity.lamEta f g|
        + 10 ^ 17 * |Work.Coercivity.wip Work.Coercivity.lamW f g|
        + 10 ^ 21 * |Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
            (Work.Spaces.Dth g)| := by
    have h := abs_add_four
      ((10 : ℝ) * Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f)
        (Work.Spaces.Dz g))
      ((10 : ℝ) ^ 10 * Work.Coercivity.wip Work.Coercivity.lamEta f g)
      ((10 : ℝ) ^ 17 * Work.Coercivity.wip Work.Coercivity.lamW f g)
      ((10 : ℝ) ^ 21 * Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
        (Work.Spaces.Dth g))
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg h10,
      abs_of_nonneg (pow_nonneg h10 10), abs_of_nonneg (pow_nonneg h10 17),
      abs_of_nonneg (pow_nonneg h10 21)] at h
    exact h
  have hT1' : 10 * |Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f)
      (Work.Spaces.Dz g)| ≤ 10 * Y := mul_le_mul_of_nonneg_left hT1 h10
  have hT2' : 10 ^ 10 * |Work.Coercivity.wip Work.Coercivity.lamEta f g| ≤ 10 ^ 10 * Y :=
    mul_le_mul_of_nonneg_left hT2 (pow_nonneg h10 10)
  have hT3' : 10 ^ 17 * |Work.Coercivity.wip Work.Coercivity.lamW f g| ≤ 10 ^ 17 * Y :=
    mul_le_mul_of_nonneg_left hT3 (pow_nonneg h10 17)
  have hT4' : 10 ^ 21 * |Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
      (Work.Spaces.Dth g)| ≤ 10 ^ 21 * Y :=
    mul_le_mul_of_nonneg_left hT4 (pow_nonneg h10 21)
  have hsum : |Work.Coercivity.H1IP α f g|
      ≤ 10 * Y + 10 ^ 10 * Y + 10 ^ 17 * Y + 10 ^ 21 * Y :=
    le_trans habs (add_le_add (add_le_add (add_le_add hT1' hT2') hT3') hT4')
  calc |Work.Coercivity.H1IP α f g|
      ≤ 10 * Y + 10 ^ 10 * Y + 10 ^ 17 * Y + 10 ^ 21 * Y := hsum
    _ = ((10 : ℝ) + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * Y := by ring
    _ ≤ (10 : ℝ) ^ 22 * Y := mul_le_mul_of_nonneg_right (by norm_num) hYnn
    _ = (10 : ℝ) ^ 22
          * (Real.sqrt (Work.Spaces.HkSq α 1 f) * Real.sqrt (Work.Spaces.HkSq α 1 g)) := by
        rw [hYdef]
    _ = (10 : ℝ) ^ 22 * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g := by
        simp only [Work.Spaces.HkNorm]
        ring

end Work.FTS.CoercivityFix.Assembly
