/-
# `N0Aux.B4P2` — level-`4` bounds for the pieces `NP4a` and `NP5a`

Both pieces are separated products (`...blocks/N0Aux/B4SepId`):

  `NP4a α w = VfsA1 α θ · (VfsRad z · L₁₂w z)`,
  `NP5a α w = VfsA2 α θ · (Hz z · L₁₂w z)`   on the open quadrant,

so the level-`4` separation bound `sep_HkSq4_le` (angular block `AngBlk4`, radial slot sum
`SlotSum4`) applies together with the angular masses `angBlk4_VfsA_mass`, the radial block
`radBlk5` (multiplier jets from `H6N0Aux.nzradZop_bound6`), the moment-free pricing
`HkSq α 4 w = (Xn α w)² ≤ C₀²α⁴` and the `α`-uniformity of the angular mass.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4Aux
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4SepDefs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.sep_HkSq4_le
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.angBlk4_VfsA_mass
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.radBlk5
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4SepId
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0PieceHelpers
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem NP4a_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NP4a α w) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨Ka, hKapos, hA⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.angBlk4_VfsA_mass
  obtain ⟨Cr, hCrpos, hrad⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.radBlk5
  obtain ⟨Kr, hKrpos, hKrF, _hKrH⟩ := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzradZop_bound6
  have hK0nn : (0 : ℝ) ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hKapos.le hCrpos.le) (sq_nonneg _)) (sq_nonneg _)
  refine ⟨Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1, by linarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hw.mem
  obtain ⟨hAngInt, hAngMass, _hAngInt2, _hAngMass2⟩ := hA α hαIoc
  -- the multiplier `VfsRad = F_*` and its jets
  have hVF5 : ContDiffOn ℝ 5 Work.FTS.StrongPersist.L3Rhs.VfsRad (Set.Ioi 0) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzsmoothOn_FMFstar).of_le (by norm_num)
  have hVFjet : ∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] Work.FTS.StrongPersist.L3Rhs.VfsRad z| ≤ Kr :=
    fun b hb z hz => hKrF b (by omega) z hz
  have hradB := hrad α hαIoc Work.FTS.StrongPersist.L3Rhs.VfsRad w Kr hKrpos.le
    hVF5 hVFjet hsmw hm4 hw.l12
  -- the congruence to the separated form and the separation bound
  have hcongr : Work.Spaces.HkSq α 4 (NP4a α w)
      = Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.StrongPersist.L3Rhs.VfsA1 α θ
          * (Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 (NP4a_eq_sep4 hα w)
  have hsep := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.sep_HkSq4_le
    (α := α) (C := Work.FTS.StrongPersist.L3Rhs.VfsA1 α)
    (B := fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z)
    hAngInt hradB.1
  -- the arithmetic
  have hw5 : Work.Spaces.HkSq α 4 w ≤ C₀ ^ 2 * α ^ 4 := by
    rw [sq_xn w]
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hIntnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz,
      SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z) z :=
    integral_nonneg fun z => SlotSum4_nonneg _ z
  have h1 : (α * (∫ θ in Work.Spaces.Iθ,
        AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ))
      * (∫ z in Work.Spaces.Iz,
          SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
            * Work.Construction.L12 w z) z)
      ≤ Ka * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w) :=
    mul_le_mul hAngMass hradB.2 hIntnn hKapos.le
  have hprod : (∫ θ in Work.Spaces.Iθ,
        AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ)
      * (∫ z in Work.Spaces.Iz,
          SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
            * Work.Construction.L12 w z) z)
      ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3 := by
    refine le_of_mul_le_mul_left ?_ hα
    calc α * ((∫ θ in Work.Spaces.Iθ,
            AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ)
          * (∫ z in Work.Spaces.Iz,
              SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
                * Work.Construction.L12 w z) z))
        = (α * (∫ θ in Work.Spaces.Iθ,
              AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ))
            * (∫ z in Work.Spaces.Iz,
                SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
                  * Work.Construction.L12 w z) z) := by ring
      _ ≤ Ka * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w) := h1
      _ = Ka * Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w := by ring
      _ ≤ Ka * Cr * (1 + Kr) ^ 2 * (C₀ ^ 2 * α ^ 4) :=
          mul_le_mul_of_nonneg_left hw5
            (mul_nonneg (mul_nonneg hKapos.le hCrpos.le) (sq_nonneg _))
      _ = α * (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3) := by ring
  have hα3 : α ^ 3 ≤ 1 := pow_le_one₀ hα.le hα1
  have hHnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  calc Work.Spaces.HkSq α 4 (NP4a α w)
      = Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.StrongPersist.L3Rhs.VfsA1 α θ
          * (Work.FTS.StrongPersist.L3Rhs.VfsRad z * Work.Construction.L12 w z)) := hcongr
    _ ≤ (∫ θ in Work.Spaces.Iθ, AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ)
          * (∫ z in Work.Spaces.Iz,
              SlotSum4 (fun z => Work.FTS.StrongPersist.L3Rhs.VfsRad z
                * Work.Construction.L12 w z) z) := hsep
    _ ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3 := hprod
    _ ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hα3 hK0nn
    _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        calc Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * 1
            = Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 := by ring
          _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2) * (1 + Work.Spaces.HkSq α 5 w) :=
              le_mul_of_one_le_right hK0nn hone
          _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) :=
              mul_le_mul_of_nonneg_right (by linarith) hHnn

theorem NP5a_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NP5a α w) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨Ka, hKapos, hA⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.angBlk4_VfsA_mass
  obtain ⟨Cr, hCrpos, hrad⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.radBlk5
  obtain ⟨Kr, hKrpos, _hKrF, hKrH⟩ := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzradZop_bound6
  have hK0nn : (0 : ℝ) ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hKapos.le hCrpos.le) (sq_nonneg _)) (sq_nonneg _)
  refine ⟨Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1, by linarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hw.mem
  obtain ⟨_hAngInt, _hAngMass, hAngInt2, hAngMass2⟩ := hA α hαIoc
  -- the multiplier `Hz` and its jets
  have hHz5 : ContDiffOn ℝ 5 Work.FTS.Nonlinear.FstarPkg.Hz (Set.Ioi 0) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzsmoothOn_Hz).of_le (by norm_num)
  have hHzjet : ∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ Kr :=
    fun b hb z hz => hKrH b (by omega) z hz
  have hradB := hrad α hαIoc Work.FTS.Nonlinear.FstarPkg.Hz w Kr hKrpos.le
    hHz5 hHzjet hsmw hm4 hw.l12
  have hcongr : Work.Spaces.HkSq α 4 (NP5a α w)
      = Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.StrongPersist.L3Rhs.VfsA2 α θ
          * (Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 (NP5a_eq_sep4 w)
  have hsep := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.sep_HkSq4_le
    (α := α) (C := Work.FTS.StrongPersist.L3Rhs.VfsA2 α)
    (B := fun z => Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z)
    hAngInt2 hradB.1
  have hw5 : Work.Spaces.HkSq α 4 w ≤ C₀ ^ 2 * α ^ 4 := by
    rw [sq_xn w]
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hIntnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz,
      SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z) z :=
    integral_nonneg fun z => SlotSum4_nonneg _ z
  have h1 : (α * (∫ θ in Work.Spaces.Iθ,
        AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ))
      * (∫ z in Work.Spaces.Iz,
          SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
            * Work.Construction.L12 w z) z)
      ≤ Ka * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w) :=
    mul_le_mul hAngMass2 hradB.2 hIntnn hKapos.le
  have hprod : (∫ θ in Work.Spaces.Iθ,
        AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ)
      * (∫ z in Work.Spaces.Iz,
          SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
            * Work.Construction.L12 w z) z)
      ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3 := by
    refine le_of_mul_le_mul_left ?_ hα
    calc α * ((∫ θ in Work.Spaces.Iθ,
            AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ)
          * (∫ z in Work.Spaces.Iz,
              SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
                * Work.Construction.L12 w z) z))
        = (α * (∫ θ in Work.Spaces.Iθ,
              AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ))
            * (∫ z in Work.Spaces.Iz,
                SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
                  * Work.Construction.L12 w z) z) := by ring
      _ ≤ Ka * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w) := h1
      _ = Ka * Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 4 w := by ring
      _ ≤ Ka * Cr * (1 + Kr) ^ 2 * (C₀ ^ 2 * α ^ 4) :=
          mul_le_mul_of_nonneg_left hw5
            (mul_nonneg (mul_nonneg hKapos.le hCrpos.le) (sq_nonneg _))
      _ = α * (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3) := by ring
  have hα3 : α ^ 3 ≤ 1 := pow_le_one₀ hα.le hα1
  have hHnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  calc Work.Spaces.HkSq α 4 (NP5a α w)
      = Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.StrongPersist.L3Rhs.VfsA2 α θ
          * (Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z)) := hcongr
    _ ≤ (∫ θ in Work.Spaces.Iθ, AngBlk4 α (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ)
          * (∫ z in Work.Spaces.Iz,
              SlotSum4 (fun z => Work.FTS.Nonlinear.FstarPkg.Hz z
                * Work.Construction.L12 w z) z) := hsep
    _ ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * α ^ 3 := hprod
    _ ≤ Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hα3 hK0nn
    _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        calc Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 * 1
            = Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 := by ring
          _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2) * (1 + Work.Spaces.HkSq α 5 w) :=
              le_mul_of_one_le_right hK0nn hone
          _ ≤ (Ka * Cr * (1 + Kr) ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) :=
              mul_le_mul_of_nonneg_right (by linarith) hHnn

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
