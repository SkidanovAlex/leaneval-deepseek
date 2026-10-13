import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0PieceHelpers
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.radBlk_le7
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.gamQfun_angBlk
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05a_Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.angBlk_bound
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.sep_HkSq_le
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary facts about the constant `Cc α = 3α/(2c(α))` -/

lemma Cc_pos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 < Cc α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  rw [Cc]
  positivity

lemma Cc_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : Cc α ≤ 15 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  rw [Cc, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Work.Spaces.c α)]
  nlinarith

lemma abs_Cc_le_twenty (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : |Cc α| ≤ 20 := by
  rw [abs_of_pos (Cc_pos hα hα1)]
  have h := Cc_le α hα hα1
  linarith

lemma sq_Cc_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : (Cc α) ^ 2 ≤ 225 * α ^ 2 := by
  have h := Cc_le α hα hα1
  have h0 : 0 ≤ Cc α := le_of_lt (Cc_pos hα hα1)
  calc (Cc α) ^ 2 ≤ (15 * α) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 225 * α ^ 2 := by ring

/-! ## The two separated forms -/

/-- **The separated form of `NP4a`.**  On the open quadrant the piece `NP4a α w` is the product
of the angular profile `CC α` and the radial profile `BB4 w`. -/
lemma NP4a_eq_sep {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.StrongPersist.H6Pair6Aux.NP4a α w z θ = CC α θ * BB4 w z := by
  intro z θ hz hθ hθ2
  have h1 : Work.FTS.StrongPersist.H6Pair6Aux.NP4a α w z θ
      = Work.Construction.N04a α (fun z θ => Work.Construction.Fstar α z θ + w z θ) w z θ := by
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP4a,
      Work.FTS.StrongPersist.H6Pair6Aux.NA4, Work.Construction.N04a,
      Work.Construction.s2, Work.Spaces.Dth, Work.Spaces.pth,
      Work.Construction.Fstar]
    ring
  rw [h1, Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzN04a_sep hα hα1 z θ hz ⟨hθ, hθ2⟩]
  simp only [CC, BB4]
  ring

/-- **The separated form of `NP5a`.** -/
lemma NP5a_eq_sep {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.StrongPersist.H6Pair6Aux.NP5a α w z θ = CC5 α θ * BB5 w z := by
  intro z θ hz hθ hθ2
  have h1 : Work.FTS.StrongPersist.H6Pair6Aux.NP5a α w z θ
      = Work.Construction.N05a α (fun z θ => Work.Construction.Fstar α z θ + w z θ) w z θ := by
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5a,
      Work.FTS.StrongPersist.H6Pair6Aux.NA5, Work.Construction.N05a]
    ring
  rw [h1, Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzN05a_sep hα hα1 z θ hz ⟨hθ, hθ2⟩]
  simp only [CC5, BB5]
  ring

/-! ## The `ℋ⁶`-square of the two pieces equals that of their separated forms -/

lemma HkSq_NP4a_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4a α w)
      = Work.Spaces.HkSq α 6 (fun z θ => CC α θ * BB4 w z) :=
  Work.FTS.EllipticEst.HkSq_congr_open α 6 (NP4a_eq_sep hα hα1 w)

lemma HkSq_NP5a_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5a α w)
      = Work.Spaces.HkSq α 6 (fun z θ => CC5 α θ * BB5 w z) :=
  Work.FTS.EllipticEst.HkSq_congr_open α 6 (NP5a_eq_sep hα hα1 w)

/-! ## The angular block of the separated forms -/

lemma AngBlk_CC_eq (α : ℝ) :
    AngBlk α (CC α) = Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (Cc α) := by
  funext θ
  simp only [AngBlk, CC, Cc, Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk]

lemma AngBlk_CC5_eq (α : ℝ) :
    AngBlk α (CC5 α) = Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (-(Cc α)) := by
  funext θ
  simp only [AngBlk, CC5, Cc, Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk]

/-! ## The main theorem -/

/-
Route hint (the `X · f` engine `radialMaj6_split` does NOT apply here: its `f`-side would be the
non-decaying factor `NA4`/`NA5`, whose `HkSq α 6` is the junk value `0`).  Instead use the
**separation** identities `H6Pair6Aux.nzN04a_sep` / `nzN05a_sep`, which write (for `z > 0`,
`θ ∈ Ioo 0 (π/2)`)

  `N04a α (F_*+w) w = (3α/(2c α)) · (Gam α θ · qfun θ) · (L₁₂ w z · FM.Fstar z)`,
  `N05a α (F_*+w) w = (-(3α/(2c α))) · (Gam α θ · qfun θ) · (L₁₂ w z · Hz z)`,

i.e. both pieces are `ρ(z) · γ(θ)` with a *radial* `ρ` and an *angular* `γ` (up to the
constants `3α/(2c α)`), so their `ℋ⁶`-slots are `(D_z^j ρ)(z)·(D_θ^i γ)(θ)` and the double
integral **factors**:

  `∫∫ (D_z^jρ · D_θ^iγ)² slotW_i = (∫_z (D_z^jρ)² w²) · (∫_θ (D_θ^iγ)² σ_i²)`

(with `σ_i² = sin(2θ)^{-η}` for `i = 0` and `sin(2θ)^{-γ}` for `i ≥ 1`).  The two one-variable
inputs are: `radBlk_le7` (`Cr`, giving `∑_{q≤6} ∫_z (D_z^q(ρ·L₁₂ w))² w² ≤ Cr(1+Kρ)² HkSq α 6 w`
for a radial `ρ` with `|Zop^[b]ρ| ≤ Kρ`, `b ≤ 6`; use `ρ := FM.Fstar` resp. `ρ := Hz`, whose
jet bounds are `H6Pair6Aux.H6N0Aux.nzradZop_bound6`), and the angular bounds
`∫_θ (D_θ^iγ)² σ_i² ≤ C_i·max(1, 1/α)` from `|D_θ^i(Gam·qfun)| ≤ C_i·Gam`
(`LocData6.DthIter_Gam_abs_le6` plus the bounded jets of `qfun θ = cos 2θ - 1/3`) together with
`α·∫_θ Gam α θ² sin(2θ)^{-γ}dθ ≤ C` (spell it as
`∫ (sin 2θ)^{2α/3-γ} ≤ 3000/(17α)`, exactly as in `H6Rows.FstarI12H6.integral_gammaAngMaj6_le`).
-/
theorem N04aN05a_HkSq6 : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4a α w)
        ≤ K * (1 + Work.Spaces.HkSq α 6 w) ∧
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5a α w)
        ≤ K * (1 + Work.Spaces.HkSq α 6 w) := by
  intro C₀
  obtain ⟨Aang, hAangpos, hAang⟩ := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.angBlk_bound
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.radBlk_le7
  obtain ⟨Kr, hKrpos, hKrF, hKrH⟩ := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzradZop_bound6
  refine ⟨225 * Aang * Cr * (1 + Kr) ^ 2 + 1, by positivity, ?_⟩
  intro α hαIoc w hC hXn
  have hαIoc' : α ∈ Set.Ioc (0 : ℝ) 1 := hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  -- the class hypotheses
  have hsm : Work.FTS.EllipticEst.SmoothOpen w := hC.reg
  have hmem7 : Work.Spaces.HkMem α 7 w := hC.mem
  have hmem6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (k := 6) (k' := 7) (by norm_num) hsm hmem7
  have hl12 : Work.Construction.L12 w 0 = 0 := hC.l12
  -- the smoothness of the two radial profiles
  have hFs6 : ContDiffOn ℝ 6 Work.FM.Fstar (Set.Ioi 0) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzsmoothOn_FMFstar).of_le (by norm_num)
  have hHz6 : ContDiffOn ℝ 6 Work.FTS.Nonlinear.FstarPkg.Hz (Set.Ioi 0) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzsmoothOn_Hz).of_le (by norm_num)
  -- the radial block bounds
  have hrad4 : MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.SlotSum (BB4 w))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB4 w) z)
        ≤ Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w := by
    have h := hCr α hαIoc' Work.FM.Fstar w Kr (le_of_lt hKrpos) hFs6
      (fun b hb z hz => hKrF b hb z hz) hsm hmem6 hmem7 hl12
    have hfun : Work.FTS.StrongPersist.SlotSum (BB4 w)
        = fun z => ∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z' _ => Work.FM.Fstar z'
              * Work.Construction.L12 w z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl
    rw [hfun]
    exact h
  have hrad5 : MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.SlotSum (BB5 w))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB5 w) z)
        ≤ Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w := by
    have h := hCr α hαIoc' Work.FTS.Nonlinear.FstarPkg.Hz w Kr (le_of_lt hKrpos) hHz6
      (fun b hb z hz => hKrH b hb z hz) hsm hmem6 hmem7 hl12
    have hfun : Work.FTS.StrongPersist.SlotSum (BB5 w)
        = fun z => ∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z' _ => Work.FTS.Nonlinear.FstarPkg.Hz z'
              * Work.Construction.L12 w z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl
    rw [hfun]
    exact h
  -- the angular block bounds
  have hIntAng4 : MeasureTheory.IntegrableOn (AngBlk α (CC α)) Work.Spaces.Iθ := by
    rw [AngBlk_CC_eq]
    exact (hAang α hαIoc' (Cc α) (abs_Cc_le_twenty α hα hα1)).1
  have hIntAng5 : MeasureTheory.IntegrableOn (AngBlk α (CC5 α)) Work.Spaces.Iθ := by
    rw [AngBlk_CC5_eq]
    exact (hAang α hαIoc' (-(Cc α)) (by
      rw [abs_neg]; exact abs_Cc_le_twenty α hα hα1)).1
  have hAngBd4 : (∫ θ in Work.Spaces.Iθ, AngBlk α (CC α) θ) ≤ 225 * Aang := by
    rw [AngBlk_CC_eq]
    have hb := (hAang α hαIoc' (Cc α) (abs_Cc_le_twenty α hα hα1)).2
    have h2 : Aang * (Cc α) ^ 2 ≤ Aang * (225 * α ^ 2) :=
      mul_le_mul_of_nonneg_left (sq_Cc_le α hα hα1) (le_of_lt hAangpos)
    have h3 : α ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (Cc α) θ)
        ≤ α ^ 2 * (225 * Aang) := by
      calc α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (Cc α) θ)
          ≤ Aang * (Cc α) ^ 2 := hb
        _ ≤ Aang * (225 * α ^ 2) := h2
        _ = α ^ 2 * (225 * Aang) := by ring
    exact le_of_mul_le_mul_left h3 (pow_pos hα 2)
  have hAngBd5 : (∫ θ in Work.Spaces.Iθ, AngBlk α (CC5 α) θ) ≤ 225 * Aang := by
    rw [AngBlk_CC5_eq]
    have hb := (hAang α hαIoc' (-(Cc α)) (by
      rw [abs_neg]; exact abs_Cc_le_twenty α hα hα1)).2
    have h2 : Aang * (-(Cc α)) ^ 2 ≤ Aang * (225 * α ^ 2) := by
      rw [neg_sq]
      exact mul_le_mul_of_nonneg_left (sq_Cc_le α hα hα1) (le_of_lt hAangpos)
    have h3 : α ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (-(Cc α)) θ)
        ≤ α ^ 2 * (225 * Aang) := by
      calc α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (-(Cc α)) θ)
          ≤ Aang * (-(Cc α)) ^ 2 := hb
        _ ≤ Aang * (225 * α ^ 2) := h2
        _ = α ^ 2 * (225 * Aang) := by ring
    exact le_of_mul_le_mul_left h3 (pow_pos hα 2)
  -- the two separation bounds
  have hsep4 := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.sep_HkSq_le (α := α) (C := CC α) (B := BB4 w) hIntAng4 hrad4.1
  have hsep5 := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.sep_HkSq_le (α := α) (C := CC5 α) (B := BB5 w) hIntAng5 hrad5.1
  -- the two block integrals are nonnegative
  have hSlot4nn : 0 ≤ (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB4 w) z) :=
    integral_nonneg fun z =>
      Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hSlot5nn : 0 ≤ (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB5 w) z) :=
    integral_nonneg fun z =>
      Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h225 : 0 ≤ 225 * Aang := by linarith [hAangpos]
  have hKnn : 0 ≤ 225 * Aang * Cr * (1 + Kr) ^ 2 := by positivity
  constructor
  · rw [HkSq_NP4a_eq hα hα1 w]
    refine hsep4.trans ?_
    have h1 : (∫ θ in Work.Spaces.Iθ, AngBlk α (CC α) θ)
        * (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB4 w) z)
        ≤ (225 * Aang) * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w) :=
      mul_le_mul hAngBd4 hrad4.2 hSlot4nn h225
    refine h1.trans ?_
    have h2 : (225 * Aang) * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w)
        = (225 * Aang * Cr * (1 + Kr) ^ 2) * Work.Spaces.HkSq α 6 w := by ring
    rw [h2]
    have hS := Work.Spaces.HkSq_nonneg α 6 w
    nlinarith [hS, hKnn]
  · rw [HkSq_NP5a_eq hα hα1 w]
    refine hsep5.trans ?_
    have h1 : (∫ θ in Work.Spaces.Iθ, AngBlk α (CC5 α) θ)
        * (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB5 w) z)
        ≤ (225 * Aang) * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w) :=
      mul_le_mul hAngBd5 hrad5.2 hSlot5nn h225
    refine h1.trans ?_
    have h2 : (225 * Aang) * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w)
        = (225 * Aang * Cr * (1 + Kr) ^ 2) * Work.Spaces.HkSq α 6 w := by ring
    rw [h2]
    have hS := Work.Spaces.HkSq_nonneg α 6 w
    nlinarith [hS, hKnn]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
