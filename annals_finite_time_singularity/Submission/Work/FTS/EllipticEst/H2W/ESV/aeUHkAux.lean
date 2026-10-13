import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.FTS.EllipticEst.AngAWeak.aeSliceBdd
-- NOTE: `AngAWeak.aeLeftTendsto` is not imported yet: importing it together with
-- `H2W.AeProof.AeSliceRightTendsto` clashes on `Honest.contDiffOn_slice` (defined in both
-- `Honest/HonDifQuotBound.lean` and `Honest/HonSliceRightTendsto.lean`).  Re-add it once that
-- tree-level duplicate declaration has gone.
import Submission.Work.FTS.EllipticEst.AngAWeak.aeTruncIdent
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.LzeroSelfFormHon
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngAWeak/aeUHkAux` — auxiliary lemmas for `AngAWeak/aeUHk`

Sorry-free helpers for the level-`0` `ρ`-mass estimate in the a.e. class `AeData`
(see `AngAWeak/NOTES_aeUHk.md`):

* `HkIntegrand_zero_eq_w_esv` — the level-`0` integrand on `Iθ`;
* `hkMemU_slices` — the first conjunct of `HkMem α 0 u`, from `aeSliceBdd`;
* `integrableOn_pth_sq_of_AeData_esv` — `(∂_θu z ·)² ∈ L¹(Iθ)` for every `z > 0`;
* `YslicePlain`, `Uslice` — the two slice energies.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- On `Iθ` the level-`0` `HkIntegrand` is the single weighted square `g² w² σ`. -/
theorem HkIntegrand_zero_eq_w_esv (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-- **The first conjunct of `HkMem α 0 u`.**  For every `z ∈ Iz` the level-`0` integrand of `u`
is integrable over `Iθ`: at `z = 0` it vanishes (`w 0 = 0`), and for `z > 0` it is the constant
`(w z)²` times `u²σ`, which is integrable by `aeSliceBdd`. -/
theorem hkMemU_slices (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 u z θ) Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | h0
  · -- at `z = 0` the weight `w` vanishes
    have hw : Work.Spaces.w z = 0 := by
      rw [← h0, Work.Spaces.w]
      norm_num
    refine integrableOn_zero.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show (0 : ℝ) = Work.Spaces.HkIntegrand α 0 u z θ
    rw [HkIntegrand_zero_eq_w_esv α u z hθ, hw]
    ring
  · -- for `z > 0` divide out the constant `(w z)²`
    have hbase : IntegrableOn
        (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      (aeSliceBdd α u G h).2 z h0
    have h2 : IntegrableOn
        (fun θ => (Work.Spaces.w z) ^ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        Work.Spaces.Iθ := hbase.const_mul _
    refine h2.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    show (Work.Spaces.w z) ^ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = Work.Spaces.HkIntegrand α 0 u z θ
    rw [HkIntegrand_zero_eq_w_esv α u z hθ]
    ring

/-- The `θ`-energy of the slice `u z ·`: `Y z = ∫_θ (∂_θu z θ)²`. -/
def YslicePlain (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2

/-- The plain `θ`-mass of the slice: `U z = ∫_θ (u z θ)²`. -/
def Uslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2

/-- **The `θ`-derivative of a slice is square-integrable for every `z > 0`.**  From
`HkMem α 0 (∂_θθu)` the slice lemma `slice_bdd_of_sq_mul_sEta` bounds `u z θ` and `∂_θu z θ` on
the open interval, whence `(∂_θu z ·)²` is integrable on `Iθ`. -/
theorem integrableOn_pth_sq_of_AeData_esv (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z : ℝ, 0 < z →
      IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  have hslice : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact ((h.smooth 2).comp (by fun_prop) hmap)
  have hint : IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    have h1 := h.memAng2.1 z hzI
    have h2 : IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      h1.congr_fun (fun θ hθ => HkIntegrand_zero_eq_w_esv α (Work.Spaces.pthIter 2 u) z hθ)
        measurableSet_Icc
    have hw' : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
    have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
    refine h3.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show ((Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
        = (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ
    have hpth2 : Work.Spaces.pthIter 2 u z θ
        = deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ := by
      simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
        Work.Spaces.pthIter_zero, Work.Spaces.pth]
    rw [hpth2]
    field_simp
  obtain ⟨C, hC0, hC⟩ :=
    Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta hslice hint
  -- `Iθ` and the open interval differ by the null set `{0, π/2}`: integrate there.
  have hpair : volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hms : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Measure.restrict_congr_set hst
  rw [IntegrableOn, hms]
  refine IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    ((measurable_deriv (fun θ' : ℝ => u z θ')).pow_const 2).aestronglyMeasurable
    (C ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hb := (hC θ hθ).2
  rw [Real.norm_of_nonneg (sq_nonneg _), show Work.Spaces.pth u z θ
    = deriv (fun θ' : ℝ => u z θ') θ from rfl, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hb 2
