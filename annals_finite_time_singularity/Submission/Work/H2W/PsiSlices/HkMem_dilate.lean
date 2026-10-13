/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H^k`-membership is invariant under dilation of the radial variable

`Work.Spaces.HkMem α k F` says that the weighted `H^k` integrand of `F` is integrable, in `θ`
for every `z ≥ 0` and in `z` over `[0,∞)`.  The weight occurring in the integrand is
`w z = (1+z)²/z²`, and the derivatives are the Euler derivatives `D_z = z∂_z`, `D_θ`, which are
*invariant* under `z ↦ lam z` (`DilateOps.DzIter_dilate`, `DilateOps.mixed_dilate`).  Hence

  `HkIntegrand α k (F(lam·,·)) z θ = (w z / w (lam z))² · HkIntegrand α k F (lam z) θ`,

and the multiplier `(w z / w (lam z))² = (lam(1+z)/(1+lam z))⁴` is bounded on `z ≥ 0` by
`(max lam 1)⁴` (`T_bound` below).  Substituting `ζ = lam z` in the `z`-integral
(`integrableOn_Ioi_comp_mul_left_iff`) and applying `Integrable.mul_bdd` therefore gives
`HkMem α k (F(lam·,·))`.

The multiplier's measurability comes for free from `w_measurable` (`Measurable.div` needs no
side condition); the pointwise bound `T_bound` is obtained by squaring the exact per-slice
identity `z²·w z = (1+z)²` (`w_sq_mul`) and cancelling the positive factor `(z·lam z)⁴`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Spaces.Defs
import Submission.Work.H2W.PsiSlices.DilateOps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Elementary facts about the radial weight `w` -/

/-- The radial weight is positive where `z > 0`. -/
theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  simp only [Work.Spaces.w]
  exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)

/-- The radial weight does not vanish where `z > 0`. -/
theorem w_ne_zero {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := (w_pos hz).ne'

/-- The radial weight is (everywhere) measurable: division is measurable without any side
condition. -/
theorem w_measurable : Measurable Work.Spaces.w := by
  change Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
  exact ((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)

/-- The exact value of `z²·w z`. -/
theorem w_sq_mul {z : ℝ} (hz : z ≠ 0) : z ^ 2 * Work.Spaces.w z = (1 + z) ^ 2 := by
  simp only [Work.Spaces.w]
  rw [mul_comm]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 hz)

/-! ## The `H^k` integrand at `z = 0` -/

theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]

/-! ## The integrand with the radial weight removed

The Euler derivatives commute with a dilation while the weight does not; isolating the weight
makes the dilation invariance of the derivative part a purely combinatorial statement. -/

/-- The `H^k` integrand of the paper with the radial weight `w` removed: the `θ`-weights
`sin(2θ)^{-η/2}`, `wTheta` and the iterated derivatives survive. -/
noncomputable def HkCore (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ * ((1 : ℝ) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i f z θ * ((1 : ℝ) * Work.Spaces.wTheta α θ)) ^ 2 else 0

/-- The `H^k` integrand is the square of the radial weight times the weightless core. -/
theorem HkIntegrand_eq_w_sq_mul_core (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ = (Work.Spaces.w z) ^ 2 * HkCore α k f z θ := by
  simp only [Work.Spaces.HkIntegrand, HkCore, Work.Spaces.Wt, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h <;> ring

/-- The weightless core is invariant under dilation of the radial variable. -/
theorem HkCore_dilate (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (lam z θ : ℝ) :
    HkCore α k (fun z θ => F (lam * z) θ) z θ = HkCore α k F (lam * z) θ := by
  have h1 : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => F (lam * z) θ) z θ
      = Work.Spaces.DzIter i F (lam * z) θ :=
    fun i => congrFun (congrFun (DzIter_dilate F lam i) z) θ
  have h2 : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => F (lam * z) θ) z θ
      = Work.Spaces.mixed j i F (lam * z) θ :=
    fun j i => congrFun (congrFun (mixed_dilate F lam j i) z) θ
  simp only [HkCore]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [h2 j i]

/-- **The pointwise factorisation of the `H^k` integrand under a dilation.**  For `z > 0` the
dilated integrand is the integrand of the datum at `lam z`, multiplied by the square of the
ratio of the two radial weights. -/
theorem HkIntegrand_dilate_eq (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam)
    {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => F (lam * z) θ) z θ
      = ((Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2)
          * Work.Spaces.HkIntegrand α k F (lam * z) θ := by
  have hl : Work.Spaces.w (lam * z) ≠ 0 := w_ne_zero (mul_pos hlam hz)
  rw [HkIntegrand_eq_w_sq_mul_core, HkCore_dilate, HkIntegrand_eq_w_sq_mul_core,
    div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hl)]
  ring

/-! ## The multiplier `(w z / w (lam z))²` is bounded on `[0,∞)` -/

/-- Measurability of the multiplier `(w z / w (lam z))²`. -/
theorem T_measurable (lam : ℝ) :
    AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
  have h2 : Measurable (fun z : ℝ => Work.Spaces.w (lam * z)) :=
    w_measurable.comp (measurable_const.mul measurable_id)
  have hnum : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := w_measurable.pow_const 2
  have hden : Measurable (fun z : ℝ => (Work.Spaces.w (lam * z)) ^ 2) := h2.pow_const 2
  exact (hnum.div hden).aestronglyMeasurable

/-- **The multiplier is bounded on `z > 0`.**  Indeed `w z / w (lam z) = (lam(1+z)/(1+lam z))²`,
and `lam(1+z)/(1+lam z) ≤ max lam 1`. -/
theorem T_bound {lam z : ℝ} (hlam : 0 < lam) (hz : 0 < z) :
    ‖(Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2‖ ≤ max lam 1 ^ 4 := by
  have hz0 : z ≠ 0 := hz.ne'
  have hlz0 : lam * z ≠ 0 := (mul_pos hlam hz).ne'
  have hlz : 0 < lam * z := mul_pos hlam hz
  -- the squared weight identities
  have hA : z ^ 4 * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 := by
    calc z ^ 4 * (Work.Spaces.w z) ^ 2 = (z ^ 2 * Work.Spaces.w z) ^ 2 := by ring
      _ = ((1 + z) ^ 2) ^ 2 := by rw [w_sq_mul hz0]
      _ = (1 + z) ^ 4 := by ring
  have hB : (lam * z) ^ 4 * (Work.Spaces.w (lam * z)) ^ 2 = (1 + lam * z) ^ 4 := by
    calc (lam * z) ^ 4 * (Work.Spaces.w (lam * z)) ^ 2
        = ((lam * z) ^ 2 * Work.Spaces.w (lam * z)) ^ 2 := by ring
      _ = ((1 + lam * z) ^ 2) ^ 2 := by rw [w_sq_mul hlz0]
      _ = (1 + lam * z) ^ 4 := by ring
  -- the elementary comparison
  have hq : lam * (1 + z) ≤ max lam 1 * (1 + lam * z) := by
    rcases le_total lam 1 with h | h
    · calc lam * (1 + z) ≤ 1 * (1 + lam * z) := by nlinarith
        _ ≤ max lam 1 * (1 + lam * z) :=
            mul_le_mul_of_nonneg_right (le_max_right lam 1) (by positivity)
    · calc lam * (1 + z) ≤ lam * (1 + lam * z) :=
            mul_le_mul_of_nonneg_left
              (by nlinarith [mul_le_mul_of_nonneg_right h hz.le]) hlam.le
        _ = max lam 1 * (1 + lam * z) := by rw [max_eq_left h]
  have hqnn : 0 ≤ lam * (1 + z) := mul_nonneg hlam.le (by linarith)
  have hmain : (1 + z) ^ 4 * (lam * z) ^ 4
      ≤ (max lam 1) ^ 4 * ((1 + lam * z) ^ 4 * z ^ 4) := by
    have hp : (lam * (1 + z)) ^ 4 ≤ (max lam 1) ^ 4 * (1 + lam * z) ^ 4 := by
      have h1 := pow_le_pow_left₀ hqnn hq 4
      simpa only [mul_pow] using h1
    calc (1 + z) ^ 4 * (lam * z) ^ 4 = (lam * (1 + z)) ^ 4 * z ^ 4 := by ring
      _ ≤ ((max lam 1) ^ 4 * (1 + lam * z) ^ 4) * z ^ 4 :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (max lam 1) ^ 4 * ((1 + lam * z) ^ 4 * z ^ 4) := by ring
  -- cancel the positive factor `(z · lam z)^4`
  have hkey : (Work.Spaces.w z) ^ 2 * (z ^ 4 * (lam * z) ^ 4)
      ≤ ((max lam 1) ^ 4 * (Work.Spaces.w (lam * z)) ^ 2) * (z ^ 4 * (lam * z) ^ 4) := by
    calc (Work.Spaces.w z) ^ 2 * (z ^ 4 * (lam * z) ^ 4)
        = (z ^ 4 * (Work.Spaces.w z) ^ 2) * (lam * z) ^ 4 := by ring
      _ = (1 + z) ^ 4 * (lam * z) ^ 4 := by rw [hA]
      _ ≤ (max lam 1) ^ 4 * ((1 + lam * z) ^ 4 * z ^ 4) := hmain
      _ = (max lam 1) ^ 4 * ((lam * z) ^ 4 * (Work.Spaces.w (lam * z)) ^ 2) * z ^ 4 := by
            rw [hB]; ring
      _ = ((max lam 1) ^ 4 * (Work.Spaces.w (lam * z)) ^ 2) * (z ^ 4 * (lam * z) ^ 4) := by
            ring
  have hfin : (Work.Spaces.w z) ^ 2
      ≤ (max lam 1) ^ 4 * (Work.Spaces.w (lam * z)) ^ 2 :=
    le_of_mul_le_mul_right hkey (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)),
    div_le_iff₀ (pow_pos (w_pos hlz) 2)]
  exact hfin

/-! ## The main lemma -/

theorem HkMem_dilate {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α k F)
    {lam : ℝ} (hlam : 0 < lam) :
    Work.Spaces.HkMem α k (fun z θ => F (lam * z) θ) := by
  obtain ⟨h1, h2⟩ := h
  -- the pointwise factorisation of the integrand, valid for every `z ∈ Iz`
  have hfac : ∀ z ∈ Work.Spaces.Iz, ∀ θ,
      Work.Spaces.HkIntegrand α k (fun z θ => F (lam * z) θ) z θ
        = ((Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2)
            * Work.Spaces.HkIntegrand α k F (lam * z) θ := by
    intro z hz θ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      simp [HkIntegrand_zero]
    · exact HkIntegrand_dilate_eq α k F hlam hzpos θ
  constructor
  · -- the `θ`-slices
    intro z hz
    have hz' : lam * z ∈ Work.Spaces.Iz :=
      Set.mem_Ici.mpr (mul_nonneg hlam.le (Set.mem_Ici.mp hz))
    have hmul : IntegrableOn (fun θ => ((Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2)
        * Work.Spaces.HkIntegrand α k F (lam * z) θ) Work.Spaces.Iθ :=
      MeasureTheory.Integrable.const_mul (h1 (lam * z) hz') _
    refine hmul.congr_fun_ae ?_
    exact Eventually.of_forall fun θ => (hfac z hz θ).symm
  · -- the `z`-integral
    have hGcomp : IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F (lam * z) θ)
        (Set.Ioi 0) := by
      have hGi : IntegrableOn
          (fun ζ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F ζ θ) (Set.Ioi 0) :=
        (integrableOn_Ici_iff_integrableOn_Ioi (b := (0 : ℝ))).1 h2
      have hh := (integrableOn_Ioi_comp_mul_left_iff
        (fun ζ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F ζ θ) 0 hlam)
      rw [mul_zero] at hh
      exact hh.2 hGi
    have hTmeas : AEStronglyMeasurable
        (fun z => (Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2)
        (volume.restrict (Set.Ioi 0)) := T_measurable lam
    have hTbdd : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
        ‖(Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2‖ ≤ max lam 1 ^ 4 := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun z hz => T_bound hlam (Set.mem_Ioi.mp hz)
    have hTprod : IntegrableOn
        (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F (lam * z) θ)
          * ((Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2)) (Set.Ioi 0) :=
      Integrable.mul_bdd hGcomp hTmeas hTbdd
    have hEqOn : EqOn
        (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F (lam * z) θ)
          * ((Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2))
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => F (lam * z) θ) z θ)
        (Set.Ioi 0) := by
      intro z hz
      have hzpos : 0 < z := Set.mem_Ioi.mp hz
      show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F (lam * z) θ)
            * ((Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2)
          = ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (fun z θ => F (lam * z) θ) z θ
      rw [mul_comm (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F (lam * z) θ)]
      have hconst : (∫ θ in Work.Spaces.Iθ,
            ((Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2)
              * Work.Spaces.HkIntegrand α k F (lam * z) θ)
          = ((Work.Spaces.w z) ^ 2 / (Work.Spaces.w (lam * z)) ^ 2)
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F (lam * z) θ) :=
        integral_const_mul _ _
      rw [← hconst]
      exact integral_congr_ae
        (Eventually.of_forall fun θ => (hfac z (Set.mem_Ici.mpr hzpos.le) θ).symm)
    have hAioi : IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => F (lam * z) θ) z θ) (Set.Ioi 0) :=
      hTprod.congr_fun hEqOn measurableSet_Ioi
    exact (integrableOn_Ici_iff_integrableOn_Ioi (b := (0 : ℝ))).2 hAioi

end Work.H2W.PsiSlices
