import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepWideEndDefs
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.sweepTopTools
-- import Submission.Work.Drive.chamferVel_hasDerivAt
-- import Submission.Work.Drive.sweepLoopChamfer_ftc
import Submission.Work.Drive.sweepBlurFacts

/-!
# Auxiliary lemmas for the wide-end tolerance estimate

The matched knot parameter of the wide end is `Work.Drive.wideSigma ta w d lam` (with
`d = period - w`), whose profile-level version is `wideSfrac` and whose rate is `wideRho`.

This file collects the elementary facts about these functions: the period shift, the (a.e.)
derivative, the Lipschitz bound of `wideSigma` in the loop parameter, and the positivity and
boundedness of the rate.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-! ## The matched parameter and its rate -/

/-- The matched knot parameter (period-shifting version of `wideSfrac`). -/
def wtPar (ta w d lam : ℝ) : ℝ → ℝ := fun τ => wideSigma ta w d lam τ

/-- The branch rate of the matched parameter, in the loop parameter. -/
def wtRate (w d lam : ℝ) : ℝ → ℝ := fun τ => wideRho w d lam (sweepParam τ)

lemma wtPar_add_period (ta w d lam τ : ℝ) :
    wtPar ta w d lam (τ + period) = wtPar ta w d lam τ + period :=
  wideSigma_add_period ta w d lam τ

/-- The matched parameter in terms of the sheet index and the profile. -/
lemma wtPar_eq_floor (ta w d lam τ : ℝ) :
    wtPar ta w d lam τ
      = (⌊τ / period⌋ : ℤ) * period + wideSfrac ta w d lam (sweepParam τ) := by
  have hp : period ≠ 0 := ne_of_gt period_pos
  have hτ : τ = (⌊τ / period⌋ : ℤ) * period + sweepParam τ * period := by
    rw [sweepParam]
    field_simp
    ring
  have hmain : τ + (wideSfrac ta w d lam (sweepParam τ) - sweepParam τ * period)
      = (⌊τ / period⌋ : ℤ) * period + wideSfrac ta w d lam (sweepParam τ) := by
    nth_rewrite 1 [hτ]
    ring
  exact hmain

lemma sweepParam_measurable : Measurable sweepParam := by
  have h4 : sweepParam = fun t : ℝ => Int.fract (t / period) := by
    funext t; rw [sweepParam, Int.fract]
  rw [h4]
  exact measurable_fract.comp (measurable_id.div_const _)

lemma measurable_wideRho (w d lam : ℝ) : Measurable (fun u : ℝ => wideRho w d lam u) := by
  simp only [wideRho]
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
        measurable_const))

lemma wtRate_measurable (w d lam : ℝ) : Measurable (wtRate w d lam) :=
  (measurable_wideRho w d lam).comp sweepParam_measurable

/-! ## Slope facts for `wideSfrac` -/

/-- The chord-zone branch of `wideSfrac` is affine with slope `2 * d`. -/
lemma wideSfrac_chord_affine (ta w d lam v : ℝ) (hden : (1:ℝ)/2 - lam ≠ 0) :
    ta + w + lam*d + ((1 - 2*lam)*d)*((v - (1/2+lam/2))/(1/2-lam))
      = ta + w + lam*d + 2*d*(v - (1/2+lam/2)) := by
  congr 1
  rw [mul_div_assoc', div_eq_iff hden]
  ring

/-- **Upper bound for the increment of `wideSfrac`**:  its four slopes are at most `2 * period`. -/
lemma wideSfrac_sub_le (ta w d lam u u' : ℝ) (hwd : w + d = period) (hw0 : 0 ≤ w)
    (hd0 : 0 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (huu : u ≤ u') :
    wideSfrac ta w d lam u' - wideSfrac ta w d lam u ≤ 2 * period * (u' - u) := by
  have hP : 0 < period := period_pos
  have hwP : w ≤ period := by linarith
  have hsl : (1 - 2 * lam) * w ≤ period := by
    have h1' : (1 - 2*lam) ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h1' hw0]
  have hden : (1:ℝ)/2 - lam ≠ 0 := by linarith
  by_cases hu1 : u ≤ 1/2
  · by_cases hv1 : u' ≤ 1/2
    · rw [wideSfrac_arc hu1, wideSfrac_arc hv1]; nlinarith [hsl]
    · by_cases hv2 : u' ≤ 1/2 + lam/2
      · rw [wideSfrac_arc hu1, wideSfrac_chamfer₁ hv1 hv2]
        have hA : (1 - 2*u)*((1-2*lam)*w - period) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        nlinarith [hA]
      · by_cases hv3 : u' ≤ 1 - lam/2
        · rw [wideSfrac_arc hu1, wideSfrac_chord hv1 hv2 hv3,
            wideSfrac_chord_affine ta w d lam u' hden]
          have hA : (1 - 2*u)*((1-2*lam)*w - period) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          have hB : 2*d*(u' - (1/2+lam/2)) ≤ 2*period*(u' - (1/2+lam/2)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
          nlinarith [hA, hB]
        · rw [wideSfrac_arc hu1, wideSfrac_chamfer₂ hv1 hv2 hv3]
          have hA : (1 - 2*u)*((1-2*lam)*w - period) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          nlinarith [hA]
  · by_cases hu2 : u ≤ 1/2 + lam/2
    · by_cases hv2 : u' ≤ 1/2 + lam/2
      · have hv1 : ¬ u' ≤ 1/2 := by linarith
        rw [wideSfrac_chamfer₁ hu1 hu2, wideSfrac_chamfer₁ hv1 hv2]; nlinarith
      · by_cases hv3 : u' ≤ 1 - lam/2
        · have hv1 : ¬ u' ≤ 1/2 := by linarith
          rw [wideSfrac_chamfer₁ hu1 hu2, wideSfrac_chord hv1 hv2 hv3,
            wideSfrac_chord_affine ta w d lam u' hden]
          have hB : 2*d*(u' - (1/2+lam/2)) ≤ 2*period*(u' - (1/2+lam/2)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
          nlinarith [hB]
        · have hv1 : ¬ u' ≤ 1/2 := by linarith
          rw [wideSfrac_chamfer₁ hu1 hu2, wideSfrac_chamfer₂ hv1 hv2 hv3]; nlinarith
    · by_cases hv3 : u' ≤ 1 - lam/2
      · have hv1 : ¬ u' ≤ 1/2 := by linarith
        have hv2 : ¬ u' ≤ 1/2 + lam/2 := by linarith
        have hu3 : u ≤ 1 - lam/2 := by linarith
        rw [wideSfrac_chord hu1 hu2 hu3, wideSfrac_chord hv1 hv2 hv3,
          wideSfrac_chord_affine ta w d lam u' hden, wideSfrac_chord_affine ta w d lam u hden]
        nlinarith
      · by_cases hu3 : u ≤ 1 - lam/2
        · have hv1 : ¬ u' ≤ 1/2 := by linarith
          have hv2 : ¬ u' ≤ 1/2 + lam/2 := by linarith
          rw [wideSfrac_chord hu1 hu2 hu3, wideSfrac_chamfer₂ hv1 hv2 hv3,
            wideSfrac_chord_affine ta w d lam u hden]
          nlinarith
        · have hv1 : ¬ u' ≤ 1/2 := by linarith
          have hv2 : ¬ u' ≤ 1/2 + lam/2 := by linarith
          rw [wideSfrac_chamfer₂ hu1 hu2 hu3, wideSfrac_chamfer₂ hv1 hv2 hv3]; nlinarith

/-- **Lower bound for the increment of `wideSfrac`**:  its four slopes are nonnegative. -/
lemma wideSfrac_sub_le_rev (ta w d lam u u' : ℝ) (hwd : w + d = period) (hw0 : 0 ≤ w)
    (hd0 : 0 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (huu : u ≤ u') :
    wideSfrac ta w d lam u - wideSfrac ta w d lam u' ≤ 2 * period * (u' - u) := by
  have hP : 0 < period := period_pos
  have hwP : w ≤ period := by linarith
  have hden : (1:ℝ)/2 - lam ≠ 0 := by linarith
  have huu' : 0 ≤ u' - u := sub_nonneg.mpr huu
  have h1 : 0 ≤ 1 - 2*lam := by linarith
  have hk : ∀ a b : ℝ, a ≤ b → (1 - 2*lam)*a ≤ (1 - 2*lam)*b :=
    fun a b h => mul_le_mul_of_nonneg_left h h1
  by_cases hu1 : u ≤ 1/2
  · have key1 : (1-2*lam)*(2*u) ≤ (1-2*lam)*(2*(1/2:ℝ)) := hk _ _ (by linarith)
    have k1 := mul_le_mul_of_nonneg_right key1 hw0
    by_cases hv1 : u' ≤ 1/2
    · rw [wideSfrac_arc hu1, wideSfrac_arc hv1]
      nlinarith [k1, mul_nonneg (mul_nonneg h1 hw0) huu']
    · by_cases hv2 : u' ≤ 1/2 + lam/2
      · rw [wideSfrac_arc hu1, wideSfrac_chamfer₁ hv1 hv2]
        nlinarith [k1, mul_nonneg hP.le huu']
      · by_cases hv3 : u' ≤ 1 - lam/2
        · rw [wideSfrac_arc hu1, wideSfrac_chord hv1 hv2 hv3,
            wideSfrac_chord_affine ta w d lam u' hden]
          have hB : 0 ≤ 2*d*(u' - (1/2+lam/2)) := mul_nonneg (by linarith) (by linarith)
          nlinarith [k1, hB, mul_nonneg hP.le huu']
        · rw [wideSfrac_arc hu1, wideSfrac_chamfer₂ hv1 hv2 hv3]
          nlinarith [k1, mul_nonneg hP.le huu']
  · by_cases hu2 : u ≤ 1/2 + lam/2
    · by_cases hv2 : u' ≤ 1/2 + lam/2
      · have hv1 : ¬ u' ≤ 1/2 := by linarith
        rw [wideSfrac_chamfer₁ hu1 hu2, wideSfrac_chamfer₁ hv1 hv2]
        nlinarith [mul_nonneg hP.le huu']
      · by_cases hv3 : u' ≤ 1 - lam/2
        · have hv1 : ¬ u' ≤ 1/2 := by linarith
          rw [wideSfrac_chamfer₁ hu1 hu2, wideSfrac_chord hv1 hv2 hv3,
            wideSfrac_chord_affine ta w d lam u' hden]
          have hB : 0 ≤ 2*d*(u' - (1/2+lam/2)) := mul_nonneg (by linarith) (by linarith)
          nlinarith [hB, mul_nonneg hP.le huu']
        · have hv1 : ¬ u' ≤ 1/2 := by linarith
          rw [wideSfrac_chamfer₁ hu1 hu2, wideSfrac_chamfer₂ hv1 hv2 hv3]
          nlinarith [mul_nonneg hP.le huu']
    · by_cases hv3 : u' ≤ 1 - lam/2
      · have hv1 : ¬ u' ≤ 1/2 := by linarith
        have hv2 : ¬ u' ≤ 1/2 + lam/2 := by linarith
        have hu3 : u ≤ 1 - lam/2 := by linarith
        rw [wideSfrac_chord hu1 hu2 hu3, wideSfrac_chord hv1 hv2 hv3,
          wideSfrac_chord_affine ta w d lam u' hden, wideSfrac_chord_affine ta w d lam u hden]
        have hB : 2*d*(u - (1/2+lam/2)) ≤ 2*d*(u' - (1/2+lam/2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        nlinarith [hB, mul_nonneg hP.le huu']
      · by_cases hu3 : u ≤ 1 - lam/2
        · have hv1 : ¬ u' ≤ 1/2 := by linarith
          have hv2 : ¬ u' ≤ 1/2 + lam/2 := by linarith
          rw [wideSfrac_chord hu1 hu2 hu3, wideSfrac_chamfer₂ hv1 hv2 hv3,
            wideSfrac_chord_affine ta w d lam u hden]
          have hB : 2*d*(u - (1/2+lam/2)) ≤ 2*d*(1 - lam/2 - (1/2+lam/2)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          nlinarith [hB, mul_nonneg hP.le huu']
        · have hv1 : ¬ u' ≤ 1/2 := by linarith
          have hv2 : ¬ u' ≤ 1/2 + lam/2 := by linarith
          rw [wideSfrac_chamfer₂ hu1 hu2 hu3, wideSfrac_chamfer₂ hv1 hv2 hv3]
          nlinarith [mul_nonneg hP.le huu']

/-- **The profile-level Lipschitz bound for `wideSfrac`.** -/
lemma wideSfrac_abs_sub_le (ta w d lam u u' : ℝ) (hwd : w + d = period) (hw0 : 0 ≤ w)
    (hd0 : 0 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    |wideSfrac ta w d lam u' - wideSfrac ta w d lam u| ≤ 2 * period * |u' - u| := by
  rcases le_total u u' with h | h
  · have h1 := wideSfrac_sub_le ta w d lam u u' hwd hw0 hd0 hlam0 hlam1 h
    have h2 := wideSfrac_sub_le_rev ta w d lam u u' hwd hw0 hd0 hlam0 hlam1 h
    rw [abs_le]
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    constructor <;> linarith
  · have h1 := wideSfrac_sub_le ta w d lam u' u hwd hw0 hd0 hlam0 hlam1 h
    have h2 := wideSfrac_sub_le_rev ta w d lam u' u hwd hw0 hd0 hlam0 hlam1 h
    rw [abs_le]
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    constructor <;> linarith

/-- `wideSfrac` shifted by one profile unit gains exactly one period. -/
lemma wideSfrac_one_sub {ta w lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    wideSfrac ta w (period - w) lam 1 = wideSfrac ta w (period - w) lam 0 + period :=
  wideSfrac_periodicity hlam0 hlam1

/-! ## The matched parameter is `2`-Lipschitz -/

/-- The reverse period shift. -/
lemma wtPar_sub_int_mul_period (ta w d lam : ℝ) (k : ℤ) (τ : ℝ) :
    wtPar ta w d lam (τ - (k:ℝ) * period) = wtPar ta w d lam τ - (k:ℝ) * period := by
  have hg : Function.Periodic (fun x : ℝ => wtPar ta w d lam x - x) period := by
    intro x
    show wideSigma ta w d lam (x + period) - (x + period) = wideSigma ta w d lam x - x
    rw [wideSigma_add_period]; ring
  have h := hg.sub_int_mul_eq (x := τ) k
  have h2 : wtPar ta w d lam (τ - (k:ℝ) * period) - (τ - (k:ℝ) * period)
      = wtPar ta w d lam τ - τ := h
  linarith

/-- **The matched parameter is `2`-Lipschitz** (one-sided form). -/
lemma wtPar_sub_le_wt (ta w d lam τ τ' : ℝ) (hwd : w + d = period) (hw0 : 0 ≤ w) (hd0 : 0 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (hτ : τ ≤ τ') :
    wtPar ta w d lam τ' - wtPar ta w d lam τ ≤ 2 * (τ' - τ) := by
  have hP : 0 < period := period_pos
  set n : ℤ := ⌊τ / period⌋ with hn
  set n' : ℤ := ⌊τ' / period⌋ with hn'
  set u : ℝ := sweepParam τ with hu
  set u' : ℝ := sweepParam τ' with hu'
  have hτeq : τ = (n:ℝ) * period + u * period := by
    rw [hu, hn, sweepParam]; field_simp; ring
  have hτ'eq : τ' = (n':ℝ) * period + u' * period := by
    rw [hu', hn', sweepParam]; field_simp; ring
  have hττ : τ' - τ = ((n' - n : ℤ) : ℝ) * period + (u' - u) * period := by
    rw [hτeq, hτ'eq]; push_cast; ring
  have hwt : wtPar ta w d lam τ = (n:ℝ) * period + wideSfrac ta w d lam u := by
    rw [wtPar_eq_floor, hn, hu]
  have hwt' : wtPar ta w d lam τ' = (n':ℝ) * period + wideSfrac ta w d lam u' := by
    rw [wtPar_eq_floor, hn', hu']
  have humem : u ∈ Set.Ico (0:ℝ) 1 := by rw [hu]; exact sweepParam_mem τ
  have hu'mem : u' ∈ Set.Ico (0:ℝ) 1 := by rw [hu']; exact sweepParam_mem τ'
  have hnn_nonneg : (0:ℝ) ≤ ((n' - n : ℤ) : ℝ) := by
    have hle : n ≤ n' := by
      rw [hn, hn']
      apply Int.floor_mono
      rw [div_le_div_iff_of_pos_right hP]
      exact hτ
    have : (0:ℤ) ≤ n' - n := by omega
    exact Int.cast_nonneg this
  have key : wideSfrac ta w d lam u' - wideSfrac ta w d lam u
      ≤ 2 * period * (u' - u) + ((n' - n : ℤ) : ℝ) * period := by
    rcases lt_or_ge u u' with huv | huv
    · have h1 := wideSfrac_sub_le ta w d lam u u' hwd hw0 hd0 hlam0 hlam1 huv.le
      have h2 : (0:ℝ) ≤ ((n' - n : ℤ) : ℝ) * period := mul_nonneg hnn_nonneg hP.le
      linarith
    · rcases eq_or_lt_of_le huv with heq | hlt
      · have hz : wideSfrac ta w d lam u' - wideSfrac ta w d lam u = 0 := by rw [heq]; ring
        rw [hz]
        have h2 : (0:ℝ) ≤ ((n' - n : ℤ) : ℝ) * period := mul_nonneg hnn_nonneg hP.le
        have h3 : u' - u = 0 := by linarith
        rw [h3]; simpa using h2
      · have hnn1 : (1:ℝ) ≤ ((n' - n : ℤ) : ℝ) := by
          have hpos : (0:ℝ) < ((n' - n : ℤ) : ℝ) := by
            have hprod : (0:ℝ) < ((n' - n : ℤ) : ℝ) * period := by
              have h3 : (u' - u) * period < 0 := mul_neg_of_neg_of_pos (by linarith) hP
              linarith [hττ]
            by_contra hc
            have hc' : ((n' - n : ℤ) : ℝ) ≤ 0 := not_lt.mp hc
            nlinarith [hprod, hc', hP]
          have h4 : (0:ℤ) < n' - n := by exact_mod_cast hpos
          have h5 : (1:ℤ) ≤ n' - n := by omega
          exact_mod_cast h5
        have h1 : wideSfrac ta w d lam u' - wideSfrac ta w d lam 0 ≤ 2 * period * u' := by
          have h := wideSfrac_abs_sub_le ta w d lam 0 u' hwd hw0 hd0 hlam0 hlam1
          rw [show |u' - 0| = u' by rw [sub_zero, abs_of_nonneg hu'mem.1]] at h
          exact (abs_le.mp h).2
        have h2 : wideSfrac ta w d lam 1 - wideSfrac ta w d lam u ≤ 2 * period * (1 - u) := by
          have h := wideSfrac_abs_sub_le ta w d lam u 1 hwd hw0 hd0 hlam0 hlam1
          rw [show |1 - u| = 1 - u by rw [abs_of_nonneg (by linarith [humem.2])]] at h
          exact (abs_le.mp h).2
        have h3 : wideSfrac ta w d lam 1 = wideSfrac ta w d lam 0 + period := by
          have hd : d = period - w := by linarith
          rw [hd]; exact wideSfrac_periodicity hlam0 (by linarith)
        have h45 : wideSfrac ta w d lam u' - wideSfrac ta w d lam u
            = (wideSfrac ta w d lam u' - wideSfrac ta w d lam 0)
              + (wideSfrac ta w d lam 1 - wideSfrac ta w d lam u) - period := by
          rw [h3]; ring
        have h5 : (1:ℝ) * period ≤ ((n' - n : ℤ) : ℝ) * period :=
          mul_le_mul_of_nonneg_right hnn1 hP.le
        rw [h45]
        nlinarith [h1, h2, h5]
  rw [hwt, hwt']
  nlinarith [key, hττ]

/-- **The matched parameter is `2`-Lipschitz** (mirrored one-sided form). -/
lemma wtPar_sub_le_wt_rev (ta w d lam τ τ' : ℝ) (hwd : w + d = period) (hw0 : 0 ≤ w)
    (hd0 : 0 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (hτ : τ ≤ τ') :
    wtPar ta w d lam τ - wtPar ta w d lam τ' ≤ 2 * (τ' - τ) := by
  have hP : 0 < period := period_pos
  set n : ℤ := ⌊τ / period⌋ with hn
  set n' : ℤ := ⌊τ' / period⌋ with hn'
  set u : ℝ := sweepParam τ with hu
  set u' : ℝ := sweepParam τ' with hu'
  have hτeq : τ = (n:ℝ) * period + u * period := by
    rw [hu, hn, sweepParam]; field_simp; ring
  have hτ'eq : τ' = (n':ℝ) * period + u' * period := by
    rw [hu', hn', sweepParam]; field_simp; ring
  have hττ : τ' - τ = ((n' - n : ℤ) : ℝ) * period + (u' - u) * period := by
    rw [hτeq, hτ'eq]; push_cast; ring
  have hwt : wtPar ta w d lam τ = (n:ℝ) * period + wideSfrac ta w d lam u := by
    rw [wtPar_eq_floor, hn, hu]
  have hwt' : wtPar ta w d lam τ' = (n':ℝ) * period + wideSfrac ta w d lam u' := by
    rw [wtPar_eq_floor, hn', hu']
  have humem : u ∈ Set.Ico (0:ℝ) 1 := by rw [hu]; exact sweepParam_mem τ
  have hu'mem : u' ∈ Set.Ico (0:ℝ) 1 := by rw [hu']; exact sweepParam_mem τ'
  have hnn_nonneg : (0:ℝ) ≤ ((n' - n : ℤ) : ℝ) := by
    have hle : n ≤ n' := by
      rw [hn, hn']
      apply Int.floor_mono
      rw [div_le_div_iff_of_pos_right hP]
      exact hτ
    have : (0:ℤ) ≤ n' - n := by omega
    exact Int.cast_nonneg this
  have hnnP : (0:ℝ) ≤ ((n' - n : ℤ) : ℝ) * period := mul_nonneg hnn_nonneg hP.le
  have key : wideSfrac ta w d lam u - wideSfrac ta w d lam u'
      ≤ 2 * period * (u' - u) + 3 * (((n' - n : ℤ) : ℝ) * period) := by
    rcases le_total u u' with huv | huv
    · have h1 := wideSfrac_sub_le_rev ta w d lam u u' hwd hw0 hd0 hlam0 hlam1 huv
      linarith
    · rcases eq_or_lt_of_le huv with heq | hlt
      · have hz : wideSfrac ta w d lam u - wideSfrac ta w d lam u' = 0 := by rw [heq]; ring
        rw [hz]
        have h3 : u' - u = 0 := by linarith
        rw [h3]; simpa using hnnP
      · have hnn1 : (1:ℝ) ≤ ((n' - n : ℤ) : ℝ) := by
          have hpos : (0:ℝ) < ((n' - n : ℤ) : ℝ) := by
            have hprod : (0:ℝ) < ((n' - n : ℤ) : ℝ) * period := by
              have h3 : (u' - u) * period < 0 := mul_neg_of_neg_of_pos (by linarith) hP
              linarith [hττ]
            by_contra hc
            have hc' : ((n' - n : ℤ) : ℝ) ≤ 0 := not_lt.mp hc
            nlinarith [hprod, hc', hP]
          have h4 : (0:ℤ) < n' - n := by exact_mod_cast hpos
          have h5 : (1:ℤ) ≤ n' - n := by omega
          exact_mod_cast h5
        have h1 : wideSfrac ta w d lam u - wideSfrac ta w d lam 1 ≤ 2 * period * (1 - u) := by
          have h := wideSfrac_abs_sub_le ta w d lam u 1 hwd hw0 hd0 hlam0 hlam1
          rw [show |1 - u| = 1 - u by rw [abs_of_nonneg (by linarith [humem.2])]] at h
          have h2 := (abs_le.mp h).1
          linarith
        have h2 : wideSfrac ta w d lam 0 - wideSfrac ta w d lam u' ≤ 2 * period * u' := by
          have h := wideSfrac_abs_sub_le ta w d lam 0 u' hwd hw0 hd0 hlam0 hlam1
          rw [show |u' - 0| = u' by rw [sub_zero, abs_of_nonneg hu'mem.1]] at h
          have h2 := (abs_le.mp h).1
          linarith
        have h3 : wideSfrac ta w d lam 1 = wideSfrac ta w d lam 0 + period := by
          have hd : d = period - w := by linarith
          rw [hd]; exact wideSfrac_periodicity hlam0 (by linarith)
        have h45 : wideSfrac ta w d lam u - wideSfrac ta w d lam u'
            = (wideSfrac ta w d lam u - wideSfrac ta w d lam 1)
              + (wideSfrac ta w d lam 0 - wideSfrac ta w d lam u') + period := by
          rw [h3]; ring
        have h5 : (1:ℝ) * period ≤ ((n' - n : ℤ) : ℝ) * period :=
          mul_le_mul_of_nonneg_right hnn1 hP.le
        rw [h45]
        nlinarith [h1, h2, h5]
  rw [hwt, hwt']
  nlinarith [key, hττ]

/-- **The matched parameter is `2`-Lipschitz.** -/
lemma wtPar_lipschitz (ta w d lam : ℝ) (hwd : w + d = period) (hw0 : 0 ≤ w) (hd0 : 0 ≤ d)
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (τ τ' : ℝ) :
    |wtPar ta w d lam τ' - wtPar ta w d lam τ| ≤ 2 * |τ' - τ| := by
  rcases le_total τ τ' with h | h
  · have h1 := wtPar_sub_le_wt ta w d lam τ τ' hwd hw0 hd0 hlam0 hlam1 h
    have h2 := wtPar_sub_le_wt_rev ta w d lam τ τ' hwd hw0 hd0 hlam0 hlam1 h
    have hc : |τ' - τ| = τ' - τ := abs_of_nonneg (sub_nonneg.mpr h)
    rw [abs_le]
    constructor
    · rw [hc]; linarith
    · rw [hc]; linarith
  · have h1 := wtPar_sub_le_wt ta w d lam τ' τ hwd hw0 hd0 hlam0 hlam1 h
    have h2 := wtPar_sub_le_wt_rev ta w d lam τ' τ hwd hw0 hd0 hlam0 hlam1 h
    have hc : |τ' - τ| = τ - τ' := by rw [abs_of_nonpos (sub_nonpos.mpr h)]; ring
    rw [abs_le]
    constructor
    · rw [hc]; linarith
    · rw [hc]; linarith

end Work.Drive
