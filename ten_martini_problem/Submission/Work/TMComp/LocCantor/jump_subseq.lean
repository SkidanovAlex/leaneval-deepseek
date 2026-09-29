import Mathlib
import Submission.Work.TMComp.LocCantor.C8_jump
import Submission.Work.TMComp.Kotani.GlueDefs
import Submission.Work.TMComp.Kotani.Objects

/-!
# `jump_subseq`: extracting a subsequence on which the jump of `cayley ∘ Ψ` integrates to `0`

The route's extension step needs, from the vanishing `∫_K K2(E+iε_j, y) dE → 0` of the
(K2)-integrand, a sequence `ε_{φ j} → 0` for which the *Euclidean* jump
`J_j(E) = ‖cayley (Ψ (E+iε_j)) - cayley (Ψ (E-iε_j))‖` is small in `L¹(K)`.

The pointwise input is `Psi_jump_cube_le_eight_K2` (`C8_jump.lean`):

  `J(E,ε)^3 ≤ 8 · K2(E+iε, y)`   for all `E ∈ ℝ`, `ε > 0`,

together with the trivial bound `J ≤ 2` (the Cayley transform maps `ℍ` to the unit disc).

These two facts already give FIXED-Sequence convergence: by Hölder (`p = 3`, `q = 3/2`) on the
finite measure space `(K, dE)`,

  `∫_K J ≤ (∫_K J^3)^{1/3} (vol K)^{2/3} ≤ (8 ∫_K K2)^{1/3} (vol K)^{2/3} → 0`,

so the conclusion holds with `φ = id` (a strictly monotone map `ℕ → ℕ`).  The general
interpolation/limit step is isolated in `tendsto_integral_of_cube_le`.
-/

open MeasureTheory Filter Topology Set
open Work.TMComp.Kotani

noncomputable section

namespace Work.TMComp.LocCantor

set_option linter.style.haveILetI false

/-! ## Continuity of the integrand along the horizontal line -/

/-- `E ↦ mfun α lam (E + iε) x` is continuous for `ε > 0` (the line stays in the upper half
plane, where `mfun` is continuous jointly). -/
lemma continuous_mfun_horiz (α lam : ℝ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Continuous (fun E : ℝ => mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) x) := by
  have h := MfunProbs.mfun_continuousOn α lam
  have hc : Continuous (fun E : ℝ => (((E : ℂ) + (ε : ℂ) * Complex.I), x)) := by fun_prop
  have hm : ∀ E : ℝ, (((E : ℂ) + (ε : ℂ) * Complex.I), x)
      ∈ {p : ℂ × ℝ | 0 < p.1.im} := by
    intro E
    show 0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one]
    linarith
  exact h.comp_continuous hc hm

/-- `E ↦ sigSec α lam (E + iε) y` is continuous for `ε > 0`. -/
lemma continuous_sigSec_horiz (α lam : ℝ) {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    Continuous (fun E : ℝ => sigSec α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y) := by
  have h1 := continuous_mfun_horiz α lam hε (α - y)
  have h3 : ∀ E : ℝ, star (mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) (α - y)) ≠ 0 := by
    intro E
    refine star_ne_zero.mpr ?_
    refine ne_of_apply_ne Complex.im (ne_of_gt ?_)
    exact MfunProbs.mfun_im_pos α lam (by
      show 0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_one]
      linarith) (α - y)
  have h2 : Continuous (fun E : ℝ =>
      (star (mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) (α - y)))⁻¹) := h1.star.inv₀ h3
  have h3' : (fun E : ℝ => (star (mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) (α - y)))⁻¹)
      = fun E : ℝ => sigSec α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y := by
    funext E; rw [sigSec, one_div]
  rw [h3'] at h2
  exact h2

/-- Composition of a continuous `ℍ`-valued map with `cayley` is continuous. -/
lemma continuous_cayley_comp {f : ℝ → ℂ} (hf : Continuous f) (hpos : ∀ x, 0 < (f x).im) :
    Continuous (fun x => cayley (f x)) := by
  have hI : Continuous (fun _ : ℝ => Complex.I) := continuous_const
  have h : ∀ x, f x + Complex.I ≠ 0 := by
    intro x h; have := congrArg Complex.im h; simp at this; linarith [hpos x]
  have hc : Continuous (fun x => (f x - Complex.I) / (f x + Complex.I)) :=
    (hf.sub hI).div (hf.add hI) h
  exact hc.congr (fun x => by rw [cayley])

/-- `0 < Im(-1/z)` whenever `0 < Im z`. -/
lemma neg_one_div_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := ne_of_apply_ne Complex.im (ne_of_gt hz)
  rw [neg_one_div_im hz0]
  exact div_pos hz (pow_pos (norm_pos_iff.mpr hz0) 2)

/-- The jump integrand `E ↦ ‖cayley (Ψ (E+iε)) - cayley (Ψ (E-iε))‖` is continuous on `ℝ`
(hence strongly measurable); `Ψ` is continuous off the real axis and `cayley` has no pole
because both values of `Ψ` lie in the upper half plane. -/
lemma continuous_jump_integrand (α lam y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun E : ℝ =>
      ‖cayley (Psi α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y)
        - cayley (Psi α lam ((E : ℂ) - (ε : ℂ) * Complex.I) y)‖) := by
  have hEpos : ∀ E : ℝ, 0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im := by
    intro E
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one]
    linarith
  have hXim : ∀ E : ℝ, ((mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
        - ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E / 2 : ℝ) : ℂ)).im
      = N1 α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y := by
    intro E
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, sub_zero, N1]
    ring
  have hYim : ∀ E : ℝ, ((sigSec α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
        + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E / 2 : ℝ) : ℂ)).im
      = N2 α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y := by
    intro E
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, sub_zero, N2]
    ring
  have hup : Continuous (fun E : ℝ => cayley (Psi α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y)) := by
    have hcont : Continuous (fun E : ℝ =>
        (mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
          - ((E / 2 : ℝ) : ℂ)) :=
      ((continuous_mfun_horiz α lam hε y).sub continuous_const).sub (by fun_prop)
    have hne : ∀ E : ℝ, (mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
        - ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E / 2 : ℝ) : ℂ) ≠ 0 := by
      intro E h
      have h1 : ((mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
          - ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E / 2 : ℝ) : ℂ)).im = 0 := by rw [h]; simp
      rw [hXim E] at h1
      linarith [N1_pos α lam ((E : ℂ) + (ε : ℂ) * Complex.I) (hEpos E) y]
    have hinv : Continuous (fun E : ℝ =>
        -1 / ((mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
          - ((E / 2 : ℝ) : ℂ))) := continuous_const.div hcont hne
    have hpos' : ∀ E : ℝ, 0 < ((-1 / ((mfun α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
        - ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E / 2 : ℝ) : ℂ)))).im := fun E =>
      neg_one_div_im_pos (by rw [hXim E]; exact N1_pos α lam _ (hEpos E) y)
    refine (continuous_cayley_comp hinv hpos').congr (fun E => ?_)
    rw [Psi_eq_inv_upper α lam E ε hε y]
  have hlo : Continuous (fun E : ℝ => cayley (Psi α lam ((E : ℂ) - (ε : ℂ) * Complex.I) y)) := by
    have hcont : Continuous (fun E : ℝ =>
        (sigSec α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y + ((ε / 2 : ℝ) : ℂ) * Complex.I)
          - ((E / 2 : ℝ) : ℂ)) :=
      ((continuous_sigSec_horiz α lam hε y).add continuous_const).sub (by fun_prop)
    have hne : ∀ E : ℝ, (sigSec α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
        + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E / 2 : ℝ) : ℂ) ≠ 0 := by
      intro E h
      have h1 : ((sigSec α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
          + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E / 2 : ℝ) : ℂ)).im = 0 := by rw [h]; simp
      rw [hYim E] at h1
      linarith [N2_pos α lam ((E : ℂ) + (ε : ℂ) * Complex.I) (hEpos E) y]
    have hinv : Continuous (fun E : ℝ =>
        -1 / ((sigSec α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y + ((ε / 2 : ℝ) : ℂ) * Complex.I)
          - ((E / 2 : ℝ) : ℂ))) := continuous_const.div hcont hne
    have hpos' : ∀ E : ℝ, 0 < ((-1 / ((sigSec α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
        + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E / 2 : ℝ) : ℂ)))).im := fun E =>
      neg_one_div_im_pos (by rw [hYim E]; exact N2_pos α lam _ (hEpos E) y)
    refine (continuous_cayley_comp hinv hpos').congr (fun E => ?_)
    rw [Psi_eq_inv_lower α lam E ε hε y]
  exact (hup.sub hlo).norm

/-! ## `Ψ` lies in the upper half plane on both sides of the axis -/

lemma im_Psi_pos (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    0 < (Psi α lam E y).im := by
  have hXim : (mfun α lam E y - E / 2).im = N1 α lam E y := by
    rw [Complex.sub_im, N1]; simp
  have hne : mfun α lam E y - E / 2 ≠ 0 := by
    intro h; rw [h] at hXim; simp at hXim; linarith [N1_pos α lam E hE y]
  rw [Psi, glued_of_pos α lam hE y, neg_one_div_im hne, hXim]
  exact div_pos (N1_pos α lam E hE y) (by positivity)

lemma im_Psi_pos_lower (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    0 < (Psi α lam ((E₀ : ℂ) - (ε : ℂ) * Complex.I) y).im := by
  rw [Psi_eq_inv_lower α lam E₀ ε hε y]
  have hEpos : 0 < ((E₀ : ℂ) + (ε : ℂ) * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one]
    linarith
  have hwim : 0 < ((sigSec α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
        + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ)).im := by
    have h := sigSec_im_pos α lam hEpos y
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one]
    linarith
  have hwne : (sigSec α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
        + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hwim; simp at hwim
  rw [neg_one_div_im hwne]
  exact div_pos hwim (by positivity)

/-- The jump is bounded by `2` (both Cayley values lie in the unit disc). -/
lemma norm_cayley_sub_le_two (α lam : ℝ) (E ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    ‖cayley (Psi α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y)
        - cayley (Psi α lam ((E : ℂ) - (ε : ℂ) * Complex.I) y)‖ ≤ 2 := by
  have hEpos : 0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one]
    linarith
  have h1 : ‖cayley (Psi α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y)‖ < 1 :=
    norm_cayley_lt_one (im_Psi_pos α lam hEpos y)
  have h2 : ‖cayley (Psi α lam ((E : ℂ) - (ε : ℂ) * Complex.I) y)‖ < 1 :=
    norm_cayley_lt_one (im_Psi_pos_lower α lam E ε hε y)
  calc ‖cayley (Psi α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y)
        - cayley (Psi α lam ((E : ℂ) - (ε : ℂ) * Complex.I) y)‖
      ≤ ‖cayley (Psi α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y)‖
        + ‖cayley (Psi α lam ((E : ℂ) - (ε : ℂ) * Complex.I) y)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by linarith
    _ = 2 := by norm_num

/-! ## An interpolation/limit lemma for integrals on a finite measure space -/

/-- `x ↦ x ^ (1/3)` sends sequences tending to `0` to sequences tending to `0`. -/
lemma tendsto_rpow_one_third {a : ℕ → ℝ} (ha : Tendsto a atTop (nhds 0)) :
    Tendsto (fun j => (a j) ^ ((1:ℝ)/3)) atTop (nhds 0) := by
  have h0 : ContinuousAt (fun x : ℝ => x ^ ((1:ℝ)/3)) 0 :=
    Real.continuousAt_rpow_const 0 ((1:ℝ)/3) (Or.inr (by norm_num))
  have h1 := h0.tendsto.comp ha
  rwa [Real.zero_rpow (by norm_num : ((1:ℝ)/3) ≠ 0)] at h1

/-- **Interpolation step.**  On a finite measure space, if `0 ≤ F j`, `F j ≤ 2` and
`∫ F j^3 → 0`, then `∫ F j → 0`.  This is Hölder's inequality with `p = 3`, `q = 3/2`
together with a squeeze. -/
theorem integral_cube_le_implies
    {K : Set ℝ} (hKfin : volume K < ⊤) (F : ℕ → ℝ → ℝ)
    (hFcont : ∀ j, Continuous (F j))
    (hFnonneg : ∀ j, ∀ x, 0 ≤ F j x)
    (hFbound : ∀ j, ∀ x, F j x ≤ 2)
    (hcube : Tendsto (fun j => ∫ x in K, F j x ^ 3) atTop (nhds 0)) :
    Tendsto (fun j => ∫ x in K, F j x) atTop (nhds 0) := by
  haveI hI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr (ne_of_lt hKfin)
  have hp : (3:ℝ).HolderConjugate (3/2:ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hmem : ∀ j, MemLp (F j) (ENNReal.ofReal 3) (volume.restrict K) := fun j =>
    MemLp.of_bound (hFcont j).aestronglyMeasurable 2
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hFnonneg j x)]; exact hFbound j x)
  have hmem1 : MemLp (fun _ : ℝ => (1:ℝ)) (ENNReal.ofReal (3/2)) (volume.restrict K) :=
    memLp_const 1
  have key : ∀ j, ∫ x in K, F j x ≤ (∫ x in K, F j x ^ 3) ^ ((1:ℝ)/3) *
      (∫ x, (1:ℝ) ^ ((3:ℝ)/2) ∂(volume.restrict K)) ^ (1 / ((3:ℝ)/2)) := by
    intro j
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg hp
      (Filter.Eventually.of_forall (hFnonneg j))
      (Filter.Eventually.of_forall fun x => (show (0:ℝ) ≤ 1 by norm_num))
      (hmem j) hmem1
    simpa using h
  have hA : Tendsto (fun j => (∫ x in K, F j x ^ 3) ^ ((1:ℝ)/3)) atTop (nhds 0) :=
    tendsto_rpow_one_third hcube
  have hbound : Tendsto (fun j => (∫ x in K, F j x ^ 3) ^ ((1:ℝ)/3) *
      (∫ x, (1:ℝ) ^ ((3:ℝ)/2) ∂(volume.restrict K)) ^ (1 / ((3:ℝ)/2))) atTop (nhds 0) := by
    have h2 := hA.mul_const ((∫ x, (1:ℝ) ^ ((3:ℝ)/2) ∂(volume.restrict K)) ^ (1 / ((3:ℝ)/2)))
    simpa using h2
  exact squeeze_zero (fun j => integral_nonneg (hFnonneg j)) key hbound

/-- **The limiting step used by `jump_subseq`.**  If `F j` is continuous, nonnegative, bounded
by `2`, and dominated pointwise by `G j` with `G j` integrable and `∫_K G j → 0`, then
`∫_K F j → 0`. -/
theorem tendsto_integral_of_cube_le
    {K : Set ℝ} (hKfin : volume K < ⊤) (F G : ℕ → ℝ → ℝ)
    (hFcont : ∀ j, Continuous (F j))
    (hFnonneg : ∀ j, ∀ x, 0 ≤ F j x)
    (hFbound : ∀ j, ∀ x, F j x ≤ 2)
    (hGint : ∀ j, IntegrableOn (G j) K)
    (hFG : ∀ j, ∀ x, F j x ^ 3 ≤ G j x)
    (hGlim : Tendsto (fun j => ∫ x in K, G j x) atTop (nhds 0)) :
    Tendsto (fun j => ∫ x in K, F j x) atTop (nhds 0) := by
  refine integral_cube_le_implies hKfin F hFcont hFnonneg hFbound ?_
  refine squeeze_zero (fun j => integral_nonneg fun x => pow_nonneg (hFnonneg j x) 3)
    (fun j => ?_) hGlim
  have hF3int : Integrable (fun x => F j x ^ 3) (volume.restrict K) :=
    Integrable.mono (hGint j) ((hFcont j).pow 3).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (pow_nonneg (hFnonneg j x) 3)]
        exact le_trans (hFG j x) (le_abs_self (G j x)))
  exact integral_mono hF3int (hGint j) (fun x => hFG j x)

/-! ## The lemma -/

theorem jump_subseq (α lam : ℝ) {K : Set ℝ} (hK : MeasurableSet K) (hKfin : MeasureTheory.volume K < ⊤) (y : ℝ) (e : ℕ → ℝ) (he : ∀ j : ℕ, 0 < e j) (hK2 : Filter.Tendsto (fun j : ℕ => ∫ E in K, Work.TMComp.LocCantor.K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y) Filter.atTop (nhds 0)) (hint : ∀ j : ℕ, MeasureTheory.IntegrableOn (fun E : ℝ => Work.TMComp.LocCantor.K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y) K) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (fun j : ℕ => ∫ E in K, ‖Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam ((E : ℂ) + (e (φ j) : ℂ) * Complex.I) y) - Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam ((E : ℂ) - (e (φ j) : ℂ) * Complex.I) y)‖) Filter.atTop (nhds 0) := by
  refine ⟨id, strictMono_id, ?_⟩
  show Tendsto (fun j : ℕ => ∫ E in K,
      ‖cayley (Psi α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y)
        - cayley (Psi α lam ((E : ℂ) - (e j : ℂ) * Complex.I) y)‖) atTop (nhds 0)
  refine tendsto_integral_of_cube_le hKfin
    (fun j E => ‖cayley (Psi α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y)
        - cayley (Psi α lam ((E : ℂ) - (e j : ℂ) * Complex.I) y)‖)
    (fun j E => 8 * K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro j; exact continuous_jump_integrand α lam y (he j)
  · intro j E; positivity
  · intro j E; exact norm_cayley_sub_le_two α lam E (e j) (he j) y
  · intro j; exact (hint j).const_mul 8
  · intro j E; exact Psi_jump_cube_le_eight_K2 α lam E (e j) (he j) y
  · have h := hK2.const_mul 8
    have h2 : (fun j : ℕ => ∫ x in K, (8:ℝ) * K2 α lam ((x : ℂ) + (e j : ℂ) * Complex.I) y)
        = (fun j : ℕ => (8:ℝ) * ∫ x in K, K2 α lam ((x : ℂ) + (e j : ℂ) * Complex.I) y) := by
      funext j
      rw [integral_const_mul]
    rw [h2]
    simpa using h

end Work.TMComp.LocCantor
