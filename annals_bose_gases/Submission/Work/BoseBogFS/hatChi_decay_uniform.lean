import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBogFS.Canonical
import Submission.Work.BoseBogFS.ChatChiFun
import Submission.Work.BoseBogFS.CloseFS
import Submission.Work.BoseBogFS.FsMatchEnvDefs
import Submission.Work.BoseBogFS.ViewRows
import Submission.Work.BoseBogFS.W1fun_mass_pos
import Submission.Work.BoseBogFS.bogOpBoundAtFSWith_of_honestRows
import Submission.Work.BoseBogFS.card_le_of_separated
import Submission.Work.BoseBogFS.chat_W1fun_pos_near_zero
import Submission.Work.BoseBogFS.chat_zero_eq_integral
import Submission.Work.BoseBogFS.continuous_chat
import Submission.Work.BoseBogFS.lhyEps_le_errSlot
import Submission.Work.BoseFixR.Rb5Lin.radial_fourier_sinc
import Submission.Work.BoseGateFS.TauRows
import Submission.Work.BoseK15.BoxInhabited
import Submission.Work.BoseK15.alphaCoef_eq_h
import Submission.Work.BoseK15.chi_small_of_decay
import Submission.Work.BoseK15.tauFun_lipschitz
import Submission.Work.BoseK15.tau_PH_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.hatChi_decay_uniform`

**The uniform decay of the `χ̂`-kernel of `RViewFS`**: there is an absolute constant `C`
with

`|E.hatChi k| ≤ C / (1 + ‖F.kmom k‖ * E.ell) ^ s`  for every mode `k`,

at every decay order `s`, uniformly over the whole view `RViewFS v h μ F T E gHat0`.

## Why the statement is true, and how the proof runs

The view pins the kernel to the **normalised** `χ̂`

`E.hatChi k = chat (χ_ℓ) (F.kmom k) / chat (χ_ℓ²) 0`,   `ℓ = E.ell = ell v μ`,

which for `ℓ > 0` is *exactly* the corpus `χ̂ = Work.BoseK15.corpusBox.hatChi` at the
scaled momentum `ℓ • k`:

* `chat (χ_ℓ) p = ℓ³ χ̂(ℓ • p)` (`Work.BoseBogFS.chat_chiFun_eq` (`ChatChiFun.lean`),
  `∫ χ_Λ e^{ikx} = ℓ³χ̂(ℓk)` of FS `eq:Commutator_general`);
* `chat (χ_ℓ²) 0 = ℓ³` (`Work.BoseFixR.chat_chiSq_zero`, FS's normalisation `∫χ² = 1`),

so the `ℓ³` factors cancel.  The corpus `χ̂` decays faster than any polynomial
(`Work.BoseK15.decay_cos_integral_smooth`: for a `C^∞` compactly supported `g` and every
order `m` there is `C ≥ 0` with `|∫ g·cos⟨p,·⟩| ≤ C/(1+‖p‖)^m`), and this is the estimate
we need after rescaling `‖ℓ • k‖ = ℓ‖k‖`.

Two degenerate points have to be handled, and they are the reason the statement is
*uniform* over `μ` (there is no positivity hypothesis on `μ` in `RViewFS`, and `ell v μ`
is a real power):

* `ell v μ ≥ 0` for **every** `μ`: `sideAt μ a = K_ℓ(μa)^{-1/2}` with
  `K_ℓ = (μa³)^{-3/646}`, and Mathlib's real power is nonnegative (for `x < 0` and the
  half-integer exponent the `cos (π·(-1/2))` factor vanishes, so `x^{-1/2} = 0`; this is
  `rpow_neg_half_nonneg`);
* `ℓ = 0`: then `χ_ℓ = χ(·/ℓ)` degenerates to the constant `χ(0)`, and its normaliser
  `chat (χ_ℓ²) 0` is `0` (the `chat`-transform of a nonzero constant on `ℝ³` vanishes,
  the integrand having constant modulus), so `E.hatChi k = _ / 0 = 0` and the bound is
  trivial.

Everything used below is fully proved: the helper evaluations `sideAt_nonneg`,
`chat_const_zero`, `chiFun_zero` are proved here from scratch (they also occur in
`Work.BoseBoxFock.honestEnvBessel`, whose *separate* target is a false statement recorded
verbatim there, so that module is deliberately not imported).  All three imported source
modules (`ChiPin`, `CanonViewFalse`, `ChiReg_corpus`) are complete.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The degenerate evaluations of the box side and of `chat` -/

/-- Mathlib's real power `x^{-1/2}` is nonnegative for every real `x`: for `x < 0` the
definition `x^y = exp (y log|x|) cos (πy)` has `cos (π·(-1/2)) = 0`. -/
lemma rpow_neg_half_nonneg (x : ℝ) : 0 ≤ x ^ (-(1 / 2 : ℝ)) := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.rpow_def_of_neg h]
    have h1 : -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) := by ring
    rw [h1, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  · subst h
    rw [Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)]
  · exact Real.rpow_nonneg h.le _

/-- `K_ℓ = (μa³)^{-3/646} ≥ 0` for every diluteness (the exponent `(-3/2)/323` has
`|(-3/2)/323 · π| ≤ π/2`, so the cosine factor of `rpow_def_of_neg` is nonnegative). -/
lemma fsXp_neg_three_half_nonneg (t : ℝ) : 0 ≤ Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) := by
  rw [Work.BoseBox.fsXp]
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.rpow_def_of_neg h]
    refine mul_nonneg (Real.exp_nonneg _) (Real.cos_nonneg_of_mem_Icc ?_)
    have hb : |((-(3 / 2 : ℝ)) / 323) * Real.pi| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      have h1 : |( (-(3 / 2 : ℝ)) / 323 : ℝ)| ≤ 1 / 2 := by norm_num
      calc |( (-(3 / 2 : ℝ)) / 323 : ℝ)| * Real.pi ≤ (1 / 2) * Real.pi :=
            mul_le_mul_of_nonneg_right h1 Real.pi_pos.le
        _ = Real.pi / 2 := by ring
    exact abs_le.mp hb
  · subst h
    rw [Real.zero_rpow (by norm_num : (-(3 / 2 : ℝ) / 323) ≠ 0)]
  · exact Real.rpow_nonneg h.le _

/-- **`sideAt μ a ≥ 0` for all `μ, a`** — in particular `E.ell ≥ 0` under `RViewFS`,
with no positivity hypothesis on `μ`. -/
lemma sideAt_nonneg (μ a : ℝ) : 0 ≤ Work.BoseBox.sideAt μ a := by
  rw [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  exact mul_nonneg (fsXp_neg_three_half_nonneg (μ * a ^ 3)) (rpow_neg_half_nonneg (μ * a))

/-- The Lebesgue integral of a constant on `ℝ³` vanishes.  (Proof from the change of
variables `x ↦ 0 • x`, which makes the integral equal to `0 • ∫ c`; this avoids any
integrability discussion.) -/
lemma integral_const_complex (c : ℂ) : (∫ _x : ℝ³, c) = 0 := by
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure ℝ³))
    (f := fun _ : ℝ³ => c) (R := (0 : ℝ))
  simpa using h

/-- **`chat` of a constant vanishes**: the integrand has constant modulus `|c|` on the
unbounded `ℝ³`. -/
lemma chat_const_zero (c : ℝ) : Work.BoseFixR.chat (fun _ : ℝ³ => c) 0 = 0 := by
  rw [Work.BoseFixR.chat, Submission.BoseGases.kinFT]
  rw [show (∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ 0 y : ℂ))) * ((c : ℝ) : ℂ))
        = ∫ _y : ℝ³, ((c : ℝ) : ℂ) from by
      apply integral_congr_ae; filter_upwards with y; simp]
  rw [integral_const_complex, Complex.zero_re]

/-- At `ℓ = 0` the scaled bump `χ_ℓ` degenerates to the constant `χ(0)`. -/
lemma chiFun_zero : Work.BoseFixR.chiFun 0 = fun _ : ℝ³ => Submission.BoseGases.chi 0 := by
  funext x
  simp [Work.BoseFixR.chiFun, Submission.BoseGases.chiScale]

/-- **The normaliser at `ℓ = 0` vanishes** (`χ_0²` is the nonzero constant `χ(0)²`), so
the pinned kernel is `_ / 0 = 0` there. -/
lemma chat_chiFun_sq_zero_zero :
    Work.BoseFixR.chat (fun z : ℝ³ => Work.BoseFixR.chiFun 0 z ^ 2) 0 = 0 := by
  have h : (fun z : ℝ³ => Work.BoseFixR.chiFun 0 z ^ 2)
      = fun _ : ℝ³ => (Submission.BoseGases.chi 0) ^ 2 := by
    funext z
    simp [chiFun_zero]
  rw [h, chat_const_zero]

/-! ## 2. The uniform decay -/

theorem hatChi_decay_uniform (s : ℕ) {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
      (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
      (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ),
      Work.BoseBogFS.RViewFS v h μ F T E gHat0 → ∀ k : Mode,
      |E.hatChi k| ≤ C / (1 + ‖F.kmom k‖ * E.ell) ^ s := by
  -- the decay of the corpus bump `χ`: `|χ̂(p)| ≤ C/(1+‖p‖)^s`
  obtain ⟨C, hC0, hC⟩ := Work.BoseK15.decay_cos_integral_smooth
    (fun x : ℝ³ => Submission.BoseGases.chi x) Submission.BoseGases.chi_contDiff
    Submission.BoseGases.chi_hasCompactSupport s
  refine ⟨C, hC0, ?_⟩
  intro v h μ F T E gHat0 hview k
  have hdec : ∀ p : ℝ³, |Work.BoseK15.corpusBox.hatChi p| ≤ C / (1 + ‖p‖) ^ s := by
    intro p
    simpa only [Work.BoseB4.BoxData.hatChi, Work.BoseK15.corpusBox_chi] using hC p
  -- put `ell = ell v μ` everywhere
  rw [hview.ell_eq]
  have hℓ : 0 ≤ Work.BoseFixR.ell v μ := by
    rw [Work.BoseFixR.ell]
    exact sideAt_nonneg μ (_root_.BoseGases.a v)
  have hpin : E.hatChi k
      = Work.BoseFixR.chat (Work.BoseFixR.chiFun (Work.BoseFixR.ell v μ)) (F.kmom k)
        / Work.BoseFixR.chat (fun z => Work.BoseFixR.chiFun (Work.BoseFixR.ell v μ) z ^ 2)
            0 := by
    rw [hview.hatChi_pin]
  rcases eq_or_lt_of_le hℓ with h0 | hpos
  · -- degenerate box side: the normaliser vanishes and the kernel is `0`
    rw [hpin, ← h0, chat_chiFun_sq_zero_zero, div_zero, abs_zero]
    simp only [mul_zero, add_zero, one_pow, div_one]
    exact hC0
  · -- `ℓ > 0`: the normalised `χ̂` is the corpus `χ̂` at `ℓ • k`
    have hnum := chat_chiFun_eq (Work.BoseFixR.ell v μ) hpos (F.kmom k)
    have hden := Work.BoseFixR.chat_chiSq_zero hpos
    rw [hpin, hnum, hden, mul_div_cancel_left₀ _ (pow_ne_zero 3 (ne_of_gt hpos))]
    have hq : ‖(Work.BoseFixR.ell v μ) • F.kmom k‖
        = ‖F.kmom k‖ * Work.BoseFixR.ell v μ := by
      rw [norm_smul, Real.norm_of_nonneg hℓ, mul_comm]
    rw [← hq]
    exact hdec _

end Work.BoseBogFS
