import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs

/-!
# Shared vocabulary for the uniform near-cut separation inequality

This module collects the definitions used by `separation_ineq_nearCut` and by the auxiliary
lemmas it is built from:

* the two *fixed* elementary cutoffs `cutPhi` (a left step at scale `1`) and `cutPsi` (a right
  step at scale `1`), together with the identity `nearCut a b x = cutPhi (x/a) * cutPsi (x/b)`;
* the dyadic partition bump `dyadEta` and the smooth step `dyadStep` it is built from;
* the "chirped cutoff" `chat a b α x = nearCut a b x * |x|^{iα}` and its rescaled normalisation
  `fcut ε α u = cutPhi u * cutPsi (ε*u) * |u|^{iα}`.
-/

namespace Work.FIArea4.Vflip.Vfd

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-! ## The two elementary cutoffs -/

/-- The (fixed) left cutoff `Φ(u) = 1` for `|u| ≥ 1`, `= 0` for `|u| ≤ 1/2`. -/
def cutPhi (u : ℝ) : ℝ := Real.smoothTransition (4 * u ^ 2 - 1)

/-- The (fixed) right cutoff `Ψ(s) = 1` for `s ^ 2 ≤ 3`, `= 0` for `s ^ 2 ≥ 4`. -/
def cutPsi (s : ℝ) : ℝ := Real.smoothTransition (4 - s ^ 2)

/-- The fixed smooth step `t ↦ st(t-1)`: `0` for `t ≤ 1`, `1` for `t ≥ 2`. -/
def dyadStep (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

/-- The dyadic partition bump `η(t) = st(2t-1) - st(t-1)`: nonnegative, supported in `[1/2,2]`,
and `∑_{j ∈ ℤ} η(v / 2^j) = 1` for every `v > 0`. -/
def dyadEta (t : ℝ) : ℝ := dyadStep (2 * t) - dyadStep t

/-- The chirp `u ↦ exp(iα log |u|)` (written in exponential form). -/
def chirp (α u : ℝ) : ℂ := Complex.exp (((α * Real.log |u| : ℝ) : ℂ) * Complex.I)

/-- The chirped cutoff `chat a b α x = nearCut a b x · |x|^{iα}`. -/
def chat (a b α : ℝ) : ℝ → ℂ :=
  fun x => ((nearCut a b x : ℝ) : ℂ) * (((|x| : ℝ) : ℂ) ^ (Complex.I * (α : ℂ)))

/-- The rescaled normalisation of `chat`: `fcut ε α u = cutPhi u * cutPsi (ε*u) * |u|^{iα}`;
for `a, b > 0` one has `chat a b α x = a^{iα} · fcut (a/b) α (x/a)`. -/
def fcut (ε α : ℝ) : ℝ → ℂ :=
  fun u => ((cutPhi u : ℝ) : ℂ) * ((cutPsi (ε * u) : ℝ) : ℂ) *
    (((|u| : ℝ) : ℂ) ^ (Complex.I * (α : ℂ)))

/-! ## Elementary properties of the cutoffs -/

lemma cutPhi_nonneg (u : ℝ) : 0 ≤ cutPhi u := Real.smoothTransition.nonneg _
lemma cutPhi_le_one (u : ℝ) : cutPhi u ≤ 1 := Real.smoothTransition.le_one _
lemma cutPsi_nonneg (s : ℝ) : 0 ≤ cutPsi s := Real.smoothTransition.nonneg _
lemma cutPsi_le_one (s : ℝ) : cutPsi s ≤ 1 := Real.smoothTransition.le_one _

lemma contDiff_cutPhi : ContDiff ℝ (⊤ : ℕ∞) cutPhi := by
  unfold cutPhi; fun_prop

lemma contDiff_cutPsi : ContDiff ℝ (⊤ : ℕ∞) cutPsi := by
  unfold cutPsi; fun_prop

lemma contDiff_dyadStep : ContDiff ℝ (⊤ : ℕ∞) dyadStep := by
  unfold dyadStep; fun_prop

lemma contDiff_dyadEta : ContDiff ℝ (⊤ : ℕ∞) dyadEta := by
  unfold dyadEta
  exact contDiff_dyadStep.comp (by fun_prop) |>.sub contDiff_dyadStep

lemma dyadStep_zero_of_le {t : ℝ} (h : t ≤ 1) : dyadStep t = 0 := by
  have h' : t - 1 ≤ 0 := by linarith
  simpa [dyadStep] using Real.smoothTransition.zero_of_nonpos h'

lemma dyadStep_one_of_le {t : ℝ} (h : 2 ≤ t) : dyadStep t = 1 := by
  have h' : (1 : ℝ) ≤ t - 1 := by linarith
  simpa [dyadStep] using Real.smoothTransition.one_of_one_le h'

/-- `dyadStep` is monotone. -/
lemma monotone_dyadStep : Monotone dyadStep := by
  intro x y hxy
  unfold dyadStep
  exact Real.smoothTransition.monotone (by linarith)

lemma dyadEta_nonneg (t : ℝ) : 0 ≤ dyadEta t := by
  unfold dyadEta dyadStep
  rcases le_or_gt t 0 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 * t - 1 ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0)]
    norm_num
  · have : Real.smoothTransition (t - 1) ≤ Real.smoothTransition (2 * t - 1) :=
      Real.smoothTransition.monotone (by linarith)
    linarith

lemma dyadEta_eq_zero_of_le {t : ℝ} (h : t ≤ 1 / 2) : dyadEta t = 0 := by
  unfold dyadEta dyadStep
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 * t - 1 ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0)]
  norm_num

lemma dyadEta_eq_zero_of_ge {t : ℝ} (h : 2 ≤ t) : dyadEta t = 0 := by
  unfold dyadEta dyadStep
  rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 2 * t - 1),
      Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ t - 1)]
  norm_num

/-- `dyadEta` is supported in `[1/2, 2]`. -/
lemma dyadEta_support {t : ℝ} (h : dyadEta t ≠ 0) : 1 / 2 ≤ t ∧ t ≤ 2 := by
  constructor
  · by_contra hc
    exact h (dyadEta_eq_zero_of_le (le_of_lt (not_le.mp hc)))
  · by_contra hc
    exact h (dyadEta_eq_zero_of_ge (le_of_lt (not_le.mp hc)))

lemma cutPhi_eq_one_of_one_le {u : ℝ} (h : 1 ≤ |u|) : cutPhi u = 1 := by
  have h2 : (1 : ℝ) ≤ u ^ 2 := by
    have h' := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h 2
    rw [sq_abs] at h'
    norm_num1 at h'
    exact h'
  unfold cutPhi
  exact Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 * u ^ 2 - 1)

lemma cutPhi_eq_zero_of_abs_le {u : ℝ} (h : |u| ≤ 1 / 2) : cutPhi u = 0 := by
  have h2 : u ^ 2 ≤ 1 / 4 := by
    have h' := pow_le_pow_left₀ (abs_nonneg u) h 2
    rw [sq_abs] at h'
    norm_num1 at h'
    exact h'
  unfold cutPhi
  exact Real.smoothTransition.zero_of_nonpos (by linarith : 4 * u ^ 2 - 1 ≤ 0)

lemma cutPsi_eq_one_of_sq_le {s : ℝ} (h : s ^ 2 ≤ 3) : cutPsi s = 1 := by
  unfold cutPsi
  exact Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 4 - s ^ 2)

lemma cutPsi_eq_zero_of_sq_ge {s : ℝ} (h : 4 ≤ s ^ 2) : cutPsi s = 0 := by
  unfold cutPsi
  exact Real.smoothTransition.zero_of_nonpos (by linarith : 4 - s ^ 2 ≤ 0)

/-- **The `nearCut` cutoffs are the rescaled fixed cutoffs**: for `a, b ≠ 0`,
`nearCut a b x = cutPhi (x / a) * cutPsi (x / b)`. -/
lemma nearCut_eq (a b x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    nearCut a b x = cutPhi (x / a) * cutPsi (x / b) := by
  unfold nearCut cutPhi cutPsi
  have h1 : (4 * x ^ 2 - a ^ 2) / a ^ 2 = 4 * (x / a) ^ 2 - 1 := by field_simp
  have h2 : (4 * b ^ 2 - x ^ 2) / b ^ 2 = 4 - (x / b) ^ 2 := by field_simp
  rw [h1, h2]

/-! ## The chirp, its norm and its derivative -/

lemma norm_chirp (α u : ℝ) : ‖chirp α u‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- The cpow form of the chirp agrees with `chirp` away from `0`. -/
lemma cpow_eq_chirp {α u : ℝ} (hu : u ≠ 0) :
    (((|u| : ℝ) : ℂ) ^ (Complex.I * (α : ℂ))) = chirp α u := by
  rw [chirp, Complex.cpow_def_of_ne_zero (by exact_mod_cast abs_ne_zero.mpr hu),
    ← Complex.ofReal_log (abs_nonneg u)]
  congr 1
  push_cast
  ring

lemma chirp_eq_cpow {α u : ℝ} (hu : u ≠ 0) :
    chirp α u = (((|u| : ℝ) : ℂ) ^ (Complex.I * (α : ℂ))) := (cpow_eq_chirp hu).symm

end

end Work.FIArea4.Vflip.Vfd
