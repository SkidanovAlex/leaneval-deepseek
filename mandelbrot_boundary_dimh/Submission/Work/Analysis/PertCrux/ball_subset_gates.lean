import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic

/-!
# PertCrux · `ball_subset_gates`

Elementary geometry of the two `§4.2` gates used by the perturbation layer.

`Work.Pert.Qp ξ α = MandelDim.Qreg (some ξ) (some (-ξ + 1/α))` is the *upper* gate: the set of
`w` with

* `ξ - |w.im| < w.re` (the horizontal cone condition at the vertex `ξ`), and
* `w.re + ξ - (1/α).re < |w.im - (1/α).im|` (the cone condition at the vertex `-ξ + 1/α`).

`MandelDim.Qreg (some (ξ : ℂ)) none` imposes only the first of these (the second vertex is
`none = -∞`, hence vacuous).

Both conditions are *open* and depend only on `w.re`, `|w.im|` and `|w.im - (1/α).im|`, each of
which changes by at most `R` when `w` ranges over the ball of radius `R` about `z`:
`|w.re - z.re| ≤ ‖w - z‖ < R` and `| |w.im - c| - |z.im - c| | ≤ |w.im - z.im| < R` for
`c = 0` and `c = (1/α).im`. Hence the cone conditions of `z`, with slack `2R`, put the whole
ball inside the gates — which is the content of `ball_subset_gates`.
-/

namespace Work.Analysis.PertCrux

open MandelDim Complex Set Metric

noncomputable section

/-- The two coordinate conditions of the upper gate `Qp ξ α` (see `Work.Pert.Qp_mem_iff`). -/
private lemma mem_Qp_iff {ξ : ℝ} {α w : ℂ} :
    w ∈ Work.Pert.Qp ξ α ↔
      (ξ - |w.im| < w.re ∧ w.re + ξ - (1 / α).re < |w.im - (1 / α).im|) := by
  unfold Work.Pert.Qp MandelDim.Qreg
  constructor
  · rintro ⟨hA, hB⟩
    have hA' := hA (ξ : ℂ) (by simp)
    have hB' := hB (-(ξ : ℂ) + 1 / α) (by simp)
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      at hA'
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, neg_zero, zero_add]
      at hB'
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor
    · intro b hb
      simp only [Option.mem_some_iff] at hb
      subst hb
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      linarith
    · intro b hb
      simp only [Option.mem_some_iff] at hb
      subst hb
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, neg_zero, zero_add]
      linarith

/-- The single coordinate condition of `Qreg (some ξ) none`: the cone at the vertex `ξ`. -/
private lemma mem_Qreg_some_none_iff {ξ : ℝ} {w : ℂ} :
    w ∈ MandelDim.Qreg (some (ξ : ℂ)) none ↔ ξ - |w.im| < w.re := by
  unfold MandelDim.Qreg
  constructor
  · intro h
    have hA' := h.1 (ξ : ℂ) (by simp)
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      at hA'
    linarith
  · intro h
    constructor
    · intro b hb
      simp only [Option.mem_some_iff] at hb
      subst hb
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      linarith
    · intro b hb
      exact absurd hb (by simp)

/-- **The gate ball lemma.** If the two cone conditions of the upper gate `Qp Ξ' α` hold at `z`
with a slack of `2R`, then the whole ball of radius `R` about `z` lies in that gate, and likewise
in the one-sided region `Qreg (some Ξ') none`.

The proof is the observation that both conditions are open and that, for `w` in the ball,
`z.re - R < w.re < z.re + R` and `|z.im - c| - R < |w.im - c|` for `c = 0` and `c = (1/α).im`. -/
theorem ball_subset_gates {Ξ' R : ℝ} {α z : ℂ} (hR : 0 ≤ R)
    (hcone : Ξ' + 2 * R < z.re + |z.im|)
    (hfar : z.re + Ξ' - (1 / α).re + 2 * R < |z.im - (1 / α).im|) :
    Metric.ball z R ⊆ Work.Pert.Qp Ξ' α ∧ Metric.ball z R ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none := by
  have _hR : (0 : ℝ) ≤ R := hR
  have key : ∀ w ∈ Metric.ball z R,
      Ξ' - |w.im| < w.re ∧ w.re + Ξ' - (1 / α).re < |w.im - (1 / α).im| := by
    intro w hw
    have hw' : ‖w - z‖ < R := by rwa [Metric.mem_ball, Complex.dist_eq] at hw
    have hre : |w.re - z.re| < R := by
      have h := Complex.abs_re_le_norm (w - z)
      rw [Complex.sub_re] at h
      exact lt_of_le_of_lt h hw'
    have him : |w.im - z.im| < R := by
      have h := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im] at h
      exact lt_of_le_of_lt h hw'
    constructor
    · -- `Ξ' < w.re + |w.im|`
      have h1 : z.re - R < w.re := by
        have := (abs_lt.mp hre).1
        linarith
      have h2 : |z.im| - R < |w.im| := by
        have h3 : |z.im| - |w.im| ≤ |z.im - w.im| := abs_sub_abs_le_abs_sub z.im w.im
        rw [abs_sub_comm z.im w.im] at h3
        linarith
      linarith
    · -- `w.re + Ξ' - (1/α).re < |w.im - (1/α).im|`
      have h1 : w.re < z.re + R := by
        have := (abs_lt.mp hre).2
        linarith
      have h2 : |z.im - (1 / α).im| - |w.im - z.im| ≤ |w.im - (1 / α).im| := by
        have h := abs_sub_abs_le_abs_sub (z.im - (1 / α).im) (-(w.im - z.im))
        have h2 : z.im - (1 / α).im - -(w.im - z.im) = w.im - (1 / α).im := by ring
        rw [h2, abs_neg] at h
        exact h
      linarith
  constructor
  · intro w hw
    exact (mem_Qp_iff).2 (key w hw)
  · intro w hw
    exact (mem_Qreg_some_none_iff).2 (key w hw).1

end

end Work.Analysis.PertCrux
