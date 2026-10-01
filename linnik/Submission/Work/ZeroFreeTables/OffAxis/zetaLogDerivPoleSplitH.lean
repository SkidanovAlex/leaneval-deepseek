import Mathlib
import Submission.Work.ZeroFreeTables.P9.zetaExtPoleLemmas

/-!
# `Work.ZeroFreeTables.OffAxis.zetaLogDerivPoleSplitH`

The logarithmic derivative of `ζ` is bounded above by the contribution of its pole, up to an
additive constant, on the strip `{1 < Re s ≤ 2, |Im s| ≤ T}` for any `T ≥ 0`:

  `∃ C, 0 < C ∧ ∀ s, 1 < re s → re s ≤ 2 → |im s| ≤ T → (-logDeriv ζ s).re ≤ (1/(s-1)).re + C`.

Math.  For `Re s > 1` put `φ(s) = (s-1)ζ(s)` (the holomorphic extension `zetaExtPole`).  Then `φ`
is holomorphic on `{0}ᶜ` and nonzero on the closed rectangle `1 ≤ Re s ≤ 2, |Im s| ≤ T`: the only
delicate point is `s = 1`, where `φ(1) = 1`, and elsewhere `φ(s) = (s-1)ζ(s)` with `ζ(s) ≠ 0` for
`Re s ≥ 1`.  Moreover

  `logDeriv φ s = 1/(s-1) + logDeriv ζ s`   for `Re s > 1`,

so `(-logDeriv ζ s).re - (1/(s-1)).re = (-logDeriv φ s).re`, which is a continuous function of `s`
on the (compact) closed rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ T}`, hence bounded above by a constant.
The theorem follows with `|C₁| + 1`.

This is the `|Im s| ≤ 4` lemma `Work.ZeroFreeTables.P9.zetaLogDeriv_pole_split` generalised to an
arbitrary height bound `T`.
-/
open Complex Set Filter
open scoped Topology
open Work.ZeroFreeTables.P9

namespace Work.ZeroFreeTables.OffAxis

noncomputable section

/-- The closed rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ T}`. -/
private def zetaRectT (T : ℝ) : Set ℂ := {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ T}

/-- The closed rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ T}` is compact. -/
private lemma isCompact_zetaRectT (T : ℝ) : IsCompact (zetaRectT T) := by
  have h : zetaRectT T = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I)
      '' (Icc 1 2 ×ˢ Icc (-T) T) := by
    ext s
    constructor
    · intro ⟨h1, h2, h3⟩
      refine ⟨(s.re, s.im), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · rw [abs_le] at h3; exact ⟨h3.1, h3.2⟩
      · simp
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
      refine ⟨?_, ?_, ?_⟩
      · simpa using hp1
      · simpa using hp2
      · simp only [ofReal_re, ofReal_im, add_im, mul_I_im, zero_add]
        exact abs_le.mpr ⟨hp3, hp4⟩
  rw [h]
  exact (isCompact_Icc.prod isCompact_Icc).image (by continuity)

/-- The extension `zetaExtPole` of `(s-1)ζ(s)` is nonzero for `1 ≤ Re s ≤ 2`. -/
private lemma zetaExtPole_ne_zero_rect (s : ℂ) (h1 : 1 ≤ s.re) (h2 : s.re ≤ 2) :
    zetaExtPole s ≠ 0 := by
  rcases eq_or_ne s 1 with h | h
  · subst h
    simp [zetaExtPole, psiExtPole, Gammaℝ_one]
  · rw [zetaExtPole_eq s (by rintro rfl; norm_num at h1) h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re h1)

/-- The closed rectangle sits inside the open set `zetaExtU` where `zetaExtPole` is analytic and
nonzero. -/
private lemma zetaRectT_subset_zetaExtU (T : ℝ) : zetaRectT T ⊆ zetaExtU := by
  intro z hz
  have hz' : 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T := hz
  refine ⟨?_, zetaExtPole_ne_zero_rect z hz'.1 hz'.2.1⟩
  intro h0
  have hre : z.re = 0 := by rw [h0]; simp
  linarith [hz'.1]

theorem zetaLogDerivPoleSplitH (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ T →
      (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C := by
  have hKU := zetaRectT_subset_zetaExtU T
  -- `-logDeriv φ` is continuous on the compact rectangle
  have hcont : ContinuousOn (fun s : ℂ => (-logDeriv zetaExtPole s).re) (zetaRectT T) := by
    have hd : ContinuousOn (deriv zetaExtPole) (zetaRectT T) :=
      analyticOn_zetaExtPole_of_U.deriv.continuousOn.mono hKU
    have hp : ContinuousOn zetaExtPole (zetaRectT T) :=
      analyticOn_zetaExtPole_of_U.continuousOn.mono hKU
    have hlg : ContinuousOn (logDeriv zetaExtPole) (zetaRectT T) :=
      hd.div hp (fun s hs => zetaExtPole_ne_zero_on_U s (hKU hs))
    have hre : ContinuousOn (fun s : ℂ => (logDeriv zetaExtPole s).re) (zetaRectT T) :=
      Complex.continuous_re.comp_continuousOn hlg
    have hneg : ContinuousOn (fun s : ℂ => -(logDeriv zetaExtPole s).re) (zetaRectT T) := hre.neg
    simpa only [Complex.neg_re] using hneg
  obtain ⟨C₁, hC₁⟩ := (isCompact_zetaRectT T).bddAbove_image hcont
  refine ⟨|C₁| + 1, by positivity, ?_⟩
  intro s h1 h2 h3
  have hs : s ∈ zetaRectT T := ⟨le_of_lt h1, h2, h3⟩
  have hbound : (-logDeriv zetaExtPole s).re ≤ |C₁| + 1 := by
    have hmem : (-logDeriv zetaExtPole s).re ∈
        (fun s : ℂ => (-logDeriv zetaExtPole s).re) '' (zetaRectT T) := mem_image_of_mem _ hs
    have hle := hC₁ hmem
    have hC : C₁ ≤ |C₁| + 1 := by have h := le_abs_self C₁; linarith
    linarith
  have hrew : (-logDeriv riemannZeta s).re
      = (1 / (s - 1)).re + (-logDeriv zetaExtPole s).re := by
    have h2' : -logDeriv riemannZeta s = 1 / (s - 1) - logDeriv zetaExtPole s := by
      rw [logDeriv_zetaExtPole_eq s h1]; ring
    rw [h2', Complex.sub_re, Complex.neg_re]
    ring
  rw [hrew]
  linarith

end

end Work.ZeroFreeTables.OffAxis
