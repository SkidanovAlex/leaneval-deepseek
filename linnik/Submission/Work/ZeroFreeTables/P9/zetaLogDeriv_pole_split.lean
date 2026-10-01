/-
# `Work.ZeroFreeTables.P9.zetaLogDeriv_pole_split`

The logarithmic derivative of `ζ` is bounded above by the contribution of its pole, up to a
constant, on the rectangle `{1 < Re s ≤ 2, |Im s| ≤ 4}`:

  `∃ C, 0 < C ∧ ∀ s, 1 < re s → re s ≤ 2 → |im s| ≤ 4 → (-logDeriv ζ s).re ≤ (1/(s-1)).re + C`.

Math.  For `Re s > 1` put `φ(s) = (s-1)ζ(s)`.  Then `φ` is holomorphic and nonzero on a
neighbourhood of the closed rectangle `1 ≤ Re s ≤ 2`, `|Im s| ≤ 4` (the only delicate point is
`s = 1`, where `φ` has the removable extension `ψ/Γℝ` with `ψ(s) = (s-1)Λ₀(s) - (s-1)/s + 1` and
`ψ(1) = Γℝ(1) = 1`), and

  `-logDeriv ζ s = -(logDeriv φ s) + 1/(s-1)`.

Hence `(-logDeriv ζ s).re - (1/(s-1)).re = (-logDeriv φ s).re`, which is a continuous function of
`s` on the (compact) closed rectangle, so it is bounded above by a constant `C`.  The theorem
follows with `|C| + 1`.
-/
import Mathlib

open Complex Set Filter
open scoped Topology

namespace Work.ZeroFreeTables.P9

noncomputable section

/-- The closed rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ 4}` on which everything takes place. -/
private def zetaRect : Set ℂ := {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ 4}

/-- The holomorphic extension of `(s-1)ζ(s)` across `s = 1`: for `s ≠ 0, 1` it equals
`(s-1)Λ(s)`, with `Λ = completedRiemannZeta`. -/
private def psi (s : ℂ) : ℂ := (s - 1) * completedRiemannZeta₀ s - (s - 1) / s + 1

/-- `(s-1)ζ(s)`, extended holomorphically across the pole `s = 1`. -/
private def phi (s : ℂ) : ℂ := psi s / Gammaℝ s

private lemma isCompact_zetaRect : IsCompact zetaRect := by
  have h : zetaRect = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) '' (Icc 1 2 ×ˢ Icc (-4:ℝ) 4) := by
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

private lemma differentiableOn_psi : DifferentiableOn ℂ psi {0}ᶜ := by
  have hΛ : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (z - 1) * completedRiemannZeta₀ z) s :=
    (differentiableAt_id.sub_const 1).mul hΛ.differentiableAt
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (z - 1) / z) s :=
    (differentiableAt_id.sub_const 1).div differentiableAt_id hs
  exact ((h1.sub h2).add_const 1).differentiableWithinAt

private lemma analyticOn_phi : AnalyticOnNhd ℂ phi {0}ᶜ := by
  have hG : DifferentiableOn ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) {0}ᶜ :=
    differentiable_Gammaℝ_inv.differentiableOn
  have h : phi = psi * fun s : ℂ => (Gammaℝ s)⁻¹ := rfl
  rw [h]
  exact (differentiableOn_psi.mul hG).analyticOnNhd isOpen_compl_singleton

/-- Away from the removable point `s = 1` the extension `φ` is literally `(s-1)ζ(s)`. -/
private lemma phi_eq (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) : phi s = (s - 1) * riemannZeta s := by
  have hΛ : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    completedRiemannZeta_eq s
  have hζ : riemannZeta s = completedRiemannZeta s / Gammaℝ s := riemannZeta_def_of_ne_zero h0
  rw [hζ, hΛ]
  unfold phi psi
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

private lemma phi_ne_zero (s : ℂ) (hs : s ∈ zetaRect) : phi s ≠ 0 := by
  obtain ⟨h1, -, -⟩ := hs
  rcases eq_or_ne s 1 with h | h
  · subst h
    simp [phi, psi, Gammaℝ_one]
  · rw [phi_eq s (by rintro rfl; exact absurd h1 (by norm_num)) h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re h1)

/-- The logarithmic derivative of `ζ` differs from that of `φ` by the pole term `1/(s-1)`. -/
private lemma logDeriv_phi_eq (s : ℂ) (hs : 1 < s.re) :
    logDeriv phi s = 1 / (s - 1) + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hev : phi =ᶠ[𝓝 s] (fun t => (t - 1) * riemannZeta t) := by
    filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with t ht0 ht1
    exact phi_eq t ht0 ht1
  rw [(logDeriv_congr_nhds hev).self_of_nhds]
  have hkey := logDeriv_mul (f := fun t : ℂ => t - 1) (g := riemannZeta) s
    (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_lt_re hs)
    (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hs1)
  erw [hkey]
  have hder : deriv (fun t : ℂ => t - 1) s = 1 := by
    rw [deriv_sub_const, deriv_id'']
  rw [logDeriv_apply, hder]

theorem zetaLogDeriv_pole_split :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 4 →
      (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C := by
  have hRsub : zetaRect ⊆ {0}ᶜ := by
    intro s hs h0
    obtain ⟨h1, -, -⟩ := hs
    rw [h0] at h1
    norm_num at h1
  have hcont : ContinuousOn (fun s : ℂ => (-logDeriv phi s).re) zetaRect := by
    have hd : ContinuousOn (deriv phi) zetaRect := analyticOn_phi.deriv.continuousOn.mono hRsub
    have hp : ContinuousOn phi zetaRect := analyticOn_phi.continuousOn.mono hRsub
    have hlg : ContinuousOn (logDeriv phi) zetaRect :=
      hd.div hp (fun s hs => phi_ne_zero s hs)
    have hre : ContinuousOn (fun s : ℂ => (logDeriv phi s).re) zetaRect :=
      Complex.continuous_re.comp_continuousOn hlg
    have hneg : ContinuousOn (fun s : ℂ => -(logDeriv phi s).re) zetaRect := hre.neg
    simpa only [Complex.neg_re] using hneg
  obtain ⟨C₁, hC₁⟩ := isCompact_zetaRect.bddAbove_image hcont
  refine ⟨|C₁| + 1, by positivity, ?_⟩
  intro s h1 h2 h3
  have hs : s ∈ zetaRect := ⟨le_of_lt h1, h2, h3⟩
  have hbound : (-logDeriv phi s).re ≤ |C₁| + 1 := by
    have hmem : (-logDeriv phi s).re ∈ (fun s : ℂ => (-logDeriv phi s).re) '' zetaRect :=
      mem_image_of_mem _ hs
    have hle := hC₁ hmem
    have hC : C₁ ≤ |C₁| + 1 := by
      have h := abs_nonneg C₁; nlinarith [le_abs_self C₁]
    linarith
  have hrew : (-logDeriv riemannZeta s).re
      = (1 / (s - 1)).re + (-logDeriv phi s).re := by
    have h2' : -logDeriv riemannZeta s = 1 / (s - 1) - logDeriv phi s := by
      rw [logDeriv_phi_eq s h1]; ring
    rw [h2', Complex.sub_re, Complex.neg_re]
    ring
  rw [hrew]
  linarith

end

end Work.ZeroFreeTables.P9
