/-
# `Work.ZeroFreeTables.XY.PrincipalSigma.ZetaPhiDefs`

Definitions shared by the proof that the logarithmic derivative of `ζ`, together with its
first two derivatives, is bounded by the contribution of the pole `s = 1` on the rectangle
`{1 ≤ Re s ≤ 4, |Im s| ≤ 5}`.

The function `zetaPhi s = (s-1)ζ(s)` is extended holomorphically across `s = 1` (it is the
entire completion `Λ₀`-based expression `(ψ s)/Γℝ s` with `ψ s = (s-1)Λ₀(s) - (s-1)/s + 1`,
`ψ(1) = Γℝ(1) = 1`).  Then `logDeriv ζ = logDeriv zetaPhi - 1/(s-1)` wherever `Re s > 1`,
which is the identity used to render the pole terms removable.
-/
import Mathlib

open Complex Set Filter
open scoped Topology

namespace Work.ZeroFreeTables.XY.PrincipalSigma

noncomputable section

/-- The closed rectangle `{1 ≤ Re s ≤ 4, |Im s| ≤ 5}`. -/
def zetaRect : Set ℂ := {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 4 ∧ |s.im| ≤ 5}

lemma isCompact_zetaRect : IsCompact zetaRect := by
  have h : zetaRect = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) '' (Icc 1 4 ×ˢ Icc (-5:ℝ) 5) := by
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

private def psi (s : ℂ) : ℂ := (s - 1) * completedRiemannZeta₀ s - (s - 1) / s + 1

/-- `(s-1)ζ(s)`, extended holomorphically across the pole `s = 1`. -/
def zetaPhi (s : ℂ) : ℂ := psi s / Gammaℝ s

private lemma differentiableOn_psi : DifferentiableOn ℂ psi {0}ᶜ := by
  have hΛ : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (z - 1) * completedRiemannZeta₀ z) s :=
    (differentiableAt_id.sub_const 1).mul hΛ.differentiableAt
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (z - 1) / z) s :=
    (differentiableAt_id.sub_const 1).div differentiableAt_id hs
  exact ((h1.sub h2).add_const 1).differentiableWithinAt

lemma analyticOnNhd_zetaPhi : AnalyticOnNhd ℂ zetaPhi {0}ᶜ := by
  have hG : DifferentiableOn ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) {0}ᶜ :=
    differentiable_Gammaℝ_inv.differentiableOn
  have h : zetaPhi = psi * fun s : ℂ => (Gammaℝ s)⁻¹ := rfl
  rw [h]
  exact (differentiableOn_psi.mul hG).analyticOnNhd isOpen_compl_singleton

/-- Away from `s = 0, 1` the extension `zetaPhi` is literally `(s-1)ζ(s)`. -/
lemma zetaPhi_eq (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) : zetaPhi s = (s - 1) * riemannZeta s := by
  have hΛ : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    completedRiemannZeta_eq s
  have hζ : riemannZeta s = completedRiemannZeta s / Gammaℝ s := riemannZeta_def_of_ne_zero h0
  rw [hζ, hΛ]
  unfold zetaPhi psi
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

/-- `zetaPhi` does not vanish on the closed half-plane `Re s ≥ 1`. -/
lemma zetaPhi_ne_zero (s : ℂ) (h1 : 1 ≤ s.re) : zetaPhi s ≠ 0 := by
  rcases eq_or_ne s 1 with h | h
  · subst h
    simp [zetaPhi, psi, Gammaℝ_one]
  · rw [zetaPhi_eq s (by rintro rfl; exact absurd h1 (by norm_num)) h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re h1)

/-- The logarithmic derivative of `ζ` differs from that of the entire function `zetaPhi` by the
pole term `1/(s-1)`. -/
lemma logDeriv_zetaPhi_eq (s : ℂ) (hs : 1 < s.re) :
    logDeriv zetaPhi s = 1 / (s - 1) + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hev : zetaPhi =ᶠ[𝓝 s] (fun t => (t - 1) * riemannZeta t) := by
    filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with t ht0 ht1
    exact zetaPhi_eq t ht0 ht1
  rw [(logDeriv_congr_nhds hev).self_of_nhds]
  have hkey := logDeriv_mul (f := fun t : ℂ => t - 1) (g := riemannZeta) s
    (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_lt_re hs)
    (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hs1)
  erw [hkey]
  have hder : deriv (fun t : ℂ => t - 1) s = 1 := by
    rw [deriv_sub_const, deriv_id'']
  rw [logDeriv_apply, hder]

/-- Reformulation of `logDeriv_zetaPhi_eq` with the logarithmic derivative of `ζ` isolated. -/
lemma logDeriv_riemannZeta_eq (s : ℂ) (hs : 1 < s.re) :
    logDeriv riemannZeta s = logDeriv zetaPhi s - 1 / (s - 1) := by
  rw [logDeriv_zetaPhi_eq s hs]; ring

/-- The `n`-th derivative of `t ↦ (t-1)⁻¹`. -/
lemma iteratedDeriv_inv_sub_one (n : ℕ) (s : ℂ) :
    iteratedDeriv n (fun t : ℂ => (t - 1)⁻¹) s
      = (-1) ^ n * (n.factorial : ℂ) * (s - 1) ^ (-1 - (n : ℤ)) := by
  rw [iteratedDeriv_eq_iterate]
  have h := iter_deriv_inv_linear_sub (𝕜 := ℂ) n 1 1
  simp only [one_mul] at h
  rw [h]
  simp

/-- An open neighbourhood of the rectangle on which `zetaPhi` is analytic and nonzero. -/
def zetaPhiGood : Set ℂ := {0}ᶜ ∩ zetaPhi ⁻¹' {0}ᶜ

lemma isOpen_zetaPhiGood : IsOpen zetaPhiGood :=
  analyticOnNhd_zetaPhi.continuousOn.isOpen_inter_preimage isOpen_compl_singleton
    isOpen_compl_singleton

lemma zetaRect_subset_good : zetaRect ⊆ zetaPhiGood := by
  intro s hs
  obtain ⟨h1, -, -⟩ := hs
  exact ⟨by rintro rfl; norm_num at h1, zetaPhi_ne_zero s h1⟩

/-- `logDeriv zetaPhi` is analytic on the neighbourhood `zetaPhiGood`. -/
lemma analyticOnNhd_logDeriv_zetaPhi : AnalyticOnNhd ℂ (logDeriv zetaPhi) zetaPhiGood := by
  have hphi : AnalyticOnNhd ℂ zetaPhi zetaPhiGood :=
    analyticOnNhd_zetaPhi.mono Set.inter_subset_left
  have hne : ∀ s ∈ zetaPhiGood, zetaPhi s ≠ 0 := fun s hs => hs.2
  exact hphi.deriv.div hphi hne

/-- `logDeriv zetaPhi` is analytic at every point with `Re s > 1`. -/
lemma analyticAt_logDeriv_zetaPhi (s : ℂ) (hs : 1 < s.re) :
    AnalyticAt ℂ (logDeriv zetaPhi) s :=
  analyticOnNhd_logDeriv_zetaPhi s
    ⟨by rintro rfl; norm_num at hs, zetaPhi_ne_zero s (le_of_lt hs)⟩

end

end Work.ZeroFreeTables.XY.PrincipalSigma
