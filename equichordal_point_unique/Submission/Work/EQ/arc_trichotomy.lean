import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.polarPt_basic

namespace Work.EQ

open Complex
open scoped Topology

/-- **Trichotomy.** For `ρ' ∈ (0,1)` and `ε ∈ (0,π)` there is `η > 0` such that a point
`P θ = polarPt (-(a/2)) (ρ₁ θ) θ` with `θ ∈ (0,π)`, of height `(P θ).im ≤ η` and with
`|(P θ).re + 1/2| ≤ ρ'`, must have `θ > π - ε`.

Proof: put `g θ = (P θ).re + 1/2 = (1-a)/2 + ρ₁ θ · cos θ`, so `g 0 = (1-a)/2 + ρ₁ 0 = 1 > ρ'`;
continuity at `0` gives `δ > 0` with `g θ > ρ'` for `|θ| < δ`.  For `θ ∈ [δ, π-ε]` (a compact
subinterval of `(0,π)`) the continuous function `θ ↦ (P θ).im = ρ₁ θ · sin θ` is `> 0`
pointwise, so has minimum `m > 0`.  Take `η = m/2`. -/
theorem arc_trichotomy {a : ℝ} {ρ₁ : ℝ → ℝ}
    (hcont : Continuous ρ₁) (hpos : ∀ θ, 0 < ρ₁ θ) (h0 : ρ₁ 0 = (1 + a) / 2) :
    ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∀ ε : ℝ, 0 < ε → ε < Real.pi →
      ∃ η : ℝ, 0 < η ∧ ∀ θ, 0 < θ → θ < Real.pi →
        (polarPt (-(a / 2)) (ρ₁ θ) θ).im ≤ η →
        |(polarPt (-(a / 2)) (ρ₁ θ) θ).re + 1 / 2| ≤ ρ' → Real.pi - ε < θ := by
  intro ρ' hρ'pos hρ'1 ε hεpos hεπ
  -- The point of the curve at angle `θ`, the height, and the abscissa function.
  set P : ℝ → ℂ := fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ with hP
  have hPcont : Continuous P := by
    rw [hP]; unfold polarPt; fun_prop
  have him_eq : ∀ θ, (P θ).im = ρ₁ θ * Real.sin θ := by
    intro θ; rw [hP]; exact (polarPt_basic (hpos θ)).1
  have hre_eq : ∀ θ, (P θ).re = -(a / 2) + ρ₁ θ * Real.cos θ := by
    intro θ
    change (polarPt (-(a / 2)) (ρ₁ θ) θ).re = -(a / 2) + ρ₁ θ * Real.cos θ
    have hexp : polarPt (-(a / 2)) (ρ₁ θ) θ =
        ((-(a / 2) + ρ₁ θ * Real.cos θ : ℝ) : ℂ) +
          ((ρ₁ θ * Real.sin θ : ℝ) : ℂ) * Complex.I := by
      rw [polarPt, Complex.exp_ofReal_mul_I]; push_cast; ring
    rw [hexp, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  set g : ℝ → ℝ := fun θ => (P θ).re + 1 / 2 with hg
  have hgcont : Continuous g := by
    rw [hg]; exact (Complex.continuous_re.comp hPcont).add continuous_const
  have hg0 : g 0 = 1 := by
    simp only [hg]
    rw [hre_eq 0, h0, Real.cos_zero, mul_one]
    ring
  have hg0gt : ρ' < g 0 := by rw [hg0]; exact hρ'1
  -- Continuity at `0` with `g 0 = 1 > ρ'` gives a neighbourhood `|θ| < δ` where `g θ > ρ'`.
  have hopen : IsOpen {x : ℝ | ρ' < x} := isOpen_lt continuous_const continuous_id
  have hev : ∀ᶠ θ in 𝓝 (0 : ℝ), ρ' < g θ :=
    hgcont.continuousAt (hopen.mem_nhds hg0gt)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  have hδ' : ∀ θ, 0 < θ → θ < δ → ρ' < g θ := by
    intro θ hθpos hθ
    apply hδ
    rw [Real.dist_eq, sub_zero, abs_of_pos hθpos]; exact hθ
  by_cases hle : δ ≤ Real.pi - ε
  · -- Nonempty compact piece `[δ, π-ε]`: the height is bounded below by a positive constant.
    obtain ⟨c, hc_mem, hc_min⟩ :=
      isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hle)
        (Complex.continuous_im.comp hPcont).continuousOn
    have hc_pos : 0 < (P c).im := by
      rw [him_eq c]
      exact mul_pos (hpos c)
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hc_mem.1, hδpos])
          (by linarith [hc_mem.2, hεπ]))
    refine ⟨(P c).im / 2, by linarith, ?_⟩
    intro θ hθ0 hθπ himθ hgθ
    by_contra hcon
    push Not at hcon
    rcases lt_or_ge θ δ with hlt | hge
    · -- `θ < δ` contradicts `g θ > ρ' ≥ |g θ|`.
      have hgt := hδ' θ hθ0 hlt
      have hab : g θ ≤ |g θ| := le_abs_self _
      have hgθ' : |g θ| ≤ ρ' := by simpa [hg] using hgθ
      linarith
    · -- `θ ∈ [δ, π-ε]` contradicts `(P θ).im ≥ (P c).im > (P c).im / 2 ≥ (P θ).im`.
      have hmem : θ ∈ Set.Icc δ (Real.pi - ε) := ⟨hge, hcon⟩
      have hcθ : (P c).im ≤ (P θ).im := (isMinOn_iff.mp hc_min) θ hmem
      have himθ' : (P θ).im ≤ (P c).im / 2 := himθ
      linarith
  · -- If `π - ε < δ`, every `θ ≤ π - ε` is `< δ` and excluded by the neighbourhood.
    refine ⟨1, one_pos, ?_⟩
    intro θ hθ0 hθπ himθ hgθ
    by_contra hcon
    push Not at hcon
    have hlt : θ < δ := by have := not_le.mp hle; linarith
    have hgt := hδ' θ hθ0 hlt
    have hab : g θ ≤ |g θ| := le_abs_self _
    have hgθ' : |g θ| ≤ ρ' := by simpa [hg] using hgθ
    linarith

end Work.EQ
