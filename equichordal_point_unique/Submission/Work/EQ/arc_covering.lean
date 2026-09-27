import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.polarPt_basic

namespace Work.EQ

/-- Real part of a polar point: `(polarPt c r θ).re = c + r cos θ`. -/
lemma arc_covering_polarPt_re (c r θ : ℝ) :
    (polarPt c r θ).re = c + r * Real.cos θ := by
  rw [polarPt, Complex.exp_ofReal_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one]
  ring

/-- Imaginary part of a polar point: `(polarPt c r θ).im = r sin θ`. -/
lemma arc_covering_polarPt_im (c r θ : ℝ) :
    (polarPt c r θ).im = r * Real.sin θ := by
  rw [polarPt, Complex.exp_ofReal_mul_I]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_mul]
  ring

/-- **Covering.** For `ρ' ∈ (0,1)` there is `η > 0` such that every height `y ∈ (0, η)` is
attained by a point `P θ = polarPt (-(a/2)) (ρ₁ θ) θ`, `θ ∈ (0,π)`, with
`|(P θ).re + 1/2| ≤ ρ'`.

Proof: `g θ := (P θ).re + 1/2` is continuous with `g π = (1-a)/2 - ρ₁ π = 0`, so
`{θ | |g θ| < ρ'/2}` is a neighbourhood of `π`; fix `c ∈ (0,π)` with `|g θ| < ρ'/2` on
`[c, π]`.  The continuous `h θ := (P θ).im = ρ₁ θ · sin θ` has `h c = ρ₁ c · sin c > 0` and
`h π = 0`, so every `y ∈ (0, h c)` is attained at some `θ ∈ (c, π)` by the intermediate value
theorem; take `η = h c`. -/
theorem arc_covering {a : ℝ} {ρ₁ : ℝ → ℝ}
    (hcont : Continuous ρ₁) (hpos : ∀ θ, 0 < ρ₁ θ) (hπ : ρ₁ Real.pi = (1 - a) / 2) :
    ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ η : ℝ, 0 < η ∧ ∀ y, 0 < y → y < η → ∃ θ, 0 < θ ∧ θ < Real.pi ∧
        (polarPt (-(a / 2)) (ρ₁ θ) θ).im = y ∧
        |(polarPt (-(a / 2)) (ρ₁ θ) θ).re + 1 / 2| ≤ ρ' := by
  intro ρ' hρ'pos hρ'lt
  -- the horizontal coordinate `g θ = (P θ).re + 1/2`
  set g : ℝ → ℝ := fun θ => (1 - a) / 2 + ρ₁ θ * Real.cos θ with hgdef
  have hgc : Continuous g := by
    rw [hgdef]
    exact continuous_const.add (hcont.mul Real.continuous_cos)
  have hgpi : g Real.pi = 0 := by
    simp only [hgdef, hπ, Real.cos_pi]
    ring
  have hhalf : 0 < ρ' / 2 := by linarith
  have hmem : Real.pi ∈ {θ | |g θ| < ρ' / 2} := by
    show |g Real.pi| < ρ' / 2
    rw [hgpi, abs_zero]
    exact hhalf
  have hopen : IsOpen {θ : ℝ | |g θ| < ρ' / 2} := isOpen_lt hgc.abs continuous_const
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hopen Real.pi hmem
  -- choose `d` small and `c = π - d ∈ (0, π)` with `|g θ| < ρ'/2` on `[c, π]`
  set d : ℝ := min (δ / 2) (Real.pi / 2) with hddef
  have hdpos : 0 < d := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hdle : d ≤ δ / 2 := min_le_left _ _
  have hdpi2 : d ≤ Real.pi / 2 := min_le_right _ _
  set c : ℝ := Real.pi - d with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith [Real.pi_pos]
  have hclt : c < Real.pi := by rw [hcdef]; linarith
  have hgbound : ∀ θ ∈ Set.Icc c Real.pi, |g θ| < ρ' / 2 := by
    intro θ hθ
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq]
    have hle : θ ≤ Real.pi := hθ.2
    have hge : c ≤ θ := hθ.1
    have hcd : Real.pi - d ≤ θ := by rw [hcdef] at hge; exact hge
    rw [abs_of_nonpos (by linarith : θ - Real.pi ≤ 0)]
    linarith
  -- the vertical coordinate `h θ = (P θ).im`
  set h : ℝ → ℝ := fun θ => ρ₁ θ * Real.sin θ with hhdef
  have hhc : Continuous h := by
    rw [hhdef]
    exact hcont.mul Real.continuous_sin
  have hhcpos : 0 < h c := by
    rw [hhdef]
    exact mul_pos (hpos c) (Real.sin_pos_of_pos_of_lt_pi hcpos hclt)
  have hhpi : h Real.pi = 0 := by
    simp only [hhdef, Real.sin_pi, mul_zero]
  refine ⟨h c, hhcpos, ?_⟩
  intro y hypos hylt
  have hmem2 : y ∈ Set.Ioo (h Real.pi) (h c) := by
    rw [hhpi]
    exact ⟨hypos, hylt⟩
  obtain ⟨θ, hθmem, hθeq⟩ :=
    intermediate_value_Ioo' (le_of_lt hclt) hhc.continuousOn hmem2
  have hθeq' : ρ₁ θ * Real.sin θ = y := by simpa only [hhdef] using hθeq
  refine ⟨θ, ?_, ?_, ?_, ?_⟩
  · linarith [hθmem.1, hcpos]
  · exact hθmem.2
  · rw [arc_covering_polarPt_im]
    exact hθeq'
  · have hre : (polarPt (-(a / 2)) (ρ₁ θ) θ).re + 1 / 2 = g θ := by
      rw [arc_covering_polarPt_re, hgdef]
      simp only []
      ring
    rw [hre]
    have hb := hgbound θ (Set.Ioo_subset_Icc_self hθmem)
    linarith

end Work.EQ
