import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- Membership in the rational box `boxOf a b ρ` in terms of the (real) coordinates:
`z` lies in the box iff its real part is within `ρ` of `a` and its imaginary part is within
`ρ` of `-b`. -/
private lemma mem_boxOf_iff (a b ρ : ℚ) (z : ℂ) :
    (boxOf a b ρ).mem z ↔ |z.re - (a : ℝ)| ≤ (ρ : ℝ) ∧ |z.im + (b : ℝ)| ≤ (ρ : ℝ) := by
  rw [Box.mem]
  simp only [boxOf_xl, boxOf_xh, boxOf_yl, boxOf_yh]
  push_cast
  constructor
  · intro ⟨h1, h2, h3, h4⟩
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · intro ⟨h1, h2⟩
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The elementary separation step: if `a * b ≤ ρ * s` with `s ≤ max a b` and `0 ≤ ρ`, then at
least one of `a`, `b` is at most `ρ`.  (Here `a`, `b` are the distances from a point `v` to
`w₀` and to `-w₀`, `s` a lower bound for `‖w₀‖`, and `ρ` the half-width of the target box.) -/
private lemma key_disj (a b ρ s : ℝ) (hρ : 0 ≤ ρ)
    (hab : a * b ≤ ρ * s) (hmax : s ≤ max a b) : a ≤ ρ ∨ b ≤ ρ := by
  rcases le_max_iff.mp hmax with h | h
  · by_cases ha : a ≤ 0
    · exact Or.inl (le_trans ha hρ)
    · refine Or.inr ?_
      have hapos : 0 < a := not_le.mp ha
      have h1 : b * a ≤ ρ * a := by
        calc b * a = a * b := mul_comm b a
          _ ≤ ρ * s := hab
          _ ≤ ρ * a := mul_le_mul_of_nonneg_left h hρ
      exact le_of_mul_le_mul_right h1 hapos
  · by_cases hb : b ≤ 0
    · exact Or.inr (le_trans hb hρ)
    · refine Or.inl ?_
      have hbpos : 0 < b := not_le.mp hb
      have h1 : a * b ≤ ρ * b := le_trans hab (mul_le_mul_of_nonneg_left h hρ)
      exact le_of_mul_le_mul_right h1 hbpos

/-- **The square-root step of the certified ray chain.**

If `w₀ = w0re + i w0im`, `‖w₀‖ ≥ s ≥ 0`, `0 ≤ ρ`, and for every `q ∈ Bq`, `c ∈ X` the
quantity `(q - c) - w₀²` is bounded by `R ≤ ρ · s`, then the two-valued preimage of `Bq`
under `T_c(u) = conj u ^ 2 + c` (with `c` ranging over `X`) is covered by the rational box
`boxOf w0re w0im ρ` of half-width `ρ` around `conj w₀` and its reflection.

Indeed, for a preimage `u` with `T_c u = q` one has `q - c = conj(u)²`, hence, writing
`v = conj u`, the product `‖v - w₀‖ · ‖v + w₀‖ = ‖v² - w₀²‖ ≤ R ≤ ρ s`.  Since
`max (‖v - w₀‖) (‖v + w₀‖) ≥ ‖w₀‖ ≥ s`, at least one of the two factors is `≤ ρ`; the
corresponding factor being small gives `u ∈ boxOf w0re w0im ρ` or `-u ∈ boxOf w0re w0im ρ`. -/
theorem sqrtCover_of_bounds (Bq X : Work.SeedCertRay.Box) (w0re w0im s R ρ : ℚ) (hs : 0 ≤ s) (hρ : 0 ≤ ρ) (h1 : (s : ℝ) ^ 2 ≤ (w0re : ℝ) ^ 2 + (w0im : ℝ) ^ 2) (h2 : (R : ℝ) ≤ (ρ : ℝ) * (s : ℝ)) (hZ : ∀ q c : ℂ, Bq.mem q → X.mem c → ‖(q - c) - (((w0re : ℝ) : ℂ) + ((w0im : ℝ) : ℂ) * Complex.I) ^ 2‖ ≤ (R : ℝ)) : Work.SeedCertRay.SqrtCover Bq X (Work.SeedCertRay.boxOf w0re w0im ρ) := by
  intro q c u hq hc hTu
  set w0 : ℂ := ((w0re : ℝ) : ℂ) + ((w0im : ℝ) : ℂ) * Complex.I with hw0
  have hw0re : w0.re = (w0re : ℝ) := by rw [hw0]; simp
  have hw0im : w0.im = (w0im : ℝ) := by rw [hw0]; simp
  -- `T_c u = q` gives `q - c = conj u ^ 2`
  have hqc : q - c = (starRingEnd ℂ u) ^ 2 := by
    rw [← hTu]; simp only [LeanEval.ComplexAnalysis.Tantibar]; ring
  have hnorm : ‖(starRingEnd ℂ u) ^ 2 - w0 ^ 2‖ ≤ (R : ℝ) := by
    have hh := hZ q c hq hc
    rw [hqc] at hh
    exact hh
  -- factor the norm
  have hmul : ‖(starRingEnd ℂ u) - w0‖ * ‖(starRingEnd ℂ u) + w0‖
      = ‖(starRingEnd ℂ u) ^ 2 - w0 ^ 2‖ := by
    rw [← norm_mul]
    congr 1
    ring
  have hαβ : ‖(starRingEnd ℂ u) - w0‖ * ‖(starRingEnd ℂ u) + w0‖ ≤ (ρ : ℝ) * (s : ℝ) := by
    rw [hmul]
    exact le_trans hnorm h2
  -- `‖w₀‖ ≥ s`
  have hw0_sq : ‖w0‖ ^ 2 = (w0re : ℝ) ^ 2 + (w0im : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hw0]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero]
    ring
  have hsR : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs_w0 : (s : ℝ) ≤ ‖w0‖ := by
    have h2' : (s : ℝ) ^ 2 ≤ ‖w0‖ ^ 2 := by rw [hw0_sq]; exact h1
    have h3 := sq_le_sq.mp h2'
    rw [abs_of_nonneg hsR, abs_of_nonneg (norm_nonneg w0)] at h3
    exact h3
  -- the larger of the two factors is at least `‖w₀‖`
  have htri : (2 : ℝ) * ‖w0‖ ≤ ‖(starRingEnd ℂ u) + w0‖ + ‖(starRingEnd ℂ u) - w0‖ := by
    have h := norm_sub_le ((starRingEnd ℂ u) + w0) ((starRingEnd ℂ u) - w0)
    have h2w : ((starRingEnd ℂ u) + w0) - ((starRingEnd ℂ u) - w0) = (2 : ℂ) * w0 := by ring
    rw [h2w, norm_mul, Complex.norm_ofNat] at h
    exact h
  have hmax : (s : ℝ) ≤ max ‖(starRingEnd ℂ u) - w0‖ ‖(starRingEnd ℂ u) + w0‖ := by
    have ha : ‖(starRingEnd ℂ u) - w0‖ ≤ max ‖(starRingEnd ℂ u) - w0‖ ‖(starRingEnd ℂ u) + w0‖ :=
      le_max_left _ _
    have hb : ‖(starRingEnd ℂ u) + w0‖ ≤ max ‖(starRingEnd ℂ u) - w0‖ ‖(starRingEnd ℂ u) + w0‖ :=
      le_max_right _ _
    linarith [hs_w0]
  have hρ' : (0 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have hdisj : ‖(starRingEnd ℂ u) - w0‖ ≤ (ρ : ℝ) ∨ ‖(starRingEnd ℂ u) + w0‖ ≤ (ρ : ℝ) :=
    key_disj _ _ _ _ hρ' hαβ hmax
  rcases hdisj with hd | hd
  · -- `‖v - w₀‖ ≤ ρ`  ⟹  `u ∈ boxOf w0re w0im ρ`
    left
    rw [mem_boxOf_iff]
    constructor
    · have hh := Complex.abs_re_le_norm ((starRingEnd ℂ u) - w0)
      rw [Complex.sub_re, Complex.conj_re, hw0re] at hh
      linarith
    · have hh := Complex.abs_im_le_norm ((starRingEnd ℂ u) - w0)
      rw [Complex.sub_im, Complex.conj_im, hw0im] at hh
      rw [show -u.im - (w0im : ℝ) = -(u.im + (w0im : ℝ)) by ring, abs_neg] at hh
      linarith
  · -- `‖v + w₀‖ ≤ ρ`  ⟹  `-u ∈ boxOf w0re w0im ρ`
    right
    rw [mem_boxOf_iff]
    constructor
    · rw [Complex.neg_re]
      rw [show -u.re - (w0re : ℝ) = -(u.re + (w0re : ℝ)) by ring, abs_neg]
      have hh := Complex.abs_re_le_norm ((starRingEnd ℂ u) + w0)
      rw [Complex.add_re, Complex.conj_re, hw0re] at hh
      linarith [hd]
    · rw [Complex.neg_im]
      have hh := Complex.abs_im_le_norm ((starRingEnd ℂ u) + w0)
      rw [Complex.add_im, Complex.conj_im, hw0im] at hh
      linarith [hd]

end Work.SeedCertRay
