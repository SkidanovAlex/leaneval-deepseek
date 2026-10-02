import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- The core real-analysis content of `Petal_iff_norm`: writing `w = A (z - z₁)` for the
(nonzero) Fatou-chart coordinate, the condition `Re (-1/w) < -R` is exactly the statement that
`w` lies in the open disk of centre `1/(2R)` and radius `1/(2R)` (which passes through `0`).

For `w = 0` both sides are false, so no non-degeneracy hypothesis on `w` is needed. -/
private lemma petal_key {R : ℝ} (hR : 0 < R) (w : ℂ) :
    (-(w⁻¹)).re < -R ↔ ‖w - (((1 / (2 * R) : ℝ)) : ℂ)‖ < (1 / (2 * R) : ℝ) := by
  set k : ℝ := 1 / (2 * R) with hk
  have hknn : 0 ≤ k := by rw [hk]; positivity
  -- `-(w⁻¹).re < -R` ⟺ `R * normSq w < w.re` (with `w = 0` a degenerate both-false case).
  have hA : (-(w⁻¹)).re < -R ↔ R * Complex.normSq w < w.re := by
    rw [Complex.neg_re, Complex.inv_re]
    by_cases hw : w = 0
    · subst w
      simp only [Complex.normSq_zero, Complex.zero_re, mul_zero, div_zero, neg_zero]
      constructor <;> intro h <;> linarith
    · have hn : 0 < Complex.normSq w := by rwa [Complex.normSq_pos]
      constructor
      · intro h
        have h' : R < w.re / Complex.normSq w := by linarith
        rwa [lt_div_iff₀ hn] at h'
      · intro h
        have h' : R < w.re / Complex.normSq w := by rwa [lt_div_iff₀ hn]
        linarith
  -- squaring turns the disk condition into `normSq (w - k) < normSq k`.
  have h1 : ‖w - (k : ℂ)‖ < k ↔ Complex.normSq (w - (k : ℂ)) < Complex.normSq ((k : ℂ)) := by
    have hk2 : Complex.normSq ((k : ℂ)) = k ^ 2 := by rw [Complex.normSq_ofReal, sq]
    rw [← Complex.sq_norm (w - (k : ℂ)), hk2, sq_lt_sq₀ (norm_nonneg _) hknn]
  have h2 : Complex.normSq (w - (k : ℂ)) = Complex.normSq w + k * k - 2 * (w.re * k) := by
    rw [Complex.normSq_sub, Complex.conj_ofReal, Complex.normSq_ofReal, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- the two forms of the condition agree.
  have h4 : (Complex.normSq w + k * k - 2 * (w.re * k) < k * k) ↔
      R * Complex.normSq w < w.re := by
    have hkR : k * (2 * R) = 1 := by
      rw [hk, one_div, inv_mul_cancel₀ (by positivity : (2 * R : ℝ) ≠ 0)]
    have h2k : 2 * k = 1 / R := by
      rw [eq_div_iff (ne_of_gt hR), ← hkR]; ring
    have e1 : (Complex.normSq w + k * k - 2 * (w.re * k) < k * k) ↔
        Complex.normSq w < 2 * (w.re * k) := by
      constructor <;> intro h <;> linarith
    have heq : (2 * (w.re * k) : ℝ) = w.re / R := by
      rw [show 2 * (w.re * k) = w.re * (2 * k) by ring, h2k]
      simp [div_eq_mul_inv]
    have e2 : (Complex.normSq w < 2 * (w.re * k)) ↔ Complex.normSq w < w.re / R := by
      rw [heq]
    have e3 : (Complex.normSq w < w.re / R) ↔ Complex.normSq w * R < w.re :=
      lt_div_iff₀ hR
    have e4 : (Complex.normSq w * R < w.re) ↔ R * Complex.normSq w < w.re := by
      rw [mul_comm (Complex.normSq w) R]
    exact e1.trans (e2.trans (e3.trans e4))
  have hB : (‖w - (k : ℂ)‖ < k) ↔ R * Complex.normSq w < w.re := by
    rw [h1, h2, Complex.normSq_ofReal]
    exact h4
  exact hA.trans hB.symm

theorem Petal_iff_norm {z₁ A : ℂ} {R : ℝ} (hR : 0 < R) (hA : A ≠ 0) (z : ℂ) :
    z ∈ Work.SeedCertRay.Petal z₁ A R ↔ ‖A * (z - z₁) - (1 / (2 * R) : ℂ)‖ < 1 / (2 * R) := by
  rw [Work.SeedCertRay.mem_Petal_iff, Work.SeedCertRay.fatou]
  rw [show (1 / (2 * R) : ℂ) = (((1 / (2 * R) : ℝ)) : ℂ) from by push_cast; ring]
  set w : ℂ := A * (z - z₁) with hw
  have hwz : w = 0 ↔ z = z₁ := by
    rw [hw, mul_eq_zero]
    simp [hA, sub_eq_zero]
  have hp : (-(w⁻¹)).re < -R ↔ ‖w - (((1 / (2 * R) : ℝ)) : ℂ)‖ < (1 / (2 * R) : ℝ) :=
    petal_key hR w
  constructor
  · rintro ⟨hz1, h2⟩
    exact hp.mp h2
  · intro h
    by_cases hw0 : w = 0
    · exfalso
      have hcontr : ¬ (‖(0 : ℂ) - (((1 / (2 * R) : ℝ)) : ℂ)‖ < (1 / (2 * R) : ℝ)) := by
        rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * R))]
        exact not_lt.mpr le_rfl
      rw [hw0] at h
      exact hcontr h
    · exact ⟨fun hz1 => hw0 (hwz.mpr hz1), hp.mpr h⟩

end Work.SeedCertRay
