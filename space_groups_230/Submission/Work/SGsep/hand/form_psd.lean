import Mathlib
import Submission.Work.SGsep.hand.HandDefs2

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-! ## The `2 × 2` and `3 × 3` positive-semidefiniteness criteria used below

`M3.psd` tests a flat integer matrix through its seven principal minors.  For a *symmetric*
matrix over an ordered field this characterises positive semidefiniteness; the two lemmas
below are the real-algebra core of that fact in dimension `2` and `3`.

The `3 × 3` proof splits on the leading entry `a`: if `a ≠ 0` one completes the square and
applies the `2 × 2` criterion to the Schur complement (whose determinant is `det M / a`), and
if `a = 0` the minors `ae - b²` and `ai - c²` force `b = c = 0`, leaving the `2 × 2` principal
submatrix on the last two coordinates. -/

/-- A symmetric `2 × 2` real matrix with nonnegative diagonal and nonnegative determinant is
positive semidefinite. -/
theorem form_psd_two_by_two {p q s : ℝ} (hp : 0 ≤ p) (hs : 0 ≤ s) (hdet : 0 ≤ p * s - q ^ 2) :
    ∀ x y : ℝ, 0 ≤ p * x ^ 2 + 2 * q * x * y + s * y ^ 2 := by
  intro x y
  obtain h0 | hpos := eq_or_lt_of_le hp
  · obtain rfl : p = 0 := h0.symm
    have hq : q = 0 := by
      have : q ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg q)
      exact sq_eq_zero_iff.mp this
    rw [hq]
    nlinarith [sq_nonneg y]
  · have h2 : 0 ≤ (s - q ^ 2 / p) * y ^ 2 := by
      apply mul_nonneg _ (sq_nonneg _)
      rw [sub_nonneg, div_le_iff₀ hpos]
      nlinarith
    have hid : p * (x + q / p * y) ^ 2 + (s - q ^ 2 / p) * y ^ 2
        = p * x ^ 2 + 2 * q * x * y + s * y ^ 2 := by
      field_simp
      ring
    rw [← hid]
    nlinarith [sq_nonneg (x + q / p * y), h2]

/-- A symmetric `3 × 3` real matrix with nonnegative diagonal entries, nonnegative `2 × 2`
principal minors and nonnegative determinant is positive semidefinite.  Here `a b c e f i`
are the entries `M₀₀ M₀₁ M₀₂ M₁₁ M₁₂ M₂₂` of the symmetric matrix
`![![a, b, c], ![b, e, f], ![c, f, i]]`. -/
theorem form_psd_three_by_three {a b c e f i : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (hi : 0 ≤ i)
    (hab : 0 ≤ a * e - b ^ 2) (hac : 0 ≤ a * i - c ^ 2) (hei : 0 ≤ e * i - f ^ 2)
    (hd : 0 ≤ a * (e * i - f ^ 2) - b * (b * i - f * c) + c * (b * f - e * c)) :
    ∀ y1 y2 y3 : ℝ,
      0 ≤ a * y1 ^ 2 + e * y2 ^ 2 + i * y3 ^ 2 + 2 * b * y1 * y2 + 2 * c * y1 * y3
        + 2 * f * y2 * y3 := by
  intro y1 y2 y3
  obtain ha0 | hapos := eq_or_lt_of_le ha
  · obtain rfl : a = 0 := ha0.symm
    have hb : b = 0 := by
      have : b ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg b)
      exact sq_eq_zero_iff.mp this
    have hc : c = 0 := by
      have : c ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg c)
      exact sq_eq_zero_iff.mp this
    rw [hb, hc]
    have h2 := form_psd_two_by_two he hi hei y2 y3
    linarith
  · have hp : 0 ≤ e - b ^ 2 / a := by
      rw [sub_nonneg, div_le_iff₀ hapos]; linarith
    have hs : 0 ≤ i - c ^ 2 / a := by
      rw [sub_nonneg, div_le_iff₀ hapos]; linarith
    have hps : 0 ≤ (e - b ^ 2 / a) * (i - c ^ 2 / a) - (f - b * c / a) ^ 2 := by
      have hkey : (e - b ^ 2 / a) * (i - c ^ 2 / a) - (f - b * c / a) ^ 2
          = (a * (e * i - f ^ 2) - b * (b * i - f * c) + c * (b * f - e * c)) / a := by
        field_simp
        ring
      rw [hkey]
      exact div_nonneg (by linarith) hapos.le
    have h2 := form_psd_two_by_two hp hs hps y2 y3
    have hid : a * (y1 + (b * y2 + c * y3) / a) ^ 2
          + ((e - b ^ 2 / a) * y2 ^ 2 + 2 * (f - b * c / a) * y2 * y3
              + (i - c ^ 2 / a) * y3 ^ 2)
        = a * y1 ^ 2 + e * y2 ^ 2 + i * y3 ^ 2 + 2 * b * y1 * y2 + 2 * c * y1 * y3
          + 2 * f * y2 * y3 := by
      field_simp
      ring
    rw [← hid]
    nlinarith [mul_nonneg ha (sq_nonneg (y1 + (b * y2 + c * y3) / a))]

/-! ## The flat integer matrix and its real image -/

/-- `M3.psd` unpacked: the seven principal minors of the flat matrix are nonnegative. -/
theorem form_psd_iff (N : M3) : (M3.psd N = true) ↔
    (0 ≤ N.a ∧ 0 ≤ N.e ∧ 0 ≤ N.i ∧ 0 ≤ N.a * N.e - N.b * N.d ∧
      0 ≤ N.a * N.i - N.c * N.g ∧ 0 ≤ N.e * N.i - N.f * N.h ∧ 0 ≤ M3.det N) := by
  simp only [M3.psd, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The hypotheses on `N` that are actually used: `M3.psd`, plus the symmetry `N.b = N.d`,
`N.c = N.g`, `N.f = N.h` (which the three `2 × 2` minors need to be genuine principal minors),
give the real positive-semidefiniteness conditions of `form_psd_three_by_three`. -/
theorem form_psd_conditions {N : M3} (hsym : N.b = N.d ∧ N.c = N.g ∧ N.f = N.h)
    (h : M3.psd N = true) :
    (0 : ℝ) ≤ (N.a : ℝ) ∧ (0 : ℝ) ≤ (N.e : ℝ) ∧ (0 : ℝ) ≤ (N.i : ℝ) ∧
    (0 : ℝ) ≤ (N.a : ℝ) * (N.e : ℝ) - (N.b : ℝ) ^ 2 ∧
    (0 : ℝ) ≤ (N.a : ℝ) * (N.i : ℝ) - (N.c : ℝ) ^ 2 ∧
    (0 : ℝ) ≤ (N.e : ℝ) * (N.i : ℝ) - (N.f : ℝ) ^ 2 ∧
    (0 : ℝ) ≤ (N.a : ℝ) * ((N.e : ℝ) * (N.i : ℝ) - (N.f : ℝ) ^ 2)
      - (N.b : ℝ) * ((N.b : ℝ) * (N.i : ℝ) - (N.f : ℝ) * (N.c : ℝ))
      + (N.c : ℝ) * ((N.b : ℝ) * (N.f : ℝ) - (N.e : ℝ) * (N.c : ℝ)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (form_psd_iff N).mp h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · have hh : (0 : ℝ) ≤ ((N.a * N.e - N.b * N.d : ℤ) : ℝ) := by exact_mod_cast h4
    rw [← hsym.1] at hh
    push_cast at hh
    simpa [pow_two] using hh
  · have hh : (0 : ℝ) ≤ ((N.a * N.i - N.c * N.g : ℤ) : ℝ) := by exact_mod_cast h5
    rw [← hsym.2.1] at hh
    push_cast at hh
    simpa [pow_two] using hh
  · have hh : (0 : ℝ) ≤ ((N.e * N.i - N.f * N.h : ℤ) : ℝ) := by exact_mod_cast h6
    rw [← hsym.2.2] at hh
    push_cast at hh
    simpa [pow_two] using hh
  · have hh : (0 : ℝ) ≤ ((M3.det N : ℤ) : ℝ) := by exact_mod_cast h7
    rw [M3.det] at hh
    rw [← hsym.1, ← hsym.2.1, ← hsym.2.2] at hh
    push_cast at hh
    simpa [pow_two] using hh

/-- `M3.form A z = AᵀS - SA` is always symmetric. -/
theorem form_psd_symm (A : M3) (z : V3) : (M3.form A z).b = (M3.form A z).d ∧
    (M3.form A z).c = (M3.form A z).g ∧ (M3.form A z).f = (M3.form A z).h := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [M3.form, M3.trans, M3.skew, M3.mul, M3.sub] <;> ring

/-- The quadratic form of `M3.form A z` is twice `y ↦ det(y, A y, z)`. -/
theorem form_psd_quad_ident (A : M3) (z : V3) (y : Fin 3 → ℝ) :
    dotProduct ((toRMat (M3.form A z).toIMat).mulVec y) y =
      2 * detCols y ((toRMat A.toIMat).mulVec y) (toRealV z) := by
  rw [detCols, Matrix.det_fin_three]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  simp [toRMat, M3.toIMat, M3.form, M3.trans, M3.skew, M3.mul, M3.sub, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, toRVec, V3.toFun]
  ring

set_option linter.unusedVariables false

/-- If `eps • (Aᵀ S - S A)` (`S = skew z`) is positive semidefinite — tested through the seven
principal minors by `M3.psd` — then the quadratic form `y ↦ det(y, A y, z)` has the sign of `eps`
everywhere.  (For `A` a rotation with rotation axis `z` this form is definite, which is what makes
the orientation condition of `Data.HandCert.chk` well defined.) -/
theorem form_psd {A : M3} {z : V3} {eps : Int} (heps : eps = 1 ∨ eps = -1)
    (h : M3.psd (M3.smulM eps (M3.form A z)) = true) :
    ∀ y : Fin 3 → ℝ, 0 ≤ (eps : ℝ) * detCols y ((toRMat A.toIMat).mulVec y) (toRealV z) := by
  intro y
  obtain ⟨hbF, hcF, hfF⟩ := form_psd_symm A z
  have hsymN : (M3.smulM eps (M3.form A z)).b = (M3.smulM eps (M3.form A z)).d ∧
      (M3.smulM eps (M3.form A z)).c = (M3.smulM eps (M3.form A z)).g ∧
      (M3.smulM eps (M3.form A z)).f = (M3.smulM eps (M3.form A z)).h := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [M3.smulM, hbF]
    · simp only [M3.smulM, hcF]
    · simp only [M3.smulM, hfF]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := form_psd_conditions hsymN h
  have hq := form_psd_three_by_three h1 h2 h3 h4 h5 h6 h7 (y 0) (y 1) (y 2)
  have hexp : dotProduct ((toRMat (M3.smulM eps (M3.form A z)).toIMat).mulVec y) y
      = ((M3.smulM eps (M3.form A z)).a : ℝ) * y 0 ^ 2
        + ((M3.smulM eps (M3.form A z)).e : ℝ) * y 1 ^ 2
        + ((M3.smulM eps (M3.form A z)).i : ℝ) * y 2 ^ 2
        + 2 * ((M3.smulM eps (M3.form A z)).b : ℝ) * y 0 * y 1
        + 2 * ((M3.smulM eps (M3.form A z)).c : ℝ) * y 0 * y 2
        + 2 * ((M3.smulM eps (M3.form A z)).f : ℝ) * y 1 * y 2 := by
    simp [toRMat, M3.toIMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [← hsymN.1, ← hsymN.2.1, ← hsymN.2.2]
    ring
  have hnonneg : 0 ≤ dotProduct ((toRMat (M3.smulM eps (M3.form A z)).toIMat).mulVec y) y := by
    rw [hexp]; exact hq
  have hmat : toRMat (M3.smulM eps (M3.form A z)).toIMat
      = (eps : ℝ) • toRMat (M3.form A z).toIMat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toRMat, M3.toIMat, M3.smulM, Matrix.map_apply]
  have hscale : dotProduct ((toRMat (M3.smulM eps (M3.form A z)).toIMat).mulVec y) y
      = (eps : ℝ) * dotProduct ((toRMat (M3.form A z).toIMat).mulVec y) y := by
    rw [hmat, Matrix.smul_mulVec, smul_dotProduct, smul_eq_mul]
  rw [hscale, form_psd_quad_ident A z y] at hnonneg
  nlinarith [hnonneg]

end Work.SGsep.hand
