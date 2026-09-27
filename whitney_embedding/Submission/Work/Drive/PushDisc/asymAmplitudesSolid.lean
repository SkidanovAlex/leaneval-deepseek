import Mathlib

namespace Work.Drive.PushDisc

noncomputable section

/-- Smooth cutoff: equals `1` on `[-1,1]` and `0` outside `(-X,X)` (for `1 < X`). -/
private def asymPsi (X x : ℝ) : ℝ :=
  Real.smoothTransition ((x + X) / (X - 1)) * Real.smoothTransition ((X - x) / (X - 1))

private lemma contDiff_asymPsi {X : ℝ} :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (asymPsi X) := by
  unfold asymPsi
  fun_prop

private lemma asymPsi_nonneg (X x : ℝ) : 0 ≤ asymPsi X x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

private lemma asymPsi_le_one (X x : ℝ) : asymPsi X x ≤ 1 := by
  unfold asymPsi
  nlinarith [Real.smoothTransition.le_one ((x + X) / (X - 1)),
    Real.smoothTransition.le_one ((X - x) / (X - 1)),
    Real.smoothTransition.nonneg ((x + X) / (X - 1)),
    Real.smoothTransition.nonneg ((X - x) / (X - 1))]

private lemma asymPsi_eq_one_of_abs_le_one {X x : ℝ} (hX : 1 < X) (hx : |x| ≤ 1) :
    asymPsi X x = 1 := by
  have hX1 : 0 < X - 1 := by linarith
  have hxhi : x ≤ 1 := (abs_le.mp hx).2
  have hxlo : -1 ≤ x := (abs_le.mp hx).1
  have ha : (1 : ℝ) ≤ (x + X) / (X - 1) := by rw [one_le_div hX1]; linarith
  have hb : (1 : ℝ) ≤ (X - x) / (X - 1) := by rw [one_le_div hX1]; linarith
  unfold asymPsi
  rw [Real.smoothTransition.one_of_one_le ha, Real.smoothTransition.one_of_one_le hb, mul_one]

private lemma asymPsi_eq_zero_of_abs_ge {X x : ℝ} (hX : 1 < X) (h : X ≤ |x|) :
    asymPsi X x = 0 := by
  have hX1 : 0 < X - 1 := by linarith
  unfold asymPsi
  rcases le_or_gt x 0 with hx | hx
  · have hxX : x ≤ -X := by rw [abs_of_nonpos hx] at h; linarith
    rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : x + X ≤ 0) hX1.le), zero_mul]
  · have hxX : X ≤ x := by rw [abs_of_pos hx] at h; exact h
    rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : X - x ≤ 0) hX1.le), mul_zero]

private lemma asymPsi_pos_imp_abs_lt {X x : ℝ} (hX : 1 < X) (h : 0 < asymPsi X x) :
    |x| < X := by
  by_contra hcon
  rw [not_lt] at hcon
  rw [asymPsi_eq_zero_of_abs_ge hX hcon] at h
  exact lt_irrefl 0 h

theorem asymAmplitudesSolid {c : ℝ → ℝ} (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    {X η ε : ℝ} (hX : 1 < X) (hη : 0 < η) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hcneg : ∀ x : ℝ, 1 < |x| → |x| < X → c x < 0)
    (hcη : ∀ x : ℝ, |x| ≤ X → -η / 2 ≤ c x) :
    ∃ m l : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) l ∧ (∀ x : ℝ, 0 ≤ m x) ∧
      (∀ t : ℝ, 0 ≤ l t) ∧ (∀ x : ℝ, X ≤ |x| → m x = 0) ∧ l 0 = 1 ∧
      (∀ t : ℝ, l t ≤ 1) ∧ (∀ t : ℝ, 1 / 2 ≤ t → l t = 0) ∧
      (∀ t : ℝ, ε ^ 2 ≤ t → l t = 0) ∧
      (∀ x : ℝ, |x| < X → c x < 2 * m x) ∧ (∀ x : ℝ, |x| < X → 2 * m x ≤ c x + η / 2) := by
  -- the height amplitude: smooth, nonnegative, `1` at `0`, supported in `(-∞, ε^2)`
  have hl_zero : ∀ t : ℝ, ε ^ 2 ≤ t → Real.smoothTransition (1 - t / ε ^ 2) = 0 := by
    intro t ht
    apply Real.smoothTransition.zero_of_nonpos
    rw [sub_nonpos, one_le_div (by positivity)]
    exact ht
  have hεsq : ε ^ 2 ≤ 1 / 2 := by nlinarith [hε.le, hε2]
  refine ⟨fun x => asymPsi X x * (c x / 2 + η / 4),
    fun t => Real.smoothTransition (1 - t / ε ^ 2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness of `m`
    exact contDiff_asymPsi.mul ((hc.div_const 2).add contDiff_const)
  · -- smoothness of `l`
    exact (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)
  · -- nonnegativity of `m`
    intro x
    change 0 ≤ asymPsi X x * (c x / 2 + η / 4)
    rcases eq_or_lt_of_le (asymPsi_nonneg X x) with h0 | hpos
    · rw [← h0, zero_mul]
    · exact mul_nonneg hpos.le
        (by linarith [hcη x (asymPsi_pos_imp_abs_lt hX hpos).le])
  · -- nonnegativity of `l`
    intro t
    exact Real.smoothTransition.nonneg _
  · -- `m` is supported in `(-X, X)`
    intro x hx
    change asymPsi X x * (c x / 2 + η / 4) = 0
    rw [asymPsi_eq_zero_of_abs_ge hX hx, zero_mul]
  · -- `l 0 = 1`
    show Real.smoothTransition (1 - 0 / ε ^ 2) = 1
    have h : 1 - (0 : ℝ) / ε ^ 2 = 1 := by norm_num
    rw [h, Real.smoothTransition.one]
  · -- `l ≤ 1`
    intro t
    exact Real.smoothTransition.le_one _
  · -- `l` vanishes for `t ≥ 1/2`
    intro t ht
    exact hl_zero t (le_trans hεsq ht)
  · -- `l` vanishes for `t ≥ ε^2`
    intro t ht
    exact hl_zero t ht
  · -- lower bound on `2 * m`
    intro x hx
    change c x < 2 * (asymPsi X x * (c x / 2 + η / 4))
    have hmc : 2 * (asymPsi X x * (c x / 2 + η / 4)) = asymPsi X x * (c x + η / 2) := by ring
    rw [hmc]
    rcases le_or_gt 0 (c x) with hc0 | hc0
    · have hx1 : |x| ≤ 1 := by
        by_contra hcon
        exact absurd (hcneg x (not_le.mp hcon) hx) (not_lt.mpr hc0)
      rw [asymPsi_eq_one_of_abs_le_one hX hx1]
      linarith
    · have hc2 : 0 ≤ c x + η / 2 := by linarith [hcη x hx.le]
      nlinarith [mul_nonneg (asymPsi_nonneg X x) hc2]
  · -- upper bound on `2 * m`
    intro x hx
    change 2 * (asymPsi X x * (c x / 2 + η / 4)) ≤ c x + η / 2
    have hmc : 2 * (asymPsi X x * (c x / 2 + η / 4)) = asymPsi X x * (c x + η / 2) := by ring
    rw [hmc]
    have hc2 : 0 ≤ c x + η / 2 := by linarith [hcη x hx.le]
    calc asymPsi X x * (c x + η / 2) ≤ 1 * (c x + η / 2) :=
          mul_le_mul_of_nonneg_right (asymPsi_le_one X x) hc2
      _ = c x + η / 2 := one_mul _

end

end Work.Drive.PushDisc
