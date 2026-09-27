import Mathlib

namespace Work.Drive.PushDisc

noncomputable section

/-- Radial cutoff used in the amplitudes: smooth, equal to `1` on `[-1,1]` and supported in
`[-X,X]` (for `1 < X`). -/
private def ampPsi (X x : ℝ) : ℝ :=
  Real.smoothTransition ((x + X) / (X - 1)) * Real.smoothTransition ((X - x) / (X - 1))

/-- Height profile: smooth, nonnegative, equal to `t/2 + g` for `t ≥ 0`, and zero for
`t ≤ -g/2`. -/
private def ampF (g t : ℝ) : ℝ :=
  Real.smoothTransition ((2 * t + g) / g) * (t / 2 + g)

/-- The auxiliary amplitude: smooth, `1` at `0`, supported in `[-1/2, 1/2]`. -/
private def ampL (t : ℝ) : ℝ := Real.smoothTransition (2 - 8 * t ^ 2)

private lemma contDiff_ampPsi {X : ℝ} :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ampPsi X) := by
  unfold ampPsi
  fun_prop

private lemma contDiff_ampF {g : ℝ} : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ampF g) := by
  unfold ampF
  fun_prop

private lemma contDiff_ampL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ampL := by
  unfold ampL
  fun_prop

private lemma ampPsi_nonneg (X x : ℝ) : 0 ≤ ampPsi X x := by
  unfold ampPsi
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

private lemma ampPsi_le_one (X x : ℝ) : ampPsi X x ≤ 1 := by
  unfold ampPsi
  nlinarith [Real.smoothTransition.le_one ((x + X) / (X - 1)),
    Real.smoothTransition.le_one ((X - x) / (X - 1)),
    Real.smoothTransition.nonneg ((x + X) / (X - 1)),
    Real.smoothTransition.nonneg ((X - x) / (X - 1))]

private lemma ampPsi_eq_one_of_abs_le_one {X x : ℝ} (hX : 1 < X) (hx : |x| ≤ 1) :
    ampPsi X x = 1 := by
  have hX1 : 0 < X - 1 := by linarith
  have hx1 : x ≤ 1 := (abs_le.mp hx).2
  have hx2 : -1 ≤ x := (abs_le.mp hx).1
  have ha : (1 : ℝ) ≤ (x + X) / (X - 1) := by rw [one_le_div hX1]; linarith
  have hb : (1 : ℝ) ≤ (X - x) / (X - 1) := by rw [one_le_div hX1]; linarith
  unfold ampPsi
  rw [Real.smoothTransition.one_of_one_le ha, Real.smoothTransition.one_of_one_le hb, mul_one]

private lemma ampPsi_eq_zero_of_abs_ge {X x : ℝ} (hX : 1 < X) (h : X ≤ |x|) :
    ampPsi X x = 0 := by
  have hX1 : 0 < X - 1 := by linarith
  unfold ampPsi
  rcases le_or_gt x 0 with hx | hx
  · have hxX : x ≤ -X := by rw [abs_of_nonpos hx] at h; linarith
    rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : x + X ≤ 0) hX1.le), zero_mul]
  · have hxX : X ≤ x := by rw [abs_of_pos hx] at h; exact h
    rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : X - x ≤ 0) hX1.le), mul_zero]

private lemma smoothTransition_ratio_eq_zero {g t : ℝ} (hg : 0 < g) (ht : 2 * t + g ≤ 0) :
    Real.smoothTransition ((2 * t + g) / g) = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht hg.le)

private lemma smoothTransition_ratio_eq_one {g t : ℝ} (hg : 0 < g) (ht : 0 ≤ t) :
    Real.smoothTransition ((2 * t + g) / g) = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [one_le_div hg]; linarith)

private lemma ampF_nonneg {g : ℝ} (hg : 0 < g) (t : ℝ) : 0 ≤ ampF g t := by
  unfold ampF
  rcases le_or_gt (2 * t + g) 0 with h | h
  · rw [smoothTransition_ratio_eq_zero hg h, zero_mul]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (by linarith)

private lemma ampF_eq_zero {g : ℝ} (hg : 0 < g) {t : ℝ} (h : 2 * t + g ≤ 0) : ampF g t = 0 := by
  unfold ampF
  rw [smoothTransition_ratio_eq_zero hg h, zero_mul]

private lemma ampF_le_g {g : ℝ} (hg : 0 < g) {t : ℝ} (ht : t ≤ 0) : ampF g t ≤ g := by
  unfold ampF
  rcases le_or_gt (2 * t + g) 0 with h | h
  · rw [smoothTransition_ratio_eq_zero hg h, zero_mul]
    linarith
  · calc Real.smoothTransition ((2 * t + g) / g) * (t / 2 + g)
        ≤ 1 * (t / 2 + g) :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _) (by linarith)
      _ = t / 2 + g := one_mul _
      _ ≤ g := by linarith

private lemma two_ampF_sub_of_nonneg {g : ℝ} (hg : 0 < g) {t : ℝ} (ht : 0 ≤ t) :
    2 * ampF g t - t = 2 * g := by
  unfold ampF
  rw [smoothTransition_ratio_eq_one hg ht]
  ring

private lemma abs_two_mul_sub_of_bounds {m t g η : ℝ} (hη : 2.5 * g < η)
    (hm0 : 0 ≤ m) (hmg : m ≤ g) (ht0 : t < 0) (ht : -(g / 2) < t) :
    |2 * m - t| < η := by
  have hpos : 0 ≤ 2 * m - t := by linarith
  rw [abs_of_nonneg hpos]
  linarith

private lemma ampL_nonneg (t : ℝ) : 0 ≤ ampL t := Real.smoothTransition.nonneg _

private lemma ampL_eq_zero {t : ℝ} (h : 1 / 2 ≤ t) : ampL t = 0 := by
  unfold ampL
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith

private lemma ampL_zero : ampL 0 = 1 := by
  unfold ampL
  norm_num [Real.smoothTransition.one_of_one_le]

theorem heightAmplitudesNear {w : ℝ → ℝ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    {X X' η : ℝ} (h1X : 1 < X) (hXX' : X < X') (hη : 0 < η)
    (hwneg : ∀ x : ℝ, 1 < |x| → |x| < X' → w x < 0)
    (hwsmall : ∀ x : ℝ, 1 < |x| → |x| < X' → |w x| < η) :
    ∃ (m l : ℝ → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) l ∧ (∀ x : ℝ, 0 ≤ m x) ∧ (∀ t : ℝ, 0 ≤ l t) ∧
      (∀ x : ℝ, X ≤ |x| → m x = 0) ∧ (∀ t : ℝ, 1 / 2 ≤ t → l t = 0) ∧ l 0 = 1 ∧
      (∀ x : ℝ, |x| < X' → w x ≠ 2 * m x * l 0) ∧
      (∀ x : ℝ, |x| < X' → 2 * m x * l 0 = 0 ∨ |2 * m x * l 0 - w x| < η) := by
  set g : ℝ := η / 4 with hgdef
  have hgpos : 0 < g := by rw [hgdef]; linarith
  have h2g : 2 * g < η := by rw [hgdef]; linarith
  have h52g : 2.5 * g < η := by rw [hgdef]; linarith
  -- pointwise content at every base point with `|x| < X'`
  have key : ∀ x : ℝ, |x| < X' →
      (ampPsi X x * ampF g (w x) = 0 ∧ w x ≠ 0) ∨
        (2 * (ampPsi X x * ampF g (w x)) - w x ≠ 0 ∧
          |2 * (ampPsi X x * ampF g (w x)) - w x| < η) := by
    intro x hx
    rcases le_or_gt X |x| with hXle | hXlt
    · -- Case A: `X ≤ |x|`; here `m` vanishes and `w` is negative
      have hwx : w x < 0 := hwneg x (by linarith) hx
      have hm : ampPsi X x * ampF g (w x) = 0 := by
        rw [ampPsi_eq_zero_of_abs_ge h1X hXle, zero_mul]
      exact Or.inl ⟨hm, ne_of_lt hwx⟩
    · rcases le_or_gt |x| 1 with hx1 | hx1
      · -- Case B1: `|x| ≤ 1`; the cutoff is `1` and `m = ampF g (w x)`
        have hpsi : ampPsi X x = 1 := ampPsi_eq_one_of_abs_le_one h1X hx1
        have hm : ampPsi X x * ampF g (w x) = ampF g (w x) := by rw [hpsi, one_mul]
        rcases le_or_gt 0 (w x) with ht | ht
        · -- `0 ≤ w x`
          refine Or.inr ⟨?_, ?_⟩
          · rw [hm]
            have h2 := two_ampF_sub_of_nonneg hgpos ht
            linarith
          · rw [hm, two_ampF_sub_of_nonneg hgpos ht, abs_of_pos (by linarith)]
            linarith
        · rcases le_or_gt (w x) (-(g / 2)) with ht' | ht'
          · -- `w x ≤ -g/2`: `m` vanishes
            have h0 : ampF g (w x) = 0 := ampF_eq_zero hgpos (by linarith)
            exact Or.inl ⟨by rw [hm, h0], by linarith⟩
          · -- `-g/2 < w x < 0`
            have hm0 : 0 ≤ ampF g (w x) := ampF_nonneg hgpos _
            have hmg : ampF g (w x) ≤ g := ampF_le_g hgpos ht.le
            have hne : 2 * ampF g (w x) - w x ≠ 0 := by linarith
            have hlt : |2 * ampF g (w x) - w x| < η :=
              abs_two_mul_sub_of_bounds h52g hm0 hmg ht ht'
            exact Or.inr ⟨by rw [hm]; exact hne, by rw [hm]; exact hlt⟩
      · -- Case B2: `1 < |x| < X`; here `w x < 0` and `m = ampPsi X x * ampF g (w x)`
        have hwx : w x < 0 := hwneg x hx1 (by linarith)
        rcases le_or_gt (w x) (-(g / 2)) with ht' | ht'
        · -- `w x ≤ -g/2`: `m` vanishes
          have h0 : ampF g (w x) = 0 := ampF_eq_zero hgpos (by linarith)
          exact Or.inl ⟨by rw [h0, mul_zero], ne_of_lt hwx⟩
        · -- `-g/2 < w x < 0`
          have hm0 : 0 ≤ ampPsi X x * ampF g (w x) :=
            mul_nonneg (ampPsi_nonneg X x) (ampF_nonneg hgpos _)
          have hmg : ampPsi X x * ampF g (w x) ≤ g :=
            le_trans (mul_le_of_le_one_left (ampF_nonneg hgpos _) (ampPsi_le_one X x))
              (ampF_le_g hgpos hwx.le)
          have hne : 2 * (ampPsi X x * ampF g (w x)) - w x ≠ 0 := by linarith
          exact Or.inr ⟨hne, abs_two_mul_sub_of_bounds h52g hm0 hmg hwx ht'⟩
  refine ⟨fun x => ampPsi X x * ampF g (w x), ampL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_ampPsi (X := X)).mul ((contDiff_ampF (g := g)).comp hw)
  · exact contDiff_ampL
  · intro x
    exact mul_nonneg (ampPsi_nonneg X x) (ampF_nonneg hgpos _)
  · exact ampL_nonneg
  · intro x hx
    show ampPsi X x * ampF g (w x) = 0
    rw [ampPsi_eq_zero_of_abs_ge h1X hx, zero_mul]
  · intro t ht
    exact ampL_eq_zero ht
  · exact ampL_zero
  · intro x hx
    rcases key x hx with ⟨hm, hwne⟩ | ⟨hne, _⟩
    · show w x ≠ 2 * (ampPsi X x * ampF g (w x)) * ampL 0
      simpa only [ampL_zero, mul_one, hm, mul_zero] using hwne
    · show w x ≠ 2 * (ampPsi X x * ampF g (w x)) * ampL 0
      rw [ampL_zero, mul_one]
      exact fun hcon => hne (by linarith)
  · intro x hx
    rcases key x hx with ⟨hm, _⟩ | ⟨_, hlt⟩
    · refine Or.inl ?_
      show 2 * (ampPsi X x * ampF g (w x)) * ampL 0 = 0
      simp only [ampL_zero, mul_one, hm, mul_zero]
    · refine Or.inr ?_
      show |2 * (ampPsi X x * ampF g (w x)) * ampL 0 - w x| < η
      simpa only [ampL_zero, mul_one] using hlt

end

end Work.Drive.PushDisc
