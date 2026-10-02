import Mathlib
import Submission.Work.PARIMPL2.Direct.oidArcNeg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-! ## Telescoping estimate for the "positive arc" of the orbit

Along a `1/3`-separated real sequence whose phases `t_i = λ x_i` lie in `(π/2, π)`, one has

  `∑_{i=j+1}^{j0-1} λ² / sin²(λ x_i) ≤ 3 λ · (−cot (λ x_j))`.

The proof telescopes the cotangent.  Write `t_i = λ x_i`.  For `i` in the summation range the
hypotheses put `π/2 < t_i < π` and (using the predecessor index) `t_i ≤ t_{i-1}` with
`t_{i-1} − t_i ≥ λ/3`.  The elementary mean-value inequality

  `(b − a) / sin² a ≤ cot a − cot b`   (`π/2 < a ≤ b < π`)

then gives `λ²/sin² t_i ≤ 3 λ (cot t_i − cot t_{i-1})`.  Summing and telescoping,

  `∑ λ²/sin² t_i ≤ 3 λ (cot t_{j0-1} − cot t_j) ≤ 3 λ (−cot t_j)`

because `cot t_{j0-1} ≤ 0` on `(π/2, π)`. -/

/-- Elementary trigonometric core: for `0 ≤ a ≤ b < π/2`,
`(b − a) sin a ≤ sin (b − a) sin b`.

Writing `d = b − a ≥ 0`, this says `(b − a) sin a ≤ sin b · sin(b − a)`.  It follows from the two
inequalities `sin a ≤ cos(b − a) sin b` (the difference is `cos b · sin(b − a) ≥ 0`) and
`(b − a) cos(b − a) ≤ sin(b − a)` (from `tan d ≥ d`). -/
private theorem oidArcATel_sinGap_aux (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b < Real.pi / 2) :
    (b - a) * Real.sin a ≤ Real.sin (b - a) * Real.sin b := by
  have hb0 : 0 ≤ b := le_trans ha hab
  have hd0 : 0 ≤ b - a := by linarith
  have hdpi : b - a < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcosb : 0 ≤ Real.cos b :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], le_of_lt hb⟩
  have hsinb : 0 ≤ Real.sin b := Real.sin_nonneg_of_mem_Icc ⟨hb0, by linarith [hb, Real.pi_pos]⟩
  have hsind : 0 ≤ Real.sin (b - a) :=
    Real.sin_nonneg_of_mem_Icc ⟨hd0, by linarith [hdpi, Real.pi_pos]⟩
  have hstep1 : Real.sin a ≤ Real.cos (b - a) * Real.sin b := by
    have h := Real.sin_sub b (b - a)
    rw [show b - (b - a) = a by ring] at h
    have h' : Real.cos (b - a) * Real.sin b = Real.sin a + Real.cos b * Real.sin (b - a) := by
      linarith [h]
    rw [h']
    linarith [mul_nonneg hcosb hsind]
  have hcosd : 0 < Real.cos (b - a) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hdpi⟩
  have hstep2 : (b - a) * Real.cos (b - a) ≤ Real.sin (b - a) := by
    have htan : b - a ≤ Real.tan (b - a) := Real.le_tan hd0 hdpi
    rw [Real.tan_eq_sin_div_cos] at htan
    rw [le_div_iff₀ hcosd] at htan
    linarith [htan]
  calc (b - a) * Real.sin a ≤ (b - a) * (Real.cos (b - a) * Real.sin b) :=
        mul_le_mul_of_nonneg_left hstep1 hd0
    _ = ((b - a) * Real.cos (b - a)) * Real.sin b := by ring
    _ ≤ Real.sin (b - a) * Real.sin b := mul_le_mul_of_nonneg_right hstep2 hsinb

/-- Tangent-line lower bound for the cotangent on `(π/2, π)`: for `π/2 < a ≤ b < π`,
`(b − a) / sin² a ≤ cot a − cot b`.

Indeed `cot a − cot b = sin(b − a)/(sin a sin b)`, so after clearing denominators the claim is
`(b − a) sin b ≤ sin(b − a) sin a`, which is `oidArcATel_sinGap_aux` applied to `π − b ≤ π − a`. -/
private theorem oidArcATel_cotSub_aux (a b : ℝ) (ha : Real.pi / 2 < a) (hab : a ≤ b)
    (hb : b < Real.pi) :
    (b - a) / (Real.sin a) ^ 2 ≤ Real.cot a - Real.cot b := by
  have hsa : 0 < Real.sin a :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (lt_of_le_of_lt hab hb)
  have hsb : 0 < Real.sin b :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hb
  have hkey : (b - a) * Real.sin b ≤ Real.sin (b - a) * Real.sin a := by
    have h1 : (0:ℝ) ≤ Real.pi - b := by linarith
    have h2 : Real.pi - b ≤ Real.pi - a := by linarith
    have h3 : Real.pi - a < Real.pi / 2 := by linarith
    have h := oidArcATel_sinGap_aux (Real.pi - b) (Real.pi - a) h1 h2 h3
    rw [show Real.pi - a - (Real.pi - b) = b - a by ring,
        Real.sin_pi_sub, Real.sin_pi_sub] at h
    linarith [h]
  have hcot : Real.cot a - Real.cot b = Real.sin (b - a) / (Real.sin a * Real.sin b) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
    field_simp
    rw [Real.sin_sub]
    ring
  rw [hcot, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey, hsa]

theorem oidArcATel (lam : ℝ) (hlam : 0 < lam) (n j0 : ℕ) (x : ℕ → ℝ) (hj0 : j0 ≤ n)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hneg : ∀ j < j0, Real.pi / 2 < lam * x j)
    (hpit : ∀ j < j0, lam * x j < Real.pi)
    (j : ℕ) (hj : j < j0) :
    ∑ i ∈ Finset.Ico (j + 1) j0, lam ^ 2 / (Real.sin (lam * x i)) ^ 2
      ≤ 3 * lam * (-Real.cot (lam * x j)) := by
  -- Term-wise bound against the cotangent increment over the *preceding* gap.
  have hterm : ∀ i ∈ Finset.Ico (j + 1) j0,
      lam ^ 2 / (Real.sin (lam * x i)) ^ 2
        ≤ 3 * lam * (Real.cot (lam * x i) - Real.cot (lam * x (i - 1))) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
    have hi1' : 1 ≤ i := by omega
    have him1n : i - 1 < n := by omega
    have him1j0 : i - 1 < j0 := by omega
    have hsub : (i - 1) + 1 = i := Nat.sub_add_cancel hi1'
    have hdi := hdec (i - 1) him1n
    rw [hsub] at hdi
    -- the phase gap is at least `lam / 3`
    have hgap : lam / 3 ≤ lam * x (i - 1) - lam * x i := by
      have h2 := mul_le_mul_of_nonneg_left hdi hlam.le
      have h3 : lam * (x (i - 1) - 1 / 3) = lam * x (i - 1) - lam / 3 := by ring
      rw [h3] at h2
      linarith [h2]
    have hA_gt : Real.pi / 2 < lam * x i := hneg i hi2
    have hA_lt : lam * x i < Real.pi := hpit i hi2
    have hB_lt : lam * x (i - 1) < Real.pi := hpit (i - 1) him1j0
    have hAB : lam * x i ≤ lam * x (i - 1) := by linarith [hgap]
    have hcotsub : (lam * x (i - 1) - lam * x i) / (Real.sin (lam * x i)) ^ 2
        ≤ Real.cot (lam * x i) - Real.cot (lam * x (i - 1)) :=
      oidArcATel_cotSub_aux (lam * x i) (lam * x (i - 1)) hA_gt hAB hB_lt
    have hstep : lam / (Real.sin (lam * x i)) ^ 2
        ≤ 3 * ((lam * x (i - 1) - lam * x i) / (Real.sin (lam * x i)) ^ 2) := by
      have hle : lam ≤ 3 * (lam * x (i - 1) - lam * x i) := by linarith [hgap]
      have hnn : 0 ≤ (1:ℝ) / (Real.sin (lam * x i)) ^ 2 := by positivity
      calc lam / (Real.sin (lam * x i)) ^ 2
          = lam * (1 / (Real.sin (lam * x i)) ^ 2) := by ring
        _ ≤ (3 * (lam * x (i - 1) - lam * x i)) * (1 / (Real.sin (lam * x i)) ^ 2) :=
            mul_le_mul_of_nonneg_right hle hnn
        _ = 3 * ((lam * x (i - 1) - lam * x i) / (Real.sin (lam * x i)) ^ 2) := by ring
    calc lam ^ 2 / (Real.sin (lam * x i)) ^ 2
        = lam * (lam / (Real.sin (lam * x i)) ^ 2) := by ring
      _ ≤ lam * (3 * ((lam * x (i - 1) - lam * x i) / (Real.sin (lam * x i)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep hlam.le
      _ = 3 * lam * ((lam * x (i - 1) - lam * x i) / (Real.sin (lam * x i)) ^ 2) := by ring
      _ ≤ 3 * lam * (Real.cot (lam * x i) - Real.cot (lam * x (i - 1))) :=
          mul_le_mul_of_nonneg_left hcotsub (by linarith [hlam])
  have hsum := Finset.sum_le_sum hterm
  have hle_ico : j + 1 ≤ j0 := by omega
  have htel : ∑ i ∈ Finset.Ico (j + 1) j0,
        (Real.cot (lam * x i) - Real.cot (lam * x (i - 1)))
      = Real.cot (lam * x (j0 - 1)) - Real.cot (lam * x j) := by
    have h := Finset.sum_Ico_sub (fun i => Real.cot (lam * x (i - 1))) hle_ico
    simpa only [Nat.add_sub_cancel] using h
  have hbnd : Real.cot (lam * x (j0 - 1)) ≤ 0 := by
    have hlt : j0 - 1 < j0 := by omega
    have h1 : Real.pi / 2 < lam * x (j0 - 1) := hneg (j0 - 1) hlt
    have h2 : lam * x (j0 - 1) < Real.pi := hpit (j0 - 1) hlt
    have hsin : 0 < Real.sin (lam * x (j0 - 1)) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) h2
    have hcos : Real.cos (lam * x (j0 - 1)) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [Real.pi_pos, h2])
    rw [Real.cot_eq_cos_div_sin]
    exact le_of_lt (div_neg_of_neg_of_pos hcos hsin)
  calc ∑ i ∈ Finset.Ico (j + 1) j0, lam ^ 2 / (Real.sin (lam * x i)) ^ 2
      ≤ ∑ i ∈ Finset.Ico (j + 1) j0,
          3 * lam * (Real.cot (lam * x i) - Real.cot (lam * x (i - 1))) := hsum
    _ = 3 * lam * ∑ i ∈ Finset.Ico (j + 1) j0,
          (Real.cot (lam * x i) - Real.cot (lam * x (i - 1))) := by rw [Finset.mul_sum]
    _ = 3 * lam * (Real.cot (lam * x (j0 - 1)) - Real.cot (lam * x j)) := by rw [htel]
    _ ≤ 3 * lam * (-Real.cot (lam * x j)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith [hlam])
        linarith [hbnd]

end Work.PARIMPL2.Direct
