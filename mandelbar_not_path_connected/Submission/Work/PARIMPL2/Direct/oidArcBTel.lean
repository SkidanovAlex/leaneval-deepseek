import Mathlib
import Submission.Work.PARIMPL2.Direct.orbitCrossBound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Derivative of `t ↦ cos t / sin t` (the cotangent) wherever `sin t ≠ 0`:
the derivative is `-1 / sin²t`. -/
private lemma hasDerivAt_cot_div (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt (fun y => Real.cos y / Real.sin y) (-(1 / (Real.sin x) ^ 2)) x := by
  have h : HasDerivAt (fun y => Real.cos y / Real.sin y)
      (((-Real.sin x) * Real.sin x - Real.cos x * Real.cos x) / (Real.sin x) ^ 2) x :=
    (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx
  refine h.congr_deriv ?_
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- One-step mean-value bound for the cotangent on `(0, π/2]`:
for `0 < b ≤ a ≤ π/2`,
`(a - b) / sin²a ≤ cot b - cot a`.

The mean value theorem gives some `c ∈ (b, a)` with
`cot b - cot a = (a - b) / sin²c`; since `c < a` and `sin` is increasing on `(0, π/2]`,
`sin²c ≤ sin²a`, whence `(a - b)/sin²a ≤ (a - b)/sin²c`. -/
private lemma cot_one_step {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) (ha : a ≤ Real.pi / 2) :
    (a - b) / (Real.sin a) ^ 2 ≤ Real.cot b - Real.cot a := by
  rcases lt_or_eq_of_le hba with hlt | heq
  · have hmem : ∀ t ∈ Set.Icc b a, Real.sin t ≠ 0 := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hb ht.1
      have htpi : t < Real.pi := by linarith [ht.2, ha, Real.pi_pos]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht0 htpi)
    have hcont : ContinuousOn (fun y => Real.cos y / Real.sin y) (Set.Icc b a) :=
      Real.continuous_cos.continuousOn.div Real.continuous_sin.continuousOn hmem
    have hderiv : ∀ t ∈ Set.Ioo b a,
        HasDerivAt (fun y => Real.cos y / Real.sin y) (-(1 / (Real.sin t) ^ 2)) t := by
      intro t ht
      exact hasDerivAt_cot_div t (hmem t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope
      (fun y => Real.cos y / Real.sin y) (fun t => -(1 / (Real.sin t) ^ 2)) hlt hcont hderiv
    rw [Set.mem_Ioo] at hc
    obtain ⟨hbc, hca⟩ := hc
    have hne : a - b ≠ 0 := by linarith
    have hA : -(Real.cos a / Real.sin a - Real.cos b / Real.sin b)
        = (1 / (Real.sin c) ^ 2) * (a - b) := by
      rw [eq_div_iff hne] at hceq
      rw [← hceq]
      ring
    have hkey : Real.cos b / Real.sin b - Real.cos a / Real.sin a
        = (a - b) / (Real.sin c) ^ 2 := by
      rw [← neg_sub (Real.cos a / Real.sin a) (Real.cos b / Real.sin b), hA,
        one_div_mul_eq_div]
    have hsq : (Real.sin c) ^ 2 ≤ (Real.sin a) ^ 2 := by
      have hclt : Real.sin c < Real.sin a :=
        Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hbc, hb]) ha hca
      have hcpos : 0 < Real.sin c := Real.sin_pos_of_pos_of_lt_pi (by linarith [hbc, hb])
        (by linarith [hca, ha, Real.pi_pos])
      nlinarith [hclt, hcpos]
    have hmono : (a - b) / (Real.sin a) ^ 2 ≤ (a - b) / (Real.sin c) ^ 2 :=
      div_le_div_of_nonneg_left (by linarith) (pow_pos (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hbc, hb]) (by linarith [hca, ha, Real.pi_pos])) 2) hsq
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, hkey]
    exact hmono
  · subst heq
    simp

/-- The sum of `λ² / sin²(λ x_i)` over a `1/3`-decreasing run with all the angles `λ x_i`
in `(0, π/2]` is dominated by `3λ cot(λ x_j) + λ²/sin²(λ x_j)`.

Each step is telescoped through the drop of the cotangent:
`λ² / sin²(λ x_i) ≤ 3λ (cot(λ x_{i+1}) - cot(λ x_i))`, and the resulting telescoping
sum is `3λ (cot(λ x_j) - cot(λ x_{j₀})) ≤ 3λ cot(λ x_j)` since `cot(λ x_{j₀}) ≥ 0`. -/
theorem oidArcBTel (lam : ℝ) (hlam : 0 < lam) (j0 j : ℕ) (x : ℕ → ℝ) (hj : j0 ≤ j)
    (hdec : ∀ k < j, x (k + 1) ≤ x k - 1 / 3)
    (harc : ∀ k, j0 ≤ k → k ≤ j → 0 < lam * x k ∧ lam * x k ≤ Real.pi / 2) :
    ∑ i ∈ Finset.Ico j0 (j + 1), lam ^ 2 / (Real.sin (lam * x i)) ^ 2
      ≤ 3 * lam * Real.cot (lam * x j) + lam ^ 2 / (Real.sin (lam * x j)) ^ 2 := by
  have hstep : ∀ i ∈ Finset.Ico j0 j,
      lam ^ 2 / (Real.sin (lam * x i)) ^ 2
        ≤ 3 * lam * (Real.cot (lam * x (i + 1)) - Real.cot (lam * x i)) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    obtain ⟨hij0, hij⟩ := hi
    have hi1le : i + 1 ≤ j := Nat.succ_le_of_lt hij
    have hu_pos : 0 < lam * x i := (harc i hij0 (le_of_lt hij)).1
    have hu_le : lam * x i ≤ Real.pi / 2 := (harc i hij0 (le_of_lt hij)).2
    have hv_pos : 0 < lam * x (i + 1) :=
      (harc (i + 1) (le_trans hij0 (Nat.le_succ i)) hi1le).1
    have hv_le : lam * x (i + 1) ≤ lam * x i - lam / 3 := by
      have h := mul_le_mul_of_nonneg_left (hdec i hij) hlam.le
      rwa [mul_sub, mul_one_div] at h
    have hvu : lam * x (i + 1) ≤ lam * x i := by linarith
    have hgap : lam / 3 ≤ lam * x i - lam * x (i + 1) := by linarith
    have hone := cot_one_step hv_pos hvu hu_le
    have hsin2pos : 0 < (Real.sin (lam * x i)) ^ 2 :=
      pow_pos (Real.sin_pos_of_pos_of_lt_pi hu_pos (by linarith [hu_le, Real.pi_pos])) 2
    have h3 : lam / (Real.sin (lam * x i)) ^ 2
        ≤ 3 * (Real.cot (lam * x (i + 1)) - Real.cot (lam * x i)) := by
      have h4 : (lam / 3) / (Real.sin (lam * x i)) ^ 2
          ≤ (lam * x i - lam * x (i + 1)) / (Real.sin (lam * x i)) ^ 2 :=
        div_le_div_of_nonneg_right hgap hsin2pos.le
      have h5 : lam / (Real.sin (lam * x i)) ^ 2
          = 3 * ((lam / 3) / (Real.sin (lam * x i)) ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      rw [h5]; linarith
    calc lam ^ 2 / (Real.sin (lam * x i)) ^ 2
        = lam * (lam / (Real.sin (lam * x i)) ^ 2) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ ≤ lam * (3 * (Real.cot (lam * x (i + 1)) - Real.cot (lam * x i))) :=
          mul_le_mul_of_nonneg_left h3 hlam.le
      _ = 3 * lam * (Real.cot (lam * x (i + 1)) - Real.cot (lam * x i)) := by ring
  have htel : ∑ i ∈ Finset.Ico j0 j,
        (Real.cot (lam * x (i + 1)) - Real.cot (lam * x i))
      = Real.cot (lam * x j) - Real.cot (lam * x j0) :=
    Finset.sum_Ico_sub (fun i => Real.cot (lam * x i)) hj
  have hsum_eq : ∑ i ∈ Finset.Ico j0 j,
        3 * lam * (Real.cot (lam * x (i + 1)) - Real.cot (lam * x i))
      = 3 * lam * (Real.cot (lam * x j) - Real.cot (lam * x j0)) := by
    rw [← Finset.mul_sum, htel]
  have hcotj0 : 0 ≤ Real.cot (lam * x j0) := by
    have h := harc j0 le_rfl hj
    have hsin : 0 < Real.sin (lam * x j0) :=
      Real.sin_pos_of_pos_of_lt_pi h.1 (by linarith [h.2, Real.pi_pos])
    have hcos : 0 ≤ Real.cos (lam * x j0) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [h.1], h.2⟩
    rw [Real.cot_eq_cos_div_sin]
    exact div_nonneg hcos hsin.le
  rw [Finset.sum_Ico_succ_top hj (fun i => lam ^ 2 / (Real.sin (lam * x i)) ^ 2)]
  calc ∑ i ∈ Finset.Ico j0 j, lam ^ 2 / (Real.sin (lam * x i)) ^ 2
        + lam ^ 2 / (Real.sin (lam * x j)) ^ 2
      ≤ (∑ i ∈ Finset.Ico j0 j,
            3 * lam * (Real.cot (lam * x (i + 1)) - Real.cot (lam * x i)))
          + lam ^ 2 / (Real.sin (lam * x j)) ^ 2 :=
        add_le_add (Finset.sum_le_sum hstep) (le_refl _)
    _ = 3 * lam * (Real.cot (lam * x j) - Real.cot (lam * x j0))
          + lam ^ 2 / (Real.sin (lam * x j)) ^ 2 := by
        rw [hsum_eq]
    _ ≤ 3 * lam * Real.cot (lam * x j) + lam ^ 2 / (Real.sin (lam * x j)) ^ 2 := by
        have h1 : 3 * lam * (Real.cot (lam * x j) - Real.cot (lam * x j0))
            ≤ 3 * lam * Real.cot (lam * x j) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith

end Work.PARIMPL2.Direct
