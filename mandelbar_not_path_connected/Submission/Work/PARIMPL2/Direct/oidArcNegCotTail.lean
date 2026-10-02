import Mathlib
import Submission.Work.PARIMPL2.Direct.oidArcNegCotOneStep

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- The cotangent `cos t / sin t` is antitone on `(0, π/2]`:
if `0 < a ≤ b ≤ π/2` then `cos b / sin b ≤ cos a / sin a`.
This is a purely algebraic consequence of `sin (a - b) ≤ 0`. -/
lemma aux_cot_antitone (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    Real.cos b / Real.sin b ≤ Real.cos a / Real.sin a := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  rw [div_le_div_iff₀ hsb hsa]
  have hsin : Real.sin (a - b) = Real.sin a * Real.cos b - Real.cos a * Real.sin b := Real.sin_sub a b
  have hle : Real.sin (a - b) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [Real.pi_pos])
  linarith [hsin, hle]

/-- Tangent-line (concavity) inequality for `t ↦ log (sin t)` on `(0, π/2]`:
for `0 < x ≤ y ≤ π/2`,
`(y - x) * cot y ≤ log (sin y) - log (sin x)`.
Proved from the mean value theorem applied to `log (sin ·)` together with
antitonicity of `cot`. -/
lemma aux_logSin_tangent (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ Real.pi / 2) :
    (y - x) * (Real.cos y / Real.sin y) ≤ Real.log (Real.sin y) - Real.log (Real.sin x) := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]; simp
  · have hsin_ne : ∀ t ∈ Set.Icc x y, Real.sin t ≠ 0 := by
      intro t ht
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos]))
    have hcont : ContinuousOn (fun t => Real.log (Real.sin t)) (Set.Icc x y) :=
      Real.continuous_sin.continuousOn.log hsin_ne
    have hderiv : ∀ t ∈ Set.Ioo x y,
        HasDerivAt (fun t => Real.log (Real.sin t)) (Real.cos t / Real.sin t) t := by
      intro t ht
      exact (Real.hasDerivAt_sin t).log (hsin_ne t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    obtain ⟨c, hc_mem, hc_eq⟩ :=
      exists_hasDerivAt_eq_slope (fun t => Real.log (Real.sin t))
        (fun t => Real.cos t / Real.sin t) hlt hcont hderiv
    rw [Set.mem_Ioo] at hc_mem
    obtain ⟨hxc, hcy⟩ := hc_mem
    have hyx : 0 < y - x := by linarith
    have hcycot : Real.cos y / Real.sin y ≤ Real.cos c / Real.sin c :=
      aux_cot_antitone c y (by linarith) (le_of_lt hcy) hy
    have hprod : (y - x) * (Real.cos c / Real.sin c) =
        Real.log (Real.sin y) - Real.log (Real.sin x) := by
      rw [hc_eq]
      field_simp
    calc (y - x) * (Real.cos y / Real.sin y)
        ≤ (y - x) * (Real.cos c / Real.sin c) := mul_le_mul_of_nonneg_left hcycot (le_of_lt hyx)
      _ = Real.log (Real.sin y) - Real.log (Real.sin x) := hprod

theorem oidArcNegCotTail (h : ℝ) (hh : 0 < h) (m : ℕ) (v : ℕ → ℝ)
    (hv_pos : ∀ j ≤ m, 0 < v j)
    (hv_le : ∀ j ≤ m, v j ≤ Real.pi / 2)
    (hv_mono : ∀ j < m, v (j + 1) ≤ v j)
    (hv_cond : ∀ j < m, v j = Real.pi / 2 ∨ v (j + 1) + h ≤ v j) :
    h * (∑ j ∈ Finset.range m, Real.cos (v j) / Real.sin (v j))
      ≤ (Real.pi / 2) * (Real.log (Real.sin (v 0)) - Real.log (Real.sin (v m))) := by
  have hcot_nonneg : ∀ j < m, 0 ≤ Real.cos (v j) / Real.sin (v j) := by
    intro j hj
    have hpos : 0 < v j := hv_pos j (le_of_lt hj)
    have hcos : 0 ≤ Real.cos (v j) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · linarith [Real.pi_pos, hpos]
      · exact hv_le j (le_of_lt hj)
    have hsin : 0 ≤ Real.sin (v j) :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_pos, hv_le j (le_of_lt hj)]))
    exact div_nonneg hcos hsin
  have key : ∀ j ∈ Finset.range m,
      h * (Real.cos (v j) / Real.sin (v j))
        ≤ (Real.pi / 2) * (Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1)))) := by
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have hjle : j ≤ m := le_of_lt hjlt
    have hj1le : j + 1 ≤ m := Nat.succ_le_of_lt hjlt
    have hvj_pos : 0 < v j := hv_pos j hjle
    have hvj_le : v j ≤ Real.pi / 2 := hv_le j hjle
    have hvj1_pos : 0 < v (j+1) := hv_pos (j+1) hj1le
    have hvj1_le : v (j+1) ≤ Real.pi / 2 := hv_le (j+1) hj1le
    have hmono : v (j+1) ≤ v j := hv_mono j hjlt
    rcases hv_cond j hjlt with hval | hgap
    · rw [hval, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.log_one, zero_div, mul_zero]
      apply mul_nonneg
      · linarith [Real.pi_pos]
      · have h1 : 0 ≤ Real.sin (v (j+1)) :=
          le_of_lt (Real.sin_pos_of_pos_of_lt_pi hvj1_pos (by linarith [Real.pi_pos, hvj1_le]))
        have h2 : Real.log (Real.sin (v (j+1))) ≤ 0 := Real.log_nonpos h1 (Real.sin_le_one _)
        linarith
    · have hle : h ≤ v j - v (j+1) := by linarith
      have hcnn : 0 ≤ Real.cos (v j) / Real.sin (v j) := hcot_nonneg j hjlt
      have htang : (v j - v (j+1)) * (Real.cos (v j) / Real.sin (v j))
          ≤ Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1))) :=
        aux_logSin_tangent (v (j+1)) (v j) hvj1_pos hmono hvj_le
      have hLnn : 0 ≤ Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1))) :=
        le_trans (mul_nonneg (by linarith) hcnn) htang
      have h1 : h * (Real.cos (v j) / Real.sin (v j))
          ≤ (v j - v (j+1)) * (Real.cos (v j) / Real.sin (v j)) :=
        mul_le_mul_of_nonneg_right hle hcnn
      have hge1 : 1 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
      have h2 : Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1)))
          ≤ (Real.pi / 2) * (Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1)))) := by
        calc Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1)))
            = 1 * (Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1)))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hge1 hLnn
      linarith [h1, htang, h2]
  calc h * (∑ j ∈ Finset.range m, Real.cos (v j) / Real.sin (v j))
      = ∑ j ∈ Finset.range m, h * (Real.cos (v j) / Real.sin (v j)) := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range m,
          (Real.pi / 2) * (Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1)))) :=
        Finset.sum_le_sum key
    _ = (Real.pi / 2) *
          (∑ j ∈ Finset.range m, (Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1))))) := by
        rw [Finset.mul_sum]
    _ = (Real.pi / 2) * (Real.log (Real.sin (v 0)) - Real.log (Real.sin (v m))) := by
        congr 1
        have htel : (∑ j ∈ Finset.range m,
              (Real.log (Real.sin (v j)) - Real.log (Real.sin (v (j+1)))))
            = - ∑ j ∈ Finset.range m,
              (Real.log (Real.sin (v (j+1))) - Real.log (Real.sin (v j))) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [htel]
        have hstep := Finset.sum_range_sub (fun j => Real.log (Real.sin (v j))) m
        rw [hstep]
        ring

end Work.PARIMPL2.Direct
