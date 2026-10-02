import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-- Auxiliary inequality: for `0 ≤ t ≤ π` and `A - t ∈ [0, π]`,
`sin A - sin (A - t) ≤ sin t`.  The proof expands `sin A = sin ((A - t) + t)`. -/
theorem sin_sub_sin_le_aux {A t : ℝ} (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi)
    (hAt0 : 0 ≤ A - t) (hAtπ : A - t ≤ Real.pi) :
    Real.sin A - Real.sin (A - t) ≤ Real.sin t := by
  have hA : Real.sin A = Real.sin ((A - t) + t) := by ring_nf
  rw [hA, Real.sin_add]
  have hsin : 0 ≤ Real.sin (A - t) := Real.sin_nonneg_of_nonneg_of_le_pi hAt0 hAtπ
  have hcostm1 : Real.cos t - 1 ≤ 0 := by linarith [Real.cos_le_one t]
  have hsint : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 htπ
  have hcosAt : Real.cos (A - t) ≤ 1 := Real.cos_le_one _
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hsin hcostm1, mul_le_of_le_one_left hsint hcosAt]

/-- Quantitative form of `petalTrigBound`: the expression `sin u - ε sin(m u - (m-1) θ₁)` is
bounded below by `min (ε · sin((m-1)θ₁/m)) (sin((m-1)θ₁/m) - ε · sin((m+1)θ₁))`. -/
theorem petalTrigBoundMin (m : ℕ) (hm : 3 ≤ m) (θ₁ ε u : ℝ)
    (hθ1 : 0 < θ₁) (hπ : ((m : ℝ) + 1) * θ₁ < Real.pi / 2)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 2 * θ₁) :
    min (ε * Real.sin (((m : ℝ) - 1) * θ₁ / m))
        (Real.sin (((m : ℝ) - 1) * θ₁ / m) - ε * Real.sin (((m : ℝ) + 1) * θ₁))
      ≤ Real.sin u - ε * Real.sin ((m : ℝ) * u - ((m : ℝ) - 1) * θ₁) := by
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have h1lt : (1 : ℝ) < (m : ℝ) + 1 := by linarith
  have h2lt : (2 : ℝ) < (m : ℝ) + 1 := by linarith
  have h2θ : 2 * θ₁ < Real.pi / 2 := lt_trans (mul_lt_mul_of_pos_right h2lt hθ1) hπ
  have hθlt : θ₁ < Real.pi / 2 := by
    have h : θ₁ < ((m : ℝ) + 1) * θ₁ := lt_mul_of_one_lt_left hθ1 h1lt
    linarith
  -- basic size facts about the two "angles"
  have hKpos : 0 < ((m : ℝ) - 1) * θ₁ := mul_pos hm1pos hθ1
  have hK_lt : ((m : ℝ) - 1) * θ₁ < Real.pi / 2 :=
    lt_trans (mul_lt_mul_of_pos_right (by linarith : ((m : ℝ) - 1) < (m : ℝ) + 1) hθ1) hπ
  have hApos : 0 < ((m : ℝ) - 1) * θ₁ / m := by positivity
  have hA_lt : ((m : ℝ) - 1) * θ₁ / m < θ₁ := by
    have hcoef : ((m : ℝ) - 1) / (m : ℝ) < 1 := by rw [div_lt_one hmpos]; linarith
    have h2 := mul_lt_mul_of_pos_right hcoef hθ1
    have heq : ((m : ℝ) - 1) * θ₁ / (m : ℝ) = ((m : ℝ) - 1) / (m : ℝ) * θ₁ := by ring
    rw [heq]; simpa using h2
  have hA_pi : ((m : ℝ) - 1) * θ₁ / m < Real.pi / 2 := lt_trans hA_lt hθlt
  have hA_pi' : ((m : ℝ) - 1) * θ₁ / m ≤ Real.pi / 2 := le_of_lt hA_pi
  have hB_pi : ((m : ℝ) + 1) * θ₁ ≤ Real.pi / 2 := le_of_lt hπ
  -- bounds for `w = m u - (m-1) θ₁`
  have hw_ub : (m : ℝ) * u - ((m : ℝ) - 1) * θ₁ ≤ ((m : ℝ) + 1) * θ₁ := by
    have hu1' : (m : ℝ) * u ≤ (m : ℝ) * (2 * θ₁) :=
      mul_le_mul_of_nonneg_left hu1 (le_of_lt hmpos)
    nlinarith
  have hw_lb : -(((m : ℝ) - 1) * θ₁) ≤ (m : ℝ) * u - ((m : ℝ) - 1) * θ₁ := by
    have h : 0 ≤ (m : ℝ) * u := mul_nonneg (le_of_lt hmpos) hu0
    linarith
  -- reparametrisation: `u = A - (-w)/m`
  have hu_rel : ((m : ℝ) - 1) * θ₁ / m
      - (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) / m = u := by
    field_simp
    ring
  rw [min_le_iff]
  rcases le_or_gt 0 ((m : ℝ) * u - ((m : ℝ) - 1) * θ₁) with hw0 | hw0
  · -- Case `w ≥ 0`: use the second branch of the `min`, with `u ≥ A`.
    right
    have hAu : ((m : ℝ) - 1) * θ₁ / m ≤ u := by
      rw [← hu_rel]
      have h : (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) / m ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hmpos)
      linarith
    have hsinA : Real.sin (((m : ℝ) - 1) * θ₁ / m) ≤ Real.sin u :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hApos, Real.pi_pos])
        (le_of_lt (lt_of_le_of_lt hu1 h2θ)) hAu
    have hsinw : Real.sin ((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)
        ≤ Real.sin (((m : ℝ) + 1) * θ₁) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hw0, Real.pi_pos]) hB_pi hw_ub
    have hmul := mul_le_mul_of_nonneg_left hsinw hε0
    linarith
  · -- Case `w < 0`.
    left
    have hv0 : 0 < -((m : ℝ) * u - ((m : ℝ) - 1) * θ₁) := by linarith
    have hvu_le : -((m : ℝ) * u - ((m : ℝ) - 1) * θ₁) ≤ ((m : ℝ) - 1) * θ₁ := by linarith
    have hSrw : Real.sin u - ε * Real.sin ((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)
        = Real.sin u + ε * Real.sin (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) := by
      rw [Real.sin_neg]; ring
    rw [hSrw]
    rcases le_or_gt (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) (((m : ℝ) - 1) * θ₁ / m) with hvA | hAv
    · -- Sub-case `-w ≤ A`.
      have haux : Real.sin (((m : ℝ) - 1) * θ₁ / m) - Real.sin u
          ≤ Real.sin ((-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) / m) := by
        have h := sin_sub_sin_le_aux (A := ((m : ℝ) - 1) * θ₁ / m)
          (t := (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) / m)
          (div_nonneg (le_of_lt hv0) (le_of_lt hmpos))
          (by
            have h1 : (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) / m
                ≤ -((m : ℝ) * u - ((m : ℝ) - 1) * θ₁) :=
              div_le_self (le_of_lt hv0) (by linarith : (1 : ℝ) ≤ (m : ℝ))
            linarith [h1, hvu_le, hK_lt, Real.pi_pos])
          (by rw [hu_rel]; exact hu0)
          (by rw [hu_rel]; linarith [hu1, h2θ, Real.pi_pos])
        rwa [hu_rel] at h
      have hsinm : Real.sin ((-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) / m)
          ≤ Real.sin (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by have h := div_nonneg (le_of_lt hv0) (le_of_lt hmpos); linarith [h, Real.pi_pos])
          (by linarith [hvu_le, hK_lt])
          (div_le_self (le_of_lt hv0) (by linarith : (1 : ℝ) ≤ (m : ℝ)))
      have hsinu : Real.sin (((m : ℝ) - 1) * θ₁ / m)
          - Real.sin (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) ≤ Real.sin u := by
        linarith [haux, hsinm]
      have hsinAw : Real.sin (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁))
          ≤ Real.sin (((m : ℝ) - 1) * θ₁ / m) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hv0, Real.pi_pos]) hA_pi' hvA
      have hmulnn : 0 ≤ (1 - ε) * (Real.sin (((m : ℝ) - 1) * θ₁ / m)
          - Real.sin (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁))) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hsinu, hmulnn]
    · -- Sub-case `A < -w`.
      have hsinu0 : 0 ≤ Real.sin u :=
        Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith [hu1, h2θ, Real.pi_pos])
      have hsinvA : Real.sin (((m : ℝ) - 1) * θ₁ / m)
          ≤ Real.sin (-((m : ℝ) * u - ((m : ℝ) - 1) * θ₁)) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hApos, Real.pi_pos])
          (by linarith [hvu_le, hK_lt]) (le_of_lt hAv)
      have hmul := mul_le_mul_of_nonneg_left hsinvA hε0
      linarith

end Work.FatouDeg.Petal
