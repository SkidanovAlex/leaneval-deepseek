import Mathlib
import Submission.Work.FatouDeg.Petal.petalGeomDefs
import Submission.Work.FatouDeg.Petal.petalSmallR
import Submission.Work.FatouDeg.Petal.petalComplexEstim
import Submission.Work.FatouDeg.Petal.petalContractionChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

noncomputable section

open Set Filter Metric

/-- `‖1 - w‖ ^ 2 = 1 - 2 * Re w + ‖w‖ ^ 2`. -/
private theorem pnbAux_normsq (w : ℂ) : ‖1 - w‖ ^ 2 = 1 - 2 * w.re + ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  simp [Complex.normSq]
  ring

/-! ### The main lemma -/

/-- Norm decrease and contraction in the chart `z ↦ ‖z‖^(-(m-1))` for the map
`Pfun m G z = z - z^m + z^(m+1) G z`, on the part of `Dom m ρ` where
`Re (z^(m-1)) ≥ cm · ‖z‖^(m-1)`. -/
theorem petalNormBound (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) (M : ℝ) (hM : 0 ≤ M)
    (cm : ℝ) (hcm : 0 < cm) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      (∀ w : ℂ, ‖w‖ ≤ 2 * ρ → ‖G.eval w‖ ≤ M) →
      ∀ z : ℂ, z ≠ 0 → ‖z‖ < 2 * ρ → Real.cos (((m : ℝ) - 1) * z.arg) ≥ cm →
        ‖Pfun m G z‖ ≤ ‖z‖ ∧
        (‖z‖ ^ (m - 1))⁻¹ + (((m : ℝ) - 1) * cm / 2) ≤ (‖Pfun m G z‖ ^ (m - 1))⁻¹ := by
  obtain ⟨R, hRpos, hR⟩ := petalSmallR M cm hM hcm (m - 1) (by omega)
  refine ⟨R / 2, by linarith, ?_⟩
  intro ρ hρ hρR hG z hz hzρ hcos
  have hGz : ‖G.eval z‖ ≤ M := hG z (le_of_lt hzρ)
  set r : ℝ := ‖z‖ with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact norm_pos_iff.mpr hz
  have hrR : r < R := by
    rw [hrdef]
    have h : 2 * ρ ≤ R := by linarith
    linarith
  obtain ⟨hr1, hrnr, hrn1, hrM1, hrn1M, hmain⟩ := hR r hrpos hrR
  have hr0 : 0 ≤ r := le_of_lt hrpos
  -- the linearisation of `Pfun` at `z`
  set w₀ : ℂ := z ^ (m - 1) * (1 - z * G.eval z) with hwdef
  have hPfun : Pfun m G z = z * (1 - w₀) := by
    have h := Pfun_eq_mul_one_sub_pgx m (by omega : 1 ≤ m) G z
    rw [h, hwdef, pgx]
  -- real-part and modulus estimates for the linearisation term
  obtain ⟨hwre0, hwnorm0⟩ := petalComplexEstim m hm G M hM cm hz hGz hcos
  have hwre : w₀.re ≥ cm * r ^ (m - 1) - r ^ m * M := by
    rw [hwdef, hrdef]; exact hwre0
  have hwnorm : ‖w₀‖ ≤ r ^ (m - 1) * (1 + r * M) := by
    rw [hwdef, hrdef]; exact hwnorm0
  set s : ℝ := ‖1 - w₀‖ with hsdef
  -- `1 - s ^ 2` is bounded below by `(3/2) cm r^(m-1)`
  have hδ : (3 / 2) * cm * r ^ (m - 1) ≤ 1 - s ^ 2 := by
    have h2 : 1 - s ^ 2 = 2 * w₀.re - ‖w₀‖ ^ 2 := by
      rw [hsdef]; linarith [pnbAux_normsq w₀]
    rw [h2]
    have hm1 : (m - 1) + 1 = m := Nat.sub_add_cancel (by omega : 1 ≤ m)
    have hw2 : ‖w₀‖ ^ 2 ≤ r ^ (2 * (m - 1)) * (1 + r * M) ^ 2 := by
      calc ‖w₀‖ ^ 2 ≤ (r ^ (m - 1) * (1 + r * M)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hwnorm 2
        _ = r ^ (2 * (m - 1)) * (1 + r * M) ^ 2 := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm (m - 1) 2]
    have hmb : 2 * r ^ m * M + r ^ (2 * (m - 1)) * (1 + r * M) ^ 2
        ≤ (cm / 2) * r ^ (m - 1) := by
      have hh := hmain
      rwa [hm1] at hh
    nlinarith [hwre, hw2, hmb]
  have hs_le_one : s ≤ 1 := by
    have hpos : 0 < (3 / 2 : ℝ) * cm * r ^ (m - 1) := by positivity
    have h : s ^ 2 ≤ 1 := by linarith
    nlinarith [sq_nonneg (s - 1)]
  have hs_ge : 1 / 2 ≤ s := by
    have h1 : (1 : ℝ) - ‖w₀‖ ≤ ‖1 - w₀‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) w₀
      simpa using hh
    rw [← hsdef] at h1
    have h2 : ‖w₀‖ ≤ 1 / 2 := le_trans hwnorm hrn1M
    linarith
  have hPnorm : ‖Pfun m G z‖ = r * s := by
    rw [hPfun, norm_mul, hsdef, hrdef]
  constructor
  · rw [hPnorm, hrdef]
    exact mul_le_of_le_one_right (norm_nonneg z) hs_le_one
  · have hk : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
    have hchart : ((m - 1 : ℕ) : ℝ) * cm / 2 ≤ (r ^ (m - 1))⁻¹ * ((s⁻¹) ^ (m - 1) - 1) :=
      petalContractionChart cm hcm (m - 1) (by omega) hrpos hs_ge hs_le_one hδ
    rw [hk] at hchart
    have hstep : (r ^ (m - 1))⁻¹ + (((m : ℝ) - 1) * cm / 2)
        ≤ (r ^ (m - 1))⁻¹ * (s⁻¹) ^ (m - 1) := by
      nlinarith [hchart]
    have hzn : ‖z‖ ^ (m - 1) = r ^ (m - 1) := by rw [hrdef]
    rw [hPnorm, mul_pow, mul_inv, ← inv_pow s (m - 1), hzn]
    exact hstep

end

end Work.FatouDeg.Petal
