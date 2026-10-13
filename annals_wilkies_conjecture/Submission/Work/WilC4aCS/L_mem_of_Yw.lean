import Mathlib
import Submission.Work.WilC4aCS.Defs
import Submission.Work.WilC4aCS.Yw_iff
import Submission.Work.WilC4aCS.wpoly_eq_Qeval

namespace Work.WilC4aCS

/-- If `τ` and `u` are two nonzero reals of the same sign (`SignType.sign τ = SignType.sign u`)
and `τ * Y` is positive, then `u * Y` is positive as well. -/
private lemma sign_mul_pos_of_sign_eq {τ u Y : ℝ} (hu : u ≠ 0)
    (h : SignType.sign τ = SignType.sign u) (hτY : 0 < τ * Y) : 0 < u * Y := by
  have h' : 0 < Y * τ := by rwa [mul_comm] at hτY
  have hune : SignType.sign u ≠ 0 := sign_ne_zero.mpr hu
  rcases SignType.trichotomy (SignType.sign τ) with hτ | hτ | hτ
  · have hτneg : τ < 0 := sign_eq_neg_one_iff.mp hτ
    have huneg : u < 0 := sign_eq_neg_one_iff.mp (h ▸ hτ)
    exact mul_pos_of_neg_of_neg huneg (neg_of_mul_pos_left h' (le_of_lt hτneg))
  · exact absurd (h ▸ hτ) hune
  · have hτpos : 0 < τ := sign_eq_one_iff.mp hτ
    have hupos : 0 < u := sign_eq_one_iff.mp (h ▸ hτ)
    exact mul_pos hupos (pos_of_mul_pos_left h' (le_of_lt hτpos))

theorem L_mem_of_Yw {n l : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (g : Fin l → (Fin (n + 1) → ℝ) → ℝ) (h : Fin (l + 1) → (Fin (n + 1) → ℝ) → ℝ)
    (h0 : h 0 = F) (hs : ∀ j, h (Fin.succ j) = g j)
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (d : Fin (l + 1) → ℕ) (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ)
    (u : Fin (l + 1) → (Fin (n + 1) → ℝ) → ℝ) (δ : ℝ)
    (hid : ∀ x, ‖x‖ < δ → ∀ i, h i (L x) = u i x * WilkiesDesign.CG.C4a.wpoly (a i) x)
    (hu : ∀ x, ‖x‖ < δ → ∀ i, u i x ≠ 0)
    (hus : ∀ x, ‖x‖ < δ → ∀ i, SignType.sign (u i x) = SignType.sign (u i 0))
    (τ : Fin l → ℝ) (hτ : ∀ j, SignType.sign (τ j) = SignType.sign (u (Fin.succ j) 0))
    {y : Fin (n + 1) → ℝ} (hy : ‖y‖ < δ) (hyw : y ∈ Work.WilC4aCS.Yw d a τ) :
    L y ∈ WilkiesDesign.CG.C4a.BasicSA F g := by
  -- `δ` is positive because it dominates the nonnegative `‖y‖`
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg y) hy
  -- the `Yw` sign conditions on the Weierstrass coefficients of `y`
  obtain ⟨hQ0, hQpos⟩ := (Work.WilC4aCS.Yw_iff d a τ y).mp hyw
  -- `wpoly (a i) y` is the same as the coefficient-space evaluation at `y`
  have hwp : ∀ i, WilkiesDesign.CG.C4a.wpoly (a i) y
      = Work.WilC4aCS.Qeval d (Work.WilC4aCS.coefFun d a (Fin.init y)) (y (Fin.last n)) i := by
    intro i
    have := Work.WilC4aCS.wpoly_eq_Qeval d a (Fin.init y) (y (Fin.last n)) i
    rwa [Fin.snoc_init_self y] at this
  refine ⟨?_, ?_⟩
  · -- the equation `F = 0`: `h 0 (L y) = u 0 y * wpoly (a 0) y = u 0 y * 0 = 0`
    rw [← h0, hid y hy 0, hwp 0, hQ0, mul_zero]
  · -- the inequalities: `g j (L y)` and `Qeval … (Fin.succ j)` carry the same sign as `τ j`
    intro j
    rw [← hs j, hid y hy (Fin.succ j), hwp (Fin.succ j)]
    exact sign_mul_pos_of_sign_eq (hu y hy (Fin.succ j))
      ((hτ j).trans (hus y hy (Fin.succ j)).symm) (hQpos j)

end Work.WilC4aCS
