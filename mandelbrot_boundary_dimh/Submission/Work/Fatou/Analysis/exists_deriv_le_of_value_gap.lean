import Mathlib
import Submission.Unif.Commons.Analysis.Complex.Landau.landau_theorem
import Submission.Unif.Commons.Analysis.Complex.Koebe.weak_koebe_of_landau

/-!
# A uniform derivative bound from a value gap

If `Φ` is holomorphic and injective on a ball `ball z ρ` and `a ∈ ball z ρ` satisfies
`Φ a = Φ z + 1`, then `‖deriv Φ z‖ ≤ C / ‖a - z‖` for a universal constant `C > 0`.

The proof uses the weak Koebe one-quarter theorem (`Commons.Analysis.Complex.Koebe.weak_koebe_of_landau`,
built on Landau's theorem): a normalised univalent function on the unit disc omits no value of
modulus `< c₀/π`.  Rescaling `Φ` around `z` by the half gap `s = ‖a - z‖/2` and normalising the
derivative to `1` produces a univalent normalised `F`; the value `v = 1/(s Φ'z)` is omitted because
`a ∉ ball z s`, and Koebe gives `c₀/π ≤ ‖v‖ = 1/(s ‖Φ'z‖)`, whence `‖Φ'z‖ ≤ (2π/c₀)/‖a - z‖`.
-/

namespace Work.Fatou.Analysis

open Metric Set

theorem exists_deriv_le_of_value_gap :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : ℂ → ℂ) (z a : ℂ) (ρ : ℝ), 0 < ρ →
      (∀ w ∈ Metric.ball z ρ, AnalyticAt ℂ Φ w) → Set.InjOn Φ (Metric.ball z ρ) →
      a ∈ Metric.ball z ρ → Φ a = Φ z + 1 →
      ‖deriv Φ z‖ ≤ C / ‖a - z‖ := by
  obtain ⟨c₀, hc₀pos, hlandau⟩ := Commons.Analysis.Complex.Landau.landau_theorem
  have hkoebe := Commons.Analysis.Complex.Koebe.weak_koebe_of_landau hc₀pos hlandau
  refine ⟨2 / (c₀ / Real.pi), by positivity, ?_⟩
  intro Φ z a ρ hρ hana hinj ha hval
  have hc : 0 < c₀ / Real.pi := by positivity
  have hCpos : 0 < 2 / (c₀ / Real.pi) := by positivity
  have har : 0 < ‖a - z‖ := by
    by_contra h
    have h0 : ‖a - z‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    have haz : a = z := sub_eq_zero.mp (norm_eq_zero.mp h0)
    have h01 : (1 : ℂ) = 0 := by
      rw [haz] at hval
      exact add_left_cancel (show Φ z + 1 = Φ z + 0 by rw [add_zero]; exact hval.symm)
    exact one_ne_zero h01
  have haρ : ‖a - z‖ < ρ := by
    have h := ha
    rwa [Metric.mem_ball, dist_eq_norm] at h
  set s : ℝ := ‖a - z‖ / 2 with hs
  have hspos : 0 < s := by rw [hs]; linarith
  have hsρ : s < ρ := by rw [hs]; linarith
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hmem : ∀ η : ℂ, η ∈ Metric.ball (0 : ℂ) 1 → z + (s : ℂ) * η ∈ Metric.ball z ρ := by
    intro η hη
    have hηn : ‖η‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hη
    rw [Metric.mem_ball, dist_eq_norm]
    have hz : z + (s : ℂ) * η - z = (s : ℂ) * η := by ring
    rw [hz, norm_mul, Complex.norm_of_nonneg hspos.le]
    have h1 : s * ‖η‖ < s := by
      have := mul_lt_mul_of_pos_left hηn hspos
      simpa using this
    linarith
  by_cases hderiv : deriv Φ z = 0
  · rw [hderiv, norm_zero]
    exact div_nonneg hCpos.le (norm_nonneg _)
  · have hne : (s : ℂ) * deriv Φ z ≠ 0 := mul_ne_zero hsC hderiv
    set F : ℂ → ℂ := fun η => (Φ (z + (s : ℂ) * η) - Φ z) * (((s : ℂ) * deriv Φ z))⁻¹ with hF
    set v : ℂ := (Φ a - Φ z) * (((s : ℂ) * deriv Φ z))⁻¹ with hvdef
    have hFana : ∀ η ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ F η := by
      intro η hη
      have hΦ : AnalyticAt ℂ Φ (z + (s : ℂ) * η) := hana _ (hmem η hη)
      rw [hF]
      have haff : AnalyticAt ℂ (fun w : ℂ => z + (s : ℂ) * w) η := by fun_prop
      have hcomp : AnalyticAt ℂ (fun w : ℂ => Φ (z + (s : ℂ) * w)) η := by
        have h := AnalyticAt.comp (x := η) (f := fun w : ℂ => z + (s : ℂ) * w) (g := Φ) hΦ haff
        simpa [Function.comp_def] using h
      exact (hcomp.sub analyticAt_const).mul analyticAt_const
    have hFinj : Set.InjOn F (Metric.ball (0 : ℂ) 1) := by
      intro η1 hη1 η2 hη2 heq
      rw [hF] at heq
      have hΦeq : Φ (z + (s : ℂ) * η1) = Φ (z + (s : ℂ) * η2) :=
        sub_left_inj.mp (mul_right_cancel₀ (inv_ne_zero hne) heq)
      have h := hinj (hmem η1 hη1) (hmem η2 hη2) hΦeq
      exact mul_left_cancel₀ hsC (add_left_cancel h)
    have hF0 : F 0 = 0 := by rw [hF]; simp
    have hF1 : deriv F 0 = 1 := by
      rw [hF]
      have hgd : HasDerivAt (fun w : ℂ => z + (s : ℂ) * w) (s : ℂ) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (s : ℂ)).const_add z
      have hΦd : HasDerivAt Φ (deriv Φ z) (z + (s : ℂ) * (0 : ℂ)) := by
        simpa using (hana z (Metric.mem_ball_self hρ)).hasStrictDerivAt.hasDerivAt
      have h1 : HasDerivAt (fun w : ℂ => Φ (z + (s : ℂ) * w)) ((s : ℂ) * deriv Φ z) 0 := by
        have h := HasDerivAt.scomp (0 : ℂ) hΦd hgd
        simpa [Function.comp_def, smul_eq_mul] using h
      have h3 : HasDerivAt
          (fun w : ℂ => (Φ (z + (s : ℂ) * w) - Φ z) * (((s : ℂ) * deriv Φ z))⁻¹)
          (((s : ℂ) * deriv Φ z) * (((s : ℂ) * deriv Φ z))⁻¹) 0 :=
        (h1.sub_const (Φ z)).mul_const _
      rw [h3.deriv, mul_inv_cancel₀ hne]
    have hv : v ∉ F '' (Metric.ball (0 : ℂ) 1) := by
      rintro ⟨η, hη, hηeq⟩
      rw [hF, hvdef] at hηeq
      have hΦeq : Φ (z + (s : ℂ) * η) = Φ a :=
        sub_left_inj.mp (mul_right_cancel₀ (inv_ne_zero hne) hηeq)
      have hza : z + (s : ℂ) * η = a := hinj (hmem η hη) ha hΦeq
      have h1 : (s : ℂ) * η = a - z := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hza
      have h2 : s * ‖η‖ = ‖a - z‖ := by
        rw [← h1, norm_mul, Complex.norm_of_nonneg hspos.le]
      have hηn : ‖η‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hη
      have h3 : s * ‖η‖ < s := by
        have := mul_lt_mul_of_pos_left hηn hspos
        simpa using this
      nlinarith [hs, h2, h3, hspos]
    have hkb := hkoebe F hFana hFinj hF0 hF1 v hv
    have hnum : Φ a - Φ z = 1 := by rw [hval]; ring
    have hnormv : ‖v‖ = 1 / (s * ‖deriv Φ z‖) := by
      rw [hvdef, norm_mul, norm_inv, norm_mul, hnum, norm_one, Complex.norm_of_nonneg hspos.le,
        one_mul, one_div]
    have hsd : s * ‖deriv Φ z‖ ≤ 1 / (c₀ / Real.pi) := by
      rw [hnormv] at hkb
      have hkb' : c₀ / Real.pi * (s * ‖deriv Φ z‖) ≤ 1 :=
        (le_div_iff₀ (mul_pos hspos (norm_pos_iff.mpr hderiv))).mp hkb
      rw [le_div_iff₀ hc]
      nlinarith [hkb']
    have hgoal : ‖deriv Φ z‖ * ‖a - z‖ ≤ 2 / (c₀ / Real.pi) := by
      have h1 : ‖deriv Φ z‖ * ‖a - z‖ = 2 * (s * ‖deriv Φ z‖) := by rw [hs]; ring
      rw [h1]
      calc (2 : ℝ) * (s * ‖deriv Φ z‖) ≤ 2 * (1 / (c₀ / Real.pi)) := by linarith [hsd]
        _ = 2 / (c₀ / Real.pi) := by ring
    rw [le_div_iff₀ har]
    exact hgoal

end Work.Fatou.Analysis
