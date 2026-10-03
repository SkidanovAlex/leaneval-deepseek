import Mathlib
import Submission.Work.Repel.landau_explicit
import Submission.Unif.Commons.Analysis.Complex.Koebe.weak_koebe_of_landau

namespace Work.Pert.V5

open Metric Set

/-- **Value-gap derivative bound with an explicit constant.**  If `Φ` is holomorphic and injective on `ball z ρ` with `ρ ≥ 3/4`, and `a ∈ ball z ρ` satisfies `Φ a = Φ z + 1` and `3/4 ≤ ‖a - z‖`, then `‖deriv Φ z‖ ≤ 400π/3`.

Route (self-contained; if `deriv Φ z = 0` it is trivial).  Put `s = 3/4` and
`G η = (Φ (z + (s:ℂ) * η) - Φ z) * ((s:ℂ) * deriv Φ z)⁻¹`.  Then `G` is `AnalyticAt` on `Metric.ball 0 1` (composition with an affine map), `Set.InjOn G (Metric.ball 0 1)` (from `hinj`, after cancelling the constant factor), `G 0 = 0` and `deriv G 0 = 1` (chain rule; `exists_deriv_le_of_value_gap` in this workspace shows the exact `HasDerivAt` pattern to copy).  The value `v = ((s:ℂ) * deriv Φ z)⁻¹ = 1/(s * deriv Φ z)` is *omitted* by `G` on the unit disc: `G η = v` forces `Φ (z + s η) = Φ a`, hence `z + s η = a` by `hinj` (`z + sη ∈ ball z ρ` because `s * ‖η‖ < 3/4 ≤ ρ`, and `ha`), hence `s * ‖η‖ = ‖a - z‖ ≥ 3/4`, so `‖η‖ ≥ 1`.

The weak Koebe inequality with the *explicit* Landau constant `1/100`:
take `hlandau : ∀ g, (∀ z ∈ ball 0 1, AnalyticAt ℂ g z) → g 0 = 0 → deriv g 0 = 1 → ∃ w, Metric.closedBall w (1/100) ⊆ g '' ball 0 1 := fun g hg _ hg1 => Work.Repel.LandauExplicit.landau_explicit hg hg1` (see `Submission/Work/Repel/lower_growth_univalent.lean` for this exact incantation) and apply `Commons.Analysis.Complex.Koebe.weak_koebe_of_landau (c₀ := (1/100 : ℝ)) (by norm_num) hlandau` (module `Submission.Unif.Commons.Analysis.Complex.Koebe.weak_koebe_of_landau`) to `G`, getting `(1/100)/Real.pi ≤ ‖v‖ = 1/(s * ‖deriv Φ z‖)`, i.e. `s * ‖deriv Φ z‖ ≤ 100 * Real.pi`, i.e. `‖deriv Φ z‖ ≤ 100 * Real.pi / (3/4) = 400 * Real.pi / 3`. -/
theorem deriv_le_of_value_gap_explicit {Φ : ℂ → ℂ} {z a : ℂ} {ρ : ℝ}
    (hρ : (3 : ℝ) / 4 ≤ ρ)
    (hana : ∀ w ∈ Metric.ball z ρ, AnalyticAt ℂ Φ w)
    (hinj : Set.InjOn Φ (Metric.ball z ρ))
    (ha : a ∈ Metric.ball z ρ) (hval : Φ a = Φ z + 1)
    (hgap : (3 : ℝ) / 4 ≤ ‖a - z‖) :
    ‖deriv Φ z‖ ≤ 400 * Real.pi / 3 := by
  have hρpos : 0 < ρ := by linarith
  by_cases hderiv : deriv Φ z = 0
  · rw [hderiv, norm_zero]
    positivity
  · -- the normalising scale and the affine reparametrisation
    set s : ℝ := 3 / 4 with hs
    have hspos : 0 < s := by rw [hs]; norm_num
    have hsρ : s ≤ ρ := by rw [hs]; exact hρ
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
    have hcne : (s : ℂ) * deriv Φ z ≠ 0 := mul_ne_zero hsC hderiv
    -- the rescaled disc sits inside `ball z ρ`
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
    -- Landau's theorem with the explicit constant `1/100`, in the shape needed by Koebe
    have hlandau : ∀ g : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ g z) → g 0 = 0 →
        deriv g 0 = 1 →
        ∃ w : ℂ, Metric.closedBall w ((1 : ℝ) / 100) ⊆ g '' Metric.ball (0 : ℂ) 1 :=
      fun g hg _ hg1 => _root_.Work.Repel.LandauExplicit.landau_explicit hg hg1
    have hwk := _root_.Commons.Analysis.Complex.Koebe.weak_koebe_of_landau
      (c₀ := ((1 : ℝ) / 100)) (by norm_num) hlandau
    -- the normalised univalent map on the unit disc
    set G : ℂ → ℂ := fun η => (Φ (z + (s : ℂ) * η) - Φ z) * (((s : ℂ) * deriv Φ z))⁻¹ with hG
    set v : ℂ := (((s : ℂ) * deriv Φ z))⁻¹ with hvdef
    have hGana : ∀ η ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ G η := by
      intro η hη
      have hΦ : AnalyticAt ℂ Φ (z + (s : ℂ) * η) := hana _ (hmem η hη)
      rw [hG]
      have haff : AnalyticAt ℂ (fun w : ℂ => z + (s : ℂ) * w) η := by fun_prop
      have hcomp : AnalyticAt ℂ (fun w : ℂ => Φ (z + (s : ℂ) * w)) η := by
        have h := AnalyticAt.comp (x := η) (f := fun w : ℂ => z + (s : ℂ) * w)
          (g := Φ) hΦ haff
        simpa [Function.comp_def] using h
      exact (hcomp.sub analyticAt_const).mul analyticAt_const
    have hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1) := by
      intro η1 hη1 η2 hη2 heq
      rw [hG] at heq
      have hΦeq : Φ (z + (s : ℂ) * η1) = Φ (z + (s : ℂ) * η2) :=
        sub_left_inj.mp (mul_right_cancel₀ (inv_ne_zero hcne) heq)
      have h := hinj (hmem η1 hη1) (hmem η2 hη2) hΦeq
      exact mul_left_cancel₀ hsC (add_left_cancel h)
    have hG0 : G 0 = 0 := by rw [hG]; simp
    have hG1 : deriv G 0 = 1 := by
      rw [hG]
      have hgd : HasDerivAt (fun w : ℂ => z + (s : ℂ) * w) (s : ℂ) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (s : ℂ)).const_add z
      have hΦd : HasDerivAt Φ (deriv Φ z) (z + (s : ℂ) * (0 : ℂ)) := by
        simpa using (hana z (Metric.mem_ball_self hρpos)).hasStrictDerivAt.hasDerivAt
      have h1 : HasDerivAt (fun w : ℂ => Φ (z + (s : ℂ) * w)) ((s : ℂ) * deriv Φ z) 0 := by
        have h := HasDerivAt.scomp (0 : ℂ) hΦd hgd
        simpa [Function.comp_def, smul_eq_mul] using h
      have h3 : HasDerivAt
          (fun w : ℂ => (Φ (z + (s : ℂ) * w) - Φ z) * (((s : ℂ) * deriv Φ z))⁻¹)
          (((s : ℂ) * deriv Φ z) * (((s : ℂ) * deriv Φ z))⁻¹) 0 :=
        (h1.sub_const (Φ z)).mul_const _
      rw [h3.deriv, mul_inv_cancel₀ hcne]
    -- the value `v` is omitted
    have hv : v ∉ G '' (Metric.ball (0 : ℂ) 1) := by
      rintro ⟨η, hη, hηeq⟩
      rw [hG, hvdef] at hηeq
      have hΦz : Φ (z + (s : ℂ) * η) - Φ z = 1 := by
        have h2 : (Φ (z + (s : ℂ) * η) - Φ z) * (((s : ℂ) * deriv Φ z))⁻¹
            = (1 : ℂ) * (((s : ℂ) * deriv Φ z))⁻¹ := by
          rw [one_mul]; exact hηeq
        exact mul_right_cancel₀ (inv_ne_zero hcne) h2
      have hΦeq : Φ (z + (s : ℂ) * η) = Φ a := by
        have h1 : Φ (z + (s : ℂ) * η) = Φ z + 1 := by
          calc Φ (z + (s : ℂ) * η) = (Φ (z + (s : ℂ) * η) - Φ z) + Φ z := by ring
            _ = 1 + Φ z := by rw [hΦz]
            _ = Φ z + 1 := by ring
        rw [h1, hval]
      have hza : z + (s : ℂ) * η = a := hinj (hmem η hη) ha hΦeq
      have h2 : s * ‖η‖ = ‖a - z‖ := by
        have h1 : (s : ℂ) * η = a - z := by
          rw [eq_sub_iff_add_eq, add_comm]
          exact hza
        rw [← h1, norm_mul, Complex.norm_of_nonneg hspos.le]
      have hηn : ‖η‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hη
      have h3 : s * ‖η‖ < s := by
        have := mul_lt_mul_of_pos_left hηn hspos
        simpa using this
      have h4 : s ≤ s * ‖η‖ := by rw [h2, hs]; exact hgap
      linarith
    have hkoebe := hwk G hGana hGinj hG0 hG1 v hv
    have hnormv : ‖v‖ = 1 / (s * ‖deriv Φ z‖) := by
      rw [hvdef, norm_inv, norm_mul, Complex.norm_of_nonneg hspos.le, one_div]
    rw [hnormv] at hkoebe
    have hWpos : 0 < s * ‖deriv Φ z‖ := mul_pos hspos (norm_pos_iff.mpr hderiv)
    have hkey : s * ‖deriv Φ z‖ ≤ 100 * Real.pi := by
      have h1 : (1 : ℝ) / 100 ≤ Real.pi / (s * ‖deriv Φ z‖) := by
        rw [div_le_iff₀ Real.pi_pos] at hkoebe
        calc (1 : ℝ) / 100 ≤ (1 / (s * ‖deriv Φ z‖)) * Real.pi := hkoebe
          _ = Real.pi / (s * ‖deriv Φ z‖) := by ring
      have h2 : (1 : ℝ) / 100 * (s * ‖deriv Φ z‖) ≤ Real.pi := (le_div_iff₀ hWpos).mp h1
      have hmul := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 100)
      calc s * ‖deriv Φ z‖ = 100 * ((1 : ℝ) / 100 * (s * ‖deriv Φ z‖)) := by ring
        _ ≤ 100 * Real.pi := hmul
    calc ‖deriv Φ z‖ ≤ 100 * Real.pi / s := by
          rw [le_div_iff₀ hspos]
          have hcomm : ‖deriv Φ z‖ * s = s * ‖deriv Φ z‖ := by ring
          rw [hcomm]; exact hkey
      _ = 400 * Real.pi / 3 := by rw [hs]; ring

end Work.Pert.V5
