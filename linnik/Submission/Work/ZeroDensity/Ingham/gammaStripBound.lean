import Mathlib
import Submission.Work.ZeroDensity.Ingham.norm_Gamma_le_Gamma_re

/-!
# A uniform bound for `Γ` on the strip `-1/2 ≤ Re s ≤ -δ`

The bound proved here is the one used to control the `Γ`-factor of the Ingham
zero-detecting integral on a vertical line sitting to the left of the pole of `Γ` at
`s = 0`:

`‖Γ(a + i·u)‖ ≤ C · (1/δ) / (1 + |u|)`   for `-1/2 ≤ a ≤ -δ`,  `0 < δ ≤ 1/2`.

Note that `a` lies a distance at least `-a ≥ δ` to the left of the pole at `0` (this is the
source of the factor `1/δ`), while the polynomial decay `1/(1+|u|)` along the imaginary
direction controls the far regime.  We take `C = 4√π`, which is far from optimal.

The proof has two regimes:

* **`|u| ≤ 1`.**  The functional equation `Γ(z+1) = z Γ(z)` turns the pole at `0` into the
  factor `1/z`.  On the half-plane `Re > 0` the elementary bound
  `‖Γ w‖ ≤ Γ(Re w)` (`norm_Gamma_le_Gamma_re`) gives `‖Γ(z+1)‖ ≤ Γ(a+1) ≤ Γ(1/2) = √π`
  because `a+1 ∈ [1/2,1]` and `Γ` decreases on `(0,1]`; finally `‖z‖ ≥ |a| ≥ δ`.

* **`|u| ≥ 1`.**  Applying the functional equation twice writes `Γ(z) = Γ(z+2)/((z)(z+1))`
  with `Re(z+2) ∈ [3/2,2]`, so `‖Γ(z+2)‖ ≤ Γ(a+2) ≤ √π` and `‖z‖, ‖z+1‖ ≥ |u|` give
  `‖Γ z‖ ≤ √π/|u|² ≤ 2√π/(1+|u|)`.
-/

namespace Work.ZeroDensity.Ingham

/-- Pointwise bound `‖Γ w‖ ≤ √π` for `Re w ∈ [1/2, 1]`, obtained from
`‖Γ w‖ ≤ Γ (Re w)` (`norm_Gamma_le_Gamma_re`), the monotonicity of `Γ` on `(0,1]` and
`Γ(1/2) = √π`. -/
lemma Gamma_norm_le_sqrt_pi_of_mem_Ioc (w : ℂ) (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ Real.sqrt Real.pi := by
  have hpos : 0 < w.re := by linarith
  have h := norm_Gamma_le_Gamma_re w hpos
  have hmem1 : w.re ∈ Set.Ioc (0 : ℝ) 1 := ⟨hpos, h2⟩
  have hmem2 : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hle : Real.Gamma w.re ≤ Real.Gamma (1 / 2) :=
    Real.Gamma_strictAntiOn_Ioc.antitoneOn hmem2 hmem1 h1
  rw [Real.Gamma_one_half_eq] at hle
  exact h.trans hle

theorem gammaStripBound : ∃ C : ℝ, 0 < C ∧ ∀ (δ a u : ℝ), 0 < δ → δ ≤ 1 / 2 →
    -(1 / 2 : ℝ) ≤ a → a ≤ -δ →
      ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤ C * (1 / δ) / (1 + |u|) := by
  refine ⟨4 * Real.sqrt Real.pi, mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos), ?_⟩
  intro δ a u hδ hδ2 ha1 ha2
  set z : ℂ := (a : ℂ) + (u : ℂ) * Complex.I with hzdef
  have hzre : z.re = a := by rw [hzdef]; simp
  have hzim : z.im = u := by rw [hzdef]; simp
  have hzne : z ≠ 0 := by
    intro h
    have h0 : z.re = 0 := by rw [h]; simp
    rw [hzre] at h0
    linarith
  have hzδ : δ ≤ ‖z‖ := by
    calc δ ≤ -a := by linarith
      _ = |a| := by rw [abs_of_nonpos (by linarith : a ≤ 0)]
      _ = |z.re| := by rw [hzre]
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  by_cases hu : |u| ≤ 1
  · -- Regime `|u| ≤ 1`: the pole of `Γ` at `0` is the only obstruction.
    have hz1re : (z + 1).re = a + 1 := by rw [hzdef]; simp
    have hG1 : ‖Complex.Gamma (z + 1)‖ ≤ Real.sqrt Real.pi :=
      Gamma_norm_le_sqrt_pi_of_mem_Ioc (z + 1)
        (by rw [hz1re]; linarith) (by rw [hz1re]; linarith)
    have hrec : ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + 1)‖ / ‖z‖ := by
      rw [eq_div_iff (norm_ne_zero_iff.mpr hzne)]
      rw [mul_comm, ← norm_mul, ← Complex.Gamma_add_one z hzne]
    have harith : Real.sqrt Real.pi / δ ≤ 4 * Real.sqrt Real.pi * (1 / δ) / (1 + |u|) := by
      have h1u : 0 < 1 + |u| := by positivity
      rw [div_le_div_iff₀ hδ h1u]
      rw [show (4 * Real.sqrt Real.pi * (1 / δ)) * δ = Real.sqrt Real.pi * 4 by
            rw [mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hδ), mul_one, mul_comm]]
      have h2 : (1 + |u|) ≤ 4 := by linarith [abs_nonneg u, hu]
      have h3 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg Real.pi)
      simpa using h3
    calc ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + 1)‖ / ‖z‖ := hrec
      _ ≤ Real.sqrt Real.pi / ‖z‖ := div_le_div_of_nonneg_right hG1 (norm_nonneg z)
      _ ≤ Real.sqrt Real.pi / δ :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hδ hzδ
      _ ≤ 4 * Real.sqrt Real.pi * (1 / δ) / (1 + |u|) := harith
  · -- Regime `|u| ≥ 1`: two shifts of the functional equation give a factor `|u|^{-2}`.
    have hu1 : (1 : ℝ) ≤ |u| := le_of_lt (not_le.mp hu)
    have hzn1 : z + 1 ≠ 0 := by
      intro h
      have h0 : (z + 1).re = 0 := by rw [h]; simp
      have hz1re : (z + 1).re = a + 1 := by rw [hzdef]; simp
      rw [hz1re] at h0
      linarith
    have hz2re : (z + 2).re = a + 2 := by rw [hzdef]; simp
    have hG2 : ‖Complex.Gamma (z + 2)‖ ≤ Real.sqrt Real.pi := by
      have h := norm_Gamma_le_Gamma_re (z + 2) (by rw [hz2re]; linarith)
      rw [hz2re] at h
      refine h.trans ?_
      have hone : a + 1 ≠ 0 := by linarith
      have hadd : Real.Gamma (a + 2) = (a + 1) * Real.Gamma (a + 1) := by
        rw [show a + 2 = (a + 1) + 1 by ring, Real.Gamma_add_one hone]
      rw [hadd]
      have hGle1 : Real.Gamma (a + 1) ≤ Real.sqrt Real.pi := by
        have hmem1 : a + 1 ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have hmem2 : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
        have hh := Real.Gamma_strictAntiOn_Ioc.antitoneOn hmem2 hmem1
          (by linarith : (1 / 2 : ℝ) ≤ a + 1)
        rwa [Real.Gamma_one_half_eq] at hh
      have hGpos : 0 < Real.Gamma (a + 1) := Real.Gamma_pos_of_pos (by linarith)
      have hmul := mul_le_mul (show a + 1 ≤ 1 by linarith) hGle1
        (le_of_lt hGpos) (by norm_num : (0 : ℝ) ≤ 1)
      simpa using hmul
    have hrec1 : ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + 1)‖ / ‖z‖ := by
      rw [eq_div_iff (norm_ne_zero_iff.mpr hzne)]
      rw [mul_comm, ← norm_mul, ← Complex.Gamma_add_one z hzne]
    have hrec2 : ‖Complex.Gamma (z + 1)‖ = ‖Complex.Gamma (z + 2)‖ / ‖z + 1‖ := by
      have h2 : (z + 1) + 1 = z + 2 := by ring
      rw [eq_div_iff (norm_ne_zero_iff.mpr hzn1), mul_comm, ← norm_mul, ← h2,
        ← Complex.Gamma_add_one (z + 1) hzn1]
    have hrec : ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + 2)‖ / (‖z‖ * ‖z + 1‖) := by
      rw [hrec1, hrec2, div_div, mul_comm]
    have hzu : |u| ≤ ‖z‖ := by
      have h := Complex.abs_im_le_norm z
      rwa [hzim] at h
    have hzu1 : |u| ≤ ‖z + 1‖ := by
      have h := Complex.abs_im_le_norm (z + 1)
      have him : (z + 1).im = u := by rw [hzdef]; simp
      rwa [him] at h
    have hprod : |u| ^ 2 ≤ ‖z‖ * ‖z + 1‖ := by
      have h := mul_le_mul hzu hzu1 (abs_nonneg u) (norm_nonneg z)
      simpa [pow_two] using h
    have harith : Real.sqrt Real.pi / |u| ^ 2 ≤ 4 * Real.sqrt Real.pi * (1 / δ) / (1 + |u|) := by
      have hspos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      have hu2 : 0 < |u| ^ 2 := by positivity
      have h1u : 0 < 1 + |u| := by positivity
      rw [div_le_div_iff₀ hu2 h1u]
      have hle : (1 + |u|) ≤ 4 * |u| ^ 2 / δ := by
        rw [le_div_iff₀ hδ]
        nlinarith [hu1, hδ2, abs_nonneg u, sq_nonneg u]
      calc Real.sqrt Real.pi * (1 + |u|)
          ≤ Real.sqrt Real.pi * (4 * |u| ^ 2 / δ) := mul_le_mul_of_nonneg_left hle hspos.le
        _ = (4 * Real.sqrt Real.pi * (1 / δ)) * |u| ^ 2 := by ring_nf
    calc ‖Complex.Gamma z‖ = ‖Complex.Gamma (z + 2)‖ / (‖z‖ * ‖z + 1‖) := hrec
      _ ≤ Real.sqrt Real.pi / (‖z‖ * ‖z + 1‖) :=
          div_le_div_of_nonneg_right hG2 (by positivity)
      _ ≤ Real.sqrt Real.pi / |u| ^ 2 :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) hprod
      _ ≤ 4 * Real.sqrt Real.pi * (1 / δ) / (1 + |u|) := harith

end Work.ZeroDensity.Ingham
