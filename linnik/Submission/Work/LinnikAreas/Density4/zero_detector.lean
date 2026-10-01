import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.zeroDetAux
import Submission.Work.LinnikAreas.Density4.det_split
import Submission.Work.LinnikAreas.Density4.Ssm_fixed_bound
import Submission.Work.LinnikAreas.Density4.Sbig_approx
import Submission.Work.LinnikContract.Areas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

open Work.LinnikContract

/-- **HB (1992) §11, (11.8)–(11.10): the zero detector.**
For each fixed tuple of exponents `0 < w < u < v < x` with `v + w + 1/3 < x` and
`2w + 1/3 < u` there is `C > 0` such that for every `q ≥ 2`, character `χ` mod `q` and zero `ρ`
of `χ` in the working region with `λ(ρ) ≤ λ₀(q)`, the detector sum
`detSum = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}(e^{-n/X} - e^{-n𝓛²/U})` (with `U = q^u`, `V = q^v`, `W = q^w`,
`X = q^x`, `𝓛 = log q`) has modulus `≥ 1 - C/𝓛`.

This is assembled from the two halves of HB §11:
* `Sbig_approx` (HB (11.10) plus the tail): `‖Sbig - e^{-𝓛²/U}‖ ≤ C₁/𝓛`, where
  `Sbig = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}e^{-n𝓛²/U}`;
* `Ssm_fixed_bound` (HB (11.9)): `‖Ssm‖ ≤ C₂/𝓛`, where `Ssm = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}e^{-n/X}`;
* `det_split` (the termwise split of the detector): `detSum = Ssm - Sbig`.

The triangle inequality then gives
`‖detSum‖ ≥ ‖Sbig‖ - ‖Ssm‖ ≥ e^{-𝓛²/U} - (C₁+C₂)/𝓛 ≥ 1 - 𝓛²/U - (C₁+C₂)/𝓛`, and the elementary
estimate `𝓛³/q^u ≤ 27/u³` (from `log x ≤ x^{u/3}/(u/3)`) turns `𝓛²/U` into `(27/u³)/𝓛`. -/
theorem zero_detector (h1 : Work.LinnikContract.Area1) :
    ∀ (u v w x : ℝ), 0 < w → w < u → u < v → v < x → v + w + 1/3 < x → 2*w + 1/3 < u →
      ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
        2 ≤ q → Work.LinnikContract.IsZ χ ρ →
        Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q →
        1 - C/(Real.log q) ≤ ‖Work.LinnikAreas.Density4.detSum q ((q:ℝ)^u) ((q:ℝ)^v)
            ((q:ℝ)^w) ((q:ℝ)^x) (Real.log q) χ ρ‖ := by
  intro u v w x hw hwu huv hvx hvwx h2wu
  obtain ⟨C₁, _hC₁pos, hC₁⟩ := Sbig_approx u v w x hw hwu huv hvx hvwx h2wu
  obtain ⟨C₂, _hC₂pos, hC₂⟩ := Ssm_fixed_bound h1 u v w x hw hwu huv hvx hvwx h2wu
  have hu : 0 < u := lt_trans hw hwu
  refine ⟨C₁ + C₂ + 27/u^3 + 1, by positivity, ?_⟩
  intro q _inst χ ρ hq hIsZ hlam
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hL : 0 < Real.log q := Real.log_pos hq1
  have hU : 0 < (q:ℝ)^u := Real.rpow_pos_of_pos hqpos u
  have hX : 0 < (q:ℝ)^x := Real.rpow_pos_of_pos hqpos x
  have hsplit := det_split (q := q) ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x)
    (Real.log q) χ ρ hU hL hX
  have hb1 := hC₁ q χ ρ hq hIsZ hlam
  have hb2 := hC₂ q χ ρ hq hIsZ hlam
  set α : ℂ := ((Real.exp (-((Real.log q)^2 / ((q:ℝ)^u))) : ℝ) : ℂ) with hαdef
  have hαnorm : ‖α‖ = Real.exp (-((Real.log q)^2 / ((q:ℝ)^u))) := by
    rw [hαdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hSbig_lb : Real.exp (-((Real.log q)^2 / ((q:ℝ)^u))) - C₁ / Real.log q
      ≤ ‖Sbig q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) (Real.log q) χ ρ‖ := by
    have h := abs_norm_sub_norm_le α (Sbig q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) (Real.log q) χ ρ)
    have h2 : ‖α‖ - ‖Sbig q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) (Real.log q) χ ρ‖
        ≤ ‖α - Sbig q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) (Real.log q) χ ρ‖ :=
      le_trans (le_abs_self _) h
    rw [hαnorm] at h2
    rw [norm_sub_rev] at h2
    linarith [hb1, h2]
  have hdet : Real.exp (-((Real.log q)^2 / ((q:ℝ)^u))) - C₁ / Real.log q - C₂ / Real.log q
      ≤ ‖detSum q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) (Real.log q) χ ρ‖ := by
    rw [hsplit]
    have h := abs_norm_sub_norm_le (Sbig q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) (Real.log q) χ ρ)
      (Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ)
    have h2 : ‖Sbig q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) (Real.log q) χ ρ‖
        - ‖Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ‖
        ≤ ‖Sbig q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) (Real.log q) χ ρ
            - Ssm q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x) χ ρ‖ :=
      le_trans (le_abs_self _) h
    rw [norm_sub_rev] at h2
    linarith [hSbig_lb, hb2, h2]
  have hexp : 1 - (Real.log q)^2 / ((q:ℝ)^u) ≤ Real.exp (-((Real.log q)^2 / ((q:ℝ)^u))) :=
    Real.one_sub_le_exp_neg _
  have hlog3 : (Real.log q)^3 / ((q:ℝ)^u) ≤ 27/u^3 := by
    have h1 : Real.log (q:ℝ) ≤ (q:ℝ)^(u/3) / (u/3) :=
      Real.log_le_rpow_div (le_of_lt hqpos) (by positivity)
    have h2 : (q:ℝ)^(u/3) / (u/3) = 3 * (q:ℝ)^(u/3) / u := by
      rw [div_eq_div_iff (by positivity : (u/3) ≠ 0) (by positivity : u ≠ 0)]
      ring
    rw [h2] at h1
    have h3 : (Real.log q)^3 ≤ (3 * (q:ℝ)^(u/3) / u)^3 :=
      pow_le_pow_left₀ (Real.log_nonneg (le_of_lt hq1)) h1 3
    have hq3 : ((q:ℝ)^(u/3))^3 = (q:ℝ)^u := by
      rw [← Real.rpow_natCast ((q:ℝ)^(u/3)) 3, ← Real.rpow_mul (le_of_lt hqpos)]
      congr 1
      push_cast
      ring
    have h4 : (3 * (q:ℝ)^(u/3) / u)^3 = 27 * (q:ℝ)^u / u^3 := by
      rw [div_pow, mul_pow, hq3]
      norm_num
    rw [h4] at h3
    rw [div_le_iff₀ hU]
    calc (Real.log q)^3 ≤ 27 * (q:ℝ)^u / u^3 := h3
      _ = 27 / u^3 * (q:ℝ)^u := by ring
  have hL2U : (Real.log q)^2 / ((q:ℝ)^u) ≤ (27/u^3)/Real.log q := by
    have heq : (Real.log q)^2 / ((q:ℝ)^u) = ((Real.log q)^3 / ((q:ℝ)^u)) / Real.log q := by
      rw [div_div, div_eq_div_iff (ne_of_gt hU) (by positivity)]
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hlog3 (le_of_lt hL)
  have hpart : (C₁ + C₂ + 27/u^3)/Real.log q
      = C₁/Real.log q + C₂/Real.log q + (27/u^3)/Real.log q := by
    rw [add_div, add_div]
  have hgoalsuff : 1 - (C₁ + C₂ + 27/u^3 + 1)/Real.log q
      ≤ 1 - (C₁ + C₂ + 27/u^3)/Real.log q := by
    have h := div_le_div_of_nonneg_right
      (show C₁ + C₂ + 27/u^3 ≤ C₁ + C₂ + 27/u^3 + 1 by linarith) (le_of_lt hL)
    linarith
  have hmid : 1 - (C₁ + C₂ + 27/u^3)/Real.log q
      ≤ Real.exp (-((Real.log q)^2 / ((q:ℝ)^u))) - C₁ / Real.log q - C₂ / Real.log q := by
    rw [hpart]
    linarith [hexp, hL2U]
  linarith [hgoalsuff, hmid, hdet]

end Work.LinnikAreas.Density4
