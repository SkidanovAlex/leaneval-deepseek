import Mathlib
import Submission.Work.ZeroDensity.LogFree.GramProps
import Submission.Work.ZeroDensity.LogFree.hybridDetector
import Submission.Work.ZeroDensity.LogFree.Sbig_approx_D
import Submission.Work.ZeroDensity.LogFree.Ssm_bound_D_gen

namespace Work.ZeroDensity.LogFree

open Work.LinnikAreas.Density4

/-- `Work.ZeroDensity.LogFree.DetectorBound p` (defined in `Submission/Work/ZeroDensity/LogFree/GramProps.lean`): for **every** threshold `c₀ > 0` there are `C > 0`, `D₀ > 0` with `1 - C/Lscale q T ≤ ‖Density4.detSum q U V W X L chi rho‖` for every non-principal character and every zero with `λ(ρ) = (1-Re ρ)·Lscale q T ≥ c₀`. This is the parametrised form of the proved `Work.ZeroDensity.LogFree.hybridDetector` (`Submission/Work/ZeroDensity/LogFree/hybridDetector.lean`), whose proof fixes the threshold at `1`. Route: generalise the two inputs of that proof, replacing the hypothesis `1 ≤ (1-ρ.re)*Lscale q T` by `c₀ ≤ (1-ρ.re)*Lscale q T` and propagating the resulting factor `1/c₀^K`: the strip bound `boundD_gamma_line`/`boundD_lfunc_strip_two` in `Submission/Work/ZeroDensity/LogFree/Ssm_bound_D.lean` loses only the factor `L/c₀` (the distance of the `Γ`-pole), `boundD_gamma_edge` and `boundD_arith` carry no threshold hypothesis, and then `Ssm_bound_D` and the assembly of `hybridDetector` (residue vanishing at `s = 0`, `Sbig_approx_D`, the model term `e^{-L²/U}`, `L³/U ≤ 27/u³`) go through with the constant `27/p.u³ + C₁ + C₂/c₀ + 1`. -/
theorem detectorGen (p : Work.ZeroDensity.LogFree.Params) :
    Work.ZeroDensity.LogFree.DetectorBound p := by
  intro c₀ hc₀pos
  have hupos : 0 < p.u := lt_trans p.hw p.hwu
  obtain ⟨C₁, hC₁pos, hSbig⟩ := Sbig_approx_D p.u hupos
  obtain ⟨C₂, hC₂pos, D₀, hD₀pos, hSsm⟩ := Ssm_bound_D_gen p c₀ hc₀pos
  have hσ₀pos : (0 : ℝ) < p.σ₀ := by linarith [p.hσ₀]
  refine ⟨27 / p.u ^ 3 + C₁ + C₂ + 1, by positivity,
    max D₀ 2, lt_max_of_lt_left hD₀pos, ?_⟩
  intro q hq _inst T hT hD χ hχ ρ hz hσ hρ1 him hc₀le
  set D : ℝ := scale q T with hDdef
  set L : ℝ := Lscale q T with hLdef
  set U : ℝ := Dpow q T p.u with hUdef
  set V : ℝ := Dpow q T p.v with hVdef
  set W : ℝ := Dpow q T p.w with hWdef
  set X : ℝ := Dpow q T p.x with hXdef
  have hmax2 : (2 : ℝ) ≤ max D₀ 2 := le_max_right D₀ 2
  have hmaxD : D₀ ≤ max D₀ 2 := le_max_left D₀ 2
  have hD2 : (2 : ℝ) ≤ D := le_trans hmax2 hD
  have hD₀le : D₀ ≤ D := le_trans hmaxD hD
  have hD1 : (1 : ℝ) ≤ D := by linarith
  have hDgt1 : 1 < D := by linarith
  have hDpos : 0 < D := by linarith
  have hLeq : L = Real.log D := by rw [hLdef, Lscale, ← hDdef]
  have hLpos : 0 < L := by rw [hLeq]; exact Real.log_pos hDgt1
  have hUeq : U = D ^ p.u := by rw [hUdef, Dpow, ← hDdef]
  have hVeq : V = D ^ p.v := by rw [hVdef, Dpow, ← hDdef]
  have hWeq : W = D ^ p.w := by rw [hWdef, Dpow, ← hDdef]
  have hUpos : 0 < U := by rw [hUeq]; exact Real.rpow_pos_of_pos hDpos _
  have hVpos : 0 < V := by rw [hVeq]; exact Real.rpow_pos_of_pos hDpos _
  have hWpos : 0 < W := by rw [hWeq]; exact Real.rpow_pos_of_pos hDpos _
  have hXpos : 0 < X := by rw [hXdef]; exact Real.rpow_pos_of_pos hDpos _
  have hW1 : 1 < W := by rw [hWeq]; exact Real.one_lt_rpow hDgt1 p.hw
  have hWU : W ≤ U := by
    rw [hWeq, hUeq]; exact Real.rpow_le_rpow_of_exponent_le hD1 p.hwu.le
  have hUV : U ≤ V := by
    rw [hUeq, hVeq]; exact Real.rpow_le_rpow_of_exponent_le hD1 p.huv.le
  have hre : |ρ.re| ≤ 1 := by
    have h0 : 0 < ρ.re := lt_of_lt_of_le hσ₀pos hσ
    rw [abs_of_pos h0]; exact hρ1.le
  have hL0 : DirichletCharacter.LFunction χ ρ = 0 :=
    LFunction_eq_zero_of_zeroMult_ne hχ hz
  have hb1 := hSbig q T hq hT V W χ ρ hW1 hWU hUV hre
  have hb2 := hSsm q T hq hT hD₀le χ hχ ρ hL0 hσ hρ1 him hc₀le
  set α : ℂ := ((Real.exp (-(L ^ 2 / U)) : ℝ) : ℂ) with hαdef
  have hb1' : ‖Sbig q U V W L χ ρ - α‖ ≤ C₁ / L := by
    have h := hb1
    rw [← hLdef, ← hUdef] at h
    rw [hαdef]
    exact h
  have hb2' : ‖Ssm q U V W X χ ρ‖ ≤ C₂ / L := by
    have h := hb2
    rw [← hLdef, ← hUdef, ← hVdef, ← hWdef, ← hXdef] at h
    exact h
  have hlog3 : L ^ 3 / U ≤ 27 / p.u ^ 3 := by
    rw [hLeq, hUeq]
    have h1 : Real.log D ≤ D ^ (p.u / 3) / (p.u / 3) :=
      Real.log_le_rpow_div (le_of_lt hDpos) (by positivity)
    have h2 : D ^ (p.u / 3) / (p.u / 3) = 3 * D ^ (p.u / 3) / p.u := by
      rw [div_eq_div_iff (by positivity : p.u / 3 ≠ 0) (by positivity : p.u ≠ 0)]
      ring
    rw [h2] at h1
    have h3 : (Real.log D) ^ 3 ≤ (3 * D ^ (p.u / 3) / p.u) ^ 3 :=
      pow_le_pow_left₀ (Real.log_nonneg hD1) h1 3
    have hD3 : (D ^ (p.u / 3)) ^ 3 = D ^ p.u := by
      rw [← Real.rpow_natCast (D ^ (p.u / 3)) 3, ← Real.rpow_mul (le_of_lt hDpos)]
      congr 1
      push_cast
      ring
    have h4 : (3 * D ^ (p.u / 3) / p.u) ^ 3 = 27 * D ^ p.u / p.u ^ 3 := by
      rw [div_pow, mul_pow, hD3]
      norm_num
    rw [h4] at h3
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hDpos _)]
    calc (Real.log D) ^ 3 ≤ 27 * D ^ p.u / p.u ^ 3 := h3
      _ = 27 / p.u ^ 3 * D ^ p.u := by ring
  have hL2U : L ^ 2 / U ≤ (27 / p.u ^ 3) / L := by
    have heq : L ^ 2 / U = (L ^ 3 / U) / L := by
      rw [div_div, div_eq_div_iff (ne_of_gt hUpos) (by positivity)]
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hlog3 (le_of_lt hLpos)
  have hexp : 1 - (27 / p.u ^ 3) / L ≤ Real.exp (-(L ^ 2 / U)) := by
    have h1 : (1 : ℝ) - L ^ 2 / U ≤ Real.exp (-(L ^ 2 / U)) := Real.one_sub_le_exp_neg _
    linarith
  have hαnorm : ‖α‖ = Real.exp (-(L ^ 2 / U)) := by
    rw [hαdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hSbig_lb : Real.exp (-(L ^ 2 / U)) - C₁ / L ≤ ‖Sbig q U V W L χ ρ‖ := by
    have h := abs_norm_sub_norm_le α (Sbig q U V W L χ ρ)
    have h2 : ‖α‖ - ‖Sbig q U V W L χ ρ‖ ≤ ‖α - Sbig q U V W L χ ρ‖ :=
      le_trans (le_abs_self _) h
    rw [hαnorm] at h2
    rw [norm_sub_rev] at h2
    linarith [hb1', h2]
  have hsplit : detSum q U V W X L χ ρ = Ssm q U V W X χ ρ - Sbig q U V W L χ ρ :=
    det_split (q := q) U V W X L χ ρ hUpos hLpos hXpos
  have hdet : Real.exp (-(L ^ 2 / U)) - C₁ / L - C₂ / L ≤ ‖detSum q U V W X L χ ρ‖ := by
    rw [hsplit]
    have h := abs_norm_sub_norm_le (Sbig q U V W L χ ρ) (Ssm q U V W X χ ρ)
    have h2 : ‖Sbig q U V W L χ ρ‖ - ‖Ssm q U V W X χ ρ‖
        ≤ ‖Sbig q U V W L χ ρ - Ssm q U V W X χ ρ‖ := le_trans (le_abs_self _) h
    rw [norm_sub_rev] at h2
    linarith [hSbig_lb, hb2', h2]
  have hpart : (27 / p.u ^ 3 + C₁ + C₂ + 1) / L
      = (27 / p.u ^ 3) / L + C₁ / L + C₂ / L + 1 / L := by
    rw [add_div, add_div, add_div]
  have hmono : 1 - (27 / p.u ^ 3 + C₁ + C₂ + 1) / L
      ≤ 1 - ((27 / p.u ^ 3) / L + C₁ / L + C₂ / L) := by
    rw [hpart]
    have : 0 < 1 / L := by positivity
    linarith
  linarith [hmono, hexp, hdet]

end Work.ZeroDensity.LogFree
