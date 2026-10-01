import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.zeroDetAux
import Submission.Work.LinnikAreas.Density4.det_split
import Submission.Work.LinnikAreas.Density4.Sbig_approx
import Submission.Work.LinnikAreas.Density4.Ssm_fixed_bound
import Submission.Work.LinnikAreas.Density4.isZ_LFunction_zero
import Submission.Work.LinnikContract.Areas
import Submission.Work.ZeroDensity.LogFree.Sbig_approx_D
import Submission.Work.ZeroDensity.LogFree.Ssm_bound_D


namespace Work.ZeroDensity.LogFree

open Work.LinnikAreas.Density4
/-! ## An auxiliary fact — a `zeroMult`-zero vanishes for `L(·,χ)` -/

/-- If `ρ` is a zero of `L(·,χ)` in the sense of `zeroMult` (a zero of the completed
`L`-function of the primitive character inducing `χ`) and `χ ≠ 1`, then `L(ρ,χ) = 0`.
This is `Work.LinnikAreas.Density4.isZ_LFunction_zero` without the height restriction
`|Im ρ| ≤ 1`. -/
lemma LFunction_eq_zero_of_zeroMult_ne {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {ρ : ℂ} (hz : Work.LinnikContract.zeroMult χ ρ ≠ 0) :
    DirichletCharacter.LFunction χ ρ = 0 := by
  have hcond : χ.conductor ≠ 1 := fun hc =>
    hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mpr hc)
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hcomp : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero
      (by simpa only [Work.LinnikContract.zeroMult] using hz)
  have hLprim : DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inr hcond), hcomp,
      zero_div]
  have hprim_ne : χ.primitiveCharacter ≠ 1 := by
    intro hψ
    have h1 := χ.changeLevel_primitiveCharacter
    rw [hψ, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h1
    exact hχ h1.symm
  rw [← χ.changeLevel_primitiveCharacter]
  rw [DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (Or.inl hprim_ne), hLprim, zero_mul]


/-- L1 of JUTILA_UNIFIED_LEAD.md section 3: the hybrid zero detector. Let `p : Work.ZeroDensity.LogFree.Params` be the parameter packet (`p.sigma0 > 1/2`, `p.eta > 0`, `0 < p.w < p.u < p.v < p.x`, and the two conditions `P1 : x*sigma0 >= 1/2 + v + w + 2*eta` and `P2 : u*(2*sigma0-1) >= 1/2 + 2*w + 2*eta`). Write `D = scale q T = q*(T+2)`, `L = Lscale q T = log D`, `U = D^u`, `V = D^v`, `W = D^w`, `X = D^x`. Then there are `c0 > 0`, `C > 0` and `D0 > 0` such that for all `q >= 2`, all `T >= 1` with `D0 <= D`, every non-principal `chi` mod `q` and every zero `rho` of `L(s, chi)` with `sigma0 <= Re rho < 1`, `|Im rho| <= T` and `c0 <= (1 - Re rho)*L` (a *non-exceptional* zero),

  `||Density4.detSum q U V W X L chi rho|| >= 1 - C/L`.

`Density4.detSum q U V W X L chi rho` is the already-defined Heath-Brown (11.8) detector sum `sum_n (sum_{d|n} psi_d)(sum_{d|n} theta_d) chi(n) n^(-rho) (e^(-n/X) - e^(-n*L^2/U))` with `psiM U V`, `thetaM W` the mollifiers (11.6), (11.7) of `Submission.Work.LinnikAreas.Density4`. This generalises the proved `Density4.zero_detector`, which has the fixed exponent `1/3` in place of `p.eta`, the scale `q` in place of `D = q(T+2)`, the working range `|Im rho| <= 1` in place of `|Im rho| <= T`, and an additive `1/C` (rather than `C/L`) error. Route: Heath-Brown (11.8)-(11.10) with the line of integration moved to `Re(s + rho) = 0`, i.e. `Re s = -beta` (the residue at `s = 0` vanishes because `L(rho, chi) = 0`; the pole of `Gamma` at `-1` is at distance `(1-beta)*L >= c0`, giving `Gamma(-beta+it) << e^(-|t|) L/c0`; `|X^s| = X^(-beta) <= X^(-sigma0)`; `|L(it', chi)| <= C D^(1/2+eta)(1+|t|)^(1/2+eta)` by the convexity bound on `Re s = 0` for the non-principal character, which is the already proved `Commons...LFunctionCritLineBound` `||L(iy, chi)|| <= C (q(1+|y|))^(1/2+eps)`; `|F(it'')| <= V W`), so the contour is `<< L^O(1) D^(1/2+eta) V W X^(-sigma0) <= D^(-eta)` by `P1`. The main term `e^(-L^2/U)` and the vanishing for `2 <= n <= U` are the proved `Density4.Sbig_approx`; the tail `n > U` is `<< e^(-L)`. The model is `Density4.Ssm_fixed_bound`, whose hypotheses `v+w+1/3 < x` and `2w+1/3 < u` are here replaced by `P1` and `P2`. -/
theorem hybridDetector (p : Work.ZeroDensity.LogFree.Params) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T →
        D₀ ≤ Work.ZeroDensity.LogFree.scale q T →
        ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ ρ : ℂ,
          Work.LinnikContract.zeroMult χ ρ ≠ 0 → p.σ₀ ≤ ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
          c₀ ≤ (1 - ρ.re) * Work.ZeroDensity.LogFree.Lscale q T →
          1 - C / Work.ZeroDensity.LogFree.Lscale q T ≤
            ‖Work.LinnikAreas.Density4.detSum q (Work.ZeroDensity.LogFree.Dpow q T p.u)
              (Work.ZeroDensity.LogFree.Dpow q T p.v) (Work.ZeroDensity.LogFree.Dpow q T p.w)
              (Work.ZeroDensity.LogFree.Dpow q T p.x) (Work.ZeroDensity.LogFree.Lscale q T)
              χ ρ‖ := by
  have hupos : 0 < p.u := lt_trans p.hw p.hwu
  obtain ⟨C₁, hC₁pos, hSbig⟩ := Sbig_approx_D p.u hupos
  obtain ⟨C₂, hC₂pos, D₀, hD₀pos, hSsm⟩ := Ssm_bound_D p
  have hσ₀pos : (0 : ℝ) < p.σ₀ := by linarith [p.hσ₀]
  refine ⟨1, one_pos, 27 / p.u ^ 3 + C₁ + C₂ + 1, by positivity,
    max D₀ 2, lt_max_of_lt_left hD₀pos, ?_⟩
  intro q hq _inst T hT hD χ hχ ρ hz hσ hρ1 him hc₀
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
  have hge : 1 ≤ (1 - ρ.re) * L := hc₀
  have hb1 := hSbig q T hq hT V W χ ρ hW1 hWU hUV hre
  have hb2 := hSsm q T hq hT hD₀le χ hχ ρ hL0 hσ hρ1 him hge
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
