import Mathlib
import Submission.Work.ZeroDensity.LogFree.Ssm_bound_D

noncomputable section

namespace Work.ZeroDensity.LogFree

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators

open Work.LinnikAreas.Density4

set_option maxHeartbeats 2000000

/-! ## Threshold-parametrised Gamma bound

`boundD_gamma_line` (from `Ssm_bound_D`) is the case `c₀ = 1`.  For a general
threshold `c₀ > 0` the only change is that the factor `L` coming from
`1 / ‖s‖ ≤ 1 / (1 - β) ≤ L` becomes `L / c₀`, so the constant `Cg` is divided
by `c₀`. -/
theorem boundD_gamma_line_gen (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β L : ℝ), 0 < β → β < 1 → c₀ ≤ (1 - β) * L →
      ∀ t : ℝ, ‖Complex.Gamma (((1 - β : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * L * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |t|)) := by
  obtain ⟨Cg, hCgpos, hCg⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  refine ⟨Cg / c₀, div_pos hCgpos hc₀, ?_⟩
  intro β L hβ0 hβ1 hL t
  have hLpos : 0 < L := by nlinarith
  have hβm : 0 < 1 - β := by linarith
  set s : ℂ := ((1 - β : ℝ) : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = 1 - β := by simp [hsdef]
  have hsne : s ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    rw [hsre] at h1
    simp at h1
    linarith
  have hsn : 1 - β ≤ ‖s‖ := by
    calc 1 - β = |s.re| := by rw [hsre, abs_of_pos hβm]
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hinv : 1 / ‖s‖ ≤ L / c₀ := by
    rw [div_le_div_iff₀ (norm_pos_iff.mpr hsne) hc₀]
    nlinarith [hsn, hL]
  have harg : s + 1 = (((2 - β : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
    rw [hsdef]; push_cast; ring
  have hsharp := hCg (2 - β) t (by linarith) (by linarith)
  have hsharp' : ‖Complex.Gamma (s + 1)‖
      ≤ Cg * (1 + |t|) ^ (2 - β - 1 / 2) * Real.exp (-(Real.pi / 2 * |t|)) := by
    rw [harg]
    have hh := hsharp
    rw [show Real.exp (-(Real.pi / 2) * |t|) = Real.exp (-(Real.pi / 2 * |t|)) by ring] at hh
    exact hh
  have hx1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hpow : (1 + |t|) ^ (2 - β - 1 / 2) ≤ (1 + |t|) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hG2 : ‖Complex.Gamma s‖
      ≤ Cg * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |t|)) * (L / c₀) := by
    have hfac : Complex.Gamma s = Complex.Gamma (s + 1) / s := by
      rw [Complex.Gamma_add_one s hsne]
      field_simp
    rw [hfac, norm_div]
    have h2 : ‖Complex.Gamma (s + 1)‖ / ‖s‖ = ‖Complex.Gamma (s + 1)‖ * (1 / ‖s‖) := by
      rw [div_eq_mul_inv, one_div]
    rw [h2]
    calc ‖Complex.Gamma (s + 1)‖ * (1 / ‖s‖)
        ≤ ‖Complex.Gamma (s + 1)‖ * (L / c₀) := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ ≤ (Cg * (1 + |t|) ^ (2 - β - 1 / 2) * Real.exp (-(Real.pi / 2 * |t|))) * (L / c₀) :=
          mul_le_mul_of_nonneg_right hsharp' (by positivity)
      _ ≤ (Cg * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |t|))) * (L / c₀) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCgpos.le)
            (Real.exp_nonneg _)
      _ = Cg * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |t|)) * (L / c₀) := by ring
  calc ‖Complex.Gamma (((1 - β : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = ‖Complex.Gamma s‖ := by
        rw [hsdef]
    _ ≤ Cg * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |t|)) * (L / c₀) := hG2
    _ = (Cg / c₀) * L * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |t|)) := by ring

/-! ## Main theorem (threshold-parametrised) -/

theorem Ssm_bound_D_gen (p : Work.ZeroDensity.LogFree.Params) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
      ∀ (q : ℕ) [NeZero q] (T : ℝ), 2 ≤ q → 1 ≤ T →
        D₀ ≤ Work.ZeroDensity.LogFree.scale q T →
        ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ ρ : ℂ,
          DirichletCharacter.LFunction χ ρ = 0 → p.σ₀ ≤ ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
          c₀ ≤ (1 - ρ.re) * Work.ZeroDensity.LogFree.Lscale q T →
          ‖Work.LinnikAreas.Density4.Ssm q (Work.ZeroDensity.LogFree.Dpow q T p.u)
            (Work.ZeroDensity.LogFree.Dpow q T p.v) (Work.ZeroDensity.LogFree.Dpow q T p.w)
            (Work.ZeroDensity.LogFree.Dpow q T p.x) χ ρ‖
            ≤ C / Work.ZeroDensity.LogFree.Lscale q T := by
  obtain ⟨Cstr, hCstrpos, hCstr⟩ := boundD_lfunc_strip_two p.η p.hη
  obtain ⟨Ccrit, hCcritpos, hCcrit⟩ :=
    Work.LinnikAreas.JutilaPieces.LFunctionCritLineBound p.η p.hη
  obtain ⟨Cgl, hCglpos, hCgl⟩ := boundD_gamma_line_gen c₀ hc₀
  obtain ⟨Cge, hCgepos, hCge⟩ := boundD_gamma_edge
  have hIntMaj : Integrable
      (fun t : ℝ => (1 + |t|) ^ (2 + p.η) * Real.exp (-(Real.pi / 2 * |t|))) :=
    Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp (2 + p.η) (Real.pi / 2)
      (by positivity)
  set Kint : ℝ := ∫ t : ℝ, (1 + |t|) ^ (2 + p.η) * Real.exp (-(Real.pi / 2 * |t|)) with hKintdef
  set C₀ : ℝ := Cgl * (Ccrit / p.σ₀) * (|Kint| + 1) with hC₀def
  have hC₀pos : 0 < C₀ := by
    rw [hC₀def]
    have h1 : 0 < Ccrit / p.σ₀ := div_pos hCcritpos (by linarith [p.hσ₀])
    have h2 : 0 < |Kint| + 1 := by positivity
    exact mul_pos (mul_pos hCglpos h1) h2
  obtain ⟨D₀a, hD₀a1, harith⟩ :=
    boundD_arith (η := p.η) (σ₀ := p.σ₀) (v := p.v) (w := p.w) (x := p.x) (C₀ := C₀)
      p.hη p.hσ₀ p.hσ₀1 p.hw (lt_trans p.hwu p.huv) (by linarith [p.hw, p.hwu, p.huv, p.hvx] : (0:ℝ) < p.x) p.P1 hC₀pos
  refine ⟨C₀, hC₀pos, max D₀a 2, by positivity, ?_⟩
  intro q _inst T hq hT hDq χ hχ ρ hL0 hσρ hρ1 hρim hnexc
  set 𝓓 : ℝ := scale q T with h𝓓def
  set L : ℝ := Lscale q T with hLdef
  have h𝓓eq : 𝓓 = (q : ℝ) * (T + 2) := by rw [h𝓓def, scale]
  have hLeq : L = Real.log 𝓓 := by rw [hLdef, h𝓓def, Lscale]
  have h𝓓2 : (2 : ℝ) ≤ 𝓓 := by
    rw [h𝓓eq]
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith only [hqR, hT]
  have h𝓓pos : (0 : ℝ) < 𝓓 := by linarith
  have h𝓓1 : (1 : ℝ) ≤ 𝓓 := by linarith
  have hLpos : 0 < L := by rw [hLeq]; exact Real.log_pos (by linarith)
  have hxv : 0 < p.x := by linarith [p.hw, p.hwu, p.huv, p.hvx]
  have hσpos : 0 < p.σ₀ := by linarith [p.hσ₀]
  have hvw : (0 : ℝ) < p.v + p.w := by linarith [p.hw, p.huv, p.hwu]
  have hpσ : 0 < ρ.re := lt_of_lt_of_le hσpos hσρ
  set U : ℝ := Dpow q T p.u with hUdef
  set V : ℝ := Dpow q T p.v with hVdef
  set W : ℝ := Dpow q T p.w with hWdef
  set X : ℝ := Dpow q T p.x with hXdef
  have hDp_u : U = 𝓓 ^ p.u := by rw [hUdef, Dpow, ← h𝓓def]
  have hDp_v : V = 𝓓 ^ p.v := by rw [hVdef, Dpow, ← h𝓓def]
  have hDp_w : W = 𝓓 ^ p.w := by rw [hWdef, Dpow, ← h𝓓def]
  have hDp_x : X = 𝓓 ^ p.x := by rw [hXdef, Dpow, ← h𝓓def]
  have hUpos : 0 < U := by rw [hDp_u]; exact Real.rpow_pos_of_pos h𝓓pos _
  have hV1 : 1 ≤ V := by
    rw [hDp_v]
    exact Real.one_le_rpow h𝓓1 (by linarith [p.hw, p.hwu, p.huv] : (0:ℝ) ≤ p.v)
  have hW1 : 1 ≤ W := by rw [hDp_w]; exact Real.one_le_rpow h𝓓1 (le_of_lt p.hw)
  have hXpos : 0 < X := by rw [hDp_x]; exact Real.rpow_pos_of_pos h𝓓pos _
  have hX1 : 1 ≤ X := by rw [hDp_x]; exact Real.one_le_rpow h𝓓1 (le_of_lt hxv)
  have hUV : U ≤ V := by
    rw [hDp_u, hDp_v]
    exact Real.rpow_le_rpow_of_exponent_le h𝓓1 (le_of_lt p.huv)
  have hVWsum : V * W = 𝓓 ^ (p.v + p.w) := by rw [hDp_v, hDp_w, ← Real.rpow_add h𝓓pos]
  have hlogVW : Real.log (V * W) = (p.v + p.w) * L := by
    rw [hVWsum, Real.log_rpow h𝓓pos, hLeq]
  have hargVW : 𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (-(p.x * p.σ₀)) * 𝓓 ^ (p.v + p.w)
      = 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀) := by
    rw [← Real.rpow_add h𝓓pos, ← Real.rpow_add h𝓓pos]
    congr 1
    ring
  have hargVW2 : 𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (p.v + p.w)
      = 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w) := by
    rw [← Real.rpow_add h𝓓pos]
    congr 1
    ring
  -- ============ vertical line ============
  set Aline : ℝ := Cgl * L * (Ccrit / p.σ₀)
      * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (-(p.x * p.σ₀)) * 𝓓 ^ (p.v + p.w))
      * (1 + (p.v + p.w) * L) ^ 3 with hAlinedef
  have hline_pt : ∀ t : ℝ,
      ‖Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Aline * ((1 + |t|) ^ (2 + p.η) * Real.exp (-(Real.pi / 2 * |t|))) := by
    intro t
    set s : ℂ := ((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I with hsdef
    have hsre : s.re = -ρ.re := by simp [hsdef]
    have hsim : s.im = t := by simp [hsdef]
    have hsnorm : ρ.re ≤ ‖s‖ := by
      calc ρ.re = |s.re| := by rw [hsre, abs_neg, abs_of_pos hpσ]
        _ ≤ ‖s‖ := Complex.abs_re_le_norm s
    have hsne : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hsnorm
      linarith
    have hdslope : dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0 s
        = s⁻¹ * DirichletCharacter.LFunction χ (ρ + s) := by
      rw [dslope_of_ne _ hsne, slope]
      simp [hL0, smul_eq_mul]
    have hinvs : ‖s⁻¹‖ ≤ 1 / p.σ₀ := by
      rw [norm_inv, one_div]
      exact inv_anti₀ (by linarith : (0 : ℝ) < p.σ₀) (le_trans hσρ hsnorm)
    have hLn : ‖DirichletCharacter.LFunction χ (ρ + s)‖
        ≤ Ccrit * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |t|) ^ ((1 : ℝ) / 2 + p.η) := by
      have hre : (ρ + s).re = 0 := by rw [Complex.add_re, hsre]; ring
      have him : (ρ + s).im = ρ.im + t := by rw [Complex.add_im, hsim]
      have harg : ρ + s = ((ρ.im + t : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre, him]
      have hb := hCcrit q χ hχ (ρ.im + t)
      rw [← harg] at hb
      refine le_trans hb ?_
      have h1 : |ρ.im + t| ≤ T + |t| := by
        have := abs_add_le ρ.im t; linarith only [this, hρim]
      have hbase : (q : ℝ) * (1 + |ρ.im + t|) ≤ 𝓓 * (1 + |t|) := by
        rw [h𝓓eq]
        have h3 : 1 + |ρ.im + t| ≤ (T + 2) * (1 + |t|) := by
          have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
          nlinarith only [h1, ht0, hT, mul_nonneg (by linarith only [hT] : (0 : ℝ) ≤ T) ht0]
        calc (q : ℝ) * (1 + |ρ.im + t|) ≤ (q : ℝ) * ((T + 2) * (1 + |t|)) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = (q : ℝ) * (T + 2) * (1 + |t|) := by ring
      have h4 : ((q : ℝ) * (1 + |ρ.im + t|)) ^ ((1 : ℝ) / 2 + p.η)
          ≤ (𝓓 * (1 + |t|)) ^ ((1 : ℝ) / 2 + p.η) :=
        Real.rpow_le_rpow (by positivity) hbase (by linarith [p.hη])
      rw [Real.mul_rpow h𝓓pos.le (by positivity : (0 : ℝ) ≤ 1 + |t|)] at h4
      calc Ccrit * ((q : ℝ) * (1 + |ρ.im + t|)) ^ ((1 : ℝ) / 2 + p.η)
          ≤ Ccrit * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |t|) ^ ((1 : ℝ) / 2 + p.η)) :=
            mul_le_mul_of_nonneg_left h4 hCcritpos.le
        _ = Ccrit * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |t|) ^ ((1 : ℝ) / 2 + p.η) := by ring
    have hΓb : ‖Complex.Gamma (s + 1)‖
        ≤ Cgl * L * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |t|)) := by
      have h := hCgl ρ.re L hpσ hρ1 hnexc t
      have harg : s + 1 = (((1 - ρ.re : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
        rw [hsdef]; push_cast; ring
      rw [harg]
      exact h
    have hXb : ‖(X : ℂ) ^ s‖ ≤ 𝓓 ^ (-(p.x * p.σ₀)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hsre, hDp_x, ← Real.rpow_mul h𝓓pos.le]
      exact Real.rpow_le_rpow_of_exponent_le h𝓓1
        (by nlinarith only [mul_le_mul_of_nonneg_left hσρ (le_of_lt hxv)])
    have hFb : ‖lcmF q U V W χ (ρ + s)‖
        ≤ 𝓓 ^ (p.v + p.w) * (1 + (p.v + p.w) * L) ^ 3 := by
      have hre : 1 - ((1 : ℕ) : ℝ)⁻¹ ≤ (ρ + s).re := by
        rw [Complex.add_re, hsre]; norm_num
      have h := norm_lcmF_le_gen q hUpos hUV hV1 hW1 χ (k := 1) le_rfl (s := ρ + s) hre
      have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
      rw [hlogVW, hVWsum, h1, Real.rpow_one] at h
      exact h
    have hΦeq : ‖Phi q U V W X χ ρ s‖
        = ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
            * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖ := by
      rw [Phi, hdslope]
      simp only [norm_mul]
    have hpowt : (1 + |t|) ^ ((3 : ℝ) / 2) * (1 + |t|) ^ ((1 : ℝ) / 2 + p.η)
        = (1 + |t|) ^ (2 + p.η) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |t|)]
      have hexp : (3 : ℝ) / 2 + ((1 : ℝ) / 2 + p.η) = 2 + p.η := by ring
      rw [hexp]
    have hmain0 : ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
          * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖
        ≤ (Cgl * L * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |t|)))
          * ((1 / p.σ₀) * (Ccrit * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |t|) ^ ((1 : ℝ) / 2 + p.η)))
          * 𝓓 ^ (-(p.x * p.σ₀))
          * (𝓓 ^ (p.v + p.w) * (1 + (p.v + p.w) * L) ^ 3) := by
      refine mul_le_mul (mul_le_mul (mul_le_mul hΓb (mul_le_mul hinvs hLn
        (norm_nonneg _) (by positivity)) (by positivity) (by positivity)) hXb
        (norm_nonneg _) (by positivity)) hFb (norm_nonneg _) (by positivity)
    have hmain : ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
          * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖
        ≤ (Cgl * L * (Ccrit / p.σ₀)
            * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (-(p.x * p.σ₀)) * 𝓓 ^ (p.v + p.w))
            * (1 + (p.v + p.w) * L) ^ 3)
          * ((1 + |t|) ^ ((3 : ℝ) / 2) * (1 + |t|) ^ ((1 : ℝ) / 2 + p.η)
              * Real.exp (-(Real.pi / 2 * |t|))) := by
      calc ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
            * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖
          ≤ (Cgl * L * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |t|)))
            * ((1 / p.σ₀) * (Ccrit * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |t|) ^ ((1 : ℝ) / 2 + p.η)))
            * 𝓓 ^ (-(p.x * p.σ₀))
            * (𝓓 ^ (p.v + p.w) * (1 + (p.v + p.w) * L) ^ 3) := hmain0
        _ = (Cgl * L * (Ccrit / p.σ₀)
              * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (-(p.x * p.σ₀)) * 𝓓 ^ (p.v + p.w))
              * (1 + (p.v + p.w) * L) ^ 3)
            * ((1 + |t|) ^ ((3 : ℝ) / 2) * (1 + |t|) ^ ((1 : ℝ) / 2 + p.η)
                * Real.exp (-(Real.pi / 2 * |t|))) := by ring
    calc ‖Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖Phi q U V W X χ ρ s‖ := by rw [hsdef]
      _ = ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
            * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖ := hΦeq
      _ ≤ (Cgl * L * (Ccrit / p.σ₀)
            * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (-(p.x * p.σ₀)) * 𝓓 ^ (p.v + p.w))
            * (1 + (p.v + p.w) * L) ^ 3)
          * ((1 + |t|) ^ ((3 : ℝ) / 2) * (1 + |t|) ^ ((1 : ℝ) / 2 + p.η)
              * Real.exp (-(Real.pi / 2 * |t|))) := hmain
      _ = Aline * ((1 + |t|) ^ (2 + p.η) * Real.exp (-(Real.pi / 2 * |t|))) := by
          rw [hAlinedef, hpowt]
  have hAlineMerged : Aline = Cgl * L * (Ccrit / p.σ₀)
      * 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀) * (1 + (p.v + p.w) * L) ^ 3 := by
    rw [hAlinedef, hargVW]
  have hcont : Continuous (fun t : ℝ =>
      Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    have hline : Continuous (fun t : ℝ => ((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    refine (Work.LinnikAreas.Density4.continuousOn_Phi q U V W X χ ρ hXpos hχ).comp_continuous
      hline (fun t => ?_)
    rw [Set.mem_setOf_eq]
    have hre : ((((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re = -ρ.re := by simp
    rw [hre]
    linarith
  have hIntP : Integrable (fun t : ℝ =>
      Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    refine (hIntMaj.const_mul Aline).mono' hcont.aestronglyMeasurable ?_
    filter_upwards with t
    exact hline_pt t
  have hint_bound : ∫ t : ℝ,
        ‖Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Aline * Kint := by
    calc ∫ t : ℝ, ‖Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ∫ t : ℝ, Aline * ((1 + |t|) ^ (2 + p.η) * Real.exp (-(Real.pi / 2 * |t|))) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _))
            (hIntMaj.const_mul Aline) (Filter.Eventually.of_forall hline_pt)
      _ = Aline * Kint := by rw [integral_const_mul, hKintdef]
  -- ============ horizontal edges ============
  set Cedge0 : ℝ := Cge * Cstr * X * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (p.v + p.w))
      * (1 + (p.v + p.w) * L) ^ 3 with hCedge0def
  set Cedge : ℝ := Cedge0 * (2 : ℝ) ^ (2 + p.η) with hCedgedef
  have hCedge0pos : 0 < Cedge0 := by
    rw [hCedge0def]
    have h1 : (0 : ℝ) < 𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (p.v + p.w) :=
      mul_pos (Real.rpow_pos_of_pos h𝓓pos _) (Real.rpow_pos_of_pos h𝓓pos _)
    have h2 : (0 : ℝ) < 1 + (p.v + p.w) * L := by
      have := mul_pos hvw hLpos; linarith
    have hA : (0 : ℝ) < Cge * Cstr := mul_pos hCgepos hCstrpos
    have hB : (0 : ℝ) < Cge * Cstr * X := mul_pos hA hXpos
    have hC : (0 : ℝ) < Cge * Cstr * X * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (p.v + p.w)) :=
      mul_pos hB h1
    exact mul_pos hC (pow_pos h2 3)
  have hCedgepos : 0 < Cedge := by rw [hCedgedef]; positivity
  have hedge_pt : ∀ x : ℝ, -ρ.re ≤ x → x ≤ 1 → ∀ v : ℝ, 1 ≤ |v| →
      ‖Phi q U V W X χ ρ (((x : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖
        ≤ Cedge * Real.exp (-(Real.pi / 2) * |v|) * |v| ^ (2 + p.η) := by
    intro x hx1 hx2 v hv
    set s : ℂ := ((x : ℝ) : ℂ) + (v : ℂ) * Complex.I with hsdef
    have hsre : s.re = x := by simp [hsdef]
    have hsim : s.im = v := by simp [hsdef]
    have hsn : |v| ≤ ‖s‖ := by
      calc |v| = |s.im| := by rw [hsim]
        _ ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hsne : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hsn
      linarith
    have hdslope : dslope (fun u : ℂ => DirichletCharacter.LFunction χ (ρ + u)) 0 s
        = s⁻¹ * DirichletCharacter.LFunction χ (ρ + s) := by
      rw [dslope_of_ne _ hsne, slope]
      simp [hL0, smul_eq_mul]
    have hLn : ‖DirichletCharacter.LFunction χ (ρ + s)‖
        ≤ Cstr * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |v|) ^ ((1 : ℝ) / 2 + p.η) := by
      have hre : (ρ + s).re = ρ.re + x := by rw [Complex.add_re, hsre]
      have him : (ρ + s).im = ρ.im + v := by rw [Complex.add_im, hsim]
      have harg : ρ + s = ((ρ.re + x : ℝ) : ℂ) + ((ρ.im + v : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre, him]
      have hb := hCstr q χ hq hχ (ρ.re + x) (ρ.im + v) (by linarith) (by linarith)
      rw [← harg] at hb
      refine le_trans hb ?_
      have h1 : |ρ.im + v| ≤ T + |v| := by
        have := abs_add_le ρ.im v; linarith only [this, hρim]
      have hbase : (q : ℝ) * (2 + |ρ.im + v|) ≤ 𝓓 * (1 + |v|) := by
        rw [h𝓓eq]
        have h3 : 2 + |ρ.im + v| ≤ (T + 2) * (1 + |v|) := by
          have hv0 : (0 : ℝ) ≤ |v| := abs_nonneg v
          nlinarith only [h1, hv0, hT, mul_nonneg (by linarith only [hT] : (0 : ℝ) ≤ T) hv0]
        calc (q : ℝ) * (2 + |ρ.im + v|) ≤ (q : ℝ) * ((T + 2) * (1 + |v|)) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = (q : ℝ) * (T + 2) * (1 + |v|) := by ring
      have h4 : ((q : ℝ) * (2 + |ρ.im + v|)) ^ ((1 : ℝ) / 2 + p.η)
          ≤ (𝓓 * (1 + |v|)) ^ ((1 : ℝ) / 2 + p.η) :=
        Real.rpow_le_rpow (by positivity) hbase (by linarith [p.hη])
      rw [Real.mul_rpow h𝓓pos.le (by positivity : (0 : ℝ) ≤ 1 + |v|)] at h4
      calc Cstr * ((q : ℝ) * (2 + |ρ.im + v|)) ^ ((1 : ℝ) / 2 + p.η)
          ≤ Cstr * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |v|) ^ ((1 : ℝ) / 2 + p.η)) :=
            mul_le_mul_of_nonneg_left h4 hCstrpos.le
        _ = Cstr * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |v|) ^ ((1 : ℝ) / 2 + p.η) := by ring
    have hΓb : ‖Complex.Gamma (s + 1)‖
        ≤ Cge * (1 + |v|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |v|)) := by
      have h := hCge ρ.re hpσ hρ1 x hx1 hx2 v hv
      have harg : s + 1 = (((x + 1 : ℝ)) : ℂ) + (v : ℂ) * Complex.I := by
        rw [hsdef]; push_cast; ring
      rw [harg]
      exact h
    have hXb : ‖(X : ℂ) ^ s‖ ≤ X := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos, hsre]
      calc X ^ x ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 hx2
        _ = X := Real.rpow_one X
    have hFb : ‖lcmF q U V W χ (ρ + s)‖
        ≤ 𝓓 ^ (p.v + p.w) * (1 + (p.v + p.w) * L) ^ 3 := by
      have hre : 1 - ((1 : ℕ) : ℝ)⁻¹ ≤ (ρ + s).re := by
        rw [Complex.add_re, hsre]; linarith
      have h := norm_lcmF_le_gen q hUpos hUV hV1 hW1 χ (k := 1) le_rfl (s := ρ + s) hre
      have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
      rw [hlogVW, hVWsum, h1, Real.rpow_one] at h
      exact h
    have hΦeq : ‖Phi q U V W X χ ρ s‖
        = ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
            * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖ := by
      rw [Phi, hdslope]
      simp only [norm_mul]
    have hins : ‖s⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_trans hv hsn)
    have hpowv : (1 + |v|) ^ ((3 : ℝ) / 2) * (1 + |v|) ^ ((1 : ℝ) / 2 + p.η)
        = (1 + |v|) ^ (2 + p.η) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |v|)]
      have hexp : (3 : ℝ) / 2 + ((1 : ℝ) / 2 + p.η) = 2 + p.η := by ring
      rw [hexp]
    have hcut : (1 + |v|) ^ (2 + p.η) ≤ (2 : ℝ) ^ (2 + p.η) * |v| ^ (2 + p.η) := by
      have h3 : (1 + |v|) ≤ 2 * |v| := by linarith [hv]
      calc (1 + |v|) ^ (2 + p.η) ≤ (2 * |v|) ^ (2 + p.η) :=
            Real.rpow_le_rpow (by positivity) h3 (by linarith [p.hη])
        _ = (2 : ℝ) ^ (2 + p.η) * |v| ^ (2 + p.η) :=
            Real.mul_rpow (by norm_num) (by positivity)
    have hmain0 : ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
          * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖
        ≤ (Cge * (1 + |v|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |v|)))
          * (1 * (Cstr * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |v|) ^ ((1 : ℝ) / 2 + p.η)))
          * X
          * (𝓓 ^ (p.v + p.w) * (1 + (p.v + p.w) * L) ^ 3) := by
      refine mul_le_mul (mul_le_mul (mul_le_mul hΓb (mul_le_mul hins hLn
        (norm_nonneg _) (by positivity)) (by positivity) (by positivity)) hXb
        (norm_nonneg _) (by positivity)) hFb (norm_nonneg _) (by positivity)
    have hmain : ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
          * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖
        ≤ (Cge * Cstr * X * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (p.v + p.w))
            * (1 + (p.v + p.w) * L) ^ 3)
          * ((1 + |v|) ^ ((3 : ℝ) / 2) * (1 + |v|) ^ ((1 : ℝ) / 2 + p.η)
              * Real.exp (-(Real.pi / 2 * |v|))) := by
      calc ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
            * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖
          ≤ (Cge * (1 + |v|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2 * |v|)))
            * (1 * (Cstr * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (1 + |v|) ^ ((1 : ℝ) / 2 + p.η)))
            * X
            * (𝓓 ^ (p.v + p.w) * (1 + (p.v + p.w) * L) ^ 3) := hmain0
        _ = (Cge * Cstr * X * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (p.v + p.w))
              * (1 + (p.v + p.w) * L) ^ 3)
            * ((1 + |v|) ^ ((3 : ℝ) / 2) * (1 + |v|) ^ ((1 : ℝ) / 2 + p.η)
                * Real.exp (-(Real.pi / 2 * |v|))) := by ring
    calc ‖Phi q U V W X χ ρ (((x : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖
        = ‖Phi q U V W X χ ρ s‖ := by rw [hsdef]
      _ = ‖Complex.Gamma (s + 1)‖ * (‖s⁻¹‖ * ‖DirichletCharacter.LFunction χ (ρ + s)‖)
            * ‖(X : ℂ) ^ s‖ * ‖lcmF q U V W χ (ρ + s)‖ := hΦeq
      _ ≤ (Cge * Cstr * X * (𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (p.v + p.w))
            * (1 + (p.v + p.w) * L) ^ 3)
          * ((1 + |v|) ^ ((3 : ℝ) / 2) * (1 + |v|) ^ ((1 : ℝ) / 2 + p.η)
              * Real.exp (-(Real.pi / 2 * |v|))) := hmain
      _ = Cedge0 * ((1 + |v|) ^ (2 + p.η) * Real.exp (-(Real.pi / 2) * |v|)) := by
          rw [hCedge0def, hpowv]
          ring
      _ ≤ Cedge0 * (((2 : ℝ) ^ (2 + p.η) * |v| ^ (2 + p.η))
            * Real.exp (-(Real.pi / 2) * |v|)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcut (Real.exp_nonneg _)) hCedge0pos.le
      _ = Cedge * Real.exp (-(Real.pi / 2) * |v|) * |v| ^ (2 + p.η) := by
          rw [hCedgedef]
          ring
  have htop : Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in (-ρ.re)..1,
      Phi q U V W X χ ρ ((x : ℂ) + (R : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
    refine Work.LinnikAreas.Density4.rect_edge_tendsto_zero (Phi q U V W X χ ρ) (-ρ.re) 1
      (2 + p.η) Cedge (by linarith) hCedgepos ?_
    intro x hx R hR
    rw [Set.mem_Icc] at hx
    have hR0 : (0 : ℝ) ≤ R := by linarith
    have h := hedge_pt x hx.1 hx.2 R (by rw [abs_of_nonneg hR0]; exact hR)
    rw [abs_of_nonneg hR0] at h
    exact h
  have hbot : Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in (-ρ.re)..1,
      Phi q U V W X χ ρ ((x : ℂ) - (R : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
    have harg : ∀ (x R : ℝ), starRingEnd ℂ ((x : ℂ) + (R : ℂ) * Complex.I)
        = (x : ℂ) - (R : ℂ) * Complex.I := by
      intro x R; simp [map_add, map_mul]; ring
    have hb : ∀ x ∈ Set.Icc (-ρ.re) 1, ∀ R : ℝ, 1 ≤ R →
        ‖(fun s : ℂ => Phi q U V W X χ ρ (starRingEnd ℂ s)) ((x : ℂ) + (R : ℂ) * Complex.I)‖
          ≤ Cedge * Real.exp (-(Real.pi / 2) * R) * R ^ (2 + p.η) := by
      intro x hx R hR
      rw [Set.mem_Icc] at hx
      have hR0 : (0 : ℝ) ≤ R := by linarith
      have h := hedge_pt x hx.1 hx.2 (-R)
        (by rw [abs_neg, abs_of_nonneg hR0]; exact hR)
      rw [abs_neg, abs_of_nonneg hR0] at h
      have hgoal_eq : (fun s : ℂ => Phi q U V W X χ ρ (starRingEnd ℂ s))
            ((x : ℂ) + (R : ℂ) * Complex.I)
          = Phi q U V W X χ ρ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) := by
        simp only [harg x R]
        congr 1
        push_cast
        ring
      rw [hgoal_eq]
      exact h
    have h2 := Work.LinnikAreas.Density4.rect_edge_tendsto_zero
      (fun s : ℂ => Phi q U V W X χ ρ (starRingEnd ℂ s)) (-ρ.re) 1 (2 + p.η) Cedge
      (by linarith) hCedgepos hb
    have heq : (fun R : ℝ => ∫ x : ℝ in (-ρ.re)..1,
          Phi q U V W X χ ρ (starRingEnd ℂ ((x : ℂ) + (R : ℂ) * Complex.I)))
        = fun R : ℝ => ∫ x : ℝ in (-ρ.re)..1,
            Phi q U V W X χ ρ ((x : ℂ) - (R : ℂ) * Complex.I) := by
      funext R
      apply intervalIntegral.integral_congr
      intro x _
      simp only [harg x R]
    rw [heq] at h2
    exact h2
  -- ============ contour shift and conclusion ============
  have hcontour := Work.ZeroDensity.LogFree.Ssm_eq_shifted_contour q hUpos hUV hV1 hW1 hXpos
    χ hχ ρ hpσ hL0 (by linarith : -1 < -ρ.re) (by linarith : -ρ.re ≤ 1) hIntP htop hbot
  have hconst : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    have hgoal : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by
      rw [Complex.ofReal_div (1 : ℝ) (2 * Real.pi), Complex.ofReal_mul (2 : ℝ) Real.pi]
      norm_num
    have h1 : ‖(((1 / (2 * Real.pi) : ℝ)) : ℂ)‖ = |(1 / (2 * Real.pi) : ℝ)| :=
      RCLike.norm_ofReal (1 / (2 * Real.pi))
    rw [← hgoal, h1, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  have hSsm : ‖Ssm q U V W X χ ρ‖ ≤ (1 / (2 * Real.pi)) * (Aline * Kint) := by
    rw [hcontour, norm_mul, hconst]
    have h1 : ‖∫ t : ℝ, Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ ∫ t : ℝ, ‖Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have h2 : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
    calc (1 / (2 * Real.pi)) * ‖∫ t : ℝ,
            Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ,
            ‖Phi q U V W X χ ρ (((-ρ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_left h1 h2
      _ ≤ (1 / (2 * Real.pi)) * (Aline * Kint) := mul_le_mul_of_nonneg_left hint_bound h2
  have hKcut : (1 / (2 * Real.pi)) * Kint ≤ |Kint| + 1 := by
    have h2 : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
    have h1 : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith only [Real.pi_gt_three]
    calc (1 / (2 * Real.pi)) * Kint ≤ (1 / (2 * Real.pi)) * |Kint| :=
          mul_le_mul_of_nonneg_left (le_abs_self Kint) h2
      _ ≤ 1 * |Kint| := mul_le_mul_of_nonneg_right h1 (abs_nonneg Kint)
      _ = |Kint| := one_mul _
      _ ≤ |Kint| + 1 := by linarith
  have hC₀rel : (1 / (2 * Real.pi)) * (Aline * Kint)
      ≤ C₀ * (L * 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀)
          * (1 + (p.v + p.w) * L) ^ 3) := by
    rw [hAlineMerged]
    have hstep : (1 / (2 * Real.pi)) * ((Cgl * L * (Ccrit / p.σ₀)
          * 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀)
          * (1 + (p.v + p.w) * L) ^ 3) * Kint)
        = ((1 / (2 * Real.pi)) * Kint) * (Cgl * (Ccrit / p.σ₀))
          * (L * 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀)
              * (1 + (p.v + p.w) * L) ^ 3) := by ring
    rw [hstep]
    have hnonneg : (0 : ℝ) ≤ L * 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀)
        * (1 + (p.v + p.w) * L) ^ 3 := by
      have h1 : (0 : ℝ) ≤ 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀) :=
        Real.rpow_nonneg h𝓓pos.le _
      have h2 : (0 : ℝ) < 1 + (p.v + p.w) * L := by
        have := mul_pos hvw hLpos; linarith
      exact mul_nonneg (mul_nonneg hLpos.le h1) (pow_nonneg h2.le 3)
    have hCgl0 : 0 ≤ Cgl * (Ccrit / p.σ₀) :=
      mul_nonneg hCglpos.le (div_nonneg hCcritpos.le (by linarith [p.hσ₀]))
    calc ((1 / (2 * Real.pi)) * Kint) * (Cgl * (Ccrit / p.σ₀))
          * (L * 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀)
              * (1 + (p.v + p.w) * L) ^ 3)
        ≤ (|Kint| + 1) * (Cgl * (Ccrit / p.σ₀))
          * (L * 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀)
              * (1 + (p.v + p.w) * L) ^ 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKcut hCgl0) hnonneg
      _ = C₀ * (L * 𝓓 ^ ((1 : ℝ) / 2 + p.η + p.v + p.w - p.x * p.σ₀)
            * (1 + (p.v + p.w) * L) ^ 3) := by rw [hC₀def]; ring
  have harith' := harith 𝓓 (le_trans (le_max_left _ _) hDq)
  calc ‖Ssm q U V W X χ ρ‖ ≤ (1 / (2 * Real.pi)) * (Aline * Kint) := hSsm
    _ ≤ C₀ * (L * 𝓓 ^ (1 / 2 + p.η + p.v + p.w - p.x * p.σ₀) * (1 + (p.v + p.w) * L) ^ 3) :=
        hC₀rel
    _ = C₀ * Real.log 𝓓 * 𝓓 ^ (1 / 2 + p.η + p.v + p.w - p.x * p.σ₀)
          * (1 + (p.v + p.w) * Real.log 𝓓) ^ 3 := by rw [hLeq]; ring
    _ ≤ C₀ / Real.log 𝓓 := harith'
    _ = C₀ / L := by rw [← hLeq]

end Work.ZeroDensity.LogFree
