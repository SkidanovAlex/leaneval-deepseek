import Mathlib
import Submission.Work.ZeroDensity.LogFree.GramProps
import Submission.Work.ZeroDensity.LogFree.LFunction_strip_bound
import Submission.Work.ZeroDensity.LogFree.CrossShift

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.ZeroDensity.LogFree

set_option linter.unusedSectionVars false

/-- If `χ ≠ χ'` then `χ χ'⁻¹` is not the principal character. -/
lemma mul_inv_ne_one {q : ℕ} {χ χ' : DirichletCharacter ℂ q} (h : χ ≠ χ') : χ * χ'⁻¹ ≠ 1 := by
  intro h1
  apply h
  calc χ = χ * χ'⁻¹ * χ' := by group
    _ = 1 * χ' := by rw [h1]
    _ = χ' := by simp

/-- For `u > 0` there is `D₀ ≥ 1` with `(log x)^2 ≤ x^u` for every `x ≥ D₀`. -/
lemma exists_log_sq_le_rpow {u : ℝ} (hu : 0 < u) :
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ x : ℝ, D₀ ≤ x → (Real.log x) ^ 2 ≤ x ^ u := by
  set δ : ℝ := u / 3 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have h3δ : 3 * δ = u := by rw [hδdef]; ring
  refine ⟨max 1 ((1 / δ ^ 2) ^ (1 / δ)), le_max_left _ _, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hxT : (1 / δ ^ 2) ^ (1 / δ) ≤ x := le_trans (le_max_right _ _) hx
  have hK1 : (1 / δ ^ 2) ≤ x ^ δ := by
    have h1 : ((1 / δ ^ 2) ^ (1 / δ)) ^ δ = (1 / δ ^ 2) ^ ((1 / δ) * δ) :=
      (Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / δ ^ 2) _ _).symm
    have h2 : (1 / δ ^ 2) ^ ((1 / δ) * δ) = 1 / δ ^ 2 := by
      rw [show (1 / δ) * δ = 1 by field_simp, Real.rpow_one]
    calc (1 / δ ^ 2) = ((1 / δ ^ 2) ^ (1 / δ)) ^ δ := by rw [h1, h2]
      _ ≤ x ^ δ := Real.rpow_le_rpow (by positivity) hxT hδpos.le
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδpos
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hsq : (Real.log x) ^ 2 ≤ (x ^ δ / δ) ^ 2 := by
    have hdiv : 0 ≤ x ^ δ / δ := div_nonneg (Real.rpow_nonneg hx0.le _) hδpos.le
    nlinarith [hlog, hlog0, hdiv]
  have hsq' : (x ^ δ / δ) ^ 2 = x ^ (2 * δ) / δ ^ 2 := by
    rw [div_pow, ← Real.rpow_natCast (x ^ δ) 2, ← Real.rpow_mul hx0.le]
    ring_nf
  calc (Real.log x) ^ 2 ≤ (x ^ δ / δ) ^ 2 := hsq
    _ = x ^ (2 * δ) / δ ^ 2 := hsq'
    _ = x ^ (2 * δ) * (1 / δ ^ 2) := by ring
    _ ≤ x ^ (2 * δ) * x ^ δ := mul_le_mul_of_nonneg_left hK1 (Real.rpow_nonneg hx0.le _)
    _ = x ^ (2 * δ + δ) := (Real.rpow_add hx0 _ _).symm
    _ = x ^ u := by rw [show 2 * δ + δ = 3 * δ by ring, h3δ]

/-- `Work.ZeroDensity.LogFree.GramCross p` (defined in `Submission/Work/ZeroDensity/LogFree/GramProps.lean`): for every `c₀ > 0` there are `C, E, D₀` such that for non-principal characters `χ ≠ χ'` and zeros `ρ, ρ'` with `Re ≥ p.σ₀`, `Re < 1`, `|Im| ≤ T` and `λ(ρ) = (1-Re ρ)·Lscale q T ≥ c₀`, `λ(ρ') ≥ c₀`, the cross-character Gram entry `gramEntry q W X U' χ χ' ρ ρ' = Σ'_n (Σθ(n))² (χχ'⁻¹)(n) n^{1-ρ-\barρ'} g(n)` is at most `C·(Lscale q T)^E·Dpow q T (-p.η)`, with `W = Dpow q T p.w`, `X = Dpow q T p.x`, `U' = Dpow q T p.u / L²`. Route: `Σ'_n (Σθ(n))² ψ(n) n^{-s₀} g(n) = (1/2πi)∫ L(ρ+ρ̄'-1+s,ψ)Q_ψ(ρ+ρ̄'-1+s)Γ(s)(X^s-U'^s)ds` with `ψ = χχ'⁻¹ ≠ 1` entire and `Q_ψ` the finite Dirichlet polynomial `Σ_{d,e≤W}θ_dθ_e`-twisted; shift the line to `Re(ρ+ρ̄'-1+s) = 0` (the residue at `s=0` vanishes because `X^s-U'^s` is zero there, and the `Γ`-pole at `-1` is at distance `(λ+λ')/L ≥ 2c₀/L`, giving a factor `L/c₀`); on that line `‖L‖ ≤ C D^{1/2+η}(1+|t|)^{1/2+η}` by the convexity bound `LFunction_strip_bound` (imprimitive characters included), `‖Q_ψ‖ ≤ W²`, and `‖X^s-U'^s‖ ≤ 2U'^{1-2σ₀}`; the `t`-integral converges against `Γ`. Finally `D^{1/2+η}W²U'^{1-2σ₀} = L^{2(2σ₀-1)}D^{1/2+η+2w-u(2σ₀-1)} ≤ D^{-η}` up to the polylog `L^{2(2σ₀-1)}` absorbed into `L^E`, by `p.P2` (`u(2σ₀-1) ≥ 1/2+2w+2η`). -/
theorem gramCross (p : Work.ZeroDensity.LogFree.Params) :
    Work.ZeroDensity.LogFree.GramCross p := by
  intro c₀ hc₀
  obtain ⟨CL, hCLpos, hCL⟩ := cross_Lbd p.η p.hη
  have hδ₁ : 0 < (2 * p.σ₀ - 1) / 2 := by linarith [p.hσ₀]
  have hδ₂ : (2 * p.σ₀ - 1) / 2 < 1 := by linarith [p.hσ₀1]
  obtain ⟨CG, hCGpos, hCG⟩ := gamma_integral_shifted_cross ((1 : ℝ) / 2 + p.η) ((2 * p.σ₀ - 1) / 2)
    (by linarith [p.hη]) hδ₁ hδ₂
  obtain ⟨Dlog, hDlog1, hDlog⟩ := exists_log_sq_le_rpow (by linarith [p.hw, p.hwu] : (0:ℝ) < p.u)
  have hxu : 0 < p.x - p.u := by linarith [p.hw, p.hwu, p.huv, p.hvx]
  obtain ⟨Dlog2, hDlog2_1, hDlog2⟩ := exists_log_sq_le_rpow hxu
  set D₀ : ℝ := max 1 (max (Real.exp 1) (max Dlog Dlog2)) with hD₀def
  have hD₀pos : 0 < D₀ := by rw [hD₀def]; positivity
  refine ⟨(1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀)) + 1, by positivity,
    1 + 2 * (2 * p.σ₀ - 1), D₀, hD₀pos, ?_⟩
  intro q hq _inst T hT hDq χ χ' ρ ρ' hχ1 hχ'1 hχne hz hz' hre1 hlt1 hre2 hlt2 him1 him2 hnc1 hnc2
  clear hz hz'
  -- notation
  set 𝓓 : ℝ := scale q T with h𝓓def
  set L : ℝ := Lscale q T with hLdef
  have hLeq : L = Real.log 𝓓 := by rw [hLdef, h𝓓def, Lscale]
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hT1 : (1 : ℝ) ≤ T := hT
  have h𝓓2 : (2 : ℝ) ≤ 𝓓 := by rw [h𝓓def, scale]; nlinarith
  have h𝓓1 : (1 : ℝ) ≤ 𝓓 := by linarith
  have h𝓓pos : 0 < 𝓓 := lt_of_lt_of_le one_pos h𝓓1
  have hD₀le : D₀ ≤ 𝓓 := by
    rw [hD₀def] at hDq ⊢
    exact hDq
  have hexp1 : Real.exp 1 ≤ 𝓓 := by
    have h1 : Real.exp 1 ≤ max (Real.exp 1) (max Dlog Dlog2) := le_max_left _ _
    have h2 : max (Real.exp 1) (max Dlog Dlog2) ≤ D₀ := by
      rw [hD₀def]; exact le_max_right _ _
    exact le_trans (le_trans h1 h2) hD₀le
  have hDlogle : Dlog ≤ 𝓓 := by
    have h1 : Dlog ≤ max Dlog Dlog2 := le_max_left _ _
    have h2 : max Dlog Dlog2 ≤ max (Real.exp 1) (max Dlog Dlog2) := le_max_right _ _
    have h3 : max (Real.exp 1) (max Dlog Dlog2) ≤ D₀ := by
      rw [hD₀def]; exact le_max_right _ _
    exact le_trans (le_trans h1 (le_trans h2 h3)) hD₀le
  have hL1 : 1 ≤ L := by
    rw [hLeq]
    have h := Real.log_le_log (Real.exp_pos 1) hexp1
    rwa [Real.log_exp] at h
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  -- the three cut-offs
  set W : ℝ := Dpow q T p.w with hWdef
  set X : ℝ := Dpow q T p.x with hXdef
  set U : ℝ := Dpow q T p.u with hUdef
  set U' : ℝ := U / L ^ 2 with hU'def
  have hW𝓓 : W = 𝓓 ^ p.w := by rw [hWdef, Dpow, ← h𝓓def]
  have hX𝓓 : X = 𝓓 ^ p.x := by rw [hXdef, Dpow, ← h𝓓def]
  have hU𝓓 : U = 𝓓 ^ p.u := by rw [hUdef, Dpow, ← h𝓓def]
  have hW1 : 1 < W := by
    rw [hW𝓓]
    exact Real.one_lt_rpow (by linarith) p.hw
  have hXpos : 0 < X := by rw [hX𝓓]; exact Real.rpow_pos_of_pos h𝓓pos _
  have hX1 : 1 ≤ X := by
    rw [hX𝓓]
    exact Real.one_le_rpow h𝓓1 (by linarith [p.hw, p.hwu] : (0 : ℝ) ≤ p.x)
  have hUpos : 0 < U := by rw [hU𝓓]; exact Real.rpow_pos_of_pos h𝓓pos _
  have hU'pos : 0 < U' := by rw [hU'def]; positivity
  have hU'1 : 1 ≤ U' := by
    rw [hU'def, hU𝓓, hLeq, le_div_iff₀ (by positivity : (0:ℝ) < (Real.log 𝓓) ^ 2)]
    simpa using hDlog 𝓓 hDlogle
  have hU'X : U' ≤ X := by
    rw [hU'def, hX𝓓]
    have hUL : U ≤ X := by
      rw [hU𝓓, hX𝓓]
      exact Real.rpow_le_rpow_of_exponent_le h𝓓1 (le_trans p.huv.le p.hvx.le)
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have hUL2 : U / L ^ 2 ≤ U := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < L ^ 2)]
      nlinarith [hUpos.le, hL2]
    exact le_trans hUL2 hUL
  -- the character and the zero-sum
  set ψ : DirichletCharacter ℂ q := χ * χ'⁻¹ with hψdef
  have hψ : ψ ≠ 1 := mul_inv_ne_one hχne
  set σ : ℂ := ρ + (starRingEnd ℂ) ρ' - 1 with hσdef
  have hσre : σ.re = ρ.re + ρ'.re - 1 := by simp [hσdef]
  have hδpos : 0 < (2 * p.σ₀ - 1) / 2 := hδ₁
  have hσ0 : 0 < σ.re := by rw [hσre]; linarith
  have hσ1 : σ.re < 1 := by rw [hσre]; linarith
  have hσδ : (2 * p.σ₀ - 1) / 2 ≤ σ.re := by rw [hσre]; linarith [p.hσ₀]
  have hσim : |σ.im| ≤ 2 * T := by
    have h : σ.im = ρ.im - ρ'.im := by simp [hσdef]; ring
    rw [h]
    calc |ρ.im - ρ'.im| ≤ |ρ.im| + |ρ'.im| := abs_sub _ _
      _ ≤ T + T := by linarith
      _ = 2 * T := by ring
  have hcdef : (-σ.re) = 1 - (ρ.re + ρ'.re) := by rw [hσre]; ring
  have hcm2σ : -σ.re ≤ 1 - 2 * p.σ₀ := by rw [hcdef]; linarith
  -- the pointwise L-bound on the shifted line
  have hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction ψ
      (σ + (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ (CL * 𝓓 ^ ((1 : ℝ) / 2 + p.η)) * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η) := by
    intro t
    have h := hCL q T hq hT ψ hψ σ hσim t
    rw [← h𝓓def] at h
    exact h
  -- integrability, edge decay and the contour shift
  have hInt : Integrable (fun t : ℝ => Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ
      (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    integrable_Ptw_cross_shifted q hW1 hXpos hU'pos
      (mul_pos hCLpos (Real.rpow_pos_of_pos h𝓓pos _))
      (by linarith [p.hη] : (0:ℝ) ≤ 1 / 2 + p.η) hδpos ψ hψ σ hσ0 hσ1 hσδ hLbd
  obtain ⟨htop, hbot⟩ := crossGram_edge_tendsto q hq hW1 hXpos hU'pos ψ hψ σ hσ0 hσ1
  have hshift := crossGram_eq_Ptw_line_shifted q hq hW1 hXpos hU'pos ψ hψ σ hσ0 hσ1 hInt htop hbot
  rw [gramEntry_eq_crossGram q hW1 hXpos hU'pos χ χ' ρ ρ', hshift]
  -- the shifted-line pointwise bound and the integral bound
  have hbd := norm_Ptw_cross_line q hW1 hXpos hU'pos
    (mul_pos hCLpos (Real.rpow_pos_of_pos h𝓓pos _))
    (by linarith [p.hη] : (0:ℝ) ≤ 1 / 2 + p.η) hσ0 hLbd
  have hΓint : Integrable (fun t : ℝ =>
      ‖Complex.Gamma (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η)) :=
    integrable_gamma_shifted ((1 : ℝ) / 2 + p.η) (by linarith [p.hη]) hδpos (-σ.re)
      (by linarith [hσ1]) (by linarith [hσδ])
  have hmaj : Integrable (fun t : ℝ =>
      ((CL * 𝓓 ^ ((1 : ℝ) / 2 + p.η)) * (X ^ (-σ.re) + U' ^ (-σ.re)) * (2 * W) ^ 2)
        * (‖Complex.Gamma (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η))) := hΓint.const_mul _
  have hnormint : ‖∫ t : ℝ, Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ
        (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((CL * 𝓓 ^ ((1 : ℝ) / 2 + p.η)) * (X ^ (-σ.re) + U' ^ (-σ.re)) * (2 * W) ^ 2)
        * ∫ t : ℝ, ‖Complex.Gamma (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
            * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η) := by
    have h := norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall fun t => by
      have hb := hbd t
      exact hb.trans (le_of_eq (by ring)))
    rwa [integral_const_mul] at h
  have hΓle : ∫ t : ℝ, ‖Complex.Gamma (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        * (2 + |t|) ^ ((1 : ℝ) / 2 + p.η) ≤ CG * L / (2 * c₀) := by
    have h := hCG (-σ.re) (by linarith) (by linarith)
    refine h.trans ?_
    have h1c : 1 + (-σ.re) = 2 - ρ.re - ρ'.re := by rw [hcdef]; ring
    have hspos : 0 < 2 - ρ.re - ρ'.re := by rw [← h1c]; linarith
    have h2c₀ : 0 < 2 * c₀ := by linarith
    have hkey : c₀ ≤ (1 - ρ.re) * L := by
      have := hnc1; rw [hLeq] at this; exact this
    have hkey' : c₀ ≤ (1 - ρ'.re) * L := by
      have := hnc2; rw [hLeq] at this; exact this
    have hbound : 2 * c₀ ≤ L * (1 + (-σ.re)) := by
      rw [h1c]
      nlinarith [hkey, hkey', hnc1, hnc2]
    have hdiv : 1 / (1 + (-σ.re)) ≤ L / (2 * c₀) := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + (-σ.re))]
      rw [div_mul_eq_mul_div, le_div_iff₀ h2c₀]
      linarith
    calc CG / (1 + (-σ.re)) = CG * (1 / (1 + (-σ.re))) := by ring
      _ ≤ CG * (L / (2 * c₀)) := mul_le_mul_of_nonneg_left hdiv hCGpos.le
      _ = CG * L / (2 * c₀) := by ring
  -- the `U'`-power
  have hU'eq : U' ^ (1 - 2 * p.σ₀)
      = 𝓓 ^ (-(p.u * (2 * p.σ₀ - 1))) * L ^ (2 * (2 * p.σ₀ - 1)) := by
    have hbase : U' = 𝓓 ^ p.u / L ^ 2 := by rw [hU'def, hU𝓓]
    have hL2 : L ^ 2 = L ^ (2 : ℝ) := (Real.rpow_two L).symm
    calc U' ^ (1 - 2 * p.σ₀)
        = (𝓓 ^ p.u / L ^ 2) ^ (1 - 2 * p.σ₀) := by rw [hbase]
      _ = (𝓓 ^ p.u) ^ (1 - 2 * p.σ₀) / (L ^ 2) ^ (1 - 2 * p.σ₀) :=
            Real.div_rpow (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 𝓓) _) (by positivity)
              (1 - 2 * p.σ₀)
      _ = 𝓓 ^ (p.u * (1 - 2 * p.σ₀)) / (L ^ 2) ^ (1 - 2 * p.σ₀) := by
            rw [← Real.rpow_mul h𝓓pos.le]
      _ = 𝓓 ^ (p.u * (1 - 2 * p.σ₀)) / L ^ (2 * (1 - 2 * p.σ₀)) := by
            rw [hL2, ← Real.rpow_mul hLpos.le]
      _ = 𝓓 ^ (p.u * (1 - 2 * p.σ₀)) * L ^ (-(2 * (1 - 2 * p.σ₀))) := by
            rw [Real.rpow_neg hLpos.le, div_eq_mul_inv]
      _ = 𝓓 ^ (-(p.u * (2 * p.σ₀ - 1))) * L ^ (2 * (2 * p.σ₀ - 1)) := by
            rw [show p.u * (1 - 2 * p.σ₀) = -(p.u * (2 * p.σ₀ - 1)) by ring,
              show -(2 * (1 - 2 * p.σ₀)) = 2 * (2 * p.σ₀ - 1) by ring]
  -- the bound `X^c + U'^c ≤ 2 U'^{1-2σ₀}`
  have hB : X ^ (-σ.re) + U' ^ (-σ.re) ≤ 2 * U' ^ (1 - 2 * p.σ₀) := by
    have hXc : X ^ (-σ.re) ≤ U' ^ (-σ.re) :=
      Real.rpow_le_rpow_of_nonpos hU'pos hU'X (by linarith : -σ.re ≤ 0)
    have hU'c : U' ^ (-σ.re) ≤ U' ^ (1 - 2 * p.σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hU'1 hcm2σ
    linarith
  -- the final arithmetic
  have hmain : (1 / (2 * Real.pi)) * ‖∫ t : ℝ, Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ
        (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀)) + 1)
          * L ^ (1 + 2 * (2 * p.σ₀ - 1)) * 𝓓 ^ (-p.η) := by
    -- the Fourier-theoretic constant is positive
    have h2π : 0 < 1 / (2 * Real.pi) := by positivity
    have h2πle : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Real.pi_gt_three]
    -- step 1: the pointwise/integral bound
    have hstep1 : (1 / (2 * Real.pi)) * ‖∫ t : ℝ, Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ
          (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (1 / (2 * Real.pi)) * (((CL * 𝓓 ^ ((1 : ℝ) / 2 + p.η))
            * (X ^ (-σ.re) + U' ^ (-σ.re)) * (2 * W) ^ 2) * (CG * L / (2 * c₀))) := by
      refine mul_le_mul_of_nonneg_left ?_ h2π.le
      refine hnormint.trans (mul_le_mul_of_nonneg_left hΓle ?_)
      exact mul_nonneg (mul_nonneg (mul_nonneg hCLpos.le (Real.rpow_nonneg (by linarith) _))
        (add_nonneg (Real.rpow_nonneg hXpos.le _) (Real.rpow_nonneg hU'pos.le _)))
        (by positivity)
    -- step 2: replace the two factors by their upper bounds
    have hstep2 : (1 / (2 * Real.pi)) * (((CL * 𝓓 ^ ((1 : ℝ) / 2 + p.η))
          * (X ^ (-σ.re) + U' ^ (-σ.re)) * (2 * W) ^ 2) * (CG * L / (2 * c₀)))
        ≤ (1 / (2 * Real.pi)) * (CL * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (2 * U' ^ (1 - 2 * p.σ₀))
            * (4 * 𝓓 ^ (2 * p.w)) * (CG * L / (2 * c₀))) := by
      refine mul_le_mul_of_nonneg_left ?_ h2π.le
      have hW2 : ((2 * W) ^ 2 : ℝ) = 4 * 𝓓 ^ (2 * p.w) := by
        rw [hW𝓓, mul_pow, ← Real.rpow_natCast (𝓓 ^ p.w) 2, ← Real.rpow_mul h𝓓pos.le]
        ring_nf
      rw [hW2]
      have hA0 : 0 ≤ CL * 𝓓 ^ ((1 : ℝ) / 2 + p.η) := by positivity
      have hD0 : 0 ≤ 4 * 𝓓 ^ (2 * p.w) := by positivity
      have hK0 : 0 ≤ CG * L / (2 * c₀) := by positivity
      refine mul_le_mul_of_nonneg_right ?_ hK0
      refine mul_le_mul_of_nonneg_right ?_ hD0
      exact mul_le_mul_of_nonneg_left hB hA0
    -- step 3: collect the powers
    have hstep3 : (1 / (2 * Real.pi)) * (CL * 𝓓 ^ ((1 : ℝ) / 2 + p.η) * (2 * U' ^ (1 - 2 * p.σ₀))
          * (4 * 𝓓 ^ (2 * p.w)) * (CG * L / (2 * c₀)))
        = (1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀))
          * L ^ (1 + 2 * (2 * p.σ₀ - 1))
          * 𝓓 ^ (1 / 2 + p.η + 2 * p.w - p.u * (2 * p.σ₀ - 1)) := by
      rw [hU'eq]
      have h𝓓pow : 𝓓 ^ ((1 : ℝ) / 2 + p.η) * 𝓓 ^ (-(p.u * (2 * p.σ₀ - 1))) * 𝓓 ^ (2 * p.w)
          = 𝓓 ^ (1 / 2 + p.η + 2 * p.w - p.u * (2 * p.σ₀ - 1)) := by
        rw [← Real.rpow_add h𝓓pos, ← Real.rpow_add h𝓓pos]
        congr 1
        ring
      have hLpow : L ^ (2 * (2 * p.σ₀ - 1)) * L = L ^ (1 + 2 * (2 * p.σ₀ - 1)) := by
        calc L ^ (2 * (2 * p.σ₀ - 1)) * L
            = L ^ (2 * (2 * p.σ₀ - 1)) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = L ^ (2 * (2 * p.σ₀ - 1) + 1) := (Real.rpow_add hLpos _ _).symm
          _ = L ^ (1 + 2 * (2 * p.σ₀ - 1)) := by congr 1; ring
      rw [← h𝓓pow, ← hLpow]
      ring
    -- step 4: the exponent is `≤ -η` by `P2`
    have hstep4 : (1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀))
          * L ^ (1 + 2 * (2 * p.σ₀ - 1)) * 𝓓 ^ (1 / 2 + p.η + 2 * p.w - p.u * (2 * p.σ₀ - 1))
        ≤ ((1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀)) + 1)
            * L ^ (1 + 2 * (2 * p.σ₀ - 1)) * 𝓓 ^ (-p.η) := by
      have hexp : (1 : ℝ) / 2 + p.η + 2 * p.w - p.u * (2 * p.σ₀ - 1) ≤ -p.η := by
        nlinarith [p.P2]
      have h𝓓e : 𝓓 ^ (1 / 2 + p.η + 2 * p.w - p.u * (2 * p.σ₀ - 1)) ≤ 𝓓 ^ (-p.η) :=
        Real.rpow_le_rpow_of_exponent_le h𝓓1 hexp
      have h0 : 0 ≤ (1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀)) := by positivity
      have hLp : 0 ≤ L ^ (1 + 2 * (2 * p.σ₀ - 1)) := Real.rpow_nonneg (by linarith) _
      have h1 : 0 ≤ (1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀))
          * L ^ (1 + 2 * (2 * p.σ₀ - 1)) := by positivity
      calc (1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀))
            * L ^ (1 + 2 * (2 * p.σ₀ - 1)) * 𝓓 ^ (1 / 2 + p.η + 2 * p.w - p.u * (2 * p.σ₀ - 1))
          ≤ (1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀))
              * L ^ (1 + 2 * (2 * p.σ₀ - 1)) * 𝓓 ^ (-p.η) :=
            mul_le_mul_of_nonneg_left h𝓓e h1
        _ ≤ ((1 / (2 * Real.pi)) * CL * 8 * CG * (1 / (2 * c₀)) + 1)
              * L ^ (1 + 2 * (2 * p.σ₀ - 1)) * 𝓓 ^ (-p.η) := by
            have h2 : 0 ≤ L ^ (1 + 2 * (2 * p.σ₀ - 1)) := hLp
            have h3 : 0 ≤ 𝓓 ^ (-p.η) := Real.rpow_nonneg h𝓓pos.le _
            nlinarith [h0, h2, h3]
    exact le_trans hstep1 (le_trans hstep2 (hstep3 ▸ hstep4))
  have hnorm2 : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul]
    simp [Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le]
  rw [norm_mul, hnorm2]
  exact hmain

end Work.ZeroDensity.LogFree
