import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.ZeroDensity.LogFree.LFunction_strip_bound
import Submission.Work.LinnikAreas.Density4.det_split
import Submission.Work.LinnikAreas.Density4.zeroDetAux
import Submission.Work.LinnikAreas2.Hb11Defs
import Submission.Work.LinnikAreas2.psiS_one_eq_thetaS
import Submission.Work.LinnikAreas2.hb11_crude_bound
import Submission.Work.LinnikAreas2.dslope_diff_cpow_norm_le

/-!
# `Work.ZeroDensity.LogFree.CrossDefs` — the vocabulary of the cross-character Gram entry (L3(a))

The cross-character Gram entry of Heath-Brown (1992) §11, L3(a) of `JUTILA_UNIFIED_LEAD.md` §3, is

  `G_ij = Σ'_n (Σ_{d|n} θ_d)² (χ_i χ_j^{-1})(n) n^{1-ρ_i-\barρ_j} g(n)`,
  `g(n) = e^{-n/X} - e^{-n/U'}`,

which is `Work.ZeroDensity.LogFree.gramEntry`.  Writing `ψ = χ χ'⁻¹` (non-principal because
`χ ≠ χ'`) and `σ = ρ + \barρ' - 1`, the entry is the difference of the two smoothed Dirichlet sums
`Ssm q 1 W W X ψ σ - Ssm q 1 W W U' ψ σ` (`crossGram`): at the parameters `U = 1`, `V = W` the
mollifier `Ψ` of `Density4.psiM` reproduces `Θ` (`LinnikAreas2.psiS_one_eq_thetaS`), so the
coefficient is `Θ(n)²`.

The contour input is the regularised kernel `LinnikAreas2.Ptw q 1 W W X U' ψ σ`, which is
`Γ(s+1)·dslope (u ↦ X^u - U'^u) 0 s · L(σ+s,ψ) · F(σ+s)` with the finite lcm-weight
`F(s) = lcmF q 1 W W ψ s = Σ_{d,e ≤ ⌈W⌉} θ_d θ_e ψ([d,e]) [d,e]^{-s}` (`crossQ`).  On the line
`Re(σ+s) = 0` (`Re s = -Re σ`) the convexity bound bounds `L` by `𝓓^{1/2+η}(2+|t|)^{1/2+η}` and
`F` by `(2W)²`, giving the gain `𝓓^{1/2+η} W² U'^{1-2σ₀}` of L3(a).
-/

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikAreas.Density4

/-- At `U = 1` the mollifier `ψ_d` (with cut-off `V = W`) coincides with `θ_d` (with cut-off `W`)
for every `d ≥ 1`. -/
lemma psiM_one_eq_thetaM {W : ℝ} (hW : 1 < W) {d : ℕ} (hd : 1 ≤ d) :
    psiM 1 W d = thetaM W d := by
  rcases eq_or_lt_of_le hd with h | h
  · subst h
    have hlog : Real.log W ≠ 0 := ne_of_gt (Real.log_pos hW)
    simp only [psiM, thetaM, Nat.cast_one, div_one]
    rw [if_pos le_rfl, if_pos hW.le]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]
    exact (div_self hlog).symm
  · have hd1 : ¬ ((d : ℝ) ≤ 1) := by
      have h2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
      linarith
    simp only [psiM, thetaM, if_neg hd1, div_one]

/-- The two divisor sums `Θ` agree (`LogFree.thetaS` is `Density4.thetaS`). -/
lemma logfree_thetaS_eq (W : ℝ) (n : ℕ) :
    thetaS W n = Work.LinnikAreas.Density4.thetaS W n := rfl

/-- The finite Dirichlet polynomial `Q_ψ` of the cross-character Gram entry:
`Q_ψ(s) = Σ_{d,e ≤ ⌈W⌉} θ_d θ_e ψ([d,e]) [d,e]^{-s}`.  It is the lcm-weight `F` of HB §11 at
the parameters `U = 1`, `V = W`. -/
def crossQ (q : ℕ) [NeZero q] (W : ℝ) (ψ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 ⌈W⌉₊, ∑ e ∈ Finset.Icc 1 ⌈W⌉₊,
    ((thetaM W d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ)
      * (ψ ((Nat.lcm d e : ℕ) : ZMod q)) * (((Nat.lcm d e : ℕ) : ℂ) ^ (-s))

/-- `crossQ` is the lcm-weight `F` of HB §11 at the parameters `U = 1`, `V = W`. -/
lemma lcmF_one_eq_crossQ (q : ℕ) [NeZero q] {W : ℝ} (hW : 1 < W)
    (ψ : DirichletCharacter ℂ q) (s : ℂ) :
    lcmF q 1 W W ψ s = crossQ q W ψ s := by
  rw [lcmF, crossQ]
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  rw [psiM_one_eq_thetaM hW hd1]

/-- On the line `Re s ≥ 0` the polynomial `Q_ψ` is bounded by `(2W)²`. -/
lemma norm_crossQ_le (q : ℕ) [NeZero q] {W : ℝ} (hW : 1 < W)
    (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖crossQ q W ψ s‖ ≤ (2 * W) ^ 2 := by
  have hW0 : (0 : ℝ) < W := lt_trans one_pos hW
  have hterm : ∀ d ∈ Finset.Icc 1 ⌈W⌉₊, ∀ e ∈ Finset.Icc 1 ⌈W⌉₊,
      ‖((thetaM W d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ)
        * (ψ ((Nat.lcm d e : ℕ) : ZMod q)) * (((Nat.lcm d e : ℕ) : ℂ) ^ (-s))‖ ≤ 1 := by
    intro d hd e he
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hd0 : 0 < d := by omega
    have he0 : 0 < e := by omega
    have hlcm1 : 1 ≤ Nat.lcm d e :=
      le_trans hd1 (Nat.le_of_dvd (Nat.lcm_pos hd0 he0) (Nat.dvd_lcm_left d e))
    have hlcmpos : (0 : ℝ) < (Nat.lcm d e : ℝ) := by exact_mod_cast hlcm1
    have hnorm : ‖(((Nat.lcm d e : ℕ) : ℂ) ^ (-s))‖ = (Nat.lcm d e : ℝ) ^ (-s.re) := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hlcmpos, Complex.neg_re]
    have hle1 : (Nat.lcm d e : ℝ) ^ (-s.re) ≤ 1 := by
      rw [← Real.rpow_zero (Nat.lcm d e : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hlcm1) (by linarith)
    have hθd : ‖((thetaM W d : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.LinnikAreas2.abs_thetaM_le_one hW d
    have hθe : ‖((thetaM W e : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.LinnikAreas2.abs_thetaM_le_one hW e
    have hψ : ‖(ψ ((Nat.lcm d e : ℕ) : ZMod q) : ℂ)‖ ≤ 1 := ψ.norm_le_one _
    have hA0 : (0 : ℝ) ≤ ‖((thetaM W d : ℝ) : ℂ)‖ := norm_nonneg _
    have hB0 : (0 : ℝ) ≤ ‖((thetaM W e : ℝ) : ℂ)‖ := norm_nonneg _
    have hC0 : (0 : ℝ) ≤ ‖(ψ ((Nat.lcm d e : ℕ) : ZMod q) : ℂ)‖ := norm_nonneg _
    have hD0 : (0 : ℝ) ≤ (Nat.lcm d e : ℝ) ^ (-s.re) := Real.rpow_nonneg hlcmpos.le _
    have h1 : ‖((thetaM W d : ℝ) : ℂ)‖ * ‖((thetaM W e : ℝ) : ℂ)‖
          * ‖(ψ ((Nat.lcm d e : ℕ) : ZMod q) : ℂ)‖ ≤ 1 * 1 * 1 :=
      mul_le_mul (mul_le_mul hθd hθe hB0 (by norm_num)) hψ hC0 (by norm_num)
    have h2 : ‖((thetaM W d : ℝ) : ℂ)‖ * ‖((thetaM W e : ℝ) : ℂ)‖
          * ‖(ψ ((Nat.lcm d e : ℕ) : ZMod q) : ℂ)‖ * (Nat.lcm d e : ℝ) ^ (-s.re)
        ≤ (1 * 1 * 1) * 1 :=
      mul_le_mul h1 hle1 hD0 (by norm_num)
    rw [norm_mul, norm_mul, norm_mul, hnorm]
    linarith [h2]
  calc ‖crossQ q W ψ s‖
      ≤ ∑ d ∈ Finset.Icc 1 ⌈W⌉₊, ∑ e ∈ Finset.Icc 1 ⌈W⌉₊, (1 : ℝ) := by
        rw [crossQ]
        exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun d hd =>
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun e he => hterm d hd e he))
    _ = ((Finset.Icc 1 ⌈W⌉₊).card : ℝ) * ((Finset.Icc 1 ⌈W⌉₊).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * W) ^ 2 := by
        have hceil : ((⌈W⌉₊ : ℕ) : ℝ) < W + 1 := Nat.ceil_lt_add_one hW0.le
        have hcardle : ((Finset.Icc 1 ⌈W⌉₊).card : ℝ) ≤ 2 * W := by
          rw [Nat.card_Icc]
          push_cast
          linarith
        have hnn : (0 : ℝ) ≤ ((Finset.Icc 1 ⌈W⌉₊).card : ℝ) := Nat.cast_nonneg _
        nlinarith [hcardle, hnn]

/-- The cross-character Gram sum, as the difference of the two cut-off smoothed Dirichlet sums of
the coefficient `Θ(n)² ψ(n)`. -/
def crossGram (q : ℕ) [NeZero q] (W X U' : ℝ) (ψ : DirichletCharacter ℂ q) (σ : ℂ) : ℂ :=
  Ssm q 1 W W X ψ σ - Ssm q 1 W W U' ψ σ

/-- **The cross Gram entry is the difference of two smoothed Dirichlet sums.**  With `ψ = χ χ'⁻¹`
(non-principal for `χ ≠ χ'`) and `σ = ρ + \barρ' - 1`,

  `gramEntry q W X U' χ χ' ρ ρ' = Ssm q 1 W W X ψ σ - Ssm q 1 W W U' ψ σ`. -/
theorem gramEntry_eq_crossGram (q : ℕ) [NeZero q] {W X U' : ℝ} (hW : 1 < W) (hX : 0 < X)
    (hU' : 0 < U') (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ) :
    gramEntry q W X U' χ χ' ρ ρ'
      = crossGram q W X U' (χ * χ'⁻¹) (ρ + (starRingEnd ℂ) ρ' - 1) := by
  set σ : ℂ := ρ + (starRingEnd ℂ) ρ' - 1 with hσ
  set ψ : DirichletCharacter ℂ q := χ * χ'⁻¹ with hψ
  have hsX : Summable (fun n : ℕ =>
      detCoeff q 1 W W ψ σ n * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ)) := by
    have := summable_detCoeff_mul_exp (q := q) 1 W W ψ σ (t := 1 / X) one_pos (by positivity)
    simpa [div_eq_mul_inv] using this
  have hsY : Summable (fun n : ℕ =>
      detCoeff q 1 W W ψ σ n * ((Real.exp (-(n : ℝ) / U') : ℝ) : ℂ)) := by
    have := summable_detCoeff_mul_exp (q := q) 1 W W ψ σ (t := 1 / U') one_pos (by positivity)
    simpa [div_eq_mul_inv] using this
  rw [crossGram, Ssm, Ssm, ← Summable.tsum_sub hsX hsY, gramEntry]
  refine tsum_congr fun n => ?_
  have hdet : detCoeff q 1 W W ψ σ n
      = ((Work.LinnikAreas.Density4.thetaS W n : ℝ) : ℂ) ^ 2 * (ψ (n : ZMod q))
          * ((n : ℂ) ^ (-σ)) := by
    rw [detCoeff, Work.LinnikAreas2.psiS_one_eq_thetaS (W := W) hW]
    ring
  have hexp : (-σ) = (1 : ℂ) - ρ - (starRingEnd ℂ) ρ' := by rw [hσ]; ring
  rw [logfree_thetaS_eq W n, hdet, hexp, hψ]
  simp only [Complex.ofReal_sub]
  ring

end Work.ZeroDensity.LogFree
