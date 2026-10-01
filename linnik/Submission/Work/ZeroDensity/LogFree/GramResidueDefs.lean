import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs

/-!
# `Work.ZeroDensity.LogFree` — the residue decomposition of the `q`-free Gram entry

This file fixes the vocabulary of the proof of `gramEntrySame`: the Fréchet/contour identity

  `gramEntryFree W X U' ρ ρ' - (poleResidue W : ℂ) * poleK X U' ρ ρ'
      = (1/2π) ∫_ℝ gramPhi W X U' s (δ + it) dt`,   `s = 1 - ρ - conj ρ'`, `δ = s.re`,

obtained by shifting the inverse-Mellin contour `Re z = 2` of the smoothed sum down to
`Re z = δ`, the only pole crossed being the ζ-pole at `z = s + 1` (the Γ-pole at `z = 0` is
killed by the vanishing of `X^z - U'^z` there).

The pieces:

* `gramA W s z = Σ_{d,e ≤ ⌈W⌉} θ_d θ_e [d,e]^{s-z}` — the finite "lcm weight" of the mollifier,
  entire in `z`, with `gramA W s (s+1) = poleResidue W` and `‖gramA W s z‖ ≤ ⌈W⌉²` for
  `z.re = s.re`;
* `zetaReg w = w·ζ(w+1)` (`= 1` at `w = 0`) — the ζ-pole factor, entire;
* `gammaPow X U' z = Γ(z)·(X^z - U'^z)`, redefined at `z = 0` by its removable value, so that
  it is holomorphic on `z.re > -1` (this is the Γ-pole at `0` removed);
* `gramPhi` — the integrand on the contour, with the ζ-pole at `z = s + 1`;
* `gramPsi z = (z - (s+1))·gramPhi z` — its regularized numerator, holomorphic on the strip, with
  `gramPsi (s+1) = (poleResidue W : ℂ) * poleK X U' ρ ρ'`.
-/

open DirichletCharacter Complex Filter
open scoped Classical BigOperators Topology
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikContract

/-- The finite "lcm weight" of the mollifier `θ_d` (HB (11.7)):
`A(z) = Σ_{d,e ≤ ⌈W⌉} θ_d θ_e [d,e]^{s-z}`.  At `z = s+1` this is the pole residue
`Σ θ_d θ_e / [d,e] = poleResidue W`. -/
def gramA (W : ℝ) (s z : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (Nat.ceil W), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
    ((Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)
      * ((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ)
      * (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))

/-- The ζ-pole factor `w ↦ w·ζ(w+1)`, redefined at `w = 0` so as to be continuous there
(the removable singularity of `ζ` at `1`). -/
def zetaReg : ℂ → ℂ :=
  Function.update (fun w : ℂ => w * riemannZeta (w + 1)) 0 1

/-- `Γ(z)·(X^z - U'^z)`, redefined at `z = 0` by its removable value `log X - log U'`
(the Γ-pole at `0` being cancelled by the vanishing of `X^z - U'^z`).  This is holomorphic on
`z.re > -1`. -/
def gammaPow (X U' : ℝ) (z : ℂ) : ℂ :=
  Function.update (fun z : ℂ => Complex.Gamma z * ((X : ℂ) ^ z - (U' : ℂ) ^ z)) 0
    (limUnder (𝓝[≠] (0 : ℂ)) fun z : ℂ => Complex.Gamma z * ((X : ℂ) ^ z - (U' : ℂ) ^ z)) z

/-- The integrand of the inverse-Mellin representation of the smoothing
`e^{-n/X} - e^{-n/U'}`: `Γ(z)(X^z - U'^z)·ζ(z-s)·gramA W s z`, whose only pole in the
strip `-1 < z.re < 2` is the ζ-pole at `z = s + 1`. -/
def gramPhi (W X U' : ℝ) (s z : ℂ) : ℂ :=
  gammaPow X U' z * riemannZeta (z - s) * gramA W s z

/-- The numerator `(z - (s+1))·gramPhi z`, holomorphic across the pole. -/
def gramPsi (W X U' : ℝ) (s z : ℂ) : ℂ :=
  gammaPow X U' z * zetaReg (z - s - 1) * gramA W s z


/-! ## Elementary values and the `lcm`-weight facts -/

lemma zetaReg_zero : zetaReg 0 = 1 := Function.update_self _ _ _

lemma zetaReg_of_ne {w : ℂ} (hw : w ≠ 0) : zetaReg w = w * riemannZeta (w + 1) :=
  Function.update_of_ne hw _ _

lemma gammaPow_of_ne (X U' : ℝ) {z : ℂ} (hz : z ≠ 0) :
    gammaPow X U' z = Complex.Gamma z * ((X : ℂ) ^ z - (U' : ℂ) ^ z) :=
  Function.update_of_ne hz _ _

lemma gramA_shift (W : ℝ) (s w : ℂ) : gramA W s (w + s) = gramA W 0 w := by
  rw [gramA, gramA]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  have : s - (w + s) = -(w) - 0 := by ring
  rw [this]
  ring

lemma gramA_differentiableAt (W : ℝ) (s z : ℂ) :
    DifferentiableAt ℂ (gramA W s) z := by
  classical
  rw [show gramA W s = (fun z : ℂ => ∑ d ∈ Finset.Icc 1 (Nat.ceil W),
      ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
      ((Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)
        * ((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ)
        * (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))) from rfl]
  refine DifferentiableAt.fun_sum fun d hd => DifferentiableAt.fun_sum fun e he => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  have hlcm : 0 < Nat.lcm d e := Nat.lcm_pos (by omega) (by omega)
  have hc : ((Nat.lcm d e : ℕ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]; exact Complex.ofReal_ne_zero.mpr (by exact_mod_cast hlcm.ne')
  have hone : DifferentiableAt ℂ (fun z : ℂ => (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))) z := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => s - z) z :=
      (differentiableAt_const (c := s)).sub differentiableAt_id
    exact h1.const_cpow (Or.inl hc)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => ((Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)
      * (((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ) * (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z)))) z :=
    (hone.const_mul ((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ)).const_mul
      ((Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)
  simpa only [mul_assoc] using h2

lemma gramA_eq_poleResidue (W : ℝ) (s : ℂ) : gramA W s (s + 1) = ((poleResidue W : ℝ) : ℂ) := by
  rw [gramA, poleResidue, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hne : s + 1 ≠ s := by intro h; exact one_ne_zero (by linear_combination h)
  have hexp : s - (s + 1) = -1 := by ring
  rw [hexp, Complex.cpow_neg_one, Complex.ofReal_div, Complex.ofReal_mul]
  rfl

lemma abs_thetaM_le_one' {W : ℝ} (hW : 1 < W) (d : ℕ) :
    |Work.LinnikAreas.Density4.thetaM W d| ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [Work.LinnikAreas.Density4.thetaM]
  · have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    rw [Work.LinnikAreas.Density4.thetaM]
    split_ifs with hdle
    · have hlogW : 0 < Real.log W := Real.log_pos hW
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := d)
        rw [← Int.cast_abs]
        exact_mod_cast h
      have hWd1 : 1 ≤ W / (d:ℝ) := (one_le_div₀ hdpos).mpr (by linarith)
      have hWdle : W / (d:ℝ) ≤ W := by
        rw [div_le_iff₀ hdpos]; nlinarith [hd1, hW]
      have hlognn : 0 ≤ Real.log (W / (d:ℝ)) := Real.log_nonneg hWd1
      have hlogle : Real.log (W / (d:ℝ)) ≤ Real.log W := Real.log_le_log (by linarith) hWdle
      rw [abs_div, abs_mul, abs_of_nonneg hlognn, abs_of_pos hlogW, div_le_one₀ hlogW]
      calc |(ArithmeticFunction.moebius d : ℝ)| * Real.log (W / (d:ℝ))
          ≤ 1 * Real.log W := mul_le_mul hmu hlogle hlognn (by norm_num)
        _ = Real.log W := one_mul _
    · simp

lemma norm_gramA_le (W : ℝ) (hW : 1 < W) (s z : ℂ) (hz : z.re = s.re) :
    ‖gramA W s z‖ ≤ ((Nat.ceil W : ℝ)) ^ 2 := by
  classical
  rw [gramA]
  have hd_card : ((Finset.Icc 1 (Nat.ceil W)).card : ℝ) ≤ (Nat.ceil W : ℝ) := by
    have : (Finset.Icc 1 (Nat.ceil W)).card ≤ Nat.ceil W := by
      rw [Nat.card_Icc]; omega
    exact_mod_cast this
  have hcard0 : (0 : ℝ) ≤ ((Finset.Icc 1 (Nat.ceil W)).card : ℝ) := Nat.cast_nonneg _
  have hterm : ∀ d ∈ Finset.Icc 1 (Nat.ceil W), ∀ e ∈ Finset.Icc 1 (Nat.ceil W),
      ‖(((Work.LinnikAreas.Density4.thetaM W d : ℝ)) : ℂ)
        * ((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ)
        * (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))‖ ≤ 1 := by
    intro d hd e he
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hlcm : 0 < Nat.lcm d e := Nat.lcm_pos (by omega) (by omega)
    have hbase : ‖(((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hlcm, Complex.sub_re, hz, sub_self, Real.rpow_zero]
    rw [norm_mul, norm_mul, hbase,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_one]
    have h1 := abs_thetaM_le_one' hW d
    have h2 := abs_thetaM_le_one' hW e
    nlinarith [abs_nonneg (Work.LinnikAreas.Density4.thetaM W d),
      abs_nonneg (Work.LinnikAreas.Density4.thetaM W e)]
  calc ‖∑ d ∈ Finset.Icc 1 (Nat.ceil W), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
        ((Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)
          * ((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ)
          * (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))‖
      ≤ ∑ d ∈ Finset.Icc 1 (Nat.ceil W), ‖∑ e ∈ Finset.Icc 1 (Nat.ceil W),
          ((Work.LinnikAreas.Density4.thetaM W d : ℝ) : ℂ)
            * ((Work.LinnikAreas.Density4.thetaM W e : ℝ) : ℂ)
            * (((Nat.lcm d e : ℕ) : ℂ) ^ (s - z))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.ceil W), ∑ e ∈ Finset.Icc 1 (Nat.ceil W), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        refine le_trans (norm_sum_le _ _) ?_
        exact Finset.sum_le_sum fun e he => hterm d hd e he
    _ = ((Finset.Icc 1 (Nat.ceil W)).card : ℝ)
          * ((Finset.Icc 1 (Nat.ceil W)).card : ℝ) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp [nsmul_eq_mul]
    _ ≤ (Nat.ceil W : ℝ) ^ 2 := by nlinarith [hd_card, hcard0]

end Work.ZeroDensity.LogFree
