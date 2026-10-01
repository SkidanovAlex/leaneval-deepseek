import Mathlib
import Submission.Work.LinnikAreas2.d1_of_area1
import Submission.Work.LinnikAreas.Density4.det_split

namespace Work.LinnikAreas2

open scoped Classical BigOperators
noncomputable section

/-! ## Absolute convergence of the off-diagonal product `a_n · conj a'_n`

The coefficient `a_n` of HB (11.11) is

`a_n = √w_χ · Θ(n) · χ(n) · n^{1/2-ρ} · √(wt_n)`,

a polynomial size factor times `√(wt_n)`.  By `wt_le_exp` the weight satisfies
`wt_n ≤ e^{-n/q^x}` and `q^x > 0`, so `√(wt_n)² ≤ e^{-n/q^x}` is exponentially
decaying.  The remaining factors `|Θ(n)| ≤ n` (the divisor-sum bound of
`abs_thetaS_le`) and `‖n^{1/2-ρ}‖ = n^{1/2-Re ρ}` grow at most polynomially.
Hence for *arbitrary* parameters `(q, u, w, x, χ, ρ, w_χ)` the sequence
`n ↦ a_n · conj a'_n` is dominated by `n ↦ C · n^K · e^{-n/q^x}`, which is
summable.  This is the (absolute) convergence that all the `tsum` manipulations
of HB §11 rely on.

Note that no hypothesis on `ρ` (in particular no zero-free region) is needed:
the convergence is a purely quantitative decay statement. -/

/-- Boundary behaviour of the complex power `n ↦ n^s`: for `n ≥ 1` the modulus
of `n^s` is at most `n^K` whenever `s.re ≤ K`. -/
lemma norm_natCast_cpow_le {n : ℕ} (hn : 0 < n) {s : ℂ} {K : ℕ} (hK : s.re ≤ (K : ℝ)) :
    ‖((n : ℂ) ^ s)‖ ≤ (n : ℝ) ^ K := by
  rw [Complex.norm_natCast_cpow_of_pos hn, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hK

/-- The squared modulus of the Heath-Brown weight `√(wt_n)` is bounded by
`e^{-n/q^x}`: the weight itself is `≤ e^{-n/q^x}` (`wt_le_exp`), and `√x² = x`
on the nonnegative part while `√x = 0` for `x < 0`. -/
lemma sqrt_WT_sq_le {q : ℕ} [NeZero q] (u x : ℝ) (n : ℕ) :
    (Real.sqrt (Work.LinnikAreas2.WT q u x n)) ^ 2 ≤ Real.exp (-(n : ℝ) / (q : ℝ) ^ x) := by
  have hle : Work.LinnikAreas2.WT q u x n ≤ Real.exp (-(n : ℝ) / (q : ℝ) ^ x) :=
    Work.LinnikAreas2.wt_le_exp n
  have hb : 0 ≤ Real.exp (-(n : ℝ) / (q : ℝ) ^ x) := (Real.exp_pos _).le
  calc (Real.sqrt (Work.LinnikAreas2.WT q u x n)) ^ 2
      ≤ (Real.sqrt (Real.exp (-(n : ℝ) / (q : ℝ) ^ x))) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hle) 2
    _ = Real.exp (-(n : ℝ) / (q : ℝ) ^ x) := Real.sq_sqrt hb

/-- Pointwise polynomial bound for one coefficient:
`‖a_n‖ ≤ √w_χ · |Θ(n)| · n^{⌈1/2+|Re ρ|⌉} · √(wt_n)` for `n ≥ 1`.
The four factors come from `√w_χ`, the modulus `|Θ(n)| ≥ 0`, the unit modulus
of `χ(n)`, the complex power `n^{1/2-ρ}`, and the weight. -/
lemma norm_acoef_le {q : ℕ} [NeZero q] {u w x : ℝ} (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (wc : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖
      ≤ Real.sqrt wc * |Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n|
          * (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|)) * Real.sqrt (Work.LinnikAreas2.WT q u x n) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcp : ‖((n : ℂ) ^ ((1 / 2 : ℂ) - ρ))‖ ≤ (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|)) := by
    refine norm_natCast_cpow_le hn ?_
    have hre : ((1 / 2 : ℂ) - ρ).re = 1 / 2 - ρ.re := by simp [Complex.sub_re]
    rw [hre]
    calc (1 / 2 - ρ.re : ℝ) ≤ 1 / 2 + |ρ.re| := by linarith [neg_le_abs ρ.re]
      _ ≤ ((Nat.ceil (1 / 2 + |ρ.re|) : ℕ) : ℝ) := Nat.le_ceil _
  have hwc : ‖((Real.sqrt wc : ℝ) : ℂ)‖ = Real.sqrt wc := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg wc)]
  have hth : ‖(((Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n : ℝ)) : ℂ)‖
      = |Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hwt : ‖((Real.sqrt (Work.LinnikAreas2.WT q u x n) : ℝ) : ℂ)‖
      = Real.sqrt (Work.LinnikAreas2.WT q u x n) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hchi : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  calc ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖
      = Real.sqrt wc * |Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n| * ‖χ (n : ZMod q)‖
          * ‖((n : ℂ) ^ ((1 / 2 : ℂ) - ρ))‖ * Real.sqrt (Work.LinnikAreas2.WT q u x n) := by
          simp only [Work.LinnikAreas2.acoef, norm_mul, hwc, hth, hwt]
    _ ≤ Real.sqrt wc * |Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n| * 1
          * (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|)) * Real.sqrt (Work.LinnikAreas2.WT q u x n) := by
          gcongr
    _ = Real.sqrt wc * |Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n|
          * (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|)) * Real.sqrt (Work.LinnikAreas2.WT q u x n) := by
          ring

/-- **Absolute convergence of `n ↦ a_n · conj a'_n`.**  The sequence is dominated
by `√w_χ √w_{χ'} · n^{K} · e^{-n/q^x}` with `K = ⌈1/2+|Re ρ|⌉ + ⌈1/2+|Re ρ'|⌉ + 2`,
which is summable because `q^x > 0` and any polynomial is dominated by an
exponential. -/
theorem acoef_pair_summable {q : ℕ} [NeZero q] {u w x : ℝ}
    (χ χ' : DirichletCharacter ℂ q) (ρ ρ' : ℂ) (wc wc' : ℝ) :
    Summable (fun n : ℕ =>
      Work.LinnikAreas2.acoef q u w x χ ρ wc n
        * (starRingEnd ℂ) (Work.LinnikAreas2.acoef q u w x χ' ρ' wc' n)) := by
  set X : ℝ := (q : ℝ) ^ x with hXeq
  have hXpos : 0 < X := by
    rw [hXeq]; exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos q)) x
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => Real.sqrt wc * Real.sqrt wc'
        * ((n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|)) * (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ'.re|))
            * (n : ℝ) ^ 2 * Real.exp (-(1 / X) * (n : ℝ)))) ?hg ?hb
  · -- summability of the majorant: one power of `n` times a geometric decay
    have hbase : Summable (fun n : ℕ =>
        (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|) + Nat.ceil (1 / 2 + |ρ'.re|) + 2)
          * Real.exp (-(1 / X) * (n : ℝ))) :=
      Real.summable_pow_mul_exp_neg_nat_mul _ (by positivity)
    refine (hbase.mul_left (Real.sqrt wc * Real.sqrt wc')).congr (fun n => ?_)
    rw [pow_add, pow_add]
  · intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [Work.LinnikAreas2.acoef_zero]
    · have hA := norm_acoef_le (u := u) (w := w) (x := x) χ ρ wc hn
      have hB := norm_acoef_le (u := u) (w := w) (x := x) χ' ρ' wc' hn
      have hθ : |Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n| ≤ (n : ℝ) :=
        Work.LinnikAreas.Density4.abs_thetaS_le _ _
      have hWT : (Real.sqrt (Work.LinnikAreas2.WT q u x n)) ^ 2 ≤ Real.exp (-(n : ℝ) / X) := by
        have hle : Work.LinnikAreas2.WT q u x n ≤ Real.exp (-(n : ℝ) / X) := by
          rw [hXeq]; exact Work.LinnikAreas2.wt_le_exp n
        have hb : 0 ≤ Real.exp (-(n : ℝ) / X) := (Real.exp_pos _).le
        calc (Real.sqrt (Work.LinnikAreas2.WT q u x n)) ^ 2
            ≤ (Real.sqrt (Real.exp (-(n : ℝ) / X))) ^ 2 :=
              pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hle) 2
          _ = Real.exp (-(n : ℝ) / X) := Real.sq_sqrt hb
      have hsq : Real.sqrt (Work.LinnikAreas2.WT q u x n) * Real.sqrt (Work.LinnikAreas2.WT q u x n)
          ≤ Real.exp (-(n : ℝ) / X) := by rw [← pow_two]; exact hWT
      calc ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n
              * (starRingEnd ℂ) (Work.LinnikAreas2.acoef q u w x χ' ρ' wc' n)‖
          = ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖
              * ‖Work.LinnikAreas2.acoef q u w x χ' ρ' wc' n‖ := by
              rw [norm_mul, Complex.norm_conj]
        _ ≤ (Real.sqrt wc * |Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n|
                * (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|)) * Real.sqrt (Work.LinnikAreas2.WT q u x n))
              * (Real.sqrt wc' * |Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n|
                * (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ'.re|)) * Real.sqrt (Work.LinnikAreas2.WT q u x n)) := by
              exact mul_le_mul hA hB (norm_nonneg _) (by positivity)
        _ = Real.sqrt wc * Real.sqrt wc'
              * (|Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n|
                  * |Work.LinnikAreas.Density4.thetaS ((q : ℝ) ^ w) n|)
              * ((n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|)) * (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ'.re|)))
              * (Real.sqrt (Work.LinnikAreas2.WT q u x n)
                  * Real.sqrt (Work.LinnikAreas2.WT q u x n)) := by
              ring
        _ ≤ Real.sqrt wc * Real.sqrt wc' * ((n : ℝ) * (n : ℝ))
              * ((n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|)) * (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ'.re|)))
              * Real.exp (-(n : ℝ) / X) := by
              gcongr
        _ = Real.sqrt wc * Real.sqrt wc'
              * ((n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ.re|)) * (n : ℝ) ^ (Nat.ceil (1 / 2 + |ρ'.re|))
                  * (n : ℝ) ^ 2 * Real.exp (-(1 / X) * (n : ℝ))) := by
              rw [show Real.exp (-(n : ℝ) / X) = Real.exp (-(1 / X) * (n : ℝ)) by congr 1; ring]
              ring

end

end Work.LinnikAreas2
