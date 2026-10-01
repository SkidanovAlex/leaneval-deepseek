/-
# Abel's integral representation for `ζ(s)L(s,χ) - s·L(1,χ)/(s-1)`

For a Dirichlet character `χ` mod `q` and `1 < Re s`, Abel summation applied to the
coefficients `λ(n) = Σ_{d ∣ n} χ(d)` of `ζ(s)L(s,χ) = Σ λ(n) n^{-s}` gives

  `s · ∫_1^∞ (A(x) - x·L(1,χ)) x^{-s-1} dx = ζ(s)L(s,χ) - s·L(1,χ)/(s-1)`,

where `A(x) = Σ_{n ≤ x} λ(n)` and the hypothesis `‖A(x) - x·L(1,χ)‖ ≤ K√x` provides the
convergence of the integral (this is the crude Pólya–Vinogradov-type bound available for the
application).  The proof splits `A(x) - x·L(1,χ) = A(x) - x·L(1,χ)`, uses
`LSeries_eq_mul_integral` for `A(x)x^{-s-1}` and the elementary
`∫_1^∞ x^{-s} dx = 1/(s-1)` for the linear piece.
-/
import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Work.LinnikAreas.AsumCPowIntegrable
import Submission.Work.LinnikAreas.AsumPartialIsBigO

namespace Work.LinnikAreas

open DirichletCharacter Complex MeasureTheory Filter Asymptotics
open scoped BigOperators

noncomputable section

variable {q : ℕ} [NeZero q]

/-- `λ` is the Dirichlet convolution of the constant sequence `1` with `χ`:
`λ(n) = Σ_{d ∣ n} χ(d)`. -/
lemma lam_eq_convolution (χ : DirichletCharacter ℂ q) :
    ∀ {n : ℕ}, n ≠ 0 →
      lam χ n = (LSeries.convolution (fun m : ℕ => χ (m : ZMod q)) (1 : ℕ → ℂ)) n := by
  intro n _
  have h : (LSeries.convolution (fun m : ℕ => χ (m : ZMod q)) (1 : ℕ → ℂ)) n
      = ∑ p ∈ n.divisorsAntidiagonal, χ (p.1 : ZMod q) := by
    rw [LSeries.convolution_def]
    simp
  rw [lam, h, Nat.sum_divisorsAntidiagonal (fun a _ => χ (a : ZMod q))]

/-- The Dirichlet series `Σ λ(n) n^{-s}` converges absolutely for `Re s > 1`
(as the convolution of the two convergent series `ζ(s)` and `L(s,χ)`). -/
lemma LSeriesSummable_lam (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => lam χ n) s := by
  have hf : LSeriesSummable (fun m : ℕ => χ (m : ZMod q)) s := χ.LSeriesSummable_of_one_lt_re hs
  have hg : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  exact (LSeriesSummable_congr s (f := fun n : ℕ => lam χ n)
    (g := LSeries.convolution (fun m : ℕ => χ (m : ZMod q)) (1 : ℕ → ℂ))
    (fun {n} hn => lam_eq_convolution χ hn)).mpr (hf.convolution hg)

/-- For `Re s > 1` the Dirichlet series of `λ` equals `ζ(s)L(s,χ)`. -/
lemma LSeries_lam (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => lam χ n) s = riemannZeta s * LFunction χ s := by
  have hf : LSeriesSummable (fun m : ℕ => χ (m : ZMod q)) s := χ.LSeriesSummable_of_one_lt_re hs
  have hg : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  rw [LSeries_congr (f := fun n : ℕ => lam χ n)
        (g := LSeries.convolution (fun m : ℕ => χ (m : ZMod q)) (1 : ℕ → ℂ))
        (fun {n} hn => lam_eq_convolution χ hn) s]
  rw [LSeries_convolution' hf hg]
  rw [← LFunction_eq_LSeries χ hs, LSeries_one_eq_riemannZeta hs]
  ring

/-- The elementary integral `∫_1^∞ x^{-s} dx = 1/(s-1)` for `Re s > 1`. -/
lemma integral_Ioi_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s)) = 1 / (s - 1) := by
  have ha : (-s).re < -1 := by simp only [Complex.neg_re]; linarith
  have h := integral_Ioi_cpow_of_lt (a := -s) ha (c := 1) (by norm_num)
  rw [h, show (((1 : ℝ)) : ℂ) = 1 by norm_num, Complex.one_cpow]
  have h1 : (-s + 1) = (1 - s) := by ring
  rw [h1]
  have hsne : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hA : (1 - s) ≠ 0 := by intro h; exact hsne (by linear_combination -h)
  have hB : (s - 1) ≠ 0 := sub_ne_zero.mpr hsne
  rw [show (-1 : ℂ) / (1 - s) = 1 / (s - 1) by
    rw [div_eq_div_iff hA hB]; ring]

/-- Pointwise splitting of the integrand: for `x > 0`,
`E(x)·x^{-s-1} = A(x)·x^{-s-1} - L(1,χ)·x^{-s}`. -/
lemma Efun_mul_cpow (χ : DirichletCharacter ℂ q) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Efun χ x * (x : ℂ) ^ (-(s + 1))
      = Asum χ x * (x : ℂ) ^ (-(s + 1)) - LFunction χ 1 * (x : ℂ) ^ (-s) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpow : (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
    have h := Complex.cpow_add (x := (x : ℂ)) (1 : ℂ) (-(s + 1)) hxne
    rw [show (1 : ℂ) + (-(s + 1)) = -s by ring, Complex.cpow_one] at h
    exact h.symm
  rw [Efun_apply]
  calc (Asum χ x - (x : ℂ) * LFunction χ 1) * (x : ℂ) ^ (-(s + 1))
      = Asum χ x * (x : ℂ) ^ (-(s + 1))
          - (x : ℂ) * LFunction χ 1 * (x : ℂ) ^ (-(s + 1)) := by ring
    _ = Asum χ x * (x : ℂ) ^ (-(s + 1))
          - LFunction χ 1 * ((x : ℂ) * (x : ℂ) ^ (-(s + 1))) := by ring
    _ = Asum χ x * (x : ℂ) ^ (-(s + 1)) - LFunction χ 1 * (x : ℂ) ^ (-s) := by rw [hpow]

theorem lamAbelIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {K : ℝ}
    (hE : ∀ x : ℝ, 1 ≤ x → ‖Work.LinnikAreas.Efun χ x‖ ≤ K * Real.sqrt x) {s : ℂ}
    (hs : 1 < s.re) :
    s * (∫ x in Set.Ioi (1:ℝ), Work.LinnikAreas.Efun χ x * (x:ℂ) ^ (-(s + 1)))
      = riemannZeta s * DirichletCharacter.LFunction χ s
        - s * DirichletCharacter.LFunction χ 1 / (s - 1) := by
  have hS : LSeriesSummable (fun n : ℕ => lam χ n) s := LSeriesSummable_lam χ hs
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, lam χ k)
      =O[Filter.atTop] fun n : ℕ => (n:ℝ)^(1:ℝ) := AsumPartialIsBigO χ hE
  have hInt : LSeries (fun n : ℕ => lam χ n) s
      = s * ∫ t in Set.Ioi (1:ℝ), Asum χ t * (t:ℂ)^(-(s+1)) := by
    have h := LSeries_eq_mul_integral (fun n : ℕ => lam χ n) (show (0:ℝ) ≤ 1 by norm_num)
      hs hS hO
    simpa only [Asum_apply] using h
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith : (0:ℝ) < s.re)
  have hA : (∫ t in Set.Ioi (1:ℝ), Asum χ t * (t:ℂ)^(-(s+1)))
      = LSeries (fun n : ℕ => lam χ n) s / s := by
    rw [hInt, mul_div_cancel_left₀ _ hs0]
  have hf : IntegrableOn (fun t : ℝ => Asum χ t * (t:ℂ)^(-(s+1))) (Set.Ioi 1) :=
    AsumCPowIntegrable χ hE hs
  have hbase : IntegrableOn (fun t : ℝ => (t:ℂ)^(-s)) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (a := -s) (by simp only [Complex.neg_re]; linarith)
      (c := 1) (by norm_num)
  have hg : IntegrableOn (fun t : ℝ => LFunction χ 1 * (t:ℂ)^(-s)) (Set.Ioi 1) :=
    hbase.const_mul _
  have hI0 : (∫ t in Set.Ioi (1:ℝ), (t:ℂ)^(-s)) = 1/(s-1) := integral_Ioi_cpow_neg hs
  have hdecomp : (∫ x in Set.Ioi (1:ℝ), Efun χ x * (x:ℂ)^(-(s+1)))
      = (∫ x in Set.Ioi (1:ℝ), Asum χ x * (x:ℂ)^(-(s+1)))
        - LFunction χ 1 * (∫ x in Set.Ioi (1:ℝ), (x:ℂ)^(-s)) := by
    rw [setIntegral_congr_fun (s := Set.Ioi 1) measurableSet_Ioi
        (fun x hx => Efun_mul_cpow χ s (lt_trans zero_lt_one (Set.mem_Ioi.mp hx)))]
    rw [integral_sub hf hg, integral_const_mul]
  rw [hdecomp, hI0, hA, LSeries_lam χ hs]
  field_simp
  try ring

end

end Work.LinnikAreas
