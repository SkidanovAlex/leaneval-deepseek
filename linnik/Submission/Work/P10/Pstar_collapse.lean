import Mathlib
import Submission.Work.ZeroFreeTables.P10.P3star_nonpos
import Submission.Work.ZeroFreeTables.P3.DefsL

namespace Work.P10

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

/-- Canonical form of the ten `P₃`-values of the collapse:
`Re P₃((a+λ₁)/(A+it))`, with the numerator written at type `ℂ`. -/
private def pval (a lam1 : ℝ) (A t : ℝ) : ℝ :=
  (Work.ZeroFreeTables.P3
    (((a : ℂ) + (lam1 : ℂ)) / (((A : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I))).re

/-- `Re P₃((a+λ₁)/(A+it))` is even in `t` (it only depends on `t ^ 2`). -/
private lemma pval_even (a lam1 A t : ℝ) (hA : 0 < A) :
    pval a lam1 A (-t) = pval a lam1 A t := by
  unfold pval
  rw [show (((a : ℂ) + (lam1 : ℂ)) / (((A : ℝ) : ℂ) + (((-t) : ℝ) : ℂ) * Complex.I))
        = ((↑(a + lam1) : ℂ) / (((A : ℝ) : ℂ) + (((-t) : ℝ) : ℂ) * Complex.I)) by
        push_cast; ring,
      show (((a : ℂ) + (lam1 : ℂ)) / (((A : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I))
        = ((↑(a + lam1) : ℂ) / (((A : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I)) by
        push_cast; ring]
  rw [Work.ZeroFreeTables.P10.P3_re_at A (a + lam1) (-t) hA,
      Work.ZeroFreeTables.P10.P3_re_at A (a + lam1) t hA]
  ring

/-- The `P₃star` bracket of `P3star_nonpos`, in the canonical `pval`-form. -/
private lemma pval_bracket {a lam1 lam2 lam3 t : ℝ} (ha : 0 < a) (hlam1 : 0 ≤ lam1)
    (h12 : lam1 ≤ lam2) (h23 : lam2 ≤ lam3)
    (hside : 1 / a ^ 3 ≤ 1 / (a + lam1) ^ 3 + 1 / (a + lam2) ^ 3 + 1 / (a + lam3) ^ 3) :
    pval a lam1 a t - pval a lam1 (a + lam1) t - pval a lam1 (a + lam2) t
      - pval a lam1 (a + lam3) t ≤ 0 := by
  have h := Work.ZeroFreeTables.P10.P3star_nonpos (a := a) (lam₁ := lam1) (lam₂ := lam2)
    (lam₃ := lam3) (t := t) ha hlam1 h12 h23 hside
  simpa only [pval, Complex.sub_re] using h

theorem Pstar_collapse {q : ℕ} [NeZero q] (chi1 chi2 chi3 : DirichletCharacter ℂ q)
    (rho1 rho2 rho3 : ℂ)
    {a lam1 lam2 lam3 δ L e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 eS : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hL : 0 < L) (hlam1 : 0 ≤ lam1) (h12 : lam1 ≤ lam2)
    (h23 : lam2 ≤ lam3) (hγ1 : rho1.im = 0)
    (hsq1 : chi1 ^ 2 = 1) (hsq2 : chi2 ^ 2 = 1) (hsq3 : chi3 ^ 2 = 1)
    (hprod : chi1 * chi2 * chi3 = 1)
    (hside : 1 / a ^ 3 ≤ 1 / (a + lam1) ^ 3 + 1 / (a + lam2) ^ 3 + 1 / (a + lam3) ^ 3)
    (he7 : 0 ≤ e7) (he8 : 0 ≤ e8) (he9 : 0 ≤ e9) (he10 : 0 ≤ e10)
    (heS : 24 / (δ * L) + (1 / 2) * (e1 + e2 + e3 + e4 + e5 + e6) + (e7 + e8 + e9 + e10) ≤ eS)
    (hp1 : Work.ZeroFreeTables.SigmaP3L q L (chi1 * chi2) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho2.im) : ℂ) * Complex.I)) a lam1 ≤ -( Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam3 : ℝ) : ℂ) + (((rho2.im - rho3.im) * L) : ℂ) * Complex.I))).re + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e1))
    (hp2 : Work.ZeroFreeTables.SigmaP3L q L (chi1 * chi2⁻¹) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im - rho2.im) : ℂ) * Complex.I)) a lam1 ≤ -( Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam3 : ℝ) : ℂ) + ((-(rho2.im + rho3.im) * L) : ℂ) * Complex.I))).re + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e2))
    (hp3 : Work.ZeroFreeTables.SigmaP3L q L (chi1 * chi3) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho3.im) : ℂ) * Complex.I)) a lam1 ≤ -( Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam2 : ℝ) : ℂ) + (((rho3.im - rho2.im) * L) : ℂ) * Complex.I))).re + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e3))
    (hp4 : Work.ZeroFreeTables.SigmaP3L q L (chi1 * chi3⁻¹) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im - rho3.im) : ℂ) * Complex.I)) a lam1 ≤ -( Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam2 : ℝ) : ℂ) + ((-(rho2.im + rho3.im) * L) : ℂ) * Complex.I))).re + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e4))
    (hp5 : Work.ZeroFreeTables.SigmaP3L q L (chi2 * chi3) ((((1 + a / L : ℝ) : ℂ) + ((rho2.im + rho3.im) : ℂ) * Complex.I)) a lam1 ≤ -( Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam1 : ℝ) : ℂ) + (((rho2.im + rho3.im) * L) : ℂ) * Complex.I))).re + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e5))
    (hp6 : Work.ZeroFreeTables.SigmaP3L q L (chi2 * chi3⁻¹) ((((1 + a / L : ℝ) : ℂ) + ((rho2.im - rho3.im) : ℂ) * Complex.I)) a lam1 ≤ -( Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam1 : ℝ) : ℂ) + (((rho2.im - rho3.im) * L) : ℂ) * Complex.I))).re + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e6))
    (hq1 : Work.ZeroFreeTables.SigmaP3L q L (1) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho2.im + rho3.im) : ℂ) * Complex.I)) a lam1 ≤ ( Work.ZeroFreeTables.P3 ((a + lam1) / (((a : ℝ) : ℂ) + (((rho2.im + rho3.im) * L) : ℂ) * Complex.I))).re + (a + lam1) * (0 + e7))
    (hq2 : Work.ZeroFreeTables.SigmaP3L q L (1) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho2.im - rho3.im) : ℂ) * Complex.I)) a lam1 ≤ ( Work.ZeroFreeTables.P3 ((a + lam1) / (((a : ℝ) : ℂ) + (((rho2.im - rho3.im) * L) : ℂ) * Complex.I))).re + (a + lam1) * (0 + e8))
    (hq3 : Work.ZeroFreeTables.SigmaP3L q L (1) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im - rho2.im + rho3.im) : ℂ) * Complex.I)) a lam1 ≤ ( Work.ZeroFreeTables.P3 ((a + lam1) / (((a : ℝ) : ℂ) + (((rho3.im - rho2.im) * L) : ℂ) * Complex.I))).re + (a + lam1) * (0 + e9))
    (hq4 : Work.ZeroFreeTables.SigmaP3L q L (1) ((((1 + a / L : ℝ) : ℂ) + ((-rho1.im + rho2.im + rho3.im) : ℂ) * Complex.I)) a lam1 ≤ ( Work.ZeroFreeTables.P3 ((a + lam1) / (((a : ℝ) : ℂ) + (((rho2.im + rho3.im) * L) : ℂ) * Complex.I))).re + (a + lam1) * (0 + e10))
    : (1 / 2) * (Work.ZeroFreeTables.SigmaP3L q L (chi1 * chi2) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho2.im) : ℂ) * Complex.I)) a lam1 + Work.ZeroFreeTables.SigmaP3L q L (chi1 * chi2⁻¹) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im - rho2.im) : ℂ) * Complex.I)) a lam1 + Work.ZeroFreeTables.SigmaP3L q L (chi1 * chi3) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho3.im) : ℂ) * Complex.I)) a lam1 + Work.ZeroFreeTables.SigmaP3L q L (chi1 * chi3⁻¹) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im - rho3.im) : ℂ) * Complex.I)) a lam1 + Work.ZeroFreeTables.SigmaP3L q L (chi2 * chi3) ((((1 + a / L : ℝ) : ℂ) + ((rho2.im + rho3.im) : ℂ) * Complex.I)) a lam1 + Work.ZeroFreeTables.SigmaP3L q L (chi2 * chi3⁻¹) ((((1 + a / L : ℝ) : ℂ) + ((rho2.im - rho3.im) : ℂ) * Complex.I)) a lam1)
      + (1 / 4) * (Work.ZeroFreeTables.SigmaP3L q L (1) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho2.im + rho3.im) : ℂ) * Complex.I)) a lam1 + Work.ZeroFreeTables.SigmaP3L q L (1) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho2.im - rho3.im) : ℂ) * Complex.I)) a lam1 + Work.ZeroFreeTables.SigmaP3L q L (1) ((((1 + a / L : ℝ) : ℂ) + ((rho1.im - rho2.im + rho3.im) : ℂ) * Complex.I)) a lam1 + Work.ZeroFreeTables.SigmaP3L q L (1) ((((1 + a / L : ℝ) : ℂ) + ((-rho1.im + rho2.im + rho3.im) : ℂ) * Complex.I)) a lam1)
      ≤ (a + lam1) * (3 / 8 + eS) := by
  -- the ten `P₃`-values appearing in the hypotheses, as named reals
  set N1 : ℝ := (Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam3 : ℝ) : ℂ) + (((rho2.im - rho3.im) * L) : ℂ) * Complex.I))).re with hN1
  set N2 : ℝ := (Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam3 : ℝ) : ℂ) + ((-(rho2.im + rho3.im) * L) : ℂ) * Complex.I))).re with hN2
  set N3 : ℝ := (Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam2 : ℝ) : ℂ) + (((rho3.im - rho2.im) * L) : ℂ) * Complex.I))).re with hN3
  set N4 : ℝ := (Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam2 : ℝ) : ℂ) + ((-(rho2.im + rho3.im) * L) : ℂ) * Complex.I))).re with hN4
  set N5 : ℝ := (Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam1 : ℝ) : ℂ) + (((rho2.im + rho3.im) * L) : ℂ) * Complex.I))).re with hN5
  set N6 : ℝ := (Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam1 : ℝ) : ℂ) + (((rho2.im - rho3.im) * L) : ℂ) * Complex.I))).re with hN6
  set Q1 : ℝ := (Work.ZeroFreeTables.P3 ((a + lam1) / (((a : ℝ) : ℂ) + (((rho2.im + rho3.im) * L) : ℂ) * Complex.I))).re with hQ1
  set Q2 : ℝ := (Work.ZeroFreeTables.P3 ((a + lam1) / (((a : ℝ) : ℂ) + (((rho2.im - rho3.im) * L) : ℂ) * Complex.I))).re with hQ2
  set Q3 : ℝ := (Work.ZeroFreeTables.P3 ((a + lam1) / (((a : ℝ) : ℂ) + (((rho3.im - rho2.im) * L) : ℂ) * Complex.I))).re with hQ3
  -- each of them is a `pval` at one of two values of `t`
  have hN1G : N1 = pval a lam1 (a + lam3) ((rho2.im - rho3.im) * L) := by
    rw [hN1]
    rw [show (((a + lam3 : ℝ) : ℂ) + (((rho2.im - rho3.im) * L) : ℂ) * Complex.I)
          = (((a + lam3 : ℝ) : ℂ) + ((((rho2.im - rho3.im) * L) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    rfl
  have hN2G : N2 = pval a lam1 (a + lam3) ((rho2.im + rho3.im) * L) := by
    rw [hN2]
    rw [show (((a + lam3 : ℝ) : ℂ) + (((-(rho2.im + rho3.im)) * L) : ℂ) * Complex.I)
          = (((a + lam3 : ℝ) : ℂ) + (((-((rho2.im + rho3.im) * L)) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    exact pval_even a lam1 (a + lam3) ((rho2.im + rho3.im) * L) (by linarith)
  have hN3G : N3 = pval a lam1 (a + lam2) ((rho2.im - rho3.im) * L) := by
    rw [hN3]
    rw [show (((a + lam2 : ℝ) : ℂ) + (((rho3.im - rho2.im) * L) : ℂ) * Complex.I)
          = (((a + lam2 : ℝ) : ℂ) + (((-((rho2.im - rho3.im) * L)) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    exact pval_even a lam1 (a + lam2) ((rho2.im - rho3.im) * L) (by linarith)
  have hN4G : N4 = pval a lam1 (a + lam2) ((rho2.im + rho3.im) * L) := by
    rw [hN4]
    rw [show (((a + lam2 : ℝ) : ℂ) + (((-(rho2.im + rho3.im)) * L) : ℂ) * Complex.I)
          = (((a + lam2 : ℝ) : ℂ) + (((-((rho2.im + rho3.im) * L)) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    exact pval_even a lam1 (a + lam2) ((rho2.im + rho3.im) * L) (by linarith)
  have hN5G : N5 = pval a lam1 (a + lam1) ((rho2.im + rho3.im) * L) := by
    rw [hN5]
    rw [show (((a + lam1 : ℝ) : ℂ) + (((rho2.im + rho3.im) * L) : ℂ) * Complex.I)
          = (((a + lam1 : ℝ) : ℂ) + ((((rho2.im + rho3.im) * L) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    rfl
  have hN6G : N6 = pval a lam1 (a + lam1) ((rho2.im - rho3.im) * L) := by
    rw [hN6]
    rw [show (((a + lam1 : ℝ) : ℂ) + (((rho2.im - rho3.im) * L) : ℂ) * Complex.I)
          = (((a + lam1 : ℝ) : ℂ) + ((((rho2.im - rho3.im) * L) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    rfl
  have hQ1G : Q1 = pval a lam1 a ((rho2.im + rho3.im) * L) := by
    rw [hQ1]
    rw [show (((a : ℝ) : ℂ) + (((rho2.im + rho3.im) * L) : ℂ) * Complex.I)
          = (((a : ℝ) : ℂ) + ((((rho2.im + rho3.im) * L) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    rfl
  have hQ2G : Q2 = pval a lam1 a ((rho2.im - rho3.im) * L) := by
    rw [hQ2]
    rw [show (((a : ℝ) : ℂ) + (((rho2.im - rho3.im) * L) : ℂ) * Complex.I)
          = (((a : ℝ) : ℂ) + ((((rho2.im - rho3.im) * L) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    rfl
  have hQ3G : Q3 = pval a lam1 a ((rho2.im - rho3.im) * L) := by
    rw [hQ3]
    rw [show (((a : ℝ) : ℂ) + (((rho3.im - rho2.im) * L) : ℂ) * Complex.I)
          = (((a : ℝ) : ℂ) + (((-((rho2.im - rho3.im) * L)) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring]
    exact pval_even a lam1 a ((rho2.im - rho3.im) * L) ha
  -- the two `P₃star` brackets, at `t = (ρ₂-ρ₃)L` and `t = (ρ₂+ρ₃)L`
  have hb1 := pval_bracket (a := a) (lam1 := lam1) (lam2 := lam2) (lam3 := lam3)
    (t := (rho2.im - rho3.im) * L) ha hlam1 h12 h23 hside
  have hb2 := pval_bracket (a := a) (lam1 := lam1) (lam2 := lam2) (lam3 := lam3)
    (t := (rho2.im + rho3.im) * L) ha hlam1 h12 h23 hside
  -- the collapse of the ten `P₃`-values to a non-positive combination
  have hcomb : -(1/2 : ℝ) * (N1 + N2 + N3 + N4 + N5 + N6)
      + (1/4 : ℝ) * (Q1 + Q2 + Q3 + Q1) ≤ 0 := by
    rw [hN1G, hN2G, hN3G, hN4G, hN5G, hN6G, hQ1G, hQ2G, hQ3G]
    linarith [hb1, hb2]
  have hα : 0 < a + lam1 := by linarith
  have hα0 : (0 : ℝ) ≤ a + lam1 := le_of_lt hα
  -- replace the symbolic divisions `x / (δ * L)` by `x * (δ * L)⁻¹`, which `linarith`
  -- can combine (it refuses to identify `x / d` with `y / d`)
  have hδLdiv : ∀ x : ℝ, x / (δ * L) = x * (δ * L)⁻¹ := fun x => div_eq_mul_inv x (δ * L)
  rw [hδLdiv] at hp1 hp2 hp3 hp4 hp5 hp6 heS
  have hmult := mul_le_mul_of_nonneg_left heS hα0
  have htail : (a + lam1) * ((1/4 : ℝ) * (e7 + e8 + e9 + e10))
      ≤ (a + lam1) * (e7 + e8 + e9 + e10) :=
    mul_le_mul_of_nonneg_left (by linarith) hα0
  linarith [hp1, hp2, hp3, hp4, hp5, hp6, hq1, hq2, hq3, hq4, hcomb, hmult, htail]

end

end Work.P10
