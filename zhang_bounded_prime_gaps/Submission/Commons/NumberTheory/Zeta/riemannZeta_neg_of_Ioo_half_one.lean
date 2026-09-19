import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Commons.NumberTheory.DirichletCharacter.estermann_positivity

open Complex Finset
open scoped Topology BigOperators

namespace Commons.NumberTheory.Zeta

noncomputable section

/-- For `0 < a < 1` and `x > 0`, the secant slope of `y ↦ y ^ a` on `[x, x + 1]` is at least the
value of `deriv (y ↦ y ^ a)` at the right endpoint: `a * (x+1)^(a-1) ≤ (x+1)^a - x^a`. -/
private lemma rpow_secant_ge_right {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) :
    a * (x + 1) ^ (a - 1) ≤ (x + 1) ^ a - x ^ a := by
  have hlt : x < x + 1 := by linarith
  have hcont : ContinuousOn (fun y : ℝ => y ^ a) (Set.Icc x (x + 1)) :=
    (Real.continuous_rpow_const (le_of_lt ha)).continuousOn
  have hdiff : DifferentiableOn ℝ (fun y : ℝ => y ^ a) (Set.Ioo x (x + 1)) := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt (lt_trans hx hy.1)
    exact ((Real.hasDerivAt_rpow_const (p := a) (Or.inl hy0)).differentiableAt).differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun y : ℝ => y ^ a) hlt hcont hdiff
  have hcpos : 0 < c := lt_trans hx hc.1
  have hderiv : deriv (fun y : ℝ => y ^ a) c = a * c ^ (a - 1) :=
    (Real.hasDerivAt_rpow_const (x := c) (p := a) (Or.inl (ne_of_gt hcpos))).deriv
  have hcd' : a * c ^ (a - 1) = (x + 1) ^ a - x ^ a := by
    rw [← hderiv, hcd]
    norm_num
  have hmono : (x + 1) ^ (a - 1) ≤ c ^ (a - 1) :=
    Real.rpow_le_rpow_of_nonpos hcpos (le_of_lt hc.2) (by linarith)
  calc a * (x + 1) ^ (a - 1) ≤ a * c ^ (a - 1) :=
        mul_le_mul_of_nonneg_left hmono (le_of_lt ha)
    _ = (x + 1) ^ a - x ^ a := hcd'

/-- The `m`-th term of the Euler–Maclaurin tail for the Riemann zeta function (with `N = 1`),
specialised to a real argument `σ`; it is non-positive for `0 < σ < 1`. -/
private lemma emTailR_nonpos (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (m : ℕ) :
    ((((1 + m + 1 : ℕ) : ℝ) ^ (-σ)) -
        (((((1 + m + 1 : ℕ) : ℝ) ^ (1 - σ)) - (((1 + m : ℕ) : ℝ) ^ (1 - σ))) / (1 - σ))) ≤ 0 := by
  have ha : 0 < 1 - σ := by linarith
  have ha1 : 1 - σ < 1 := by linarith
  have hx0 : 0 < ((1 + m : ℕ) : ℝ) := by positivity
  have hkey := rpow_secant_ge_right (a := 1 - σ) (x := ((1 + m : ℕ) : ℝ)) ha ha1 hx0
  have hk : ((1 + m : ℕ) : ℝ) + 1 = ((1 + m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hk] at hkey
  have hexp : (1 - σ) - 1 = -σ := by ring
  rw [hexp] at hkey
  have hle : ((((1 + m + 1 : ℕ) : ℝ) ^ (-σ))) ≤
      (((((1 + m + 1 : ℕ) : ℝ) ^ (1 - σ)) - (((1 + m : ℕ) : ℝ) ^ (1 - σ))) / (1 - σ)) := by
    rw [le_div_iff₀ ha]
    linarith [hkey]
  linarith [hle]

/-- The complex Euler–Maclaurin tail term (with `N = 1`). -/
private def zetaTailC (σ : ℝ) (m : ℕ) : ℂ :=
  (((1 + m + 1 : ℕ) : ℂ) ^ (-(σ : ℂ))) -
    (((((1 + m + 1 : ℕ) : ℂ) ^ (1 - (σ : ℂ))) - (((1 + m : ℕ) : ℂ) ^ (1 - (σ : ℂ)))) /
      (1 - (σ : ℂ)))

/-- The real Euler–Maclaurin tail term (with `N = 1`). -/
private def zetaTailR (σ : ℝ) (m : ℕ) : ℝ :=
  (((1 + m + 1 : ℕ) : ℝ) ^ (-σ)) -
    (((((1 + m + 1 : ℕ) : ℝ) ^ (1 - σ)) - (((1 + m : ℕ) : ℝ) ^ (1 - σ))) / (1 - σ))

private lemma zetaTailC_eq (σ : ℝ) (m : ℕ) :
    zetaTailC σ m = ((zetaTailR σ m : ℝ) : ℂ) := by
  simp only [zetaTailC, zetaTailR]
  rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by simp,
      show (1 : ℂ) - (σ : ℂ) = ((1 - σ : ℝ) : ℂ) by simp]
  rw [← Complex.ofReal_natCast (1 + m + 1), ← Complex.ofReal_natCast (1 + m)]
  rw [← Complex.ofReal_cpow (show (0 : ℝ) ≤ ((1 + m + 1 : ℕ) : ℝ) by positivity) (-σ),
      ← Complex.ofReal_cpow (show (0 : ℝ) ≤ ((1 + m + 1 : ℕ) : ℝ) by positivity) (1 - σ),
      ← Complex.ofReal_cpow (show (0 : ℝ) ≤ ((1 + m : ℕ) : ℝ) by positivity) (1 - σ)]
  rw [← Complex.ofReal_sub, ← Complex.ofReal_div, ← Complex.ofReal_sub]

private lemma zetaTailR_nonpos (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (m : ℕ) :
    zetaTailR σ m ≤ 0 :=
  emTailR_nonpos σ hσ0 hσ1 m

theorem riemannZeta_neg_of_Ioo_half_one {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ < 1) :
    ∃ c : ℝ, c < 0 ∧ riemannZeta (σ : ℂ) = (c : ℂ) := by
  have hσ0 : 0 < σ := by linarith
  have hσ1 : σ ≠ 1 := by linarith
  have hs0 : 0 < ((σ : ℂ)).re := by simpa using hσ0
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h
    exact hσ1 (Complex.ofReal_injective (by simpa using h))
  -- summability of the complex tail
  have hsumC : Summable (zetaTailC σ) :=
    (emTerm_tsum_le 1 le_rfl (σ : ℂ) hs0 hs1).1
  -- corresponding real summability
  have hsumCast : Summable (fun m : ℕ => ((zetaTailR σ m : ℝ) : ℂ)) :=
    hsumC.congr (fun m => zetaTailC_eq σ m)
  have hsumR : Summable (zetaTailR σ) :=
    (Complex.summable_ofReal (f := zetaTailR σ)).mp hsumCast
  -- the tail is non-positive
  have hS : (∑' m : ℕ, zetaTailR σ m) ≤ 0 := by
    have h := Summable.tsum_le_tsum (f := zetaTailR σ) (g := fun _ : ℕ => (0 : ℝ))
      (fun m => zetaTailR_nonpos σ hσ0 h2 m) hsumR summable_zero
    simpa using h
  -- algebraic identity for the finite part
  have hT1 : 1 + (σ - 1)⁻¹ = -σ / (1 - σ) := by
    field_simp
    ring
  have hT1neg : -σ / (1 - σ) < 0 := by
    apply div_neg_of_neg_of_pos <;> linarith
  refine ⟨1 + (σ - 1)⁻¹ + ∑' m : ℕ, zetaTailR σ m, ?_, ?_⟩
  · have hle : 1 + (σ - 1)⁻¹ + ∑' m : ℕ, zetaTailR σ m ≤ -σ / (1 - σ) := by
      rw [hT1]
      linarith [hS]
    linarith
  · have h := zeta_eq_emN (s := (σ : ℂ)) hs0 hs1 1 le_rfl
    rw [h]
    change (∑ n ∈ Finset.Icc 1 1, (((n : ℕ) : ℂ) ^ (-(σ : ℂ)))) +
        ((((1 : ℕ) : ℂ) ^ (1 - (σ : ℂ))) / ((σ : ℂ) - 1)) +
        ∑' m : ℕ, zetaTailC σ m = ((1 + (σ - 1)⁻¹ + ∑' m : ℕ, zetaTailR σ m : ℝ) : ℂ)
    have hA : (∑ n ∈ Finset.Icc 1 1, (((n : ℕ) : ℂ) ^ (-(σ : ℂ)))) = (1 : ℂ) := by
      rw [Finset.Icc_self, Finset.sum_singleton]
      rw [show (((1 : ℕ) : ℂ)) = (1 : ℂ) by norm_num, Complex.one_cpow]
    have hB : ((((1 : ℕ) : ℂ) ^ (1 - (σ : ℂ))) / ((σ : ℂ) - 1)) = ((((σ - 1)⁻¹ : ℝ)) : ℂ) := by
      rw [show (((1 : ℕ) : ℂ)) = (1 : ℂ) by norm_num, Complex.one_cpow, one_div]
      rw [show ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) by simp]
      rw [← Complex.ofReal_inv]
    have hT : (∑' m : ℕ, zetaTailC σ m) = (((∑' m : ℕ, zetaTailR σ m : ℝ)) : ℂ) := by
      rw [Complex.ofReal_tsum (zetaTailR σ)]
      exact tsum_congr (fun m => zetaTailC_eq σ m)
    rw [hA, hB, hT]
    push_cast
    ring

end

end Commons.NumberTheory.Zeta
