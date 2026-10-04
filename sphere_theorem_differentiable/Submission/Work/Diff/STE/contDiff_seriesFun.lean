import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `contDiff_seriesFun`: smoothness of a rapidly decaying Fourier series

If the coefficient family `c : (ι → ℤ) → ℂ` decays faster than every polynomial in the
weight `⟨k⟩² = wt k = 1 + Σ kᵢ²`, then the series
`seriesFun c x = ∑'_k c k * exp (2π i k·x)`
is `C^∞` on the torus `ι → ℝ`.

The proof is the standard Weierstrass M-test for smooth series (`contDiff_tsum`): we bound
the `k`-th iterated derivative of each character `fourierExp m` by `(2π Σᵢ |mᵢ|)^k`, and
`Σᵢ |mᵢ| ≤ card ι * wt m`, so the resulting majorant is summable by hypothesis.

The sub-lemma driving the bound is that `Complex.exp` has iterated derivatives
`iteratedFDeriv ℝ k Complex.exp z = exp z • (∏ ·)` (product of the arguments), hence norm
`‖exp z‖`, which combined with the chain rule and `‖charLin m‖ ≤ 2π Σᵢ |mᵢ|` gives the
estimate.
-/

noncomputable section

open ContinuousMultilinearMap ContinuousLinearMap

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real-linear functional `x ↦ 2πi ∑_j m_j x_j`, whose exponential is the Fourier
character `fourierExp m`. -/
def charLin (m : ι → ℤ) : (ι → ℝ) →L[ℝ] ℂ :=
  ∑ j : ι, (2 * Real.pi * Complex.I * (m j : ℂ)) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j))

/-- The defining formula of `charLin`. -/
lemma charLin_apply (m : ι → ℤ) (x : ι → ℝ) :
    charLin m x = 2 * Real.pi * Complex.I * ∑ j, (m j : ℂ) * (x j : ℂ) := by
  simp only [charLin, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `fourierExp m` is the exponential of the linear functional `charLin m`. -/
lemma fourierExp_eq_exp_charLin (m : ι → ℤ) :
    fourierExp m = fun y => Complex.exp (charLin m y) := by
  funext y
  rw [charLin_apply]
  rfl

/-- Derivative of `y ↦ Complex.exp y • P` for a fixed multilinear map `P`. -/
lemma fderiv_exp_smul (k : ℕ) (P : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ) (z : ℂ) :
    fderiv ℝ (fun y : ℂ => Complex.exp y • P) z
      = (((1 : ℂ →L[ℝ] ℂ).smulRight P).comp ((Complex.exp z) • (1 : ℂ →L[ℝ] ℂ))) := by
  have h := (ContinuousLinearMap.hasFDerivAt (((1 : ℂ →L[ℝ] ℂ).smulRight P))).comp z
    (Complex.hasStrictFDerivAt_exp_real z).hasFDerivAt
  have h2 : (fun y : ℂ => Complex.exp y • P) =
      ⇑(((1 : ℂ →L[ℝ] ℂ).smulRight P)) ∘ Complex.exp := by
    funext y; simp [ContinuousLinearMap.smulRight_apply]
  exact (h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq h2)).fderiv

/-- The `k`-th iterated derivative of `Complex.exp` at `z` is `exp z` times the product
multilinear map `(v₀, …, v_{k-1}) ↦ v₀ ⋯ v_{k-1}`. -/
lemma exp_iteratedFDeriv (k : ℕ) (z : ℂ) :
    iteratedFDeriv ℝ k Complex.exp z
      = (Complex.exp z) • (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ) := by
  induction k generalizing z with
  | zero =>
    ext v
    simp [ContinuousMultilinearMap.mkPiAlgebra_apply]
  | succ k ih =>
    ext v
    rw [iteratedFDeriv_succ_apply_left]
    rw [show iteratedFDeriv ℝ k Complex.exp =
        (fun y : ℂ => (Complex.exp y) • (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ))
        from funext ih]
    rw [fderiv_exp_smul]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, ContinuousMultilinearMap.mkPiAlgebra_apply, one_apply_eq_self,
      smul_eq_mul, Fin.prod_univ_succ]
    rw [mul_assoc]
    rfl

/-- The norm of the `k`-th iterated derivative of `Complex.exp` at `z` is `‖exp z‖`. -/
lemma norm_exp_iteratedFDeriv (k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k Complex.exp z‖ = ‖Complex.exp z‖ := by
  rw [exp_iteratedFDeriv, norm_smul, ContinuousMultilinearMap.norm_mkPiAlgebra, mul_one]

/-- `‖↑r * I‖ = |r|` for a real number `r`. -/
lemma norm_ofReal_mul_I (r : ℝ) : ‖((r : ℂ)) * Complex.I‖ = |r| := by simp

/-- `Complex.exp (charLin m x)` has modulus one: its argument is purely imaginary. -/
lemma norm_exp_charLin (m : ι → ℤ) (x : ι → ℝ) :
    ‖Complex.exp (charLin m x)‖ = 1 := by
  rw [charLin_apply]
  have h : 2 * (Real.pi : ℂ) * Complex.I * ∑ j, (m j : ℂ) * (x j : ℂ)
      = ((2 * Real.pi * ∑ j, ((m j : ℝ) * x j) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The operator norm of the linear functional `charLin m` is at most `2π Σᵢ |mᵢ|`. -/
lemma norm_charLin_le (m : ι → ℤ) :
    ‖charLin m‖ ≤ 2 * Real.pi * ∑ i, |(m i : ℝ)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  rw [charLin_apply]
  have h1 : ‖2 * (Real.pi : ℂ) * Complex.I * ∑ j, (m j : ℂ) * (x j : ℂ)‖
      = 2 * Real.pi * |∑ j, (m j : ℝ) * x j| := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ∑ j, (m j : ℂ) * (x j : ℂ)
        = (((2 * Real.pi * (∑ j, (m j : ℝ) * x j) : ℝ)) : ℂ) * Complex.I by
      push_cast; ring]
    rw [norm_ofReal_mul_I, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    ring
  rw [h1]
  have h2 : |∑ j, (m j : ℝ) * x j| ≤ (∑ j, |(m j : ℝ)|) * ‖x‖ := by
    calc |∑ j, (m j : ℝ) * x j| ≤ ∑ j, |(m j : ℝ) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |(m j : ℝ)| * |x j| := by simp [abs_mul]
      _ ≤ ∑ j, |(m j : ℝ)| * ‖x‖ := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have hx : |x j| ≤ ‖x‖ := by simpa using norm_le_pi_norm x j
          exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      _ = (∑ j, |(m j : ℝ)|) * ‖x‖ := by rw [Finset.sum_mul]
  calc 2 * Real.pi * |∑ j, (m j : ℝ) * x j|
      ≤ 2 * Real.pi * ((∑ j, |(m j : ℝ)|) * ‖x‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 * Real.pi * ∑ j, |(m j : ℝ)|) * ‖x‖ := by ring

/-- Bound on the iterated derivatives of the Fourier character `fourierExp m`. -/
lemma norm_iteratedFDeriv_fourierExp_le (m : ι → ℤ) (k : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ k (fourierExp m) x‖ ≤ (2 * Real.pi * ∑ i, |(m i : ℝ)|) ^ k := by
  have hf : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_right (charLin m) hf x
    (i := k) (by simp)
  have hfun : fourierExp m = Complex.exp ∘ ⇑(charLin m) := fourierExp_eq_exp_charLin m
  rw [hfun, hcomp]
  calc ‖(iteratedFDeriv ℝ k Complex.exp (charLin m x)).compContinuousLinearMap
        (fun _ => charLin m)‖
      ≤ ‖iteratedFDeriv ℝ k Complex.exp (charLin m x)‖ *
          ∏ _ : Fin k, ‖charLin m‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖charLin m‖ ^ k := by
        rw [norm_exp_iteratedFDeriv, norm_exp_charLin]
        simp
    _ ≤ (2 * Real.pi * ∑ i, |(m i : ℝ)|) ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_charLin_le m) k

/-- `Σᵢ |mᵢ| ≤ card ι * wt m`. -/
lemma sum_abs_le_card_mul_wt (m : ι → ℤ) :
    ∑ i, |(m i : ℝ)| ≤ (Fintype.card ι : ℝ) * wt m := by
  have h : ∀ i, |(m i : ℝ)| ≤ wt m := by
    intro i
    have h1 : ((m i : ℤ) : ℝ) ^ 2 ≤ ∑ j, ((m j : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun j => ((m j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    simp only [wt]
    nlinarith [abs_nonneg ((m i : ℝ)), sq_abs ((m i : ℝ))]
  calc ∑ i, |(m i : ℝ)| ≤ ∑ i, wt m := Finset.sum_le_sum (fun i _ => h i)
    _ = (Fintype.card ι : ℝ) * wt m := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The Fourier character is smooth. -/
lemma contDiff_fourierExp_top (m : ι → ℤ) : ContDiff ℝ ⊤ (fourierExp m) := by
  rw [fourierExp_eq_exp_charLin]
  exact Complex.contDiff_exp.comp (charLin m).contDiff

theorem contDiff_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι] (c : (ι → ℤ) → ℂ)
    (h : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.seriesFun c) := by
  rw [show seriesFun c = fun x => ∑' m : ι → ℤ, c m * fourierExp m x from rfl]
  refine contDiff_tsum (𝕜 := ℝ) (E := ι → ℝ) (F := ℂ) (N := ⊤)
    (f := fun m x => c m * fourierExp m x)
    (v := fun k m => (2 * Real.pi * (Fintype.card ι : ℝ)) ^ k * (wt m) ^ k * ‖c m‖) ?_ ?_ ?_
  · intro m
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => c m * fourierExp m x) :=
      contDiff_const.mul ((contDiff_fourierExp_top m).of_le le_top)
    exact h
  · intro k _
    have := (h k).mul_left ((2 * Real.pi * (Fintype.card ι : ℝ)) ^ k)
    simpa [mul_assoc] using this
  · intro k m x _
    have hsmul : iteratedFDeriv ℝ k (fun x => c m • fourierExp m x) x
        = c m • iteratedFDeriv ℝ k (fourierExp m) x :=
      iteratedFDeriv_const_smul_apply'
        ((contDiff_fourierExp_top m).contDiffAt.of_le le_top)
    have h1 : iteratedFDeriv ℝ k (fun x => c m * fourierExp m x) x
        = c m • iteratedFDeriv ℝ k (fourierExp m) x := hsmul
    rw [h1, norm_smul]
    calc ‖c m‖ * ‖iteratedFDeriv ℝ k (fourierExp m) x‖
        ≤ ‖c m‖ * (2 * Real.pi * ∑ i, |(m i : ℝ)|) ^ k :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_fourierExp_le m k x)
            (norm_nonneg _)
      _ ≤ ‖c m‖ * ((2 * Real.pi * (Fintype.card ι : ℝ)) * wt m) ^ k := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k)
            (norm_nonneg _)
          nlinarith [sum_abs_le_card_mul_wt m, Real.pi_pos]
      _ = (2 * Real.pi * (Fintype.card ι : ℝ)) ^ k * (wt m) ^ k * ‖c m‖ := by
          rw [mul_pow]; ring

end Work.Diff.STE
