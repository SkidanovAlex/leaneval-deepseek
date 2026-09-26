import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.SummableExpansionTerms
import Submission.Work.FunctionalEquations.DirichletExpansion
import Submission.Work.FunctionalEquations.PeriodicIntTranslate
import Submission.Work.FunctionalEquations.EqZeroOfTsumExp

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

/-- The order isomorphism `ℕ ≃ {m : ℕ // 1 ≤ m}`, `k ↦ k + 1`. -/
private def natEquivIciOneSub : ℕ ≃ Set.Ici (1 : ℕ) where
  toFun k := ⟨k + 1, Nat.le_add_left 1 k⟩
  invFun m := m.1 - 1
  left_inv k := by simp
  right_inv m := by ext; simp [Nat.sub_add_cancel m.2]

/-- The Dirichlet kernel is periodic of period `1` in `τ`. -/
private lemma dirichletTerm_add_one_sub (m : ℕ) (τ : ℂ) :
    dirichletTerm m (τ + 1) = dirichletTerm m τ := by
  rw [dirichletTerm, dirichletTerm]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (τ + 1)
      = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * τ
        + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]

/-- **A single Dirichlet coefficient is controlled by the sup norm of the series on any
interval of length `1`.**  If `c` grows at most polynomially in `m`, and the Dirichlet
series `∑_m c_m e^{2π i m (t + i y)}` is bounded by `e^{-2π y} M` on some interval
`[A, A+1]` of length one, then `‖c_1‖ ≤ M`.

The proof extracts the first Fourier coefficient by integrating against the character
`e^{-2π i (t + i y)}` over `(0,1)` (the hypothesis being transported to `(0,1)` by the
`1`-periodicity of the series). -/
theorem DirichletCoeffOneNormLe {c : Set.Ici (1:ℕ) → ℂ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hc : ∀ m : Set.Ici (1:ℕ), ‖c m‖ ≤ C * ((m.1:ℝ) + 1) ^ N)
    {y M A : ℝ} (hy : 0 < y)
    (hbd : ∀ t : ℝ, t ∈ Set.Icc A (A + 1) →
      ‖∑' m : Set.Ici (1:ℕ), c m * Work.FE.dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ Real.exp (-(2 * Real.pi * y)) * M) :
    ‖c ⟨1, by simp⟩‖ ≤ M := by
  -- The Dirichlet series as a function of `τ` and on the line `Im = y`.
  let g : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1 : ℕ), c m * dirichletTerm m.1 τ
  let φ : ℝ → ℂ := fun t => g ((t : ℂ) + (y : ℂ) * Complex.I)
  let c' : ℕ → ℂ := fun k => c ⟨k + 1, Nat.le_add_left 1 k⟩
  -- Absolute convergence on every horizontal line `Im = y`.
  have hsumm : ∀ t : ℝ, Summable (fun m : Set.Ici (1 : ℕ) =>
      c m * dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I)) := by
    intro t
    refine summable_mul_dirichletTerm hC hc _ ?_
    have hτ : ((t : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    rw [hτ]; exact hy
  -- `g` is periodic of period `1`.
  have hgper : ∀ τ : ℂ, 0 < τ.im → g (τ + 1) = g τ := by
    intro τ _
    exact tsum_congr fun m => by rw [dirichletTerm_add_one_sub]
  have hgint := PeriodicIntTranslate hgper
  -- Pointwise bound for every real `t`, transported to the strip `[A, A+1]`.
  have hbound_all : ∀ t : ℝ, ‖φ t‖ ≤ Real.exp (-(2 * Real.pi * y)) * M := by
    intro t
    set k : ℤ := ⌈A - t⌉ with hk
    have hk1 : A ≤ t + (k : ℝ) := by
      have h := Int.le_ceil (A - t); rw [← hk] at h; linarith
    have hk2 : t + (k : ℝ) ≤ A + 1 := by
      have h := Int.ceil_lt_add_one (A - t); rw [← hk] at h; linarith
    have hb : ‖g (((t + (k : ℝ) : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ Real.exp (-(2 * Real.pi * y)) * M := hbd (t + (k : ℝ)) ⟨hk1, hk2⟩
    have hshift : g (((t + (k : ℝ) : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        = g ((t : ℂ) + (y : ℂ) * Complex.I) := by
      have hcast : ((t + (k : ℝ) : ℝ) : ℂ) = (t : ℂ) + (k : ℂ) := by push_cast; ring
      rw [hcast, show (t : ℂ) + (k : ℂ) + (y : ℂ) * Complex.I
          = ((t : ℂ) + (y : ℂ) * Complex.I) + (k : ℂ) from by ring]
      exact hgint k ((t : ℂ) + (y : ℂ) * Complex.I)
        (by rw [show ((t : ℂ) + (y : ℂ) * Complex.I).im = y by simp]; exact hy)
    rw [hshift] at hb
    exact hb
  -- The `ℕ`-indexed (`k ↦` frequency `k+1`) form of the expansion.
  have hHS : ∀ t : ℝ, HasSum (fun k : ℕ =>
      c' k * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1)
        * ((t : ℂ) + (y : ℂ) * Complex.I))) (φ t) := by
    intro t
    have hbase : HasSum (fun m : Set.Ici (1 : ℕ) =>
        c m * dirichletTerm m.1 ((t : ℂ) + (y : ℂ) * Complex.I)) (φ t) :=
      (hsumm t).hasSum
    have hre := (Equiv.hasSum_iff natEquivIciOneSub).mpr hbase
    refine hre.congr_fun ?_
    intro k
    simp only [Function.comp_apply, natEquivIciOneSub, Equiv.coe_fn_mk, c', dirichletTerm]
    congr 2
    push_cast
    ring
  -- Summability of the coefficient norms, in the form required by `CoeffIntegral`.
  have hs : Summable fun k : ℕ =>
      ‖c' k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y)) := by
    have hsh : Summable (fun k : ℕ =>
        c' k * dirichletTerm (k + 1) ((0 : ℂ) + (y : ℂ) * Complex.I)) := by
      have hbase : HasSum (fun m : Set.Ici (1 : ℕ) =>
          c m * dirichletTerm m.1 ((0 : ℂ) + (y : ℂ) * Complex.I)) (φ 0) := (hsumm 0).hasSum
      have hre := (Equiv.hasSum_iff natEquivIciOneSub).mpr hbase
      refine hre.summable.congr ?_
      intro k
      simp only [Function.comp_apply, natEquivIciOneSub, Equiv.coe_fn_mk, c']
    refine hsh.norm.congr ?_
    intro k
    rw [norm_mul, normDirichletTermAux]
    have harg : -(2 * Real.pi * (((k + 1 : ℕ) : ℝ)) * ((0 : ℂ) + (y : ℂ) * Complex.I).im)
        = -(2 * Real.pi * ((k : ℝ) + 1) * y) := by
      simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, zero_add, Nat.cast_add, Nat.cast_one]
      ring
    rw [harg]
  -- Extraction of the first coefficient by integration.
  have hkey : c' 0 = ∫ t in (0 : ℝ)..1, φ t * Complex.exp
      (-(2 * (Real.pi : ℂ) * Complex.I * ((0 : ℂ) + 1)
        * ((t : ℂ) + (y : ℂ) * Complex.I))) := by
    have h := CoeffIntegral (c := c') (φ := φ) hy hHS hs 0
    simpa using h
  -- The integrand is bounded by `M`.
  have hle : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖φ x * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((0 : ℂ) + 1)
        * ((x : ℂ) + (y : ℂ) * Complex.I)))‖ ≤ M := by
    intro x _
    rw [norm_mul, Complex.norm_exp]
    have hB : (2 * (Real.pi : ℂ) * Complex.I * ((0 : ℂ) + 1)
        * ((x : ℂ) + (y : ℂ) * Complex.I)).re = -(2 * Real.pi * y) := by
      simp only [zero_add, mul_one, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im]
      norm_num
    rw [Complex.neg_re, hB]
    calc ‖φ x‖ * Real.exp (- -(2 * Real.pi * y))
        ≤ (Real.exp (-(2 * Real.pi * y)) * M) * Real.exp (- -(2 * Real.pi * y)) :=
          mul_le_mul_of_nonneg_right (hbound_all x) (Real.exp_pos _).le
      _ = M := by
          have hexp : Real.exp (-(2 * Real.pi * y)) * Real.exp (- -(2 * Real.pi * y)) = 1 := by
            rw [← Real.exp_add]; ring_nf; simp
          rw [mul_assoc]
          calc Real.exp (-(2 * Real.pi * y)) * (M * Real.exp (- -(2 * Real.pi * y)))
              = M * (Real.exp (-(2 * Real.pi * y)) * Real.exp (- -(2 * Real.pi * y))) := by ring
            _ = M * 1 := by rw [hexp]
            _ = M := mul_one M
  have hnorm : ‖c' 0‖ ≤ M := by
    rw [hkey]
    have := intervalIntegral.norm_integral_le_of_norm_le_const hle
    simpa using this
  -- `c' 0` is `c 1`.
  simpa only [c'] using hnorm

end

end Work.FunctionalEquations
