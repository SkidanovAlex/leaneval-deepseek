import Submission.Work.FunctionalEquations.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations.BasisDelta
export _root_.Work.FunctionalEquations.BasisDelta (DirichletCoeffUnique)
end Work.FunctionalEquations.BasisDelta
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (SummableMulExpNeg)
end Work.FunctionalEquations
namespace Work.FunctionalEquations.BasisDelta
export _root_.Work.FunctionalEquations.BasisDelta (dirichletTerm_add_one)
end Work.FunctionalEquations.BasisDelta
namespace Work.FunctionalEquations.BasisDelta
export _root_.Work.FunctionalEquations.BasisDelta (PeriodicAddSmulUHP)
end Work.FunctionalEquations.BasisDelta
namespace Work.FunctionalEquations.BasisDelta
export _root_.Work.FunctionalEquations.BasisDelta (radialDeriv_one_of_nonneg)
end Work.FunctionalEquations.BasisDelta
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (FourierInversionRadial)
end Work.FunctionalEquations
namespace Work.FunctionalEquations.BasisDelta
export _root_.Work.FunctionalEquations.BasisDelta (two_pi_I_ne_zero)
end Work.FunctionalEquations.BasisDelta
namespace Work.FunctionalEquations.BasisDelta
export _root_.Work.FunctionalEquations.BasisDelta (rate_mul_bound)
end Work.FunctionalEquations.BasisDelta
namespace Work.FunctionalEquations.BasisDelta
export _root_.Work.FunctionalEquations.BasisDelta (rate_ne_zero)
end Work.FunctionalEquations.BasisDelta

/-!
# The samples of the interpolation basis are Kronecker deltas

For a solution `S` of the functional equations (with its coefficient families, paper
Section 8), the four samples of the `i`-th basis function are `1` at the sample `i` and
`0` at every other sample.

The proof first establishes the value/derivative pattern of the individual coefficient
families at the sample points (`BasisSampleValuesAt`, the paper's Section 8 computation):
for all `m, k ≥ 1`,
```
a_m(√(2k)) = δ_{mk},   ã_m(√(2k)) = 0,   b_m(√(2k)) = 0,   b̃_m(√(2k)) = 0,
D a_m(√(2k)) = 0,     D ã_m(√(2k)) = 0, D b_m(√(2k)) = δ_{mk}, D b̃_m(√(2k)) = 0.
```
It is obtained from the four Fourier expansions of `F` and `F̃`, evaluated at the sample
point and split into a `1`-periodic and a `τ`-linear part
(`Work.FunctionalEquations.BasisDelta.PeriodicAddSmulUHP`), followed by uniqueness of
Dirichlet coefficients (`Work.FunctionalEquations.BasisDelta.DirichletCoeffUnique`).

The passage from this pattern to the samples of the basis functions uses that the Fourier
transform exchanges `a_m ↔ ã_m` and `b_m ↔ b̃_m`, together with Fourier inversion for
radial Schwartz functions.
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap
open BasisDelta

/-- The series `∑ m, δ_{km} e^{2πimτ}` is the single term `e^{2πikτ}`. -/
private lemma tsum_delta_dirichletTerm (k : Set.Ici (1 : ℕ)) (τ : ℂ) :
    (∑' m : Set.Ici (1 : ℕ), (if k = m then (1 : ℂ) else 0) * dirichletTerm m.1 τ)
      = dirichletTerm k.1 τ := by
  rw [tsum_eq_single k (fun m hm => by rw [if_neg (Ne.symm hm), zero_mul])]
  simp

/-- The same for the delta sequence scaled by the rate `√(2 k)`. -/
private lemma tsum_rate_delta_dirichletTerm (k : Set.Ici (1 : ℕ)) (τ : ℂ) :
    (∑' m : Set.Ici (1 : ℕ), (if k = m then (rate k.1 : ℂ) else 0) * dirichletTerm m.1 τ)
      = (rate k.1 : ℂ) * dirichletTerm k.1 τ := by
  rw [tsum_eq_single k (fun m hm => by rw [if_neg (Ne.symm hm), zero_mul])]
  simp

/-- Uniqueness of Dirichlet coefficients, specialised to the line `Im τ = 1`. -/
private lemma dirichlet_extract {c d : Set.Ici (1 : ℕ) → ℂ}
    (hc : Summable fun m : Set.Ici (1 : ℕ) =>
      c m * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))))
    (hd : Summable fun m : Set.Ici (1 : ℕ) =>
      d m * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))))
    (h : ∀ t : ℝ,
      (∑' m : Set.Ici (1 : ℕ), c m * dirichletTerm m.1 ((t : ℂ) + (1 : ℂ) * Complex.I))
        = ∑' m : Set.Ici (1 : ℕ),
            d m * dirichletTerm m.1 ((t : ℂ) + (1 : ℂ) * Complex.I)) :
    ∀ m : Set.Ici (1 : ℕ), c m = d m :=
  DirichletCoeffUnique one_pos hc hd h

/-- Absolute convergence on the line `Im τ = 1` of a finitely supported sequence. -/
private lemma summable_delta (k : Set.Ici (1 : ℕ)) (a : ℂ) :
    Summable fun m : Set.Ici (1 : ℕ) =>
      (if k = m then a else 0) * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
  refine SummableMulExpNeg (C := ‖a‖) (N := 0) (norm_nonneg a) one_pos fun m => ?_
  by_cases h : k = m
  · rw [if_pos h, pow_zero, mul_one]
  · rw [if_neg h, norm_zero, pow_zero, mul_one]
    exact norm_nonneg a

/-- The zero sequence is summable against the exponential decay. -/
private lemma summable_zero_exp :
    Summable fun m : Set.Ici (1 : ℕ) =>
      (0 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
  simp

/-- **Paper Section 8: the values of the coefficient families at the sample points.**
For all `m, k ≥ 1`,
`a_m(√(2k)) = δ_{mk}`, `ã_m(√(2k)) = 0`, `b_m(√(2k)) = 0`, `b̃_m(√(2k)) = 0`,
`D a_m(√(2k)) = 0`, `D ã_m(√(2k)) = 0`, `D b_m(√(2k)) = δ_{mk}`, `D b̃_m(√(2k)) = 0`. -/
theorem BasisSampleValuesAt {n : ℕ} [NeZero n] (S : InterpolationSolution n)
    (k : Set.Ici (1 : ℕ)) :
    ∀ m : Set.Ici (1 : ℕ),
      (S.basis (m, 0)).1 (samplePoint (n := n) (k.1 : ℝ)) = (if k = m then 1 else 0) ∧
      (S.basis (m, 1)).1 (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      (S.basis (m, 2)).1 (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      (S.basis (m, 3)).1 (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      radialDeriv 1 (⇑(S.basis (m, 0)).1) (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      radialDeriv 1 (⇑(S.basis (m, 1)).1) (samplePoint (n := n) (k.1 : ℝ)) = 0 ∧
      radialDeriv 1 (⇑(S.basis (m, 2)).1) (samplePoint (n := n) (k.1 : ℝ))
        = (if k = m then 1 else 0) ∧
      radialDeriv 1 (⇑(S.basis (m, 3)).1) (samplePoint (n := n) (k.1 : ℝ)) = 0 := by
  classical
  let x : E n := samplePoint (n := n) (k.1 : ℝ)
  let a : Set.Ici (1 : ℕ) → ℂ := fun m => (S.basis (m, 0)).1 x
  let atr : Set.Ici (1 : ℕ) → ℂ := fun m => (S.basis (m, 1)).1 x
  let b : Set.Ici (1 : ℕ) → ℂ := fun m => (S.basis (m, 2)).1 x
  let bt : Set.Ici (1 : ℕ) → ℂ := fun m => (S.basis (m, 3)).1 x
  let da : Set.Ici (1 : ℕ) → ℂ := fun m => radialDeriv 1 (⇑(S.basis (m, 0)).1) x
  let dat : Set.Ici (1 : ℕ) → ℂ := fun m => radialDeriv 1 (⇑(S.basis (m, 1)).1) x
  let db : Set.Ici (1 : ℕ) → ℂ := fun m => radialDeriv 1 (⇑(S.basis (m, 2)).1) x
  let dbt : Set.Ici (1 : ℕ) → ℂ := fun m => radialDeriv 1 (⇑(S.basis (m, 3)).1) x
  let A : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1 : ℕ), a m * dirichletTerm m.1 τ
  let Atr : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1 : ℕ), atr m * dirichletTerm m.1 τ
  let B : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * b m * dirichletTerm m.1 τ
  let Bt : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * bt m * dirichletTerm m.1 τ
  let DA : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1 : ℕ), da m * dirichletTerm m.1 τ
  let DAt : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1 : ℕ), dat m * dirichletTerm m.1 τ
  let DB : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * db m * dirichletTerm m.1 τ
  let DBt : ℂ → ℂ := fun τ => ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * dbt m * dirichletTerm m.1 τ
  have hAper : ∀ τ : ℂ, A (τ + 1) = A τ := fun τ => by
    simp only [A]; exact tsum_congr fun m => by rw [dirichletTerm_add_one]
  have hAtrper : ∀ τ : ℂ, Atr (τ + 1) = Atr τ := fun τ => by
    simp only [Atr]; exact tsum_congr fun m => by rw [dirichletTerm_add_one]
  have hBper : ∀ τ : ℂ, B (τ + 1) = B τ := fun τ => by
    simp only [B]; exact tsum_congr fun m => by rw [dirichletTerm_add_one]
  have hBtper : ∀ τ : ℂ, Bt (τ + 1) = Bt τ := fun τ => by
    simp only [Bt]; exact tsum_congr fun m => by rw [dirichletTerm_add_one]
  have hDAper : ∀ τ : ℂ, DA (τ + 1) = DA τ := fun τ => by
    simp only [DA]; exact tsum_congr fun m => by rw [dirichletTerm_add_one]
  have hDAtper : ∀ τ : ℂ, DAt (τ + 1) = DAt τ := fun τ => by
    simp only [DAt]; exact tsum_congr fun m => by rw [dirichletTerm_add_one]
  have hDBper : ∀ τ : ℂ, DB (τ + 1) = DB τ := fun τ => by
    simp only [DB]; exact tsum_congr fun m => by rw [dirichletTerm_add_one]
  have hDBtper : ∀ τ : ℂ, DBt (τ + 1) = DBt τ := fun τ => by
    simp only [DBt]; exact tsum_congr fun m => by rw [dirichletTerm_add_one]
  -- The four functional equations at the sample point `x`, in `τ`-linear form.
  have hIdA : ∀ τ : ℂ, 0 < τ.im →
      A τ + τ * (2 * (Real.pi : ℂ) * Complex.I * B τ) = dirichletTerm k.1 τ + τ * 0 := by
    intro τ hτ
    have h1 := S.expansion_F τ x hτ
    have h2 := S.value_F k τ hτ
    calc A τ + τ * (2 * (Real.pi : ℂ) * Complex.I * B τ)
        = (∑' m : Set.Ici (1 : ℕ), (S.basis (m, 0)).1 x * dirichletTerm m.1 τ)
            + (2 * (Real.pi : ℂ) * Complex.I * τ)
              * (∑' m : Set.Ici (1 : ℕ),
                  (rate m.1 : ℂ) * (S.basis (m, 2)).1 x * dirichletTerm m.1 τ) := by
          simp only [A, B, a, b]; ring
      _ = S.F τ x := h1.symm
      _ = dirichletTerm k.1 τ := h2
      _ = dirichletTerm k.1 τ + τ * 0 := by ring
  have hIdAtr : ∀ τ : ℂ, 0 < τ.im →
      Atr τ + τ * (2 * (Real.pi : ℂ) * Complex.I * Bt τ) = (0 : ℂ) + τ * 0 := by
    intro τ hτ
    have h1 := S.expansion_Ftilde τ x hτ
    have h2 := S.value_Ftilde k τ hτ
    calc Atr τ + τ * (2 * (Real.pi : ℂ) * Complex.I * Bt τ)
        = (∑' m : Set.Ici (1 : ℕ), (S.basis (m, 1)).1 x * dirichletTerm m.1 τ)
            + (2 * (Real.pi : ℂ) * Complex.I * τ)
              * (∑' m : Set.Ici (1 : ℕ),
                  (rate m.1 : ℂ) * (S.basis (m, 3)).1 x * dirichletTerm m.1 τ) := by
          simp only [Atr, Bt, atr, bt]; ring
      _ = S.Ftilde τ x := h1.symm
      _ = 0 := h2
      _ = (0 : ℂ) + τ * 0 := by ring
  have hIdDA : ∀ τ : ℂ, 0 < τ.im →
      DA τ + τ * (2 * (Real.pi : ℂ) * Complex.I * DB τ)
        = (0 : ℂ)
          + τ * (2 * (Real.pi : ℂ) * Complex.I * ((rate k.1 : ℂ) * dirichletTerm k.1 τ)) := by
    intro τ hτ
    have h1 := S.expansion_F_radialDeriv 1 τ x hτ
    have h2 := S.value_radialDeriv_F k τ hτ
    calc DA τ + τ * (2 * (Real.pi : ℂ) * Complex.I * DB τ)
        = (∑' m : Set.Ici (1 : ℕ),
              radialDeriv 1 (⇑(S.basis (m, 0)).1) x * dirichletTerm m.1 τ)
            + (2 * (Real.pi : ℂ) * Complex.I * τ)
              * (∑' m : Set.Ici (1 : ℕ),
                  (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m, 2)).1) x
                    * dirichletTerm m.1 τ) := by
          simp only [DA, DB, da, db]; ring
      _ = radialDeriv 1 (S.F τ) x := h1.symm
      _ = (2 * (Real.pi : ℂ) * Complex.I * τ * (rate k.1 : ℂ)) * dirichletTerm k.1 τ := h2
      _ = (0 : ℂ)
            + τ * (2 * (Real.pi : ℂ) * Complex.I * ((rate k.1 : ℂ) * dirichletTerm k.1 τ)) := by
          ring
  have hIdDAt : ∀ τ : ℂ, 0 < τ.im →
      DAt τ + τ * (2 * (Real.pi : ℂ) * Complex.I * DBt τ) = (0 : ℂ) + τ * 0 := by
    intro τ hτ
    have h1 := S.expansion_Ftilde_radialDeriv 1 τ x hτ
    have h2 := S.value_radialDeriv_Ftilde k τ hτ
    calc DAt τ + τ * (2 * (Real.pi : ℂ) * Complex.I * DBt τ)
        = (∑' m : Set.Ici (1 : ℕ),
              radialDeriv 1 (⇑(S.basis (m, 1)).1) x * dirichletTerm m.1 τ)
            + (2 * (Real.pi : ℂ) * Complex.I * τ)
              * (∑' m : Set.Ici (1 : ℕ),
                  (rate m.1 : ℂ) * radialDeriv 1 (⇑(S.basis (m, 3)).1) x
                    * dirichletTerm m.1 τ) := by
          simp only [DAt, DBt, dat, dbt]; ring
      _ = radialDeriv 1 (S.Ftilde τ) x := h1.symm
      _ = 0 := h2
      _ = (0 : ℂ) + τ * 0 := by ring
  -- Periodicity of the right-hand sides.
  have hA₂per : ∀ τ : ℂ, (fun σ : ℂ => dirichletTerm k.1 σ) (τ + 1)
      = (fun σ : ℂ => dirichletTerm k.1 σ) τ := fun τ => dirichletTerm_add_one k.1 τ
  have hzero_per : ∀ τ : ℂ, (fun _ : ℂ => (0 : ℂ)) (τ + 1) = (fun _ : ℂ => (0 : ℂ)) τ :=
    fun τ => rfl
  have hB1per : ∀ τ : ℂ, (fun σ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * B σ) (τ + 1)
      = (fun σ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * B σ) τ := by
    intro τ
    show 2 * (Real.pi : ℂ) * Complex.I * B (τ + 1) = 2 * (Real.pi : ℂ) * Complex.I * B τ
    rw [hBper τ]
  have hBt1per : ∀ τ : ℂ, (fun σ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * Bt σ) (τ + 1)
      = (fun σ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * Bt σ) τ := by
    intro τ
    show 2 * (Real.pi : ℂ) * Complex.I * Bt (τ + 1) = 2 * (Real.pi : ℂ) * Complex.I * Bt τ
    rw [hBtper τ]
  have hDB1per : ∀ τ : ℂ, (fun σ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * DB σ) (τ + 1)
      = (fun σ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * DB σ) τ := by
    intro τ
    show 2 * (Real.pi : ℂ) * Complex.I * DB (τ + 1) = 2 * (Real.pi : ℂ) * Complex.I * DB τ
    rw [hDBper τ]
  have hDBt1per : ∀ τ : ℂ, (fun σ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * DBt σ) (τ + 1)
      = (fun σ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * DBt σ) τ := by
    intro τ
    show 2 * (Real.pi : ℂ) * Complex.I * DBt (τ + 1) = 2 * (Real.pi : ℂ) * Complex.I * DBt τ
    rw [hDBtper τ]
  have hDB₂per : ∀ τ : ℂ,
      (fun σ : ℂ =>
        2 * (Real.pi : ℂ) * Complex.I * ((rate k.1 : ℂ) * dirichletTerm k.1 σ)) (τ + 1)
        = (fun σ : ℂ =>
          2 * (Real.pi : ℂ) * Complex.I * ((rate k.1 : ℂ) * dirichletTerm k.1 σ)) τ := by
    intro τ
    show 2 * (Real.pi : ℂ) * Complex.I * ((rate k.1 : ℂ) * dirichletTerm k.1 (τ + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * ((rate k.1 : ℂ) * dirichletTerm k.1 τ)
    rw [dirichletTerm_add_one]
  -- Splitting off the linear parts.
  obtain ⟨hA_val, hB_lin⟩ := PeriodicAddSmulUHP hAper hA₂per hB1per hzero_per hIdA
  obtain ⟨hAtr_val, hBt_lin⟩ := PeriodicAddSmulUHP hAtrper hzero_per hBt1per hzero_per hIdAtr
  obtain ⟨hDA_val, hDB_lin⟩ := PeriodicAddSmulUHP hDAper hzero_per hDB1per hDB₂per hIdDA
  obtain ⟨hDAt_val, hDBt_lin⟩ := PeriodicAddSmulUHP hDAtper hzero_per hDBt1per hzero_per hIdDAt
  have hBzero : ∀ τ : ℂ, 0 < τ.im → B τ = 0 := fun τ hτ =>
    (mul_eq_zero.mp (hB_lin τ hτ)).resolve_left two_pi_I_ne_zero
  have hBtzero : ∀ τ : ℂ, 0 < τ.im → Bt τ = 0 := fun τ hτ =>
    (mul_eq_zero.mp (hBt_lin τ hτ)).resolve_left two_pi_I_ne_zero
  have hDBval : ∀ τ : ℂ, 0 < τ.im → DB τ = (rate k.1 : ℂ) * dirichletTerm k.1 τ := fun τ hτ =>
    mul_left_cancel₀ two_pi_I_ne_zero (hDB_lin τ hτ)
  have hDBtzero : ∀ τ : ℂ, 0 < τ.im → DBt τ = 0 := fun τ hτ =>
    (mul_eq_zero.mp (hDBt_lin τ hτ)).resolve_left two_pi_I_ne_zero
  -- Summability of the coefficient sequences on the line `Im τ = 1`.
  have hsum_a : Summable fun m : Set.Ici (1 : ℕ) =>
      a m * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
    obtain ⟨C, N, hC, hb⟩ := basis_sample_bound S 0 k
    exact SummableMulExpNeg hC one_pos hb
  have hsum_atr : Summable fun m : Set.Ici (1 : ℕ) =>
      atr m * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
    obtain ⟨C, N, hC, hb⟩ := basis_sample_bound S 1 k
    exact SummableMulExpNeg hC one_pos hb
  have hsum_da : Summable fun m : Set.Ici (1 : ℕ) =>
      da m * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
    obtain ⟨C, N, hC, hb⟩ := radialDeriv_basis_sample_bound S 0 k
    exact SummableMulExpNeg hC one_pos hb
  have hsum_dat : Summable fun m : Set.Ici (1 : ℕ) =>
      dat m * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
    obtain ⟨C, N, hC, hb⟩ := radialDeriv_basis_sample_bound S 1 k
    exact SummableMulExpNeg hC one_pos hb
  have hsum_rate_b : Summable fun m : Set.Ici (1 : ℕ) =>
      ((rate m.1 : ℂ) * b m) * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
    obtain ⟨C, N, hC, hb⟩ := basis_sample_bound S 2 k
    obtain ⟨C', N', hC', hb'⟩ := rate_mul_bound hC hb
    exact SummableMulExpNeg hC' one_pos hb'
  have hsum_rate_bt : Summable fun m : Set.Ici (1 : ℕ) =>
      ((rate m.1 : ℂ) * bt m) * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
    obtain ⟨C, N, hC, hb⟩ := basis_sample_bound S 3 k
    obtain ⟨C', N', hC', hb'⟩ := rate_mul_bound hC hb
    exact SummableMulExpNeg hC' one_pos hb'
  have hsum_rate_db : Summable fun m : Set.Ici (1 : ℕ) =>
      ((rate m.1 : ℂ) * db m) * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
    obtain ⟨C, N, hC, hb⟩ := radialDeriv_basis_sample_bound S 2 k
    obtain ⟨C', N', hC', hb'⟩ := rate_mul_bound hC hb
    exact SummableMulExpNeg hC' one_pos hb'
  have hsum_rate_dbt : Summable fun m : Set.Ici (1 : ℕ) =>
      ((rate m.1 : ℂ) * dbt m) * Complex.exp (-(2 * (Real.pi : ℂ) * (1 : ℂ) * (m.1 : ℝ))) := by
    obtain ⟨C, N, hC, hb⟩ := radialDeriv_basis_sample_bound S 3 k
    obtain ⟨C', N', hC', hb'⟩ := rate_mul_bound hC hb
    exact SummableMulExpNeg hC' one_pos hb'
  -- Extraction of the eight families.
  have ha_val : ∀ m : Set.Ici (1 : ℕ), a m = (if k = m then 1 else 0) := by
    refine dirichlet_extract (c := a) (d := fun m => if k = m then (1 : ℂ) else 0)
      hsum_a (summable_delta k 1) ?_
    intro t
    set τ : ℂ := (t : ℂ) + (1 : ℂ) * Complex.I with hτdef
    have hτ : 0 < τ.im := by rw [hτdef]; simp
    show (∑' m : Set.Ici (1 : ℕ), a m * dirichletTerm m.1 τ)
      = ∑' m : Set.Ici (1 : ℕ), (if k = m then (1 : ℂ) else 0) * dirichletTerm m.1 τ
    rw [show (∑' m : Set.Ici (1 : ℕ), a m * dirichletTerm m.1 τ) = A τ from rfl,
      hA_val τ hτ, tsum_delta_dirichletTerm k τ]
  have hr_b : ∀ m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * b m = 0 := by
    refine dirichlet_extract (c := fun m => (rate m.1 : ℂ) * b m) (d := fun _ => 0)
      hsum_rate_b summable_zero_exp ?_
    intro t
    set τ : ℂ := (t : ℂ) + (1 : ℂ) * Complex.I with hτdef
    have hτ : 0 < τ.im := by rw [hτdef]; simp
    show (∑' m : Set.Ici (1 : ℕ), ((rate m.1 : ℂ) * b m) * dirichletTerm m.1 τ)
      = ∑' m : Set.Ici (1 : ℕ), (0 : ℂ) * dirichletTerm m.1 τ
    rw [show (∑' m : Set.Ici (1 : ℕ), ((rate m.1 : ℂ) * b m) * dirichletTerm m.1 τ)
        = B τ from rfl, hBzero τ hτ]
    simp
  have hda_val : ∀ m : Set.Ici (1 : ℕ), da m = 0 := by
    refine dirichlet_extract (c := da) (d := fun _ => 0) hsum_da summable_zero_exp ?_
    intro t
    set τ : ℂ := (t : ℂ) + (1 : ℂ) * Complex.I with hτdef
    have hτ : 0 < τ.im := by rw [hτdef]; simp
    show (∑' m : Set.Ici (1 : ℕ), da m * dirichletTerm m.1 τ)
      = ∑' m : Set.Ici (1 : ℕ), (0 : ℂ) * dirichletTerm m.1 τ
    rw [show (∑' m : Set.Ici (1 : ℕ), da m * dirichletTerm m.1 τ) = DA τ from rfl,
      hDA_val τ hτ]
    simp
  have hr_db : ∀ m : Set.Ici (1 : ℕ),
      (rate m.1 : ℂ) * db m = (if k = m then (rate k.1 : ℂ) else 0) := by
    refine dirichlet_extract (c := fun m => (rate m.1 : ℂ) * db m)
      (d := fun m => if k = m then (rate k.1 : ℂ) else 0)
      hsum_rate_db (summable_delta k (rate k.1)) ?_
    intro t
    set τ : ℂ := (t : ℂ) + (1 : ℂ) * Complex.I with hτdef
    have hτ : 0 < τ.im := by rw [hτdef]; simp
    show (∑' m : Set.Ici (1 : ℕ), ((rate m.1 : ℂ) * db m) * dirichletTerm m.1 τ)
      = ∑' m : Set.Ici (1 : ℕ),
          (if k = m then (rate k.1 : ℂ) else 0) * dirichletTerm m.1 τ
    rw [show (∑' m : Set.Ici (1 : ℕ), ((rate m.1 : ℂ) * db m) * dirichletTerm m.1 τ)
        = DB τ from rfl, hDBval τ hτ, tsum_rate_delta_dirichletTerm k τ]
  have hatr_val : ∀ m : Set.Ici (1 : ℕ), atr m = 0 := by
    refine dirichlet_extract (c := atr) (d := fun _ => 0) hsum_atr summable_zero_exp ?_
    intro t
    set τ : ℂ := (t : ℂ) + (1 : ℂ) * Complex.I with hτdef
    have hτ : 0 < τ.im := by rw [hτdef]; simp
    show (∑' m : Set.Ici (1 : ℕ), atr m * dirichletTerm m.1 τ)
      = ∑' m : Set.Ici (1 : ℕ), (0 : ℂ) * dirichletTerm m.1 τ
    rw [show (∑' m : Set.Ici (1 : ℕ), atr m * dirichletTerm m.1 τ) = Atr τ from rfl,
      hAtr_val τ hτ]
    simp
  have hr_bt : ∀ m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * bt m = 0 := by
    refine dirichlet_extract (c := fun m => (rate m.1 : ℂ) * bt m) (d := fun _ => 0)
      hsum_rate_bt summable_zero_exp ?_
    intro t
    set τ : ℂ := (t : ℂ) + (1 : ℂ) * Complex.I with hτdef
    have hτ : 0 < τ.im := by rw [hτdef]; simp
    show (∑' m : Set.Ici (1 : ℕ), ((rate m.1 : ℂ) * bt m) * dirichletTerm m.1 τ)
      = ∑' m : Set.Ici (1 : ℕ), (0 : ℂ) * dirichletTerm m.1 τ
    rw [show (∑' m : Set.Ici (1 : ℕ), ((rate m.1 : ℂ) * bt m) * dirichletTerm m.1 τ)
        = Bt τ from rfl, hBtzero τ hτ]
    simp
  have hdat_val : ∀ m : Set.Ici (1 : ℕ), dat m = 0 := by
    refine dirichlet_extract (c := dat) (d := fun _ => 0) hsum_dat summable_zero_exp ?_
    intro t
    set τ : ℂ := (t : ℂ) + (1 : ℂ) * Complex.I with hτdef
    have hτ : 0 < τ.im := by rw [hτdef]; simp
    show (∑' m : Set.Ici (1 : ℕ), dat m * dirichletTerm m.1 τ)
      = ∑' m : Set.Ici (1 : ℕ), (0 : ℂ) * dirichletTerm m.1 τ
    rw [show (∑' m : Set.Ici (1 : ℕ), dat m * dirichletTerm m.1 τ) = DAt τ from rfl,
      hDAt_val τ hτ]
    simp
  have hr_dbt : ∀ m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * dbt m = 0 := by
    refine dirichlet_extract (c := fun m => (rate m.1 : ℂ) * dbt m) (d := fun _ => 0)
      hsum_rate_dbt summable_zero_exp ?_
    intro t
    set τ : ℂ := (t : ℂ) + (1 : ℂ) * Complex.I with hτdef
    have hτ : 0 < τ.im := by rw [hτdef]; simp
    show (∑' m : Set.Ici (1 : ℕ), ((rate m.1 : ℂ) * dbt m) * dirichletTerm m.1 τ)
      = ∑' m : Set.Ici (1 : ℕ), (0 : ℂ) * dirichletTerm m.1 τ
    rw [show (∑' m : Set.Ici (1 : ℕ), ((rate m.1 : ℂ) * dbt m) * dirichletTerm m.1 τ)
        = DBt τ from rfl, hDBtzero τ hτ]
    simp
  -- Divide by the nonzero rate.
  have hb_val : ∀ m : Set.Ici (1 : ℕ), b m = 0 := fun m =>
    (mul_eq_zero.mp (hr_b m)).resolve_left (rate_ne_zero m.1 m.2)
  have hbt_val : ∀ m : Set.Ici (1 : ℕ), bt m = 0 := fun m =>
    (mul_eq_zero.mp (hr_bt m)).resolve_left (rate_ne_zero m.1 m.2)
  have hdbt_val : ∀ m : Set.Ici (1 : ℕ), dbt m = 0 := fun m =>
    (mul_eq_zero.mp (hr_dbt m)).resolve_left (rate_ne_zero m.1 m.2)
  have hdb_val : ∀ m : Set.Ici (1 : ℕ), db m = (if k = m then 1 else 0) := by
    intro m
    have hm := hr_db m
    by_cases h : k = m
    · subst h
      rw [if_pos rfl] at hm
      rw [if_pos rfl]
      exact mul_left_cancel₀ (rate_ne_zero k.1 k.2) (by rw [mul_one]; exact hm)
    · rw [if_neg h] at hm
      rw [if_neg h]
      exact (mul_eq_zero.mp hm).resolve_left (rate_ne_zero m.1 m.2)
  intro m
  exact ⟨ha_val m, hatr_val m, hb_val m, hbt_val m, hda_val m, hdat_val m, hdb_val m,
    hdbt_val m⟩

/-- The four samples of the coefficient families at the radius `√(2k)`, in the order
used by `coeffs`. -/
private lemma coeffs_zero {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)) :
    coeffs n 1 f (k, 0) = f (samplePoint (n := n) (k.1 : ℝ)) := by
  simp [coeffs, Function.uncurry_apply_pair, samplePoint]

private lemma coeffs_one {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)) :
    coeffs n 1 f (k, 1)
      = (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f) (samplePoint (n := n) (k.1 : ℝ)) := by
  simp [coeffs, Function.uncurry_apply_pair, samplePoint]

private lemma coeffs_two {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)) :
    coeffs n 1 f (k, 2) = radialDeriv 1 (⇑f) (samplePoint (n := n) (k.1 : ℝ)) := by
  rw [show samplePoint (n := n) (k.1 : ℝ) = realIncl (Real.sqrt (2 * (k.1 : ℝ))) from rfl]
  rw [radialDeriv_one_of_nonneg (g := ⇑f) (Real.sqrt_nonneg _)]
  simp [coeffs, Function.uncurry_apply_pair]

private lemma coeffs_three {n : ℕ} [NeZero n] (f : 𝓢(E n, ℂ)) (k : Set.Ici (1 : ℕ)) :
    coeffs n 1 f (k, 3)
      = radialDeriv 1 (⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f))
          (samplePoint (n := n) (k.1 : ℝ)) := by
  rw [show samplePoint (n := n) (k.1 : ℝ) = realIncl (Real.sqrt (2 * (k.1 : ℝ))) from rfl]
  rw [radialDeriv_one_of_nonneg (g := ⇑(FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) f))
    (Real.sqrt_nonneg _)]
  simp [coeffs, Function.uncurry_apply_pair]

/-- The condition `(k, s) = (m, s)` only involves the first coordinate. -/
private lemma ite_diag {α : Type*} [DecidableEq α] {k m : α} (s : Fin 4) (a : ℂ) :
    (if (k, s) = (m, s) then a else 0) = (if k = m then a else 0) := by
  by_cases h : k = m
  · subst h; simp
  · rw [if_neg h, if_neg (fun hh => h (Prod.ext_iff.mp hh).1)]

theorem BasisCoeffsDelta {n : ℕ} [NeZero n] (S : InterpolationSolution n) :
    ∀ i : SampleIdx 1, coeffs n 1 (S.basis i).1 = fun j => if j = i then (1 : ℂ) else 0 := by
  intro i
  obtain ⟨m, s⟩ := i
  have hFF1 : FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (S.basis (m, 0)).1)
      = (S.basis (m, 0)).1 := by
    ext y
    exact FourierInversionRadial (S.basis (m, 0)).1 (S.basis (m, 0)).2 y
  have hFF2 : FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ))
      (FourierTransform.fourierCLM ℂ (𝓢(E n, ℂ)) (S.basis (m, 2)).1)
      = (S.basis (m, 2)).1 := by
    ext y
    exact FourierInversionRadial (S.basis (m, 2)).1 (S.basis (m, 2)).2 y
  fin_cases s
  · funext j
    obtain ⟨k, t⟩ := j
    fin_cases t
    · show coeffs n 1 (S.basis (m, (0 : Fin 4))).1 (k, (0 : Fin 4))
          = (if (k, (0 : Fin 4)) = (m, (0 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_zero, ite_diag (0 : Fin 4) (1 : ℂ)]
      exact (BasisSampleValuesAt S k m).1
    · show coeffs n 1 (S.basis (m, (0 : Fin 4))).1 (k, (1 : Fin 4))
          = (if (k, (1 : Fin 4)) = (m, (0 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_one, ← S.fourier_basis m,
        if_neg (by simp : ¬ ((k, (1 : Fin 4)) = (m, (0 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.1
    · show coeffs n 1 (S.basis (m, (0 : Fin 4))).1 (k, (2 : Fin 4))
          = (if (k, (2 : Fin 4)) = (m, (0 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_two, if_neg (by simp : ¬ ((k, (2 : Fin 4)) = (m, (0 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.2.2.1
    · show coeffs n 1 (S.basis (m, (0 : Fin 4))).1 (k, (3 : Fin 4))
          = (if (k, (3 : Fin 4)) = (m, (0 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_three, ← S.fourier_basis m,
        if_neg (by simp : ¬ ((k, (3 : Fin 4)) = (m, (0 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.2.2.2.1
  · funext j
    obtain ⟨k, t⟩ := j
    fin_cases t
    · show coeffs n 1 (S.basis (m, (1 : Fin 4))).1 (k, (0 : Fin 4))
          = (if (k, (0 : Fin 4)) = (m, (1 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_zero, if_neg (by simp : ¬ ((k, (0 : Fin 4)) = (m, (1 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.1
    · show coeffs n 1 (S.basis (m, (1 : Fin 4))).1 (k, (1 : Fin 4))
          = (if (k, (1 : Fin 4)) = (m, (1 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_one, S.fourier_basis m, hFF1, ite_diag (1 : Fin 4) (1 : ℂ)]
      exact (BasisSampleValuesAt S k m).1
    · show coeffs n 1 (S.basis (m, (1 : Fin 4))).1 (k, (2 : Fin 4))
          = (if (k, (2 : Fin 4)) = (m, (1 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_two, if_neg (by simp : ¬ ((k, (2 : Fin 4)) = (m, (1 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.2.2.2.1
    · show coeffs n 1 (S.basis (m, (1 : Fin 4))).1 (k, (3 : Fin 4))
          = (if (k, (3 : Fin 4)) = (m, (1 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_three, S.fourier_basis m, hFF1,
        if_neg (by simp : ¬ ((k, (3 : Fin 4)) = (m, (1 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.2.2.1
  · funext j
    obtain ⟨k, t⟩ := j
    fin_cases t
    · show coeffs n 1 (S.basis (m, (2 : Fin 4))).1 (k, (0 : Fin 4))
          = (if (k, (0 : Fin 4)) = (m, (2 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_zero, if_neg (by simp : ¬ ((k, (0 : Fin 4)) = (m, (2 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.1
    · show coeffs n 1 (S.basis (m, (2 : Fin 4))).1 (k, (1 : Fin 4))
          = (if (k, (1 : Fin 4)) = (m, (2 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_one, ← S.fourier_basis' m,
        if_neg (by simp : ¬ ((k, (1 : Fin 4)) = (m, (2 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.2.1
    · show coeffs n 1 (S.basis (m, (2 : Fin 4))).1 (k, (2 : Fin 4))
          = (if (k, (2 : Fin 4)) = (m, (2 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_two, ite_diag (2 : Fin 4) (1 : ℂ)]
      exact (BasisSampleValuesAt S k m).2.2.2.2.2.2.1
    · show coeffs n 1 (S.basis (m, (2 : Fin 4))).1 (k, (3 : Fin 4))
          = (if (k, (3 : Fin 4)) = (m, (2 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_three, ← S.fourier_basis' m,
        if_neg (by simp : ¬ ((k, (3 : Fin 4)) = (m, (2 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.2.2.2.2.2
  · funext j
    obtain ⟨k, t⟩ := j
    fin_cases t
    · show coeffs n 1 (S.basis (m, (3 : Fin 4))).1 (k, (0 : Fin 4))
          = (if (k, (0 : Fin 4)) = (m, (3 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_zero, if_neg (by simp : ¬ ((k, (0 : Fin 4)) = (m, (3 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.2.1
    · show coeffs n 1 (S.basis (m, (3 : Fin 4))).1 (k, (1 : Fin 4))
          = (if (k, (1 : Fin 4)) = (m, (3 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_one, S.fourier_basis' m, hFF2,
        if_neg (by simp : ¬ ((k, (1 : Fin 4)) = (m, (3 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.1
    · show coeffs n 1 (S.basis (m, (3 : Fin 4))).1 (k, (2 : Fin 4))
          = (if (k, (2 : Fin 4)) = (m, (3 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_two, if_neg (by simp : ¬ ((k, (2 : Fin 4)) = (m, (3 : Fin 4))))]
      exact (BasisSampleValuesAt S k m).2.2.2.2.2.2.2
    · show coeffs n 1 (S.basis (m, (3 : Fin 4))).1 (k, (3 : Fin 4))
          = (if (k, (3 : Fin 4)) = (m, (3 : Fin 4)) then (1 : ℂ) else 0)
      rw [coeffs_three, S.fourier_basis' m, hFF2, ite_diag (3 : Fin 4) (1 : ℂ)]
      exact (BasisSampleValuesAt S k m).2.2.2.2.2.2.1

end Work.FunctionalEquations


end Work.CKFinal.Shadow
