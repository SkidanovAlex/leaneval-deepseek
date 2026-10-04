import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.QkDef
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: `contDiff_lamCoeff_seriesFun` — smoothness of the `λ^k`-multiplied Fourier series

`Qk D k h` (`Work.Diff.STE.B3.QkDef`) is the section whose `i`-th component function is the Fourier
multiplier with symbol `λ(m)^k` applied to the periodised component `D.Rper i h a b`, where
`λ(m) = lamSym m = Σⱼ (2π mⱼ)²` is the symbol of the *flat* Laplacian.  For the construction of `Qk`
as a genuine smooth section (not merely an `L²` object) one needs that the series

  `seriesFun (fun m => ((λ(m)^k : ℝ) : ℂ) * fourierCoeff (D.Rper i h a b) m)`

is `C^∞` on the torus.  This is the statement proved here.

## Route

The general Weierstrass test for smooth series `Work.Diff.STE.contDiff_seriesFun` reduces the claim to
the *moment* summability of the coefficient family: for every `N`, the family
`m ↦ ⟨m⟩^N ‖c m‖` must be summable, where `⟨m⟩² = wt m = 1 + Σ mᵢ²`.

* The coefficient family is the Fourier transform of the periodised local component
  `D.Rper i h a b`, which is smooth and `1`-periodic as soon as the local component `D.R i h a b` is
  smooth (`Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff`); hence *every* polynomial moment
  of its Fourier coefficients is summable
  (`Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff`, which is Layer A's rapid-decay
  theorem on top of Bessel/Parseval).
* Multiplication by the symbol `λ(m)^k` only costs a polynomial factor: `λ(m) ≤ 4π² ⟨m⟩²` (the symbol
  is `4π²` times the sum of the squared coordinates, which is `≤ 4π² ⟨m⟩²`), so
  `λ(m)^k ≤ (4π²)^k ⟨m⟩^{2k}` and the level-`N` moment of the product is dominated by the level
  `N + k` moment of the original family.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3

/-! ## The elementary bound on the symbol `λ(m) = Σⱼ (2π mⱼ)²` -/

private lemma lamCoeff_nonneg (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (m : Fin (Module.finrank ℝ E) → ℤ) : 0 ≤ lamSym (E := E) m := by
  rw [lamSym_apply]
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The symbol of the flat Laplacian is bounded by `4π²` times the weight `⟨m⟩²` (each coordinate
contributes `(2π mᵢ)² = 4π² mᵢ²`, and `Σ mᵢ² ≤ 1 + Σ mᵢ²`). -/
private lemma lamCoeff_le_wt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (m : Fin (Module.finrank ℝ E) → ℤ) :
    lamSym (E := E) m ≤ 4 * Real.pi ^ 2 * Work.Diff.STE.wt m := by
  have hsum : (0 : ℝ) ≤ ∑ j : Fin (Module.finrank ℝ E), ((m j : ℤ) : ℝ) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hcast : lamSym (E := E) m
      = 4 * Real.pi ^ 2 * ∑ j : Fin (Module.finrank ℝ E), ((m j : ℤ) : ℝ) ^ 2 := by
    rw [lamSym_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hwt : Work.Diff.STE.wt m
      = 1 + ∑ j : Fin (Module.finrank ℝ E), ((m j : ℤ) : ℝ) ^ 2 := rfl
  rw [hcast, hwt]
  nlinarith [hsum, sq_nonneg Real.pi]

/-- `λ(m)^k ≤ (4π²)^k ⟨m⟩^{2k}`. -/
private lemma lamCoeff_pow_le (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (k : ℕ) (m : Fin (Module.finrank ℝ E) → ℤ) :
    lamSym (E := E) m ^ k ≤ (4 * Real.pi ^ 2) ^ k * (Work.Diff.STE.wt m) ^ k := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (lamCoeff_nonneg E m) (lamCoeff_le_wt E m) k

/-! ## Absorption of the symbol into the weight -/

/-- **Moment summability survives multiplication by the symbol `λ^k`.**  If every polynomial moment
`⟨m⟩^N ‖d m‖` is summable, then so is every moment of `m ↦ λ(m)^k · d m`: the symbol grows at most
like `⟨m⟩^{2k}`, so the level-`N` moment of the product is dominated by the level-`N + k` moment of
`d`. -/
private lemma summable_wt_pow_mul_lamSym_pow (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (d : (Fin (Module.finrank ℝ E) → ℤ) → ℂ) (k : ℕ)
    (hd : ∀ N : ℕ, Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      (Work.Diff.STE.wt m) ^ N * ‖d m‖)) (N : ℕ) :
    Summable (fun m : Fin (Module.finrank ℝ E) → ℤ => (Work.Diff.STE.wt m) ^ N *
      ‖((lamSym (E := E) m ^ k : ℝ) : ℂ) * d m‖) := by
  refine Summable.of_nonneg_of_le (f := fun m : Fin (Module.finrank ℝ E) → ℤ =>
      (4 * Real.pi ^ 2) ^ k * ((Work.Diff.STE.wt m) ^ (N + k) * ‖d m‖))
    (fun m => ?_) (fun m => ?_) ((hd (N + k)).mul_left ((4 * Real.pi ^ 2) ^ k))
  · exact mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos m).le N) (norm_nonneg _)
  · have hA : 0 ≤ ‖d m‖ := norm_nonneg _
    have hN : 0 ≤ (Work.Diff.STE.wt m) ^ N := pow_nonneg (Work.Diff.STE.wt_pos m).le N
    have h2 : (Work.Diff.STE.wt m) ^ N * lamSym (E := E) m ^ k
        ≤ (4 * Real.pi ^ 2) ^ k * ((Work.Diff.STE.wt m) ^ N * (Work.Diff.STE.wt m) ^ k) := by
      calc (Work.Diff.STE.wt m) ^ N * lamSym (E := E) m ^ k
          ≤ (Work.Diff.STE.wt m) ^ N *
              ((4 * Real.pi ^ 2) ^ k * (Work.Diff.STE.wt m) ^ k) :=
            mul_le_mul_of_nonneg_left (lamCoeff_pow_le E k m) hN
        _ = (4 * Real.pi ^ 2) ^ k *
              ((Work.Diff.STE.wt m) ^ N * (Work.Diff.STE.wt m) ^ k) := by ring
    rw [norm_mul, Work.Diff.STE.norm_ofReal_cast,
      abs_of_nonneg (pow_nonneg (lamCoeff_nonneg E m) k)]
    calc (Work.Diff.STE.wt m) ^ N * (lamSym (E := E) m ^ k * ‖d m‖)
        = ((Work.Diff.STE.wt m) ^ N * lamSym (E := E) m ^ k) * ‖d m‖ := by ring
      _ ≤ ((4 * Real.pi ^ 2) ^ k *
            ((Work.Diff.STE.wt m) ^ N * (Work.Diff.STE.wt m) ^ k)) * ‖d m‖ :=
          mul_le_mul_of_nonneg_right h2 hA
      _ = (4 * Real.pi ^ 2) ^ k * ((Work.Diff.STE.wt m) ^ (N + k) * ‖d m‖) := by
          rw [pow_add]; ring

/-! ## The target -/

theorem contDiff_lamCoeff_seriesFun
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E))
    (hsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => Work.Diff.STE.seriesFun (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      ((Work.Diff.STE.B3.lamSym (E := E) m ^ k : ℝ) : ℂ) *
        Work.Diff.STE.fourierCoeff (D.Rper i h a b) m) z) := by
  obtain ⟨hcd, hper⟩ := Rper_contDiff_periodic_of_R_contDiff D i h a b hsm
  exact Work.Diff.STE.contDiff_seriesFun
    (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      ((lamSym (E := E) m ^ k : ℝ) : ℂ) * Work.Diff.STE.fourierCoeff (D.Rper i h a b) m)
    (fun N => summable_wt_pow_mul_lamSym_pow E
      (fun m : Fin (Module.finrank ℝ E) → ℤ =>
        Work.Diff.STE.fourierCoeff (D.Rper i h a b) m) k
      (fun N => Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff
        (D.Rper i h a b) hcd hper N) N)

end Work.Diff.STE.B3
