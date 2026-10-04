import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pdVec_pair_eq_lambda`: the `L²` pairing of the `k`-th order flat energy as a multiplier form

For two smooth `1`-periodic functions `X, Y` on the flat torus `(ι → ℝ)` and every `k`,

  `Σ_{l : Fin k → ι} ⟨∂^l X, ∂^l Y⟩_{L²} = ⟨Λ^k X, Y⟩_{L²}`,

where `Λ` is the flat Laplacian, acting on the Fourier side by multiplication with the symbol
`λ(m) = Σᵢ (2π mᵢ)²`: this is the "Parseval / integration by parts for `pdVec`" identity needed to
read the `Hᵏ` energy as the quadratic form of the Fourier multiplier `λ^k`.

The proof is purely Fourier-analytic and is the composition of three ingredients of the Layer A
toolkit:

* `seriesFun_fourierCoeff`: a smooth `1`-periodic function is its own Fourier series,
  `f = seriesFun (fourierCoeff f)`;
* `pdList_seriesFun` together with the multiplier identity
  `fourierCoeff (∂^l f) m = ∏ᵢ 2πi m_{lᵢ} · f̂(m)`: the iterated derivative of the Fourier series
  is the Fourier series of the coefficient family `dmulV l (fourierCoeff f)`;
* `integral_seriesFun_mul_conj` (Parseval for Fourier series):
  `⟨seriesFun c, seriesFun d⟩_{L²} = (Σₘ c m · conj (d m)).re`.

After these reductions the statement becomes the elementary identity
`Σ_{l : Fin k → ι} ∏ᵢ (2πi m_{lᵢ})·conj(2πi m_{lᵢ}) = (Σᵢ (2π mᵢ)²)^k`
(the multinomial expansion `Fintype.sum_pow`, with `z·conj z = |z|²`), together with the exchange
of the finite sum over `l` with the `tsum` over `m` (`Summable.tsum_finsetSum`), for which the
product families are dominated by `⟨m⟩^{2k}‖Ŷ(m)‖` using `norm_dmulV_le` and the rapid decay of
the Fourier coefficients (`summable_wt_pow_norm_fourierCoeff_of_contDiff`).
-/

noncomputable section

namespace Work.Diff.STE.B3

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The symbol of the flat Laplacian, `λ m = Σᵢ (2π mᵢ)²`. -/
private def lam (m : ι → ℤ) : ℝ := ∑ i, (2 * Real.pi * (m i : ℝ)) ^ 2

private lemma lam_nonneg (m : ι → ℤ) : 0 ≤ lam m :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma lam_le (m : ι → ℤ) : lam m ≤ (2 * Real.pi) ^ 2 * Work.Diff.STE.wt m := by
  have h1 : lam m = (2 * Real.pi) ^ 2 * ∑ i, ((m i : ℤ) : ℝ) ^ 2 := by
    rw [lam, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow]
  have h2 : ∑ i, ((m i : ℤ) : ℝ) ^ 2 ≤ Work.Diff.STE.wt m := by
    have h3 : ∑ i, ((m i : ℤ) : ℝ) ^ 2 ≤ 1 + ∑ i, ((m i : ℤ) : ℝ) ^ 2 := by linarith
    simpa [Work.Diff.STE.wt] using h3
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

/-- The coefficient family of `Λ^k X`, `m ↦ λ(m)^k · X̂(m)`. -/
private def lamCoeff (k : ℕ) (X : (ι → ℝ) → ℂ) : (ι → ℤ) → ℂ :=
  fun m => ((lam m ^ k : ℝ) : ℂ) * Work.Diff.STE.fourierCoeff X m

/-- The Fourier multiplier factor `2πi mᵢ` times its conjugate is `(2π mᵢ)²`. -/
private lemma dmul_factor_mul_star (z : ℤ) :
    (2 * Real.pi * Complex.I * (z : ℂ)) * star (2 * Real.pi * Complex.I * (z : ℂ))
      = (((2 * Real.pi * (z : ℝ)) ^ 2 : ℝ) : ℂ) := by
  have h : (2 * Real.pi * Complex.I * (z : ℂ))
      = (((2 * Real.pi * (z : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h]
  simp only [Complex.star_def]
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_pow]
  rw [show (((2 * Real.pi * (z : ℝ)) : ℝ) : ℂ) * Complex.I
        * ((((2 * Real.pi * (z : ℝ)) : ℝ) : ℂ) * -Complex.I)
      = -((((2 * Real.pi * (z : ℝ)) : ℝ) : ℂ) * (((2 * Real.pi * (z : ℝ)) : ℝ) : ℂ)
        * (Complex.I * Complex.I)) by ring,
    Complex.I_mul_I]
  ring

/-- The multinomial expansion of the symbol: summing the products of the multipliers of a word
`l : Fin k → ι` over all words gives the `k`-th power of `Σᵢ (2π mᵢ)²`. -/
private lemma sum_prod_dmul_factor (k : ℕ) (m : ι → ℤ) :
    (∑ l : Fin k → ι, ∏ i : Fin k, (2 * Real.pi * Complex.I * (m (l i) : ℂ))
        * star (2 * Real.pi * Complex.I * (m (l i) : ℂ)))
      = (((∑ i, (2 * Real.pi * (m i : ℝ)) ^ 2) ^ k : ℝ) : ℂ) := by
  rw [Finset.sum_congr rfl
    (fun l _ => Finset.prod_congr rfl (fun i _ => dmul_factor_mul_star (m (l i))))]
  rw [← Fintype.sum_pow (fun i : ι => (((2 * Real.pi * (m i : ℝ)) ^ 2 : ℝ) : ℂ)) k]
  rw [← Complex.ofReal_sum Finset.univ (fun i : ι => (2 * Real.pi * (m i : ℝ)) ^ 2)]
  rw [← Complex.ofReal_pow]

/-- The multiplier factorisation of one summand: the `l`-th iterated derivative contributes
`∏ᵢ (2πi m_{lᵢ})` to each of the two factors, and the cross terms pair up to
`∏ᵢ (2πi m_{lᵢ})·conj(2πi m_{lᵢ})`. -/
private lemma dmulV_pair_star (k : ℕ) (l : Fin k → ι) (m : ι → ℤ) (c d : (ι → ℤ) → ℂ) :
    Work.Diff.STE.dmulV (List.ofFn l) c m * star (Work.Diff.STE.dmulV (List.ofFn l) d m)
      = (∏ i : Fin k, (2 * Real.pi * Complex.I * (m (l i) : ℂ))
          * star (2 * Real.pi * Complex.I * (m (l i) : ℂ)))
        * (c m * star (d m)) := by
  have hdmul : ∀ e : (ι → ℤ) → ℂ, Work.Diff.STE.dmulV (List.ofFn l) e m
      = (∏ i : Fin k, (2 * Real.pi * Complex.I * (m (l i) : ℂ))) * e m := by
    intro e
    rw [Work.Diff.STE.dmulV, List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hdmul c, hdmul d]
  rw [show (∏ i : Fin k, (2 * Real.pi * Complex.I * (m (l i) : ℂ))
          * star (2 * Real.pi * Complex.I * (m (l i) : ℂ)))
        = (∏ i : Fin k, (2 * Real.pi * Complex.I * (m (l i) : ℂ)))
          * star (∏ i : Fin k, (2 * Real.pi * Complex.I * (m (l i) : ℂ))) by
      rw [Finset.prod_mul_distrib, star_prod]]
  rw [star_mul]
  generalize hp : (∏ i : Fin k, (2 * Real.pi * Complex.I * (m (l i) : ℂ))) = P
  ring

/-- Parseval for Fourier series: the `L²` pairing of two Fourier series is the coefficient pairing
`(Σₘ c m · conj (d m)).re`. -/
private lemma L2re_seriesFun (c d : (ι → ℤ) → ℂ) (hc : Summable fun k => ‖c k‖)
    (hd : Summable fun k => ‖d k‖) :
    Work.Diff.STE.L2re (Work.Diff.STE.seriesFun c) (Work.Diff.STE.seriesFun d)
      = (∑' k : ι → ℤ, c k * star (d k)).re := by
  rw [Work.Diff.STE.L2re, Work.Diff.STE.integral_seriesFun_mul_conj c d hc hd]

/-- The product of two differentiated rapidly decaying coefficient families is summable: it is
dominated by `(2π)^{2k} · (Σ‖u‖) · ⟨m⟩^{2k}‖v m‖`, which is summable by the rapid decay of `v`. -/
private lemma summable_dmulV_pair (k : ℕ) (l : Fin k → ι) {u v : (ι → ℤ) → ℂ}
    (hu : ∀ N : ℕ, Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ N * ‖u m‖))
    (hv : ∀ N : ℕ, Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ N * ‖v m‖)) :
    Summable (fun m : ι → ℤ => Work.Diff.STE.dmulV (List.ofFn l) u m
      * star (Work.Diff.STE.dmulV (List.ofFn l) v m)) := by
  have hU : Summable (fun m : ι → ℤ => ‖u m‖) := by simpa using hu 0
  have hSU : 0 ≤ ∑' m : ι → ℤ, ‖u m‖ := tsum_nonneg fun m => norm_nonneg _
  refine Summable.of_norm_bounded
    ((hv (2 * k)).mul_left ((2 * Real.pi) ^ (2 * k) * (∑' m : ι → ℤ, ‖u m‖))) (fun m => ?_)
  have hwt : (0 : ℝ) ≤ Work.Diff.STE.wt m := (Work.Diff.STE.wt_pos m).le
  have hfac : (0 : ℝ) ≤ 2 * Real.pi * Work.Diff.STE.wt m :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) hwt
  calc ‖Work.Diff.STE.dmulV (List.ofFn l) u m * star (Work.Diff.STE.dmulV (List.ofFn l) v m)‖
      = ‖Work.Diff.STE.dmulV (List.ofFn l) u m‖ * ‖Work.Diff.STE.dmulV (List.ofFn l) v m‖ := by
        rw [norm_mul, norm_star]
    _ ≤ ((2 * Real.pi * Work.Diff.STE.wt m) ^ (List.ofFn l).length * ‖u m‖)
          * ((2 * Real.pi * Work.Diff.STE.wt m) ^ (List.ofFn l).length * ‖v m‖) :=
        mul_le_mul (Work.Diff.STE.norm_dmulV_le (List.ofFn l) u m)
          (Work.Diff.STE.norm_dmulV_le (List.ofFn l) v m) (norm_nonneg _)
          (mul_nonneg (pow_nonneg hfac _) (norm_nonneg _))
    _ ≤ ((2 * Real.pi * Work.Diff.STE.wt m) ^ k * (∑' m : ι → ℤ, ‖u m‖))
          * ((2 * Real.pi * Work.Diff.STE.wt m) ^ k * ‖v m‖) := by
        rw [List.length_ofFn]
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (hU.le_tsum m fun a _ => norm_nonneg _) (pow_nonneg hfac k)) (le_refl _)
          (mul_nonneg (pow_nonneg hfac k) (norm_nonneg _))
          (mul_nonneg (pow_nonneg hfac k) hSU)
    _ = ((2 * Real.pi) ^ (2 * k) * (∑' m : ι → ℤ, ‖u m‖))
          * ((Work.Diff.STE.wt m) ^ (2 * k) * ‖v m‖) := by rw [mul_pow, mul_pow]; ring

theorem pdVec_pair_eq_lambda {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (X Y : (ι → ℝ) → ℂ)
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hpX : Work.Diff.STE.Periodic1 X) (hpY : Work.Diff.STE.Periodic1 Y) :
    (∑ l : Fin k → ι, Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l X) (Work.Diff.STE.pdVec k l Y))
      = Work.Diff.STE.L2re (fun z => Work.Diff.STE.seriesFun
            (fun m : ι → ℤ => (((∑ i, (2 * Real.pi * (m i : ℝ)) ^ 2) ^ k : ℝ) : ℂ) *
              Work.Diff.STE.fourierCoeff X m) z) Y := by
  classical
  have hdecX : ∀ N : ℕ,
      Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ N * ‖Work.Diff.STE.fourierCoeff X m‖) :=
    fun N => Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff X hX hpX N
  have hdecY : ∀ N : ℕ,
      Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ N * ‖Work.Diff.STE.fourierCoeff Y m‖) :=
    fun N => Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff Y hY hpY N
  have hXser : X = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff X) :=
    funext fun x => (Work.Diff.STE.flat.seriesFun_fourierCoeff X hX hpX x).symm
  have hYser : Y = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff Y) :=
    funext fun x => (Work.Diff.STE.flat.seriesFun_fourierCoeff Y hY hpY x).symm
  -- the `l`-th term of the left hand side, as a coefficient pairing
  have hterm : ∀ l : Fin k → ι,
      Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l X) (Work.Diff.STE.pdVec k l Y)
        = (∑' m : ι → ℤ, Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) m
            * star (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) m)).re := by
    intro l
    have h1 : Work.Diff.STE.pdVec k l X
        = Work.Diff.STE.seriesFun
            (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X)) :=
      (congrArg (fun f => Work.Diff.STE.pdVec k l f) hXser).trans
        (funext fun x =>
          Work.Diff.STE.pdList_seriesFun (List.ofFn l) (Work.Diff.STE.fourierCoeff X) hdecX x)
    have h2 : Work.Diff.STE.pdVec k l Y
        = Work.Diff.STE.seriesFun
            (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y)) :=
      (congrArg (fun f => Work.Diff.STE.pdVec k l f) hYser).trans
        (funext fun x =>
          Work.Diff.STE.pdList_seriesFun (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) hdecY x)
    rw [h1, h2, L2re_seriesFun _ _
      (by simpa using
        Work.Diff.STE.summable_dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) hdecX 0)
      (by simpa using
        Work.Diff.STE.summable_dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) hdecY 0)]
  have hsum1 : (∑ l : Fin k → ι,
        Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l X) (Work.Diff.STE.pdVec k l Y))
      = (∑ l : Fin k → ι, ∑' m : ι → ℤ,
          Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) m
          * star (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) m)).re := by
    rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Complex.re_sum Finset.univ
      (fun l : Fin k → ι => ∑' m : ι → ℤ,
        Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) m
          * star (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) m))]
  have hsumm : ∀ l : Fin k → ι, Summable (fun m : ι → ℤ =>
      Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) m
        * star (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) m)) :=
    fun l => summable_dmulV_pair k l hdecX hdecY
  have hswap : (∑ l : Fin k → ι, ∑' m : ι → ℤ,
        Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) m
          * star (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) m))
      = ∑' m : ι → ℤ, ∑ l : Fin k → ι,
        Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) m
          * star (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) m) :=
    (Summable.tsum_finsetSum (s := Finset.univ)
      (f := fun l : Fin k → ι => fun m : ι → ℤ =>
        Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) m
          * star (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) m))
      (fun l _ => hsumm l)).symm
  have hpt : ∀ m : ι → ℤ, (∑ l : Fin k → ι,
        Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) m
          * star (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) m))
      = lamCoeff k X m * star (Work.Diff.STE.fourierCoeff Y m) := by
    intro m
    rw [Finset.sum_congr rfl (fun l _ =>
      dmulV_pair_star k l m (Work.Diff.STE.fourierCoeff X) (Work.Diff.STE.fourierCoeff Y))]
    rw [← Finset.sum_mul, sum_prod_dmul_factor k m]
    simp only [lamCoeff, lam]
    ring
  have htsum : (∑' m : ι → ℤ, ∑ l : Fin k → ι,
        Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff X) m
          * star (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff Y) m))
      = ∑' m : ι → ℤ, lamCoeff k X m * star (Work.Diff.STE.fourierCoeff Y m) := tsum_congr hpt
  have hYsum : Summable (fun m : ι → ℤ => ‖Work.Diff.STE.fourierCoeff Y m‖) := by
    simpa using hdecY 0
  have hcsum : Summable (fun m : ι → ℤ => ‖lamCoeff k X m‖) := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
      ((hdecX k).mul_left ((2 * Real.pi) ^ (2 * k)))
    rw [lamCoeff, norm_mul, Work.Diff.STE.norm_ofReal_cast,
      abs_of_nonneg (pow_nonneg (lam_nonneg m) k)]
    calc (lam m) ^ k * ‖Work.Diff.STE.fourierCoeff X m‖
        ≤ ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt m) ^ k
            * ‖Work.Diff.STE.fourierCoeff X m‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (lam_nonneg m) (lam_le m) k)
            (norm_nonneg _)
      _ = (2 * Real.pi) ^ (2 * k)
            * ((Work.Diff.STE.wt m) ^ k * ‖Work.Diff.STE.fourierCoeff X m‖) := by
          rw [mul_pow, ← pow_mul]
          ring
  have hRHS : Work.Diff.STE.L2re (Work.Diff.STE.seriesFun (lamCoeff k X)) Y
      = (∑' m : ι → ℤ, lamCoeff k X m * star (Work.Diff.STE.fourierCoeff Y m)).re := by
    rw [← L2re_seriesFun (lamCoeff k X) (Work.Diff.STE.fourierCoeff Y) hcsum hYsum]
    exact congrArg (fun g => Work.Diff.STE.L2re (Work.Diff.STE.seriesFun (lamCoeff k X)) g) hYser
  rw [hsum1, hswap, htsum]
  exact hRHS.symm

end Work.Diff.STE.B3
