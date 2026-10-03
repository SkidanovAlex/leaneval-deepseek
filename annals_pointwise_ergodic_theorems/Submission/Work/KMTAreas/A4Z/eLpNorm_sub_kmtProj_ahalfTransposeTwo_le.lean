import Mathlib
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.Analysis.InverseTheory.Transpose
import Submission.Port.Aesm

/-!
# The `ℓ²` bound for the minor-arc part of the second dual function

Krause--Mirek--Tao, §5.2.  The second dual function of the halved average is
`Ã_N^{**}(f,h)(x) = N⁻¹ ∑_{N/2 < n ≤ N} f(x+n-P(n)) h(x-P(n))`.  Writing `F = Ã_N^{**}(g,h)`
and `Π = Π_{≤l,≤d(l-Log N)}`, the paper needs the `ℓ²` bound

`‖(1 - Π) F‖_{ℓ²} ≤ (1 + C₁⟨l⟩) C₃ N^{d(1/2-1/p)} ‖g‖_{ℓ^p}`

on good major arcs, where the constant `C₃` comes from the `ℓ^p`-improving estimate for the
average `A_N^{n-P(n)}` (area A3 at `Q = P - X`) and `C₁⟨l⟩` from the Ionescu--Wainger multiplier
bound for `Π`.

The file proves the *elementary* part of this: the triangle inequality
`‖(1-Π)F‖₂ ≤ ‖F‖₂ + ‖Π F‖₂`, the projection bound `‖Π F‖₂ ≤ C₁⟨l⟩‖F‖₂` (taken as the
hypothesis `hProj`), and the single-scale `ℓ²` bound for `F` itself,

`‖Ã_N^{**}(g,h)‖_{ℓ²} ≤ C₃ N^{d(1/2-1/p)} ‖g‖_{ℓ^p}`,

which follows from the `ℓ^p`-improving estimate `hA3` by the pointwise domination
`‖Ã_N^{**}(g,h)(x)‖ ≤ N⁻¹ ∑_{n ≤ N} ‖g(x - (P-X)(n))‖` (valid since `‖h‖_∞ ≤ 1` and
`{N/2 < n ≤ N} ⊆ {1 ≤ n ≤ N}`, the latter because `N ≥ 1`).
-/

open MeasureTheory Polynomial
open scoped BigOperators ENNReal

set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A4Z

/-- **The norm of a finite sum of non-negative reals, viewed in `ℂ`.** -/
private lemma norm_finset_sum_ofReal {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ n ∈ s, 0 ≤ r n) : ‖∑ n ∈ s, ((r n : ℝ) : ℂ)‖ = ∑ n ∈ s, r n := by
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg hr)]

/-- **The pointwise domination of the second dual function.**  For `‖h‖_∞ ≤ 1` and `N ≥ 1`,
`‖Ã_N^{**}(f,h)(x)‖ ≤ N⁻¹ ∑_{n ≤ N} ‖f(x - (P-X)(n))‖`: the sum of `Ã_N^{**}` runs over
`{N/2 < n ≤ N} ⊆ {1 ≤ n ≤ N}`, its second factor is bounded by `1`, and
`x + n - P(n) = x - (P-X)(n)`. -/
private lemma norm_AhalfTranspose₂_le (N : ℕ) (hN : 1 ≤ N) (P : Polynomial ℤ) (f h : ℤ → ℂ)
    (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (y : ℤ) :
    ‖Work.Analysis.InverseTheory.AhalfTranspose₂ N P f h y‖
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖f (y - (P - Polynomial.X).eval (n : ℤ))‖ := by
  have hpoly : ∀ n : ℕ, (P - Polynomial.X).eval (n : ℤ) = P.eval (n : ℤ) - (n : ℤ) := fun n => by
    rw [Polynomial.eval_sub, Polynomial.eval_X]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
  have hsub : Finset.Ioc (N / 2) N ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    have h1 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
    omega
  have hS : ‖∑ n ∈ Finset.Ioc (N / 2) N,
        f (y + (n : ℤ) - P.eval (n : ℤ)) * h (y - P.eval (n : ℤ))‖
      ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖f (y + (n : ℤ) - P.eval (n : ℤ))‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hh _)
  have hcongr : ∀ n : ℕ, y + (n : ℤ) - P.eval (n : ℤ)
      = y - (P - Polynomial.X).eval (n : ℤ) := by
    intro n
    rw [hpoly n]
    ring
  have hsumle : ∑ n ∈ Finset.Ioc (N / 2) N, ‖f (y + (n : ℤ) - P.eval (n : ℤ))‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖f (y - (P - Polynomial.X).eval (n : ℤ))‖ := by
    have hm : ∑ n ∈ Finset.Ioc (N / 2) N, ‖f (y + (n : ℤ) - P.eval (n : ℤ))‖
        = ∑ n ∈ Finset.Ioc (N / 2) N, ‖f (y - (P - Polynomial.X).eval (n : ℤ))‖ :=
      Finset.sum_congr rfl (fun n _ => by rw [hcongr n])
    rw [hm]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => norm_nonneg _)
  have hc1 : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNinv]
  rw [Work.Analysis.InverseTheory.AhalfTranspose₂]
  have hstep1 : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ) * (∑ n ∈ Finset.Ioc (N / 2) N,
        f (y + (n : ℤ) - P.eval (n : ℤ)) * h (y - P.eval (n : ℤ)))‖
      = ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
        f (y + (n : ℤ) - P.eval (n : ℤ)) * h (y - P.eval (n : ℤ))‖ := norm_mul _ _
  have hstep2 : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
        f (y + (n : ℤ) - P.eval (n : ℤ)) * h (y - P.eval (n : ℤ))‖
      = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
        f (y + (n : ℤ) - P.eval (n : ℤ)) * h (y - P.eval (n : ℤ))‖ := by rw [hc1]
  have hstep3 : (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
        f (y + (n : ℤ) - P.eval (n : ℤ)) * h (y - P.eval (n : ℤ))‖
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        ‖f (y + (n : ℤ) - P.eval (n : ℤ))‖ := mul_le_mul_of_nonneg_left hS hNinv
  exact hstep1.le.trans (hstep2.le.trans
    (hstep3.trans (mul_le_mul_of_nonneg_left hsumle hNinv)))

theorem eLpNorm_sub_kmtProj_ahalfTransposeTwo_le (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {C₃ : ℝ} (hC₃ : 0 < C₃) (hA3 : ∀ (N : ℕ) (u : ℤ → ℂ), 1 ≤ N → MeasureTheory.eLpNorm (fun x : ℤ => (N : ℂ)⁻¹ * Finset.sum (Finset.Icc 1 N) (fun n => u (x - (P - Polynomial.X).eval (n : ℤ)))) 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal C₃ * ENNReal.ofReal ((N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p))) * MeasureTheory.eLpNorm u (ENNReal.ofReal p) MeasureTheory.Measure.count) {N : ℕ} (hN : 1 ≤ N) {g h : ℤ → ℂ} (hg : Work.KMTAreas.A5.BoundedZ g) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) {ρ : ℝ} {l : ℕ} {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hProj : MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N)) (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y)) 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal C₁ * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ) * MeasureTheory.eLpNorm (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2 MeasureTheory.Measure.count) : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h x - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N)) (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) x) 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal ((1 + C₁ * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * C₃ * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p))) * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by
    have h : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact inv_nonneg.mpr h.le
  have habnn : (0 : ℝ) ≤ (Work.Analysis.IWMultiplier.angleBracket l : ℝ) := by
    have h := Work.Analysis.IWMultiplier.one_le_angleBracket l
    exact le_trans zero_le_one (by exact_mod_cast h)
  have hc2 : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg N)]
  have hTnorm : ∀ y : ℤ, ‖∑ n ∈ Finset.Icc 1 N,
        ((‖g (y - (P - Polynomial.X).eval (n : ℤ))‖ : ℝ) : ℂ)‖
      = ∑ n ∈ Finset.Icc 1 N, ‖g (y - (P - Polynomial.X).eval (n : ℤ))‖ := fun y => by
    have h := norm_finset_sum_ofReal (Finset.Icc 1 N)
      (fun n : ℕ => ‖g (y - (P - Polynomial.X).eval (n : ℤ))‖) (fun n _ => norm_nonneg _)
    exact h
  -- (1) pointwise domination of `Ã_N^{**}(g,h)` by the average of `‖g ·‖`
  have hpt : ∀ y : ℤ, ‖Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y‖
      ≤ ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            ((‖g (y - (P - Polynomial.X).eval (n : ℤ))‖ : ℝ) : ℂ)‖ := by
    intro y
    refine (norm_AhalfTranspose₂_le N hN P g h hh y).trans ?_
    rw [norm_mul, hc2, hTnorm]
  have hmono : MeasureTheory.eLpNorm
        (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
        MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun y : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            ((‖g (y - (P - Polynomial.X).eval (n : ℤ))‖ : ℝ) : ℂ)) 2
          MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono (hf := by pw_aesm) hpt
  have hug : MeasureTheory.eLpNorm (fun y : ℤ => ((‖g y‖ : ℝ) : ℂ))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_congr_norm_ae (hf := by pw_aesm) (hg := by pw_aesm) (Filter.Eventually.of_forall fun y : ℤ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])
  -- (2) the single-scale `ℓ²` bound for `Ã_N^{**}(g,h)` from area A3
  have hcoef : ENNReal.ofReal (C₃ * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
      = ENNReal.ofReal C₃
        * ENNReal.ofReal ((N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p))) :=
    ENNReal.ofReal_mul hC₃.le
  have hFb : MeasureTheory.eLpNorm
        (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₃ * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
        * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    have hkey : ENNReal.ofReal C₃
          * ENNReal.ofReal ((N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
          * MeasureTheory.eLpNorm (fun y : ℤ => ((‖g y‖ : ℝ) : ℂ))
              (ENNReal.ofReal p) MeasureTheory.Measure.count
        = ENNReal.ofReal (C₃ * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
          * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
      rw [← hcoef, hug]
    exact hmono.trans ((hA3 N (fun y : ℤ => ((‖g y‖ : ℝ) : ℂ)) hN).trans hkey.le)
  -- (3) the triangle inequality `‖F - ΠF‖ ≤ ‖F‖ + ‖ΠF‖`
  have htri : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h x
        - Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N))
            (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) x) 2
        MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm
          (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
          MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l
            ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N))
            (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y)) 2
          MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_sub_le
      (f := fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y)
      (g := Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N))
              (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y))
      (by norm_num)
  -- (4) the assembly
  have hStep2 : MeasureTheory.eLpNorm
        (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
        MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l
            ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N))
            (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y)) 2
          MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm
          (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
          MeasureTheory.Measure.count
        + ENNReal.ofReal C₁ * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ)
          * MeasureTheory.eLpNorm
              (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
              MeasureTheory.Measure.count :=
    add_le_add_right hProj _
  have hStep3 : MeasureTheory.eLpNorm
        (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
        MeasureTheory.Measure.count
        + ENNReal.ofReal C₁ * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ)
          * MeasureTheory.eLpNorm
              (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
              MeasureTheory.Measure.count
      = (1 + ENNReal.ofReal C₁ * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
          * MeasureTheory.eLpNorm
              (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
              MeasureTheory.Measure.count := by
    rw [add_mul, one_mul]
  have heq : (1 + ENNReal.ofReal C₁
          * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        * (ENNReal.ofReal (C₃ * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
            * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count)
      = ENNReal.ofReal ((1 + C₁ * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * C₃
            * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
          * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    have h1 : ENNReal.ofReal (1 + C₁ * (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        = 1 + ENNReal.ofReal C₁
            * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ) := by
      rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hC₁ habnn), ENNReal.ofReal_one,
        ENNReal.ofReal_mul hC₁]
    rw [← mul_assoc, ← h1,
      ← ENNReal.ofReal_mul (add_nonneg zero_le_one (mul_nonneg hC₁ habnn)),
      show (1 + C₁ * (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
            * (C₃ * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
          = (1 + C₁ * (Work.Analysis.IWMultiplier.angleBracket l : ℝ)) * C₃
            * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)) by ring]
  have hStep4 : (1 + ENNReal.ofReal C₁
        * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        * MeasureTheory.eLpNorm
            (fun y : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P g h y) 2
            MeasureTheory.Measure.count
      ≤ (1 + ENNReal.ofReal C₁
          * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        * (ENNReal.ofReal (C₃ * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
            * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count) :=
    mul_le_mul_right hFb _
  exact htri.trans (hStep2.trans (hStep3.le.trans (hStep4.trans heq.le)))

end Work.KMTAreas.A4Z
