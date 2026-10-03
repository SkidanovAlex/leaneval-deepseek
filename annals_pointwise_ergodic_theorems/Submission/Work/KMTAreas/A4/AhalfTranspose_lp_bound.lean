import Mathlib
import Submission.Work.KMTAreas.A4.improvOneZDefs
import Submission.Work.KMTAreas.A7.ProjBound
import Submission.Port.Aesm

/-!
# The `l^2` bound for the minor-arc part of the first dual function `A*_N(h,g)`

Krause--Mirek--Tao, §5.1.  The first dual function of the halved average is

  `A*_N(h,g)(x) = N^{-1} sum_{N/2 < n <= N} h(x - n) g(x + P(n) - n)`.

Writing `F = A*_N(h,g)` and `Pi = Pi_{<=l,<=k}` (the Ionescu--Wainger projection `kmtProj ρ l k`),
the paper (in the form in which area `A4` consumes it) needs the `l^2` bound

  `||(1 - Pi) F||_{l^2} <= K <l> N^{d(1/2 - 1/p)} ||g||_{l^p}`   (`d = deg P`)

on good major arcs, for some `1 < p < 2`.

The proof is elementary once the two inputs of the contract are available:

* since `g(x + P(n) - n) = g(x - (X - P)(n))` and `||h||_infty <= 1`, the pointwise domination

    `||F(x)|| <= N^{-1} sum_{n <= N} ||g(x - (X-P)(n))||`

  turns the `l^p`-improving estimate of area `A3` for `Q = X - P` (`hA3`) into

    `||F||_{l^2} <= C_3 N^{d(1/2-1/p)} ||g||_{l^p}`;

* the Ionescu--Wainger multiplier theorem of area `A1` (`kmtProj_lp_bound_holds`) bounds the
  projection on `l^2` by `C_1 <l>`;

* the triangle inequality `||F - Pi F|| <= ||F|| + ||Pi F||` then gives the claim.

The overall constant is `(1 + C_1) C_3`.
-/

set_option maxHeartbeats 8000000

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4

/-- **The norm of a finite sum of non-negative reals, viewed in `ℂ`.** -/
private lemma norm_finset_sum_ofReal {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ n ∈ s, 0 ≤ r n) : ‖∑ n ∈ s, ((r n : ℝ) : ℂ)‖ = ∑ n ∈ s, r n := by
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg hr)]

/-- **Pointwise domination of the first dual function.**  If `‖h‖_∞ ≤ 1` and `N ≥ 1`, then
`‖A*_N(h,g)(x)‖ ≤ N⁻¹ ∑_{n ≤ N} ‖g(x - (X-P)(n))‖`: the sum of `A*_N` runs over
`{N/2 < n ≤ N} ⊆ {1 ≤ n ≤ N}`, its `h`-factor is bounded by `1`, and
`x + P(n) - n = x - (X-P)(n)`. -/
private lemma norm_AhalfTranspose_le_Icc (N : ℕ) (hN : 1 ≤ N) (P : Polynomial ℤ) (h g : ℤ → ℂ)
    (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (y : ℤ) :
    ‖AhalfTranspose N P h g y‖
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, ‖g (y - (Polynomial.X - P).eval (n : ℤ))‖ := by
  have hpoly : ∀ n : ℕ, (Polynomial.X - P).eval (n : ℤ) = (n : ℤ) - P.eval (n : ℤ) := fun n => by
    rw [Polynomial.eval_sub, Polynomial.eval_X]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
  have hsub : Finset.Ioc (N / 2) N ⊆ Finset.Icc 1 N := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    omega
  have hS : ‖∑ n ∈ Finset.Ioc (N / 2) N,
        h (y - (n : ℤ)) * g (y + P.eval (n : ℤ) - (n : ℤ))‖
      ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖g (y - (Polynomial.X - P).eval (n : ℤ))‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    have hc : y + P.eval (n : ℤ) - (n : ℤ) = y - (Polynomial.X - P).eval (n : ℤ) := by
      rw [hpoly n]; ring
    rw [norm_mul, hc]
    exact mul_le_of_le_one_left (norm_nonneg _) (hh _)
  have hsumle : ∑ n ∈ Finset.Ioc (N / 2) N, ‖g (y - (Polynomial.X - P).eval (n : ℤ))‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖g (y - (Polynomial.X - P).eval (n : ℤ))‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => norm_nonneg _)
  have hc1 : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNinv]
  rw [AhalfTranspose]
  have hmain : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ) * (∑ n ∈ Finset.Ioc (N / 2) N,
          h (y - (n : ℤ)) * g (y + P.eval (n : ℤ) - (n : ℤ)))‖
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          ‖g (y - (Polynomial.X - P).eval (n : ℤ))‖ := by
    rw [norm_mul, hc1]
    exact mul_le_mul_of_nonneg_left hS hNinv
  exact hmain.trans (mul_le_mul_of_nonneg_left hsumle hNinv)

theorem AhalfTranspose_lp_bound (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (hA3 : Work.KMTContract.PolyImproving (Polynomial.X - P)) : ∃ p : ℝ, 1 < p ∧ p < 2 ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ K : ℝ, 0 < K ∧ ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k → ∀ (N : ℕ), 1 ≤ N → ∀ (g h : ℤ → ℂ), (∀ x : ℤ, ‖h x‖ ≤ 1) → MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose N P h g x - Work.KMTContract.kmtProj ρ l k (Work.Analysis.InverseTheory.AhalfTranspose N P h g) x) 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal (K * (max 1 (l : ℝ)) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p))) * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨p, hp1, hp2, C3, hC3, hA3b⟩ := hA3
  have hXdeg : (Polynomial.X : ℤ[X]).natDegree < P.natDegree := by
    rw [Polynomial.natDegree_X]; omega
  have hdeg : (Polynomial.X - P).natDegree = P.natDegree :=
    Polynomial.natDegree_sub_eq_right_of_natDegree_lt hXdeg
  have hexpr : ((Polynomial.X - P).natDegree : ℝ) * (1 / 2 - 1 / p)
      = (P.natDegree : ℝ) * (1 / 2 - 1 / p) := by rw [hdeg]
  have hC3R : (0 : ℝ) < (C3 : ℝ) := by exact_mod_cast hC3
  refine ⟨p, hp1, hp2, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨Cρ, hCρ, C1, hC1, hproj⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_holds hA1 ρ hρ0 hρ1 2 (by norm_num)
  have hC1R : (0 : ℝ) < (C1 : ℝ) := by exact_mod_cast hC1
  refine ⟨Cρ, hCρ, (1 + (C1 : ℝ)) * (C3 : ℝ), by positivity, fun l k harc N hN g h hh => ?_⟩
  have hA3gen : ∀ (M : ℕ) (u : ℤ → ℂ), 1 ≤ M →
      MeasureTheory.eLpNorm (fun x : ℤ => (M : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 M,
          u (x - (Polynomial.X - P).eval (n : ℤ))) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C3 : ℝ)
            * ENNReal.ofReal ((M : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
            * MeasureTheory.eLpNorm u (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    intro M u hM
    have h := hA3b M u hM
    rw [← ENNReal.ofReal_coe_nnreal (p := C3), hexpr] at h
    exact h
  have hc2 : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg N)]
  have hTnorm : ∀ y : ℤ, ‖∑ n ∈ Finset.Icc 1 N,
        ((‖g (y - (Polynomial.X - P).eval (n : ℤ))‖ : ℝ) : ℂ)‖
      = ∑ n ∈ Finset.Icc 1 N, ‖g (y - (Polynomial.X - P).eval (n : ℤ))‖ := fun y =>
    norm_finset_sum_ofReal (Finset.Icc 1 N)
      (fun n : ℕ => ‖g (y - (Polynomial.X - P).eval (n : ℤ))‖) (fun n _ => norm_nonneg _)
  have hpt : ∀ y : ℤ, ‖AhalfTranspose N P h g y‖
      ≤ ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            ((‖g (y - (Polynomial.X - P).eval (n : ℤ))‖ : ℝ) : ℂ)‖ := by
    intro y
    refine (norm_AhalfTranspose_le_Icc N hN P h g hh y).trans ?_
    rw [norm_mul, hc2, hTnorm]
  have hmono : MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
        MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun y : ℤ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            ((‖g (y - (Polynomial.X - P).eval (n : ℤ))‖ : ℝ) : ℂ)) 2
          MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono (hf := by pw_aesm) hpt
  have hug : MeasureTheory.eLpNorm (fun y : ℤ => ((‖g y‖ : ℝ) : ℂ)) (ENNReal.ofReal p)
        MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_congr_norm_ae (hf := by pw_aesm) (hg := by pw_aesm) (Filter.Eventually.of_forall fun y : ℤ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])
  have hFb : MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((C3 : ℝ) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
        * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    have hcoef : ENNReal.ofReal (C3 : ℝ)
          * ENNReal.ofReal ((N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
        = ENNReal.ofReal ((C3 : ℝ) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p))) :=
      (ENNReal.ofReal_mul hC3R.le).symm
    have hkey : ENNReal.ofReal (C3 : ℝ)
          * ENNReal.ofReal ((N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
          * MeasureTheory.eLpNorm (fun y : ℤ => ((‖g y‖ : ℝ) : ℂ)) (ENNReal.ofReal p)
              MeasureTheory.Measure.count
        = ENNReal.ofReal ((C3 : ℝ) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
          * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
      rw [hcoef, hug]
    exact hmono.trans ((hA3gen N (fun y : ℤ => ((‖g y‖ : ℝ) : ℂ)) hN).trans hkey.le)
  have htri : MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
        - Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h g) x) 2
        MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
          MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k
            (AhalfTranspose N P h g)) 2 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_sub_le
      (f := fun y : ℤ => AhalfTranspose N P h g y)
      (g := Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h g)) (by norm_num)
  have hPj : MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k
        (fun y : ℤ => AhalfTranspose N P h g y)) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C1 : ℝ) * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ)
        * MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
            MeasureTheory.Measure.count := by
    simpa using hproj l k harc (fun y : ℤ => AhalfTranspose N P h g y)
  have hStep2 : MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
          MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k (AhalfTranspose N P h g)) 2
            MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
          MeasureTheory.Measure.count
        + ENNReal.ofReal (C1 : ℝ) * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ)
          * MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
              MeasureTheory.Measure.count :=
    add_le_add_right hPj _
  have hStep3 : MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
          MeasureTheory.Measure.count
        + ENNReal.ofReal (C1 : ℝ) * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ)
          * MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
              MeasureTheory.Measure.count
      = (1 + ENNReal.ofReal (C1 : ℝ)
            * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
          * MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
              MeasureTheory.Measure.count := by
    rw [add_mul, one_mul]
  have hStep4 : (1 + ENNReal.ofReal (C1 : ℝ)
          * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        * MeasureTheory.eLpNorm (fun y : ℤ => AhalfTranspose N P h g y) 2
            MeasureTheory.Measure.count
      ≤ (1 + ENNReal.ofReal (C1 : ℝ)
          * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        * (ENNReal.ofReal ((C3 : ℝ) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
            * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count) :=
    mul_le_mul_right hFb _
  have hang : ((Work.Analysis.IWMultiplier.angleBracket l : NNReal) : ℝ) = max 1 (l : ℝ) := by
    simp [Work.Analysis.IWMultiplier.angleBracket]
  have hangnn : (0 : ℝ) ≤ (Work.Analysis.IWMultiplier.angleBracket l : ℝ) := by positivity
  have hkey2 : ENNReal.ofReal (1 + (C1 : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        * ENNReal.ofReal ((C3 : ℝ) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
      ≤ ENNReal.ofReal ((1 + (C1 : ℝ)) * (C3 : ℝ) * (max 1 (l : ℝ))
          * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p))) := by
    rw [← ENNReal.ofReal_mul (add_nonneg zero_le_one (mul_nonneg hC1R.le hangnn))]
    apply ENNReal.ofReal_le_ofReal
    have hle1 : (1 : ℝ) ≤ (Work.Analysis.IWMultiplier.angleBracket l : ℝ) := by
      rw [hang]; exact le_max_left _ _
    have hprod : (1 + (C1 : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        ≤ (1 + (C1 : ℝ)) * (Work.Analysis.IWMultiplier.angleBracket l : ℝ) := by
      nlinarith [hle1, hC1R, hangnn]
    calc (1 + (C1 : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
          * ((C3 : ℝ) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
        ≤ ((1 + (C1 : ℝ)) * (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
          * ((C3 : ℝ) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p))) := by
          apply mul_le_mul_of_nonneg_right hprod
          positivity
      _ = (1 + (C1 : ℝ)) * (C3 : ℝ) * (max 1 (l : ℝ))
            * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)) := by
          rw [hang]; ring
  have h1 : ENNReal.ofReal (1 + (C1 : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
      = 1 + ENNReal.ofReal (C1 : ℝ)
          * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ) := by
    rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hC1R.le hangnn), ENNReal.ofReal_one,
      ENNReal.ofReal_mul hC1R.le]
  have hfin : (1 + ENNReal.ofReal (C1 : ℝ)
          * ENNReal.ofReal (Work.Analysis.IWMultiplier.angleBracket l : ℝ))
        * (ENNReal.ofReal ((C3 : ℝ) * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
            * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal ((1 + (C1 : ℝ)) * (C3 : ℝ) * (max 1 (l : ℝ))
            * (N : ℝ) ^ ((P.natDegree : ℝ) * (1 / 2 - 1 / p)))
          * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    rw [← mul_assoc, ← h1]
    exact mul_le_mul_left hkey2 _
  exact htri.trans (hStep2.trans (hStep3.le.trans (hStep4.trans hfin)))


end Work.KMTAreas.A4
