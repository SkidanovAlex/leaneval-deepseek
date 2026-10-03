import Mathlib
import Submission.Work.A7Hi2.SieveDefs
import Submission.Port.Aesm

/-!
# The decimated dilation variational estimate, uniform in the decimation

This module proves `Work.A7Hi2.decimDilVarUnif`: from the arithmetic-free real-scale lacunary
dilation estimate `Work.A7Hi2.DilVarRealScale` (the real-scale form of JSW Theorem 1.1), the
**decimated** pure dilation family

  `decimDilFam m₀ K d g m x = Σ'_j (1/σ_m) K (d j / σ_m) g (x - d j)`,  `σ_m = 2^{m₀+m}`,

satisfies the variational `ℓᵖ`-estimate with the *sharp* constant `C / d`, uniformly in the
decimation `d ≥ 1` and in the starting scale `m₀` (subject only to `d ≤ σ_0`):

  `‖Vʳ(m ↦ decimDilFam m₀ K d g m)‖_{ℓᵖ(ℤ)} ≤ (C/d) ‖g‖_{ℓᵖ(ℤ)}`.

## The proof

The only structural facts are the coset decomposition of a sum over `ℤ`
(`Work.A7Hi2.tsum_coset_decomp`) and the coset identity for the decimated family:

on the residue class `r + dℤ`, i.e. at the point `x = d s + r`, the decimated family is `1/d` times
a genuine (real-scale) lacunary dilation family with the rescaled scales `σ_m / d` applied to the
sampled function `t ↦ g (d t + r)`:

  `decimDilFam m₀ K d g m (d s + r) = (1/d) Σ'_j (1/τ_m) K (j/τ_m) g (d (s-j) + r)`,
  `τ_m = σ_m / d`.

Since `d ≤ 2^{m₀} ≤ σ_m`, the sequence `τ` satisfies `1 ≤ τ m` and `2 τ m ≤ τ (m+1)`, so
`DilVarRealScale` applies to each residue class; the `ℓᵖ`-norm over `ℤ` is the `ℓᵖ`-sum of the
norms over the `d` residue classes, and `(1/d)^p` is pulled out of the whole sum.  The analytic
content is entirely in `DilVarRealScale`.

This is the per-`d` input `Work.A7Hi2.DecimDilBound` of the sieve assembly
(`Submission/Work/A7Hi2/SieveAssembly.lean`).
-/

namespace Work.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## 1. Elementary bookkeeping for the `ℒᵖ`-seminorm on `ℤ` with the counting measure -/

/-- The `q`-th power of the `ℒᵖ`-seminorm (counting measure on `ℤ`) of an `ℝ≥0∞`-valued function
is the `ℝ≥0∞`-sum of the pointwise `q`-th powers. -/
private theorem eLpNorm_count_rpow_tsum_enn (V : ℤ → ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    (MeasureTheory.eLpNorm V (ENNReal.ofReal q) MeasureTheory.Measure.count) ^ q
      = ∑' x : ℤ, (V x) ^ q := by
  have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hqt : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt, ENNReal.toReal_ofReal hq.le]
  simp only [enorm_eq_self]
  rw [lintegral_count, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

/-- The `q`-th power of the `ℒᵖ`-seminorm (counting measure on `ℤ`) of a complex sequence is the
`ℝ≥0∞`-sum of the pointwise `q`-th powers of the norms. -/
private theorem eLpNorm_count_rpow_tsum_cplx (g : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    (MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count) ^ q
      = ∑' x : ℤ, ‖g x‖ₑ ^ q := by
  have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hqt : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt, ENNReal.toReal_ofReal hq.le]
  rw [lintegral_count, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

/-- The scalar identity `1/L = (1/d)·(1/(L/d))` (in `ℂ`, for `L ∈ ℝ`, `d ∈ ℕ`, `d ≥ 1`,
`L ≠ 0`), which converts the coefficient `1/σ_m` of the decimated family into the coefficient
`1/(σ_m/d)` of the rescaled lacunary family. -/
private lemma coset_coeff (L : ℝ) (d : ℕ) (hd : 1 ≤ d) (hL : L ≠ 0) :
    (1 / ((L : ℝ) : ℂ)) = (1 / (d : ℂ)) * (1 / (((L / (d : ℝ)) : ℝ) : ℂ)) := by
  have hLc : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast (show (d : ℝ) ≠ 0 by positivity)
  rw [Complex.ofReal_div, Complex.ofReal_natCast, one_div_div]
  field_simp

/-! ## 2. The coset identity for the decimated dilation family -/

/-- **The coset identity.**  On the residue class `r + dℤ`, the decimated dilation family at the
scales `σ_m = 2^{m₀+m}` equals `1/d` times the ordinary (real-scale) dilation family at the
rescaled lacunary scales `σ_m / d`, applied to the sampled function `t ↦ g (d t + r)`. -/
private theorem decimDilFam_coset_unif (m₀ : ℕ) (K : SchwartzMap ℝ ℂ) (d : ℕ) (hd : 1 ≤ d)
    (g : ℤ → ℂ) (σ : ℕ → ℝ) (hσ : ∀ n, σ n = (Work.KMTAreas.A7Hi.lpfScale m₀ n : ℝ) / (d : ℝ))
    (r s : ℤ) (m : ℕ) :
    decimDilFam m₀ K d g m ((d : ℤ) * s + r)
      = (1 / (d : ℂ)) * ∑' j : ℤ,
          (1 / σ m) * K ((j : ℝ) / (σ m)) * g ((d : ℤ) * (s - j) + r) := by
  have hL : ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℝ)) ≠ 0 := by
    have h1 : (0 : ℝ) < (Work.KMTAreas.A7Hi.lpfScale m₀ m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Work.KMTAreas.A7Hi.lpfScale_pos m₀ m))
    exact h1.ne'
  rw [decimDilFam, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have harg : (((d : ℤ) : ℝ) * (j : ℝ)) / (Work.KMTAreas.A7Hi.lpfScale m₀ m : ℝ)
      = (j : ℝ) / σ m := by
    rw [hσ m]
    field_simp
    push_cast
    ring
  have hgg : (d : ℤ) * s + r - (d : ℤ) * j = (d : ℤ) * (s - j) + r := by ring
  have hcoeff : (1 / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℝ) : ℂ))
      = (1 / (d : ℂ)) * (1 / ((σ m : ℝ) : ℂ)) := by
    rw [hσ m]
    exact coset_coeff _ d hd hL
  rw [harg, hgg, hcoeff]
  ring

/-! ## 3. The uniform decimated dilation estimate -/

/-- **The decimated dilation variational estimate, uniform in `d`.**  From the real-scale lacunary
dilation estimate `DilVarRealScale` (`h`), for every Schwartz kernel `K`, `2 < r` and `1 < p` there
is `C > 0` such that for every `d ≥ 1`, every `m₀` with `d ≤ lpfScale m₀ 0` and every `g : ℤ → ℂ`,

  `‖Vʳ(m ↦ Σ'_j (1/σ_m) K (d j / σ_m) g (· - d j))‖_{ℓᵖ(ℤ)} ≤ (C/d) ‖g‖_{ℓᵖ(ℤ)}`. -/
theorem decimDilVarUnif (h : Work.A7Hi2.DilVarRealScale) (K : SchwartzMap ℝ ℂ) (r : NNReal)
    (hr : 2 < r) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (m₀ : ℕ)
      (hm₀ : d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.A7Hi2.decimDilFam m₀ K d g m x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C / d) * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := h p hp r hr K
  refine ⟨C, hCpos, ?_⟩
  intro d hd m₀ hm₀ g
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  -- the rescaled lacunary scale sequence
  set σ : ℕ → ℝ := fun m => (Work.KMTAreas.A7Hi.lpfScale m₀ m : ℝ) / (d : ℝ) with hσdef
  have hσ : ∀ n, σ n = (Work.KMTAreas.A7Hi.lpfScale m₀ n : ℝ) / (d : ℝ) := fun n => by
    simp only [hσdef]
  -- the hypothesis `d ≤ σ_0` gives `1 ≤ σ_m` for every `m`
  have hσ1 : ∀ m : ℕ, 1 ≤ σ m := by
    intro m
    have hdm : d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ m := by
      refine le_trans hm₀ ?_
      rw [Work.KMTAreas.A7Hi.lpfScale, Work.KMTAreas.A7Hi.lpfScale]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hσ m, one_le_div hdR]
    exact_mod_cast hdm
  -- and `σ` is `2`-lacunary
  have hσ2 : ∀ m : ℕ, 2 * σ m ≤ σ (m + 1) := by
    intro m
    rw [hσ m, hσ (m + 1), ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hdR.le
    exact_mod_cast Work.KMTAreas.A7Hi.lpfScale_lacunary m₀ m
  -- on each residue class the decimated family is `1/d` times a genuine lacunary dilation family
  have hpoint : ∀ (rr : ℕ) (s : ℤ),
      (PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => decimDilFam m₀ K d g m ((d : ℤ) * s + (rr : ℤ)))) ^ p
      = ENNReal.ofReal ((1 / (d : ℝ)) ^ p) *
        (PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => ∑' j : ℤ, (1 / σ m) * K ((j : ℝ) / (σ m))
            * g ((d : ℤ) * (s - j) + (rr : ℤ)))) ^ p := by
    intro rr s
    have hfam : (fun m : ℕ => decimDilFam m₀ K d g m ((d : ℤ) * s + (rr : ℤ)))
        = (1 / (d : ℂ)) • (fun m : ℕ => ∑' j : ℤ, (1 / σ m) * K ((j : ℝ) / (σ m))
            * g ((d : ℤ) * (s - j) + (rr : ℤ))) := by
      funext m
      rw [Pi.smul_apply, smul_eq_mul]
      exact decimDilFam_coset_unif m₀ K d hd g σ hσ (rr : ℤ) s m
    have hnorm : (‖(1 / (d : ℂ))‖ₑ) ^ p = ENNReal.ofReal ((1 / (d : ℝ)) ^ p) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
      congr 1
      rw [norm_div, norm_one, Complex.norm_natCast]
    rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1,
        ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hnorm]
  -- the per-residue-class bound, from `DilVarRealScale`
  have hsumbound : ∀ rr : ℕ, (∑' s : ℤ, (PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => ∑' j : ℤ, (1 / σ m) * K ((j : ℝ) / (σ m))
          * g ((d : ℤ) * (s - j) + (rr : ℤ)))) ^ p)
      ≤ ENNReal.ofReal (C ^ p) * (∑' s : ℤ, ‖g ((d : ℤ) * s + (rr : ℤ))‖ₑ ^ p) := by
    intro rr
    have happ := hC σ hσ1 hσ2 (fun t : ℤ => g ((d : ℤ) * t + (rr : ℤ)))
    have h2 : (MeasureTheory.eLpNorm (fun s : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => ∑' j : ℤ, (1 / σ m) * K ((j : ℝ) / (σ m))
            * (fun t : ℤ => g ((d : ℤ) * t + (rr : ℤ))) (s - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p
      ≤ (ENNReal.ofReal C * MeasureTheory.eLpNorm (fun t : ℤ => g ((d : ℤ) * t + (rr : ℤ)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p :=
      ENNReal.rpow_le_rpow happ hp0.le
    rw [eLpNorm_count_rpow_tsum_enn _ hp0,
        ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
        ENNReal.ofReal_rpow_of_nonneg hCpos.le hp0.le,
        eLpNorm_count_rpow_tsum_cplx _ hp0] at h2
    exact h2
  -- the `p`-th power form of the target inequality
  have hmain : (∑' x : ℤ, (PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => decimDilFam m₀ K d g m x)) ^ p)
      ≤ ENNReal.ofReal ((C / (d : ℝ)) ^ p) * (∑' x : ℤ, ‖g x‖ₑ ^ p) := by
    rw [tsum_coset_decomp d hd (fun x : ℤ => (PointwiseErgodicTheorems.variationalNorm r
      (fun m : ℕ => decimDilFam m₀ K d g m x)) ^ p)]
    calc ∑ rr ∈ Finset.range d, (∑' s : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => decimDilFam m₀ K d g m ((d : ℤ) * s + (rr : ℤ)))) ^ p)
        = ∑ rr ∈ Finset.range d, ENNReal.ofReal ((1 / (d : ℝ)) ^ p) *
            (∑' s : ℤ, (PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => ∑' j : ℤ, (1 / σ m) * K ((j : ℝ) / (σ m))
                * g ((d : ℤ) * (s - j) + (rr : ℤ)))) ^ p) := by
          refine Finset.sum_congr rfl fun rr _ => ?_
          rw [tsum_congr (fun s => hpoint rr s), ENNReal.tsum_mul_left]
      _ ≤ ∑ rr ∈ Finset.range d, ENNReal.ofReal ((1 / (d : ℝ)) ^ p) *
            (ENNReal.ofReal (C ^ p) * (∑' s : ℤ, ‖g ((d : ℤ) * s + (rr : ℤ))‖ₑ ^ p)) := by
          refine Finset.sum_le_sum fun rr _ => ?_
          exact mul_le_mul_of_nonneg_left (hsumbound rr) bot_le
      _ = ENNReal.ofReal ((1 / (d : ℝ)) ^ p) * ENNReal.ofReal (C ^ p) *
            (∑ rr ∈ Finset.range d, ∑' s : ℤ, ‖g ((d : ℤ) * s + (rr : ℤ))‖ₑ ^ p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun rr _ => ?_
          rw [mul_assoc]
      _ = ENNReal.ofReal ((1 / (d : ℝ)) ^ p) * ENNReal.ofReal (C ^ p) *
            (∑' x : ℤ, ‖g x‖ₑ ^ p) := by
          rw [← tsum_coset_decomp d hd (fun x : ℤ => ‖g x‖ₑ ^ p)]
      _ = ENNReal.ofReal ((C / (d : ℝ)) ^ p) * (∑' x : ℤ, ‖g x‖ₑ ^ p) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (one_div_nonneg.mpr hdR.le) p),
              ← Real.mul_rpow (one_div_nonneg.mpr hdR.le) hCpos.le,
              show (1 / (d : ℝ)) * C = C / (d : ℝ) by ring]
  -- raise the target to the power `p` and use the strict monotonicity of `x ↦ x^p`
  have hgoal : (MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => decimDilFam m₀ K d g m x))
      (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p
      ≤ (ENNReal.ofReal (C / (d : ℝ)) * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
          MeasureTheory.Measure.count) ^ p := by
    rw [eLpNorm_count_rpow_tsum_enn _ hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
        ENNReal.ofReal_rpow_of_nonneg (div_nonneg hCpos.le hdR.le) hp0.le,
        eLpNorm_count_rpow_tsum_cplx _ hp0]
    exact hmain
  exact (ENNReal.rpow_le_rpow_iff hp0).mp hgoal

end

end Work.A7Hi2
