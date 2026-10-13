/-
Copyright: work module for the Elgindi finite-time singularity project.

# `LevelOneAsm/eigFun_span_dense`: density of the angular eigenfunctions on `Iθ`

The angular eigenfunctions `Θ_n(θ) = cos θ · p_n(sin θ)` of `EigBasis` (`p_n` the eigenpolynomials
of the Jacobi operator of `L₀`, spanning the odd polynomials) are orthogonal in `L²(cos θ dθ)` and
their span is dense: a function `f ∈ L²(Iθ, cos θ dθ)` which is orthogonal to all `Θ_n` (`n ≥ 1`)
vanishes a.e.

## The proof

The orthogonality `∫_{Iθ} f·Θ_n·cos θ = 0` reads `∫_{Iθ} f·cos²θ·p_n(sin θ) = 0`; since
`p_1, …, p_{k+1}` span the odd polynomials up to degree `2k+1` (`eigPoly_spans_odd`), linearity of
the integral gives

  `∫_{Iθ} f(θ)·cos²θ·sin^{2k+1}θ dθ = 0`   for all `k ≥ 0`.   `(∗)`

From `(∗)` one gets, by Weierstrass approximation on `[0,1]` (the test functions are
`sin θ · q(sin²θ)`, `q` a polynomial, and `∫|f|cos²θsin θ < ∞`),

  `∫_{Iθ} f(θ)·cos²θ·sin θ·h(sin²θ) dθ = 0`  for every continuous `h`.   `(∗∗)`

Now take a compact set `K ⊆ Iθ`.  Approximating the indicator of the compact set
`C = (θ ↦ sin²θ) '' K` from above by the continuous functions `v ↦ max 0 (1 - n·d(v,C))` and
letting `n → ∞` (dominated convergence, domination by `|f|cos²θsin θ ∈ L¹`) gives, using that
`θ ↦ sin²θ` is injective on `Iθ`,

  `∫_K f(θ)·cos²θ·sin θ dθ = 0`  for every compact `K ⊆ Iθ`.

The vanishing of the integrals of `f·cos²θ·sin θ` over all compact subsets of the interval gives
`f(θ)·cos²θ·sin θ = 0` for a.e. `θ ∈ Iθ` (`ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero`),
and since `cos²θ·sin θ ≠ 0` off the two endpoints `0, π/2` (a null set), `f = 0` a.e.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigBasis
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigPoly_spans_odd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-- Compatibility notation: in this Mathlib revision `AEMeasurable` is a root-level declaration
(the qualified name `MeasureTheory.AEMeasurable` does not resolve).  This notation is parse-time
only: it introduces no declaration and expands to the root-level `AEMeasurable`. -/
notation "MeasureTheory.AEMeasurable" => @AEMeasurable

noncomputable section

open scoped Real Topology Polynomial
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary facts about the interval -/

private lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩

private lemma sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin θ :=
  Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩

private lemma integrableOn_one_Iθ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Iθ :=
  integrableOn_const (μ := volume) (s := Iθ) (C := (1 : ℝ))
    (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

/-- A.e. point of `Iθ` is an interior point: the two endpoints form a null set. -/
private lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [MeasureTheory.ae_iff]
  change (volume.restrict Iθ) ((Set.Ioo 0 (Real.pi / 2))ᶜ) = 0
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
  have hnull : volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) volume
  refine MeasureTheory.measure_mono_null ?_ hnull
  intro θ hθ
  have h1 : θ ∈ Iθ := hθ.2
  have h2 : θ ∉ Set.Ioo 0 (Real.pi / 2) := hθ.1
  by_cases h : θ ≤ 0
  · exact Or.inl (le_antisymm h h1.1)
  · refine Or.inr (le_antisymm h1.2 (le_of_not_gt fun hc => ?_))
    exact absurd ⟨lt_of_not_ge h, hc⟩ h2

private lemma continuous_eigPoly (n : ℕ) : Continuous (eigPoly n) := by
  change Continuous (fun u : ℝ => ∑ k ∈ Finset.range n, eigCoef n k * u ^ (2 * k + 1))
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_id.pow _)

private lemma continuous_eigFun (n : ℕ) : Continuous (eigFun n) := by
  change Continuous (fun θ : ℝ => Real.cos θ * eigPoly n (Real.sin θ))
  exact Real.continuous_cos.mul ((continuous_eigPoly n).comp Real.continuous_sin)

/-! ## Integrability of the pieces -/

/-- `|f|·cos θ` is integrable on `Iθ` as soon as `f²cos θ` is (and `f` is a.e. measurable). -/
private lemma abs_f_cos_integrable {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Iθ) :
    IntegrableOn (fun θ => |f θ| * Real.cos θ) Iθ := by
  have hmaj : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Real.cos θ + 1) Iθ :=
    hf.add integrableOn_one_Iθ
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · exact (hme.abs.mul Real.continuous_cos.aemeasurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (cos_nonneg_of_mem_Iθ hθ)]
    have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
    have hle1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have h3 : 0 ≤ Real.cos θ * (|f θ| - 1) ^ 2 + (1 - Real.cos θ) := by
      have h4 := mul_nonneg hc (sq_nonneg (|f θ| - 1))
      linarith
    have h4 : Real.cos θ * (|f θ| - 1) ^ 2 + (1 - Real.cos θ)
        = (f θ) ^ 2 * Real.cos θ - 2 * |f θ| * Real.cos θ + 1 := by
      rw [show (|f θ| - 1) ^ 2 = |f θ| ^ 2 - 2 * |f θ| + 1 from by ring, sq_abs]
      ring
    have h5 : |f θ| * Real.cos θ ≤ ((f θ) ^ 2 * Real.cos θ + 1) / 2 := by
      linarith [h3, h4]
    have h6 : ((f θ) ^ 2 * Real.cos θ + 1) / 2 ≤ (f θ) ^ 2 * Real.cos θ + 1 := by
      have h7 : 0 ≤ (f θ) ^ 2 * Real.cos θ + 1 := by
        have h8 := mul_nonneg (sq_nonneg (f θ)) hc
        linarith
      linarith
    linarith [h5, h6]

/-- Multiplying `f` by a function bounded by `C·cos θ` preserves integrability on `Iθ`. -/
private lemma integrableOn_f_mul_le_cos {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf1 : IntegrableOn (fun θ => |f θ| * Real.cos θ) Iθ) {C : ℝ} (hC : 0 ≤ C) {g : ℝ → ℝ}
    (hgm : AEMeasurable g (volume.restrict Iθ))
    (hbd : ∀ θ ∈ Iθ, |g θ| ≤ C * Real.cos θ) :
    IntegrableOn (fun θ => f θ * g θ) Iθ := by
  have hmaj : IntegrableOn (fun θ : ℝ => C * (|f θ| * Real.cos θ)) Iθ := hf1.const_mul C
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · exact (hme.mul hgm).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |f θ| * |g θ| ≤ |f θ| * (C * Real.cos θ) :=
      mul_le_mul_of_nonneg_left (hbd θ hθ) (abs_nonneg _)
    calc |f θ| * |g θ| ≤ |f θ| * (C * Real.cos θ) := h1
      _ = C * (|f θ| * Real.cos θ) := by ring

/-- The eigenfunctions are bounded by a multiple of `cos θ` on `Iθ`. -/
private lemma abs_eigFun_le (n : ℕ) :
    ∀ θ ∈ Iθ, |eigFun n θ| ≤ (∑ k ∈ Finset.range n, |eigCoef n k|) * Real.cos θ := by
  intro θ hθ
  have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hpoly : |eigPoly n (Real.sin θ)| ≤ ∑ k ∈ Finset.range n, |eigCoef n k| := by
    rw [eigPoly]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [abs_mul, abs_pow]
    have hsk : |Real.sin θ| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
    calc |eigCoef n k| * |Real.sin θ| ^ (2 * k + 1)
        ≤ |eigCoef n k| * 1 := mul_le_mul_of_nonneg_left hsk (abs_nonneg _)
      _ = |eigCoef n k| := mul_one _
  rw [eigFun, abs_mul, abs_of_nonneg hc]
  calc Real.cos θ * |eigPoly n (Real.sin θ)|
      ≤ Real.cos θ * (∑ k ∈ Finset.range n, |eigCoef n k|) :=
        mul_le_mul_of_nonneg_left hpoly hc
    _ = (∑ k ∈ Finset.range n, |eigCoef n k|) * Real.cos θ := by ring

private lemma integrableOn_f_eigFun_cos {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Iθ) (n : ℕ) :
    IntegrableOn (fun θ => f θ * eigFun n θ * Real.cos θ) Iθ := by
  have hf1 := abs_f_cos_integrable hme hf
  have hC : (0 : ℝ) ≤ ∑ k ∈ Finset.range n, |eigCoef n k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have h := integrableOn_f_mul_le_cos hme hf1 hC
    (g := fun θ => eigFun n θ * Real.cos θ)
    (((continuous_eigFun n).mul Real.continuous_cos).aemeasurable) (fun θ hθ => ?_)
  · simpa [mul_assoc] using h
  · have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
    have hle1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have h1 := abs_eigFun_le n θ hθ
    rw [abs_mul, abs_of_nonneg hc]
    calc |eigFun n θ| * Real.cos θ
        ≤ ((∑ k ∈ Finset.range n, |eigCoef n k|) * Real.cos θ) * Real.cos θ :=
          mul_le_mul_of_nonneg_right h1 hc
      _ ≤ (∑ k ∈ Finset.range n, |eigCoef n k|) * Real.cos θ := by
          rw [show ((∑ k ∈ Finset.range n, |eigCoef n k|) * Real.cos θ) * Real.cos θ
              = (∑ k ∈ Finset.range n, |eigCoef n k|) * (Real.cos θ * Real.cos θ) from by ring]
          exact mul_le_mul_of_nonneg_left (by nlinarith [hc, hle1]) hC

/-- Absolute value of the angular weight times a factor. -/
private lemma abs_cos2_sin_mul {θ : ℝ} (hθ : θ ∈ Iθ) (X : ℝ) :
    |Real.cos θ ^ 2 * Real.sin θ * X| = Real.cos θ ^ 2 * |Real.sin θ| * |X| := by
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.cos θ ^ 2)] <;> ring

/-- Absolute value of `f` times the angular weight times a factor. -/
private lemma abs_f_cos2_sin_mul {f : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Iθ) (X : ℝ) :
    |f θ * Real.cos θ ^ 2 * Real.sin θ * X|
      = (|f θ| * Real.cos θ ^ 2 * Real.sin θ) * |X| := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.cos θ ^ 2),
    abs_of_nonneg (sin_nonneg_of_mem_Iθ hθ)] <;> ring

/-- The moment integrands of `(∗)`. -/
private lemma integrableOn_f_moment {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Iθ) (k : ℕ) :
    IntegrableOn (fun θ => f θ * Real.cos θ ^ 2 * (Real.sin θ) ^ (2 * k + 1)) Iθ := by
  have hf1 := abs_f_cos_integrable hme hf
  have h := integrableOn_f_mul_le_cos hme hf1 (C := 1) zero_le_one
    (g := fun θ => Real.cos θ ^ 2 * (Real.sin θ) ^ (2 * k + 1))
    (((Real.continuous_cos.pow 2).mul (Real.continuous_sin.pow (2 * k + 1))).aemeasurable) (fun θ hθ => ?_)
  · simpa [mul_assoc] using h
  · have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
    have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg hc, one_mul]
    have hspow : |Real.sin θ| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
    have hcos2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc, Real.cos_le_one θ]
    calc Real.cos θ ^ 2 * |Real.sin θ| ^ (2 * k + 1)
        ≤ Real.cos θ ^ 2 * 1 := mul_le_mul_of_nonneg_left hspow (by positivity)
      _ ≤ Real.cos θ := by simpa using hcos2

/-- The dominating integrand for the DCT argument. -/
private lemma integrableOn_abs_f_cos2_sin {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Iθ) :
    IntegrableOn (fun θ => |f θ| * Real.cos θ ^ 2 * Real.sin θ) Iθ := by
  have hf1 := abs_f_cos_integrable hme hf
  refine MeasureTheory.Integrable.mono' hf1 ?_ ?_
  · have hg : AEMeasurable (fun θ : ℝ => |f θ| * (Real.cos θ ^ 2 * Real.sin θ))
        (volume.restrict Iθ) :=
      (hme.abs).mul ((Real.continuous_cos.pow 2).mul Real.continuous_sin).aemeasurable
    simpa only [mul_assoc] using hg.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
    have hs : 0 ≤ Real.sin θ := sin_nonneg_of_mem_Iθ hθ
    have hcos2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc, Real.cos_le_one θ]
    have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.cos θ ^ 2), abs_of_nonneg hs]
    calc |f θ| * Real.cos θ ^ 2 * Real.sin θ ≤ |f θ| * Real.cos θ * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hcos2 (abs_nonneg _)) hsin1 hs ?_
          positivity
      _ = |f θ| * Real.cos θ := by ring

/-- `f·cos²θ·sin θ` is integrable on `Iθ`. -/
private lemma integrableOn_f_cos2_sin {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Iθ) :
    IntegrableOn (fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ) Iθ := by
  have h := integrableOn_f_mul_le_cos hme (abs_f_cos_integrable hme hf) (C := 1) zero_le_one
    (g := fun θ => Real.cos θ ^ 2 * Real.sin θ)
    (((Real.continuous_cos.pow 2).mul Real.continuous_sin).aemeasurable) (fun θ hθ => ?_)
  · simpa [mul_assoc] using h
  · have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
    have hcos2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc, Real.cos_le_one θ]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.cos θ ^ 2),
      abs_of_nonneg (sin_nonneg_of_mem_Iθ hθ), one_mul]
    calc Real.cos θ ^ 2 * Real.sin θ ≤ Real.cos θ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.sin_le_one θ) (by positivity)
      _ ≤ Real.cos θ := by simpa using hcos2

/-! ## The moments `(∗)` -/

/-- **The odd moments.**  Orthogonality to all eigenfunctions gives the vanishing of the integrals
of `f·cos²θ·sin^{2k+1}θ`. -/
private lemma moment_odd {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Iθ)
    (horth : ∀ n : ℕ, 1 ≤ n → (∫ θ in Iθ, f θ * eigFun n θ * Real.cos θ) = 0) (k : ℕ) :
    (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * (Real.sin θ) ^ (2 * k + 1)) = 0 := by
  obtain ⟨a, ha⟩ := eigPoly_spans_odd k
  have key : ∀ θ : ℝ, f θ * Real.cos θ ^ 2 * (Real.sin θ) ^ (2 * k + 1)
      = ∑ j ∈ Finset.range (k + 1), a j * (f θ * eigFun (j + 1) θ * Real.cos θ) := by
    intro θ
    rw [ha (Real.sin θ), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [eigFun]
    ring
  calc (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * (Real.sin θ) ^ (2 * k + 1))
      = ∫ θ in Iθ, ∑ j ∈ Finset.range (k + 1),
          a j * (f θ * eigFun (j + 1) θ * Real.cos θ) :=
        integral_congr_ae (Eventually.of_forall key)
    _ = ∑ j ∈ Finset.range (k + 1),
          a j * (∫ θ in Iθ, f θ * eigFun (j + 1) θ * Real.cos θ) := by
        rw [MeasureTheory.integral_finsetSum]
        · refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [MeasureTheory.integral_const_mul]
        · intro j _
          exact (integrableOn_f_eigFun_cos hme hf (j + 1)).const_mul (a j)
    _ = 0 := by
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [horth (j + 1) (by omega), mul_zero]

/-- **Polynomial test functions.**  `∫ f·cos²θ·sin θ·p(sin²θ) = 0` for every polynomial `p`. -/
private lemma moment_poly {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Iθ)
    (horth : ∀ n : ℕ, 1 ≤ n → (∫ θ in Iθ, f θ * eigFun n θ * Real.cos θ) = 0)
    (p : ℝ[X]) :
    (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ * p.eval (Real.sin θ ^ 2)) = 0 := by
  have key : ∀ θ : ℝ, f θ * Real.cos θ ^ 2 * Real.sin θ * p.eval (Real.sin θ ^ 2)
      = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k *
          (f θ * Real.cos θ ^ 2 * (Real.sin θ) ^ (2 * k + 1)) := by
    intro θ
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← pow_mul, show Real.sin θ ^ (2 * k + 1) = Real.sin θ ^ (2 * k) * Real.sin θ from
      by rw [pow_succ]]
    ring
  calc (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ * p.eval (Real.sin θ ^ 2))
      = ∫ θ in Iθ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k *
          (f θ * Real.cos θ ^ 2 * (Real.sin θ) ^ (2 * k + 1)) :=
        integral_congr_ae (Eventually.of_forall key)
    _ = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k *
          (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * (Real.sin θ) ^ (2 * k + 1)) := by
        rw [MeasureTheory.integral_finsetSum]
        · refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [MeasureTheory.integral_const_mul]
        · intro k _
          exact (integrableOn_f_moment hme hf k).const_mul (p.coeff k)
    _ = 0 := by
        refine Finset.sum_eq_zero (fun k _ => ?_)
        rw [moment_odd hme hf horth k, mul_zero]

/-- `|p.eval v|` is bounded on `[0,1]` by the sum of the absolute values of the coefficients. -/
private lemma abs_poly_eval_le (p : ℝ[X]) :
    ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |p.eval v| ≤ ∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k| := by
  intro v hv
  rw [Polynomial.eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [abs_mul, abs_pow]
  have hv1 : |v| ≤ 1 := by rw [abs_of_nonneg hv.1]; exact hv.2
  calc |p.coeff k| * |v| ^ k ≤ |p.coeff k| * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hv1) (abs_nonneg _)
    _ = |p.coeff k| := mul_one _

private lemma integrableOn_f_poly {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf1 : IntegrableOn (fun θ => |f θ| * Real.cos θ) Iθ) (p : ℝ[X]) :
    IntegrableOn (fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ * p.eval (Real.sin θ ^ 2)) Iθ := by
  have hC : (0 : ℝ) ≤ ∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hsin2 : Continuous (fun θ : ℝ => Real.sin θ ^ 2) := Real.continuous_sin.pow 2
  have hcontg : Continuous
      (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin θ * p.eval (Real.sin θ ^ 2)) :=
    ((Real.continuous_cos.pow 2).mul Real.continuous_sin).mul
      ((Polynomial.continuous p).comp hsin2)
  have h := integrableOn_f_mul_le_cos hme hf1 hC
    (g := fun θ => Real.cos θ ^ 2 * Real.sin θ * p.eval (Real.sin θ ^ 2))
    hcontg.aemeasurable (fun θ hθ => ?_)
  · simpa [mul_assoc] using h
  · have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
    have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hp : |p.eval (Real.sin θ ^ 2)| ≤ ∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k| :=
      abs_poly_eval_le p _ ⟨by positivity, by nlinarith [Real.sin_sq_le_one θ]⟩
    have hcos2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc, Real.cos_le_one θ]
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.cos θ ^ 2)]
    calc Real.cos θ ^ 2 * |Real.sin θ| * |p.eval (Real.sin θ ^ 2)|
        ≤ Real.cos θ ^ 2 * 1 * (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hp (abs_nonneg _) (by positivity)
      _ = (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|) * (Real.cos θ ^ 2 * 1) := by ring
      _ ≤ (∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|) * Real.cos θ := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          simpa using hcos2

private lemma le_zero_of_forall_pos_le_mul {y D : ℝ} (hD : 0 ≤ D)
    (h : ∀ ε : ℝ, 0 < ε → y ≤ ε * D) : y ≤ 0 := by
  rcases eq_or_lt_of_le hD with hD0 | hDpos
  · have h1 := h 1 zero_lt_one
    rw [← hD0, mul_zero] at h1
    exact h1
  · by_contra hcon
    push_neg at hcon
    have hε : 0 < y / (2 * (D + 1)) := by positivity
    have h1 : y ≤ y / (2 * (D + 1)) * D := h _ hε
    have hD1 : (0 : ℝ) < D + 1 := by linarith
    have h2 : y / (2 * (D + 1)) * (2 * (D + 1)) = y :=
      div_mul_cancel₀ y (by positivity)
    have h3 : y / (2 * (D + 1)) * D < y / (2 * (D + 1)) * (2 * (D + 1)) := by
      refine mul_lt_mul_of_pos_left ?_ hε
      linarith
    rw [h2] at h3
    exact absurd h1 (not_le.mpr h3)

/-! ## Continuous test functions `(∗∗)` -/

/-- **Continuous test functions.**  `∫ f·cos²θ·sin θ·h(sin²θ) = 0` for every continuous `h`. -/
private lemma moment_continuous {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Iθ)
    (horth : ∀ n : ℕ, 1 ≤ n → (∫ θ in Iθ, f θ * eigFun n θ * Real.cos θ) = 0)
    {h : ℝ → ℝ} (hh : Continuous h) :
    (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ * h (Real.sin θ ^ 2)) = 0 := by
  have hf1 := abs_f_cos_integrable hme hf
  have hD : 0 ≤ ∫ θ in Iθ, |f θ| * Real.cos θ ^ 2 * Real.sin θ := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (sin_nonneg_of_mem_Iθ hθ)
  have key : ∀ ε : ℝ, 0 < ε →
      |∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ * h (Real.sin θ ^ 2)|
        ≤ ε * ∫ θ in Iθ, |f θ| * Real.cos θ ^ 2 * Real.sin θ := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 h hh.continuousOn ε hε
    have hA : IntegrableOn (fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ *
        p.eval (Real.sin θ ^ 2)) Iθ := integrableOn_f_poly hme hf1 p
    have hmem : ∀ θ ∈ Iθ, |h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2)| ≤ ε := by
      intro θ _
      have h1 : Real.sin θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by positivity, by nlinarith [Real.sin_sq_le_one θ]⟩
      have := hp _ h1
      rw [abs_sub_comm] at this
      exact this.le
    have hB : IntegrableOn (fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ *
        (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2))) Iθ := by
      have hsin2 : Continuous (fun θ : ℝ => Real.sin θ ^ 2) := Real.continuous_sin.pow 2
      have hcontg : Continuous (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin θ *
          (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2))) :=
        ((Real.continuous_cos.pow 2).mul Real.continuous_sin).mul
          ((hh.comp hsin2).sub ((Polynomial.continuous p).comp hsin2))
      have h := integrableOn_f_mul_le_cos hme hf1 (C := ε) hε.le
        (g := fun θ => Real.cos θ ^ 2 * Real.sin θ *
          (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2)))
        hcontg.aemeasurable (fun θ hθ => ?_)
      · simpa [mul_assoc] using h
      · have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
        have hb := hmem θ hθ
        have hcos2 : Real.cos θ ^ 2 ≤ Real.cos θ := by
          nlinarith [cos_nonneg_of_mem_Iθ hθ, Real.cos_le_one θ]
        rw [abs_cos2_sin_mul hθ]
        calc Real.cos θ ^ 2 * |Real.sin θ| *
              |h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2)|
            ≤ Real.cos θ ^ 2 * 1 * ε :=
              mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hb
                (abs_nonneg _) (by positivity)
          _ ≤ ε * Real.cos θ := by
              rw [show Real.cos θ ^ 2 * 1 * ε = ε * Real.cos θ ^ 2 from by ring]
              exact mul_le_mul_of_nonneg_left hcos2 hε.le
    have hsplit : (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ * h (Real.sin θ ^ 2))
        = (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ * p.eval (Real.sin θ ^ 2))
          + ∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ *
              (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2)) := by
      rw [← MeasureTheory.integral_add hA hB]
      exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => by ring)
    rw [hsplit, moment_poly hme hf horth p, zero_add]
    have hstep1 : |∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ *
            (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2))|
        ≤ ∫ θ in Iθ, |f θ * Real.cos θ ^ 2 * Real.sin θ *
            (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2))| := by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
          (fun θ : ℝ => f θ * Real.cos θ ^ 2 * Real.sin θ *
            (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2)))
    calc |∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ *
            (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2))|
        ≤ ∫ θ in Iθ, |f θ * Real.cos θ ^ 2 * Real.sin θ *
            (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2))| := hstep1
      _ ≤ ∫ θ in Iθ, ε * (|f θ| * Real.cos θ ^ 2 * Real.sin θ) := by
          refine MeasureTheory.integral_mono_ae hB.abs
            ((integrableOn_abs_f_cos2_sin hme hf).const_mul ε) ?_
          filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
          have hb := hmem θ hθ
          have hcs : 0 ≤ |f θ| * Real.cos θ ^ 2 * Real.sin θ :=
            mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (sin_nonneg_of_mem_Iθ hθ)
          have hfac : |f θ * Real.cos θ ^ 2 * Real.sin θ *
                (h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2))|
              = (|f θ| * Real.cos θ ^ 2 * Real.sin θ) *
                |h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2)| :=
            abs_f_cos2_sin_mul hθ _
          rw [hfac]
          calc (|f θ| * Real.cos θ ^ 2 * Real.sin θ) *
                |h (Real.sin θ ^ 2) - p.eval (Real.sin θ ^ 2)|
              ≤ (|f θ| * Real.cos θ ^ 2 * Real.sin θ) * ε :=
                mul_le_mul_of_nonneg_left hb hcs
            _ = ε * (|f θ| * Real.cos θ ^ 2 * Real.sin θ) := by ring
      _ = ε * ∫ θ in Iθ, |f θ| * Real.cos θ ^ 2 * Real.sin θ :=
          MeasureTheory.integral_const_mul ε _
  have habs : |∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ * h (Real.sin θ ^ 2)| ≤ 0 :=
    le_zero_of_forall_pos_le_mul hD key
  exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))

/-! ## Compact sets -/

/-- **Compact sets.**  `∫_K f·cos²θ·sin θ = 0` for every compact `K ⊆ Iθ`. -/
private lemma moment_compact {f : ℝ → ℝ}
    (hme : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Iθ)
    (horth : ∀ n : ℕ, 1 ≤ n → (∫ θ in Iθ, f θ * eigFun n θ * Real.cos θ) = 0)
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Iθ) :
    (∫ θ in K, f θ * Real.cos θ ^ 2 * Real.sin θ) = 0 := by
  classical
  have hbnd := integrableOn_abs_f_cos2_sin hme hf
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  set C : Set ℝ := (fun θ => Real.sin θ ^ 2) '' K with hCdef
  have hCcomp : IsCompact C := hK.image (Real.continuous_sin.pow 2)
  have hCne : C.Nonempty := hKne.image _
  have hCclosed : IsClosed C := hCcomp.isClosed
  have hCmem : ∀ θ ∈ Iθ, θ ∈ K ↔ Real.sin θ ^ 2 ∈ C := by
    intro θ hθ
    constructor
    · intro hθK
      exact ⟨θ, hθK, rfl⟩
    · rintro ⟨k, hkK, hk⟩
      have hkI : k ∈ Iθ := hKI hkK
      have h1 : 0 ≤ Real.sin θ := sin_nonneg_of_mem_Iθ hθ
      have h2 : 0 ≤ Real.sin k := sin_nonneg_of_mem_Iθ hkI
      have hsin : Real.sin θ = Real.sin k := by
        have hprod : (Real.sin θ - Real.sin k) * (Real.sin θ + Real.sin k) = 0 := by
          nlinarith [hk]
        rcases mul_eq_zero.mp hprod with h | h
        · linarith
        · linarith
      have hθmem : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
      have hkmem : k ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hkI.1, Real.pi_pos], by linarith [hkI.2]⟩
      have hθk : θ = k := Real.strictMonoOn_sin.injOn hθmem hkmem hsin
      rw [hθk]
      exact hkK
  have hlim : ∀ᵐ θ ∂(volume.restrict Iθ),
      Tendsto (fun n : ℕ => f θ * Real.cos θ ^ 2 * Real.sin θ *
          max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C)) atTop
        (𝓝 (f θ * Real.cos θ ^ 2 * Real.sin θ *
          (if Real.sin θ ^ 2 ∈ C then 1 else 0))) := by
    refine Eventually.of_forall (fun θ => ?_)
    have h1 : Tendsto (fun n : ℕ => max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C))
        atTop (𝓝 (if Real.sin θ ^ 2 ∈ C then 1 else 0)) := by
      by_cases hv : Real.sin θ ^ 2 ∈ C
      · have hz : Metric.infDist (Real.sin θ ^ 2) C = 0 :=
          Metric.infDist_zero_of_mem_closure (by rw [hCclosed.closure_eq]; exact hv)
        have hval1 : ∀ n : ℕ,
            max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C) = 1 := by
          intro n
          rw [hz, mul_zero, sub_zero]
          exact max_eq_right zero_le_one
        have heq : (fun n : ℕ => max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C))
            =ᶠ[atTop] fun _ => (if Real.sin θ ^ 2 ∈ C then 1 else 0) := by
          rw [if_pos hv]
          exact Filter.Eventually.of_forall hval1
        exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
      · have hpos : 0 < Metric.infDist (Real.sin θ ^ 2) C :=
          (hCclosed.notMem_iff_infDist_pos hCne).mp hv
        have hev : ∀ᶠ n : ℕ in atTop, 1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C < 0 := by
          refine Filter.eventually_atTop.mpr ⟨⌈(Metric.infDist (Real.sin θ ^ 2) C)⁻¹⌉₊ + 1,
            fun n hn => ?_⟩
          have hN : (Metric.infDist (Real.sin θ ^ 2) C)⁻¹ < (n : ℝ) := by
            have h1 : ((⌈(Metric.infDist (Real.sin θ ^ 2) C)⁻¹⌉₊ : ℕ) : ℝ)
                ≥ (Metric.infDist (Real.sin θ ^ 2) C)⁻¹ := Nat.le_ceil _
            have h2 : ((⌈(Metric.infDist (Real.sin θ ^ 2) C)⁻¹⌉₊ + 1 : ℕ) : ℝ)
                ≤ (n : ℝ) := by exact_mod_cast hn
            push_cast at h2
            linarith
          have hnd : 1 < (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C := by
            have := mul_lt_mul_of_pos_right hN hpos
            rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at this
          linarith
        have heq : (fun n : ℕ => max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C))
            =ᶠ[atTop] fun _ => (if Real.sin θ ^ 2 ∈ C then 1 else 0) := by
          rw [if_neg hv]
          filter_upwards [hev] with n hn
          exact max_eq_left (le_of_lt hn)
        exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
    exact h1.const_mul _
  have hcont1 : ∀ n : ℕ, Continuous (fun v : ℝ =>
      max 0 (1 - (n : ℝ) * Metric.infDist v C)) := by
    intro n
    refine Continuous.max continuous_const ?_
    refine Continuous.sub continuous_const ?_
    exact Continuous.mul continuous_const (Metric.continuous_infDist_pt C)
  have hcont : ∀ n : ℕ, Continuous (fun θ : ℝ =>
      max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C)) := fun n =>
    (hcont1 n).comp (Real.continuous_sin.pow 2)
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ *
        max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C)) (volume.restrict Iθ) := by
    intro n
    have hme' : AEMeasurable (fun θ : ℝ => f θ * Real.cos θ ^ 2 * Real.sin θ *
        max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C)) (volume.restrict Iθ) :=
      ((hme.mul (Real.continuous_cos.pow 2).aemeasurable).mul
        Real.continuous_sin.aemeasurable).mul (hcont n).aemeasurable
    exact hme'.aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ θ ∂(volume.restrict Iθ),
      ‖f θ * Real.cos θ ^ 2 * Real.sin θ *
        max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C)‖
        ≤ |f θ| * Real.cos θ ^ 2 * Real.sin θ := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
    have hs : 0 ≤ Real.sin θ := sin_nonneg_of_mem_Iθ hθ
    have hmax0 : 0 ≤ max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C) :=
      le_max_left _ _
    have hmax1 : max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C) ≤ 1 := by
      refine max_le zero_le_one ?_
      have hnn : 0 ≤ Metric.infDist (Real.sin θ ^ 2) C := Metric.infDist_nonneg
      have : 0 ≤ (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C :=
        mul_nonneg (Nat.cast_nonneg n) hnn
      linarith
    have hfac : |f θ * Real.cos θ ^ 2 * Real.sin θ|
        = |f θ| * Real.cos θ ^ 2 * Real.sin θ := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.cos θ ^ 2),
        abs_of_nonneg hs]
    rw [Real.norm_eq_abs, abs_mul, hfac, abs_of_nonneg hmax0]
    calc |f θ| * Real.cos θ ^ 2 * Real.sin θ *
          max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C)
        ≤ |f θ| * Real.cos θ ^ 2 * Real.sin θ * 1 :=
          mul_le_mul_of_nonneg_left hmax1
            (mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) hs)
      _ = |f θ| * Real.cos θ ^ 2 * Real.sin θ := mul_one _
  have hFdiff : ∀ n : ℕ, (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ *
      max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C)) = 0 := by
    intro n
    exact moment_continuous hme hf horth (hcont1 n)
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun θ : ℝ => |f θ| * Real.cos θ ^ 2 * Real.sin θ)
    (F := fun n θ => f θ * Real.cos θ ^ 2 * Real.sin θ *
      max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C))
    (f := fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ *
      (if Real.sin θ ^ 2 ∈ C then 1 else 0))
    hFmeas hbnd hbound hlim
  have h0 : Tendsto (fun n : ℕ => ∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ *
      max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C)) atTop (𝓝 0) := by
    have hiteq : (fun n : ℕ => ∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ *
        max 0 (1 - (n : ℝ) * Metric.infDist (Real.sin θ ^ 2) C)) = fun _ => (0 : ℝ) :=
      funext hFdiff
    rw [hiteq]
    exact tendsto_const_nhds
  have hval : (∫ θ in Iθ, f θ * Real.cos θ ^ 2 * Real.sin θ *
      (if Real.sin θ ^ 2 ∈ C then 1 else 0)) = 0 := (tendsto_nhds_unique h0 hDCT).symm
  have hstep : (∫ θ in K, f θ * Real.cos θ ^ 2 * Real.sin θ)
      = ∫ θ, Set.indicator Iθ (fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ *
          (if Real.sin θ ^ 2 ∈ C then 1 else 0)) θ ∂volume := by
    rw [← MeasureTheory.integral_indicator (s := K)
      (f := fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ) hK.measurableSet]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with θ
    by_cases hθ : θ ∈ Iθ
    · rw [Set.indicator_of_mem hθ]
      by_cases hv : Real.sin θ ^ 2 ∈ C
      · rw [Set.indicator_of_mem ((hCmem θ hθ).mpr hv), if_pos hv, mul_one]
      · rw [Set.indicator_of_notMem (fun hθK => hv ((hCmem θ hθ).mp hθK)), if_neg hv,
          mul_zero]
    · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem (fun hθK => hθ (hKI hθK))]
  rw [hstep, MeasureTheory.integral_indicator (s := Iθ)
    (f := fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ *
      (if Real.sin θ ^ 2 ∈ C then 1 else 0)) measurableSet_Icc, hval]

/-! ## The density theorem -/

theorem eigFun_span_dense {f : ℝ → ℝ}
    (hme : MeasureTheory.AEMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (horth : ∀ n : ℕ, 1 ≤ n →
      (∫ θ in Work.Spaces.Iθ,
        f θ * Work.FTS.EllipticEst.LevelOneAsm.eigFun n θ * Real.cos θ) = 0) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), f θ = 0 := by
  have hFint : IntegrableOn (fun θ => f θ * Real.cos θ ^ 2 * Real.sin θ) Iθ :=
    integrableOn_f_cos2_sin hme hf
  have hzero : ∀ s : Set ℝ, IsCompact s →
      (∫ x in s, f x * Real.cos x ^ 2 * Real.sin x ∂(volume.restrict Iθ)) = 0 := by
    intro s hs
    rw [MeasureTheory.Measure.restrict_restrict (s := s) (t := Iθ) hs.measurableSet]
    exact moment_compact hme hf horth (hs.inter_right isClosed_Icc) Set.inter_subset_right
  have hmain := MeasureTheory.ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero hFint hzero
  filter_upwards [hmain, ae_mem_Ioo_Iθ] with θ h1 h2
  have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [h2.1, Real.pi_pos], h2.2⟩)
  have hs : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_mem_Ioo
    ⟨h2.1, by linarith [h2.2, Real.pi_pos]⟩)
  rcases mul_eq_zero.mp h1 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' (pow_ne_zero 2 hc)
  · exact absurd h hs

end Work.FTS.EllipticEst.LevelOneAsm
