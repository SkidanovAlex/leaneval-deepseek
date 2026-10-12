import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.boxLatPoly_deriv_normSq
import Submission.Work.BoseBoxFock.L1Tails.boxLatPoly_normSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.latDirichlet` — the Dirichlet bound for the trial function

For `ψ = φ_ℓ · Σ_{n∈S} c_n e^{i⟪κ_n,x⟫}` (the trial function of the lattice-Coulomb duality, see
`latDefs`), the Dirichlet energy of `ψ` is controlled by the coefficients:

    ∑_j ∫_x ‖∂_jψ(x)‖² ≤ latConst · ℓ³ · Σ_{n∈S} ‖c_n‖²‖κ_n‖² .

Proof: the product rule `∂_jψ = (∂_jφ_ℓ)·P + φ_ℓ·(∂_jP)` (both terms compactly supported, since
`φ_ℓ` is), the pointwise bounds `0 ≤ φ_ℓ ≤ 1`, `(∂_jφ_ℓ)² ≤ (chiGradBound/ℓ)²` and
`∂_jφ_ℓ = 0` off the box, the lattice orthogonality on the box (`boxLatPoly_normSq`,
`boxLatPoly_deriv_normSq`), and Poincaré `‖κ_n‖ ≥ 2π/ℓ` for `n ≠ 0`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real Topology ContDiff

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. The complexified bump and the product rule -/

/-- The complexification of the bump `φ_ℓ`. -/
def cBump (ℓ : ℝ) : E3 → ℂ := fun x => ((bumpFun ℓ x : ℝ) : ℂ)

/-- The norm of the complexification of a real number. -/
lemma norm_ofReal_C (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : ‖((r : ℝ) : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
    ring
  nlinarith [norm_nonneg (((r : ℝ) : ℂ)), abs_nonneg r]

lemma cBump_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (cBump ℓ) :=
  Complex.ofRealCLM.contDiff.comp (bumpFun_contDiff ℓ)

lemma latPsi_eq_mul (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) :
    latPsi ℓ S c = fun x => cBump ℓ x * latPoly ℓ S c x := rfl

lemma fderiv_cBump_apply (ℓ : ℝ) (x w : E3) :
    fderiv ℝ (cBump ℓ) x w = ((fderiv ℝ (bumpFun ℓ) x w : ℝ) : ℂ) := by
  have hd : HasFDerivAt (bumpFun ℓ) (fderiv ℝ (bumpFun ℓ) x) x :=
    ((bumpFun_contDiff ℓ).differentiable (by simp) x).hasFDerivAt
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hd
  have hfe : fderiv ℝ (cBump ℓ) x
      = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ (bumpFun ℓ) x) := h.fderiv
  rw [hfe]
  simp [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-- The product rule for the trial function `ψ = φ_ℓ · P`. -/
lemma fderiv_latPsi_apply (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ)
    (x w : E3) :
    fderiv ℝ (latPsi ℓ S c) x w
      = (bumpFun ℓ x : ℂ) * fderiv ℝ (latPoly ℓ S c) x w
        + latPoly ℓ S c x * ((fderiv ℝ (bumpFun ℓ) x w : ℝ) : ℂ) := by
  rw [latPsi_eq_mul,
    fderiv_fun_mul ((cBump_contDiff ℓ).differentiable (by simp) x)
      ((latPoly_contDiff ℓ S c).differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul, fderiv_cBump_apply, cBump]

/-- The gradient of the bump is bounded by `chiGradBound/ℓ`. -/
lemma norm_fderiv_bumpFun_single_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3) (j : Fin 3) :
    ‖((fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ)) : ℝ) : ℂ)‖
      ≤ chiGradBound / ℓ := by
  rw [norm_ofReal_C, fderiv_bumpFun_apply]
  have hnorm : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
  have h1 : (0 : ℝ) < ℓ⁻¹ := by positivity
  have hop : |fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x)
        (EuclideanSpace.single j (1 : ℝ))|
      ≤ ‖fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x)‖
        * ‖EuclideanSpace.single j (1 : ℝ)‖ := by
    have h := ContinuousLinearMap.le_opNorm
      (fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x)) (EuclideanSpace.single j (1 : ℝ))
    rwa [Real.norm_eq_abs] at h
  calc |ℓ⁻¹ * fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x)
        (EuclideanSpace.single j (1 : ℝ))|
      = ℓ⁻¹ * |fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x)
          (EuclideanSpace.single j (1 : ℝ))| := by
        rw [abs_mul, abs_of_nonneg h1.le]
    _ ≤ ℓ⁻¹ * (‖fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x)‖
          * ‖EuclideanSpace.single j (1 : ℝ)‖) := mul_le_mul_of_nonneg_left hop h1.le
    _ = ℓ⁻¹ * ‖fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x)‖ := by rw [hnorm, mul_one]
    _ ≤ ℓ⁻¹ * chiGradBound := mul_le_mul_of_nonneg_left (chiBase_fderiv_le_bound _) h1.le
    _ = chiGradBound / ℓ := by ring

/-- The same bound read on the real derivative. -/
lemma abs_fderiv_bumpFun_single_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3) (j : Fin 3) :
    |fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))| ≤ chiGradBound / ℓ := by
  have h := norm_fderiv_bumpFun_single_le (ℓ := ℓ) hℓ x j
  rwa [norm_ofReal_C] at h

/-- Off the box the bump is (locally) zero, so its derivative vanishes there. -/
lemma fderiv_bumpFun_eq_zero_of_notMem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : x ∉ Work.BoseK15.corpusBox.boxL ℓ) : fderiv ℝ (bumpFun ℓ) x = 0 := by
  have h0 : bumpFun ℓ =ᶠ[𝓝 x] 0 := by
    have hopen : IsOpen (Work.BoseK15.corpusBox.boxL ℓ)ᶜ :=
      (Work.BoseB4.BoxData.boxL_compact _ ℓ).isClosed.isOpen_compl
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact bumpFun_eq_zero_of_notMem_boxL hℓ hy
  rw [h0.fderiv_eq]
  simp

/-- **The pointwise bound for the derivative of the trial function.** -/
lemma latPsi_fderiv_sq_le {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → ℂ) (x : E3) (j : Fin 3) :
    ‖fderiv ℝ (latPsi ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ 2 * ((bumpFun ℓ x) ^ 2
              * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        + 2 * ((fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))) ^ 2
              * ‖latPoly ℓ S c x‖ ^ 2) := by
  rw [fderiv_latPsi_apply]
  have hb0 : 0 ≤ bumpFun ℓ x := bumpFun_nonneg ℓ x
  have hM := abs_fderiv_bumpFun_single_le (ℓ := ℓ) hℓ x j
  have h1 : ‖(bumpFun ℓ x : ℂ) * fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))
      + latPoly ℓ S c x * ((fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ)) : ℝ) : ℂ)‖
      ≤ bumpFun ℓ x * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖
        + ‖latPoly ℓ S c x‖ * |fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))| := by
    refine le_trans (norm_add_le _ _) (add_le_add (le_of_eq ?_) (le_of_eq ?_))
    · rw [norm_mul, norm_ofReal_C, abs_of_nonneg hb0]
    · rw [norm_mul, norm_ofReal_C]
  have h2 : ‖(bumpFun ℓ x : ℂ) * fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))
      + latPoly ℓ S c x * ((fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ)) : ℝ) : ℂ)‖ ^ 2
      ≤ (bumpFun ℓ x * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖
        + ‖latPoly ℓ S c x‖ * |fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (bumpFun ℓ x * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖
        + ‖latPoly ℓ S c x‖ * |fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))|) ^ 2
      ≤ 2 * (bumpFun ℓ x * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
        + 2 * (‖latPoly ℓ S c x‖ * |fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))|) ^ 2 := by
    nlinarith [sq_nonneg (bumpFun ℓ x * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖
      - ‖latPoly ℓ S c x‖ * |fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))|)]
  have h4 : (bumpFun ℓ x * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖) ^ 2
      = (bumpFun ℓ x) ^ 2
        * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := mul_pow _ _ _
  have h5 : (‖latPoly ℓ S c x‖ * |fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))|) ^ 2
      = (fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))) ^ 2 * ‖latPoly ℓ S c x‖ ^ 2 := by
    rw [mul_pow, sq_abs, mul_comm]
  linarith [h2, h3, h4.le, h4.symm.le, h5.le, h5.symm.le]

/-! ## 2. Helpers on the box and on the lattice -/

/-- `‖v‖² = Σ_j (v j)²` for `v : E3`. -/
lemma normSq_eq_sum_sq (v : E3) : ‖v‖ ^ 2 = ∑ j : Fin 3, (v j) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

/-- The coordinate sum of the box identities. -/
lemma sum_sum_eq {ℓ : ℝ} (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) :
    ∑ j : Fin 3, ∑ n ∈ S, ‖c n‖ ^ 2 * ((kappaL ℓ n) j) ^ 2
      = ∑ n ∈ S, ‖c n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.mul_sum, ← normSq_eq_sum_sq]

/-- Poincaré on the lattice, summed against the coefficients. -/
lemma latCoeffSum_le {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ)
    (hS : (0 : Fin 3 → ℤ) ∉ S) :
    ∑ n ∈ S, ‖c n‖ ^ 2 ≤ (ℓ ^ 2 / (4 * Real.pi ^ 2))
      * ∑ n ∈ S, ‖c n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2 := by
  have hpt : ∀ n ∈ S, ‖c n‖ ^ 2 ≤ (ℓ ^ 2 / (4 * Real.pi ^ 2))
      * (‖c n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2) := by
    intro n hn
    have hn0 : n ≠ 0 := by rintro rfl; exact hS hn
    have hlow := two_pi_div_le_norm_kappaL hℓ hn0
    have h2 : (2 * Real.pi / ℓ) ^ 2 ≤ ‖kappaL ℓ n‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    have h3 : 1 ≤ (ℓ ^ 2 / (4 * Real.pi ^ 2)) * ‖kappaL ℓ n‖ ^ 2 := by
      have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
      have hpin : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have heq : (ℓ ^ 2 / (4 * Real.pi ^ 2)) * (2 * Real.pi / ℓ) ^ 2 = 1 := by
        field_simp
        ring
      calc (1 : ℝ) = (ℓ ^ 2 / (4 * Real.pi ^ 2)) * (2 * Real.pi / ℓ) ^ 2 := heq.symm
        _ ≤ (ℓ ^ 2 / (4 * Real.pi ^ 2)) * ‖kappaL ℓ n‖ ^ 2 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
    calc ‖c n‖ ^ 2 = ‖c n‖ ^ 2 * 1 := by ring
      _ ≤ ‖c n‖ ^ 2 * ((ℓ ^ 2 / (4 * Real.pi ^ 2)) * ‖kappaL ℓ n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = (ℓ ^ 2 / (4 * Real.pi ^ 2)) * (‖c n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2) := by ring
  calc ∑ n ∈ S, ‖c n‖ ^ 2
      ≤ ∑ n ∈ S, (ℓ ^ 2 / (4 * Real.pi ^ 2)) * (‖c n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2) :=
        Finset.sum_le_sum hpt
    _ = (ℓ ^ 2 / (4 * Real.pi ^ 2)) * ∑ n ∈ S, ‖c n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2 := by
        rw [Finset.mul_sum]

/-! ## 3. Integrability helpers on the box -/

/-- On the compact box, continuity gives integrability. -/
lemma integrableOn_boxL_of_continuous {ℓ : ℝ} {f : E3 → ℝ} (hf : Continuous f) :
    IntegrableOn f (Work.BoseK15.corpusBox.boxL ℓ) :=
  hf.continuousOn.integrableOn_compact (Work.BoseB4.BoxData.boxL_compact _ ℓ)

/-- If `g` vanishes off the box, its integral equals its integral over the box. -/
lemma integral_eq_boxIntegral {ℓ : ℝ} {g : E3 → ℝ}
    (hg : ∀ x, x ∉ Work.BoseK15.corpusBox.boxL ℓ → g x = 0) :
    ∫ x, g x = ∫ x in Work.BoseK15.corpusBox.boxL ℓ, g x := by
  rw [← integral_indicator (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hg x hx]


/-! ## 4. The Dirichlet bound -/

theorem dirichletLatPsi {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ)
    (hS : (0 : Fin 3 → ℤ) ∉ S) :
    ∑ j : Fin 3, ∫ x : E3, ‖fderiv ℝ (latPsi ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ latConst * ℓ ^ 3 * ∑ n ∈ S, ‖c n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2 := by
  set D : ℝ := ∑ n ∈ S, ‖c n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2 with hDdef
  set E : ℝ := ∑ n ∈ S, ‖c n‖ ^ 2 with hEdef
  set K : ℝ := 2 * ((chiGradBound / ℓ) ^ 2 * (ℓ ^ 3 * E)) with hKdef
  -- the per-coordinate bound
  have hper : ∀ j : Fin 3,
      ∫ x : E3, ‖fderiv ℝ (latPsi ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ 2 * ℓ ^ 3 * (∑ n ∈ S, ‖c n‖ ^ 2 * ((kappaL ℓ n) j) ^ 2) + K := by
    intro j
    rw [hKdef, hEdef]
    rw [integral_eq_boxIntegral (ℓ := ℓ) (g := fun x : E3 =>
      ‖fderiv ℝ (latPsi ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (by
        intro x hx
        have h1 : fderiv ℝ (bumpFun ℓ) x = 0 := fderiv_bumpFun_eq_zero_of_notMem_boxL hℓ hx
        rw [fderiv_latPsi_apply, bumpFun_eq_zero_of_notMem_boxL hℓ hx, h1]
        simp)]
    -- pointwise bound on the box
    have hφ2 : (bumpFun ℓ) ^ 2 ≤ 1 := by
      intro x
      have h1 : bumpFun ℓ x ≤ 1 := bumpFun_le_one ℓ x
      have h2 : 0 ≤ bumpFun ℓ x := bumpFun_nonneg ℓ x
      show (bumpFun ℓ x) ^ 2 ≤ 1
      nlinarith
    have hφ'2 : ∀ x, (fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))) ^ 2
        ≤ (chiGradBound / ℓ) ^ 2 := by
      intro x
      have h := abs_fderiv_bumpFun_single_le (ℓ := ℓ) hℓ x j
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hpt : ∀ x ∈ Work.BoseK15.corpusBox.boxL ℓ,
        ‖fderiv ℝ (latPsi ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ 2 * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + 2 * ((chiGradBound / ℓ) ^ 2 * ‖latPoly ℓ S c x‖ ^ 2) := by
      intro x _
      have h := latPsi_fderiv_sq_le (ℓ := ℓ) hℓ S c x j
      have hA : (bumpFun ℓ x) ^ 2
            * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        mul_le_of_le_one_left (sq_nonneg _) (hφ2 x)
      have hB : (fderiv ℝ (bumpFun ℓ) x (EuclideanSpace.single j (1 : ℝ))) ^ 2
            * ‖latPoly ℓ S c x‖ ^ 2
          ≤ (chiGradBound / ℓ) ^ 2 * ‖latPoly ℓ S c x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hφ'2 x) (sq_nonneg _)
      linarith [h, hA, hB]
    have hcontPoly : Continuous (fun x : E3 =>
        ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) :=
      (((latPoly_contDiff ℓ S c).continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2
    have hcontPsi : Continuous (fun x : E3 =>
        ‖fderiv ℝ (latPsi ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) :=
      (((latPsi_contDiff ℓ S c).continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2
    have hcontN : Continuous (fun x : E3 => ‖latPoly ℓ S c x‖ ^ 2) :=
      (latPoly_contDiff ℓ S c).continuous.norm.pow 2
    have hInt1 : IntegrableOn (fun x : E3 =>
        ‖fderiv ℝ (latPsi ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (Work.BoseK15.corpusBox.boxL ℓ) :=
      integrableOn_boxL_of_continuous (ℓ := ℓ) hcontPsi
    have hIntA : IntegrableOn (fun x : E3 =>
        2 * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (Work.BoseK15.corpusBox.boxL ℓ) :=
      integrableOn_boxL_of_continuous (ℓ := ℓ) (hcontPoly.const_mul 2)
    have hIntB : IntegrableOn (fun x : E3 =>
        2 * ((chiGradBound / ℓ) ^ 2 * ‖latPoly ℓ S c x‖ ^ 2))
        (Work.BoseK15.corpusBox.boxL ℓ) :=
      integrableOn_boxL_of_continuous (ℓ := ℓ)
        ((hcontN.const_mul ((chiGradBound / ℓ) ^ 2)).const_mul 2)
    have hInt2 : IntegrableOn (fun x : E3 =>
        2 * ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + 2 * ((chiGradBound / ℓ) ^ 2 * ‖latPoly ℓ S c x‖ ^ 2))
        (Work.BoseK15.corpusBox.boxL ℓ) := hIntA.add hIntB
    refine le_trans (MeasureTheory.setIntegral_mono_on hInt1 hInt2
      (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ) hpt) ?_
    have hI1 : IntegrableOn (fun x : E3 =>
        ‖fderiv ℝ (latPoly ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (Work.BoseK15.corpusBox.boxL ℓ) :=
      integrableOn_boxL_of_continuous (ℓ := ℓ) hcontPoly
    have hI2 : IntegrableOn (fun x : E3 => (chiGradBound / ℓ) ^ 2 * ‖latPoly ℓ S c x‖ ^ 2)
        (Work.BoseK15.corpusBox.boxL ℓ) :=
      integrableOn_boxL_of_continuous (ℓ := ℓ) (hcontN.const_mul ((chiGradBound / ℓ) ^ 2))
    rw [MeasureTheory.integral_add hIntA hIntB,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul,
      boxLatPoly_deriv_normSq hℓ S c j, boxLatPoly_normSq hℓ S c]
    exact le_of_eq (by ring)
  -- sum over the coordinates
  have hsum_le : ∑ j : Fin 3, ∫ x : E3,
        ‖fderiv ℝ (latPsi ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ ∑ j : Fin 3, (2 * ℓ ^ 3 * (∑ n ∈ S, ‖c n‖ ^ 2 * ((kappaL ℓ n) j) ^ 2) + K) :=
    Finset.sum_le_sum fun j _ => hper j
  have hstep : ∑ j : Fin 3, (2 * ℓ ^ 3 * (∑ n ∈ S, ‖c n‖ ^ 2 * ((kappaL ℓ n) j) ^ 2) + K)
      = 2 * ℓ ^ 3 * D + 3 * K := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, sum_sum_eq S c, ← hDdef]
    ring
  -- Poincaré: `E ≤ (ℓ²/4π²) D`
  have hPoinc : E ≤ (ℓ ^ 2 / (4 * Real.pi ^ 2)) * D := by
    rw [hEdef, hDdef]
    exact latCoeffSum_le hℓ S c hS
  have hfinal : 2 * ℓ ^ 3 * D + 3 * K
      ≤ 2 * ℓ ^ 3 * D + 3 * (2 * ((chiGradBound / ℓ) ^ 2 * (ℓ ^ 3 * ((ℓ ^ 2 / (4 * Real.pi ^ 2)) * D)))) := by
    have h3 : (0 : ℝ) ≤ ℓ ^ 3 := by positivity
    have h4 : (0 : ℝ) ≤ (chiGradBound / ℓ) ^ 2 := by positivity
    have h5 : ℓ ^ 3 * E ≤ ℓ ^ 3 * ((ℓ ^ 2 / (4 * Real.pi ^ 2)) * D) :=
      mul_le_mul_of_nonneg_left hPoinc h3
    have h6 : (chiGradBound / ℓ) ^ 2 * (ℓ ^ 3 * E)
        ≤ (chiGradBound / ℓ) ^ 2 * (ℓ ^ 3 * ((ℓ ^ 2 / (4 * Real.pi ^ 2)) * D)) :=
      mul_le_mul_of_nonneg_left h5 h4
    have h7 : K ≤ 2 * ((chiGradBound / ℓ) ^ 2 * (ℓ ^ 3 * ((ℓ ^ 2 / (4 * Real.pi ^ 2)) * D))) := by
      rw [hKdef]
      exact mul_le_mul_of_nonneg_left h6 (by norm_num)
    linarith [h7]
  calc ∑ j : Fin 3, ∫ x : E3, ‖fderiv ℝ (latPsi ℓ S c) x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ ∑ j : Fin 3, (2 * ℓ ^ 3 * (∑ n ∈ S, ‖c n‖ ^ 2 * ((kappaL ℓ n) j) ^ 2) + K) := hsum_le
    _ = 2 * ℓ ^ 3 * D + 3 * K := hstep
    _ ≤ 2 * ℓ ^ 3 * D + 3 * (2 * ((chiGradBound / ℓ) ^ 2
          * (ℓ ^ 3 * ((ℓ ^ 2 / (4 * Real.pi ^ 2)) * D)))) := hfinal
    _ = latConst * ℓ ^ 3 * D := by
        have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
        have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
        unfold latConst
        field_simp
        ring
    _ = latConst * ℓ ^ 3 * ∑ n ∈ S, ‖c n‖ ^ 2 * ‖kappaL ℓ n‖ ^ 2 := by rw [hDdef]

end Work.BoseBoxFock.L1Tails
