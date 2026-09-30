/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.PolarContain
import Submission.Vinogradov.TentShift
import Submission.Commons.LinearAlgebra.Matrix.det_choose_matrix
import Submission.Commons.Analysis.Convolution.aniso_tent_conv_le_scaled
import Submission.Commons.Analysis.Integral.integral_comp_linearMap
import Submission.Commons.Analysis.MomentCurve.gam_aniso_gauge_compare

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tent calculus of GLYZ Appendix A

This module proves the estimates of Guo–Li–Yung–Zorin-Kranich (arXiv:1912.09798)
Appendix A in the form in which §3.4 consumes them.

The two inputs are

* the **representation** of the plate bump as a determinant factor times the
  `L¹`-normalised anisotropic tent in the `δ`-independent gauge coordinates,
  `phiPlate k hk δ c A Cφ x = Cφ · |det G_c| · plateTent k hk A δ (G_c x)`
  (`phiPlate_eq_plateTent`), where `plateGaugeLin k δ c = diagPow k δ ∘ G_c` with `G_c`
  independent of `δ` (`plateGaugeLin_eq_diagPow_comp`);
* the **two-scale tent convolution** `plateTent_conv_le`, `∫ T_{δ₁}(x-y)T_{δ₂}(y)dy ≲ T_{δ₂}(x)`
  for `δ₂ ≤ δ₁`, obtained from the commons `aniso_tent_conv_le_scaled` — the commons lemma
  covers `δ₁ ≤ 1`, and the general case follows by the anisotropic rescaling
  `y ↦ diagPow k δ₁⁻¹ y`, which produces exactly the factor `δ₁^{-k(k+1)/2}` that is needed to
  cancel the determinant factors.

From these we deduce

* `phiPlate_conv_same` — the convolution of two plate bumps *at the same centre* is dominated
  by the finer one;
* `phiPlate_conv_le` — **GLYZ Lemma A.1**: for a fine piece `J` contained in a coarse piece `I`,
  `φ_I ∗ φ_J ≲ φ_J`.  The centre mismatch is handled by the same-scale comparison
  `exists_gauge_plateGaugeLin_compare` (from the commons `gam_aniso_gauge_compare`).

The determinants (which must be shown to be independent of the centre, so that the same-scale
comparison of the bumps is valid) are computed through `LinearMap.det_toMatrix` in the standard
basis, `Matrix.det_diagonal`, and the adjoint/transpose identity `det f^* = det f`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal
set_option autoImplicit false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov



/-- The inner product with a moment-curve derivative vector, in coordinates. -/
lemma inner_gammaDeriv_eq_sum (k : ℕ) (i : ℕ) (t : ℝ) (x : E k) :
    ⟪x, gammaDeriv k i t⟫ = ∑ j : Fin k, x j * Commons.Analysis.MomentCurve.gam k t i j := by
  rw [gammaDeriv_eq_lpSymm_gam]
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
      (Commons.Analysis.MomentCurve.gam k t i) : E k).ofLp j
      = Commons.Analysis.MomentCurve.gam k t i j := rfl
  rw [h1]

/-! ## 1. Determinants of the plate maps -/

/-- The matrix of `affVecDualLin` in the standard basis: the combinatorially explicit
`C(l+1,j+1) ρ^{j+1} t^{l-j}`. -/
lemma toMatrix_affVecDualLin (k : ℕ) (ρ t : ℝ) :
    LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin k)) (PiLp.basisFun 2 ℝ (Fin k))
      (affVecDualLin k ρ t)
      = Matrix.of (fun l j : Fin k =>
          ((l.val + 1).choose (j.val + 1) : ℝ) * ρ ^ (j.val + 1) * t ^ (l.val - j.val)) := by
  ext l j
  rw [LinearMap.toMatrix_apply, PiLp.basisFun_repr, PiLp.basisFun_apply, Matrix.of_apply]
  rw [affVecDualLin_apply, affVecDual_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have h1 : (PiLp.single 2 j 1 : E k) b = 0 := by
      rw [PiLp.single_apply]; simp [hb]
    rw [h1]; ring
  · intro h; exact absurd (Finset.mem_univ j) h

/-- `det (affVecDualLin k ρ t) = ρ^{k(k+1)/2}`. -/
lemma det_affVecDualLin (k : ℕ) (ρ t : ℝ) :
    LinearMap.det (affVecDualLin k ρ t) = ρ ^ (k * (k + 1) / 2) := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin k)) (affVecDualLin k ρ t),
    toMatrix_affVecDualLin]
  exact Commons.LinearAlgebra.Matrix.det_choose_matrix k ρ t

/-- The adjoint of `affVecDualLin` is `affVecLin`. -/
lemma adjoint_affVecDualLin (k : ℕ) (ρ t : ℝ) :
    LinearMap.adjoint (affVecDualLin k ρ t) = affVecLin k ρ t := by
  exact (((LinearMap.eq_adjoint_iff (A := affVecLin k ρ t)
    (B := affVecDualLin k ρ t)).mpr fun x y => by
      rw [affVecDualLin_apply]
      exact inner_affVecLin k ρ t x y)).symm

/-- The determinant of a linear endomorphism equals the determinant of its adjoint. -/
lemma det_adjoint_eq (k : ℕ) (f : E k →ₗ[ℝ] E k) :
    LinearMap.det (LinearMap.adjoint f) = LinearMap.det f := by
  have hb : ((LinearMap.toMatrix (stdOrthonormalBasis ℝ (E k)).toBasis
      (stdOrthonormalBasis ℝ (E k)).toBasis) (LinearMap.adjoint f))
      = (((LinearMap.toMatrix (stdOrthonormalBasis ℝ (E k)).toBasis
        (stdOrthonormalBasis ℝ (E k)).toBasis) f)).transpose := by
    rw [LinearMap.toMatrix_adjoint]
    ext i j
    simp [Matrix.conjTranspose_apply, star_trivial]
  rw [← LinearMap.det_toMatrix (stdOrthonormalBasis ℝ (E k)).toBasis (LinearMap.adjoint f),
      hb, Matrix.det_transpose, LinearMap.det_toMatrix]

/-- `det (affVecLin k ρ t) = ρ^{k(k+1)/2}`. -/
lemma det_affVecLin (k : ℕ) (ρ t : ℝ) :
    LinearMap.det (affVecLin k ρ t) = ρ ^ (k * (k + 1) / 2) := by
  rw [← adjoint_affVecDualLin k ρ t, det_adjoint_eq, det_affVecDualLin]

/-- The matrix of `diagFact` in the standard basis is the diagonal `(i+1)!`. -/
lemma toMatrix_diagFact (k : ℕ) :
    LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin k)) (PiLp.basisFun 2 ℝ (Fin k)) (diagFact k)
      = Matrix.diagonal (fun i : Fin k => ((i.val + 1).factorial : ℝ)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, PiLp.basisFun_repr, PiLp.basisFun_apply, Matrix.diagonal_apply,
    diagFact_apply]
  by_cases h : i = j <;> simp [PiLp.single_apply, h]

/-- `det (diagFact k) = ∏_i (i+1)!`. -/
lemma det_diagFact (k : ℕ) :
    LinearMap.det (diagFact k) = ∏ i : Fin k, ((i.val + 1).factorial : ℝ) := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin k)) (diagFact k), toMatrix_diagFact,
    Matrix.det_diagonal]

lemma det_diagFact_ne_zero (k : ℕ) : LinearMap.det (diagFact k) ≠ 0 := by
  rw [det_diagFact]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    exact_mod_cast (Nat.factorial_ne_zero (i.val + 1))

/-- The `δ`-independent part of the plate gauge map: `diagFact ∘ affVecLin_1`. -/
noncomputable def plateGaugeBase (k : ℕ) (c : ℝ) : E k →ₗ[ℝ] E k :=
  (diagFact k).comp (affVecLin k 1 c)

/-- **The plate gauge map is the anisotropic diagonal applied to the `δ`-independent map.** -/
lemma plateGaugeLin_eq_diagPow_comp (k : ℕ) (δ c : ℝ) :
    plateGaugeLin k δ c = (diagPow k δ).comp (plateGaugeBase k c) := by
  have h1 : plateGaugeLin k δ c = (diagFact k).comp (affVecLin k δ c) := by
    ext x i
    have hL : plateGaugeLin k δ c x i
        = δ ^ (i.val + 1)
          * ∑ j : Fin k, x j * Commons.Analysis.MomentCurve.gam k c (i.val + 1) j := by
      rw [plateGaugeLin_apply, inner_gammaDeriv_eq_sum]
    have hR : ((diagFact k).comp (affVecLin k δ c)) x i
        = ((i.val + 1).factorial : ℝ)
          * ∑ j : Fin k, x j * ((j.val + 1).choose (i.val + 1) : ℝ) * δ ^ (i.val + 1)
              * c ^ (j.val - i.val) := by
      rw [LinearMap.comp_apply, diagFact_apply, affVecLin_apply, affVec_apply]
    rw [hL, hR, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => by
      rw [Commons.Analysis.MomentCurve.gam_apply]
      have hfac : ((j.val + 1).descFactorial (i.val + 1) : ℝ)
          = ((i.val + 1).factorial : ℝ) * ((j.val + 1).choose (i.val + 1) : ℝ) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
      rw [hfac, Nat.add_sub_add_right]
      ring : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        δ ^ (i.val + 1) * (x j * Commons.Analysis.MomentCurve.gam k c (i.val + 1) j)
          = ((i.val + 1).factorial : ℝ)
            * (x j * ((j.val + 1).choose (i.val + 1) : ℝ) * δ ^ (i.val + 1)
              * c ^ (j.val - i.val)))]

  have h2 : affVecLin k δ c = (diagPow k δ).comp (affVecLin k 1 c) := by
    ext x l
    have hL : affVecLin k δ c x l = ∑ j : Fin k, x j * ((j.val + 1).choose (l.val + 1) : ℝ)
        * δ ^ (l.val + 1) * c ^ (j.val - l.val) := by
      rw [affVecLin_apply, affVec_apply]
    have hR : ((diagPow k δ).comp (affVecLin k 1 c)) x l
        = δ ^ (l.val + 1) * ∑ j : Fin k, x j * ((j.val + 1).choose (l.val + 1) : ℝ)
            * 1 ^ (l.val + 1) * c ^ (j.val - l.val) := by
      rw [LinearMap.comp_apply, diagPow_apply, affVecLin_apply, affVec_apply]
    rw [hL, hR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

  have h3pt : ∀ y : E k, diagFact k (diagPow k δ y) = diagPow k δ (diagFact k y) := fun y => by
    ext i
    have hL : diagFact k (diagPow k δ y) i
        = ((i.val + 1).factorial : ℝ) * δ ^ (i.val + 1) * y i := by
      rw [diagFact_apply, diagPow_apply]
      ring
    have hR : (diagPow k δ (diagFact k y)) i
        = δ ^ (i.val + 1) * ((i.val + 1).factorial : ℝ) * y i := by
      rw [diagPow_apply, diagFact_apply]
      ring
    rw [hL, hR]
    ring

  rw [h1, h2]
  exact LinearMap.ext fun x => h3pt (affVecLin k 1 c x)

/-- The determinant of the `δ`-independent part. -/
lemma det_plateGaugeBase (k : ℕ) (c : ℝ) :
    LinearMap.det (plateGaugeBase k c)
      = ∏ i : Fin k, ((i.val + 1).factorial : ℝ) := by
  rw [plateGaugeBase, LinearMap.det_comp, det_diagFact, det_affVecLin, one_pow, mul_one]

lemma det_plateGaugeBase_ne_zero (k : ℕ) (c : ℝ) : LinearMap.det (plateGaugeBase k c) ≠ 0 := by
  rw [det_plateGaugeBase]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    exact_mod_cast (Nat.factorial_pos (i.val + 1)).ne'

/-- The determinant of the plate gauge map, without absolute values. -/
lemma det_plateGaugeLin_eq (k : ℕ) (δ c : ℝ) :
    LinearMap.det (plateGaugeLin k δ c)
      = δ ^ (k * (k + 1) / 2) * ∏ i : Fin k, ((i.val + 1).factorial : ℝ) := by
  rw [plateGaugeLin_eq_diagPow_comp, LinearMap.det_comp, det_diagPow, det_plateGaugeBase]

/-- The determinant of the plate gauge map. -/
lemma det_plateGaugeLin (k : ℕ) (δ c : ℝ) :
    |LinearMap.det (plateGaugeLin k δ c)|
      = |δ| ^ (k * (k + 1) / 2) * ∏ i : Fin k, ((i.val + 1).factorial : ℝ) := by
  rw [det_plateGaugeLin_eq, abs_mul, abs_pow]
  congr 1
  exact abs_of_nonneg (Finset.prod_nonneg fun i _ => by positivity)

/-- **Polar plates at nearby centres are comparable.**  For `0 < δ ≤ 1`, `c, c' ∈ [0,1]`
with `|c' - c| ≤ δ`, the gauge of the polar coordinates at `c'` is at most a fixed constant
`ρ` times the gauge at `c` (and conversely, by symmetry of the statement). -/
theorem exists_gauge_plateGaugeLin_compare (k : ℕ) (hk : 1 ≤ k) :
    ∃ ρ : ℝ, 1 ≤ ρ ∧ ∀ (δ c c' : ℝ), 0 < δ → δ ≤ 1 → c ∈ Set.Icc (0:ℝ) 1 →
      c' ∈ Set.Icc (0:ℝ) 1 → |c' - c| ≤ δ → ∀ x : E k,
      gauge k hk (plateGaugeLin k δ c' x) ≤ ρ * gauge k hk (plateGaugeLin k δ c x) := by
  obtain ⟨ρ, hρ1, hρ⟩ := Commons.Analysis.MomentCurve.gam_aniso_gauge_compare k hk
  refine ⟨ρ, hρ1, fun δ c c' hδ hδ1 hc hc' hcc x => ?_⟩
  have hmain := hρ δ c c' hδ hδ1 hc hc' hcc (fun j => x j)
  rw [gauge]
  refine Finset.sup'_le _ _ fun i _ => ?_
  rw [plateGaugeLin_apply, inner_gammaDeriv_eq_sum]
  have h1 : |δ ^ (i.val + 1) * ∑ j : Fin k, x j * Commons.Analysis.MomentCurve.gam k c' (i.val + 1) j|
      = δ ^ (i.val + 1) * |∑ j : Fin k, x j * Commons.Analysis.MomentCurve.gam k c' (i.val + 1) j| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hδ.le _)]
  rw [h1]
  calc δ ^ (i.val + 1) * |∑ j : Fin k, x j * Commons.Analysis.MomentCurve.gam k c' (i.val + 1) j|
      ≤ ρ * (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          (fun i : Fin k => δ ^ (i.val + 1) * |∑ j : Fin k, x j * Commons.Analysis.MomentCurve.gam k c (i.val + 1) j|) :=
        Finset.le_sup' _ (Finset.mem_univ i) |>.trans hmain
    _ = ρ * gauge k hk (plateGaugeLin k δ c x) := by
        congr 1
        rw [gauge]
        refine Finset.sup'_congr _ rfl fun i _ => ?_
        rw [plateGaugeLin_apply, inner_gammaDeriv_eq_sum, abs_mul,
          abs_of_nonneg (pow_nonneg hδ.le _)]

/-- **The same-scale comparison of the plate bumps.**  If the gauge of the polar coordinates
at `c'` is at most `ρ` times the gauge at `c`, then the plate bump at `c` is at most `ρ^A`
times the plate bump at `c'` (same scale). -/
lemma phiPlate_le_of_gauge_le (k : ℕ) (hk : 1 ≤ k) {δ c c' A Cφ ρ : ℝ} (hA : 0 < A)
    (hρ : 1 ≤ ρ) (hCφ : 0 ≤ Cφ) {x : E k}
    (h : max 1 (gauge k hk (plateGaugeLin k δ c' x))
          ≤ ρ * max 1 (gauge k hk (plateGaugeLin k δ c x))) :
    phiPlate k hk δ c A Cφ x ≤ ρ ^ A * phiPlate k hk δ c' A Cφ x := by
  have hρ0 : (0:ℝ) ≤ ρ := le_trans zero_le_one hρ
  have hNc : 0 < max 1 (gauge k hk (plateGaugeLin k δ c x)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hNc' : 0 < max 1 (gauge k hk (plateGaugeLin k δ c' x)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hkey : (max 1 (gauge k hk (plateGaugeLin k δ c' x))) / ρ
      ≤ max 1 (gauge k hk (plateGaugeLin k δ c x)) := by
    rw [div_le_iff₀ hρpos]
    linarith
  have h3 : (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A)
      ≤ ρ ^ A * (max 1 (gauge k hk (plateGaugeLin k δ c' x))) ^ (-A) := by
    have h4 : (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A)
        ≤ ((max 1 (gauge k hk (plateGaugeLin k δ c' x))) / ρ) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hkey (by linarith)
    have h5 : ((max 1 (gauge k hk (plateGaugeLin k δ c' x))) / ρ) ^ (-A)
        = ρ ^ A * (max 1 (gauge k hk (plateGaugeLin k δ c' x))) ^ (-A) := by
      rw [Real.div_rpow (le_of_lt hNc') hρ0, Real.rpow_neg hNc'.le,
        Real.rpow_neg hρ0, div_eq_mul_inv, inv_inv, mul_comm]
    linarith [h4, h5]
  rw [phiPlate, phiPlate]
  calc Cφ * |LinearMap.det (plateGaugeLin k δ c)|
        * (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A)
      ≤ Cφ * |LinearMap.det (plateGaugeLin k δ c)|
        * (ρ ^ A * (max 1 (gauge k hk (plateGaugeLin k δ c' x))) ^ (-A)) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hCφ (abs_nonneg _))
    _ = ρ ^ A * (Cφ * |LinearMap.det (plateGaugeLin k δ c')|
          * (max 1 (gauge k hk (plateGaugeLin k δ c' x))) ^ (-A)) := by
        rw [det_plateGaugeLin, det_plateGaugeLin]
        ring








/-- The coordinate anisotropic `U`-tent. -/
noncomputable def coordU (k : ℕ) (hk : 1 ≤ k) (A δ : ℝ) (w : Fin k → ℝ) : ℝ :=
  (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    (fun i => δ ^ (i.val + 1) * |w i|))) ^ (-A)

/-- The anisotropic `U`-tent on `E k`, obtained from the coordinate tent. -/
noncomputable def gaugeU (k : ℕ) (hk : 1 ≤ k) (A δ : ℝ) (w : E k) : ℝ :=
  coordU k hk A δ w.ofLp

/-- The `L¹`-normalised anisotropic tent attached to a plate. -/
noncomputable def plateTent (k : ℕ) (hk : 1 ≤ k) (A δ : ℝ) (w : E k) : ℝ :=
  δ ^ (k * (k + 1) / 2) * gaugeU k hk A δ w

lemma coordU_nonneg (k : ℕ) (hk : 1 ≤ k) (A δ : ℝ) (w : Fin k → ℝ) : 0 ≤ coordU k hk A δ w :=
  Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

lemma gaugeU_nonneg (k : ℕ) (hk : 1 ≤ k) (A δ : ℝ) (w : E k) : 0 ≤ gaugeU k hk A δ w :=
  coordU_nonneg k hk A δ w.ofLp

lemma coordU_eq_abs (k : ℕ) (hk : 1 ≤ k) (A : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (w : Fin k → ℝ) :
    coordU k hk A δ w
      = (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          (fun i => |δ ^ (i.val + 1) * w i|))) ^ (-A) := by
  have hs : ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      (fun i => δ ^ (i.val + 1) * |w i|))
      = ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      (fun i => |δ ^ (i.val + 1) * w i|)) :=
    Finset.sup'_congr _ rfl fun i _ => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hδ _)]
  rw [coordU, hs]

/-- The `U`-tent as the gauge of the anisotropic diagonal. -/
lemma gaugeU_eq_gauge (k : ℕ) (hk : 1 ≤ k) (A : ℝ) {δ : ℝ} (hδ : 0 < δ) (w : E k) :
    gaugeU k hk A δ w = (max 1 (gauge k hk (diagPow k δ w))) ^ (-A) := by
  have hs : ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      (fun i => δ ^ (i.val + 1) * |w.ofLp i|))
      = ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      (fun i => |(diagPow k δ w).ofLp i|)) :=
    Finset.sup'_congr _ rfl fun i _ => by
      rw [diagPow_apply, abs_mul, abs_of_nonneg (pow_nonneg hδ.le _)]
  rw [gaugeU, coordU, gauge, hs]

lemma integrable_coordU (k : ℕ) (hk : 1 ≤ k) {A : ℝ} (hA : (k : ℝ) < A) {δ : ℝ}
    (hδ : 0 < δ) : Integrable (fun w : Fin k → ℝ => coordU k hk A δ w) := by
  have h0 := Commons.Analysis.Convolution.integrable_aniso_tent_scaled k hk hA hδ
  refine h0.congr ?_
  filter_upwards with w
  rw [coordU_eq_abs k hk A hδ.le]

lemma integrable_gaugeU (k : ℕ) (hk : 1 ≤ k) {A : ℝ} (hA : (k : ℝ) < A) {δ : ℝ}
    (hδ : 0 < δ) : Integrable (fun w : E k => gaugeU k hk A δ w) := by
  have h0 := integrable_coordU k hk hA hδ
  have hiff := (PiLp.volume_preserving_ofLp (Fin k)).integrable_comp h0.aestronglyMeasurable
  rw [show (fun w : E k => gaugeU k hk A δ w)
      = (fun y : Fin k → ℝ => coordU k hk A δ y) ∘ WithLp.ofLp from rfl]
  exact hiff.mpr h0

/-- The anisotropic diagonal is multiplicative. -/
lemma diagPow_comp (k : ℕ) (a b : ℝ) (x : E k) :
    diagPow k a (diagPow k b x) = diagPow k (a * b) x := by
  ext i
  rw [diagPow_apply, diagPow_apply, diagPow_apply, mul_pow]
  ring

lemma diagPow_one (k : ℕ) (x : E k) : diagPow k 1 x = x := by
  ext i; rw [diagPow_apply, one_pow, one_mul]

lemma gaugeU_comp (k : ℕ) (hk : 1 ≤ k) (A : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x : E k) : gaugeU k hk A b (diagPow k a x) = gaugeU k hk A (b * a) x := by
  rw [gaugeU_eq_gauge k hk A hb, gaugeU_eq_gauge k hk A (mul_pos hb ha), diagPow_comp]

/-- **The two-scale tent convolution in coordinates** (from the commons). -/
lemma coordU_conv_le_aux (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA1 : (k : ℝ) < A)
    (hA2 : (k : ℝ) * (k + 1) / 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ), 0 < γ → γ ≤ 1 → ∀ x : Fin k → ℝ,
      (∫ y : Fin k → ℝ, coordU k hk A 1 (x - y) * coordU k hk A γ y)
        ≤ C * coordU k hk A γ x := by
  obtain ⟨C, hC, hClem⟩ := Commons.Analysis.Convolution.aniso_tent_conv_le_scaled k hk A hA1 hA2
  refine ⟨C, hC, fun γ hγ0 hγ1 x => ?_⟩
  have h := hClem 1 γ hγ0 hγ1 le_rfl x
  have h1 : (∫ y : Fin k → ℝ, (1 ^ (k * (k + 1) / 2)
        * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            fun i => (1:ℝ) ^ (i.val + 1) * |(x - y) i|)) ^ (-A))
        * (γ ^ (k * (k + 1) / 2)
          * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
              fun i => γ ^ (i.val + 1) * |y i|)) ^ (-A)))
      = γ ^ (k * (k + 1) / 2)
        * ∫ y : Fin k → ℝ, coordU k hk A 1 (x - y) * coordU k hk A γ y := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [coordU, one_mul, one_pow]
    ring
  rw [h1] at h
  have h2 : C * (γ ^ (k * (k + 1) / 2)
        * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
            fun i => γ ^ (i.val + 1) * |x i|)) ^ (-A))
      = γ ^ (k * (k + 1) / 2) * (C * coordU k hk A γ x) := by
    simp only [coordU]
    ring
  rw [h2] at h
  exact (mul_le_mul_iff_of_pos_left (pow_pos hγ0 _)).mp h

/-- **The two-scale anisotropic tent convolution on `E k`.**  For `0 < δ₂ ≤ δ₁`,
`A > k` and `A ≥ k(k+1)/2` there is a constant `C` with
`∫ gaugeU_{δ₁}(x - y) gaugeU_{δ₂}(y) dy ≤ C δ₁^{-k(k+1)/2} gaugeU_{δ₂}(x)`. -/
theorem gaugeU_conv_le (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA1 : (k : ℝ) < A)
    (hA2 : (k : ℝ) * (k + 1) / 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ), 0 < δ₂ → δ₂ ≤ δ₁ → ∀ x : E k,
      (∫ y : E k, gaugeU k hk A δ₁ (x - y) * gaugeU k hk A δ₂ y)
        ≤ C * (δ₁ ^ (k * (k + 1) / 2))⁻¹ * gaugeU k hk A δ₂ x := by
  obtain ⟨C, hC, hClem⟩ := coordU_conv_le_aux k hk A hA1 hA2
  refine ⟨C, hC, fun δ₁ δ₂ hδ20 hδ12 x => ?_⟩
  have hδ10 : 0 < δ₁ := lt_of_lt_of_le hδ20 hδ12
  have hγ0 : 0 < δ₂ * δ₁⁻¹ := mul_pos hδ20 (inv_pos.mpr hδ10)
  have hγ1 : δ₂ * δ₁⁻¹ ≤ 1 := (mul_inv_le_iff₀ hδ10).mpr (by simpa using hδ12)
  have hbdd : ∀ y : E k, ‖gaugeU k hk A δ₂ y‖ ≤ 1 := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gaugeU_nonneg k hk A δ₂ y), gaugeU, coordU]
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith)
  have hg1 : Integrable (fun y : E k => gaugeU k hk A δ₁ (x - y)) :=
    (integrable_gaugeU k hk hA1 hδ10).comp_sub_left x
  have hint : Integrable (fun y : E k => gaugeU k hk A δ₁ (x - y) * gaugeU k hk A δ₂ y) :=
    hg1.mul_bdd (integrable_gaugeU k hk hA1 hδ20).aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  have hdet : LinearMap.det (diagPow k (δ₁⁻¹)) ≠ 0 := by
    rw [det_diagPow]
    exact pow_ne_zero _ (inv_ne_zero (ne_of_gt hδ10))
  have hsub := Commons.Analysis.Integral.integral_comp_linearMap (μ := (volume : Measure (E k)))
    hdet hint
  rw [det_diagPow] at hsub
  have habs : |((δ₁⁻¹) ^ (k * (k + 1) / 2))⁻¹| = δ₁ ^ (k * (k + 1) / 2) := by
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (inv_nonneg.mpr hδ10.le) _)), inv_pow,
      inv_inv]
  rw [habs] at hsub
  have hpt : ∀ u : E k, gaugeU k hk A δ₁ (x - diagPow k δ₁⁻¹ u)
        * gaugeU k hk A δ₂ (diagPow k δ₁⁻¹ u)
      = gaugeU k hk A 1 (diagPow k δ₁ x - u) * gaugeU k hk A (δ₂ * δ₁⁻¹) u := by
    intro u
    have e1 : gaugeU k hk A δ₁ (x - diagPow k δ₁⁻¹ u)
        = gaugeU k hk A 1 (diagPow k δ₁ x - u) := by
      rw [gaugeU_eq_gauge k hk A hδ10, gaugeU_eq_gauge k hk A one_pos]
      have hx : diagPow k δ₁ (x - diagPow k δ₁⁻¹ u) = diagPow k δ₁ x - u := by
        rw [map_sub, diagPow_comp, mul_inv_cancel₀ (ne_of_gt hδ10), diagPow_one]
      rw [hx, diagPow_one]
    have e2 : gaugeU k hk A δ₂ (diagPow k δ₁⁻¹ u) = gaugeU k hk A (δ₂ * δ₁⁻¹) u :=
      gaugeU_comp k hk A (inv_pos.mpr hδ10) hδ20 u
    rw [e1, e2]
  have hsub2 : (∫ y : E k, gaugeU k hk A δ₁ (x - y) * gaugeU k hk A δ₂ y)
      = (δ₁ ^ (k * (k + 1) / 2))⁻¹
        * ∫ u : E k, gaugeU k hk A 1 (diagPow k δ₁ x - u) * gaugeU k hk A (δ₂ * δ₁⁻¹) u := by
    rw [show (∫ y : E k, gaugeU k hk A δ₁ (x - y) * gaugeU k hk A δ₂ y)
        = (δ₁ ^ (k * (k + 1) / 2))⁻¹
          * ∫ u : E k, gaugeU k hk A δ₁ (x - diagPow k δ₁⁻¹ u)
              * gaugeU k hk A δ₂ (diagPow k δ₁⁻¹ u) from by
            rw [hsub, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt hδ10)), one_mul]]
    congr 1
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hcoord : (∫ u : E k, gaugeU k hk A 1 (diagPow k δ₁ x - u) * gaugeU k hk A (δ₂ * δ₁⁻¹) u)
      = ∫ v : Fin k → ℝ, coordU k hk A 1 ((diagPow k δ₁ x).ofLp - v)
          * coordU k hk A (δ₂ * δ₁⁻¹) v := by
    have hme : MeasurableEmbedding (WithLp.toLp 2 : (Fin k → ℝ) → E k) :=
      (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding
    rw [← (PiLp.volume_preserving_toLp (ι := Fin k)).integral_comp hme
      (fun u : E k => gaugeU k hk A 1 (diagPow k δ₁ x - u) * gaugeU k hk A (δ₂ * δ₁⁻¹) u)]
    rfl
  rw [hsub2, hcoord]
  have hfin := hClem (δ₂ * δ₁⁻¹) hγ0 hγ1 ((diagPow k δ₁ x).ofLp)
  have he : coordU k hk A (δ₂ * δ₁⁻¹) ((diagPow k δ₁ x).ofLp) = gaugeU k hk A δ₂ x := by
    show gaugeU k hk A (δ₂ * δ₁⁻¹) (diagPow k δ₁ x) = gaugeU k hk A δ₂ x
    rw [gaugeU_eq_gauge k hk A hγ0, gaugeU_eq_gauge k hk A hδ20]
    congr 1
    rw [diagPow_comp, mul_assoc, inv_mul_cancel₀ (ne_of_gt hδ10), mul_one]
  rw [he] at hfin
  calc (δ₁ ^ (k * (k + 1) / 2))⁻¹
        * (∫ v : Fin k → ℝ, coordU k hk A 1 ((diagPow k δ₁ x).ofLp - v)
            * coordU k hk A (δ₂ * δ₁⁻¹) v)
      ≤ (δ₁ ^ (k * (k + 1) / 2))⁻¹ * (C * gaugeU k hk A δ₂ x) :=
        mul_le_mul_of_nonneg_left hfin (inv_nonneg.mpr (pow_nonneg hδ10.le _))
    _ = C * (δ₁ ^ (k * (k + 1) / 2))⁻¹ * gaugeU k hk A δ₂ x := by ring







lemma plateTent_nonneg (k : ℕ) (hk : 1 ≤ k) (A : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (w : E k) :
    0 ≤ plateTent k hk A δ w :=
  mul_nonneg (pow_nonneg hδ _) (gaugeU_nonneg k hk A δ w)

/-- **The plate bump is a determinant factor times the `L¹`-normalised tent** in the
`δ`-independent gauge coordinates. -/
lemma phiPlate_eq_plateTent (k : ℕ) (hk : 1 ≤ k) {δ c A Cφ : ℝ} (hδ : 0 < δ) (x : E k) :
    phiPlate k hk δ c A Cφ x
      = Cφ * |LinearMap.det (plateGaugeBase k c)| * plateTent k hk A δ (plateGaugeBase k c x) := by
  rw [phiPlate, plateTent, gaugeU_eq_gauge k hk A hδ, plateGaugeLin_eq_diagPow_comp,
    LinearMap.det_comp, det_diagPow, abs_mul, abs_of_nonneg (pow_nonneg hδ.le _),
    LinearMap.comp_apply]
  ring

lemma integrable_phiPlate (k : ℕ) (hk : 1 ≤ k) {δ c A Cφ : ℝ} (hδ : δ ≠ 0)
    (hA : (k : ℝ) < A) : Integrable (fun x : E k => phiPlate k hk δ c A Cφ x) :=
  ((integrable_comp_plateGaugeLin hδ c (integrable_gauge_rpow k hk hA)).const_mul
    (Cφ * |LinearMap.det (plateGaugeLin k δ c)|)).congr (Filter.Eventually.of_forall fun x => by
      simp only [phiPlate])

/-! ## The two-scale tent convolution for the `L¹`-normalised tent -/

theorem plateTent_conv_le (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA1 : (k : ℝ) < A)
    (hA2 : (k : ℝ) * (k + 1) / 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ), 0 < δ₂ → δ₂ ≤ δ₁ → ∀ x : E k,
      (∫ y : E k, plateTent k hk A δ₁ (x - y) * plateTent k hk A δ₂ y)
        ≤ C * plateTent k hk A δ₂ x := by
  obtain ⟨C, hC, hClem⟩ := gaugeU_conv_le k hk A hA1 hA2
  refine ⟨C, hC, fun δ₁ δ₂ hδ20 hδ12 x => ?_⟩
  have hδ10 : 0 < δ₁ := lt_of_lt_of_le hδ20 hδ12
  have h1 : (∫ y : E k, plateTent k hk A δ₁ (x - y) * plateTent k hk A δ₂ y)
      = δ₁ ^ (k * (k + 1) / 2) * δ₂ ^ (k * (k + 1) / 2)
        * ∫ y : E k, gaugeU k hk A δ₁ (x - y) * gaugeU k hk A δ₂ y := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [plateTent]
    ring
  rw [h1]
  have h2 := hClem δ₁ δ₂ hδ20 hδ12 x
  have hne : δ₁ ^ (k * (k + 1) / 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hδ10)
  calc δ₁ ^ (k * (k + 1) / 2) * δ₂ ^ (k * (k + 1) / 2)
        * (∫ y : E k, gaugeU k hk A δ₁ (x - y) * gaugeU k hk A δ₂ y)
      ≤ δ₁ ^ (k * (k + 1) / 2) * δ₂ ^ (k * (k + 1) / 2)
        * (C * (δ₁ ^ (k * (k + 1) / 2))⁻¹ * gaugeU k hk A δ₂ x) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C * plateTent k hk A δ₂ x := by
        rw [plateTent]
        field_simp

/-! ## The convolution of two plate bumps at the same centre -/

theorem phiPlate_conv_same (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA1 : (k : ℝ) < A)
    (hA2 : (k : ℝ) * (k + 1) / 2 ≤ A) (Cφ : ℝ) (hCφ : 0 < Cφ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ c : ℝ) (x : E k), 0 < δ₂ → δ₂ ≤ δ₁ →
      (∫ y : E k, phiPlate k hk δ₁ c A Cφ (x - y) * phiPlate k hk δ₂ c A Cφ y)
        ≤ C * Cφ * phiPlate k hk δ₂ c A Cφ x := by
  obtain ⟨C, hC, hClem⟩ := plateTent_conv_le k hk A hA1 hA2
  refine ⟨C, hC, fun δ₁ δ₂ c x hδ20 hδ12 => ?_⟩
  have hδ10 : 0 < δ₁ := lt_of_lt_of_le hδ20 hδ12
  set B := plateGaugeBase k c with hB
  have hdetB : LinearMap.det B ≠ 0 := det_plateGaugeBase_ne_zero k c
  have hBpos : 0 < |LinearMap.det B| := abs_pos.mpr hdetB
  have hg1 : Integrable (fun w : E k => plateTent k hk A δ₁ (B x - w)) := by
    have h : Integrable (fun z : E k => δ₁ ^ (k * (k + 1) / 2) * gaugeU k hk A δ₁ z) :=
      (integrable_gaugeU k hk hA1 hδ10).const_mul _
    have h2 : (fun w : E k => plateTent k hk A δ₁ (B x - w))
        = (fun w : E k => δ₁ ^ (k * (k + 1) / 2) * gaugeU k hk A δ₁ (B x - w)) := by
      funext w; rw [plateTent]
    rw [h2]
    exact h.comp_sub_left (B x)
  have hbdd2 : ∀ w : E k, ‖plateTent k hk A δ₂ w‖ ≤ δ₂ ^ (k * (k + 1) / 2) := fun w => by
    rw [Real.norm_eq_abs, abs_of_nonneg (plateTent_nonneg k hk A hδ20.le w), plateTent, gaugeU,
      coordU]
    calc δ₂ ^ (k * (k + 1) / 2)
          * max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
              fun i => δ₂ ^ (i.val + 1) * |w.ofLp i|) ^ (-A)
        ≤ δ₂ ^ (k * (k + 1) / 2) * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith))
            (pow_nonneg hδ20.le _)
      _ = δ₂ ^ (k * (k + 1) / 2) := mul_one _
  have hint : Integrable (fun w : E k =>
      plateTent k hk A δ₁ (B x - w) * plateTent k hk A δ₂ w) :=
    hg1.mul_bdd
      ((integrable_gaugeU k hk hA1 hδ20).const_mul (δ₂ ^ (k * (k + 1) / 2))
        |>.aestronglyMeasurable)
      (Filter.Eventually.of_forall hbdd2)
  have hsub := Commons.Analysis.Integral.integral_comp_linearMap (μ := (volume : Measure (E k)))
    hdetB hint
  have hfirst : (∫ y : E k, phiPlate k hk δ₁ c A Cφ (x - y) * phiPlate k hk δ₂ c A Cφ y)
      = Cφ ^ 2 * |LinearMap.det B| ^ 2
        * ∫ y : E k, plateTent k hk A δ₁ (B x - B y) * plateTent k hk A δ₂ (B y) := by
    have hpt : ∀ y : E k, phiPlate k hk δ₁ c A Cφ (x - y) * phiPlate k hk δ₂ c A Cφ y
        = Cφ ^ 2 * |LinearMap.det B| ^ 2
          * (plateTent k hk A δ₁ (B x - B y) * plateTent k hk A δ₂ (B y)) := by
      intro y
      rw [phiPlate_eq_plateTent k hk hδ10, phiPlate_eq_plateTent k hk hδ20, hB, map_sub]
      ring
    rw [show (∫ y : E k, phiPlate k hk δ₁ c A Cφ (x - y) * phiPlate k hk δ₂ c A Cφ y)
        = Cφ ^ 2 * |LinearMap.det B| ^ 2
          * ∫ y : E k, plateTent k hk A δ₁ (B x - B y) * plateTent k hk A δ₂ (B y) from ?_]
    · rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hfirst, hsub]
  have h3 := hClem δ₁ δ₂ hδ20 hδ12 (B x)
  have hbInv : |(LinearMap.det B)⁻¹| = |LinearMap.det B|⁻¹ := abs_inv _
  rw [hbInv]
  calc Cφ ^ 2 * |LinearMap.det B| ^ 2
        * (|LinearMap.det B|⁻¹ * ∫ w : E k, plateTent k hk A δ₁ (B x - w) * plateTent k hk A δ₂ w)
      ≤ Cφ ^ 2 * |LinearMap.det B| ^ 2
        * (|LinearMap.det B|⁻¹ * (C * plateTent k hk A δ₂ (B x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hBpos.le))
          (by positivity)
    _ = C * Cφ * phiPlate k hk δ₂ c A Cφ x := by
        rw [phiPlate_eq_plateTent k hk hδ20]
        field_simp
        ring


/-- The plate bump is bounded by its sup, `Cφ|det|`. -/
lemma phiPlate_le_const (k : ℕ) (hk : 1 ≤ k) {δ c A Cφ : ℝ} (hA : 0 < A) (hCφ : 0 ≤ Cφ)
    (y : E k) :
    phiPlate k hk δ c A Cφ y ≤ Cφ * |LinearMap.det (plateGaugeLin k δ c)| := by
  rw [phiPlate]
  have h1 : (max 1 (gauge k hk (plateGaugeLin k δ c y))) ^ (-A) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith)
  calc Cφ * |LinearMap.det (plateGaugeLin k δ c)|
        * (max 1 (gauge k hk (plateGaugeLin k δ c y))) ^ (-A)
      ≤ Cφ * |LinearMap.det (plateGaugeLin k δ c)| * 1 :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hCφ (abs_nonneg _))
    _ = Cφ * |LinearMap.det (plateGaugeLin k δ c)| := mul_one _

/-! ## GLYZ Appendix A, Lemma A.1 -/

/-- **GLYZ Lemma A.1.**  For a fine piece `J` contained in a coarse piece `I` (in particular
`δ_J ≤ δ_I` and `|c_J - c_I| ≤ δ_I`), the convolution of the two plate bumps is dominated by
the fine one: `φ_I ∗ φ_J ≲ φ_J`. -/
theorem phiPlate_conv_le (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA1 : (k : ℝ) < A)
    (hA2 : (k : ℝ) * (k + 1) / 2 ≤ A) (Cφ : ℝ) (hCφ : 0 < Cφ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ_I δ_J c_I c_J : ℝ) (x : E k),
      0 < δ_J → δ_J ≤ δ_I → δ_I ≤ 1 → c_I ∈ Set.Icc (0:ℝ) 1 → c_J ∈ Set.Icc (0:ℝ) 1 →
      |c_J - c_I| ≤ δ_I →
      (∫ y : E k, phiPlate k hk δ_I c_I A Cφ (x - y) * phiPlate k hk δ_J c_J A Cφ y)
        ≤ C * phiPlate k hk δ_J c_J A Cφ x := by
  obtain ⟨ρ, hρ1, hρ⟩ := exists_gauge_plateGaugeLin_compare k hk
  obtain ⟨C, hC, hClem⟩ := phiPlate_conv_same k hk A hA1 hA2 Cφ hCφ
  refine ⟨ρ ^ A * C * Cφ, by positivity, fun δ_I δ_J c_I c_J x hδJ0 hδJI hδI1 hcI hcJ hcc => ?_⟩
  have hδI0 : 0 < δ_I := lt_of_lt_of_le hδJ0 hδJI
  have hApos : (0:ℝ) < A := lt_of_le_of_lt (Nat.cast_nonneg k) hA1
  -- step 1: the same-scale comparison of the bumps at `c_I` and `c_J`
  have hgauge : ∀ y : E k, max 1 (gauge k hk (plateGaugeLin k δ_I c_J (x - y)))
      ≤ ρ * max 1 (gauge k hk (plateGaugeLin k δ_I c_I (x - y))) := fun y => by
    have h := hρ δ_I c_I c_J hδI0 hδI1 hcI hcJ hcc (x - y)
    have hg0 : 0 ≤ gauge k hk (plateGaugeLin k δ_I c_I (x - y)) := gauge_nonneg k hk _
    have hρ0' : (0:ℝ) ≤ ρ := le_trans zero_le_one hρ1
    calc max 1 (gauge k hk (plateGaugeLin k δ_I c_J (x - y)))
        ≤ max 1 (ρ * gauge k hk (plateGaugeLin k δ_I c_I (x - y))) := max_le_max le_rfl h
      _ ≤ ρ * max 1 (gauge k hk (plateGaugeLin k δ_I c_I (x - y))) := by
          rcases le_total 1 (gauge k hk (plateGaugeLin k δ_I c_I (x - y))) with hg | hg
          · rw [max_eq_right hg, max_eq_right (by nlinarith [hg, hρ1, hg0])]
          · rw [max_eq_left hg, mul_one]
            exact max_le hρ1 (by nlinarith [hg, hρ0', hg0])
  have hstep1 : ∀ y : E k, phiPlate k hk δ_I c_I A Cφ (x - y)
      ≤ ρ ^ A * phiPlate k hk δ_I c_J A Cφ (x - y) := fun y =>
    phiPlate_le_of_gauge_le k hk hApos hρ1 hCφ.le (hgauge y)
  -- integrability of the two products
  have hintA : Integrable (fun y : E k =>
      phiPlate k hk δ_I c_I A Cφ (x - y) * phiPlate k hk δ_J c_J A Cφ y) :=
    ((integrable_phiPlate k hk (ne_of_gt hδI0) hA1).comp_sub_left x).mul_bdd
      (integrable_phiPlate k hk (ne_of_gt hδJ0) hA1).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (phiPlate_nonneg k hk δ_J c_J A Cφ hCφ.le y)]
        exact phiPlate_le_const k hk hApos hCφ.le y)
  have hintB : Integrable (fun y : E k =>
      phiPlate k hk δ_I c_J A Cφ (x - y) * phiPlate k hk δ_J c_J A Cφ y) :=
    ((integrable_phiPlate k hk (ne_of_gt hδI0) hA1).comp_sub_left x).mul_bdd
      (integrable_phiPlate k hk (ne_of_gt hδJ0) hA1).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (phiPlate_nonneg k hk δ_J c_J A Cφ hCφ.le y)]
        exact phiPlate_le_const k hk hApos hCφ.le y)
  have h1 : (∫ y : E k,
        phiPlate k hk δ_I c_I A Cφ (x - y) * phiPlate k hk δ_J c_J A Cφ y)
      ≤ ρ ^ A * ∫ y : E k,
        phiPlate k hk δ_I c_J A Cφ (x - y) * phiPlate k hk δ_J c_J A Cφ y := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_ae hintA (hintB.const_mul _)
      (Filter.Eventually.of_forall fun y => ?_)
    calc phiPlate k hk δ_I c_I A Cφ (x - y) * phiPlate k hk δ_J c_J A Cφ y
        ≤ (ρ ^ A * phiPlate k hk δ_I c_J A Cφ (x - y)) * phiPlate k hk δ_J c_J A Cφ y :=
          mul_le_mul_of_nonneg_right (hstep1 y)
            (phiPlate_nonneg k hk δ_J c_J A Cφ hCφ.le y)
      _ = ρ ^ A * (phiPlate k hk δ_I c_J A Cφ (x - y) * phiPlate k hk δ_J c_J A Cφ y) := by
          ring
  have h2 := hClem δ_I δ_J c_J x hδJ0 hδJI
  calc (∫ y : E k, phiPlate k hk δ_I c_I A Cφ (x - y) * phiPlate k hk δ_J c_J A Cφ y)
      ≤ ρ ^ A * (∫ y : E k,
          phiPlate k hk δ_I c_J A Cφ (x - y) * phiPlate k hk δ_J c_J A Cφ y) := h1
    _ ≤ ρ ^ A * (C * Cφ * phiPlate k hk δ_J c_J A Cφ x) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ρ ^ A * C * Cφ * phiPlate k hk δ_J c_J A Cφ x := by ring



/-! ## GLYZ Appendix A, Lemma A.2: the sup comparison on the `H`-ball -/

/-- **GLYZ Lemma A.2, the pointwise comparison.**  The plate bump `φ_{I'}` at level `m'` is
essentially constant on the `H`-ball `B_H(0, hBallR k l m')`:  the ball is contained in a
fixed multiple of the polar plate `𝒰^o_{I'}` (`gauge_plateGaugeLin_projEmbed_le`), so the
shift comparison `phiPlate_shift_le` applies. -/
theorem phiPlate_shift_ball_le {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0:ℝ) 1) (A : ℝ) (hA : 0 < A) (Cφ : ℝ) (hCφ : 0 ≤ Cφ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m' : ℕ) (c' : ℝ), c' ∈ Set.Icc (0:ℝ) 1 →
      |c' - ξ'| ≤ plateHalf m' → ∀ (w : E l), ‖w‖ ≤ hBallR k l m' → ∀ x : E k,
      phiPlate k hk (plateHalf m') c' A Cφ
          (x + projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ C * phiPlate k hk (plateHalf m') c' A Cφ x := by
  obtain ⟨ρ, hρ0, hρ⟩ := gauge_plateGaugeLin_projEmbed_le hk hl hlk hξ'
  refine ⟨(1 + ρ) ^ A, Real.rpow_nonneg (by positivity) _, ?_⟩
  intro m' c' hc' hsep w hw x
  exact phiPlate_shift_le k hk (plateHalf m') c' A Cφ hA hρ0 hCφ
    (x := x) (h := projEmbedLin k l (torsionVec k l hlk ξ') w) (hρ m' c' hc' hsep w hw)

end Submission.Vinogradov

