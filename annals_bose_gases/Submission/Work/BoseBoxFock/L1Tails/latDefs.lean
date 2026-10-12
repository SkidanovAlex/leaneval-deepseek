import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseBoxFock.L1Tails.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.latDefs` — vocabulary for the lattice-Coulomb bound

`Work.BoseBoxFock.L1Tails.latCoulomb_le` (design `sources/boseDCF/bose_L1tails.md`, T4) bounds the
lattice Coulomb sum `ℓ⁻³ Σ_{n ∈ S} ‖Ŵ(κ_n)‖²/‖κ_n‖²` of a weight `W` supported in `ball 0 (ℓ/4)`
by a fixed multiple of the Coulomb energy `∬ W(x)W(y)/‖x−y‖`.

The proof route (design §Q1(b)) is **duality**: take the trial function
`ψ = φ_ℓ · Σ_{n∈S} c_n e^{i⟪κ_n,x⟫}` with `c_n = Ŵ(κ_n)/‖κ_n‖²`, where `φ_ℓ = χ(·/ℓ)` is the
scale-`ℓ` bump (equal to `1` on `ball 0 (ℓ/4)`, supported in `ball 0 (ℓ/2)`), and apply

* T3 (`coulombDual`): `‖∫ W ψ‖² ≤ (4π)⁻¹ (∬WW/r) · Σ_j ∫ ‖∂_jψ‖²`;
* the exact pairing `∫ W ψ = Σ_{n∈S} ‖Ŵ(κ_n)‖²/‖κ_n‖²` (the bump does not change the integral,
  because `φ_ℓ ≡ 1` on `supp W`);
* the Dirichlet bound `Σ_j ∫ ‖∂_jψ‖² ≤ C ℓ³ Σ_{n∈S} ‖Ŵ(κ_n)‖²/‖κ_n‖²`
  (product rule + the lattice orthogonality `∫_{box} e^{i⟪κ_m−κ_n,x⟫} = ℓ³δ_{mn}`
  + Poincaré `‖κ_n‖ ≥ 2π/ℓ` for `n ≠ 0`).

This module fixes the vocabulary of that argument.

## Main definitions

* `bumpFun ℓ` — the scale-`ℓ` bump `φ_ℓ = χ(·/ℓ)`;
* `latWave v` — the plane wave `x ↦ e^{i⟪v,x⟫}`;
* `latPoly ℓ S c` — the trigonometric polynomial `Σ_{n∈S} c n · e^{i⟪κ_n,x⟫}`;
* `latPsi ℓ S c` — the trial function `φ_ℓ · P`;
* `latCoeff ℓ W n` — the dual coefficient `Ŵ(κ_n)/‖κ_n‖²`;
* `latSum ℓ S W` — the target's sum `Σ_{n∈S} ‖Ŵ(κ_n)‖²/‖κ_n‖²`;
* `chiGradBound` — a bound for `‖fderiv χ‖` (so that `‖∇φ_ℓ‖ ≤ chiGradBound/ℓ`);
* `latConst` — the constant `3·chiGradBound²/(2π²) + 2` of the Dirichlet bound.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real Topology ContDiff

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. The scale-`ℓ` bump `φ_ℓ = χ(·/ℓ)` -/

/-- The scale-`ℓ` bump `φ_ℓ x = χ(x/ℓ)`, where `χ` is the corpus bump (`rIn = 1/4`,
`rOut = 1/2`).  It equals `1` on `closedBall 0 (ℓ/4)` and vanishes off `ball 0 (ℓ/2)`. -/
def bumpFun (ℓ : ℝ) : E3 → ℝ := fun x => Submission.BoseGases.chiBase (ℓ⁻¹ • x)

lemma bumpFun_nonneg (ℓ : ℝ) (x : E3) : 0 ≤ bumpFun ℓ x :=
  Submission.BoseGases.chiBase_nonneg _

lemma bumpFun_le_one (ℓ : ℝ) (x : E3) : bumpFun ℓ x ≤ 1 :=
  Submission.BoseGases.chiBase_le_one _

/-- The corpus bump vanishes at distance at least `1/2` from the origin. -/
lemma chiBase_eq_zero_of_half_le_norm {y : E3} (hy : (1 : ℝ) / 2 ≤ ‖y‖) :
    Submission.BoseGases.chiBase y = 0 := by
  apply Submission.BoseGases.chiBump.zero_of_le_dist
  simpa [Submission.BoseGases.chiBump, dist_eq_norm] using hy

lemma bumpFun_eq_one {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ‖x‖ ≤ ℓ / 4) :
    bumpFun ℓ x = 1 := by
  apply Submission.BoseGases.chiBase_eq_one_of_norm_le
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le)]
  calc ℓ⁻¹ * ‖x‖ ≤ ℓ⁻¹ * (ℓ / 4) := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = 1 / 4 := by field_simp

lemma bumpFun_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ℓ / 2 ≤ ‖x‖) :
    bumpFun ℓ x = 0 := by
  apply chiBase_eq_zero_of_half_le_norm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le)]
  have h : (0 : ℝ) < ℓ⁻¹ := by positivity
  calc (1 : ℝ) / 2 = ℓ⁻¹ * (ℓ / 2) := by field_simp
    _ ≤ ℓ⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx h.le

lemma bumpFun_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (bumpFun ℓ) :=
  Submission.BoseGases.chiBase_contDiff.comp (contDiff_id.const_smul ℓ⁻¹)

lemma bumpFun_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) : HasCompactSupport (bumpFun ℓ) := by
  have hsub : Function.support (bumpFun ℓ) ⊆ Metric.closedBall (0 : E3) (ℓ / 2) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hc
    rw [not_le] at hc
    exact hx (bumpFun_eq_zero hℓ hc.le)
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) (ℓ / 2))
    (isClosed_tsupport _) (closure_minimal hsub Metric.isClosed_closedBall)

lemma hasFDerivAt_bumpFun (ℓ : ℝ) (x : E3) :
    HasFDerivAt (bumpFun ℓ)
      ((fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x)).comp
        (ℓ⁻¹ • ContinuousLinearMap.id ℝ E3)) x := by
  have h1 : HasFDerivAt (fun y : E3 => ℓ⁻¹ • y) (ℓ⁻¹ • ContinuousLinearMap.id ℝ E3) x :=
    (ContinuousLinearMap.id ℝ E3).hasFDerivAt.const_smul ℓ⁻¹
  have h2 : HasFDerivAt Submission.BoseGases.chiBase
      (fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x)) (ℓ⁻¹ • x) :=
    (((Submission.BoseGases.chiBase_contDiff.differentiable (by simp)).differentiableAt).hasFDerivAt)
  exact h2.comp x h1

lemma fderiv_bumpFun_apply (ℓ : ℝ) (x w : E3) :
    fderiv ℝ (bumpFun ℓ) x w = ℓ⁻¹ * fderiv ℝ Submission.BoseGases.chiBase (ℓ⁻¹ • x) w := by
  rw [(hasFDerivAt_bumpFun ℓ x).fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]

/-- A bound for `‖fderiv χ‖` (exists because `χ` is `C¹` with compact support). -/
lemma chiGradBound_exists : ∃ M : ℝ, ∀ x : E3, ‖fderiv ℝ Submission.BoseGases.chiBase x‖ ≤ M :=
  (Submission.BoseGases.chiBase_hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (Submission.BoseGases.chiBase_contDiff.continuous_fderiv (by simp))

/-- A fixed bound for `‖∇χ‖`. -/
noncomputable def chiGradBound : ℝ := Classical.choose chiGradBound_exists

lemma chiBase_fderiv_le_bound (x : E3) :
    ‖fderiv ℝ Submission.BoseGases.chiBase x‖ ≤ chiGradBound :=
  Classical.choose_spec chiGradBound_exists x

lemma chiGradBound_nonneg : 0 ≤ chiGradBound :=
  le_trans (norm_nonneg _) (chiBase_fderiv_le_bound 0)

/-- The constant of the Dirichlet bound: `3·chiGradBound²/(2π²) + 2`. -/
noncomputable def latConst : ℝ := 3 * chiGradBound ^ 2 / (2 * Real.pi ^ 2) + 2

lemma latConst_nonneg : 0 ≤ latConst := by
  unfold latConst
  have h : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
  have := chiGradBound_nonneg
  positivity

/-! ## 2. The lattice momenta and the box -/

/-- `kappaL ℓ n = ℓ⁻¹ • vec n` (the definitional unfolding of `kmomInt`). -/
lemma kappaL_eq (ℓ : ℝ) (n : Fin 3 → ℤ) :
    kappaL ℓ n = ℓ⁻¹ • Work.BoseB4.vec n := rfl

/-- `‖vec n‖² = Σ_i (2π n_i)²`. -/
lemma norm_vec_sq (n : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec n‖ ^ 2 = ∑ i : Fin 3, (2 * Real.pi * (n i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Work.BoseB4.vec, WithLp.ofLp_toLp, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi), mul_pow, sq_abs]

/-- A nonzero lattice momentum vector has norm at least `2π`. -/
lemma two_pi_le_norm_vec {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    2 * Real.pi ≤ ‖Work.BoseB4.vec n‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext fun i => by simpa using h i)
  have h1 : (1 : ℝ) ≤ ((n i : ℤ) : ℝ) ^ 2 := by
    have h2 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hi
    nlinarith [abs_nonneg (((n i : ℤ) : ℝ)), sq_abs (((n i : ℤ) : ℝ))]
  have h3 : (2 * Real.pi) ^ 2 ≤ ‖Work.BoseB4.vec n‖ ^ 2 := by
    rw [norm_vec_sq]
    calc (2 * Real.pi) ^ 2 = (2 * Real.pi) ^ 2 * 1 := by ring
      _ ≤ (2 * Real.pi) ^ 2 * ((n i : ℤ) : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 * Real.pi * ((n i : ℤ) : ℝ)) ^ 2 := by ring
      _ ≤ ∑ j : Fin 3, (2 * Real.pi * ((n j : ℤ) : ℝ)) ^ 2 :=
          Finset.single_le_sum (f := fun j : Fin 3 => (2 * Real.pi * ((n j : ℤ) : ℝ)) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [h3, norm_nonneg (Work.BoseB4.vec n), Real.pi_pos]

/-- **Poincaré on the lattice:** a nonzero lattice momentum has norm at least `2π/ℓ`. -/
lemma two_pi_div_le_norm_kappaL {ℓ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    2 * Real.pi / ℓ ≤ ‖kappaL ℓ n‖ := by
  have h := two_pi_le_norm_vec hn
  rw [kappaL_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
  rw [div_le_iff₀ hℓ]
  calc ℓ⁻¹ * ‖Work.BoseB4.vec n‖ * ℓ = ‖Work.BoseB4.vec n‖ := by field_simp
    _ ≥ 2 * Real.pi := h

/-- `⟪p, e_j⟫ = p_j` for the standard basis vector `e_j`. -/
lemma inner_single_right_eq (p : E3) (j : Fin 3) :
    inner ℝ p (EuclideanSpace.single j (1 : ℝ)) = p j := by
  rw [EuclideanSpace.inner_single_right]
  simp

/-- Every point of `ball 0 (ℓ/2)` lies in the box `boxL ℓ = [-ℓ/2,ℓ/2]³`. -/
lemma mem_boxL_of_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ‖x‖ < ℓ / 2) :
    x ∈ Work.BoseK15.corpusBox.boxL ℓ := by
  rw [Work.BoseB4.BoxData.boxL]
  refine Set.mem_smul_set.mpr ⟨ℓ⁻¹ • x, ?_, ?_⟩
  · show ∀ i, |(ℓ⁻¹ • x : E3) i| ≤ (1 / 2 : ℝ)
    intro i
    rw [show (ℓ⁻¹ • x : E3) i = ℓ⁻¹ * x i from rfl, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr hℓ.le)]
    have h2 : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
    have h3 : ℓ⁻¹ * ‖x‖ < 1 / 2 := by
      rw [inv_mul_lt_iff₀ hℓ]; linarith
    have h4 : ℓ⁻¹ * |x i| ≤ ℓ⁻¹ * ‖x‖ :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]

lemma bumpFun_eq_zero_of_notMem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : x ∉ Work.BoseK15.corpusBox.boxL ℓ) : bumpFun ℓ x = 0 := by
  refine bumpFun_eq_zero hℓ ?_
  by_contra hc
  rw [not_le] at hc
  exact hx (mem_boxL_of_norm_lt hℓ hc)

/-! ## 3. The plane waves, the trial polynomial and the dual coefficients -/

/-- The lattice plane wave `x ↦ e^{i⟪v,x⟫}`. -/
def latWave (v : E3) : E3 → ℂ := fun x => Complex.exp (Complex.I * ((inner ℝ v x : ℝ) : ℂ))

/-- The trigonometric polynomial `Σ_{n ∈ S} c n · e^{i⟪κ_n,x⟫}` with `κ_n = kappaL ℓ n`. -/
def latPoly (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) : E3 → ℂ :=
  fun x => ∑ n ∈ S, c n * latWave (kappaL ℓ n) x

/-- The trial function `ψ = φ_ℓ · P` of the duality argument. -/
def latPsi (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) : E3 → ℂ :=
  fun x => (bumpFun ℓ x : ℂ) * latPoly ℓ S c x

/-- The dual coefficient `c_n = Ŵ(κ_n)/‖κ_n‖²` (`Ŵ = kinFT W`). -/
def latCoeff (ℓ : ℝ) (W : E3 → ℝ) (n : Fin 3 → ℤ) : ℂ :=
  Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ)) (kappaL ℓ n)
    / ((‖kappaL ℓ n‖ ^ 2 : ℝ) : ℂ)

/-- The target's sum `Σ_{n ∈ S} ‖Ŵ(κ_n)‖²/‖κ_n‖²`. -/
def latSum (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (W : E3 → ℝ) : ℝ :=
  ∑ n ∈ S, ‖Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ)) (kappaL ℓ n)‖ ^ 2
    / ‖kappaL ℓ n‖ ^ 2

/-- The derivative of the plane wave, evaluated on a vector. -/
lemma fderiv_latWave_apply (v x w : E3) :
    fderiv ℝ (latWave v) x w = latWave v x * (Complex.I * ((inner ℝ v w : ℝ) : ℂ)) := by
  have hL : HasFDerivAt (fun y : E3 => ((inner ℝ v y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (innerSL ℝ v)) x :=
    (Complex.ofRealCLM.comp (innerSL ℝ v)).hasFDerivAt
  have hc : HasFDerivAt (fun y : E3 => Complex.I * ((inner ℝ v y : ℝ) : ℂ))
      (Complex.I • (Complex.ofRealCLM.comp (innerSL ℝ v))) x := hL.const_mul _
  have hce := hc.cexp
  have hfun : latWave v = fun y : E3 => Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) :=
    rfl
  rw [hfun, hce.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    innerSL_apply_apply, smul_eq_mul]

lemma latWave_contDiff (v : E3) : ContDiff ℝ ∞ (latWave v) := by
  have h1 : ContDiff ℝ ∞ (fun y : E3 => ((inner ℝ v y : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp (innerSL ℝ v)).contDiff
  have h2 : ContDiff ℝ ∞ (fun y : E3 => Complex.I * ((inner ℝ v y : ℝ) : ℂ)) :=
    contDiff_const.mul h1
  have h3 : latWave v = fun y : E3 => Complex.exp (Complex.I * ((inner ℝ v y : ℝ) : ℂ)) := rfl
  rw [h3]
  exact ContDiff.cexp h2

lemma latPoly_contDiff (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) :
    ContDiff ℝ ∞ (latPoly ℓ S c) := by
  unfold latPoly
  exact ContDiff.sum fun n _ => ContDiff.mul contDiff_const (latWave_contDiff (kappaL ℓ n))

lemma fderiv_latPoly_apply (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) (x w : E3) :
    fderiv ℝ (latPoly ℓ S c) x w
      = ∑ n ∈ S, c n * (latWave (kappaL ℓ n) x * (Complex.I * ((inner ℝ (kappaL ℓ n) w : ℝ) : ℂ))) := by
  have hdiff : ∀ n ∈ S, DifferentiableAt ℝ (fun x : E3 => c n * latWave (kappaL ℓ n) x) x := by
    intro n _
    have h : Differentiable ℝ (fun x : E3 => c n * latWave (kappaL ℓ n) x) :=
      ((contDiff_const.mul (latWave_contDiff (kappaL ℓ n))).differentiable (by simp))
    exact h x
  have hP : latPoly ℓ S c = fun x : E3 => ∑ n ∈ S, c n * latWave (kappaL ℓ n) x := rfl
  rw [hP, fderiv_fun_sum (fun n hn => hdiff n hn), sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [fderiv_const_mul ((latWave_contDiff (kappaL ℓ n)).differentiable (by simp) x) (c n),
    smul_apply, smul_eq_mul, fderiv_latWave_apply]

lemma latPsi_contDiff (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) :
    ContDiff ℝ ∞ (latPsi ℓ S c) := by
  unfold latPsi
  exact (Complex.ofRealCLM.contDiff.comp (bumpFun_contDiff ℓ)).mul (latPoly_contDiff ℓ S c)

lemma latPsi_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → ℂ) : HasCompactSupport (latPsi ℓ S c) := by
  refine HasCompactSupport.mono (bumpFun_hasCompactSupport hℓ) ?_
  intro x hx
  by_contra hb
  have : bumpFun ℓ x = 0 := by simpa using hb
  exact hx (by simp [latPsi, this])

end Work.BoseBoxFock.L1Tails
