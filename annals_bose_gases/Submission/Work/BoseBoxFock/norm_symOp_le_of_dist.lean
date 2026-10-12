import Mathlib.Tactic.Have
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.FRKDefs
import Submission.Work.BoseBoxFock.contDiff_symH
import Submission.Work.BoseBoxFock.kinFT_iteratedFDeriv_decay
import Submission.Work.BoseBoxFock.lap3_ibp_of_decay
import Submission.Work.BoseBoxFock.lap3_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.norm_symOp_le_of_dist` — the `|z|⁻⁶` kernel-decay estimate

For `x ∉ tsupport g`,

`‖symOp σ g x‖ ≤ 27 (2π)⁻³ ‖D⁶σ‖₁ ∫ ‖g y‖ / ‖x − y‖⁶ .

The proof is the classical "six integrations by parts" kernel estimate, organised so that the
*only* input about `σ` is the integrability of `‖D⁶σ‖` plus a quadratic growth bound, and so that
no growth information about the lower derivatives of `σ` is needed:

* `symH g x = g · (‖x − ·‖⁶)⁻¹` is smooth and compactly supported when `x ∉ tsupport g` (which
  kills the singularity), and `‖x − y‖⁶ · symH g x y = g y`;
* `symPsi g x = conj ∘ kinFT (symU g x)` with `symU g x = conj ∘ symH g x ∘ (x − ·)`: it is
  smooth, its iterated derivatives decay faster than any polynomial,
  `‖symPsi g x p‖ ≤ ∫ ‖g y‖/‖x−y‖⁶`, and the key pointwise identity is
  `lap3 (symPsi g x) = −(p ↦ e^{i⟪p,x⟫} kinFT g p)`;
* the pairing identity `∫ σ · lap3 Ψ = ∫ (lap3 σ) · Ψ` is obtained by truncating `Ψ` with a
  scaled smooth cutoff `θ_R` (so that the unconditional compact-support IBP `lap3_ibp` applies),
  and letting `R → ∞` using the Leibniz bound for sixth derivatives
  (`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one`), the scaling bound on the
  derivatives of `θ_R` and the decay of the derivatives of `Ψ`;
* finally `‖lap3 σ p‖ ≤ 27 ‖D⁶σ p‖` (`NormSymAux.norm_lap3_apply_le`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators SchwartzMap FourierTransform

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The auxiliary functions `symH`, `symU`, `symPsi`, `symW` -/

/-- `symH g x y = g y · (‖x − y‖⁶)⁻¹`; the singular factor at `y = x` is harmless because the
applications have `x ∉ tsupport g` (hence `g ≡ 0` near `x`). -/
noncomputable def symH (g : E3 → ℂ) (x : E3) : E3 → ℂ :=
  fun y => g y * ((‖x - y‖ ^ 6 : ℝ) : ℂ)⁻¹

/-- `symU g x y = conj (symH g x (x − y))`. -/
noncomputable def symU (g : E3 → ℂ) (x : E3) : E3 → ℂ :=
  fun y => star (symH g x (x - y))

/-- `symPsi g x = conj ∘ kinFT (symU g x)`. -/
noncomputable def symPsi (g : E3 → ℂ) (x : E3) : E3 → ℂ :=
  fun p => star (Submission.BoseGases.kinFT (symU g x) p)

/-- `symW g x p = e^{i⟪p,x⟫} · kinFT g p`: the integrand of `symOp`, up to the `σ`-factor. -/
noncomputable def symW (g : E3 → ℂ) (x : E3) : E3 → ℂ :=
  fun p => Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * Submission.BoseGases.kinFT g p

/-! ## 2. Elementary properties -/

/-- Bound for the operator norm of `conj` as a real-linear map. -/
lemma norm_conjCLE_le_one : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun z => ?_
  rw [one_mul]
  exact le_of_eq (Complex.norm_conj z)

/-- Conjugating a function does not increase the norm of its iterated derivatives. -/
lemma norm_iteratedFDeriv_conj_le (F : E3 → ℂ) (p : E3) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q => star (F q)) p‖ ≤ ‖iteratedFDeriv ℝ k F p‖ := by
  have h := Complex.conjCLE.iteratedFDeriv_comp_left (𝕜 := ℝ) (f := F) (x := p) (i := k)
  have hfun : (fun q => star (F q)) = (Complex.conjCLE : ℂ → ℂ) ∘ F := rfl
  rw [hfun, h]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  calc ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ * ‖iteratedFDeriv ℝ k F p‖
      ≤ 1 * ‖iteratedFDeriv ℝ k F p‖ :=
        mul_le_mul_of_nonneg_right norm_conjCLE_le_one (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k F p‖ := one_mul _

theorem symH_contDiff {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) {x : E3}
    (hx : x ∉ tsupport g) : ContDiff ℝ (⊤ : ENat) (symH g x) :=
  contDiff_symH hg hx

lemma norm_symH (g : E3 → ℂ) (x y : E3) : ‖symH g x y‖ = ‖g y‖ / ‖x - y‖ ^ 6 := by
  have h1 : ‖(((‖x - y‖ ^ 6 : ℝ)) : ℂ)‖ = ‖x - y‖ ^ 6 := by
    have h2 : ‖(((‖x - y‖ ^ 6 : ℝ)) : ℂ)‖ = |‖x - y‖ ^ 6| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (norm_nonneg _)]
      congr 1
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    rw [h2, abs_of_nonneg (by positivity)]
  rw [symH, norm_mul, norm_inv, h1, div_eq_mul_inv]

lemma symH_mul (g : E3 → ℂ) {x : E3} (hx : x ∉ tsupport g) (y : E3) :
    (((‖x - y‖ ^ 6 : ℝ)) : ℂ) * symH g x y = g y := by
  rw [symH]
  by_cases h0 : (‖x - y‖ ^ 6 : ℝ) = 0
  · have hxy : y = x := by
      have hnorm : ‖x - y‖ = 0 := by
        have h := pow_eq_zero_iff (n := 6) (by norm_num) |>.mp h0
        simpa using h
      have hsub : x - y = 0 := norm_eq_zero.mp hnorm
      exact (sub_eq_zero.mp hsub).symm
    subst hxy
    simp [image_eq_zero_of_notMem_tsupport hx]
  · have hr : (((‖x - y‖ ^ 6 : ℝ)) : ℂ) ≠ 0 := by
      simpa using h0
    rw [mul_comm (g y), ← mul_assoc, mul_inv_cancel₀ hr, one_mul]

lemma symH_hasCompactSupport (g : E3 → ℂ) (x : E3) (hgc : HasCompactSupport g) :
    HasCompactSupport (symH g x) := by
  refine HasCompactSupport.intro' hgc.isCompact (isClosed_tsupport g) fun y hy => ?_
  rw [symH, image_eq_zero_of_notMem_tsupport hy, zero_mul]

theorem symU_contDiff {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) {x : E3}
    (hx : x ∉ tsupport g) : ContDiff ℝ (⊤ : ENat) (symU g x) := by
  have h1 : ContDiff ℝ (⊤ : ENat) (fun y : E3 => symH g x (x - y)) :=
    (symH_contDiff hg hx).comp (contDiff_const.sub contDiff_id)
  have h2 := Complex.conjCLE.contDiff.comp h1
  have h3 : (symU g x) = (Complex.conjCLE : ℂ → ℂ) ∘ fun y : E3 => symH g x (x - y) := rfl
  rw [h3]
  exact h2

lemma symU_hasCompactSupport (g : E3 → ℂ) (x : E3) (hgc : HasCompactSupport g) :
    HasCompactSupport (symU g x) := by
  have h1 : HasCompactSupport (symH g x) := symH_hasCompactSupport g x hgc
  refine HasCompactSupport.of_support_subset_isCompact
    (K := ⇑(Homeomorph.subLeft x) '' tsupport (symH g x))
    (h1.isCompact.image (Homeomorph.subLeft x).continuous) ?_
  intro y hy
  rw [Function.mem_support] at hy
  refine ⟨x - y, subset_tsupport _ ?_, ?_⟩
  · intro hzero
    exact hy (by rw [symU, hzero, star_zero])
  · rw [Homeomorph.subLeft_apply]; abel

/-- The `kinFT` of a smooth compactly supported function is smooth. -/
lemma contDiff_kinFT {u : E3 → ℂ} (hu : ContDiff ℝ (⊤ : ENat) u) (huc : HasCompactSupport u) :
    ContDiff ℝ (⊤ : ENat) (fun p => Submission.BoseGases.kinFT u p) := by
  let F : 𝓢(E3, ℂ) := huc.toSchwartzMap hu
  have hcoe : (⇑F : E3 → ℂ) = u := funext fun _ => rfl
  have h1 : ContDiff ℝ (⊤ : ENat)
      (fun p : E3 => (𝓕 F) (((2 * Real.pi)⁻¹ : ℝ) • p)) :=
    ((𝓕 F).smooth (⊤ : ENat)).comp (contDiff_const_smul _)
  have hfun : (fun p : E3 => Submission.BoseGases.kinFT u p)
      = fun p : E3 => (𝓕 F) (((2 * Real.pi)⁻¹ : ℝ) • p) := by
    funext p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hcoe]
    exact congrFun (SchwartzMap.fourier_coe F).symm _
  rw [hfun]
  exact h1

theorem symPsi_contDiff {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) {x : E3}
    (hx : x ∉ tsupport g) (hgc : HasCompactSupport g) :
    ContDiff ℝ (⊤ : ENat) (symPsi g x) := by
  have h1 := contDiff_kinFT (symU_contDiff hg hx) (symU_hasCompactSupport g x hgc)
  have h2 := Complex.conjCLE.contDiff.comp h1
  have h3 : (symPsi g x)
      = (Complex.conjCLE : ℂ → ℂ) ∘ fun p : E3 => Submission.BoseGases.kinFT (symU g x) p := rfl
  rw [h3]
  exact h2

/-- Pointwise bound of `symPsi`. -/
lemma norm_symPsi_le (g : E3 → ℂ) (x p : E3) :
    ‖symPsi g x p‖ ≤ ∫ y : E3, ‖g y‖ / ‖x - y‖ ^ 6 := by
  have hp : ‖symPsi g x p‖ = ‖Submission.BoseGases.kinFT (symU g x) p‖ := by
    rw [symPsi, norm_star]
  rw [hp]
  have h1 : ‖Submission.BoseGases.kinFT (symU g x) p‖ ≤ ∫ y : E3, ‖symU g x y‖ := by
    have hb : ∀ y : E3, ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
        symU g x y‖ = ‖symU g x y‖ := by
      intro y
      rw [norm_mul]
      have he : ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))‖ = 1 := by
        have harg : -(Complex.I * (inner ℝ p y : ℂ))
            = ((-(inner ℝ p y) : ℝ) : ℂ) * Complex.I := by
          rw [Complex.ofReal_neg]; ring
        rw [harg]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [he, one_mul]
    have h2 : (∫ y : E3, ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
        symU g x y‖) = ∫ y : E3, ‖symU g x y‖ :=
      integral_congr_ae (Filter.Eventually.of_forall hb)
    rw [Submission.BoseGases.kinFT, ← h2]
    exact norm_integral_le_integral_norm _
  refine h1.trans (le_of_eq ?_)
  have hsub : (∫ y : E3, ‖symU g x y‖) = ∫ y : E3, ‖symH g x (x - y)‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ‖star (symH g x (x - y))‖ = ‖symH g x (x - y)‖
    rw [norm_star]
  rw [hsub, MeasureTheory.integral_sub_left_eq_self (fun z => ‖symH g x z‖) volume x]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => norm_symH g x y)

/-- The iterated derivatives of `symPsi g x` decay faster than any polynomial. -/
theorem symPsi_iteratedFDeriv_decay {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {x : E3} (hx : x ∉ tsupport g) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3,
      ‖iteratedFDeriv ℝ k (symPsi g x) p‖ ≤ C / (1 + ‖p‖) ^ N := by
  obtain ⟨C, hC0, hC⟩ := kinFT_iteratedFDeriv_decay (symU_contDiff hg hx)
    (symU_hasCompactSupport g x hgc) k N
  refine ⟨C, hC0, fun p => ?_⟩
  have hfun : (symPsi g x) = fun q => star (Submission.BoseGases.kinFT (symU g x) q) := rfl
  rw [hfun]
  exact (norm_iteratedFDeriv_conj_le (Submission.BoseGases.kinFT (symU g x)) p k).trans (hC p)


/-! ## 3. The pointwise identity `lap3 (symPsi g x) = - symW g x` -/

/-- `lap3` commutes with conjugation. -/
lemma lap3_star_comp {F : E3 → ℂ} (hF : ContDiff ℝ (⊤ : ENat) F) :
    lap3 (fun p => star (F p)) = fun p => star (lap3 F p) := by
  funext p
  have key : ∀ L : List E3, dIter (fun q => star (F q)) L p = star (dIter F L p) := by
    intro L
    have hsm : ContDiff ℝ (⊤ : ENat) (fun q => star (F q)) :=
      Complex.conjCLE.contDiff.comp hF
    rw [dIter_eq_iteratedFDeriv _ hsm L p, dIter_eq_iteratedFDeriv _ hF L p]
    have hfun : (fun q => star (F q)) = (Complex.conjCLE : ℂ → ℂ) ∘ F := rfl
    rw [hfun, Complex.conjCLE.iteratedFDeriv_comp_left (𝕜 := ℝ) (f := F) (x := p) (i := L.length)]
    rfl
  simp only [lap3, Finset.sum_apply]
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact key (lap3List a b c)

/-- Conjugation of the `kinFT`: `star (kinFT w p) = ∫ z, e^{i⟪p,z⟫} star (w z)`. -/
lemma star_kinFT_eq (w : E3 → ℂ) (hwc : Continuous w) (hws : HasCompactSupport w) (p : E3) :
    star (Submission.BoseGases.kinFT w p)
      = ∫ z : E3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * star (w z) := by
  have hcont : Continuous fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) := by
    fun_prop
  have hint : Integrable (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * w z) :=
    (hcont.mul hwc).integrable_of_hasCompactSupport (hws.mul_left)
  rw [Submission.BoseGases.kinFT]
  change (Complex.conjCLE : ℂ →L[ℝ] ℂ) (∫ y : E3,
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * w y)
    = ∫ z : E3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * star (w z)
  rw [← ContinuousLinearMap.integral_comp_comm (Complex.conjCLE.toContinuousLinearMap) hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  change star (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * w z)
    = Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * star (w z)
  rw [star_mul']
  rw [RCLike.star_def]
  rw [← Complex.exp_conj]
  have harg : (starRingEnd ℂ) (-(Complex.I * (inner ℝ p z : ℂ)))
      = Complex.I * (inner ℝ p z : ℂ) := by
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [harg]

/-- Change of variables in the `kinFT`-integral: `∫ z, e^{i⟪p,z⟫} g (x − z) = e^{i⟪p,x⟫} kinFT g p`. -/
lemma integral_exp_mul_sub (g : E3 → ℂ) (x p : E3) :
    (∫ z : E3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * g (x - z))
      = Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * Submission.BoseGases.kinFT g p := by
  have hpt : ∀ z : E3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * g (x - z)
      = Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        (Complex.exp (-(Complex.I * (inner ℝ p (x - z) : ℂ))) * g (x - z)) := by
    intro z
    have h1 : inner ℝ p (x - z) = inner ℝ p x - inner ℝ p z := inner_sub_right p x z
    have harg : Complex.I * (inner ℝ p z : ℂ)
        = Complex.I * (inner ℝ p x : ℂ) + (-(Complex.I * (inner ℝ p (x - z) : ℂ))) := by
      rw [h1]; push_cast; ring_nf
    rw [harg, Complex.exp_add]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    MeasureTheory.integral_sub_left_eq_self
      (fun y => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g y) volume x]
  rfl

/-- **The pointwise identity**: `lap3` of `symPsi g x` is minus `symW g x`. -/
theorem lap3_symPsi {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) {x : E3} (hx : x ∉ tsupport g)
    (hgc : HasCompactSupport g) :
    lap3 (symPsi g x) = fun p => - symW g x p := by
  funext p
  have hsm : ContDiff ℝ (⊤ : ENat) (symU g x) := symU_contDiff hg hx
  have hsc : HasCompactSupport (symU g x) := symU_hasCompactSupport g x hgc
  have hF : ContDiff ℝ (⊤ : ENat) (fun p => Submission.BoseGases.kinFT (symU g x) p) :=
    contDiff_kinFT hsm hsc
  have h1 : symPsi g x = fun p => star (Submission.BoseGases.kinFT (symU g x) p) := rfl
  rw [h1, lap3_star_comp hF, lap3_kinFT hsm hsc]
  -- `star (-kinFT w p)` where `w z = ‖z‖⁶ · symU g x z`
  have hwc : Continuous (fun z : E3 => (((‖z‖ ^ 6 : ℝ)) : ℂ) * symU g x z) := by fun_prop
  have hws : HasCompactSupport (fun z : E3 => (((‖z‖ ^ 6 : ℝ)) : ℂ) * symU g x z) :=
    hsc.mul_left
  have h2 : star (Submission.BoseGases.kinFT (fun z : E3 => (((‖z‖ ^ 6 : ℝ)) : ℂ) *
      symU g x z) p) = ∫ z : E3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
        star ((((‖z‖ ^ 6 : ℝ)) : ℂ) * symU g x z) :=
    star_kinFT_eq _ hwc hws p
  show star (- Submission.BoseGases.kinFT
      (fun z : E3 => (((‖z‖ ^ 6 : ℝ)) : ℂ) * symU g x z) p) = - symW g x p
  rw [star_neg, h2]
  -- the integrand is `e^{i⟪p,z⟫} g (x - z)`
  have h3 : (∫ z : E3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
        star ((((‖z‖ ^ 6 : ℝ)) : ℂ) * symU g x z))
      = ∫ z : E3, Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * g (x - z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show Complex.exp (Complex.I * (inner ℝ p z : ℂ)) *
        star ((((‖z‖ ^ 6 : ℝ)) : ℂ) * symU g x z)
      = Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * g (x - z)
    have h4 : star ((((‖z‖ ^ 6 : ℝ)) : ℂ) * symU g x z)
        = (((‖x - (x - z)‖ ^ 6 : ℝ)) : ℂ) * symH g x (x - z) := by
      show star ((((‖z‖ ^ 6 : ℝ)) : ℂ) * star (symH g x (x - z)))
        = (((‖x - (x - z)‖ ^ 6 : ℝ)) : ℂ) * symH g x (x - z)
      rw [star_mul', star_star]
      have h5 : star ((((‖z‖ ^ 6 : ℝ)) : ℂ)) = (((‖z‖ ^ 6 : ℝ)) : ℂ) := by
        rw [RCLike.star_def, Complex.conj_ofReal]
      rw [h5]
      congr 1
      rw [show x - (x - z) = z by abel]
    rw [h4, symH_mul g hx]
  rw [h3, integral_exp_mul_sub g x p]
  rfl


/-- Linearity of `lap3` on smooth functions (needed to compare `lap3 (θ_R Ψ)` with `lap3 Ψ`). -/
lemma lap3_sub {f g : E3 → ℂ} (hf : ContDiff ℝ (⊤ : ENat) f)
    (hg : ContDiff ℝ (⊤ : ENat) g) : lap3 (f - g) = lap3 f - lap3 g := by
  funext p
  have key : ∀ L : List E3, dIter (f - g) L p = dIter f L p - dIter g L p := by
    intro L
    have hfg : ContDiff ℝ (⊤ : ENat) (f - g) := hf.sub hg
    rw [dIter_eq_iteratedFDeriv _ hfg L p, dIter_eq_iteratedFDeriv _ hf L p,
      dIter_eq_iteratedFDeriv _ hg L p,
      iteratedFDeriv_sub (hf.of_le (WithTop.coe_le_coe.mpr le_top))
        (hg.of_le (WithTop.coe_le_coe.mpr le_top))]
    rfl
  simp only [Pi.sub_apply, lap3]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact key (lap3List a b c)


/-- `lap3` is continuous for smooth functions. -/
lemma continuous_lap3 {f : E3 → ℂ} (hf : ContDiff ℝ (⊤ : ENat) f) : Continuous (lap3 f) := by
  have h : lap3 f = fun p => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, dIter f (lap3List a b c) p :=
    rfl
  rw [h]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_finsetSum _ fun c _ => (contDiff_dIter hf (lap3List a b c)).continuous

/-- Linearity of `lap3` (addition) on smooth functions. -/
lemma lap3_add {f g : E3 → ℂ} (hf : ContDiff ℝ (⊤ : ENat) f)
    (hg : ContDiff ℝ (⊤ : ENat) g) : lap3 (f + g) = lap3 f + lap3 g := by
  funext p
  have key : ∀ L : List E3, dIter (f + g) L p = dIter f L p + dIter g L p := by
    intro L
    have hfg : ContDiff ℝ (⊤ : ENat) (f + g) := hf.add hg
    rw [dIter_eq_iteratedFDeriv _ hfg L p, dIter_eq_iteratedFDeriv _ hf L p,
      dIter_eq_iteratedFDeriv _ hg L p,
      iteratedFDeriv_add (hf.of_le (WithTop.coe_le_coe.mpr le_top))
        (hg.of_le (WithTop.coe_le_coe.mpr le_top))]
    rfl
  simp only [Pi.add_apply, lap3]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => key (lap3List a b c)

/-- Norm bound for the multiplication as a bilinear map. -/
lemma norm_mul_le_one : ‖(ContinuousLinearMap.mul ℝ ℂ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun z => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
  rw [one_mul]
  simpa using norm_mul_le z w

/-- Integrability of a weight times a rapidly decaying function. -/
lemma integrable_one_add_sq_mul_decay {h : E3 → ℝ} (hh : AEStronglyMeasurable h)
    (hnn : ∀ p : E3, 0 ≤ h p)
    (hde : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3, h p ≤ C / (1 + ‖p‖) ^ 8) :
    Integrable (fun p : E3 => (1 + ‖p‖) ^ 2 * h p) := by
  obtain ⟨C, hC0, hC⟩ := hde
  have hbase : Integrable (fun p : E3 => ((1 + ‖p‖) ^ 6)⁻¹) := by
    have h := integrable_one_add_norm (E := E3) (μ := volume) (r := 6) (by
      simp only [finrank_euclideanSpace_fin]; norm_num)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    show (1 + ‖p‖) ^ (-(6 : ℝ)) = ((1 + ‖p‖) ^ 6)⁻¹
    rw [show (-(6 : ℝ)) = -((6 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖), Real.rpow_natCast]
  refine (hbase.const_mul (C + 1)).mono' ?_ ?_
  · exact ((continuous_const.add continuous_norm).pow 2).aestronglyMeasurable.mul hh
  refine Filter.Eventually.of_forall fun p => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hnn p))]
  have hle := hC p
  rw [div_eq_mul_inv] at hle
  have h2 : (0 : ℝ) ≤ (1 + ‖p‖) ^ 2 := by positivity
  calc (1 + ‖p‖) ^ 2 * h p ≤ (1 + ‖p‖) ^ 2 * (C * ((1 + ‖p‖) ^ 8)⁻¹) :=
        mul_le_mul_of_nonneg_left hle h2
    _ = C * ((1 + ‖p‖) ^ 6)⁻¹ := by
        have hne : (1 + ‖p‖ : ℝ) ≠ 0 := by positivity
        field_simp
    _ ≤ (C + 1) * ((1 + ‖p‖) ^ 6)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)


/-- Derivative bounds for the ("cutoff minus one") function `(θ n : ℂ) - 1`. -/
lemma cutoff_diff_deriv {θ : ℝ → E3 → ℝ} (hθcd : ∀ R, ContDiff ℝ (⊤ : ENat) (θ R))
    (hθder : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ R, 1 ≤ R → ∀ x : E3,
      ‖iteratedFDeriv ℝ k (θ R) x‖ ≤ C / R ^ k)
    (i : ℕ) (hi : 1 ≤ i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ p : E3,
      ‖iteratedFDeriv ℝ i (fun q : E3 => (((θ n q : ℝ)) : ℂ) - 1) p‖ ≤ C / n ^ i := by
  obtain ⟨C, hC0, hC⟩ := hθder i
  refine ⟨C, hC0, fun n hn p => ?_⟩
  have hcd : ContDiff ℝ (⊤ : ENat) (fun q : E3 => (((θ n q : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hθcd n)
  have hsub : iteratedFDeriv ℝ i (fun q : E3 => (((θ n q : ℝ)) : ℂ) - 1) p
      = iteratedFDeriv ℝ i (fun q : E3 => (((θ n q : ℝ)) : ℂ)) p := by
    rw [show (fun q : E3 => (((θ n q : ℝ)) : ℂ) - 1)
        = (fun q : E3 => (((θ n q : ℝ)) : ℂ)) - fun _ : E3 => (1 : ℂ) from rfl]
    rw [iteratedFDeriv_sub (hcd.of_le (WithTop.coe_le_coe.mpr le_top))
      (contDiff_const.of_le (WithTop.coe_le_coe.mpr le_top))]
    simp [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by omega : i ≠ 0)]
  rw [hsub]
  rw [show (fun q : E3 => (((θ n q : ℝ)) : ℂ)) = ⇑Complex.ofRealLI ∘ θ n from rfl]
  rw [LinearIsometry.norm_iteratedFDeriv_comp_left (g := Complex.ofRealLI) (f := θ n)
    (hθcd n).contDiffAt (x := p) (i := i) (WithTop.coe_le_coe.mpr le_top)]
  exact hC n (by exact_mod_cast hn) p

theorem norm_symOp_le_of_dist {σ : EuclideanSpace ℝ (Fin 3) → ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hσ : ContDiff ℝ (⊤ : ENat) σ)
    (hσ6 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖iteratedFDeriv ℝ 6 σ p‖))
    (hσg : ∃ A : ℝ, ∀ p : EuclideanSpace ℝ (Fin 3), |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∉ tsupport g) :
    ‖Work.BoseBoxFock.symOp σ g x‖ ≤ 27 * ((2 * Real.pi) ^ 3)⁻¹ * Work.BoseBoxFock.iterDerivL1 6 σ *
      ∫ y : EuclideanSpace ℝ (Fin 3), ‖g y‖ / ‖x - y‖ ^ 6 := by
  classical
  obtain ⟨Aσ, hAσ⟩ := hσg
  have hAσ0 : 0 ≤ Aσ := by
    have h1 := hAσ 0
    have h2 : (1 : ℝ) ≤ (1 + ‖(0 : E3)‖) ^ 2 := by norm_num
    nlinarith [abs_nonneg (σ 0)]
  set A : ℝ := ∫ y : E3, ‖g y‖ / ‖x - y‖ ^ 6 with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]; exact integral_nonneg fun y => by positivity
  set F : E3 → ℂ := fun p => (σ p : ℂ) with hFdef
  have hFcd : ContDiff ℝ (⊤ : ENat) F := Complex.ofRealCLM.contDiff.comp hσ
  have hΨcd : ContDiff ℝ (⊤ : ENat) (symPsi g x) := symPsi_contDiff hg hx hgc
  have hΨbdd : ∀ p : E3, ‖symPsi g x p‖ ≤ A := fun p => by
    rw [hAdef]; exact norm_symPsi_le g x p
  -- integrability of `|σ|` against the (rapidly decaying) derivatives of `Ψ`
  have hAint : ∀ j : ℕ, Integrable (fun p : E3 => |σ p| * ‖iteratedFDeriv ℝ j (symPsi g x) p‖) := by
    intro j
    obtain ⟨C, hC0, hC⟩ := symPsi_iteratedFDeriv_decay hg hgc hx j 8
    have hcont : AEStronglyMeasurable (fun p : E3 => ‖iteratedFDeriv ℝ j (symPsi g x) p‖) :=
      ((hΨcd.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).norm).aestronglyMeasurable
    have hbase := integrable_one_add_sq_mul_decay hcont (fun p => norm_nonneg _) ⟨C, hC0, hC⟩
    refine (hbase.const_mul Aσ).mono' ((hσ.continuous.abs.aestronglyMeasurable).mul hcont) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    calc |σ p| * ‖iteratedFDeriv ℝ j (symPsi g x) p‖
        ≤ (Aσ * (1 + ‖p‖) ^ 2) * ‖iteratedFDeriv ℝ j (symPsi g x) p‖ :=
          mul_le_mul_of_nonneg_right (hAσ p) (norm_nonneg _)
      _ = Aσ * ((1 + ‖p‖) ^ 2 * ‖iteratedFDeriv ℝ j (symPsi g x) p‖) := by ring
  -- integrability of `‖D⁶F‖`
  have hF6 : Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 F p‖) := by
    have hfun : (fun p : E3 => ‖iteratedFDeriv ℝ 6 F p‖)
        = fun p : E3 => ‖iteratedFDeriv ℝ 6 σ p‖ := by
      funext p
      have h := LinearIsometry.norm_iteratedFDeriv_comp_left (g := Complex.ofRealLI) (f := σ)
        hσ.contDiffAt (x := p) (i := 6) (WithTop.coe_le_coe.mpr le_top)
      have hF : F = ⇑Complex.ofRealLI ∘ σ := rfl
      rw [hF, h]
    rw [hfun]
    exact hσ6
  -- the pointwise identity `W = -lap3 Ψ`
  have hW : ∀ p : E3, symW g x p = - lap3 (symPsi g x) p := by
    intro p
    have h := congrFun (lap3_symPsi hg hx hgc) p
    rw [h, neg_neg]

  -- the relation between `‖F p‖` and `|σ p|`
  have hnormF : ∀ p : E3, ‖F p‖ = |σ p| := fun p => by
    simpa [hFdef] using RCLike.norm_ofReal (σ p)

  -- ===== the truncation argument: `∫ F · lap3 Ψ = ∫ lap3 F · Ψ` =====
  have hkey : (∫ p : E3, F p * lap3 (symPsi g x) p)
      = ∫ p : E3, lap3 F p * symPsi g x p := by
    refine lap3_ibp_of_decay hFcd ?_ hΨcd ⟨A, hA0, hΨbdd⟩ ?_
    · refine Integrable.mono' (hF6.const_mul 27) (continuous_lap3 hFcd).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun p => norm_lap3_apply_le F hFcd p
    · intro k hk
      refine (hAint k).congr (Filter.Eventually.of_forall fun p => ?_)
      show |σ p| * ‖iteratedFDeriv ℝ k (symPsi g x) p‖
        = ‖F p‖ * ‖iteratedFDeriv ℝ k (symPsi g x) p‖
      rw [hnormF p]

  -- ===== the two integral identities =====
  have hF6eq : (∫ p : E3, ‖iteratedFDeriv ℝ 6 F p‖) = iterDerivL1 6 σ := by
    rw [iterDerivL1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have h := LinearIsometry.norm_iteratedFDeriv_comp_left (g := Complex.ofRealLI) (f := σ)
      hσ.contDiffAt (x := p) (i := 6) (WithTop.coe_le_coe.mpr le_top)
    have hF : F = ⇑Complex.ofRealLI ∘ σ := rfl
    simpa [hF] using h

  have hIexp : (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * (σ p : ℂ) *
      Submission.BoseGases.kinFT g p) = - ∫ p : E3, lap3 F p * symPsi g x p := by
    have h1 : (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * (σ p : ℂ) *
        Submission.BoseGases.kinFT g p) = ∫ p : E3, F p * symW g x p := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [hFdef, symW]
      ring
    have h2 : (∫ p : E3, F p * symW g x p)
        = - ∫ p : E3, F p * lap3 (symPsi g x) p := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [hW p]
      ring
    rw [h1, h2, hkey]

  -- ===== integrability of the two integrands =====
  have hGint : Integrable (fun p : E3 => 27 * ‖iteratedFDeriv ℝ 6 F p‖ * A) :=
    (hF6.const_mul 27).mul_const A

  have hLint : Integrable (fun p : E3 => ‖lap3 F p * symPsi g x p‖) := by
    refine hGint.mono' ((continuous_lap3 hFcd).mul hΨcd.continuous).norm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul]
    calc ‖lap3 F p‖ * ‖symPsi g x p‖
        ≤ (27 * ‖iteratedFDeriv ℝ 6 F p‖) * A :=
          mul_le_mul (norm_lap3_apply_le F hFcd p) (hΨbdd p) (norm_nonneg _) (by positivity)
      _ = 27 * ‖iteratedFDeriv ℝ 6 F p‖ * A := by ring

  -- ===== the norm bound on the multiplier integral =====
  have hbound : ‖(∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * (σ p : ℂ) *
      Submission.BoseGases.kinFT g p)‖ ≤ 27 * iterDerivL1 6 σ * A := by
    rw [hIexp, norm_neg]
    calc ‖∫ p : E3, lap3 F p * symPsi g x p‖
        ≤ ∫ p : E3, ‖lap3 F p * symPsi g x p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p : E3, 27 * ‖iteratedFDeriv ℝ 6 F p‖ * A :=
          integral_mono_ae hLint hGint (Filter.Eventually.of_forall fun p => by
            show ‖lap3 F p * symPsi g x p‖ ≤ 27 * ‖iteratedFDeriv ℝ 6 F p‖ * A
            rw [norm_mul]
            exact mul_le_mul (norm_lap3_apply_le F hFcd p) (hΨbdd p) (norm_nonneg _)
              (by positivity))
      _ = 27 * iterDerivL1 6 σ * A := by
          rw [show (∫ p : E3, 27 * ‖iteratedFDeriv ℝ 6 F p‖ * A)
                = (∫ p : E3, 27 * ‖iteratedFDeriv ℝ 6 F p‖) * A from
              integral_mul_const A _,
            show (∫ p : E3, 27 * ‖iteratedFDeriv ℝ 6 F p‖)
                = 27 * ∫ p : E3, ‖iteratedFDeriv ℝ 6 F p‖ from
              integral_const_mul 27 _,
            hF6eq]

  -- ===== assembly =====
  have hsymOp : symOp σ g x = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
      (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * (σ p : ℂ) *
        Submission.BoseGases.kinFT g p) := rfl
  rw [hsymOp, norm_mul]
  have hc : ‖((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ)‖ = ((2 * Real.pi) ^ 3)⁻¹ := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (by positivity)]
  rw [hc]
  exact (mul_le_mul_of_nonneg_left hbound (by positivity)).trans (le_of_eq (by ring))
