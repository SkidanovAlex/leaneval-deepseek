import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradIntegral
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.PressureOn.normSlopePhysVelLe
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.exists_const_Dpair_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter FiniteTimeSingularity
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.MollAux

/-! ## Small helpers -/

/-- The pairing `x ↦ ⟪Φ x, f x⟫` has compact support as soon as `f` does. -/
lemma hasCompactSupport_inner_right {Φ f : R3 → R3} (hfc : HasCompactSupport f) :
    HasCompactSupport (fun x => inner ℝ (Φ x) (f x)) :=
  HasCompactSupport.intro hfc (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_right])

/-- The inner product against a *fixed* vector in the **second** slot commutes with the Bochner
integral (mirror of `Auxiliary.integral_inner_eq_inner_integral`, where the fixed vector sits in
the first slot). -/
lemma integral_inner_eq_inner_integral_right (g : R3) (ψ : R3 → R3) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, inner ℝ (ψ x) g = inner ℝ (∫ x, ψ x) g := by
  have h := Auxiliary.integral_inner_eq_inner_integral g ψ hψ hψc
  rw [show (∫ x : R3, inner ℝ (ψ x) g) = ∫ x : R3, inner ℝ g (ψ x) from
        integral_congr_ae (Eventually.of_forall fun x => (real_inner_comm (ψ x) g).symm),
      show inner ℝ (∫ x : R3, ψ x) g = inner ℝ g (∫ x : R3, ψ x) from
        (real_inner_comm (∫ x : R3, ψ x) g).symm]
  exact h

/-- Linearity of the pairing `Dpair` in the test field, in the form needed for the argument:
for two smooth compactly supported fields `f`, `h`,
`Dpair q Φ (f - h) = Dpair q Φ f - Dpair q Φ h`. -/
lemma Dpair_sub (q : R3 → ℝ) (Φ : R3 → R3) (hq : Continuous q) (hΦ : Continuous Φ)
    (f h : R3 → R3) (hf : ∀ n : ℕ, ContDiff ℝ n f) (hfc : HasCompactSupport f)
    (hg : ∀ n : ℕ, ContDiff ℝ n h) (hgc : HasCompactSupport h) :
    Dpair q Φ (f - h) = Dpair q Φ f - Dpair q Φ h := by
  have hfcont : Continuous f := (hf 0).continuous
  have hgcont : Continuous h := (hg 0).continuous
  have hfdiv : Continuous (fun x => FiniteTimeSingularity.div f x) :=
    (Auxiliary.contDiff_div f hf 0).continuous
  have hgdiv : Continuous (fun x => FiniteTimeSingularity.div h x) :=
    (Auxiliary.contDiff_div h hg 0).continuous
  have hfcdiv : HasCompactSupport (fun x => FiniteTimeSingularity.div f x) :=
    hasCompactSupport_div f hfc
  have hgcdiv : HasCompactSupport (fun x => FiniteTimeSingularity.div h x) :=
    hasCompactSupport_div h hgc
  have hI1 : Integrable (fun x => inner ℝ (Φ x) (f x)) :=
    (hΦ.inner hfcont).integrable_of_hasCompactSupport (hasCompactSupport_inner_right hfc)
  have hI2 : Integrable (fun x => inner ℝ (Φ x) (h x)) :=
    (hΦ.inner hgcont).integrable_of_hasCompactSupport (hasCompactSupport_inner_right hgc)
  have hJ1 : Integrable (fun x => q x * FiniteTimeSingularity.div f x) :=
    (hq.mul hfdiv).integrable_of_hasCompactSupport hfcdiv.mul_left
  have hJ2 : Integrable (fun x => q x * FiniteTimeSingularity.div h x) :=
    (hq.mul hgdiv).integrable_of_hasCompactSupport hgcdiv.mul_left
  have hdiv : ∀ x, FiniteTimeSingularity.div (f - h) x
      = FiniteTimeSingularity.div f x - FiniteTimeSingularity.div h x := fun x =>
    Green.div_sub_eq f h x
      ((hf 1).differentiable (by norm_num) x)
      ((hg 1).differentiable (by norm_num) x)
  rw [Dpair_apply, Dpair_apply, Dpair_apply]
  have e1 : (fun x => inner ℝ (Φ x) ((f - h) x))
      = fun x => inner ℝ (Φ x) (f x) - inner ℝ (Φ x) (h x) := by
    funext x
    rw [Pi.sub_apply, inner_sub_right]
  have e2 : (fun x => q x * FiniteTimeSingularity.div (f - h) x)
      = fun x => q x * FiniteTimeSingularity.div f x - q x * FiniteTimeSingularity.div h x := by
    funext x
    rw [hdiv x]
    ring
  rw [e1, e2, integral_sub hI1 hI2, integral_sub hJ1 hJ2]
  ring

/-! ## The main theorem -/

theorem exists_const_Dpair_aux (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hq0 : Filter.Tendsto q (Filter.cocompact (EuclideanSpace ℝ (Fin 3))) (nhds 0))
    (hΦ0 : Filter.Tendsto Φ (Filter.cocompact (EuclideanSpace ℝ (Fin 3))) (nhds 0))
    (hdiv : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) →
      HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x)
        = -∫ x, q x * Work.FTS.PressureOn.laplaceTrace φ x)
    (hcurl : ∀ ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0) :
    ∃ c : EuclideanSpace ℝ (Fin 3),
      ∀ ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
        Work.FTS.PressureOn.Dpair q Φ ψ = inner ℝ c (∫ x, ψ x) := by
  -- boundedness of `Φ` and `q`, from the decay at infinity
  obtain ⟨DΦ, hDΦ⟩ := Auxiliary.cocompact_bound_vec hΦ hΦ0
  obtain ⟨Dq, hDq⟩ := (Auxiliary.tendsto_cocompact_bound_scalar hq hq0).1
  -- ## Step 1: the mollified difference field `Vₙ = mollV n Φ - ∇(moll n q)` is constant
  have hVconst : ∀ n : ℕ, ∃ c : R3, ∀ x, mollV n Φ x - gradient (moll n q) x = c := by
    intro n
    refine eq_const_of_weak_harmonic_smooth _ ?_ ?_ ?_
    · intro m
      exact (MollSB.contDiff_mollV n Φ hΦ m).sub
        ((Auxiliary.gradient_smooth_norm (moll n q) (MollSB.contDiff_moll n q hq)).1 m)
    · refine ⟨DΦ + Dq * ∫ t : R3, ‖fderiv ℝ (rho n) t‖, fun x => ?_⟩
      have h1 : ‖mollV n Φ x‖ ≤ DΦ := MollSB.norm_mollV_le n Φ DΦ hDΦ x
      have h2 : ‖gradient (moll n q) x‖ ≤ Dq * ∫ t : R3, ‖fderiv ℝ (rho n) t‖ := by
        rw [(Auxiliary.gradient_smooth_norm (moll n q) (MollSB.contDiff_moll n q hq)).2 x]
        exact MollSB.norm_fderiv_moll_le n q hq Dq hDq x
      calc ‖mollV n Φ x - gradient (moll n q) x‖
          ≤ ‖mollV n Φ x‖ + ‖gradient (moll n q) x‖ := norm_sub_le _ _
        _ ≤ DΦ + Dq * ∫ t : R3, ‖fderiv ℝ (rho n) t‖ := add_le_add h1 h2
    · intro W hW hWc
      exact weak_harmonic_mollified_diff q Φ hq hΦ hdiv hcurl n W hW hWc
  choose c hc using hVconst
  -- ## Step 2: the pairing against a mollified test field only sees `∫ψ`
  have hstep2 : ∀ (n : ℕ) (ψ : R3 → R3), (∀ m : ℕ, ContDiff ℝ m ψ) → HasCompactSupport ψ →
      Dpair q Φ (mollV n ψ) = inner ℝ (c n) (∫ x, ψ x) := by
    intro n ψ hψ hψc
    have hrp := rho_props n
    have hA : Dpair q Φ (mollV n ψ) = Dpair (moll n q) (mollV n Φ) ψ := by
      show Dpair q Φ (MeasureTheory.convolution (rho n) ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          = Dpair (MeasureTheory.convolution (rho n) q (ContinuousLinearMap.lsmul ℝ ℝ) volume)
              (MeasureTheory.convolution (rho n) Φ (ContinuousLinearMap.lsmul ℝ ℝ) volume) ψ
      exact Dpair_convolution q Φ (rho n) ψ hrp.1 hrp.2.1 hrp.2.2.2.2.1 hψ hψc hq hΦ
    have hB : Dpair (moll n q) (mollV n Φ) ψ
        = ∫ x, inner ℝ (mollV n Φ x - gradient (moll n q) x) (ψ x) :=
      Dpair_eq_integral_sub_gradient_of_smooth (moll n q) (mollV n Φ)
        (MollSB.contDiff_moll n q hq) (MollSB.contDiff_mollV n Φ hΦ 0).continuous ψ hψ hψc
    have hC : (∫ x, inner ℝ (mollV n Φ x - gradient (moll n q) x) (ψ x))
        = ∫ x, inner ℝ (c n) (ψ x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change inner ℝ (mollV n Φ x - gradient (moll n q) x) (ψ x) = inner ℝ (c n) (ψ x)
      rw [hc n x]
    have hD : (∫ x, inner ℝ (c n) (ψ x)) = inner ℝ (c n) (∫ x, ψ x) :=
      Auxiliary.integral_inner_eq_inner_integral (c n) ψ (hψ 0).continuous hψc
    rw [hA, hB, hC, hD]
  -- ## Step 3: the pairing annihilates mean-zero test fields
  have hmean : ∀ ψ : R3 → R3, (∀ m : ℕ, ContDiff ℝ m ψ) → HasCompactSupport ψ →
      (∫ x, ψ x) = 0 → Dpair q Φ ψ = 0 := by
    intro ψ hψ hψc h0
    have hlim := moll_tendsto q Φ hq hΦ ψ hψ hψc
    have hconst : (fun n : ℕ => Dpair q Φ (mollV n ψ)) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      rw [hstep2 n ψ hψ hψc, h0, inner_zero_right]
    rw [hconst] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  -- ## Step 4: the value of the constant, and the general test field
  have hθsm : ∀ m : ℕ, ContDiff ℝ m (rho 0) := (rho_props 0).1
  have hθc : HasCompactSupport (rho 0) := (rho_props 0).2.1
  have hθint : ∫ x : R3, rho 0 x = 1 := (rho_props 0).2.2.1
  have hθcont : Continuous (rho 0) := (hθsm 0).continuous
  have hgradθcont : Continuous (fun x => gradient (rho 0) x) :=
    (Green.contDiff_gradient (rho 0) (hθsm 2)).continuous
  have hgradθc : HasCompactSupport (fun x => gradient (rho 0) x) :=
    HasCompactSupport.intro hθc (fun x hx => Green.gradient_eq_zero_of_notMem_tsupport hx)
  refine ⟨(∫ x : R3, rho 0 x • Φ x) + ∫ x : R3, q x • gradient (rho 0) x, fun ψ hψ hψc => ?_⟩
  set g : R3 := ∫ y : R3, ψ y with hg
  -- the divergence of `x ↦ rho 0 x • g`
  have hΘdiv : ∀ x : R3,
      FiniteTimeSingularity.div (fun y : R3 => rho 0 y • g) x = (fderiv ℝ (rho 0) x) g := by
    intro x
    have h0 : FiniteTimeSingularity.div (fun _ : R3 => g) x = 0 := by
      rw [FiniteTimeSingularity.div, fderiv_const_apply]
      simp
    rw [Green.div_smul_eq (rho 0) (fun _ : R3 => g) x
      ((hθsm 1).differentiable (by norm_num) x)
      (differentiableAt_const g), h0, mul_zero, zero_add]
  -- the mean-zero field `ψ - ρg`
  have hzero_int : (∫ x : R3, (ψ x - rho 0 x • g)) = 0 := by
    have h1 : Integrable ψ := (hψ 0).continuous.integrable_of_hasCompactSupport hψc
    have h2 : Integrable (fun x : R3 => rho 0 x • g) := (MollSB.integrable_rho 0).smul_const g
    rw [integral_sub h1 h2, integral_smul_const, hθint, one_smul, hg, sub_self]
  have hmz : Dpair q Φ (fun x : R3 => ψ x - rho 0 x • g) = 0 :=
    hmean _ (fun m => (hψ m).sub ((hθsm m).smul_const g)) (hψc.sub hθc.smul_right) hzero_int
  have hsplit : Dpair q Φ (fun x : R3 => ψ x - rho 0 x • g)
      = Dpair q Φ ψ - Dpair q Φ (fun x : R3 => rho 0 x • g) :=
    Dpair_sub q Φ hq hΦ ψ (fun x : R3 => rho 0 x • g) hψ hψc
      (fun m => (hθsm m).smul_const g) hθc.smul_right
  -- the two pairings that make up `Dpair q Φ (ρ • g)`
  have hI1 : (∫ x : R3, rho 0 x * inner ℝ (Φ x) g)
      = inner ℝ (∫ x : R3, rho 0 x • Φ x) g := by
    rw [show (fun x : R3 => rho 0 x * inner ℝ (Φ x) g)
        = fun x : R3 => inner ℝ (rho 0 x • Φ x) g from
      funext (fun x => by rw [real_inner_smul_left])]
    exact integral_inner_eq_inner_integral_right g (fun x : R3 => rho 0 x • Φ x)
      (hθcont.smul hΦ) hθc.smul_right
  have hI2 : (∫ x : R3, q x * (fderiv ℝ (rho 0) x) g)
      = inner ℝ (∫ x : R3, q x • gradient (rho 0) x) g := by
    rw [show (fun x : R3 => q x * (fderiv ℝ (rho 0) x) g)
        = fun x : R3 => inner ℝ (q x • gradient (rho 0) x) g from
      funext (fun x => by rw [real_inner_smul_left, inner_gradient_left])]
    exact integral_inner_eq_inner_integral_right g (fun x : R3 => q x • gradient (rho 0) x)
      (hq.smul hgradθcont)
      (HasCompactSupport.intro hgradθc
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]))
  have hmain : Dpair q Φ (fun x : R3 => rho 0 x • g)
      = inner ℝ ((∫ x : R3, rho 0 x • Φ x) + ∫ x : R3, q x • gradient (rho 0) x) g := by
    rw [Dpair_apply]
    have hp1 : (fun x : R3 => inner ℝ (Φ x) (rho 0 x • g))
        = fun x : R3 => rho 0 x * inner ℝ (Φ x) g := by
      funext x
      rw [real_inner_smul_right]
    have hp2 : (fun x : R3 => q x * FiniteTimeSingularity.div (fun y : R3 => rho 0 y • g) x)
        = fun x : R3 => q x * (fderiv ℝ (rho 0) x) g := by
      funext x
      rw [hΘdiv x]
    rw [hp1, hp2, hI1, hI2, inner_add_left]
  have : Dpair q Φ ψ
      = inner ℝ ((∫ x : R3, rho 0 x • Φ x) + ∫ x : R3, q x • gradient (rho 0) x) g := by
    linarith [hmz, hsplit, hmain]
  rwa [hg] at this

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.tendsto_lamb_decay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set MeasureTheory
open scoped Topology

namespace Work.FTS.PressureOn

/-! ## Two elementary one-variable / filter lemmas (reproduced, see the module docstring) -/

/-- **A two-sided derivative is bounded by a bound on one-sided difference quotients.**

If the slopes of `g` at `t` are bounded by `K` on `(t,S)`, then so is `deriv g t`: when `g` is
differentiable at `t` the two-sided derivative is the limit of the slopes along `𝓝[Ioi t] t`
(`hasDerivWithinAt_iff_tendsto_slope` + `le_of_tendsto`), and otherwise `deriv g t = 0`
(`deriv_zero_of_not_differentiableAt`). -/
theorem deriv_le_of_slope_le_aux {g : ℝ → R3} {t S K : ℝ} (htS : t < S) (hK : 0 ≤ K)
    (hslope : ∀ y ∈ Set.Ioo t S, ‖(y - t)⁻¹ • (g y - g t)‖ ≤ K) :
    ‖deriv g t‖ ≤ K := by
  have hmem : Set.Ioo t S ∈ 𝓝[Set.Ioi t] t := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio S, isOpen_Iio.mem_nhds htS, fun y hy => ⟨hy.2, hy.1⟩⟩
  by_cases hd : DifferentiableAt ℝ g t
  · have hc : HasDerivAt g (deriv g t) t := hd.hasDerivAt
    have hsl : HasDerivWithinAt g (deriv g t) (Set.Ici t) t := hc.hasDerivWithinAt
    have htend : Tendsto (slope g t) (𝓝[Set.Ioi t] t) (𝓝 (deriv g t)) := by
      have h := hasDerivWithinAt_iff_tendsto_slope.mp hsl
      have hset : Set.Ici t \ {t} = Set.Ioi t := by
        ext y
        simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
        constructor
        · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
        · intro h1; exact ⟨le_of_lt h1, ne_of_gt h1⟩
      rwa [hset] at h
    have h1 : Tendsto (fun y => ‖slope g t y‖) (𝓝[Set.Ioi t] t) (𝓝 ‖deriv g t‖) :=
      (continuous_norm.tendsto _).comp htend
    refine le_of_tendsto h1 ?_
    filter_upwards [hmem] with y hy
    have hsl' : slope g t y = (y - t)⁻¹ • (g y - g t) := rfl
    rw [hsl']
    exact hslope y hy
  · rw [deriv_zero_of_not_differentiableAt hd]
    simpa using hK

/-- **The cocompact squeeze input**: `(1 + ‖x‖²)⁻¹ → 0` along the cocompact filter of `ℝ³`. -/
theorem tendsto_inv_one_add_normSq_cocompact_aux :
    Tendsto (fun x : R3 => (1 + ‖x‖ ^ 2)⁻¹) (cocompact R3) (nhds 0) := by
  have h4 : Tendsto (fun x : R3 => 1 + ‖x‖ ^ 2) (cocompact R3) atTop :=
    tendsto_atTop_mono (fun x => by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1 / 2)])
      tendsto_norm_cocompact_atTop
  exact h4.inv_tendsto_atTop

/-! ## The main statement -/

theorem tendsto_lamb_decay {α : NNReal} {ω : R3 → ℝ → R3} {T S t : ℝ}
    (hS : S ∈ Set.Ioo 0 T) (ht : t ∈ Set.Ico 0 S)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s)
    (hsupp : ∃ R, ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => FiniteTimeSingularity.timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x s) (Set.Ici s) s) :
    Filter.Tendsto (fun x : R3 =>
      FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t
        - crossVec (Work.FTS.Physical.physVel ω x t) (ω x t))
      (Filter.cocompact R3) (nhds 0) := by
  have htS : t < S := ht.2
  have ht0 : 0 ≤ t := ht.1
  have htIcc : t ∈ Set.Icc (0 : ℝ) S := ⟨ht0, ht.2.le⟩
  -- time-continuity of the vorticity curves on `[0,S]`
  have hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc (0 : ℝ) S) :=
    continuousOn_time_omega_of_strips hS hstrips hcurl
  -- Lipschitz dependence of `ω` on time, uniformly in space
  obtain ⟨C, hC, hlip⟩ := lipschitzTimeOmegaIcc hS hsupp hcontDt hderiv hcontω
  -- uniform bound and a.e. strong measurability of the vorticity slices on `[0,S]`
  obtain ⟨⟨M, hM, hbdd_pos⟩, hmeas_pos⟩ := omegaSliceRegularPos hS hstrips hcurl
  obtain ⟨hbdd0, hmeas0⟩ :=
    aeStronglyMeasurableAndBoundAtZero hS.1 hM hbdd_pos hmeas_pos hcontω
  have hbdd : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ x, ‖ω x s‖ ≤ M := by
    intro s hs x
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hbdd0 x
    · exact hbdd_pos s ⟨h, hs.2⟩ x
  have hmeas : ∀ s ∈ Set.Icc (0 : ℝ) S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact hmeas0
    · exact hmeas_pos s ⟨h, hs.2⟩
  -- the support radius, normalised to be nonnegative
  obtain ⟨R₀, hR₀⟩ := hsupp
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hsuppR : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R := by
    intro s hs x hx
    rw [hRdef]
    exact le_trans (hR₀ s hs x hx) (le_max_left _ _)
  -- the decaying bound on the time-slopes of the velocity
  have hslope := normSlopePhysVelLe (ω := ω) (S := S) (t := t) (M := M) (C := C) (R := R)
    htIcc hM hC hR hsuppR hbdd hmeas hlip
  -- the decaying bound on `∂ₜu(·,t)`
  have hderivBound : ∀ x : R3,
      ‖FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t‖
        ≤ 3 * C * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := by
    intro x
    have hK : 0 ≤ 3 * C * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := by positivity
    have h := deriv_le_of_slope_le_aux (g := fun s => Work.FTS.Physical.physVel ω x s)
      (t := t) (S := S) (K := 3 * C * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2)) htS hK
      (fun y hy => hslope x y hy)
    simpa only [FiniteTimeSingularity.timeDeriv] using h
  -- `∂ₜu(·,t) → 0` at infinity
  have hA : Filter.Tendsto (fun x : R3 =>
      FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t)
      (Filter.cocompact R3) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun x => norm_nonneg _) (fun x => hderivBound x) ?_
    have h0 : Filter.Tendsto
        (fun x : R3 => 3 * C * R * (1 + 4 * R ^ 2) * (1 + ‖x‖ ^ 2)⁻¹)
        (Filter.cocompact R3) (nhds 0) := by
      simpa using Filter.Tendsto.const_mul (3 * C * R * (1 + 4 * R ^ 2))
        tendsto_inv_one_add_normSq_cocompact_aux
    simpa only [div_eq_mul_inv] using h0
  -- `u(·,t) × ω(·,t) → 0` at infinity: it vanishes off `B(0,R)`
  have hB : Filter.Tendsto (fun x : R3 =>
      crossVec (Work.FTS.Physical.physVel ω x t) (ω x t))
      (Filter.cocompact R3) (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨(Metric.closedBall (0 : R3) R)ᶜ,
      (isCompact_closedBall (0 : R3) R).compl_mem_cocompact, ?_⟩
    intro x hx
    have hx' : R < ‖x‖ := by
      have h := hx
      rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      exact not_le.mp h
    have hω0 : ω x t = 0 := by
      by_contra hne
      exact absurd (hsuppR t htIcc x hne) (not_le.mpr hx')
    simp [crossVec, hω0]
  simpa using hA.sub hB

end Work.FTS.PressureOn
end
