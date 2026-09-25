import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps
import Submission.Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral
import Submission.Work.CR.Flat.Cauchy.integrable_bmWeight
import Submission.Work.CR.Flat.Cauchy.bmPotential_solves_dbar
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.NN.Core.bmPotential_holder

namespace Work.NN.Core

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open Work.CR.Flat

noncomputable section

/-! ### Elementary facts about `∂̄` and support -/

/-- `∂̄_j (a * g) = a * ∂̄_j g` for a constant `a : ℂ`, with the convention `fderiv = 0` at
non-differentiable points, so that no regularity hypothesis is needed. -/
private lemma twoForm_dbarCoord_const_mul {n : ℕ} (j : Fin n) (a : ℂ)
    (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    dbarCoord j (fun w => a * g w) z = a * dbarCoord j g z := by
  by_cases hg : DifferentiableAt ℝ g z
  · have h2 : fderiv ℝ (fun w => a * g w) z = a • fderiv ℝ g z := fderiv_const_mul hg a
    rw [dbarCoord, h2, dbarCoord]
    simp only [smul_apply, smul_eq_mul]
    ring
  · rcases eq_or_ne a 0 with ha | ha
    · subst ha
      have hzero : (fun w => (0 : ℂ) * g w) = Function.const (Fin n → ℂ) (0 : ℂ) := by
        funext w; rw [zero_mul]; rfl
      rw [hzero, dbarCoord, dbarCoord, fderiv_const, fderiv_zero_of_not_differentiableAt hg]
      simp
    · have h2 : ¬ DifferentiableAt ℝ (fun w => a * g w) z := by
        intro h
        refine hg ?_
        have h3 : DifferentiableAt ℝ (fun w => a⁻¹ * (a * g w)) z := h.const_mul a⁻¹
        convert h3 using 1
        ext w
        rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      rw [dbarCoord, dbarCoord, fderiv_zero_of_not_differentiableAt h2,
        fderiv_zero_of_not_differentiableAt hg]
      simp

/-- A function vanishing on `{x | R ≤ ‖x‖}` has vanishing `∂̄`-derivative at every `x` with
`R < ‖x‖`. -/
private lemma twoForm_dbarCoord_eq_zero_of_lt {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (j : Fin n) {y : Fin n → ℂ}
    (hy : R < ‖y‖) : dbarCoord j g y = 0 := by
  have hopen : IsOpen {x : Fin n → ℂ | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hg0 : g =ᶠ[𝓝 y] (fun _ : Fin n → ℂ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hy] with x hx
    exact hsupp x hx.le
  have hfd : fderiv ℝ g y = 0 :=
    ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) y).congr_of_eventuallyEq hg0).fderiv
  simp [dbarCoord, hfd]

/-- A function vanishing on `{x | R ≤ ‖x‖}` has compactly supported `∂̄`-derivative. -/
private lemma twoForm_hasCompactSupport_dbarCoord {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (j : Fin n) :
    HasCompactSupport (fun y => dbarCoord j g y) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℂ) R) ?_
  intro y hy
  rw [Function.mem_support] at hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  exact hy (twoForm_dbarCoord_eq_zero_of_lt hsupp j hcon)

/-- The translate `x ↦ ∂̄_j g (z + x)` of a `∂̄`-derivative of a function vanishing off the ball
of radius `R` has compact support. -/
private lemma twoForm_hasCompactSupport_dbarCoord_comp_add {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    {R : ℝ} (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (j : Fin n) (z : Fin n → ℂ) :
    HasCompactSupport (fun x => dbarCoord j g (z + x)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (-z) R) ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra hcon
  rw [not_le] at hcon
  refine hx (twoForm_dbarCoord_eq_zero_of_lt hsupp j ?_)
  have : x - (-z) = z + x := by abel
  rwa [this] at hcon

/-- The Bochner–Martinelli kernel is locally integrable, so that a continuous compactly
supported function times it is integrable. -/
private lemma twoForm_integrable_bmKernel_mul {n : ℕ} (hn : 0 < n) (j : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun x => Work.CR.Flat.Cauchy.bmKernel j x * g x) := by
  have h := (Work.CR.Flat.Cauchy.locallyIntegrable_bmKernel hn j)
    |>.integrable_smul_left_of_hasCompactSupport hg hgs
  simpa only [smul_eq_mul, mul_comm] using h

/-- `y ↦ ∂̄_j g y` is continuous for `g` of class `C¹`. -/
private lemma twoForm_continuous_dbarCoord {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ 1 g) (j : Fin n) : Continuous (fun y => dbarCoord j g y) := by
  have hfd : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have h1 : Continuous (fun y : Fin n → ℂ => fderiv ℝ g y (Pi.single j (1 : ℂ))) :=
    hfd.clm_apply continuous_const
  have h2 : Continuous (fun y : Fin n → ℂ => fderiv ℝ g y (Pi.single j Complex.I)) :=
    hfd.clm_apply continuous_const
  have hfun : (fun y => dbarCoord j g y)
      = fun y => (1 / 2 : ℂ) * (fderiv ℝ g y (Pi.single j (1 : ℂ))
          + Complex.I * fderiv ℝ g y (Pi.single j Complex.I)) := by
    funext y; rw [dbarCoord]
  rw [hfun]
  exact continuous_const.mul (h1.add (continuous_const.mul h2))

/-! ### The Bochner–Martinelli identity for a `(0,2)`-form -/

/-- **The `(0,2)` Bochner–Martinelli identity.**  Let `η = (η_{kl})` be a `∂̄`-closed family of
`C¹` functions vanishing off the ball of radius `R`, and let
`(Sη)_i := bmPot (η_{i·}) = Σ_l ∫ x, bmKernel l x · η_{il}(z+x)`.  Then

  `∂̄_j (Sη)_k - ∂̄_k (Sη)_j = -γ η_{jk}`,

where `γ = bmGamma n ≠ 0`.  The proof differentiates the potential under the integral
(`bmPot_dbarCoord`), uses closedness to combine the two sums into the divergence
`Σ_l ∫ bmKernel l x · ∂̄_l(η_{jk})(z+x)`, and evaluates that with the Bochner–Martinelli formula. -/
private lemma bmPot_dbarCoord_sub {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hsupp : ∀ i l y, R ≤ ‖y‖ → η i l y = 0)
    (hclosed : ∀ j k l z, dbarCoord j (η k l) z - dbarCoord k (η j l) z
      + dbarCoord l (η j k) z = 0)
    (j k : Fin n) (z : Fin n → ℂ) :
    dbarCoord j (Work.CR.Flat.Cauchy.bmPot (fun l => η k l)) z
      - dbarCoord k (Work.CR.Flat.Cauchy.bmPot (fun l => η j l)) z
      = -(Work.CR.Flat.Cauchy.bmGamma n) * η j k z := by
  have hI1 : ∀ l : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord j (η k l) (z + x)) := fun l =>
    twoForm_integrable_bmKernel_mul hn l
      ((twoForm_continuous_dbarCoord (hη k l) j).comp (continuous_const.add continuous_id))
      (twoForm_hasCompactSupport_dbarCoord_comp_add (fun y hy => hsupp k l y hy) j z)
  have hI2 : ∀ l : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord k (η j l) (z + x)) := fun l =>
    twoForm_integrable_bmKernel_mul hn l
      ((twoForm_continuous_dbarCoord (hη j l) k).comp (continuous_const.add continuous_id))
      (twoForm_hasCompactSupport_dbarCoord_comp_add (fun y hy => hsupp j l y hy) k z)
  have hdiv : (∑ l, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord l (η j k) (z + x))
      = Work.CR.Flat.Cauchy.bmGamma n * η j k z := by
    have hR' : 0 < R + ‖z‖ := by positivity
    have hg : ContDiff ℝ 1 (fun x : Fin n → ℂ => η j k (z + x)) :=
      (hη j k).comp (contDiff_const.add contDiff_id)
    have hsupp' : ∀ x : Fin n → ℂ, R + ‖z‖ ≤ ‖x‖ → η j k (z + x) = 0 := by
      intro x hx
      refine hsupp j k (z + x) ?_
      have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
        calc ‖x‖ = ‖(z + x) - z‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖z + x‖ + ‖z‖ := norm_sub_le _ _
      linarith
    have hkey := Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps hn hR' hg hsupp'
      (Work.CR.Flat.Cauchy.integrable_bmWeight hn).1
      (fun ε hε => Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral hn hR' hg hsupp' hε)
    rw [show η j k (z + 0) = η j k z from by rw [add_zero]] at hkey
    rw [← hkey]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord l (η j k) (z + x)
      = Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord l (fun y => η j k (z + y)) x
    rw [Work.CR.Flat.Cauchy.dbarCoord_comp_add l
      (((hη j k).differentiable one_ne_zero).differentiableAt)]
  rw [Work.CR.Flat.Cauchy.bmPot_dbarCoord hn (fun l => hη k l) hR
        (fun l y hy => hsupp k l y hy) j z,
      Work.CR.Flat.Cauchy.bmPot_dbarCoord hn (fun l => hη j l) hR
        (fun l y hy => hsupp j l y hy) k z]
  calc (∑ l, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord j (η k l) (z + x))
        - (∑ l, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord k (η j l) (z + x))
      = ∑ l, ((∫ x, Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord j (η k l) (z + x))
            - (∫ x, Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord k (η j l) (z + x))) := by
          rw [← Finset.sum_sub_distrib]
      _ = ∑ l, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x
            * (dbarCoord j (η k l) (z + x) - dbarCoord k (η j l) (z + x)) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← integral_sub (hI1 l) (hI2 l)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
      _ = ∑ l, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x * (-(dbarCoord l (η j k) (z + x))) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show Work.CR.Flat.Cauchy.bmKernel l x
              * (dbarCoord j (η k l) (z + x) - dbarCoord k (η j l) (z + x))
            = Work.CR.Flat.Cauchy.bmKernel l x * (-(dbarCoord l (η j k) (z + x)))
          have hc := hclosed j k l (z + x)
          have hthis : dbarCoord j (η k l) (z + x) - dbarCoord k (η j l) (z + x)
              = -(dbarCoord l (η j k) (z + x)) := by linear_combination hc
          rw [hthis]
      _ = -(∑ l, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord l (η j k) (z + x)) := by
          have hterm : ∀ l : Fin n, (∫ x, Work.CR.Flat.Cauchy.bmKernel l x
              * (-(dbarCoord l (η j k) (z + x))))
              = -(∫ x, Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord l (η j k) (z + x)) := by
            intro l
            rw [← integral_neg]
            exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
          rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_neg_distrib]
      _ = -(Work.CR.Flat.Cauchy.bmGamma n) * η j k z := by rw [hdiv]; ring

/-- **The flat `∂̄`-Poincaré result on a polydisc in bidegree `(0,2)`, with a gain of one
derivative.**  Let `n ≥ 1`, `0 < α < 1`, and let `η = Σ_{k<l} η_{kl} dz̄_k ∧ dz̄_l` be an
antisymmetric family of `C¹` functions on `ℂⁿ = Fin n → ℂ` which is `∂̄`-closed,

  `∂̄_j η_{kl} - ∂̄_k η_{jl} + ∂̄_l η_{jk} = 0`   for all `j, k, l`,

and supported in the open half-size polydisc `polydisc c (r/2)`.  Then there is a `(0,1)`-form
`ψ = Σ_k ψ_k dz̄_k` whose components solve

  `∂̄_j ψ_k - ∂̄_k ψ_j = η_{jk}`   on `polydisc c (r/2)`   for all `j, k`,

with `‖ψ_k‖_{C^{1,α}(polydisc c (r/2))} ≤ C Σ_{k,l} ‖η_{kl}‖_{C^{0,α}(ℂⁿ)}`, the constant `C`
depending only on `n, c, r, α`.  This is the missing input for the defect-correction construction
of the perturbed `∂̄`-solver of an integrable almost complex structure close to the standard one:
the datum `g - L_A v` of the naive iteration is not `∂̄₀`-closed away from the fixed point, and
`ψ` is what makes it closed. -/
theorem flat_dbar_twoForm {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ j k, ContDiff ℝ 1 (η j k)) →
      (∀ j k z, η j k z = - η k j z) →
      (∀ j k z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → η j k z = 0) →
      (∀ j k l z, dbarCoord j (η k l) z - dbarCoord k (η j l) z + dbarCoord l (η j k) z = 0) →
      ∃ ψ : Fin n → (Fin n → ℂ) → ℂ,
        (∀ j k, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < r i / 2) →
          dbarCoord j (ψ k) z - dbarCoord k (ψ j) z = η j k z) ∧
        (∀ j, holderNorm 1 α (ψ j) (polydisc c (fun i => r i / 2))
          ≤ ENNReal.ofReal C * ∑ k, ∑ l, holderNorm 0 α (η k l) Set.univ) := by
  obtain ⟨C₀, hC₀, hest⟩ := Work.NN.Core.bmPotential_holder hn hα hα1 hr
  have hγ : Work.CR.Flat.Cauchy.bmGamma n ≠ 0 :=
    Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  refine ⟨C₀ * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖,
    mul_pos hC₀ (norm_pos_iff.mpr (inv_ne_zero hγ)), ?_⟩
  intro η hη hanti hsupp0 hclosed
  -- the radius of a ball containing the support of `η`
  set R : ℝ := (∑ i, r i / 2) + ‖c‖ + 1 with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    have h1 : 0 ≤ ∑ i, r i / 2 := Finset.sum_nonneg fun i _ => by have := hr i; linarith
    have h2 : 0 ≤ ‖c‖ := norm_nonneg c
    linarith
  have hsuppR : ∀ (i l : Fin n) (y : Fin n → ℂ), R ≤ ‖y‖ → η i l y = 0 := by
    intro i l y hy
    refine hsupp0 i l y ?_
    by_contra hcon
    push_neg at hcon
    have h1 : ‖y - c‖ ≤ ∑ m, ‖y m - c m‖ := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun m _ => norm_nonneg _)]
      exact fun m => Finset.single_le_sum (fun m _ => norm_nonneg _) (Finset.mem_univ m)
    have h2 : ∑ m, ‖y m - c m‖ < ∑ i, r i / 2 :=
      Finset.sum_lt_sum (fun m _ => le_of_lt (hcon m))
        ⟨⟨0, hn⟩, Finset.mem_univ _, hcon ⟨0, hn⟩⟩
    have h3 : ‖y‖ ≤ ‖y - c‖ + ‖c‖ := by
      calc ‖y‖ = ‖(y - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - c‖ + ‖c‖ := norm_add_le _ _
    rw [hRdef] at hy
    linarith
  refine ⟨fun i z => -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPotential (fun l => η i l) z, ?_, ?_⟩
  · -- the equation `∂̄_j ψ_k - ∂̄_k ψ_j = η_{jk}`
    intro j k z hz
    have hψk : (fun w => -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPotential (fun l => η k l) w)
        = fun w => -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPot (fun l => η k l) w := by
      funext w
      rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
    have hψj : (fun w => -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPotential (fun l => η j l) w)
        = fun w => -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPot (fun l => η j l) w := by
      funext w
      rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
    have hkey := bmPot_dbarCoord_sub hn hRpos (fun i l => hη i l) hsuppR hclosed j k z
    calc dbarCoord j (fun w => -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPotential (fun l => η k l) w) z
          - dbarCoord k (fun w => -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPotential (fun l => η j l) w) z
        = -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * dbarCoord j (Work.CR.Flat.Cauchy.bmPot (fun l => η k l)) z
            - (-(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * dbarCoord k (Work.CR.Flat.Cauchy.bmPot (fun l => η j l)) z) := by
          rw [hψk, hψj, twoForm_dbarCoord_const_mul, twoForm_dbarCoord_const_mul]
        _ = -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * (dbarCoord j (Work.CR.Flat.Cauchy.bmPot (fun l => η k l)) z
              - dbarCoord k (Work.CR.Flat.Cauchy.bmPot (fun l => η j l)) z) := by ring
        _ = -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * (-(Work.CR.Flat.Cauchy.bmGamma n) * η j k z) := by rw [hkey]
        _ = η j k z := by
          rw [show -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * (-(Work.CR.Flat.Cauchy.bmGamma n) * η j k z)
                = ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmGamma n) * η j k z from by ring,
            inv_mul_cancel₀ hγ, one_mul]
  · -- the estimate
    intro j
    have hsuppj : ∀ l z, (∃ k, r k / 2 ≤ ‖z k - c k‖) → η j l z = 0 :=
      fun l z hz => hsupp0 j l z hz
    have hcont : ContDiffOn ℝ (1 : ℕ∞)
        (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l)) (polydisc c (fun i => r i / 2)) :=
      (Work.CR.Flat.Cauchy.bmPotential_contDiff_one hn hr (fun l => hη j l) hsuppj).contDiffOn
    have hU : UniqueDiffOn ℝ (polydisc c (fun i => r i / 2)) :=
      (isOpen_polydisc c (fun i => r i / 2)).uniqueDiffOn
    have hsm : (fun z => -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPotential (fun l => η j l) z)
        = (-(Work.CR.Flat.Cauchy.bmGamma n)⁻¹) • (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l)) := by
      funext z; simp [smul_eq_mul]
    calc holderNorm 1 α (fun z => -(Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmPotential (fun l => η j l) z)
            (polydisc c (fun i => r i / 2))
        = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * holderNorm 1 α
            (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
            (polydisc c (fun i => r i / 2)) := by
          rw [hsm, Work.CR.Flat.Holder.holderNorm_smul (k := 1) (α := α) (-(Work.CR.Flat.Cauchy.bmGamma n)⁻¹) hcont hU,
            norm_neg]
      _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
            (ENNReal.ofReal C₀ * ∑ l, holderNorm 0 α (η j l) Set.univ) :=
          mul_le_mul_right (hest (fun l => η j l) (fun l => hη j l) hsuppj) _
      _ = ENNReal.ofReal (C₀ * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖) * ∑ l, holderNorm 0 α (η j l) Set.univ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg (Work.CR.Flat.Cauchy.bmGamma n)⁻¹), mul_comm ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ C₀]
      _ ≤ ENNReal.ofReal (C₀ * ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖) *
            ∑ k, ∑ l, holderNorm 0 α (η k l) Set.univ := by
          refine mul_le_mul_right ?_ _
          exact Finset.single_le_sum
            (f := fun k => ∑ l, holderNorm 0 α (η k l) Set.univ)
            (fun k _ => bot_le) (Finset.mem_univ j)

end

end Work.NN.Core
