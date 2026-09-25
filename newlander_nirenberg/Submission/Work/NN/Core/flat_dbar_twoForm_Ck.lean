import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.NN.Core.flat_dbar_twoForm
import Submission.Work.NN.Core.bmPotential_holder
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc_Ck
import Submission.Work.CR.Flat.Holder.holderNorm_smul

namespace Work.NN.Core

open MeasureTheory Set
open scoped NNReal ENNReal
open Work.CR.Flat

noncomputable section

/-! ### Elementary facts about `∂̄` and support (public copies) -/

/-- `∂̄_j (a * g) = a * ∂̄_j g` for a constant `a : ℂ`, with the convention `fderiv = 0` at
non-differentiable points, so that no regularity hypothesis is needed. -/
private lemma ck_dbarCoord_const_mul {n : ℕ} (j : Fin n) (a : ℂ)
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

/-- The translate `x ↦ ∂̄_j g (z + x)` of a `∂̄`-derivative of a function vanishing off the ball
of radius `R` has compact support. -/
private lemma ck_hasCompactSupport_dbarCoord_comp_add {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (j : Fin n) (z : Fin n → ℂ) :
    HasCompactSupport (fun x => dbarCoord j g (z + x)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (-z) R) ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra hcon
  rw [not_le] at hcon
  refine hx (Work.CR.Flat.Cauchy.dbarCoord_eq_zero_of_lt_norm hsupp j ?_)
  have : x - (-z) = z + x := by abel
  rwa [this] at hcon

/-! ### The Bochner–Martinelli identity for a `(0,2)`-form -/

/-- **The `(0,2)` Bochner–Martinelli identity.**  Let `η = (η_{kl})` be a `∂̄`-closed family of
`C¹` functions vanishing off the ball of radius `R`, and let
`(Sη)_i := bmPot (η_{i·}) = Σ_l ∫ x, bmKernel l x · η_{il}(z+x)`.  Then

  `∂̄_j (Sη)_k - ∂̄_k (Sη)_j = -γ η_{jk}`,

where `γ = bmGamma n ≠ 0`.  The proof differentiates the potential under the integral
(`bmPot_dbarCoord`), uses closedness to combine the two sums into the divergence
`Σ_l ∫ bmKernel l x · ∂̄_l(η_{jk})(z+x)`, and evaluates that with the Bochner–Martinelli formula. -/
private lemma ck_bmPot_dbarCoord_sub {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
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
    Work.NN.Core.integrable_bmKernel_mul hn l
      ((Work.CR.Flat.Cauchy.continuous_dbarCoord (hη k l) j).comp
        (continuous_const.add continuous_id))
      (ck_hasCompactSupport_dbarCoord_comp_add (fun y hy => hsupp k l y hy) j z)
  have hI2 : ∀ l : Fin n, Integrable (fun x : Fin n → ℂ =>
      Work.CR.Flat.Cauchy.bmKernel l x * dbarCoord k (η j l) (z + x)) := fun l =>
    Work.NN.Core.integrable_bmKernel_mul hn l
      ((Work.CR.Flat.Cauchy.continuous_dbarCoord (hη j l) k).comp
        (continuous_const.add continuous_id))
      (ck_hasCompactSupport_dbarCoord_comp_add (fun y hy => hsupp j l y hy) k z)
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
      _ = ∑ l, ∫ x, Work.CR.Flat.Cauchy.bmKernel l x
            * (-(dbarCoord l (η j k) (z + x))) := by
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

/-- **The flat `∂̄`-Poincaré result on a polydisc in bidegree `(0,2)`, in the `C^{k,α}` scale with
a gain of one derivative.**  For `n ≥ 1`, `0 < α < 1` and every `k` there is `C > 0` such that
every `∂̄`-closed antisymmetric family `η : Fin n → Fin n → (ℂⁿ → ℂ)` with `C^{k+1}` components
supported in the open half-size polydisc admits a `(0,1)`-form `ψ` solving

  `∂̄_j ψ_k - ∂̄_k ψ_j = η_{jk}`   on `polydisc c (r/2)`,

with `‖ψ_k‖_{C^{k+1,α}} ≤ C Σ_{k,l} ‖η_{kl}‖_{C^{k,α}}`, the constant being uniform in `η`.  This
is the `C^{k,α}` version of `Work.NN.Core.flat_dbar_twoForm` (the `k = 0` case, whose proof uses
`bmPotential` of the rows together with the Bochner–Martinelli Schauder estimate), needed for the
`C^{k,α}` fixed point of the defect-correction construction of the perturbed `∂̄`-solver. -/
theorem flat_dbar_twoForm_Ck {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ j l, ContDiff ℝ (k + 1) (η j l)) →
      (∀ j l z, η j l z = - η l j z) →
      (∀ j l z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → η j l z = 0) →
      (∀ j l m z, dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0) →
      ∃ ψ : Fin n → (Fin n → ℂ) → ℂ,
        (∀ j l, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < r i / 2) →
          dbarCoord j (ψ l) z - dbarCoord l (ψ j) z = η j l z) ∧
        (∀ j, holderNorm (k + 1) α (ψ j) (polydisc c (fun i => r i / 2))
          ≤ ENNReal.ofReal C * ∑ l, ∑ m, holderNorm k α (η l m) Set.univ) := by
  -- the order-zero potential estimate on the full polydisc, obtained from the C^{1,α}
  -- Bochner–Martinelli Schauder estimate by doubling the radii
  have hbase : ∃ C : ℝ, 0 < C ∧ ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j z, (∃ i, r i ≤ ‖z i - c i‖) → g j z = 0) →
      holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential g) (polydisc c r)
        ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (g j) Set.univ := by
    obtain ⟨C₀, hC₀, hC₀'⟩ := bmPotential_holder hn (c := c) (r := fun j => 2 * r j)
      hα hα1 (fun j => by linarith [hr j])
    refine ⟨C₀, hC₀, fun g hg hgs => ?_⟩
    have h := hC₀' g hg (fun j z hz => hgs j z (by
      obtain ⟨i, hi⟩ := hz
      exact ⟨i, by rw [show 2 * r i / 2 = r i from by ring] at hi; exact hi⟩))
    rwa [show (fun j => 2 * r j / 2) = r from by funext j; ring] at h
  obtain ⟨C₁, hC₁, hiter⟩ := Work.CR.Flat.Cauchy.bmPotential_iter_bound hn hα hα1 hr k hbase
  obtain ⟨C₂, hC₂, htop⟩ := Work.CR.Flat.Cauchy.bmPotential_top_bound hn hα hα1 hr k hbase
  have hγ : Work.CR.Flat.Cauchy.bmGamma n ≠ 0 :=
    Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  set K : ℝ := 2 * ((k : ℝ) + 1) * C₁ + 2 * C₂ with hK
  refine ⟨‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * K + 1, by positivity, ?_⟩
  intro η hη hanti hsupp0 hclosed
  have hclosed' : ∀ j k l z, dbarCoord j (η k l) z - dbarCoord k (η j l) z
      + dbarCoord l (η j k) z = 0 := fun j k l z => hclosed j k l z
  have hη1 : ∀ i l, ContDiff ℝ 1 (η i l) := fun i l =>
    (hη i l).of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
  -- a ball containing the support of `η`
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
  refine ⟨fun i z => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
      * Work.CR.Flat.Cauchy.bmPotential (fun l => η i l) z, ?_, ?_⟩
  · -- the equation `∂̄_j ψ_l - ∂̄_l ψ_j = η_{jl}`
    intro j l z _hz
    have hψl : (fun w => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
          * Work.CR.Flat.Cauchy.bmPotential (fun m => η l m) w)
        = fun w => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
          * Work.CR.Flat.Cauchy.bmPot (fun m => η l m) w := by
      funext w; rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
    have hψj : (fun w => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
          * Work.CR.Flat.Cauchy.bmPotential (fun m => η j m) w)
        = fun w => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
          * Work.CR.Flat.Cauchy.bmPot (fun m => η j m) w := by
      funext w; rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
    have hkey := ck_bmPot_dbarCoord_sub hn hRpos hη1 hsuppR hclosed' j l z
    calc dbarCoord j (fun w => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
            * Work.CR.Flat.Cauchy.bmPotential (fun m => η l m) w) z
          - dbarCoord l (fun w => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
            * Work.CR.Flat.Cauchy.bmPotential (fun m => η j m) w) z
        = (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
            * dbarCoord j (Work.CR.Flat.Cauchy.bmPot (fun m => η l m)) z
          - ((-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
            * dbarCoord l (Work.CR.Flat.Cauchy.bmPot (fun m => η j m)) z) := by
          rw [hψl, hψj, ck_dbarCoord_const_mul, ck_dbarCoord_const_mul]
        _ = (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
            * (dbarCoord j (Work.CR.Flat.Cauchy.bmPot (fun m => η l m)) z
              - dbarCoord l (Work.CR.Flat.Cauchy.bmPot (fun m => η j m)) z) := by ring
        _ = (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
            * (-(Work.CR.Flat.Cauchy.bmGamma n) * η j l z) := by rw [hkey]
        _ = η j l z := by
          rw [show (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
                * (-(Work.CR.Flat.Cauchy.bmGamma n) * η j l z)
              = ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmGamma n) * η j l z
              from by ring,
            inv_mul_cancel₀ hγ, one_mul]
  · -- the `C^{k+1,α}` estimate
    intro j
    beta_reduce
    set S : ℝ≥0∞ := ∑ l, holderNorm k α (η j l) Set.univ with hS
    have hsuppj : ∀ l z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → η j l z = 0 :=
      fun l z hz => hsupp0 j l z hz
    have hcs : ∀ l, HasCompactSupport (η j l) := fun l =>
      Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc hr (fun z hz => hsupp0 j l z hz)
    have hiterb : ∀ m, m ≤ k →
        (iterDerivNorm m (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
            (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal C₁ * S) ∧
        (holderSeminorm m α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
            (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal C₁ * S) := fun m hm =>
      hiter (fun l => η j l) (fun l => hη j l) hsuppj m hm
    have hlower : holderNorm k α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
        (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S := by
      rw [holderNorm]
      calc ∑ m ∈ Finset.range (k + 1),
              (iterDerivNorm m (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
                (polydisc c (fun i => r i / 2))
                + holderSeminorm m α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
                  (polydisc c (fun i => r i / 2)))
          ≤ ∑ _m ∈ Finset.range (k + 1), (ENNReal.ofReal (2 * C₁) * S) := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            refine (add_le_add (hiterb m hmk).1 (hiterb m hmk).2).trans ?_
            rw [← add_mul, ← ENNReal.ofReal_add (le_of_lt hC₁) (le_of_lt hC₁),
              show C₁ + C₁ = 2 * C₁ from by ring]
        _ = ((k + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (2 * C₁) * S) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S := by
            rw [← ENNReal.ofReal_natCast (k + 1), ← mul_assoc,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            push_cast
            ring
    have htop' : iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
          (polydisc c (fun i => r i / 2))
        + holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
          (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal (2 * C₂) * S := by
      have hh := htop (fun l => η j l) (fun l => hη j l) hsuppj
      refine (add_le_add hh.1 hh.2).trans ?_
      rw [← add_mul, ← ENNReal.ofReal_add (le_of_lt hC₂) (le_of_lt hC₂),
        show C₂ + C₂ = 2 * C₂ from by ring]
    have hbound : holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
        (polydisc c (fun i => r i / 2)) ≤ ENNReal.ofReal K * S := by
      rw [Work.CR.Flat.Cauchy.holderNorm_succ k α
        (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l)) (polydisc c (fun i => r i / 2)), hK]
      calc holderNorm k α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
              (polydisc c (fun i => r i / 2))
            + (iterDerivNorm (k + 1) (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
                (polydisc c (fun i => r i / 2))
              + holderSeminorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
                (polydisc c (fun i => r i / 2)))
          ≤ ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁) * S + ENNReal.ofReal (2 * C₂) * S :=
            add_le_add hlower htop'
        _ = ENNReal.ofReal (2 * ((k : ℝ) + 1) * C₁ + 2 * C₂) * S := by
            rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hcd : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞)
        (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
        (polydisc c (fun i => r i / 2)) :=
      (Work.CR.Flat.Cauchy.contDiff_bmPotential_Ck hn k (fun l => hη j l) hcs).contDiffOn
    rw [show (fun z => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
            * Work.CR.Flat.Cauchy.bmPotential (fun l => η j l) z)
          = (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
            • (fun z => Work.CR.Flat.Cauchy.bmPotential (fun l => η j l) z) from rfl,
      Work.CR.Flat.Holder.holderNorm_smul (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) hcd
        ((isOpen_polydisc c (fun i => r i / 2)).uniqueDiffOn), norm_neg]
    have hST : S ≤ ∑ l, ∑ m, holderNorm k α (η l m) Set.univ := by
      rw [hS]
      exact Finset.single_le_sum (f := fun l => ∑ m, holderNorm k α (η l m) Set.univ)
        (fun l _ => bot_le) (Finset.mem_univ j)
    calc ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential (fun l => η j l))
            (polydisc c (fun i => r i / 2))
        ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (ENNReal.ofReal K * S) :=
          mul_le_mul_right hbound _
      _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * K) * S := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * K + 1) * S :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)) _
      _ ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * K + 1)
            * ∑ l, ∑ m, holderNorm k α (η l m) Set.univ :=
          mul_le_mul_right hST _

end

end Work.NN.Core
