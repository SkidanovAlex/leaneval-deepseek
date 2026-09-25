import Mathlib
import Submission.Work.NN.Core.dCoord_bmPotential_finite_holder
import Submission.Work.NN.Core.beltrami_theta_est
import Submission.Work.NN.Core.beltrami_theta_setup

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Core

/-! ## Auxiliary bounds for the `C^{0,α}`-norm of sums of products -/

section Aux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `C^{0,α}`-norm is the sum of the sup-norm and the `α`-Hölder seminorm. -/
lemma holderNorm_zero_decomp (f : X → ℂ) (α : ℝ) (Ω : Set X) :
    Work.CR.Flat.holderNorm 0 α f Ω
      = Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.holderSeminorm 0 α f Ω := by
  simp [Work.CR.Flat.holderNorm]

/-- The order-`0` iterated derivative is an isometry of the underlying function for the
difference norm: `‖D⁰f(x) - D⁰f(y)‖ = ‖f(x) - f(y)‖`. -/
lemma norm_iteratedFDerivWithin_zero_subC (f : X → ℂ) (Ω : Set X) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖ = ‖f x - f y‖ := by
  rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]

lemma iterDerivNorm_zero_mono_set (f : X → ℂ) {Ω Ω' : Set X} (h : Ω ⊆ Ω') :
    Work.CR.Flat.iterDerivNorm 0 f Ω ≤ Work.CR.Flat.iterDerivNorm 0 f Ω' := by
  simp only [Work.CR.Flat.iterDerivNorm, norm_iteratedFDerivWithin_zero]
  exact iSup₂_le fun x hx => le_iSup₂_of_le x (h hx) le_rfl

lemma holderSeminorm_zero_mono_set (f : X → ℂ) (α : ℝ) {Ω Ω' : Set X} (h : Ω ⊆ Ω') :
    Work.CR.Flat.holderSeminorm 0 α f Ω ≤ Work.CR.Flat.holderSeminorm 0 α f Ω' := by
  simp only [Work.CR.Flat.holderSeminorm, norm_iteratedFDerivWithin_zero_subC]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  exact le_iSup₂_of_le x (h hx) (le_iSup₂_of_le y (h hy) (le_iSup_of_le hxy le_rfl))

/-- The sup-norm part of the `C^{0,α}`-norm on an arbitrary subset `Ω` is bounded by the
full `C^{0,α}`-norm on all of `X`. -/
lemma iterDerivNorm_zero_le_holderNorm_univ (f : X → ℂ) (α : ℝ) (Ω : Set X) :
    Work.CR.Flat.iterDerivNorm 0 f Ω ≤ Work.CR.Flat.holderNorm 0 α f Set.univ :=
  (iterDerivNorm_zero_mono_set f (subset_univ Ω)).trans
    (Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α f Set.univ le_rfl)

/-- The Hölder part of the `C^{0,α}`-norm on an arbitrary subset `Ω` is bounded by the
full `C^{0,α}`-norm on all of `X`. -/
lemma holderSeminorm_zero_le_holderNorm_univ (f : X → ℂ) (α : ℝ) (Ω : Set X) :
    Work.CR.Flat.holderSeminorm 0 α f Ω ≤ Work.CR.Flat.holderNorm 0 α f Set.univ :=
  (holderSeminorm_zero_mono_set f α (subset_univ Ω)).trans
    (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α f Set.univ le_rfl)

/-- Sup-norm part of the Leibniz bound for a product. -/
lemma iterDerivNorm_zero_mul_leF (f g : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.iterDerivNorm 0 (fun x => f x * g x) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.iterDerivNorm 0 g Ω := by
  simp only [Work.CR.Flat.iterDerivNorm, norm_iteratedFDerivWithin_zero]
  refine iSup₂_le fun x hx => ?_
  rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  exact mul_le_mul' (le_iSup₂_of_le x hx le_rfl) (le_iSup₂_of_le x hx le_rfl)

/-- Hölder part of the Leibniz bound for a product. -/
lemma holderSeminorm_zero_mul_leF (α : ℝ) (f g : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.holderSeminorm 0 α (fun x => f x * g x) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω * Work.CR.Flat.holderSeminorm 0 α g Ω
        + Work.CR.Flat.holderSeminorm 0 α f Ω * Work.CR.Flat.iterDerivNorm 0 g Ω := by
  simp only [Work.CR.Flat.holderSeminorm, Work.CR.Flat.iterDerivNorm,
    norm_iteratedFDerivWithin_zero, norm_iteratedFDerivWithin_zero_subC]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hp : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  have hkey : ‖f x * g x - f y * g y‖
      ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
    have he : f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y := by ring
    rw [he]
    exact norm_add_le_of_le (by rw [norm_mul]) (by rw [norm_mul])
  calc ENNReal.ofReal (‖f x * g x - f y * g y‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal ((‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖) / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hkey hp.le)
    _ = ENNReal.ofReal (‖f x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)
          + (‖f x - f y‖ / ‖x - y‖ ^ α) * ‖g y‖) := by
        congr 1
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring
    _ = ENNReal.ofReal (‖f x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α))
        + ENNReal.ofReal ((‖f x - f y‖ / ‖x - y‖ ^ α) * ‖g y‖) :=
        ENNReal.ofReal_add (mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) hp.le))
          (mul_nonneg (div_nonneg (norm_nonneg _) hp.le) (norm_nonneg _))
    _ = ENNReal.ofReal ‖f x‖ * ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α)
        + ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) * ENNReal.ofReal ‖g y‖ := by
        rw [ENNReal.ofReal_mul (norm_nonneg _),
          ENNReal.ofReal_mul (div_nonneg (norm_nonneg _) hp.le)]
    _ ≤ (⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖)
          * (⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α))
        + (⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α))
          * (⨆ x ∈ Ω, ENNReal.ofReal ‖g x‖) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul' (le_iSup₂_of_le x hx le_rfl)
            (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))
        · exact mul_le_mul' (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))
            (le_iSup₂_of_le y hy le_rfl)

/-- **The `C^{0,α}`-norm of a constant multiple.** -/
lemma holderNorm_zero_const_mul_le (A : ℂ) {α : ℝ} (f : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.holderNorm 0 α (fun z => A * f z) Ω
      ≤ ENNReal.ofReal ‖A‖ * Work.CR.Flat.holderNorm 0 α f Ω := by
  rw [holderNorm_zero_decomp (fun z => A * f z) α Ω, holderNorm_zero_decomp f α Ω, mul_add]
  refine add_le_add ?_ ?_
  · simp only [Work.CR.Flat.iterDerivNorm, norm_iteratedFDerivWithin_zero]
    refine iSup₂_le fun x hx => ?_
    rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_le_mul' le_rfl (le_iSup₂_of_le x hx le_rfl)
  · simp only [Work.CR.Flat.holderSeminorm, norm_iteratedFDerivWithin_zero_subC]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hsub : A * f x - A * f y = A * (f x - f y) := by ring
    have hf : (fun z => A * f z) x - (fun z => A * f z) y = A * (f x - f y) := by simp only [hsub]
    rw [hf, norm_mul]
    rw [show ‖A‖ * ‖f x - f y‖ / ‖x - y‖ ^ α
        = ‖A‖ * (‖f x - f y‖ / ‖x - y‖ ^ α) by ring]
    rw [ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_le_mul' le_rfl
      (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))

/-- Sup-norm part of the subadditivity of the `C^{0,α}`-norm over a finite sum. -/
lemma iterDerivNorm_zero_sum_le {ι : Type*} (s : Finset ι) (g : ι → X → ℂ) (Ω : Set X) :
    Work.CR.Flat.iterDerivNorm 0 (fun x => ∑ j ∈ s, g j x) Ω
      ≤ ∑ j ∈ s, Work.CR.Flat.iterDerivNorm 0 (g j) Ω := by
  simp only [Work.CR.Flat.iterDerivNorm, norm_iteratedFDerivWithin_zero]
  refine iSup₂_le fun x hx => ?_
  calc ENNReal.ofReal ‖∑ j ∈ s, g j x‖
      ≤ ENNReal.ofReal (∑ j ∈ s, ‖g j x‖) := ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
    _ = ∑ j ∈ s, ENNReal.ofReal ‖g j x‖ := ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _)
    _ ≤ ∑ j ∈ s, ⨆ x ∈ Ω, ENNReal.ofReal ‖g j x‖ :=
        Finset.sum_le_sum fun j _ => le_iSup₂_of_le x hx le_rfl

/-- Hölder part of the subadditivity of the `C^{0,α}`-norm over a finite sum. -/
lemma holderSeminorm_zero_sum_le {ι : Type*} (s : Finset ι) (α : ℝ) (g : ι → X → ℂ)
    (Ω : Set X) :
    Work.CR.Flat.holderSeminorm 0 α (fun x => ∑ j ∈ s, g j x) Ω
      ≤ ∑ j ∈ s, Work.CR.Flat.holderSeminorm 0 α (g j) Ω := by
  simp only [Work.CR.Flat.holderSeminorm, norm_iteratedFDerivWithin_zero_subC]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hp : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hsplit : (∑ j ∈ s, g j x) - (∑ j ∈ s, g j y) = ∑ j ∈ s, (g j x - g j y) :=
    (Finset.sum_sub_distrib (fun j => g j x) (fun j => g j y)).symm
  calc ENNReal.ofReal (‖(∑ j ∈ s, g j x) - (∑ j ∈ s, g j y)‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal ((∑ j ∈ s, ‖g j x - g j y‖) / ‖x - y‖ ^ α) := by
        refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hp)
        rw [hsplit]
        exact norm_sum_le _ _
    _ = ENNReal.ofReal (∑ j ∈ s, ‖g j x - g j y‖ / ‖x - y‖ ^ α) := by rw [Finset.sum_div]
    _ = ∑ j ∈ s, ENNReal.ofReal (‖g j x - g j y‖ / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (norm_nonneg _) hp)
    _ ≤ ∑ j ∈ s, ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y),
          ENNReal.ofReal (‖g j x - g j y‖ / ‖x - y‖ ^ α) :=
        Finset.sum_le_sum fun j _ =>
          le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

/-- Subadditivity of the `C^{0,α}`-norm over a finite sum of `ℂ`-valued functions. -/
lemma holderNorm_zero_sum_le {ι : Type*} (s : Finset ι) {α : ℝ} (g : ι → X → ℂ)
    (Ω : Set X) :
    Work.CR.Flat.holderNorm 0 α (fun x => ∑ j ∈ s, g j x) Ω
      ≤ ∑ j ∈ s, Work.CR.Flat.holderNorm 0 α (g j) Ω := by
  rw [holderNorm_zero_decomp (fun x => ∑ j ∈ s, g j x) α Ω]
  calc Work.CR.Flat.iterDerivNorm 0 (fun x => ∑ j ∈ s, g j x) Ω
        + Work.CR.Flat.holderSeminorm 0 α (fun x => ∑ j ∈ s, g j x) Ω
      ≤ (∑ j ∈ s, Work.CR.Flat.iterDerivNorm 0 (g j) Ω)
        + (∑ j ∈ s, Work.CR.Flat.holderSeminorm 0 α (g j) Ω) :=
        add_le_add (iterDerivNorm_zero_sum_le s g Ω) (holderSeminorm_zero_sum_le s α g Ω)
    _ = ∑ j ∈ s, (Work.CR.Flat.iterDerivNorm 0 (g j) Ω
          + Work.CR.Flat.holderSeminorm 0 α (g j) Ω) := (Finset.sum_add_distrib).symm
    _ = ∑ j ∈ s, Work.CR.Flat.holderNorm 0 α (g j) Ω :=
        Finset.sum_congr rfl fun j _ => (holderNorm_zero_decomp (g j) α Ω).symm

end Aux

/-- **The `C^{0,α}`-bound for the one-step operator.**

Given a family `c l` of weights, each of finite `C^{0,α}`-norm on `ℂⁿ` and supported in the
polydisc `polydisc 0 ρ`, and a family `D l` whose `C^{0,α}`-norm on the larger polydisc
`polydisc 0 τ` (with `ρ < τ` coordinatewise) is bounded by `ofReal Cg`, the weighted sum
`z ↦ Σ_l c l z * D l z` — and hence its scalar multiple by any `A : ℂ` — has finite
`C^{0,α}`-norm on all of `ℂⁿ`.

The proof reduces the ambient norm to the one on `polydisc 0 τ` (valid because the sum
vanishes on the closed complement of `polydisc 0 ρ ⊆ polydisc 0 τ`), where each term is
estimated by the Leibniz rule for the sup-norm and the `α`-Hölder seminorm. -/
lemma finite_holder_of_supported_weighted {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α)
    {ρ τ : Fin n → ℝ} (hρτ : ∀ j, ρ j < τ j)
    (A : ℂ) (c D : Fin n → (Fin n → ℂ) → ℂ) (Cg : ℝ) (hCgpos : 0 < Cg)
    (hcfin : ∀ l, Work.CR.Flat.holderNorm 0 α (c l) Set.univ < ⊤)
    (hsuppc : ∀ l z, c l z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    (hD : ∀ l, Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)
      ≤ ENNReal.ofReal Cg) :
    ∃ C : ℝ, 0 < C ∧ Work.CR.Flat.holderNorm 0 α
      (fun z => A * ∑ l, c l z * D l z) Set.univ ≤ ENNReal.ofReal C := by
  -- ## The function vanishes on the closed complement of `polydisc 0 ρ`
  have hvan : ∀ z : Fin n → ℂ, (∃ i, ρ i ≤ ‖z i - (0 : Fin n → ℂ) i‖) →
      (fun z => A * ∑ l, c l z * D l z) z = 0 := by
    intro z hz
    obtain ⟨i, hi⟩ := hz
    have hzn : z ∉ Work.CR.Flat.polydisc 0 ρ := fun hmem => absurd (hmem i) (not_lt.mpr hi)
    have hsum : ∑ l, c l z * D l z = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      have hcz : c l z = 0 := by
        by_contra h
        exact hzn (hsuppc l z h)
      rw [hcz, zero_mul]
    show A * (∑ l, c l z * D l z) = 0
    rw [hsum, mul_zero]
  -- ## Reduction of the ambient norm to `polydisc 0 τ`
  have h1 : Work.CR.Flat.holderNorm 0 α (fun z => A * ∑ l, c l z * D l z) Set.univ
      ≤ Work.CR.Flat.holderNorm 0 α (fun z => A * ∑ l, c l z * D l z)
          (Work.CR.Flat.polydisc 0 τ) :=
    Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
      (c := (0 : Fin n → ℂ)) hρτ hα0 hvan
  -- ## Leibniz bound for a single term
  have hterm : ∀ l, Work.CR.Flat.holderNorm 0 α (fun z => c l z * D l z)
      (Work.CR.Flat.polydisc 0 τ)
      ≤ 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
              * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)) := by
    intro l
    have hc1 : Work.CR.Flat.iterDerivNorm 0 (c l) (Work.CR.Flat.polydisc 0 τ)
        ≤ Work.CR.Flat.holderNorm 0 α (c l) Set.univ :=
      iterDerivNorm_zero_le_holderNorm_univ (c l) α _
    have hc2 : Work.CR.Flat.holderSeminorm 0 α (c l) (Work.CR.Flat.polydisc 0 τ)
        ≤ Work.CR.Flat.holderNorm 0 α (c l) Set.univ :=
      holderSeminorm_zero_le_holderNorm_univ (c l) α _
    have hd1 : Work.CR.Flat.iterDerivNorm 0 (D l) (Work.CR.Flat.polydisc 0 τ)
        ≤ Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ) :=
      Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α (D l) _ le_rfl
    have hd2 : Work.CR.Flat.holderSeminorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)
        ≤ Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ) :=
      Work.CR.Flat.holderSeminorm_le_holderNorm 0 α (D l) _ le_rfl
    rw [holderNorm_zero_decomp (fun z => c l z * D l z) α (Work.CR.Flat.polydisc 0 τ)]
    calc Work.CR.Flat.iterDerivNorm 0 (fun z => c l z * D l z) (Work.CR.Flat.polydisc 0 τ)
          + Work.CR.Flat.holderSeminorm 0 α (fun z => c l z * D l z)
              (Work.CR.Flat.polydisc 0 τ)
        ≤ Work.CR.Flat.iterDerivNorm 0 (c l) (Work.CR.Flat.polydisc 0 τ)
            * Work.CR.Flat.iterDerivNorm 0 (D l) (Work.CR.Flat.polydisc 0 τ)
          + (Work.CR.Flat.iterDerivNorm 0 (c l) (Work.CR.Flat.polydisc 0 τ)
              * Work.CR.Flat.holderSeminorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)
            + Work.CR.Flat.holderSeminorm 0 α (c l) (Work.CR.Flat.polydisc 0 τ)
              * Work.CR.Flat.iterDerivNorm 0 (D l) (Work.CR.Flat.polydisc 0 τ)) :=
          add_le_add (iterDerivNorm_zero_mul_leF (c l) (D l) _)
            (holderSeminorm_zero_mul_leF α (c l) (D l) _)
      _ ≤ Work.CR.Flat.holderNorm 0 α (c l) Set.univ
            * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)
          + (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
              * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)
            + Work.CR.Flat.holderNorm 0 α (c l) Set.univ
              * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)) :=
          add_le_add (mul_le_mul' hc1 hd1) (add_le_add (mul_le_mul' hc1 hd2) (mul_le_mul' hc2 hd1))
      _ = 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
              * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)) := by ring
  -- ## Subadditivity over the finite sum
  have hsum : Work.CR.Flat.holderNorm 0 α (fun z => ∑ l, c l z * D l z)
      (Work.CR.Flat.polydisc 0 τ)
      ≤ ∑ l, 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
            * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)) := by
    refine (holderNorm_zero_sum_le (Finset.univ) (fun l z => c l z * D l z)
      (Work.CR.Flat.polydisc 0 τ)).trans ?_
    exact Finset.sum_le_sum fun l _ => hterm l
  have h2 : Work.CR.Flat.holderNorm 0 α (fun z => A * ∑ l, c l z * D l z)
      (Work.CR.Flat.polydisc 0 τ)
      ≤ ENNReal.ofReal ‖A‖ * (∑ l, 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
            * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ))) := by
    refine (holderNorm_zero_const_mul_le A (fun z => ∑ l, c l z * D l z)
      (Work.CR.Flat.polydisc 0 τ)).trans ?_
    exact mul_le_mul' le_rfl hsum
  -- ## Evaluating the finite sum of constants
  set K : ℝ := ∑ l, 3 * ((Work.CR.Flat.holderNorm 0 α (c l) Set.univ).toReal * Cg) with hK
  have h3 : (∑ l, 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
            * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)))
      ≤ ENNReal.ofReal K := by
    have hstep : ∀ l, 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
            * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ))
        ≤ ENNReal.ofReal (3 * ((Work.CR.Flat.holderNorm 0 α (c l) Set.univ).toReal * Cg)) := by
      intro l
      have hDl : Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)
          ≤ ENNReal.ofReal Cg := hD l
      have hMre : Work.CR.Flat.holderNorm 0 α (c l) Set.univ
          = ENNReal.ofReal ((Work.CR.Flat.holderNorm 0 α (c l) Set.univ).toReal) :=
        (ENNReal.ofReal_toReal (ne_of_lt (hcfin l))).symm
      calc 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
              * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ))
          ≤ 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ * ENNReal.ofReal Cg) :=
              mul_le_mul' le_rfl (mul_le_mul' le_rfl hDl)
        _ = 3 * (ENNReal.ofReal ((Work.CR.Flat.holderNorm 0 α (c l) Set.univ).toReal)
              * ENNReal.ofReal Cg) := by nth_rewrite 1 [hMre]; rfl
        _ = ENNReal.ofReal (3 * ((Work.CR.Flat.holderNorm 0 α (c l) Set.univ).toReal * Cg)) := by
              rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← mul_assoc,
                ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 3 by norm_num),
                ← ENNReal.ofReal_mul
                  (mul_nonneg (show (0:ℝ) ≤ 3 by norm_num) ENNReal.toReal_nonneg)]
              ring_nf
    calc (∑ l, 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
              * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ)))
        ≤ ∑ l, ENNReal.ofReal (3 * ((Work.CR.Flat.holderNorm 0 α (c l) Set.univ).toReal * Cg)) :=
            Finset.sum_le_sum fun l _ => hstep l
      _ = ENNReal.ofReal (∑ l, 3 * ((Work.CR.Flat.holderNorm 0 α (c l) Set.univ).toReal * Cg)) :=
            (ENNReal.ofReal_sum_of_nonneg
              (fun l _ => mul_nonneg (by norm_num)
                (mul_nonneg ENNReal.toReal_nonneg hCgpos.le))).symm
      _ = ENNReal.ofReal K := by rw [hK]
  -- ## Conclusion
  refine ⟨‖A‖ * K + 1, ?_, ?_⟩
  · have hK0 : 0 ≤ K := by
      rw [hK]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (by norm_num)
        (mul_nonneg ENNReal.toReal_nonneg hCgpos.le)
    have hmul := mul_nonneg (norm_nonneg A) hK0
    linarith
  · calc Work.CR.Flat.holderNorm 0 α (fun z => A * ∑ l, c l z * D l z) Set.univ
        ≤ Work.CR.Flat.holderNorm 0 α (fun z => A * ∑ l, c l z * D l z)
            (Work.CR.Flat.polydisc 0 τ) := h1
      _ ≤ ENNReal.ofReal ‖A‖ * (∑ l, 3 * (Work.CR.Flat.holderNorm 0 α (c l) Set.univ
            * Work.CR.Flat.holderNorm 0 α (D l) (Work.CR.Flat.polydisc 0 τ))) := h2
      _ ≤ ENNReal.ofReal ‖A‖ * ENNReal.ofReal K := mul_le_mul' le_rfl h3
      _ = ENNReal.ofReal (‖A‖ * K) := (ENNReal.ofReal_mul (norm_nonneg A)).symm
      _ ≤ ENNReal.ofReal (‖A‖ * K + 1) := ENNReal.ofReal_le_ofReal (by linarith)

theorem one_step_finite_holderF {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ τ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hτ : ∀ j, 0 < τ j) (hρτ : ∀ j, ρ j < τ j) :
    ∀ (c : Fin n → (Fin n → ℂ) → ℂ) (G : Fin n → (Fin n → ℂ) → ℂ),
      (∀ l, Work.CR.Flat.holderNorm 0 α (c l) Set.univ < ⊤) →
      (∀ l z, c l z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
      (∀ l, Continuous (G l)) → (∀ l, HasCompactSupport (G l)) →
      (∀ l, Work.CR.Flat.holderNorm 0 α (G l) Set.univ < ⊤) →
      ∃ C : ℝ, 0 < C ∧ Work.CR.Flat.holderNorm 0 α (fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
          ∑ l, c l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z) Set.univ
        ≤ ENNReal.ofReal C := by
  intro c G hcfin hsuppc hGcont hGcs hGfin
  obtain ⟨Cg, hCgpos, hCg⟩ :=
    dCoord_bmPotential_finite_holder (n := n) (α := α) (τ := τ) hn hα0 hα1 hτ G hGcont hGcs hGfin
  exact finite_holder_of_supported_weighted (n := n) (α := α) (ρ := ρ) (τ := τ) hα0.le hρτ
    ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) c
    (fun l z => Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential G) z) Cg hCgpos
    hcfin hsuppc hCg

end Work.NN.Core
