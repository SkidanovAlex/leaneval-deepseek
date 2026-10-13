/-
# `Work.FTS.RegPkgGal.ConsumerRegPkg` — the consumers of `RegPkg'` at the composite level

This file packages the corrected composite-Hölder transfer (`Consumer.gCompHolderQuant'`) in the
two shapes in which the physical layer (design §1, item 7) consumes it:

* `gCompHolder'` — the conjunction shape of the delivered `Work.FTS.Regularity.gCompHolder`
  (the Taylor datum as the single conjunction `|g| ≤ K z² ∧ (radial) ∧ (angular-Hölder)`);
* `gComp_abs_le'` / `gComp_abs_le_explicit` — the vanishing-rate transfer `|ĝ x| ≤ Ca·r(x)^α`, the
  delivered `Work.ConstructionInstance.gComp_abs_le` with the analytic hypothesis
  `ContDiffOn ℝ 2 ...` replaced by the *linear* vanishing `|g z θ| ≤ K z` on `z ∈ [0,1]` that
  `RegPkg'.htay` supplies directly (the two `rpow` helper lemmas are copied verbatim from the
  delivered file, where they are `private`);
* `RegPkg'.gcomp_holder` and `RegPkg'.gcomp_abs_le` — the **uniform-in-τ** versions extracted
  from a `RegPkg'`: the constants `Cv, Ng, K` of the package are chosen once for the whole strip,
  so the Hölder constant of the slice `x ↦ g (ρ(x)^{3α}) (|θ(x)|) τ` is *the same for every*
  `τ ∈ [0,S]` (this is the point of the quantitative form; see
  `Submission/Work/FTS/Regularity/physVort_holder_slice.lean` §5).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.Consumer
import Submission.Work.ConstructionInstance.gComp_abs_le
import Submission.Work.ConstructionInstance.Gamma_abs_theta_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Metric
open scoped Topology NNReal Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

variable {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}

/-- `|θ(x)| ∈ Iθ`. -/
lemma abs_theta_mem_Iθ (x : R3) : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
  refine ⟨abs_nonneg _, ?_⟩
  rw [Work.Cyl.theta]
  exact abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
    le_of_lt (Real.arctan_lt_pi_div_two _)⟩

/-- `π/2 ∈ Iθ`. -/
lemma pi_div_two_mem_Iθ : (Real.pi / 2) ∈ Work.Spaces.Iθ :=
  ⟨by positivity, le_refl _⟩

private lemma hpi_eq : (Real.pi : ℝ) / 2 = π / 2 := rfl

/-! ## The conjunction shape of the composite transfer -/

/-- The composite `x ↦ g (ρ(x)^{3α}) (|θ(x)|)` is `α`-Hölder, with the corrected constant
`gCompConst'`; hypothesis shape of `Work.FTS.Regularity.gCompHolder`, with the third clause of the
Taylor datum in the **corrected** (Hölder) form. -/
theorem gCompHolder' {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : ℝ → ℝ → ℝ}
    {Cv Lg Lθ K : ℝ} (hCv : 0 ≤ Cv) (hLg : 0 ≤ Lg) (hLθ : 0 ≤ Lθ) (hK : 0 ≤ K)
    (hvt : Work.Spaces.VanishTheta g)
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hzk : ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ - g z' θ| ≤ Lg * |z - z'| ^ α)
    (hzth : ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Lθ * |θ - θ'| ^ α)
    (htay : ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ| ≤ K * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ - g z' θ| ≤ K * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ - g z θ'| ≤ K * z ^ 2 * |θ - θ'| ^ α)) :
    HolderWith (gCompConstNN' α Cv Lg Lθ K) (⟨α, hα.le⟩ : NNReal)
      (fun x : R3 => g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)) :=
  gCompHolderQuant' hα hα13 hCv hLg hLθ hK hvt hquad0 hvan hzk hzth
    (fun z θ hz hz2 hθ => (htay θ hθ).1 z hz hz2)
    (fun z z' θ hz hz2 hz' hz'2 hθ => (htay θ hθ).2.1 z z' hz hz2 hz' hz'2)
    (fun z θ θ' hz hz2 hθ hθ' => (htay θ hθ).2.2 z hz hz2 θ' hθ')

/-! ## The vanishing-rate transfer -/

/-- `(r/ρ)^{2α} ≤ r^α` for `0 ≤ r ≤ ρ²` (copy of the `private` helper of
`Work.ConstructionInstance.gComp_abs_le`). -/
private lemma rpow_two_mul_le_of_le_sq {α r ρ : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (h : r ≤ ρ ^ 2) : (r / ρ) ^ (2 * α) ≤ r ^ α := by
  have hs0 : 0 ≤ r / ρ := div_nonneg hr hρ.le
  have hsρ : r / ρ ≤ ρ := by
    rw [div_le_iff₀ hρ]; nlinarith
  have h1 : (r / ρ) ^ α ≤ ρ ^ α := Real.rpow_le_rpow hs0 hsρ hα.le
  have h2 : (r / ρ) ^ (2 * α) = (r / ρ) ^ α * (r / ρ) ^ α := by
    rw [show 2 * α = α + α from by ring, Real.rpow_add' hs0 (by positivity)]
  rw [h2]
  calc (r / ρ) ^ α * (r / ρ) ^ α ≤ (r / ρ) ^ α * ρ ^ α :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs0 α)
    _ = (r / ρ * ρ) ^ α := (Real.mul_rpow hs0 hρ.le).symm
    _ = r ^ α := by rw [div_mul_cancel₀ r hρ.ne']

/-- `ρ^{3α} ≤ r^α` for `0 < ρ ≤ 1` and `ρ² < r` (copy of the `private` helper of
`Work.ConstructionInstance.gComp_abs_le`). -/
private lemma rpow_three_mul_le_of_sq_lt {α r ρ : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (h : ρ ^ 2 < r) : ρ ^ (3 * α) ≤ r ^ α := by
  have h1 : ρ ^ (3 * α) ≤ ρ ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have h2 : ρ ^ (2 * α) = (ρ ^ 2) ^ α := by
    rw [Real.rpow_mul hρ.le (2:ℝ) α, Real.rpow_two]
  calc ρ ^ (3 * α) ≤ ρ ^ (2 * α) := h1
    _ = (ρ ^ 2) ^ α := h2
    _ ≤ r ^ α := Real.rpow_le_rpow (sq_nonneg ρ) h.le hα.le

/-- The perturbation composite `x ↦ g (ρ(x)^{3α}) (|θ(x)|)` vanishes at least like `r^α`
(`r = Cyl.radial`), with the **explicit** constant `max K Cv`: the delivered
`Work.ConstructionInstance.gComp_abs_le` with the analytic hypothesis replaced by the *linear*
vanishing `|g z θ| ≤ K z` on `0 ≤ z ≤ 1`, which the corrected `RegPkg'.htay` supplies directly
(first clause: `|g| ≤ K z² ≤ K z` for `z ≤ 1`). -/
theorem gComp_abs_le_explicit {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    {Cv K : ℝ} (hCv : 0 ≤ Cv) (hK0 : 0 ≤ K) (hvt : Work.Spaces.VanishTheta g)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hlin : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ z : ℝ, 0 ≤ z → z ≤ 1 → |g z θ| ≤ K * z) :
    ∀ x : R3,
      |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)| ≤ max K Cv * (Work.Cyl.radial x) ^ α := by
  intro x
  by_cases hr : Work.Cyl.radial x = 0
  · have hθ : |Work.Cyl.theta x| = 0 := by
      rw [Work.Cyl.theta, hr, div_zero, Real.arctan_zero, abs_zero]
    have hz : Work.Cyl.radial x ^ α = 0 := by rw [hr, Real.zero_rpow hα.ne']
    rw [hθ, hvt.1, abs_zero, hz, mul_zero]
  · have hrpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr)
    have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hrpos (Work.Cyl.radial_le_rho x)
    have hρnn : 0 ≤ Work.Cyl.rho x := hρpos.le
    have hrn : 0 ≤ Work.Cyl.radial x := hrpos.le
    have hIθ : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
      refine ⟨abs_nonneg _, ?_⟩
      rw [Work.Cyl.theta]
      exact abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
        le_of_lt (Real.arctan_lt_pi_div_two _)⟩
    have hvan' : |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
        ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := by
      calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
          ≤ Cv * Work.ConstructionInstance.Gamma α (|Work.Cyl.theta x|) :=
            hvan _ _ (Real.rpow_nonneg hρnn _) hIθ
        _ ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) :=
            mul_le_mul_of_nonneg_left
              (Work.ConstructionInstance.Gamma_abs_theta_le hα hrpos) hCv
    by_cases hρ1 : Work.Cyl.rho x ≤ 1
    · by_cases hsub : Work.Cyl.radial x ≤ (Work.Cyl.rho x) ^ 2
      · calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := hvan'
          _ ≤ Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_left
                (rpow_two_mul_le_of_le_sq hα hrn hρpos hsub) hCv
          _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_right (le_max_right K Cv) (Real.rpow_nonneg hrn α)
      · have hz1 : Work.Cyl.rho x ^ (3 * α) ≤ 1 :=
          Real.rpow_le_one hρnn hρ1 (by positivity)
        have hKb := hlin (|Work.Cyl.theta x|) hIθ (Work.Cyl.rho x ^ (3 * α))
          (Real.rpow_nonneg hρnn _) hz1
        have h3 : Work.Cyl.rho x ^ (3 * α) ≤ (Work.Cyl.radial x) ^ α :=
          rpow_three_mul_le_of_sq_lt hα hrn hρpos hρ1 (not_le.mp hsub)
        calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
            ≤ K * (Work.Cyl.rho x ^ (3 * α)) := hKb
          _ ≤ K * (Work.Cyl.radial x) ^ α := mul_le_mul_of_nonneg_left h3 hK0
          _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
              mul_le_mul_of_nonneg_right (le_max_left K Cv) (Real.rpow_nonneg hrn α)
    · have hρge : 1 ≤ Work.Cyl.rho x := le_of_lt (not_le.mp hρ1)
      have hsub : Work.Cyl.radial x ≤ (Work.Cyl.rho x) ^ 2 := by
        have h1 : Work.Cyl.radial x ≤ Work.Cyl.rho x := Work.Cyl.radial_le_rho x
        nlinarith
      calc |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)|
          ≤ Cv * (Work.Cyl.radial x / Work.Cyl.rho x) ^ (2 * α) := hvan'
        _ ≤ Cv * (Work.Cyl.radial x) ^ α :=
            mul_le_mul_of_nonneg_left
              (rpow_two_mul_le_of_le_sq hα hrn hρpos hsub) hCv
        _ ≤ max K Cv * (Work.Cyl.radial x) ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right K Cv) (Real.rpow_nonneg hrn α)

/-- Existential form of `gComp_abs_le_explicit`. -/
theorem gComp_abs_le' {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    {Cv K : ℝ} (hCv : 0 ≤ Cv) (hK0 : 0 ≤ K)
    (hvt : Work.Spaces.VanishTheta g)
    (hvan : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ| ≤ Cv * Work.ConstructionInstance.Gamma α θ)
    (hlin : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ z : ℝ, 0 ≤ z → z ≤ 1 → |g z θ| ≤ K * z) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ x : R3,
      |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)| ≤ Ca * (Work.Cyl.radial x) ^ α :=
  ⟨max K Cv, le_trans hK0 (le_max_left K Cv),
    gComp_abs_le_explicit hα hCv hK0 hvt hvan hlin⟩

/-! ## The uniform-in-`τ` consumers of `RegPkg'` -/

theorem RegPkg'.gcomp_holder (h : RegPkg' α S A B g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc 0 S, ∀ x y : R3,
      |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|) τ
        - g (Work.Cyl.rho y ^ (3 * α)) (|Work.Cyl.theta y|) τ| ≤ C * dist x y ^ α := by
  obtain ⟨Cv, hCv0, hvan⟩ := h.hvan
  obtain ⟨N, hN⟩ := h.hg
  obtain ⟨K, hK0, htay⟩ := h.htay
  refine ⟨gCompConst' α Cv N N K,
    gCompConst'_nonneg α Cv N N K h.hα.le hCv0 hN.1 hN.1 hK0, ?_⟩
  intro τ hτ x y
  classical
  set G : ℝ → ℝ → ℝ := fun z θ => if θ ∈ Work.Spaces.Iθ then g z θ τ else 0 with hGdef
  have hGeq : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → G z θ = g z θ τ := by
    intro z θ hθ; simp only [hGdef]; rw [ite_eq_left hθ]
  have hG : HolderWith (gCompConstNN' α Cv N N K) (⟨α, h.hα.le⟩ : NNReal)
      (fun x : R3 => G (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|)) := by
    refine gCompHolderQuant' h.hα h.hα13 hCv0 hN.1 hN.1 hK0 ?_ ?_
      (fun z θ hz hθ => ?_) (fun z z' θ hz hz' hθ => ?_) (fun z θ θ' hz hθ hθ' => ?_)
      (fun z θ hz hz2 hθ => ?_) (fun z z' θ hz hz2 hz' hz'2 hθ => ?_)
      (fun z θ θ' hz hz2 hθ hθ' => ?_)
    · exact ⟨fun z => by
        simpa only [hGeq z 0 Work.Spaces.zero_mem_Iθ, gSlice_apply] using (h.hvt τ hτ).1 z,
        fun z => by
        simpa only [hGeq z (Real.pi / 2) pi_div_two_mem_Iθ, gSlice_apply] using
          (h.hvt τ hτ).2 z⟩
    · intro θ
      by_cases hθ : θ ∈ Work.Spaces.Iθ
      · simpa only [hGeq 0 θ hθ] using h.hquad0 τ hτ θ hθ
      · simp only [hGdef]
        rw [ite_eq_right hθ]
    · simpa only [hGeq z θ hθ] using hvan τ hτ z θ hz hθ
    · simpa only [hGeq z θ hθ, hGeq z' θ hθ] using hN.zmod hz hz' hθ hτ
    · simpa only [hGeq z θ hθ, hGeq z θ' hθ'] using hN.thmod hz hθ hθ' hτ
    · simpa only [hGeq z θ hθ] using (htay τ hτ θ hθ).1 z hz hz2
    · simpa only [hGeq z θ hθ, hGeq z' θ hθ] using
        (htay τ hτ θ hθ).2.1 z z' hz hz2 hz' hz'2
    · simpa only [hGeq z θ hθ, hGeq z θ' hθ'] using
        (htay τ hτ θ hθ).2.2 z hz hz2 θ' hθ'
  have hd := hG.dist_le x y
  rw [Real.dist_eq] at hd
  rw [gCompConstNN'_coe α Cv N N K h.hα.le hCv0 hN.1 hN.1 hK0] at hd
  simp only [hGeq (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|) (abs_theta_mem_Iθ x),
    hGeq (Work.Cyl.rho y ^ (3 * α)) (|Work.Cyl.theta y|) (abs_theta_mem_Iθ y)] at hd
  push_cast at hd
  exact hd

theorem RegPkg'.gcomp_abs_le (h : RegPkg' α S A B g) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ τ ∈ Set.Icc 0 S, ∀ x : R3,
      |g (Work.Cyl.rho x ^ (3 * α)) (|Work.Cyl.theta x|) τ| ≤ Ca * (Work.Cyl.radial x) ^ α := by
  obtain ⟨Cv, hCv0, hvan⟩ := h.hvan
  obtain ⟨K, hK0, htay⟩ := h.htay
  refine ⟨max K Cv, le_trans hK0 (le_max_left K Cv), ?_⟩
  intro τ hτ x
  exact gComp_abs_le_explicit h.hα hCv0 hK0 (h.hvt τ hτ)
    (fun z θ hz hθ => hvan τ hτ z θ hz hθ)
    (fun θ hθ z hz hz1 => by
      have h1 := (htay τ hτ θ hθ).1 z hz (le_trans hz1 (by norm_num))
      have h2 : z ^ 2 ≤ z := by nlinarith
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hK0)) x

end Work.FTS.RegPkgGal
