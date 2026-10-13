/-
# `Work.FTS.Regularity.physVort_bundle` — the physical vorticity is strip-admissible

This is the **assembly node** of the regularity chapter (node N7 of the audit): from the
regularity package `RegPkg α S A B g` of the self-similar profile it produces the *full*
hypothesis bundle `BSAdmissibleStripFull α (physVort α A B g) R S` of the space–time Schauder
estimate, for a suitable ball radius `R > 0`.

`BSAdmissibleStripFull` is the conjunction of three groups of clauses:

* **`BSAdmissibleStrip`** — the vorticity is supported in the fixed ball `closedBall 0 R` on the
  strip `[0,S]`, uniformly bounded there, uniformly `α`-Hölder in `x` slicewise, uniformly
  `α`-Hölder in `τ`, and every slice is ae-strongly measurable;
* **`TimeDerivStrip`** — the slices are differentiable in `τ` on the strip with uniformly bounded
  derivative and ae-strongly measurable derivative slices;
* **`TimeDerivStripHolder`** — the `τ`-derivative slices are `α`-Hölder in `τ`, uniformly in `x`.

Most clauses are transferred from the profile by the sibling modules of this chapter
(`physVort_support`, `physVort_bound`, `physVort_holder_slice`, `physVort_holder_time`,
`physVort_hasDerivAt_and_bound`, `physVort_timeDeriv_aesm`).  Two genuinely new things are proved
here, because no sibling supplies them:

* the **ae-strong measurability of the vorticity slices**: a slice is Hölder continuous of
  exponent `α > 0` (`physVort_holder_slice`), hence continuous, hence Borel measurable, hence
  ae-strongly measurable for Lebesgue measure (`physVort_slice_holder` feeds the sibling's
  estimate into the `HolderWith` form, whose `continuous` gives the measurability);
* the **`τ`-Hölder continuity of `∂_τω`** (`pvb_timeDeriv_holder`), i.e. the
  `TimeDerivStripHolder` clause.  This is the chain-rule estimate for the dynamic rescaling:
  `timeDeriv (physVort α A B g) x τ` is identified with `vortDt α A B g x τ` (Part A), and the
  `τ`-variation of that explicit expression is estimated in the two regimes of the self-similar
  variable `z = ρ(x)^{3α}/B(τ)` (Part B):

  - *inside* the support radius `z ≤ L` the curve `τ ↦ ρ^{3α}/B(τ)` is Lipschitz with a constant
    proportional to `ρ^{3α}`, which the support hypothesis bounds, and the profile, its
    `z`-derivative and the `τ`-derivative of `g` are `α`-Hölder in `(z,τ)` by the jets
    `RegPkg.hg`, `RegPkg.hpz`, `RegPkg.hgdoth`;
  - *outside* it (`ρ^{3α} > L b₁`) the self-similar variable stays beyond the support radius, so
    the profile, its `z`-derivative (`dzProfFullZero`) and `∂_τ g` (`dtgZero`) all vanish, and
    the whole derivative is `0`.

  The clock factors are the elementary estimates `pvb_clockData` (the reciprocal of the amplitude,
  and the two ratios `A'/A²`, `B'/B`), and the Lipschitz bound for the scaling is
  `clockLipschitz`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.physVort_support
import Submission.Work.FTS.Regularity.physVort_bound
import Submission.Work.FTS.Regularity.physVort_holder_slice
import Submission.Work.FTS.Regularity.physVort_holder_time
import Submission.Work.FTS.Regularity.physVort_hasDerivAt_and_bound
import Submission.Work.FTS.Regularity.physVort_timeDeriv_aesm
import Submission.Work.FTS.Regularity.profFullHolder
import Submission.Work.FTS.Regularity.profFullBounds
import Submission.Work.FTS.Regularity.dzProfFullUniform
import Submission.Work.FTS.Regularity.dzProfFullZero
import Submission.Work.FTS.Regularity.dtgZero
import Submission.Work.FTS.Regularity.clockBounds
import Submission.Work.FTS.Regularity.clockLipschitz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology

open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Work.FTS.Regularity

/-! ## The two clauses of `BSAdmissibleStrip` that are not literal copies of a sibling -/

/-- **The slicewise `HolderWith` form of `physVort_holder_slice`**, in the exponent and constant
type of the admissibility bundle (`NNReal`). -/
theorem physVort_slice_holder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ H : NNReal, ∀ τ ∈ Set.Icc 0 S,
      HolderWith H (⟨α, h.hα.le⟩ : NNReal) (fun y : R3 => physVort α A B g y τ) := by
  obtain ⟨C, hC0, hC⟩ := physVort_holder_slice h
  refine ⟨⟨C, hC0⟩, fun τ hτ => Work.Stability.holderWith_of_dist_le (fun x y => ?_)⟩
  have h1 := hC τ hτ x y
  change ‖physVort α A B g x τ - physVort α A B g y τ‖ ≤ C * ‖x - y‖ ^ α
  exact h1

/-- **The vorticity slices are ae-strongly measurable.**  Each slice is Hölder continuous of
exponent `α > 0` (`physVort_slice_holder`), hence continuous, hence Borel measurable; on `ℝ³`
with Lebesgue measure that gives ae-strong measurability. -/
theorem physVort_slice_aesm {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∀ τ ∈ Set.Icc 0 S, MeasureTheory.AEStronglyMeasurable
      (fun y : R3 => physVort α A B g y τ) MeasureTheory.volume := by
  obtain ⟨H, hH⟩ := physVort_slice_holder h
  intro τ hτ
  have hpos : (0 : NNReal) < (⟨α, h.hα.le⟩ : NNReal) := NNReal.coe_pos.mpr h.hα
  exact ((hH τ hτ).continuous hpos).aestronglyMeasurable

/-! ## Part A: the chain rule and the explicit value of `∂_τω` -/

theorem pvb_gComp_hasDerivAt {g : ℝ → ℝ → ℝ → ℝ} {θ S τ z' : ℝ}
    (hcont : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Ioo (-1) (S + 1)) {zfun : ℝ → ℝ} (hz : -1 < zfun τ)
    (hzfun : HasDerivAt zfun z' τ) :
    HasDerivAt (fun s => g (zfun s) θ s)
      (z' * Work.Spaces.pz (gSlice g τ) (zfun τ) θ
        + deriv (fun t => g (zfun τ) θ t) τ) τ := by
  set G : ℝ × ℝ → ℝ := fun q => g q.1 θ q.2 with hGdef
  have hopen : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) :=
    (isOpen_Ioi : IsOpen (Set.Ioi (-1 : ℝ))).prod
      (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) (S + 1)))
  have hmem : (zfun τ, τ) ∈ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) := ⟨hz, hτ⟩
  have hnhds : (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) ∈ 𝓝 (zfun τ, τ) :=
    hopen.mem_nhds (x := (zfun τ, τ)) hmem
  have hdiff : DifferentiableAt ℝ G (zfun τ, τ) :=
    (hcont.contDiffAt hnhds).differentiableAt (by norm_num)
  have hF : HasFDerivAt G (fderiv ℝ G (zfun τ, τ)) (zfun τ, τ) := hdiff.hasFDerivAt
  set L : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ G (zfun τ, τ) with hLdef
  have hcurve : HasDerivAt (fun s : ℝ => (zfun s, s)) ((z', (1 : ℝ)) : ℝ × ℝ) τ :=
    hzfun.prodMk (hasDerivAt_id τ)
  have hcomp : HasDerivAt (G ∘ fun s : ℝ => (zfun s, s)) (L (z', 1)) τ :=
    hF.comp_hasDerivAt (f := fun s : ℝ => (zfun s, s)) τ hcurve
  have hcomp' : HasDerivAt (fun s => g (zfun s) θ s) (L (z', 1)) τ := by
    simpa [hGdef, Function.comp_def] using hcomp
  have hL1 : L (1, 0) = Work.Spaces.pz (gSlice g τ) (zfun τ) θ := by
    have h := hF.comp_hasDerivAt (f := fun s : ℝ => (s, τ)) (zfun τ)
      (HasDerivAt.prodMk (hasDerivAt_id (zfun τ)) (hasDerivAt_const (zfun τ) τ))
    have hd : deriv (fun s => G (s, τ)) (zfun τ) = L (1, 0) := h.deriv
    have hev : deriv (fun s => G (s, τ)) (zfun τ)
        = Work.Spaces.pz (gSlice g τ) (zfun τ) θ := by
      simp [hGdef, Work.Spaces.pz]
    exact hd.symm.trans hev
  have hL2 : L (0, 1) = deriv (fun t => g (zfun τ) θ t) τ := by
    have h := hF.comp_hasDerivAt (f := fun s : ℝ => (zfun τ, s)) τ
      (HasDerivAt.prodMk (hasDerivAt_const τ (zfun τ)) (hasDerivAt_id τ))
    have hd : deriv ((fun q : ℝ × ℝ => g q.1 θ q.2) ∘ fun s : ℝ => (zfun τ, s)) τ
        = L (0, 1) := h.deriv
    simpa [hGdef, Function.comp_def] using hd.symm
  have hval : L (z', 1) = z' * Work.Spaces.pz (gSlice g τ) (zfun τ) θ
      + deriv (fun t => g (zfun τ) θ t) τ := by
    have hsplit : ((z', (1 : ℝ)) : ℝ × ℝ)
        = z' • ((1, 0) : ℝ × ℝ) + (1 : ℝ) • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, map_smul, hL1, hL2]
    simp
  rw [hval] at hcomp'
  exact hcomp'

theorem pvb_profOdd_hasDerivAt {α S : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {ρ θ τ : ℝ}
    (hθabs : |θ| ≤ Real.pi / 2) (hρ : 0 ≤ ρ)
    (hcont : ∀ θ' ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ' q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Ioo (-1) (S + 1)) (hBpos : 0 < B τ) (hBd : HasDerivAt B (deriv B τ) τ) :
    HasDerivAt (fun s => profOdd α g (ρ ^ pExp α / B s) θ s) (dProfOdd α B g ρ θ τ) τ := by
  have hBne : B τ ≠ 0 := ne_of_gt hBpos
  have hz0 : 0 ≤ ρ ^ pExp α / B τ := div_nonneg (Real.rpow_nonneg hρ _) hBpos.le
  have hz1 : -1 < ρ ^ pExp α / B τ := by linarith
  have hz : HasDerivAt (fun s : ℝ => ρ ^ pExp α / B s) (zSlope α B ρ τ) τ := by
    have h := (hasDerivAt_const τ (ρ ^ pExp α)).div hBd hBne
    rw [zSlope]
    exact h.congr_deriv (by ring)
  have hcore : ∀ θ₁ : ℝ, θ₁ ∈ Work.Spaces.Iθ →
      HasDerivAt (fun s => profFull α g (ρ ^ pExp α / B s) θ₁ s)
        (zSlope α B ρ τ * pzProf α g (ρ ^ pExp α / B τ) θ₁ τ
          + deriv (fun t => g (ρ ^ pExp α / B τ) θ₁ t) τ) τ := by
    intro θ₁ hθ₁
    have hF : HasDerivAt (fun s => Work.Construction.Fstar (pExp α) (ρ ^ pExp α / B s) θ₁)
        (Work.Spaces.pz (Work.Construction.Fstar (pExp α)) (ρ ^ pExp α / B τ) θ₁
          * zSlope α B ρ τ) τ :=
      HasDerivAt.comp (h := fun s : ℝ => ρ ^ pExp α / B s) τ
        (Work.ConstructionInstance.hasDerivAt_Fstar_z (ρ ^ pExp α / B τ) θ₁ hz1) hz
    have hG := pvb_gComp_hasDerivAt (hcont θ₁ hθ₁) hτ hz1 hz
    have hsum := hF.add hG
    have hmul : HasDerivAt (fun s : ℝ => profFull α g (ρ ^ pExp α / B s) θ₁ s)
        (Work.Spaces.pz (Work.Construction.Fstar (pExp α)) (ρ ^ pExp α / B τ) θ₁ * zSlope α B ρ τ
          + (zSlope α B ρ τ * Work.Spaces.pz (gSlice g τ) (ρ ^ pExp α / B τ) θ₁
            + deriv (fun t => g (ρ ^ pExp α / B τ) θ₁ t) τ)) τ := by
      have heq : (fun s : ℝ => profFull α g (ρ ^ pExp α / B s) θ₁ s)
          = fun s => Work.Construction.Fstar (pExp α) (ρ ^ pExp α / B s) θ₁
              + g (ρ ^ pExp α / B s) θ₁ s := by
        funext s; exact profFull_apply α g _ θ₁ s
      rw [heq]
      exact hsum
    refine hmul.congr_deriv ?_
    rw [pzProf]
    ring
  rw [dProfOdd]
  by_cases hθ0 : 0 ≤ θ
  · rw [if_pos hθ0]
    have hθ₁ : θ ∈ Work.Spaces.Iθ := ⟨hθ0, le_trans (le_abs_self θ) hθabs⟩
    have heq : (fun s : ℝ => profOdd α g (ρ ^ pExp α / B s) θ s)
        = fun s => profFull α g (ρ ^ pExp α / B s) θ s := by
      funext s; rw [profOdd, if_pos hθ0]
    rw [heq]
    exact hcore θ hθ₁
  · rw [if_neg hθ0]
    have hθ₁ : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith [not_le.mp hθ0], by linarith [neg_le_abs θ, hθabs]⟩
    have hneg := (hcore (-θ) hθ₁).neg
    have heq : (fun s : ℝ => profOdd α g (ρ ^ pExp α / B s) θ s)
        = fun s => -profFull α g (ρ ^ pExp α / B s) (-θ) s := by
      funext s; rw [profOdd, if_neg hθ0]
    rw [heq]
    exact hneg

theorem pvb_timeDeriv_eq_vortDt {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∀ x : R3, ∀ τ ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ = vortDt α A B g x τ := by
  intro x τ hτ
  have hmem : τ ∈ Set.Ioo (-1) (S + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2, h.hS]⟩
  have hscal := pvb_profOdd_hasDerivAt (α := α) (S := S) (B := B) (g := g)
    (ρ := Work.Cyl.rho x) (θ := Work.Cyl.theta x) (τ := τ)
    (abs_theta_mem_Iθ x).2 (Work.Cyl.rho_nonneg x) h.hcont hmem
    (h.hB τ hτ) (h.hBdiff τ hτ)
  have hvec := hscal.smul_const (Work.Cyl.eTheta x)
  have hAinv : HasDerivAt (fun s : ℝ => (A s)⁻¹) (-(deriv A τ) / (A τ) ^ 2) τ :=
    (h.hAdiff τ hτ).inv (ne_of_gt (h.hA τ hτ))
  have hprod := hAinv.smul hvec
  have heq : (fun s : ℝ => physVort α A B g x s)
      = fun s : ℝ => (A s)⁻¹ • (profOdd α g (Work.Cyl.rho x ^ pExp α / B s)
          (Work.Cyl.theta x) s • Work.Cyl.eTheta x) := by
    funext s; rw [physVort_eq_smul]
  have hder : HasDerivAt (fun s : ℝ => physVort α A B g x s) (vortDt α A B g x τ) τ := by
    rw [heq, vortDt]
    exact hprod
  rw [physVort_timeDeriv]
  exact hder.deriv

/-! ## Part B: the `τ`-Hölder continuity of `∂_τω` -/

/-- The `z`-slope of the self-similar variable in the form used below. -/
theorem pvb_zSlope_eq {α : ℝ} {B : ℝ → ℝ} {ρ s : ℝ} (hB : B s ≠ 0) :
    zSlope α B ρ s = -((ρ ^ pExp α / B s) * (deriv B s / B s)) := by
  rw [zSlope]
  field_simp

/-- `pzProf` is the `z`-derivative of the full profile. -/
theorem pvb_pzProf_eq_deriv {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) {z θ τ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ)
    (hτ : τ ∈ Set.Icc 0 S) :
    pzProf α g z θ τ = deriv (fun z' => profFull α g z' θ τ) z := by
  have h1 := (dzProfFullUniform h z hz).1 z θ τ hz hθ hτ
  rw [pzProf, h1]
  rfl

/-- The absolute value of the odd extension is the absolute value of the profile at `|θ|`. -/
theorem pvb_profOdd_abs_eq (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z θ τ : ℝ) :
    |profOdd α g z θ τ| = |profFull α g z |θ| τ| := by
  by_cases hθ : 0 ≤ θ
  · rw [profOdd, if_pos hθ, abs_of_nonneg hθ]
  · rw [profOdd, if_neg hθ, abs_of_neg (not_le.mp hθ), abs_neg]

/-- The odd extension vanishes where the profile does. -/
theorem pvb_profOdd_eq_zero {α : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {z θ τ : ℝ}
    (h : profFull α g z |θ| τ = 0) : profOdd α g z θ τ = 0 := by
  by_cases hθ : 0 ≤ θ
  · have hθ' : |θ| = θ := abs_of_nonneg hθ
    rw [profOdd, if_pos hθ]
    rw [hθ'] at h
    exact h
  · have hθ' : |θ| = -θ := abs_of_neg (not_le.mp hθ)
    rw [profOdd, if_neg hθ]
    rw [hθ'] at h
    rw [h, neg_zero]

/-- The odd extension of two points differs by the difference of the profiles at `|θ|`. -/
theorem pvb_profOdd_sub (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) (z z' θ τ τ' : ℝ) :
    |profOdd α g z θ τ - profOdd α g z' θ τ'|
      = |profFull α g z |θ| τ - profFull α g z' |θ| τ'| := by
  by_cases hθ : 0 ≤ θ
  · rw [profOdd, if_pos hθ, profOdd, if_pos hθ, abs_of_nonneg hθ]
  · rw [profOdd, if_neg hθ, profOdd, if_neg hθ, abs_of_neg (not_le.mp hθ)]
    rw [show -profFull α g z (-θ) τ - -profFull α g z' (-θ) τ'
        = -(profFull α g z (-θ) τ - profFull α g z' (-θ) τ') by ring, abs_neg]

/-- **The explicit form of `dProfOdd`**: the slope of the self-similar variable times the
`z`-derivative of the profile, plus the `τ`-derivative of the perturbation, with the sign of the
odd extension in `θ`. -/
theorem pvb_dProfOdd_eq {α : ℝ} {B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {ρ θ τ : ℝ}
    (hB : B τ ≠ 0) :
    dProfOdd α B g ρ θ τ
      = (if 0 ≤ θ then (1 : ℝ) else -1)
        * (-((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
            * (deriv B τ / B τ)
          + deriv (fun s => g (ρ ^ pExp α / B τ) |θ| s) τ) := by
  rw [dProfOdd]
  have hsl := pvb_zSlope_eq (α := α) (B := B) (ρ := ρ) (s := τ) hB
  by_cases hθ : 0 ≤ θ
  · rw [if_pos hθ, if_pos hθ, abs_of_nonneg hθ, hsl]
    ring
  · rw [if_neg hθ, if_neg hθ, abs_of_neg (not_le.mp hθ), hsl]
    ring

/-! ### The `τ`-Hölder estimate for `∂_τω` -/

/-- **Interpolation on a bounded strip**: `d ≤ S^(1-α)·d^α` for `0 ≤ d ≤ S` and `0 < α ≤ 1`. -/
theorem pvb_self_le_rpow {α S d : ℝ} (hd : 0 ≤ d) (hdS : d ≤ S) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    d ≤ S ^ (1 - α) * d ^ α := by
  rcases eq_or_lt_of_le hd with h | h
  · rw [← h]
    simp [Real.zero_rpow, hα0.ne']
  · have h1 : d = d ^ (1 - α) * d ^ α := by
      rw [← Real.rpow_add h, show 1 - α + α = 1 by ring, Real.rpow_one]
    have h2 : d ^ (1 - α) ≤ S ^ (1 - α) := Real.rpow_le_rpow hd hdS (by linarith)
    have h3 : 0 ≤ d ^ α := Real.rpow_nonneg hd _
    calc d = d ^ (1 - α) * d ^ α := h1
      _ ≤ S ^ (1 - α) * d ^ α := mul_le_mul_of_nonneg_right h2 h3

theorem pvb_clockData {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} (h : RegPkg α S A B g) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |(A τ)⁻¹ - (A τ')⁻¹| ≤ C * |τ - τ'| ^ α) ∧
      (∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
        |deriv A τ / (A τ) ^ 2 - deriv A τ' / (A τ') ^ 2| ≤ C * |τ - τ'| ^ α) ∧
      (∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
        |deriv B τ / B τ - deriv B τ' / B τ'| ≤ C * |τ - τ'| ^ α) := by
  obtain ⟨a₀, a₁, ha₀, hAb⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hBb⟩ := h.hBb
  obtain ⟨a₂, ha₂⟩ := h.hAd
  obtain ⟨b₂, hb₂⟩ := h.hBd
  obtain ⟨a₃, ha₃⟩ := h.hAdh
  obtain ⟨b₃, hb₃⟩ := h.hBdh
  obtain ⟨Kb, hKb0, hKb⟩ := clockLipschitz h
  set A2 : ℝ := max a₂ 0 with hA2def
  set A3 : ℝ := max a₃ 0 with hA3def
  set B2 : ℝ := max b₂ 0 with hB2def
  set B3 : ℝ := max b₃ 0 with hB3def
  set K' : ℝ := S ^ (1 - α) with hK'def
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, h.hS.le⟩
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ (le_trans (hAb 0 h0mem).1 (hAb 0 h0mem).2)
  have hb₁0 : 0 < b₁ := lt_of_lt_of_le hb₀ (le_trans (hBb 0 h0mem).1 (hBb 0 h0mem).2)
  have hA20 : 0 ≤ A2 := le_max_right _ _
  have hA30 : 0 ≤ A3 := le_max_right _ _
  have hB20 : 0 ≤ B2 := le_max_right _ _
  have hB30 : 0 ≤ B3 := le_max_right _ _
  have hK'0 : 0 ≤ K' := by rw [hK'def]; exact Real.rpow_nonneg h.hS.le _
  have hA2 : ∀ τ ∈ Set.Icc 0 S, |deriv A τ| ≤ A2 :=
    fun τ hτ => le_trans (ha₂ τ hτ) (le_max_left _ _)
  have hB2 : ∀ τ ∈ Set.Icc 0 S, |deriv B τ| ≤ B2 :=
    fun τ hτ => le_trans (hb₂ τ hτ) (le_max_left _ _)
  have hA3 : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |deriv A τ - deriv A τ'| ≤ A3 * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => le_trans (ha₃ τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (abs_nonneg _) α))
  have hB3 : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |deriv B τ - deriv B τ'| ≤ B3 * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => le_trans (hb₃ τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (abs_nonneg _) α))
  have hAlip : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |A τ - A τ'| ≤ a₂ * |τ - τ'| :=
    abs_sub_le_of_deriv_bound h.hAdiff ha₂
  have hK1 : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |τ - τ'| ≤ K' * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    have h1 : |τ - τ'| ≤ S := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hτ.1, hτ.2, hτ'.1, hτ'.2]
    have := pvb_self_le_rpow (abs_nonneg _) h1 h.hα (le_trans h.hα13 (by norm_num))
    rwa [hK'def]
  set C : ℝ := A2 / a₀ ^ 2 * K' + (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4
      + (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ A2 / a₀ ^ 2 * K' := by positivity
    have h2 : 0 ≤ (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4 := by positivity
    have h3 : 0 ≤ (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 := by positivity
    linarith
  have hterm1 : A2 / a₀ ^ 2 * K' ≤ C := by
    rw [hCdef]
    have h2 : 0 ≤ (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4 := by positivity
    have h3 : 0 ≤ (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 := by positivity
    linarith
  have hterm2 : (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ A2 / a₀ ^ 2 * K' := by positivity
    have h3 : 0 ≤ (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 := by positivity
    linarith
  have hterm3 : (B3 * b₁ + B2 * Kb * K') / b₀ ^ 2 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ A2 / a₀ ^ 2 * K' := by positivity
    have h2 : 0 ≤ (A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4 := by positivity
    linarith
  refine ⟨C, hC0, ?_, ?_, ?_⟩
  · intro τ hτ τ' hτ'
    have hAτ : 0 < A τ := h.hA τ hτ
    have hAτ' : 0 < A τ' := h.hA τ' hτ'
    have hnum : |A τ' - A τ| ≤ A2 * |τ - τ'| := by
      rw [abs_sub_comm]
      exact le_trans (hAlip τ hτ τ' hτ')
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    have hden : a₀ ^ 2 ≤ A τ * A τ' := by
      have h1 := (hAb τ hτ).1
      have h2 := (hAb τ' hτ').1
      nlinarith [mul_le_mul h1 h2 ha₀.le hAτ.le]
    have hkey : |(A τ)⁻¹ - (A τ')⁻¹| = |A τ' - A τ| / (A τ * A τ') := by
      rw [inv_sub_inv (ne_of_gt hAτ) (ne_of_gt hAτ'), abs_div, abs_of_pos (mul_pos hAτ hAτ')]
    rw [hkey]
    have h1 : |A τ' - A τ| / (A τ * A τ') ≤ A2 * |τ - τ'| / (A τ * A τ') :=
      div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hAτ hAτ'))
    have h2 : A2 * |τ - τ'| / (A τ * A τ') ≤ A2 * |τ - τ'| / a₀ ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg hA20 (abs_nonneg _)) (by positivity) hden
    have h3 : A2 * |τ - τ'| / a₀ ^ 2 ≤ A2 / a₀ ^ 2 * K' * |τ - τ'| ^ α := by
      calc A2 * |τ - τ'| / a₀ ^ 2 = (A2 / a₀ ^ 2) * |τ - τ'| := by ring
        _ ≤ (A2 / a₀ ^ 2) * (K' * |τ - τ'| ^ α) :=
            mul_le_mul_of_nonneg_left (hK1 τ hτ τ' hτ') (div_nonneg hA20 (by positivity))
        _ = A2 / a₀ ^ 2 * K' * |τ - τ'| ^ α := by ring
    have h4 : A2 / a₀ ^ 2 * K' * |τ - τ'| ^ α ≤ C * |τ - τ'| ^ α :=
      mul_le_mul_of_nonneg_right hterm1 (Real.rpow_nonneg (abs_nonneg _) α)
    exact le_trans (le_trans h1 h2) (le_trans h3 h4)
  · intro τ hτ τ' hτ'
    have hAτ : 0 < A τ := h.hA τ hτ
    have hAτ' : 0 < A τ' := h.hA τ' hτ'
    have hnum : |deriv A τ * (A τ') ^ 2 - deriv A τ' * (A τ) ^ 2|
        ≤ A3 * a₁ ^ 2 * |τ - τ'| ^ α + A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α := by
      have hsplit : deriv A τ * (A τ') ^ 2 - deriv A τ' * (A τ) ^ 2
          = (deriv A τ - deriv A τ') * (A τ') ^ 2
            + deriv A τ' * ((A τ') ^ 2 - (A τ) ^ 2) := by ring
      rw [hsplit]
      have h1 : |(deriv A τ - deriv A τ') * (A τ') ^ 2| ≤ A3 * a₁ ^ 2 * |τ - τ'| ^ α := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (A τ'))]
        calc |deriv A τ - deriv A τ'| * (A τ') ^ 2 ≤ (A3 * |τ - τ'| ^ α) * a₁ ^ 2 :=
              mul_le_mul (hA3 τ hτ τ' hτ') (by nlinarith [(hAb τ' hτ').2, ha₁0.le])
                (sq_nonneg _) (mul_nonneg hA30 (Real.rpow_nonneg (abs_nonneg _) α))
          _ = A3 * a₁ ^ 2 * |τ - τ'| ^ α := by ring
      have h2 : |deriv A τ' * ((A τ') ^ 2 - (A τ) ^ 2)|
          ≤ A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α := by
        rw [abs_mul]
        have hsq : |(A τ') ^ 2 - (A τ) ^ 2| ≤ 2 * a₁ * A2 * K' * |τ - τ'| ^ α := by
          have hfac : (A τ') ^ 2 - (A τ) ^ 2 = (A τ' - A τ) * (A τ' + A τ) := by ring
          rw [hfac, abs_mul]
          have hb1 : |A τ' - A τ| ≤ A2 * |τ - τ'| := by
            rw [abs_sub_comm]
            exact le_trans (hAlip τ hτ τ' hτ')
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
          have hb2 : |A τ' + A τ| ≤ 2 * a₁ := by
            have h1 := (hAb τ hτ).2
            have h2 := (hAb τ' hτ').2
            rw [abs_le]
            constructor <;> linarith
          calc |A τ' - A τ| * |A τ' + A τ| ≤ (A2 * |τ - τ'|) * (2 * a₁) :=
                mul_le_mul hb1 hb2 (abs_nonneg _) (mul_nonneg hA20 (abs_nonneg _))
            _ = 2 * a₁ * A2 * |τ - τ'| := by ring
            _ ≤ 2 * a₁ * A2 * (K' * |τ - τ'| ^ α) :=
                mul_le_mul_of_nonneg_left (hK1 τ hτ τ' hτ') (by positivity)
            _ = 2 * a₁ * A2 * K' * |τ - τ'| ^ α := by ring
        calc |deriv A τ'| * |(A τ') ^ 2 - (A τ) ^ 2|
            ≤ A2 * (2 * a₁ * A2 * K' * |τ - τ'| ^ α) :=
              mul_le_mul (hA2 τ' hτ') hsq (abs_nonneg _) hA20
          _ = A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α := by ring
      exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    have hkey : deriv A τ / (A τ) ^ 2 - deriv A τ' / (A τ') ^ 2
        = (deriv A τ * (A τ') ^ 2 - deriv A τ' * (A τ) ^ 2)
            / ((A τ) ^ 2 * (A τ') ^ 2) := by
      field_simp
    rw [hkey, abs_div, abs_of_pos (by positivity : 0 < (A τ) ^ 2 * (A τ') ^ 2)]
    have hden : a₀ ^ 4 ≤ (A τ) ^ 2 * (A τ') ^ 2 := by
      have h1 := (hAb τ hτ).1
      have h2 := (hAb τ' hτ').1
      nlinarith [mul_le_mul h1 h2 ha₀.le hAτ.le]
    have hP0 : 0 ≤ A3 * a₁ ^ 2 * |τ - τ'| ^ α + A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α := by
      positivity
    calc |deriv A τ * (A τ') ^ 2 - deriv A τ' * (A τ) ^ 2|
            / ((A τ) ^ 2 * (A τ') ^ 2)
        ≤ (A3 * a₁ ^ 2 * |τ - τ'| ^ α + A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α)
            / ((A τ) ^ 2 * (A τ') ^ 2) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (A3 * a₁ ^ 2 * |τ - τ'| ^ α + A2 * (2 * a₁ * A2) * K' * |τ - τ'| ^ α) / a₀ ^ 4 :=
          div_le_div_of_nonneg_left hP0 (by positivity) hden
      _ = ((A3 * a₁ ^ 2 + A2 * (2 * a₁ * A2) * K') / a₀ ^ 4) * |τ - τ'| ^ α := by ring
      _ ≤ C * |τ - τ'| ^ α :=
          mul_le_mul_of_nonneg_right hterm2 (Real.rpow_nonneg (abs_nonneg _) α)
  · intro τ hτ τ' hτ'
    have hBτ : 0 < B τ := h.hB τ hτ
    have hBτ' : 0 < B τ' := h.hB τ' hτ'
    have hnum : |(deriv B τ - deriv B τ') * B τ' + deriv B τ' * (B τ' - B τ)|
        ≤ B3 * b₁ * |τ - τ'| ^ α + B2 * Kb * K' * |τ - τ'| ^ α := by
      have h1 : |(deriv B τ - deriv B τ') * B τ'| ≤ B3 * b₁ * |τ - τ'| ^ α := by
        rw [abs_mul, abs_of_pos hBτ']
        calc |deriv B τ - deriv B τ'| * B τ' ≤ (B3 * |τ - τ'| ^ α) * b₁ :=
              mul_le_mul (hB3 τ hτ τ' hτ') (hBb τ' hτ').2 (le_of_lt hBτ')
                (mul_nonneg hB30 (Real.rpow_nonneg (abs_nonneg _) α))
          _ = B3 * b₁ * |τ - τ'| ^ α := by ring
      have h2 : |deriv B τ' * (B τ' - B τ)| ≤ B2 * Kb * K' * |τ - τ'| ^ α := by
        rw [abs_mul]
        have hstep : |B τ' - B τ| ≤ Kb * K' * |τ - τ'| ^ α := by
          rw [abs_sub_comm]
          calc |B τ - B τ'| ≤ Kb * |τ - τ'| := hKb τ hτ τ' hτ'
            _ ≤ Kb * (K' * |τ - τ'| ^ α) :=
                mul_le_mul_of_nonneg_left (hK1 τ hτ τ' hτ') hKb0
            _ = Kb * K' * |τ - τ'| ^ α := by ring
        calc |deriv B τ'| * |B τ' - B τ| ≤ B2 * (Kb * K' * |τ - τ'| ^ α) :=
              mul_le_mul (hB2 τ' hτ') hstep (abs_nonneg _) hB20
          _ = B2 * Kb * K' * |τ - τ'| ^ α := by ring
      exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    have hkey : deriv B τ / B τ - deriv B τ' / B τ'
        = ((deriv B τ - deriv B τ') * B τ' + deriv B τ' * (B τ' - B τ))
            / (B τ * B τ') := by
      field_simp
      ring
    rw [hkey, abs_div, abs_of_pos (mul_pos hBτ hBτ')]
    have hden : b₀ ^ 2 ≤ B τ * B τ' := by
      have h1 := (hBb τ hτ).1
      have h2 := (hBb τ' hτ').1
      nlinarith [mul_le_mul h1 h2 hb₀.le hBτ.le]
    have hP0 : 0 ≤ B3 * b₁ * |τ - τ'| ^ α + B2 * Kb * K' * |τ - τ'| ^ α := by positivity
    calc |(deriv B τ - deriv B τ') * B τ' + deriv B τ' * (B τ' - B τ)| / (B τ * B τ')
        ≤ (B3 * b₁ * |τ - τ'| ^ α + B2 * Kb * K' * |τ - τ'| ^ α) / (B τ * B τ') :=
          div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hBτ hBτ'))
      _ ≤ (B3 * b₁ * |τ - τ'| ^ α + B2 * Kb * K' * |τ - τ'| ^ α) / b₀ ^ 2 :=
          div_le_div_of_nonneg_left hP0 (by positivity) hden
      _ = ((B3 * b₁ + B2 * Kb * K') / b₀ ^ 2) * |τ - τ'| ^ α := by ring
      _ ≤ C * |τ - τ'| ^ α :=
          mul_le_mul_of_nonneg_right hterm3 (Real.rpow_nonneg (abs_nonneg _) α)

theorem pvb_vortDt_holder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ x : R3, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      ‖vortDt α A B g x τ - vortDt α A B g x τ'‖ ≤ N * |τ - τ'| ^ α := by
  obtain ⟨a₀, a₁, ha₀, hAb⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hBb⟩ := h.hBb
  obtain ⟨Kb, hKb0, hKb⟩ := clockLipschitz h
  obtain ⟨CA, hCA0, hAic, hAhc, hBhc⟩ := pvb_clockData h
  obtain ⟨MA, hMA0, hMA⟩ := clockBounds h
  obtain ⟨Np, hNp0, hNph⟩ := profFullHolder h
  obtain ⟨Mp, hMp0, hMp⟩ := profFullBounds h
  obtain ⟨Nd, hNd⟩ := h.hgdoth
  obtain ⟨L₀, hL₀pos, hL₀supp⟩ := h.hsupp
  obtain ⟨Lτ, hLτpos, hLτ⟩ := dtgZero h
  obtain ⟨Lz, hLzpos, hLz⟩ := dzProfFullZero h
  have hb₁0 : 0 < b₁ := by
    have h0 : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, h.hS.le⟩
    linarith [(hBb 0 h0).1, (hBb 0 h0).2]
  set Lb : ℝ := max L₀ (max Lτ Lz) + 1 with hLbdef
  have hLb_gt₀ : L₀ < Lb := by
    rw [hLbdef]
    have h1 : L₀ ≤ max L₀ (max Lτ Lz) := le_max_left _ _
    linarith
  have hLb_gtτ : Lτ < Lb := by
    rw [hLbdef]
    have h1 : Lτ ≤ max Lτ Lz := le_max_left _ _
    have h2 : max Lτ Lz ≤ max L₀ (max Lτ Lz) := le_max_right _ _
    linarith
  have hLb_gtz : Lz < Lb := by
    rw [hLbdef]
    have h1 : Lz ≤ max Lτ Lz := le_max_right _ _
    have h2 : max Lτ Lz ≤ max L₀ (max Lτ Lz) := le_max_right _ _
    linarith
  have hLb0 : 0 < Lb := lt_trans hL₀pos hLb_gt₀
  set κ : ℝ := Lb * b₁ * Kb / b₀ ^ 2 with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    exact div_nonneg (mul_nonneg (mul_nonneg hLb0.le hb₁0.le) hKb0) (by positivity)
  set Rz : ℝ := Lb * b₁ / b₀ with hRzdef
  have hRz0 : 0 ≤ Rz := by
    rw [hRzdef]
    exact div_nonneg (mul_nonneg hLb0.le hb₁0.le) hb₀.le
  obtain ⟨hsplitR, ⟨M1, hM10, hM1⟩, ⟨N1, hN10, hN1⟩⟩ := dzProfFullUniform h Rz hRz0
  set Ka : ℝ := S ^ (1 - α) with hKadef
  have hKa0 : 0 ≤ Ka := by rw [hKadef]; exact Real.rpow_nonneg h.hS.le _
  set κa : ℝ := κ * Ka with hκadef
  have hκa0 : 0 ≤ κa := by rw [hκadef]; positivity
  set Kz : ℝ := (κ + 1) ^ α with hKzdef
  have hKz0 : 0 ≤ Kz := by rw [hKzdef]; exact Real.rpow_nonneg (by linarith) _
  have hNd0 : 0 ≤ Nd := hNd.1
  set ND : ℝ := Rz * M1 * CA + MA * (Rz * N1 * Kz + M1 * κa) + Nd * Kz with hNDdef
  set MD : ℝ := Rz * M1 * MA + Nd with hMDdef
  set NP : ℝ := Np * Kz with hNPdef
  set NN : ℝ := MA * ND + CA * MD + MA * NP + CA * Mp with hNNdef
  have hND0 : 0 ≤ ND := by
    rw [hNDdef]
    have h1 : 0 ≤ Rz * M1 * CA := by positivity
    have h2 : 0 ≤ MA * (Rz * N1 * Kz + M1 * κa) := by positivity
    have h3 : 0 ≤ Nd * Kz := by positivity
    linarith
  have hMD0 : 0 ≤ MD := by
    rw [hMDdef]
    have h1 : 0 ≤ Rz * M1 * MA := by positivity
    linarith
  have hNP0 : 0 ≤ NP := by rw [hNPdef]; positivity
  have hNN0 : 0 ≤ NN := by
    rw [hNNdef]
    have h1 : 0 ≤ MA * ND := by positivity
    have h2 : 0 ≤ CA * MD := by positivity
    have h3 : 0 ≤ MA * NP := by positivity
    have h4 : 0 ≤ CA * Mp := by positivity
    linarith
  refine ⟨NN, hNN0, ?_⟩
  intro x τ hτ τ' hτ'
  set ρ : ℝ := Work.Cyl.rho x with hρdef
  set θ : ℝ := Work.Cyl.theta x with hθdef
  set e : R3 := Work.Cyl.eTheta x with hedef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact Work.Cyl.rho_nonneg x
  have hφI : |θ| ∈ Work.Spaces.Iθ := by rw [hθdef]; exact abs_theta_mem_Iθ x
  have he1 : ‖e‖ ≤ 1 := by rw [hedef]; exact norm_eTheta_le_one x
  have hvort : ∀ s : ℝ, vortDt α A B g x s
      = (A s)⁻¹ • (dProfOdd α B g ρ θ s • e)
        + (-(deriv A s) / (A s) ^ 2) • (profOdd α g (ρ ^ pExp α / B s) θ s • e) := by
    intro s
    rw [vortDt]
  rw [hvort τ, hvort τ']
  by_cases hfar : Lb * b₁ < ρ ^ pExp α
  · -- FAR: outside the support everything vanishes
    have hZnn : ∀ s ∈ Set.Icc 0 S, 0 ≤ ρ ^ pExp α / B s :=
      fun s hs => div_nonneg (Real.rpow_nonneg hρ0 _) (h.hB s hs).le
    have hZfar : ∀ s ∈ Set.Icc 0 S, Lb ≤ ρ ^ pExp α / B s := by
      intro s hs
      have hBs : 0 < B s := h.hB s hs
      rw [le_div_iff₀ hBs]
      calc Lb * B s ≤ Lb * b₁ := mul_le_mul_of_nonneg_left (hBb s hs).2 hLb0.le
        _ ≤ ρ ^ pExp α := hfar.le
    have hD0 : ∀ s ∈ Set.Icc 0 S, dProfOdd α B g ρ θ s = 0 := by
      intro s hs
      have hpz0 : pzProf α g (ρ ^ pExp α / B s) |θ| s = 0 := by
        rw [pvb_pzProf_eq_deriv h (hZnn s hs) hφI hs]
        exact hLz _ |θ| s (lt_of_lt_of_le hLb_gtz (hZfar s hs)) hφI hs
      have hw0 : deriv (fun t => g (ρ ^ pExp α / B s) |θ| t) s = 0 :=
        hLτ _ |θ| s (lt_of_lt_of_le hLb_gtτ (hZfar s hs)) hφI hs
      rw [pvb_dProfOdd_eq (α := α) (B := B) (g := g) (ρ := ρ) (θ := θ) (τ := s)
        (ne_of_gt (h.hB s hs)), hpz0, hw0]
      ring
    have hP0 : ∀ s ∈ Set.Icc 0 S, profOdd α g (ρ ^ pExp α / B s) θ s = 0 := by
      intro s hs
      exact pvb_profOdd_eq_zero (hL₀supp s hs _ _ (le_trans hLb_gt₀.le (hZfar s hs)))
    rw [hD0 τ hτ, hP0 τ hτ, hD0 τ' hτ', hP0 τ' hτ']
    simp only [zero_smul, smul_zero, add_zero, sub_self, norm_zero]
    exact mul_nonneg hNN0 (Real.rpow_nonneg (abs_nonneg _) α)
  · -- NEAR: inside the support radius
    have hρp : ρ ^ pExp α ≤ Lb * b₁ := not_lt.mp hfar
    have hZnn : ∀ s ∈ Set.Icc 0 S, 0 ≤ ρ ^ pExp α / B s :=
      fun s hs => div_nonneg (Real.rpow_nonneg hρ0 _) (h.hB s hs).le
    have hZR : ∀ s ∈ Set.Icc 0 S, ρ ^ pExp α / B s ≤ Rz := by
      intro s hs
      have hBs : 0 < B s := h.hB s hs
      rw [hRzdef, div_le_iff₀ hBs]
      calc ρ ^ pExp α ≤ Lb * b₁ := hρp
        _ = Lb * b₁ / b₀ * b₀ := by field_simp
        _ ≤ Lb * b₁ / b₀ * B s := mul_le_mul_of_nonneg_left (hBb s hs).1 (by positivity)
    have hZlip : |ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| ≤ κ * |τ - τ'| := by
      have hBτ : 0 < B τ := h.hB τ hτ
      have hBτ' : 0 < B τ' := h.hB τ' hτ'
      have hkey : ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'
          = ρ ^ pExp α * ((B τ' - B τ) / (B τ * B τ')) := by
        field_simp
      have hnum : |B τ' - B τ| ≤ Kb * |τ - τ'| := by
        rw [abs_sub_comm]; exact hKb τ hτ τ' hτ'
      have hden : b₀ ^ 2 ≤ B τ * B τ' := by
        have h1 := (hBb τ hτ).1
        have h2 := (hBb τ' hτ').1
        nlinarith [mul_le_mul h1 h2 hb₀.le hBτ.le]
      rw [hkey, abs_mul, abs_of_nonneg (Real.rpow_nonneg hρ0 _), abs_div,
        abs_of_pos (mul_pos hBτ hBτ')]
      have hstep : |B τ' - B τ| / (B τ * B τ') ≤ (Kb / b₀ ^ 2) * |τ - τ'| := by
        calc |B τ' - B τ| / (B τ * B τ') ≤ Kb * |τ - τ'| / (B τ * B τ') :=
              div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hBτ hBτ'))
          _ ≤ Kb * |τ - τ'| / b₀ ^ 2 :=
              div_le_div_of_nonneg_left (mul_nonneg hKb0 (abs_nonneg _)) (by positivity) hden
          _ = (Kb / b₀ ^ 2) * |τ - τ'| := by ring
      calc ρ ^ pExp α * (|B τ' - B τ| / (B τ * B τ'))
          ≤ ρ ^ pExp α * ((Kb / b₀ ^ 2) * |τ - τ'|) :=
            mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hρ0 _)
        _ ≤ (Lb * b₁) * ((Kb / b₀ ^ 2) * |τ - τ'|) :=
            mul_le_mul_of_nonneg_right hρp (by positivity)
        _ = κ * |τ - τ'| := by rw [hκdef]; ring
    have hKa1 : |τ - τ'| ≤ Ka * |τ - τ'| ^ α := by
      have h1 : |τ - τ'| ≤ S := by
        rw [abs_sub_le_iff]
        constructor <;> linarith [hτ.1, hτ.2, hτ'.1, hτ'.2]
      exact pvb_self_le_rpow (abs_nonneg _) h1 h.hα (le_trans h.hα13 (by norm_num))
    have hra : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a ≤ κ * |τ - τ'| → b ≤ |τ - τ'| →
        (a + b) ^ α ≤ Kz * |τ - τ'| ^ α := by
      intro a b ha hb ha' hb'
      have hd : 0 ≤ |τ - τ'| := abs_nonneg _
      have h1 : a + b ≤ (κ + 1) * |τ - τ'| := by nlinarith
      have h2 : 0 ≤ a + b := by linarith
      have hK1 : 0 ≤ κ + 1 := by linarith
      have h4 : ((κ + 1) * |τ - τ'|) ^ α = (κ + 1) ^ α * |τ - τ'| ^ α :=
        Real.mul_rpow hK1 hd
      calc (a + b) ^ α ≤ ((κ + 1) * |τ - τ'|) ^ α := Real.rpow_le_rpow h2 h1 h.hα.le
        _ = (κ + 1) ^ α * |τ - τ'| ^ α := h4
        _ = Kz * |τ - τ'| ^ α := by rw [hKzdef]
    -- the profile part
    have hPh : |profOdd α g (ρ ^ pExp α / B τ) θ τ - profOdd α g (ρ ^ pExp α / B τ') θ τ'|
        ≤ NP * |τ - τ'| ^ α := by
      rw [pvb_profOdd_sub]
      have h1 := hNph (ρ ^ pExp α / B τ) (ρ ^ pExp α / B τ') |θ| τ τ'
        (hZnn τ hτ) (hZnn τ' hτ') hφI hτ hτ'
      have h2 : (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α
          ≤ Kz * |τ - τ'| ^ α := hra (abs_nonneg _) (abs_nonneg _) hZlip le_rfl
      calc |profFull α g (ρ ^ pExp α / B τ) |θ| τ - profFull α g (ρ ^ pExp α / B τ') |θ| τ'|
          ≤ Np * (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α := h1
        _ ≤ Np * (Kz * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left h2 hNp0
        _ = NP * |τ - τ'| ^ α := by rw [hNPdef]; ring
    have hPb : |profOdd α g (ρ ^ pExp α / B τ') θ τ'| ≤ Mp := by
      rw [pvb_profOdd_abs_eq]
      exact hMp τ' hτ' _ _ (hZnn τ' hτ') hφI
    -- the `z`-derivative of the profile
    have hpzh : |pzProf α g (ρ ^ pExp α / B τ) |θ| τ
        - pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ N1 * Kz * |τ - τ'| ^ α := by
      rw [pvb_pzProf_eq_deriv h (hZnn τ hτ) hφI hτ,
        pvb_pzProf_eq_deriv h (hZnn τ' hτ') hφI hτ']
      have h1 := hN1 (ρ ^ pExp α / B τ) (ρ ^ pExp α / B τ') |θ| τ τ'
        (hZnn τ hτ) (hZR τ hτ) (hZnn τ' hτ') (hZR τ' hτ') hφI hτ hτ'
      have h2 : (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α
          ≤ Kz * |τ - τ'| ^ α := hra (abs_nonneg _) (abs_nonneg _) hZlip le_rfl
      calc |deriv (fun z' => profFull α g z' |θ| τ) (ρ ^ pExp α / B τ)
            - deriv (fun z' => profFull α g z' |θ| τ') (ρ ^ pExp α / B τ')|
          ≤ N1 * (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α := h1
        _ ≤ N1 * (Kz * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left h2 hN10
        _ = N1 * Kz * |τ - τ'| ^ α := by ring
    have hpzb : |pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ M1 := by
      rw [pvb_pzProf_eq_deriv h (hZnn τ' hτ') hφI hτ']
      exact hM1 (ρ ^ pExp α / B τ') |θ| τ' (hZnn τ' hτ') (hZR τ' hτ') hφI hτ'
    have hpzbτ : |pzProf α g (ρ ^ pExp α / B τ) |θ| τ| ≤ M1 := by
      rw [pvb_pzProf_eq_deriv h (hZnn τ hτ) hφI hτ]
      exact hM1 (ρ ^ pExp α / B τ) |θ| τ (hZnn τ hτ) (hZR τ hτ) hφI hτ
    -- `U = Z · ∂_zF`
    have hUb : |(ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ Rz * M1 := by
      rw [abs_mul, abs_of_nonneg (hZnn τ' hτ')]
      exact mul_le_mul (hZR τ' hτ') hpzb (abs_nonneg _) hRz0
    have hUbτ : |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ| ≤ Rz * M1 := by
      rw [abs_mul, abs_of_nonneg (hZnn τ hτ)]
      exact mul_le_mul (hZR τ hτ) hpzbτ (abs_nonneg _) hRz0
    have hUh : |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
        - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'|
        ≤ (Rz * N1 * Kz + M1 * κa) * |τ - τ'| ^ α := by
      have hsplit : (ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
          - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'
          = (ρ ^ pExp α / B τ) * (pzProf α g (ρ ^ pExp α / B τ) |θ| τ
              - pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
            + (ρ ^ pExp α / B τ - ρ ^ pExp α / B τ')
              * pzProf α g (ρ ^ pExp α / B τ') |θ| τ' := by ring
      rw [hsplit]
      have h1 : |(ρ ^ pExp α / B τ) * (pzProf α g (ρ ^ pExp α / B τ) |θ| τ
            - pzProf α g (ρ ^ pExp α / B τ') |θ| τ')| ≤ Rz * (N1 * Kz * |τ - τ'| ^ α) := by
        rw [abs_mul, abs_of_nonneg (hZnn τ hτ)]
        exact mul_le_mul (hZR τ hτ) hpzh (abs_nonneg _) hRz0
      have h2 : |(ρ ^ pExp α / B τ - ρ ^ pExp α / B τ')
            * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ (κa * M1) * |τ - τ'| ^ α := by
        rw [abs_mul]
        have hb : |ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'|
            * |pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ (κ * |τ - τ'|) * M1 :=
          mul_le_mul hZlip hpzb (abs_nonneg _) (mul_nonneg hκ0 (abs_nonneg _))
        calc |ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'|
              * |pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ (κ * |τ - τ'|) * M1 := hb
          _ = (κ * M1) * |τ - τ'| := by ring
          _ ≤ (κ * M1) * (Ka * |τ - τ'| ^ α) :=
              mul_le_mul_of_nonneg_left hKa1 (mul_nonneg hκ0 hM10)
          _ = (κa * M1) * |τ - τ'| ^ α := by rw [hκadef]; ring
      calc |(ρ ^ pExp α / B τ) * (pzProf α g (ρ ^ pExp α / B τ) |θ| τ
              - pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
            + (ρ ^ pExp α / B τ - ρ ^ pExp α / B τ')
              * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'|
          ≤ |(ρ ^ pExp α / B τ) * (pzProf α g (ρ ^ pExp α / B τ) |θ| τ
              - pzProf α g (ρ ^ pExp α / B τ') |θ| τ')|
            + |(ρ ^ pExp α / B τ - ρ ^ pExp α / B τ')
              * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| := abs_add_le _ _
        _ ≤ Rz * (N1 * Kz * |τ - τ'| ^ α) + (κa * M1) * |τ - τ'| ^ α := add_le_add h1 h2
        _ = (Rz * N1 * Kz + M1 * κa) * |τ - τ'| ^ α := by ring
    -- `W = ∂_τ g`
    have hWh : |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
        - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| ≤ Nd * Kz * |τ - τ'| ^ α := by
      have h1 := hNd.2.2 (ρ ^ pExp α / B τ) (ρ ^ pExp α / B τ') |θ| |θ| τ τ'
        (hZnn τ hτ) (hZnn τ' hτ') hφI hφI hτ hτ'
      have h1' : |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
          - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'|
          ≤ Nd * (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α := by
        simpa only [sub_self, abs_zero, add_zero] using h1
      have h2 : (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α
          ≤ Kz * |τ - τ'| ^ α := hra (abs_nonneg _) (abs_nonneg _) hZlip le_rfl
      calc |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
            - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'|
          ≤ Nd * (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α := h1'
        _ ≤ Nd * (Kz * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left h2 hNd0
        _ = Nd * Kz * |τ - τ'| ^ α := by ring
    have hWb : |deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| ≤ Nd :=
      hNd.abs_le (hZnn τ' hτ') hφI hτ'
    -- the clock factors
    have hVb : |deriv B τ' / B τ'| ≤ MA := (hMA τ' hτ').2.2.2
    have hVh : |deriv B τ / B τ - deriv B τ' / B τ'| ≤ CA * |τ - τ'| ^ α := hBhc τ hτ τ' hτ'
    -- the assembled derivative `D`
    have hDh : |dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ'| ≤ ND * |τ - τ'| ^ α := by
      rw [pvb_dProfOdd_eq (α := α) (B := B) (g := g) (ρ := ρ) (θ := θ) (τ := τ)
            (ne_of_gt (h.hB τ hτ)),
          pvb_dProfOdd_eq (α := α) (B := B) (g := g) (ρ := ρ) (θ := θ) (τ := τ')
            (ne_of_gt (h.hB τ' hτ'))]
      have hs1 : |(if 0 ≤ θ then (1 : ℝ) else -1)| = 1 := by split_ifs <;> norm_num
      rw [← mul_sub, abs_mul, hs1, one_mul]
      have hsplit : (-((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
              * (deriv B τ / B τ) + deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ)
          - (-((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
              * (deriv B τ' / B τ') + deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ')
          = -(((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ)
              - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
                * (deriv B τ' / B τ'))
            + (deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
              - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ') := by ring
      rw [hsplit]
      have hUV : |((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
            * (deriv B τ / B τ)
          - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
            * (deriv B τ' / B τ')| ≤ (Rz * M1 * CA + MA * (Rz * N1 * Kz + M1 * κa))
              * |τ - τ'| ^ α := by
        have hsp : ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
              * (deriv B τ / B τ)
            - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
              * (deriv B τ' / B τ')
            = ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ - deriv B τ' / B τ')
              + (deriv B τ' / B τ')
                * ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
                  - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ') := by ring
        rw [hsp]
        have h1 : |((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
              * (deriv B τ / B τ - deriv B τ' / B τ')|
            ≤ (Rz * M1) * (CA * |τ - τ'| ^ α) := by
          rw [abs_mul]
          exact mul_le_mul hUbτ hVh (abs_nonneg _) (mul_nonneg hRz0 hM10)
        have h2 : |(deriv B τ' / B τ')
              * ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
                - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')|
            ≤ MA * ((Rz * N1 * Kz + M1 * κa) * |τ - τ'| ^ α) := by
          rw [abs_mul]
          exact mul_le_mul hVb hUh (abs_nonneg _) hMA0
        calc |((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ - deriv B τ' / B τ')
              + (deriv B τ' / B τ')
                * ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
                  - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')|
            ≤ (Rz * M1) * (CA * |τ - τ'| ^ α)
              + MA * ((Rz * N1 * Kz + M1 * κa) * |τ - τ'| ^ α) :=
              le_trans (abs_add_le _ _) (add_le_add h1 h2)
          _ = (Rz * M1 * CA + MA * (Rz * N1 * Kz + M1 * κa)) * |τ - τ'| ^ α := by ring
      calc |-(((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ)
              - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
                * (deriv B τ' / B τ'))
            + (deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
              - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ')|
          ≤ |-(((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ)
              - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
                * (deriv B τ' / B τ'))|
            + |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
              - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| := abs_add_le _ _
        _ = |((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ)
              - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
                * (deriv B τ' / B τ')|
            + |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
              - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| := by rw [abs_neg]
        _ ≤ (Rz * M1 * CA + MA * (Rz * N1 * Kz + M1 * κa)) * |τ - τ'| ^ α
            + Nd * Kz * |τ - τ'| ^ α := add_le_add hUV hWh
        _ = ND * |τ - τ'| ^ α := by rw [hNDdef]; ring
    have hDb : |dProfOdd α B g ρ θ τ'| ≤ MD := by
      rw [pvb_dProfOdd_eq (α := α) (B := B) (g := g) (ρ := ρ) (θ := θ) (τ := τ')
        (ne_of_gt (h.hB τ' hτ'))]
      have hs1 : |(if 0 ≤ θ then (1 : ℝ) else -1)| = 1 := by split_ifs <;> norm_num
      rw [abs_mul, hs1, one_mul]
      have hstep : |-((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
              * (deriv B τ' / B τ') + deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'|
          ≤ |(ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'|
              * |deriv B τ' / B τ'|
            + |deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_neg]
      calc |-((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
              * (deriv B τ' / B τ') + deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'|
          ≤ |(ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'|
              * |deriv B τ' / B τ'|
            + |deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| := hstep
        _ ≤ Rz * M1 * MA + Nd :=
            add_le_add (mul_le_mul hUb hVb (abs_nonneg _) (mul_nonneg hRz0 hM10)) hWb
        _ = MD := by rw [hMDdef]
    -- the two groups of terms
    have hDterm : ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
        - (A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e)‖
        ≤ (MA * ND + CA * MD) * |τ - τ'| ^ α := by
      have hsplit : (A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
          - (A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e)
          = (A τ)⁻¹ • ((dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ') • e)
            + ((A τ)⁻¹ - (A τ')⁻¹) • (dProfOdd α B g ρ θ τ' • e) := by
        conv_rhs => rw [sub_smul, smul_sub, sub_smul]
        abel
      have ha1 : |(A τ)⁻¹| ≤ MA := (hMA τ hτ).1
      have ha2 : |(A τ)⁻¹ - (A τ')⁻¹| ≤ CA * |τ - τ'| ^ α := hAic τ hτ τ' hτ'
      calc ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
            - (A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e)‖
          = ‖(A τ)⁻¹ • ((dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ') • e)
              + ((A τ)⁻¹ - (A τ')⁻¹) • (dProfOdd α B g ρ θ τ' • e)‖ := by rw [hsplit]
        _ ≤ ‖(A τ)⁻¹ • ((dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ') • e)‖
              + ‖((A τ)⁻¹ - (A τ')⁻¹) • (dProfOdd α B g ρ θ τ' • e)‖ := norm_add_le _ _
        _ = |(A τ)⁻¹| * (|dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ'| * ‖e‖)
              + |(A τ)⁻¹ - (A τ')⁻¹| * (|dProfOdd α B g ρ θ τ'| * ‖e‖) := by
            simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ MA * (ND * |τ - τ'| ^ α * 1) + (CA * |τ - τ'| ^ α) * (MD * 1) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul ha1 (mul_le_mul hDh he1 (norm_nonneg _) (by positivity))
                (by positivity) hMA0
            · exact mul_le_mul ha2 (mul_le_mul hDb he1 (norm_nonneg _) (by positivity))
                (by positivity) (by positivity)
        _ = (MA * ND + CA * MD) * |τ - τ'| ^ α := by ring
    have hPterm : ‖(-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
        - (-(deriv A τ') / (A τ') ^ 2) • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)‖
        ≤ (MA * NP + CA * Mp) * |τ - τ'| ^ α := by
      have hsplit : (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
          - (-(deriv A τ') / (A τ') ^ 2) • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)
          = (-(deriv A τ) / (A τ) ^ 2)
              • ((profOdd α g (ρ ^ pExp α / B τ) θ τ
                  - profOdd α g (ρ ^ pExp α / B τ') θ τ') • e)
            + ((-(deriv A τ) / (A τ) ^ 2) - (-(deriv A τ') / (A τ') ^ 2))
              • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e) := by
        conv_rhs => rw [sub_smul, smul_sub, sub_smul]
        abel
      have hb1 : |-(deriv A τ) / (A τ) ^ 2| ≤ MA := by
        simpa only [abs_div, abs_neg, abs_of_nonneg (sq_nonneg (A τ))]
          using (hMA τ hτ).2.1
      have hb2 : |-(deriv A τ) / (A τ) ^ 2 - - (deriv A τ') / (A τ') ^ 2| ≤ CA * |τ - τ'| ^ α := by
        have := hAhc τ hτ τ' hτ'
        rwa [show -(deriv A τ) / (A τ) ^ 2 - -(deriv A τ') / (A τ') ^ 2
            = -(deriv A τ / (A τ) ^ 2 - deriv A τ' / (A τ') ^ 2) by ring, abs_neg]
      calc ‖(-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
            - (-(deriv A τ') / (A τ') ^ 2) • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)‖
          = ‖(-(deriv A τ) / (A τ) ^ 2)
                • ((profOdd α g (ρ ^ pExp α / B τ) θ τ
                    - profOdd α g (ρ ^ pExp α / B τ') θ τ') • e)
              + ((-(deriv A τ) / (A τ) ^ 2) - (-(deriv A τ') / (A τ') ^ 2))
                • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)‖ := by rw [hsplit]
        _ ≤ ‖(-(deriv A τ) / (A τ) ^ 2)
                • ((profOdd α g (ρ ^ pExp α / B τ) θ τ
                    - profOdd α g (ρ ^ pExp α / B τ') θ τ') • e)‖
              + ‖((-(deriv A τ) / (A τ) ^ 2) - (-(deriv A τ') / (A τ') ^ 2))
                • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)‖ := norm_add_le _ _
        _ = |-(deriv A τ) / (A τ) ^ 2|
              * (|profOdd α g (ρ ^ pExp α / B τ) θ τ
                  - profOdd α g (ρ ^ pExp α / B τ') θ τ'| * ‖e‖)
              + |(-(deriv A τ) / (A τ) ^ 2) - (-(deriv A τ') / (A τ') ^ 2)|
                * (|profOdd α g (ρ ^ pExp α / B τ') θ τ'| * ‖e‖) := by
            simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ MA * (NP * |τ - τ'| ^ α * 1) + (CA * |τ - τ'| ^ α) * (Mp * 1) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul hb1 (mul_le_mul hPh he1 (norm_nonneg _) (by positivity))
                (by positivity) hMA0
            · exact mul_le_mul hb2 (mul_le_mul hPb he1 (norm_nonneg _) (by positivity))
                (by positivity) (by positivity)
        _ = (MA * NP + CA * Mp) * |τ - τ'| ^ α := by ring
    calc ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
          + (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
          - ((A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e)
            + (-(deriv A τ') / (A τ') ^ 2) • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e))‖
        = ‖((A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
              - (A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e))
            + ((-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
              - (-(deriv A τ') / (A τ') ^ 2)
                • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e))‖ := by abel_nf
      _ ≤ (MA * ND + CA * MD) * |τ - τ'| ^ α + (MA * NP + CA * Mp) * |τ - τ'| ^ α :=
          le_trans (norm_add_le _ _) (add_le_add hDterm hPterm)
      _ = NN * |τ - τ'| ^ α := by rw [hNNdef]; ring

theorem pvb_timeDeriv_holder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ x : R3, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      ‖FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ
        - FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ'‖ ≤ N * |τ - τ'| ^ α := by
  obtain ⟨N, hN0, hN⟩ := pvb_vortDt_holder h
  refine ⟨N, hN0, fun x τ hτ τ' hτ' => ?_⟩
  rw [pvb_timeDeriv_eq_vortDt h x τ hτ, pvb_timeDeriv_eq_vortDt h x τ' hτ']
  exact hN x τ hτ τ' hτ'

/-! ## The bundle -/

/-- **THE PHYSICAL VORTICITY OF A `RegPkg` PROFILE IS STRIP-ADMISSIBLE (node N7).**  There is a
radius `R > 0` (bounding the support of `ω(·,τ)` uniformly on the strip) such that the physical
vorticity `ω = physVort α A B g` satisfies the full hypothesis bundle
`BSAdmissibleStripFull α ω R S` of the space–time Schauder estimate. -/
theorem physVort_bundle {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.RegPkg α S A B g) :
    ∃ R : ℝ, 0 < R ∧
      Work.CoreResiduals.BSAdmissibleStripFull (⟨α, h.hα.le⟩ : NNReal)
        (Work.FTS.Regularity.physVort α A B g) R S := by
  obtain ⟨R, hR0, hsupp⟩ := physVort_support h
  obtain ⟨M, _hM0, hMb⟩ := physVort_bound h
  obtain ⟨H, hH⟩ := physVort_slice_holder h
  obtain ⟨N, _hN0, hNt⟩ := physVort_holder_time h
  obtain ⟨hderiv, M₁, _hM₁0, hM₁⟩ := physVort_hasDerivAt_and_bound h
  obtain ⟨Nd, _hNd0, hNd⟩ := pvb_timeDeriv_holder h
  refine ⟨R, hR0, ⟨?_, ?_, ?_⟩⟩
  · -- `BSAdmissibleStrip`
    refine ⟨hR0, hsupp, ⟨M, fun τ hτ y => hMb τ hτ y⟩, ⟨H, ?_⟩,
      ⟨N, fun y τ hτ τ' hτ' => hNt y τ hτ τ' hτ'⟩, ?_⟩
    · intro τ hτ
      exact hH τ hτ
    · intro τ hτ
      exact physVort_slice_aesm h τ hτ
  · -- `TimeDerivStrip`
    refine ⟨fun τ hτ y => hderiv y τ hτ, ⟨M₁, fun τ hτ y => hM₁ τ hτ y⟩, ?_⟩
    intro τ hτ
    exact physVort_timeDeriv_aesm h τ hτ
  · -- `TimeDerivStripHolder`
    exact ⟨Nd, fun y τ hτ τ' hτ' => hNd y τ hτ τ' hτ'⟩

end Work.FTS.Regularity
