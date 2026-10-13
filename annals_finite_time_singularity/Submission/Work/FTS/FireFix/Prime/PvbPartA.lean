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
import Submission.Work.FTS.FireFix.Prime.physVort_support
import Submission.Work.FTS.FireFix.Prime.physVort_bound
import Submission.Work.FTS.FireFix.Prime.PhysVortHolderSlice
import Submission.Work.FTS.FireFix.Prime.physVort_holder_time
import Submission.Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound
import Submission.Work.FTS.FireFix.Prime.physVort_timeDeriv_aesm
import Submission.Work.FTS.FireFix.Prime.profFullHolder
import Submission.Work.FTS.FireFix.Prime.profFullBounds
import Submission.Work.FTS.FireFix.Prime.dzProfFullUniform
import Submission.Work.FTS.FireFix.Prime.dzProfFullZero
import Submission.Work.FTS.FireFix.Prime.dtgZero
import Submission.Work.FTS.FireFix.Prime.clockBounds
import Submission.Work.FTS.FireFix.Prime.clockLipschitz
import Submission.Work.FTS.RegPkgGal.Basic

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

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal








/-! ## The two clauses of `BSAdmissibleStrip` that are not literal copies of a sibling -/

/-- **The slicewise `HolderWith` form of `physVort_holder_slice`**, in the exponent and constant
type of the admissibility bundle (`NNReal`). -/
theorem physVort_slice_holder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
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
    (h : RegPkg' α S A B g) :
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
    (h : RegPkg' α S A B g) :
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


end Work.FTS.FireFix.Prime