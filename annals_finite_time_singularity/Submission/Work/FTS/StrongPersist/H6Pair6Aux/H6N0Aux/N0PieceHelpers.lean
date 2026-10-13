/-
# `N0PieceHelpers` — the elementary helpers of `hkmem_N0pieces`

Split off from `hkmem_N0pieces.lean` (file-size limit): the elementary tools

* `nzZop_iter_const_mul` — `Zop` commutes with constants,
* `nzc2m_eq_qfun` — `c₂ₘ = (3/2)·qfun`,
* `nzsmoothOpen_ang`, `nzsmoothOpen_sep` — `SmoothOpen` of angular and separable profiles,
* `nzcontDiffOn_qfun`, `nzcontDiffOn_c2m`, `nzsmoothOn_FMFstar`, `nzsmoothOn_Hz` — the
  smoothness of the angular profiles and of the two radial factors of the `F_*`-pieces,
* `nzradZop_bound6` — the `Zop`-iterates of `2z/(1+z)²` and `2z(1-z)/(1+z)³` are bounded,
* `nzhkmem6_of_majorant7` — the majorant criterion at level six,
* `nzN04a_sep`, `nzN05a_sep` — the separability identities for the two `F_*`-pieces,
* `nzsmoothOpen_l12Fstar`, `nzl12Fstar_zop` — smoothness and `Zop`-bounds of `L₁₂(F_*)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.L6Aux.PhiZopBound6
import Submission.Work.FTS.StrongPersist.QangAe6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.PhiStar.Psi0Defs
import Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound
import Submission.Work.FM.Core
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- `Zop` commutes with multiplication by a constant. -/
lemma nzZop_iter_const_mul (c : ℝ) (u : ℝ → ℝ) (b : ℕ) :
    Work.Spaces.Zop^[b] (fun z => c * u z) = fun z => c * (Work.Spaces.Zop^[b] u) z := by
  have hgen : ∀ w : ℝ → ℝ,
      Work.Spaces.Zop (fun z => c * w z) = fun z => c * Work.Spaces.Zop w z := by
    intro w
    funext z
    simp only [Work.Spaces.Zop]
    rw [Work.Spaces.deriv_const_mul']
    ring
  induction b generalizing u with
  | zero => rfl
  | succ n ih =>
      calc Work.Spaces.Zop^[n + 1] (fun z => c * u z)
          = Work.Spaces.Zop (Work.Spaces.Zop^[n] (fun z => c * u z)) :=
            Function.iterate_succ_apply' Work.Spaces.Zop n (fun z => c * u z)
        _ = Work.Spaces.Zop (fun z => c * (Work.Spaces.Zop^[n] u) z) := by rw [ih u]
        _ = fun z => c * (Work.Spaces.Zop (Work.Spaces.Zop^[n] u)) z := hgen _
        _ = fun z => c * (Work.Spaces.Zop^[n + 1] u) z := by
              rw [← Function.iterate_succ_apply' Work.Spaces.Zop n u]

/-- `c₂ₘ θ = (3/2)·qfun θ`, where `qfun θ = cos 2θ - 1/3`. -/
lemma nzc2m_eq_qfun (θ : ℝ) :
    Work.Construction.c2m θ = (3 / 2) * Work.Spaces.qfun θ := by
  have h1 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  simp only [Work.Construction.c2m, Work.Spaces.qfun, Real.cos_two_mul]
  rw [h1]; ring

/-- `SmoothOpen` of an angular profile. -/
theorem nzsmoothOpen_ang {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (π / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 :=
    ha.comp contDiff_snd.contDiffOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hfun : Function.uncurry (fun _ (θ : ℝ) => a θ) = fun p : ℝ × ℝ => a p.2 := rfl
  rw [hfun]; exact h1

/-- `SmoothOpen` of a separable product. -/
theorem nzsmoothOpen_sep {Cfun Bfun : ℝ → ℝ}
    (hC : ContDiffOn ℝ Work.Stability.smoothOrder Cfun (Set.Ioo 0 (π / 2)))
    (hB : ContDiffOn ℝ Work.Stability.smoothOrder Bfun (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Cfun θ * Bfun z) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Cfun p.2)
      Work.FTS.EllipticEst.Q0 :=
    hC.comp contDiff_snd.contDiffOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Bfun p.1)
      Work.FTS.EllipticEst.Q0 :=
    hB.comp contDiff_fst.contDiffOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hfun : Function.uncurry (fun z θ => Cfun θ * Bfun z)
      = fun p : ℝ × ℝ => Cfun p.2 * Bfun p.1 := rfl
  rw [hfun]
  exact h1.mul h2

/-- The angular profile `qfun θ = cos 2θ - 1/3` is `C^∞` on the open interval. -/
theorem nzcontDiffOn_qfun :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Spaces.qfun θ)
      (Set.Ioo 0 (π / 2)) := by
  have h : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.cos (2 * θ) - 1 / 3) :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub contDiff_const
  exact h.contDiffOn.congr (fun θ _ => rfl)

/-- `c₂ₘ` is `C^∞` on the open interval. -/
theorem nzcontDiffOn_c2m :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Construction.c2m θ)
      (Set.Ioo 0 (π / 2)) := by
  have h : ContDiff ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2) :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub (Real.contDiff_sin.pow 2)
  exact h.contDiffOn.congr (fun θ _ => rfl)

/-- `F_*`'s radial profile `2z/(1+z)²` is `C^∞` on `(0,∞)`. -/
theorem nzsmoothOn_FMFstar :
    ContDiffOn ℝ Work.Stability.smoothOrder Work.FM.Fstar (Set.Ioi 0) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z / (1 + z) ^ 2)
      (Set.Ioi (-1 : ℝ)) := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z) (Set.Ioi (-1 : ℝ)) :=
      contDiffOn_const.mul contDiffOn_id
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2)
        (Set.Ioi (-1 : ℝ)) :=
      (contDiffOn_const.add contDiffOn_id).pow 2
    exact hnum.div hden (fun z hz => by
      simp only [Set.mem_Ioi] at hz
      have : (0 : ℝ) < 1 + z := by linarith
      positivity)
  refine (h.mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))).congr ?_
  intro z hz
  rfl

/-- The radial profile `H(z) = 2z(1-z)/(1+z)³` of `D_z F_*` is `C^∞` on `(0,∞)`. -/
theorem nzsmoothOn_Hz :
    ContDiffOn ℝ Work.Stability.smoothOrder Work.FTS.Nonlinear.FstarPkg.Hz (Set.Ioi 0) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3)
      (Set.Ioi (-1 : ℝ)) := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z * (1 - z))
        (Set.Ioi (-1 : ℝ)) :=
      (contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.sub contDiffOn_id)
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 3)
        (Set.Ioi (-1 : ℝ)) :=
      (contDiffOn_const.add contDiffOn_id).pow 3
    exact hnum.div hden (fun z hz => by
      simp only [Set.mem_Ioi] at hz
      have : (0 : ℝ) < 1 + z := by linarith
      positivity)
  refine (h.mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))).congr ?_
  intro z hz
  rfl

/-- The `Zop`-iterates of the two radial profiles of the `F_*`-pieces are bounded. -/
theorem nzradZop_bound6 : ∃ Kr : ℝ, 0 < Kr ∧
    (∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] Work.FM.Fstar z| ≤ Kr) ∧
    (∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ Kr) := by
  obtain ⟨K, hKnn, hK⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 7
  have hfun : Work.FM.Fstar = fun y : ℝ => 2 * (y / (1 + y) ^ 2) := by
    funext y
    simp only [Work.FM.Fstar]
    ring
  have hHz : ∀ y : ℝ, 0 < y → Work.FTS.Nonlinear.FstarPkg.Hz y
      = (Work.Spaces.Zop Work.FM.Fstar) y := by
    intro y hy
    rw [Work.Spaces.Zop, Work.FM.deriv_Fstar y (by linarith)]
    simp only [Work.FTS.Nonlinear.FstarPkg.Hz]
    ring
  refine ⟨2 * K + 1, by linarith, ?_, ?_⟩
  · intro b hb z hz
    rw [hfun, nzZop_iter_const_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := hK b (by omega) z hz
    linarith
  · intro b hb z hz
    have hcongr : Work.Elliptic.DzdIter b Work.FTS.Nonlinear.FstarPkg.Hz z
        = Work.Elliptic.DzdIter b (Work.Spaces.Zop Work.FM.Fstar) z :=
      Work.FTS.StrongPersist.DzdIter_congr_Ioi hHz b z hz
    have key1 : Work.Spaces.Zop^[b] Work.FTS.Nonlinear.FstarPkg.Hz z
        = Work.Spaces.Zop^[b] (Work.Spaces.Zop Work.FM.Fstar) z := by
      rw [Zop_iter_eq_DzdIter, Zop_iter_eq_DzdIter]
      exact hcongr
    rw [key1]
    rw [show Work.Spaces.Zop^[b] (Work.Spaces.Zop Work.FM.Fstar)
        = Work.Spaces.Zop^[b + 1] Work.FM.Fstar from
      (Function.iterate_succ_apply Work.Spaces.Zop b Work.FM.Fstar).symm]
    rw [hfun, nzZop_iter_const_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := hK (b + 1) (by omega) z hz
    linarith

/-- **The majorant criterion at level six**: a piece bounded by `c·HkIntegrand α 7 f` with
`c ≥ 0`, smooth on the open quadrant, is honest in `ℋ⁶`. -/
theorem nzhkmem6_of_majorant7 {α c : ℝ} {f u : ℝ → ℝ → ℝ}
    (hc : 0 ≤ c) (hu : Work.FTS.EllipticEst.SmoothOpen u) (hm7 : Work.Spaces.HkMem α 7 f)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 u z θ ≤ c * Work.Spaces.HkIntegrand α 7 f z θ) :
    Work.Spaces.HkMem α 6 u := by
  refine Work.FTS.LocData.HkMem_of_majorant α 6 (f := u)
    (M := fun z θ => c * Work.Spaces.HkIntegrand α 7 f z θ)
    (hu.continuousOn_HkIntegrand α 6) ?_ ?_ hle
  · intro z hz
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.smul_const (hm7.1 z hz) c) ?_ measurableSet_Icc
    intro θ hθ
    exact mul_comm _ _
  · refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.smul_const hm7.2 c) ?_ measurableSet_Ici
    intro z hz
    show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ) * c
        = ∫ θ in Work.Spaces.Iθ, c * Work.Spaces.HkIntegrand α 7 f z θ
    rw [MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
      (fun θ _ => mul_comm c (Work.Spaces.HkIntegrand α 7 f z θ))]
    exact (MeasureTheory.integral_mul_const c _).symm

/-- **The separability identity for `N₀₄ₐ`.** -/
lemma nzN04a_sep {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ} :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Construction.N04a α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ
        = (3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)
            * (Work.Construction.L12 f z * Work.FM.Fstar z) := by
  intro z θ hz hθ
  have hαne : α ≠ 0 := ne_of_gt hα
  have hcne : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
      = (α * Work.FM.Fstar z / Work.Spaces.c α) * deriv (fun t => Work.Spaces.Gam α t) θ := by
    simp only [Work.Spaces.pth, Work.Construction.Fstar]
    rw [show (fun θ' : ℝ => α * (Work.Spaces.Gam α θ' / Work.Spaces.c α) * Work.FM.Fstar z)
        = fun θ' : ℝ => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ' from by
      funext θ'; ring]
    rw [Work.Spaces.deriv_const_mul']
  have hdth : Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
    have h := Work.Spaces.dthU_Gam α θ hα hθ
    simpa only [Work.Spaces.dthU] using h
  simp only [Work.Construction.N04a, Work.Construction.s2]
  rw [hpth]
  rw [show (3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 f z
        * ((α * Work.FM.Fstar z / Work.Spaces.c α) * deriv (fun t => Work.Spaces.Gam α t) θ)
      = (3 / (2 * α)) * Work.Construction.L12 f z * (α * Work.FM.Fstar z / Work.Spaces.c α)
          * (Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ) from by ring]
  rw [hdth]
  field_simp
  try ring

/-- **The separability identity for `N₀₅ₐ`.** -/
lemma nzN05a_sep {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ} :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Construction.N05a α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ
        = (-(3 * α / (2 * Work.Spaces.c α))) * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)
            * (Work.Construction.L12 f z * Work.FTS.Nonlinear.FstarPkg.Hz z) := by
  intro z θ hz hθ
  have hαne : α ≠ 0 := ne_of_gt hα
  have hcne : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  rw [Work.Construction.N05a, Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith),
    nzc2m_eq_qfun]
  field_simp
  try ring

/-- `SmoothOpen` of the radial factor `z ↦ L₁₂(F_*)(z)`. -/
theorem nzsmoothOpen_l12Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  have h4 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * α / (1 + z))
      (Set.Ioi (-1 : ℝ)) := by
    have h5 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => α * (2 / (1 + z)))
        (Set.Ioi (-1 : ℝ)) :=
      contDiffOn_const.mul Work.FTS.StrongPersist.linMem_two_div_smooth
    refine h5.congr (fun z hz => ?_)
    ring
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * α / (1 + p.1)) Work.FTS.EllipticEst.Q0 :=
    h4.comp contDiff_fst.contDiffOn (fun p hp => by
      have hz : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      show p.1 ∈ Set.Ioi (-1 : ℝ)
      exact Set.mem_Ioi.mpr (by linarith))
  refine hbase.congr ?_
  intro p hp
  have hz : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  exact Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)

/-- The `Zop`-iterates of the radial factor `L₁₂(F_*)` are bounded by `PhiZopBound6`. -/
theorem nzl12Fstar_zop {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ Kφ : ℝ, 0 < Kφ ∧ ∀ b ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z|
        ≤ Kφ := by
  obtain ⟨K3, hK3pos, hK3⟩ := Work.FTS.StrongPersist.L6Aux.PhiZopBound6
  refine ⟨(2 * α / 3) * K3 + 1, by positivity, ?_⟩
  intro b hb z hz
  have hcongr : Work.Elliptic.DzdIter b
        (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z
      = Work.Elliptic.DzdIter b (fun y => 2 * α / (1 + y)) z :=
    Work.FTS.StrongPersist.DzdIter_congr_Ioi
      (fun y hy => Work.Construction.L12_Fstar_eq hα hα1 hy.le) b z hz
  have key1 : Work.Spaces.Zop^[b] (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z
      = Work.Spaces.Zop^[b] (fun y => 2 * α / (1 + y)) z := by
    rw [Zop_iter_eq_DzdIter, Zop_iter_eq_DzdIter]
    exact hcongr
  rw [key1]
  rw [show (fun y : ℝ => 2 * α / (1 + y)) = fun y : ℝ => (2 * α / 3) * (3 / (1 + y)) from by
    funext y; ring]
  rw [nzZop_iter_const_mul]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * α / 3)]
  have h := hK3 b hb z (le_of_lt hz)
  nlinarith

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
