import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.EllipticEst.Vop_bound_reg
import Submission.Work.FTS.OpenPkg.WDp_le_of_pointwise
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.LocDataExt.Monotone

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## `SmoothOpen` closure (local copies, Mathlib-level)

The tree's `SmoothOpen`-API modules (`alphaDzW_Hk_le`, `EllHyp_certificates`, `AeI1Fts`) are
currently unbuildable (`lake` reports upstream errors), so the few closure facts needed here are
re-proved directly from Mathlib's `ContDiffOn` API. -/

theorem smoothOpen_add {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.add hg

theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.mul hg

theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ) = c • Function.uncurry f := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.const_smul c

theorem smoothOpen_sub {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = Function.uncurry f - Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.sub hg

/-- A radial function which is `C^n` on `(0,∞)` for every `n` is `C^∞` on the open quadrant. -/
theorem smoothOpen_radial {r : ℝ → ℝ} (hr : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
  refine contDiffOn_infty.mpr fun n => ?_
  change ContDiffOn ℝ n (fun p : ℝ × ℝ => r p.1) Work.FTS.EllipticEst.Q0
  exact (hr n).comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1

/-- `tan` is smooth on the open quadrant. -/
theorem smoothOpen_tan : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.tan θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.tan p.2)
    Work.FTS.EllipticEst.Q0
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hθ0], by linarith [Real.pi_pos, hθ1]⟩)
  refine ContDiffOn.congr (hsin.div hcos hne) ?_
  intro p _
  simp only [Real.tan_eq_sin_div_cos, Pi.div_apply]

/-- `Vop Φ` is smooth on the open quadrant as soon as `Φ` is. -/
theorem smoothOpen_Vop {Φ : Fn} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Φ) := by
  have hprod : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Φ z θ) :=
    smoothOpen_mul smoothOpen_tan hΦ
  have hkey : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Φ z θ - Real.tan θ * Φ z θ) :=
    smoothOpen_sub (Work.FTS.EllipticEst.SmoothOpen.pth hΦ) hprod
  refine ContDiffOn.congr (f₁ := fun p : ℝ × ℝ => Work.Construction.Vop Φ p.1 p.2) hkey ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- The `θ`-slice of a `SmoothOpen` function is differentiable. -/
theorem differentiableAt_slice_snd_of_smoothOpen {F : Fn}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => F z θ') θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hc : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry F) (z, θ) :=
    hF.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hc1 : ContDiffAt ℝ 1 (Function.uncurry F) (z, θ) := hc.of_le (by simp)
  have hd : DifferentiableAt ℝ (Function.uncurry F) (z, θ) := hc1.differentiableAt (by norm_num)
  have h2 : DifferentiableAt ℝ (fun t : ℝ => (z, t)) θ :=
    (differentiableAt_const (c := z)).prodMk differentiableAt_id
  exact (hd.comp θ h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)

/-- **The pointwise relation carried by `EllPkgGo.V`.**  Since
`PhiTil α g Φg = Φg - (1/(4α)) sin(2θ) L₁₂(g)`, one has

  `Vop (PhiTil α g Φg) = Vop Φg - (1/(2α)) · c2m(θ) · L₁₂(g)(z)`. -/
theorem vop_PhiTg_eq (α : ℝ) {g Φg : Fn} {z θ : ℝ}
    (hΦ : DifferentiableAt ℝ (fun θ' => Φg z θ') θ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
      = Work.Construction.Vop Φg z θ
        - (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z) := by
  have hθIoo : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hTheta : HasDerivAt
      (fun θ' : ℝ => (1 / (4 * α)) * (Real.sin (2 * θ') * Work.Construction.L12 g z))
      ((1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z)) θ :=
    (hsin.mul_const (Work.Construction.L12 g z)).const_mul (1 / (4 * α))
  have hPhiTg : HasDerivAt
      (fun θ' : ℝ => Work.FTS.Nonlin.PhiTg α g Φg z θ')
      (deriv (fun θ' => Φg z θ') θ
        - (1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Φg z θ') (deriv (fun θ' => Φg z θ') θ) θ :=
      hΦ.hasDerivAt
    refine (h1.sub hTheta).congr_of_eventuallyEq ?_
    filter_upwards with θ'
    simp only [Work.FTS.Nonlin.PhiTg, Work.Construction.PhiTil, Work.Construction.Theta,
      Work.Construction.s2, Pi.sub_apply]
    ring_nf
  have hmain : deriv (fun θ' => Work.FTS.Nonlin.PhiTg α g Φg z θ') θ
      = deriv (fun θ' => Φg z θ') θ
        - (1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z) :=
    hPhiTg.deriv
  have hcf : Work.Construction.c2m θ = 1 - 3 * Real.sin θ ^ 2 := by
    rw [Work.Construction.c2m, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hfac : 2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ) = 2 * Work.Construction.c2m θ := by
    rw [Work.FTS.EllipticEst.vop_factor_eq θ hθIoo, hcf]
  have htanmul : Real.tan θ * (Real.sin (2 * θ) * Work.Construction.L12 g z)
      = (2 * Real.sin θ ^ 2) * Work.Construction.L12 g z := by
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hθ.1], by linarith [Real.pi_pos, hθ.2]⟩)
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
  show deriv (fun θ' => Work.FTS.Nonlin.PhiTg α g Φg z θ') θ
      - Real.tan θ * Work.FTS.Nonlin.PhiTg α g Φg z θ
    = (deriv (fun θ' => Φg z θ') θ - Real.tan θ * Φg z θ)
      - (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z)
  have hmain2 : (1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z)
      - Real.tan θ * ((1 / (4 * α)) * (Real.sin (2 * θ) * Work.Construction.L12 g z))
      = (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z) := by
    have h1 : (1 / (4 * α)) * (2 * Real.cos (2 * θ) * Work.Construction.L12 g z)
        - Real.tan θ * ((1 / (4 * α)) * (Real.sin (2 * θ) * Work.Construction.L12 g z))
        = (1 / (4 * α))
          * ((2 * Real.cos (2 * θ) - Real.tan θ * Real.sin (2 * θ))
            * Work.Construction.L12 g z) := by ring
    rw [h1, hfac]
    ring
  rw [hmain]
  simp only [Work.FTS.Nonlin.PhiTg, Work.Construction.PhiTil, Work.Construction.Theta,
    Work.Construction.s2]
  linarith [hmain2]

/-- **The smoothness of `c2m(θ)·L₁₂(g)(z)`**, read off from `EllPkgGo.V`. -/
theorem smoothOpen_c2m_L12 {α : ℝ} {g Φg : Fn} (hα : 0 < α)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) := by
  have hVΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Φg) := smoothOpen_Vop hΦg
  have hdiff : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Vop Φg z θ
        - Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ) :=
    smoothOpen_sub hVΦ hV
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z)) := by
    refine ContDiffOn.congr (f₁ := fun p : ℝ × ℝ => (1 / (2 * α))
      * (Work.Construction.c2m p.2 * Work.Construction.L12 g p.1)) hdiff ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have h := vop_PhiTg_eq (g := g) α
      (differentiableAt_slice_snd_of_smoothOpen hΦg hz ⟨hθ0, hθ1⟩) ⟨hθ0, hθ1⟩
    show (1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z)
      = Work.Construction.Vop Φg z θ
        - Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
    rw [h]; ring
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * α) * ((1 / (2 * α))
        * (Work.Construction.c2m θ * Work.Construction.L12 g z))) :=
    smoothOpen_const_mul (2 * α) h1
  refine ContDiffOn.congr (f₁ := fun p : ℝ × ℝ =>
    Work.Construction.c2m p.2 * Work.Construction.L12 g p.1) h2 ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  show Work.Construction.c2m θ * Work.Construction.L12 g z
    = (2 * α) * ((1 / (2 * α)) * (Work.Construction.c2m θ * Work.Construction.L12 g z))
  field_simp


/-- **The radial smoothness of `L₁₂(g)`.**  Dividing `c2m(θ)·L₁₂(g)(z)` by the non-zero
constant `c2m(π/4) = -1/2` on the slice `θ = π/4` gives `C^∞`-smoothness of `z ↦ L₁₂(g)(z)`
on `(0,∞)`. -/
theorem smoothOpen_L12_radial {α : ℝ} {g Φg : Fn} (hα : 0 < α)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) := by
  have hc2m := smoothOpen_c2m_L12 hα hΦg hV
  have hθ₀ : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Construction.c2m (Real.pi / 4) * Work.Construction.L12 g z)
      (Set.Ioi 0) :=
    hc2m.curry_z hθ₀
  have hne : Work.Construction.c2m (Real.pi / 4) ≠ 0 := by
    rw [Work.Construction.c2m]
    have h1 : Real.cos (2 * (Real.pi / 4)) = 0 := by
      rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two]
    rw [h1]
    have h2 : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
      rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [h2]; norm_num
  have hmain : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Construction.L12 g z) (Set.Ioi 0) := by
    refine ContDiffOn.congr
      (hslice.const_smul ((Work.Construction.c2m (Real.pi / 4))⁻¹)) ?_
    intro z _
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  refine smoothOpen_radial (r := fun z => Work.Construction.L12 g z) fun n => ?_
  exact (contDiffOn_infty.mp hmain) n

/-! ## The `D_z`-iterate bounds for `L₁₂(g)` -/

/-- **The uniform bounds on the `D_z`-iterates of `L₁₂(g)`.**  For `GalClass`-type data,
`|D_z^b L₁₂(g)(z)| ≤ KL·Xn α g` for `b ≤ 4` and every `z > 0`: the `b = 0` case is the growth
estimate `(L₁₂ g z)² ≤ Kc X² min(z³, 1/z)`, and `b ≥ 1` is the angular-moment recursion
`D_z^{k+1}L₁₂(g) = -Qang g k` together with `(Qang g k z)² ≤ (∫Kθ²)·HkSq α 4 g`. -/
theorem L12_dzdIter_abs_le :
    ∃ KL : ℝ, 0 < KL ∧ ∀ {α : ℝ} {g : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g →
      (∀ i : ℕ, i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
        Filter.Tendsto (fun z => Work.Spaces.DzIter i g z θ) Filter.atTop (nhds 0)) →
      Work.Construction.L12 g 0 = 0 →
      ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
          ≤ KL * Work.FTS.Nonlin.Xn α g := by
  set Kc : ℝ := max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / (3 : ℝ))
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1 with hKc
  have hKth0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hmax0 : 0 ≤ max ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) / (3 : ℝ))
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) :=
    le_trans (by positivity) (le_max_right _ _)
  have hKc1 : 1 ≤ Kc := by rw [hKc]; linarith
  have hKc0 : 0 < Kc := lt_of_lt_of_le zero_lt_one hKc1
  refine ⟨Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1,
    by positivity, ?_⟩
  intro α g hα hα1 hsm hmem hdec h0 b hb z hz
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hXs : (Work.Spaces.HkSq α 4 g) = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    obtain ⟨hgrowth1, hgrowth2⟩ :=
      Work.FTS.Nonlinear.Pieces.L12_sq_le_growth α hα hα1 hsm hmem h0
    have hKcX0 : 0 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by positivity
    have hbound : (Work.Construction.L12 g z) ^ 2 ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
      rcases le_or_gt z 1 with hz1 | hz1
      · refine (hgrowth1 z hz).trans ?_
        have : z ^ 3 ≤ 1 := pow_le_one₀ hz.le hz1
        calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * z ^ 3
            ≤ Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left this hKcX0
          _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
      · refine (hgrowth2 z hz).trans ?_
        have : 1 / z ≤ 1 := by rw [div_le_one hz]; linarith
        calc Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 / z
            = (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * (1 / z) := by ring
          _ ≤ (Kc * (Work.FTS.Nonlin.Xn α g) ^ 2) * 1 :=
              mul_le_mul_of_nonneg_left this hKcX0
          _ = Kc * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    have h1 : |Work.Construction.L12 g z| ≤ Real.sqrt Kc * Work.FTS.Nonlin.Xn α g := by
      have h := Real.sqrt_le_sqrt hbound
      rw [Real.sqrt_mul (le_of_lt hKc0), Real.sqrt_sq_eq_abs,
        Real.sqrt_sq hX0] at h
      exact h
    have h2 : Real.sqrt Kc * Work.FTS.Nonlin.Xn α g
        ≤ (Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * Work.FTS.Nonlin.Xn α g := by
      have h1' : Real.sqrt Kc ≤ Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Ktheta θ ^ 2) + 1 := by
        have := Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        linarith
      exact mul_le_mul_of_nonneg_right h1' hX0
    calc |Work.Elliptic.DzdIter 0 (fun z => Work.Construction.L12 g z) z|
        = |Work.Construction.L12 g z| := rfl
      _ ≤ Real.sqrt Kc * Work.FTS.Nonlin.Xn α g := h1
      _ ≤ _ := h2
  · have hrec := (Work.FTS.Nonlinear.Pieces.L12_dzdIter_moment α hα hα1 hsm hmem h0).1
      (b - 1) (by omega) z hz
    have hbsucc : b = (b - 1) + 1 := by omega
    rw [hbsucc, hrec, abs_neg]
    have hq := Work.FTS.Nonlinear.Pieces.Qang_sq_le_const α hsm hmem hdec (i := b - 1)
      (by omega) hz
    have hq' : (Work.Elliptic.Qang g (b - 1) z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
      rw [hXs] at hq; exact hq
    have h1 : |Work.Elliptic.Qang g (b - 1) z|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.FTS.Nonlin.Xn α g := by
      have h := Real.sqrt_le_sqrt hq'
      rw [Real.sqrt_mul hKth0, Real.sqrt_sq_eq_abs, Real.sqrt_sq hX0] at h
      exact h
    have h2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.FTS.Nonlin.Xn α g
        ≤ (Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
          * Work.FTS.Nonlin.Xn α g := by
      have h1' : Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          ≤ Real.sqrt Kc + Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1 := by
        have := Real.sqrt_nonneg Kc
        linarith
      exact mul_le_mul_of_nonneg_right h1' hX0
    calc |Work.Elliptic.Qang g (b - 1) z| ≤ _ := h1
      _ ≤ _ := h2

/-- `D_θ^j` of a function of `z` alone vanishes for `j ≥ 1`. -/
theorem dthIter_rad_eq_zero (r : ℝ → ℝ) : ∀ j : ℕ, 1 ≤ j →
    Work.Spaces.DthIter j (fun z _ => r z) = 0 := by
  intro j
  induction j with
  | zero => intro hj; omega
  | succ j ih =>
      intro _hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        funext z θ
        simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth,
          Work.Spaces.pth, Pi.zero_apply, deriv_const]
        ring
      · rw [Work.Spaces.DthIter_succ, ih hjpos]
        funext z θ
        simp only [Pi.zero_apply, Work.Spaces.Dth, Work.Spaces.pth]
        rw [deriv_const]
        ring

/-- `D_z^b` of the zero function vanishes. -/
theorem dzIter_zero : ∀ b : ℕ, Work.Spaces.DzIter b (0 : ℝ → ℝ → ℝ) = 0 := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp only [Pi.zero_apply, Work.Spaces.Dz, Work.Spaces.pz, deriv_const]
      ring

/-- The radial `D_z`-iterates commute with multiplication by a constant. -/
theorem dzdIter_const_mul (b : ℕ) (c : ℝ) (r : ℝ → ℝ) :
    Work.Elliptic.DzdIter b (fun z => c * r z)
      = fun z => c * Work.Elliptic.DzdIter b r z := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Work.Elliptic.DzdIter_succ, ih, Work.Elliptic.DzdIter_succ]
      funext z
      show z * deriv (fun z' => c * Work.Elliptic.DzdIter b r z') z
        = c * (z * deriv (fun z' => Work.Elliptic.DzdIter b r z') z)
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.deriv_const_mul']
      ring

/-- Row 4 of the §8 table, in the primed vocabulary: the `ℋ⁴`-honesty and the pairing bound of
`N₀₄ᵇ = (3/(2α)) sin(2θ) L₁₂(g) ∂_θ g = ((3/(2α)) L₁₂(g)) · D_θ g`; the pairing uses the
`D_θ`-transport clause `N4Extra'.t4` with the `D`-sup coefficient `(3/(2α)) L₁₂(g)`. -/
theorem row4 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) ∧
        |IP α (Work.FTS.Nonlin.N04bF α g) g|
          ≤ K * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCi, hα₂pos⟩ := hN.pos
  obtain ⟨hCt, _⟩ := hE.pos
  obtain ⟨KL, hKLpos, hKLb⟩ := L12_dzdIter_abs_le
  refine ⟨Ct * 25 * (3 / 2) * KL + 1, by positivity, ?_⟩
  intro α g Φs Φg hctx
  have hα := hctx.hα
  have hα1 := hctx.hα1
  have hαα₂ := hctx.hαα₂
  have hgal := hctx.hg
  have hell := hctx.hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hreg6 : Work.FTS.Nonlin.RegQ α 6 g := hgal.reg
  have hreg5 : Work.FTS.Nonlin.RegQ α 5 g :=
    Work.FTS.LocDataExt.RegQ_mono (by norm_num) hreg6
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- the smoothness of the radial coefficient
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) :=
    smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  -- the coefficient `f = (3/(2α))·L₁₂(g)` as an `ℋ⁴`-function
  have hL12 := hN.l12H α hIoc g (Work.FTS.OpenPkg.HQo_of_RegQ hreg4) hgal.l12
  have hfMem : Work.Spaces.HkMem α 4 (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12.1
  have hfx0 : (0 : ℝ) ≤ 3 / (2 * α) := by positivity
  have hfXn : Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ (3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg hfx0]
    exact mul_le_mul_of_nonneg_left hL12.2 hfx0
  -- the pointwise (`D`-sup) bound on the coefficient: `WDMem 4` and `WDp`
  have hpt : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b j (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ|
        ≤ (3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g) := by
    intro b j hbj z θ hz hθ0 hθ1
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hmixed : Work.Spaces.mixed b 0
            (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ
          = (3 / (2 * α)) * Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z := by
        rw [Work.Spaces.mixed_zero_right, Work.FTS.Nonlinear.Pieces.RowsN0Aux.DzIter_const_mul]
        simp only [Work.Elliptic.DzIter_rad]
      rw [hmixed, abs_mul, abs_of_nonneg hfx0]
      exact mul_le_mul_of_nonneg_left
        (hKLb hα hα1 hreg6.1 hreg4.2.1
          (fun i hi θ' hθ' => by
            have h := hgal.decay.2 0 i (by omega) θ' hθ'
            simpa only [Work.Spaces.mixed_zero_right] using h)
          hgal.l12 b hbj z hz) hfx0
    · have hzero : Work.Spaces.mixed b j
          (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ = 0 := by
        have hd : Work.Spaces.DthIter j (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
            = 0 := by
          rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul,
            dthIter_rad_eq_zero (fun z => Work.Construction.L12 g z) j hj]
          funext z θ
          simp only [Pi.zero_apply]
          ring
        simp only [Work.Spaces.mixed, hd]
        rw [dzIter_zero b]
        simp only [Pi.zero_apply]
      rw [hzero, abs_zero]
      positivity
  have hWDmem : Work.FTS.VocabO.WDMem 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    fun b j hbj => ⟨(3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g),
      fun z θ hz hθ0 hθ1 => hpt b j hbj z θ hz hθ0 hθ1⟩
  have hWDp : Work.FTS.VocabO.WDp 4
        (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ 25 * ((3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g)) :=
    Work.FTS.OpenPkg.WDp_le_of_pointwise (α := α) (by positivity) hpt
  -- the `ℋ⁴`-honesty of the piece, by the product rule with `D_θ g`
  have hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
    Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α 4 (by linarith) hreg5
  have hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) :=
    (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hreg6.1).Dth
  have hprod := hN.prod α hIoc (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
    (Work.Spaces.Dth g) ⟨smoothOpen_const_mul (3 / (2 * α)) hL12sm, hfMem⟩ ⟨hDthSm, hDthMem⟩
  have hid : Work.FTS.Nonlin.N04bF α g
      = fun z θ => (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ
          * Work.Spaces.Dth g z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.Ftot,
      Work.Construction.Fstar, Work.Spaces.Dth, Work.Spaces.pth, Work.Construction.s2,
      Work.FTS.Nonlin.PhiTg]
    ring
  rw [hid]
  refine ⟨hprod.1, ?_⟩
  -- the pairing bound
  have ht4 := hE.t4 α hIoc (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) g
    hWDmem hreg4
  refine ht4.trans ?_
  have hrp : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hb1 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  have hXg3 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g ^ 2 := by positivity
  calc Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4
          (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
        * Work.FTS.Nonlin.Xn α g ^ 2
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (25 * ((3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g)))
        * Work.FTS.Nonlin.Xn α g ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDp ?_) hXg3
        exact mul_nonneg hCt.le hrp
    _ = Ct * 25 * (3 / 2) * KL * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
        have hpow : α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 : ℝ)) = α ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hα]
          norm_num
        have hinv : (3 : ℝ) / (2 * α) = (3 / 2) * α ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg_one]
          field_simp
        rw [hinv]
        linear_combination (Ct * 25 * (3 / 2) * KL * Work.FTS.Nonlin.Xn α g ^ 3) * hpow
    _ ≤ (Ct * 25 * (3 / 2) * KL + 1)
          * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
        refine mul_le_mul_of_nonneg_right ?_ hb1
        linarith [hCt, hKLpos]

end Work.FTS.NonlinRows
