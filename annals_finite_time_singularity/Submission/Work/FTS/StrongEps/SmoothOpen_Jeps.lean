import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.L12Moment =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TTL12M

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Integrability of the square of the angular moment -/

/-- On the domain `(0,∞)` the radial weight satisfies `1 ≤ w`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have h : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
    ring
  rw [h]
  nlinarith [one_div_pos.mpr hz]






/-! ## Smoothness of the two radial functions used in the ODE argument -/



/-! ## `F_*(D_zΨ)²` for the data of `EllHyp` -/

/-- `z² F_*(∂_z²Ψ)(z) = F_*(z² ∂_z²Ψ)(z)`: the radial factor is constant in `θ`. -/
theorem zsq_mul_Fstar {g : ℝ → ℝ → ℝ} (z : ℝ) :
    z ^ 2 * Work.Elliptic.Fstar g z
      = Work.Elliptic.Fstar (fun z' θ => z ^ 2 * g z' θ) z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, ← MeasureTheory.integral_const_mul]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)



/-! ## The moment identity -/




/-! ## The moment ODE, and the main certificate -/


/-- **The ODE for the angular moment of a solution** (rewritten form of `PsiStar_ode`). -/
theorem FstarOde (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ∀ z : ℝ, 0 < z →
      α ^ 2 * Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z
        + α * (5 + α) * Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z
      = -Work.Elliptic.Fstar F z := by
  intro z hz
  have hm1 : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z
      = z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z :=
    Work.FTS.EllipticEst.Cert.L12Aux.Fstar_DzIter_one_eq Ψ h.smoothNbhd hz
  have hm2 : deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
      = Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z :=
    (Work.FTS.EllipticEst.Cert.L12Aux.hasDerivAt_deriv_Fstar Ψ h.smoothNbhd hz).deriv
  have hscale : z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
      = Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z :=
    zsq_mul_Fstar z
  have hode := Work.Elliptic.PsiStar_ode α F Ψ z hα hz h.smoothNbhd h.sol
  rw [hm2] at hode
  rw [show α ^ 2 * z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
      = α ^ 2 * (z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z) from by ring,
    hscale] at hode
  have hm1' : Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z
      = z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hm1
  rw [show α * (5 + α) * z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z
      = α * (5 + α) * (z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z) from by ring] at hode
  rw [← hm1'] at hode
  exact hode




end Work.FTS.EllipticEst.TTL12M
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsSmoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The log map `x ↦ (exp x.1, arctan (exp x.2))` is continuous and lands in the open quadrant. -/
theorem continuous_logMap_quad :
    Continuous (fun x : ℝ × ℝ => (Real.exp x.1, Real.arctan (Real.exp x.2))) ∧
      ∀ x : ℝ × ℝ, (Real.exp x.1, Real.arctan (Real.exp x.2)) ∈ Quad := by
  constructor
  · exact (Real.continuous_exp.comp continuous_fst).prodMk
      (Real.continuous_arctan.comp (Real.continuous_exp.comp continuous_snd))
  · intro x
    refine ⟨Real.exp_pos x.1, ?_, ?_⟩
    · exact Real.arctan_pos.mpr (Real.exp_pos x.2)
    · exact Real.arctan_lt_pi_div_two _

/-- `logPull f` is continuous on `ℝ²` when `f` is `C⁰` on the open quadrant. -/
theorem continuous_logPull_of_forall_contDiffOn {f : Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) : Continuous (logPull f) := by
  have hcont : ContinuousOn (Function.uncurry f) Quad := (hf 0).continuousOn
  have hmap := continuous_logMap_quad.1
  have hmaps := continuous_logMap_quad.2
  have hcomp : Continuous ((Function.uncurry f) ∘
      fun x : ℝ × ℝ => (Real.exp x.1, Real.arctan (Real.exp x.2))) :=
    ContinuousOn.comp_continuous hcont hmap hmaps
  exact hcomp

/-- `logPull f` is locally integrable when `f` is `C⁰` on the open quadrant. -/
theorem locallyIntegrable_logPull_of_forall_contDiffOn {f : Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) :
    MeasureTheory.LocallyIntegrable (logPull f) volume :=
  (continuous_logPull_of_forall_contDiffOn hf).locallyIntegrable

/-- **`J_ε` preserves `SmoothOpen`** (for a smooth kernel): the conclusion of `Jeps_contDiffOn`
in the `SmoothOpen`-form used by the pairing's additivity lemma. -/
theorem smoothOpen_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) :
    Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε f) :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr
    (Jeps_contDiffOn ρ hρ hε (locallyIntegrable_logPull_of_forall_contDiffOn hf))

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.Kernel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 400000

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : Fn}

/-! ## The two shift regions -/

/-- The `z`-range of the shift, over `x ∈ (z/2, 2z)` and `|p| ≤ ε`. -/
def Kz (z ε : ℝ) : Set ℝ := Set.Icc (z / 2 * Real.exp (-ε)) (2 * z * Real.exp ε)

/-- The `θ`-range of the shift, over `|p| ≤ ε` (the shift is antitone in `p`). -/
def Kth (θ ε : ℝ) : Set ℝ := Set.Icc (thShift θ ε) (thShift θ (-ε))

theorem isCompact_Kz (z ε : ℝ) : IsCompact (Kz z ε) := isCompact_Icc

theorem isCompact_Kth (θ ε : ℝ) : IsCompact (Kth θ ε) := isCompact_Icc

theorem zShift_mem_Kz {z x p ε : ℝ} (hx : x ∈ Set.Ioo (z / 2) (2 * z)) (hp : |p| ≤ ε) :
    zShift x p ∈ Kz z ε := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  have hxpos : 0 < x := by linarith
  have hzpos : 0 < z := by linarith
  have hexp : Real.exp (-ε) ≤ Real.exp (-p) := Real.exp_le_exp.mpr (by linarith)
  have hexp' : Real.exp (-p) ≤ Real.exp ε := Real.exp_le_exp.mpr (by linarith)
  show z / 2 * Real.exp (-ε) ≤ zShift x p ∧ zShift x p ≤ 2 * z * Real.exp ε
  constructor
  · have h := mul_le_mul (show z / 2 ≤ x by linarith) hexp (Real.exp_pos _).le (le_of_lt hxpos)
    simpa only [zShift] using h
  · have h := mul_le_mul (le_of_lt hx2) hexp' (Real.exp_pos _).le (by linarith : (0:ℝ) ≤ 2 * z)
    simpa only [zShift] using h

theorem thShift_anti {θ p q : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hpq : p ≤ q) :
    thShift θ q ≤ thShift θ p := by
  have ht : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  have h : Real.tan θ * Real.exp (-q) ≤ Real.tan θ * Real.exp (-p) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) ht.le
  exact Real.arctan_strictMono.monotone h

theorem thShift_mem_Kth {θ p ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hp : |p| ≤ ε) :
    thShift θ p ∈ Kth θ ε := by
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  exact ⟨thShift_anti hθ hp2, thShift_anti hθ (by linarith)⟩

/-- The shifted point stays in the open quadrant. -/
theorem mem_Quad_shift {z θ x p₁ p₂ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hx : x ∈ Set.Ioo (z / 2) (2 * z)) :
    (zShift x p₁, thShift θ p₂) ∈ Quad :=
  ⟨zShift_pos (by linarith [hx.1, hz]), thShift_mem hθ⟩

/-- The map `p ↦ (zShift x p.1, thShift θ p.2)` sends the ball of radius `ε` into the compact
region `Kz z ε ×ˢ Kth θ ε`, for every `x ∈ (z/2, 2z)`. -/
theorem mapsTo_ball_region {z θ x ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hx : x ∈ Set.Ioo (z / 2) (2 * z)) :
    MapsTo (fun p : ℝ × ℝ => (zShift x p.1, thShift θ p.2)) (Metric.closedBall 0 ε)
      (Kz z ε ×ˢ Kth θ ε) := by
  intro p hp
  have hp' : max |p.1| |p.2| ≤ ε := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hp
  exact ⟨zShift_mem_Kz hx (le_trans (le_max_left _ _) hp'),
    thShift_mem_Kth hθ (le_trans (le_max_right _ _) hp')⟩

theorem Kz_subset_pos {z ε : ℝ} (hz : 0 < z) (hε : 0 < ε) :
    Kz z ε ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact lt_of_lt_of_le (by positivity) hx.1

theorem Kth_subset {θ ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Kth θ ε ⊆ Set.Ioo 0 (π / 2) :=
  fun x hx => ⟨lt_of_lt_of_le (thShift_mem hθ).1 hx.1,
    lt_of_le_of_lt hx.2 (thShift_mem hθ).2⟩

/-- The compact region of the shifts is contained in the open quadrant. -/
theorem Kz_prod_Kth_subset_Quad {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Kz z ε ×ˢ Kth θ ε ⊆ Quad := by
  intro y hy
  exact ⟨Kz_subset_pos hz hε hy.1, Kth_subset hθ hy.2⟩


theorem continuous_thShift (θ : ℝ) : Continuous fun p : ℝ => thShift θ p := by
  simp only [thShift]; fun_prop

/-- The shifted point of a fixed base point, as a continuous function of the shift. -/
theorem continuous_shift_pair (z θ : ℝ) :
    Continuous fun p : ℝ × ℝ => (zShift z p.1, thShift θ p.2) := by
  simp only [zShift, thShift]
  fun_prop

/-- A base point lies in its own symmetric region. -/
theorem self_mem_Ioo_div_two {z : ℝ} (hz : 0 < z) : z ∈ Set.Ioo (z / 2) (2 * z) :=
  Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩

/-! ## The kernel -/

theorem Jker_ne_zero_support (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : Jker ρ ε p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2 := by
  have h1 : (ε⁻¹ • p).1 ^ 2 + (ε⁻¹ • p).2 ^ 2 ≤ 1 :=
    hρ.support (ε⁻¹ • p) (fun hzero => hp (by simp [Jker, hzero]))
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1
  have h2 : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by field_simp
  nlinarith [h1, h2, sq_nonneg (ε⁻¹ * p.1), sq_nonneg (ε⁻¹ * p.2), sq_nonneg ε,
    sq_nonneg ε⁻¹, sq_nonneg (ε * ε⁻¹ * p.1), sq_nonneg (ε * ε⁻¹ * p.2)]

theorem Jker_continuous (hρ : IsMollKernel ρ) (ε : ℝ) : Continuous (Jker ρ ε) :=
  continuous_const.mul (hρ.cont.comp (continuous_const_smul _))

theorem Jker_smooth (hρ : IsSmoothKernel ρ) (ε : ℝ) {n : ℕ} : ContDiff ℝ n (Jker ρ ε) := by
  have h1 : ContDiff ℝ n fun p : ℝ × ℝ => ε⁻¹ • p := contDiff_const_smul _
  exact contDiff_const.mul ((hρ.smooth n).comp h1)

theorem Jker_hasCompactSupport (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (Jker ρ ε) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ × ℝ) ε) isClosed_closure
    (closure_minimal ?_ Metric.isClosed_closedBall)
  intro p hp
  have h := Jker_ne_zero_support hρ hε hp
  have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
  have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
  have ha : |p.1| ≤ ε := by
    rw [sq_le_sq] at h1
    rwa [abs_of_nonneg hε.le] at h1
  have hb : |p.2| ≤ ε := by
    rw [sq_le_sq] at h2
    rwa [abs_of_nonneg hε.le] at h2
  rw [Metric.mem_closedBall, dist_zero_right]
  exact max_le ha hb

theorem Jker_integrable (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (Jker ρ ε) :=
  (Jker_continuous hρ ε).integrable_of_hasCompactSupport (Jker_hasCompactSupport hρ hε)

/-- The kernel vanishes off the ball of radius `ε`. -/
theorem Jker_eq_zero_of_not_mem (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : p ∉ Metric.closedBall 0 ε) : Jker ρ ε p = 0 := by
  by_contra h
  have h' := Jker_ne_zero_support hρ hε h
  have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
  have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
  have ha : |p.1| ≤ ε := by rw [sq_le_sq] at h1; rwa [abs_of_nonneg hε.le] at h1
  have hb : |p.2| ≤ ε := by rw [sq_le_sq] at h2; rwa [abs_of_nonneg hε.le] at h2
  refine hp ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact max_le ha hb

/-- **The basic integrability fact**: on the compact ball of radius `ε`, the product of the
kernel with a function that is continuous there is integrable. -/
theorem integrableOn_Jker_mul_ball (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {A : ℝ × ℝ → ℝ} (hA : ContinuousOn A (Metric.closedBall 0 ε)) :
    IntegrableOn (fun p => Jker ρ ε p * A p) (Metric.closedBall 0 ε) :=
  ((Jker_continuous hρ ε).continuousOn.mul hA).integrableOn_compact
    (isCompact_closedBall (0 : ℝ × ℝ) ε)


/-! ## Two elementary trigonometric facts used by the commutation -/

/-- `sin (2 arctan u) = 2u/(1+u²)`. -/
theorem sin_two_mul_arctan (u : ℝ) : Real.sin (2 * Real.arctan u) = 2 * u / (1 + u ^ 2) := by
  have hpos : 0 < √(1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-- **The `θ`-half of the commutation**: `sin(2θ) ∂_θ(thShift θ p) = sin (2·thShift θ p)`, i.e.
`D_θ` of the shifted point is the shifted point's own `sin(2·)`. -/
theorem sin_mul_deriv_thShift {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ) :
    Real.sin (2 * θ) * deriv (fun θ' => thShift θ' p) θ
      = Real.sin (2 * thShift θ p) := by
  have hlt : -(π / 2) < θ := by linarith [hθ.1, Real.pi_pos]
  have hcos : Real.cos θ ≠ 0 := by
    have hp := Real.cos_arctan_pos (Real.tan θ)
    rw [Real.arctan_tan hlt hθ.2] at hp
    exact hp.ne'
  have ht : HasDerivAt (fun θ' => Real.tan θ' * Real.exp (-p))
      ((1 / Real.cos θ ^ 2) * Real.exp (-p)) θ :=
    (Real.hasDerivAt_tan hcos).mul_const _
  have harct := (Real.hasDerivAt_arctan (Real.tan θ * Real.exp (-p))).comp θ ht
  have hd : deriv (fun θ' => thShift θ' p) θ
      = (1 / (1 + (Real.tan θ * Real.exp (-p)) ^ 2))
          * ((1 / Real.cos θ ^ 2) * Real.exp (-p)) := by
    simpa only [thShift, Function.comp_def] using harct.deriv
  rw [hd]
  have h1 : Real.sin (2 * θ) = 2 * Real.tan θ * Real.cos θ ^ 2 := by
    rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos]
    field_simp
  rw [h1, show thShift θ p = Real.arctan (Real.tan θ * Real.exp (-p)) from rfl,
    sin_two_mul_arctan]
  field_simp

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.SmoothOpen_Jeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Convolution
open MeasureTheory Set Filter
open Work.FTS.EllipticEst (Q0 mem_Q0)

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-! ## The kernel `Jker ρ ε` of a merely continuous mollifier -/

/-- `Jker ρ ε` is continuous as soon as `ρ` is. -/
theorem continuous_Jker (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) (ε : ℝ) :
    Continuous (Jker ρ ε) :=
  continuous_const.mul (hρ.cont.comp (continuous_id.const_smul (ε⁻¹)))

/-- `Jker ρ ε` is compactly supported (its support is contained in the square of half-side `|ε|`,
because `ρ` is supported in the closed unit ball).  The variant of `hasCompactSupport_Jker`
(`Jeps_contDiffOn.lean`) for a merely continuous kernel. -/
theorem hasCompactSupport_Jker_moll (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) : HasCompactSupport (Jker ρ ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-|ε|) |ε| ×ˢ Set.Icc (-|ε|) |ε|)
    (isCompact_Icc.prod isCompact_Icc) ?_
  rintro ⟨x1, x2⟩ hx
  have hx' : ¬(-|ε| ≤ x1 ∧ x1 ≤ |ε|) ∨ ¬(-|ε| ≤ x2 ∧ x2 ≤ |ε|) := by
    simpa only [Set.mem_prod, Set.mem_Icc, not_and_or] using hx
  have aux : ∀ y : ℝ, ¬(-|ε| ≤ y ∧ y ≤ |ε|) → |ε| < |y| := by
    intro y hy
    rw [not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · have hy0 : y < 0 := by linarith [abs_nonneg ε, h]
      have : |y| = -y := abs_of_neg hy0
      linarith
    · have hy0 : 0 < y := by linarith [abs_nonneg ε, h]
      have : |y| = y := abs_of_nonneg hy0.le
      linarith
  have hbig : |ε| < |x1| ∨ |ε| < |x2| := by
    rcases hx' with h | h
    · exact Or.inl (aux x1 h)
    · exact Or.inr (aux x2 h)
  have habs_aux : ∀ y : ℝ, |ε| < |y| → (1 : ℝ) < (ε⁻¹ * y) ^ 2 := by
    intro y hy
    have h1 : (1 : ℝ) < |ε⁻¹ * y| := by
      rw [abs_mul, abs_inv, abs_of_pos hε, ← inv_mul_cancel₀ (ne_of_gt hε)]
      simpa [abs_of_pos hε] using mul_lt_mul_of_pos_left hy (inv_pos.mpr hε)
    have h2 : ((1 : ℝ)) ^ 2 < (ε⁻¹ * y) ^ 2 := by
      rw [sq_lt_sq]
      simpa using h1
    simpa using h2
  have hρ0 : ρ (ε⁻¹ • (x1, x2)) = 0 := by
    by_contra hne
    have hle := hρ.support _ hne
    simp only [Prod.smul_mk, smul_eq_mul] at hle
    have hsum : (1 : ℝ) < (ε⁻¹ * x1) ^ 2 + (ε⁻¹ * x2) ^ 2 := by
      rcases hbig with h | h
      · nlinarith [habs_aux x1 h, sq_nonneg (ε⁻¹ * x2)]
      · nlinarith [habs_aux x2 h, sq_nonneg (ε⁻¹ * x1)]
    exact absurd hle (not_le.mpr hsum)
  simp only [Jker, hρ0, mul_zero]

/-! ## Convolution with a compactly supported continuous kernel -/

/-- **Convolution with a compactly supported continuous kernel preserves `C^n`.**

The kernel `K` is only assumed continuous; the derivatives are pushed onto the `C^n` factor `g`.
Since `g` need not be compactly supported, one localises: near a fixed point `x₀` the convolution
only evaluates `g` on the compact set `x₀ - tsupport K`, where a smooth bump function equal to `1`
may be inserted. -/
theorem contDiff_convolution_of_continuous_hasCompactSupport {K g : ℝ × ℝ → ℝ} (n : ℕ)
    (hKc : Continuous K) (hK : HasCompactSupport K) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let r : ℝ := |R| + 1
  have hrdef : r = |R| + 1 := rfl
  have hRr : tsupport K ⊆ Metric.closedBall (0 : ℝ × ℝ) r := by
    refine hR.trans (Metric.closedBall_subset_closedBall ?_)
    rw [hrdef]
    linarith [le_abs_self R]
  let ψ : ContDiffBump x₀ := ⟨r + 1, r + 2, by rw [hrdef]; positivity, by rw [hrdef]; norm_num⟩
  have hψrIn : ψ.rIn = r + 1 := rfl
  have hev : (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
      =ᶠ[𝓝 x₀] (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun x : ℝ × ℝ => ψ x * g x)) := by
    show ∀ᶠ x in 𝓝 x₀, (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x
      = (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x : ℝ × ℝ => ψ x * g x)) x
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨Metric.ball x₀ 1, Metric.ball_mem_nhds _ zero_lt_one, fun x hx => ?_⟩
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change K y * g (x - y) = K y * (ψ (x - y) * g (x - y))
    by_cases hy : K y = 0
    · rw [hy, zero_mul, zero_mul]
    · have hyts : y ∈ tsupport K := subset_closure (Function.mem_support.mpr hy)
      have hyr : ‖y‖ ≤ r := by
        have h := Metric.mem_closedBall.mp (hRr hyts)
        simpa only [dist_eq_norm, sub_zero] using h
      have hx1 : dist x x₀ < 1 := Metric.mem_ball.mp hx
      have hlt : dist (x - y) x₀ < ψ.rIn := by
        have h1 : dist (x - y) (x₀ - y) = dist x x₀ := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          abel
        have h2 : dist (x₀ - y) x₀ = ‖y‖ := by
          rw [dist_eq_norm]
          have h3 : (x₀ - y) - x₀ = -y := by abel
          rw [h3, norm_neg]
        have h4 : dist (x - y) x₀ < r + 1 := by
          calc dist (x - y) x₀
              ≤ dist (x - y) (x₀ - y) + dist (x₀ - y) x₀ := dist_triangle _ _ _
            _ = dist x x₀ + ‖y‖ := by rw [h1, h2]
            _ < 1 + r := by linarith
            _ = r + 1 := by ring
        rwa [hψrIn]
      have hpsi : ψ (x - y) = 1 :=
        ψ.one_of_mem_closedBall (Metric.ball_subset_closedBall hlt)
      rw [hpsi, one_mul]
  have hψg_cs : HasCompactSupport (fun x : ℝ × ℝ => ψ x * g x) :=
    ψ.hasCompactSupport.mul_right (f' := g)
  have hψg_diff : ContDiff ℝ n (fun x : ℝ × ℝ => ψ x * g x) :=
    (ContDiffBump.contDiff ψ).mul hg
  have hglob : ContDiff ℝ n (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun x : ℝ × ℝ => ψ x * g x)) :=
    HasCompactSupport.contDiff_convolution_right _ hψg_cs hKc.locallyIntegrable hψg_diff
  exact ((contDiff_iff_contDiffAt.mp hglob) x₀).congr_of_eventuallyEq hev

/-! ## The target -/

theorem SmoothOpen_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε f))
      Work.FTS.EllipticEst.Q0 := by
  intro n
  -- `logPull f` is `C^n`, because `(e^s, arctan e^ζ)` always lies in `Q0`
  have hlog : ContDiff ℝ n (logPull f) := by
    have hφ : ContDiff ℝ n
        (fun s : ℝ × ℝ => (Real.exp s.1, Real.arctan (Real.exp s.2))) :=
      (Real.contDiff_exp.comp contDiff_fst).prodMk
        (Real.contDiff_arctan.comp (Real.contDiff_exp.comp contDiff_snd))
    have hmem : ∀ s : ℝ × ℝ, (Real.exp s.1, Real.arctan (Real.exp s.2)) ∈ Q0 := fun s =>
      mem_Q0.mpr ⟨Real.exp_pos _, Real.arctan_pos.mpr (Real.exp_pos s.2),
        Real.arctan_lt_pi_div_two _⟩
    have h := (hf n).comp_contDiff hφ hmem
    have hfun : ((Function.uncurry f)
        ∘ (fun s : ℝ × ℝ => (Real.exp s.1, Real.arctan (Real.exp s.2)))) = logPull f := rfl
    rwa [hfun] at h
  -- the convolution with the kernel `Jker ρ ε` is `C^n`
  have hconv : ContDiff ℝ n
      (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f) :=
    contDiff_convolution_of_continuous_hasCompactSupport n (continuous_Jker ρ hρ ε)
      (hasCompactSupport_Jker_moll ρ hρ hε) hlog
  -- compose with the log-coordinate map, which is `C^∞` on `Q0`
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f)
          (sOf p.1, zetaOf p.2))
      Work.FTS.EllipticEst.Q0 := by
    have h := hconv.comp_contDiffOn (contDiffOn_logMap n)
    simpa only [Function.comp_def, Quad, Work.FTS.EllipticEst.Q0] using h
  -- and rewrite `Jeps` as the convolution in the log coordinates
  exact hcomp.congr (fun p hp => Jeps_eq_conv ρ ε f hp.1 hp.2)

end Work.FTS.StrongEps
end
end
