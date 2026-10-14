import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.L12Sin_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

/-! ## Bridge lemmas -/












/-! ## Continuity of the angular moments -/

/-- The angular moment `Qang g j` is continuous on `(0,∞)`: it is the parametric integral of
the smooth family `D_z^j g` against the continuous angular weight `K(θ)`. -/
theorem continuousOn_Qang (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g) (j : ℕ) :
    ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) := by
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  have hz1 : (-1 : ℝ) < z := by linarith
  have hsmj : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j g) :=
    Work.Elliptic.smoothNbhd_DzIter hsm j
  have hK : ContinuousOn Work.Elliptic.Ktheta (Set.Icc 0 (π / 2)) := by
    unfold Work.Elliptic.Ktheta
    exact ((continuous_const.mul Real.continuous_sin).mul
      (Real.continuous_cos.pow 2)).continuousOn
  have hd := Work.Elliptic.hasDerivAt_integral_Iθ (Work.Spaces.DzIter j g)
    Work.Elliptic.Ktheta hsmj hK hz1
  have hfun : (fun z' => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.DzIter j g z' θ * Work.Elliptic.Ktheta θ)
      = fun z' => Work.Elliptic.Qang g j z' := by
    funext z'
    rw [Work.Elliptic.Qang]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  rw [hfun] at hd
  exact hd.continuousAt.continuousWithinAt

/-! ## The assembly -/

/-- The proof of `L12Sin_mem`, given the three analytic inputs
(`L12_moment_eq`, `L12_dzdIter_eq`, `L12_radial_bound`). -/
theorem continuousOn_w' :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := by
  have h2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [h2]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))




/-! ## The target theorem -/



end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.VMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Continuity of the `ℋ^k`-integrand from finite-order smoothness -/

/-- **The uncurried `ℋ^k`-integrand of a `C^k`-on-the-open-quadrant function is continuous
there.**  This is the finite-order version of `SmoothOpen.continuousOn_HkIntegrand`: the four
ingredients are `contDiffOn_DzIter_fin`, `contDiffOn_DthIter_fin` (for the `D_z^j D_θ^i`-block)
and the continuity of the two weights. -/
theorem continuousOn_HkIntegrand_of_contDiffOn {h : ℝ → ℝ → ℝ} {k : ℕ}
    (hh : ContDiffOn ℝ k (Function.uncurry h) Work.FTS.EllipticEst.Q0) (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        Work.FTS.EllipticEst.Q0 := by
      have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
        funext p; rfl
      rw [hfun2]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp =>
          pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
    refine hw.mul ?_
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hZ : ∀ i ≤ k, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := fun i hi =>
    (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin isOpen_Q0 hh i hi).continuousOn
  have hM : ∀ j i, i + j ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i h p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
    intro j i hij
    have hi : i ≤ k := by omega
    have hstep := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hh i hi
    have hfin := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin isOpen_Q0 hstep j
      (by omega : j ≤ k - i)
    have hgoal : (fun p : ℝ × ℝ => Work.Spaces.mixed j i h p.1 p.2)
        = Function.uncurry (Work.Spaces.mixed j i h) := rfl
    rw [hgoal]
    exact hfin.continuousOn
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i h p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i h p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    exact (((hZ i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))).mul
      continuousOn_wdivsin_Q0).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact (((hM j i h.2).mul hWt)).pow 2
    · exact continuousOn_const

/-! ## Finite-order smoothness of the two summands of the straightened datum -/




/-! ## Honesty of the straightened datum -/


end Work.FTS.EllipticEst.Cores.DiagEstEllT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.Dth_Jeps =====
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
set_option maxHeartbeats 1000000

variable {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {f : Fn}

/-! ## The compact `θ`-region of the shift

For a base angle `θ ∈ (0, π/2)` the shifts `thShift x q` with `x` near `θ` (say
`x ∈ (θ/2, (θ+π/2)/2)`) and `|q| ≤ ε` stay in the compact interval `Kth' θ ε`, strictly
inside `(0, π/2)`.  This is what makes both `pth f` and `∂_θ(thShift · q)` bounded. -/

/-- The support of the shift in `z` is `Kz` (`Kernel.lean`); its `θ`-analogue is
`Kth' θ ε`, the interval swept out by `thShift x q` for `x ∈ [θ/2, (θ+π/2)/2]` and
`|q| ≤ ε`. -/
def Kth' (θ ε : ℝ) : Set ℝ := Set.Icc (thShift (θ / 2) ε) (thShift ((θ + π / 2) / 2) (-ε))

theorem isCompact_Kth' (θ ε : ℝ) : IsCompact (Kth' θ ε) := isCompact_Icc

/-- `thShift` is monotone in its first variable on `(0, π/2)`
(the shift `θ ↦ arctan (tan θ · e^{-p})` of `tan`). -/
theorem thShift_mono_theta {θ₁ θ₂ p : ℝ} (h₁ : θ₁ ∈ Set.Ioo 0 (π / 2))
    (h₂ : θ₂ ∈ Set.Ioo 0 (π / 2)) (h : θ₁ ≤ θ₂) : thShift θ₁ p ≤ thShift θ₂ p := by
  rcases lt_or_eq_of_le h with hlt | heq
  · have ht : Real.tan θ₁ * Real.exp (-p) ≤ Real.tan θ₂ * Real.exp (-p) :=
      mul_le_mul_of_nonneg_right
        (le_of_lt (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [h₁.1, Real.pi_pos])
          h₂.2 hlt))
        (Real.exp_pos _).le
    exact Real.arctan_mono ht
  · simp [heq]

theorem mem_Ioo_half {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : θ / 2 ∈ Set.Ioo 0 (π / 2) :=
  ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem mem_Ioo_halfpi {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (θ + π / 2) / 2 ∈ Set.Ioo 0 (π / 2) :=
  ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩

/-- The shifted angle belongs to the compact region `Kth' θ ε`. -/
theorem thShift_mem_Kth' {θ x q ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hx : x ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2)) (hq : |q| ≤ ε) :
    thShift x q ∈ Kth' θ ε := by
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  have hx2 : x ∈ Set.Ioo 0 (π / 2) :=
    ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ.2, Real.pi_pos]⟩
  exact ⟨le_trans (thShift_mono_theta (mem_Ioo_half hθ) hx2 hx.1.le) (thShift_anti hx2 hq2),
    le_trans (thShift_anti hx2 hq1) (thShift_mono_theta hx2 (mem_Ioo_halfpi hθ) hx.2.le)⟩

/-- `Kth' θ ε` lies strictly inside the open quadrant in the `θ`-variable. -/
theorem Kth'_subset {θ ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Kth' θ ε ⊆ Set.Ioo 0 (π / 2) := by
  intro _y hy
  exact ⟨lt_of_lt_of_le (thShift_mem (mem_Ioo_half hθ)).1 hy.1,
    lt_of_le_of_lt hy.2 (thShift_mem (mem_Ioo_halfpi hθ)).2⟩

/-- The product region of the two shifts is contained in the open quadrant. -/
theorem Kz_prod_Kth'_subset_Quad {z θ ε : ℝ} (hz : 0 < z) (hε : 0 < ε)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Kz z ε ×ˢ Kth' θ ε ⊆ Quad :=
  fun _y hy => ⟨Kz_subset_pos hz hε hy.1, Kth'_subset hθ hy.2⟩

/-! ## The derivative of the `θ`-shift -/

/-- **The bound on `∂_θ (thShift · q)`** on the compact region: since
`∂_θ (thShift · q) = (1 + (tan θ e^{-q})²)^{-1} · (cos θ)^{-2} e^{-q}`, it is dominated by
`e^{ε} / cos((θ+π/2)/2)²` there. -/
theorem deriv_thShift_bound {θ ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∀ x ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2), ∀ q ∈ Set.Icc (-ε) ε,
      ‖deriv (fun θ' => thShift θ' q) x‖ ≤ Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2 := by
  intro x hx q hq
  obtain ⟨hq1, hq2⟩ := hq
  have hx2 : x ∈ Set.Ioo 0 (π / 2) :=
    ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ.2, Real.pi_pos]⟩
  have hcosx : Real.cos x ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx2.1, Real.pi_pos], hx2.2⟩).ne'
  have hd : deriv (fun θ' => thShift θ' q) x
      = (1 / (1 + (Real.tan x * Real.exp (-q)) ^ 2)) * ((1 / Real.cos x ^ 2) * Real.exp (-q)) := by
    have htan : HasDerivAt (fun θ' => Real.tan θ' * Real.exp (-q))
        ((1 / Real.cos x ^ 2) * Real.exp (-q)) x :=
      (Real.hasDerivAt_tan hcosx).mul_const _
    have harct := (Real.hasDerivAt_arctan (Real.tan x * Real.exp (-q))).comp x htan
    simpa only [thShift, Function.comp_def] using harct.deriv
  rw [hd, norm_mul, norm_mul,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (1 + (Real.tan x * Real.exp (-q)) ^ 2)),
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / Real.cos x ^ 2),
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have hden : (0:ℝ) < 1 + (Real.tan x * Real.exp (-q)) ^ 2 := by positivity
  have ht_le : 1 / (1 + (Real.tan x * Real.exp (-q)) ^ 2) ≤ 1 := by
    rw [div_le_one hden]
    nlinarith [sq_nonneg (Real.tan x * Real.exp (-q))]
  have hcosC : Real.cos ((θ + π / 2) / 2) ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi hx2.1.le (by linarith [hx.2, hθ.2, Real.pi_pos]) hx.2.le
  have hcosCpos : 0 < Real.cos ((θ + π / 2) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hcosxpos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hx2.1, Real.pi_pos], hx2.2⟩
  have hC : (1:ℝ) / Real.cos x ^ 2 ≤ 1 / Real.cos ((θ + π / 2) / 2) ^ 2 := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [hcosC, hcosCpos, hcosxpos]
  have he : Real.exp (-q) ≤ Real.exp ε := Real.exp_le_exp.mpr (by linarith)
  calc (1 / (1 + (Real.tan x * Real.exp (-q)) ^ 2)) * ((1 / Real.cos x ^ 2) * Real.exp (-q))
      ≤ (1 / Real.cos x ^ 2) * Real.exp (-q) :=
        mul_le_of_le_one_left (by positivity) ht_le
    _ ≤ (1 / Real.cos ((θ + π / 2) / 2) ^ 2) * Real.exp ε :=
        mul_le_mul hC he (Real.exp_pos _).le (by positivity)
    _ = Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2 := by ring

/-- **Continuity of `q ↦ ∂_θ (thShift · q)`**: it is `sin(2·thShift θ q)/sin(2θ)`. -/
theorem continuous_deriv_thShift {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Continuous fun q => deriv (fun θ' => thShift θ' q) θ := by
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (x := 2 * θ) (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
    linarith
  have hfun : (fun q => deriv (fun θ' => thShift θ' q) θ)
      = fun q => Real.sin (2 * thShift θ q) / Real.sin (2 * θ) := by
    funext q
    rw [← sin_mul_deriv_thShift hθ q]
    field_simp
  rw [hfun]
  exact (Real.continuous_sin.comp (continuous_const.mul (continuous_thShift θ))).div_const _

/-! ## The `θ`-derivative under the `p`-integral -/

/-- **The dominated-convergence computation of the `θ`-derivative.**  For a profile which is
`C¹` on the open quadrant (with continuous `θ`-derivative there), the `p`-integral form of
`J_ε f` at the radius `z` is differentiable in `θ`, with the integral of the derivative of the
integrand as derivative. -/
theorem hasDerivAt_integral_Jeps_th (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Quad)
    (hdf : ContinuousOn (Function.uncurry (Work.Spaces.pth f)) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)))
      (∫ p : ℝ × ℝ, Jker ρ ε p *
        (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε))) θ := by
  have hx0 : θ ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hsub : Set.Ioo (θ / 2) ((θ + π / 2) / 2) ⊆ Set.Ioo 0 (π / 2) :=
    fun x hx => ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ.2, Real.pi_pos]⟩
  have hmem : ∀ x ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2), ∀ p : ℝ × ℝ,
      p ∈ Metric.closedBall (0 : ℝ × ℝ) ε → (zShift z p.1, thShift x p.2) ∈ Quad := by
    intro x hx p hp
    have hp' : max |p.1| |p.2| ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hp
    exact ⟨Kz_subset_pos hz hε
        (zShift_mem_Kz (self_mem_Ioo_div_two hz) (le_trans (le_max_left _ _) hp')),
      Kth'_subset hθ (thShift_mem_Kth' hθ hx (le_trans (le_max_right _ _) hp'))⟩
  obtain ⟨C, hC⟩ := (isCompact_Kz z ε).prod (isCompact_Kth' θ ε) |>.exists_bound_of_continuousOn
    (hdf.mono (Kz_prod_Kth'_subset_Quad hz hε hθ))
  have hCs : ∀ x ∈ Set.Ioo (θ / 2) ((θ + π / 2) / 2), ∀ p : ℝ × ℝ,
      p ∈ Metric.closedBall (0 : ℝ × ℝ) ε →
        ‖Work.Spaces.pth f (zShift z p.1) (thShift x p.2)‖ ≤ C := by
    intro x hx p hp
    have hp' : max |p.1| |p.2| ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hp
    exact hC (zShift z p.1, thShift x p.2)
      ⟨zShift_mem_Kz (self_mem_Ioo_div_two hz) (le_trans (le_max_left _ _) hp'),
        thShift_mem_Kth' hθ hx (le_trans (le_max_right _ _) hp')⟩
  have hctrl := continuous_shift_pair z θ
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)) (𝕜 := ℝ)
    (F := fun x p => Jker ρ ε p * f (zShift z p.1) (thShift x p.2))
    (F' := fun x p => Jker ρ ε p * (Work.Spaces.pth f (zShift z p.1) (thShift x p.2) *
      deriv (fun θ' => thShift θ' p.2) x))
    (bound := fun p => (C * (Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2)) * ‖Jker ρ ε p‖)
    (x₀ := θ) (s := Set.Ioo (θ / 2) ((θ + π / 2) / 2)) (isOpen_Ioo.mem_nhds hx0)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [isOpen_Ioo.mem_nhds hx0] with x hx
    have hctrl' : Continuous fun p : ℝ × ℝ => (zShift z p.1, thShift x p.2) :=
      continuous_shift_pair z x
    have hcont : ContinuousOn (fun p : ℝ × ℝ => f (zShift z p.1) (thShift x p.2))
        (Metric.closedBall 0 ε) :=
      hf.continuousOn.comp hctrl'.continuousOn (fun p hp => hmem x hx p hp)
    exact (integrableOn_Jker_mul_ball hρ hε hcont).aestronglyMeasurable
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => f (zShift z p.1) (thShift θ p.2))
        (Metric.closedBall 0 ε) :=
      hf.continuousOn.comp hctrl.continuousOn (fun p hp => hmem θ hx0 p hp)
    exact integrableOn_Jker_mul_ball hρ hε hcont
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
        deriv (fun θ' => thShift θ' p.2) θ) (Metric.closedBall 0 ε) :=
      (hdf.comp hctrl.continuousOn (fun p hp => hmem θ hx0 p hp)).mul
        (((continuous_deriv_thShift hθ).comp continuous_snd).continuousOn)
    exact (integrableOn_Jker_mul_ball hρ hε hcont).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_closedBall]
    refine Eventually.of_forall fun a ha x hx => ?_
    have ha' : max |a.1| |a.2| ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using ha
    have ha2 : a.2 ∈ Set.Icc (-ε) ε := by
      rw [Set.mem_Icc]
      exact abs_le.mp (le_trans (le_max_right |a.1| |a.2|) ha')
    have h2 : ‖Work.Spaces.pth f (zShift z a.1) (thShift x a.2)‖ ≤ C := hCs x hx a ha
    have h3 : ‖deriv (fun θ' => thShift θ' a.2) x‖
        ≤ Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2 := deriv_thShift_bound hθ x hx a.2 ha2
    rw [norm_mul, norm_mul]
    calc ‖Jker ρ ε a‖ * (‖Work.Spaces.pth f (zShift z a.1) (thShift x a.2)‖ *
            ‖deriv (fun θ' => thShift θ' a.2) x‖)
        ≤ ‖Jker ρ ε a‖ * (C * (Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (norm_nonneg _) (le_trans (norm_nonneg _) h2))
            (norm_nonneg _)
      _ = (C * (Real.exp ε / Real.cos ((θ + π / 2) / 2) ^ 2)) * ‖Jker ρ ε a‖ := by ring
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖Jker ρ ε p‖) (Metric.closedBall 0 ε) :=
      (Jker_continuous hρ ε).norm.continuousOn
    exact ((hcont.integrableOn_compact (isCompact_closedBall (0 : ℝ × ℝ) ε)).const_mul _)
  · refine Eventually.of_forall fun a x hx => ?_
    have hquad : (zShift z a.1, thShift x a.2) ∈ Quad :=
      ⟨zShift_pos hz, thShift_mem (hsub hx)⟩
    have hd_on : DifferentiableOn ℝ (Function.uncurry f) Quad := hf.differentiableOn (by norm_num)
    have hd_at : DifferentiableAt ℝ (Function.uncurry f) (zShift z a.1, thShift x a.2) :=
      hd_on.differentiableAt (isOpen_Quad.mem_nhds hquad)
    have hpr : DifferentiableAt ℝ (fun y : ℝ => (zShift z a.1, y)) (thShift x a.2) := by fun_prop
    have hslice : HasDerivAt (fun y : ℝ => f (zShift z a.1) y)
        (Work.Spaces.pth f (zShift z a.1) (thShift x a.2)) (thShift x a.2) := by
      have h := (hd_at.comp (thShift x a.2) hpr).hasDerivAt
      simpa only [Function.comp_def, Function.uncurry, Work.Spaces.pth] using h
    have hcosx : Real.cos x ≠ 0 :=
      ((Real.cos_pos_of_mem_Ioo ⟨by linarith [(hsub hx).1, Real.pi_pos], (hsub hx).2⟩)).ne'
    have hdtan : HasDerivAt (fun y : ℝ => Real.tan y * Real.exp (-a.2))
        ((1 / Real.cos x ^ 2) * Real.exp (-a.2)) x := (Real.hasDerivAt_tan hcosx).mul_const _
    have hdarc : HasDerivAt (fun y : ℝ => thShift y a.2)
        ((1 / (1 + (Real.tan x * Real.exp (-a.2)) ^ 2)) *
          ((1 / Real.cos x ^ 2) * Real.exp (-a.2))) x := by
      have h := (Real.hasDerivAt_arctan (Real.tan x * Real.exp (-a.2))).comp x hdtan
      simpa only [thShift, Function.comp_def] using h
    have hx1 : HasDerivAt (fun y : ℝ => thShift y a.2) (deriv (fun θ' => thShift θ' a.2) x) x :=
      hdarc.congr_deriv hdarc.deriv.symm
    exact (hslice.comp x hx1).const_mul (Jker ρ ε a)

/-- **`E1`, `θ`-half: `J_ε` commutes with `∂_θ` under the integral** (the `p`-integral form). -/
theorem Jeps_deriv_th (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Quad)
    (hdf : ContinuousOn (Function.uncurry (Work.Spaces.pth f)) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun θ' => Jeps ρ ε f z θ') θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
            deriv (fun θ' => thShift θ' p.2) θ) := by
  have hd := hasDerivAt_integral_Jeps_th hρ hε hf hdf hz hθ
  have hballF : (fun θ' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)))
      = fun θ' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2) := by
    funext θ'
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2))
      (fun p hp => by rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])
  have hballG : (∫ p : ℝ × ℝ, Jker ρ ε p *
        (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ))
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
        (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Jker ρ ε p *
        (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ))
      (fun p hp => by rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])).symm
  have hev : (fun θ' => Jeps ρ ε f z θ')
      =ᶠ[𝓝 θ] fun θ' => ∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ' p.2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact Jeps_eq_integral ρ ε f hz hθ'
  rw [hballF] at hd
  rw [hev.deriv_eq, hd.deriv]
  exact hballG.symm

/-- **`E1`, `θ`-half, `D_θ`-form: `D_θ (J_ε f) = J_ε (D_θ f)` on the open quadrant.** -/
theorem Dth_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ 1 (Function.uncurry f) Quad)
    (hdf : ContinuousOn (Function.uncurry (Work.Spaces.pth f)) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Jeps ρ ε f) z θ = Jeps ρ ε (Work.Spaces.Dth f) z θ := by
  have hd : deriv (fun θ' => (Jeps ρ ε f) z θ') θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Work.Spaces.pth f (zShift z p.1) (thShift θ p.2) *
            deriv (fun θ' => thShift θ' p.2) θ) :=
    Jeps_deriv_th hρ hε hf hdf hz hθ
  have hJ : Jeps ρ ε (Work.Spaces.Dth f) z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p *
          (Real.sin (2 * thShift θ p.2) *
            Work.Spaces.pth f (zShift z p.1) (thShift θ p.2)) := by
    have hD : Work.Spaces.Dth f
        = fun z' θ' => Real.sin (2 * θ') * Work.Spaces.pth f z' θ' := rfl
    rw [hD, Jeps_eq_integral ρ ε _ hz hθ]
  rw [hJ]
  show Real.sin (2 * θ) * deriv (fun θ' => (Jeps ρ ε f) z θ') θ = _
  rw [hd]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have hsin := sin_mul_deriv_thShift hθ p.2
  simp only [Work.Spaces.pth]
  calc Real.sin (2 * θ) * (Jker ρ ε p * (deriv (fun θ' => f (zShift z p.1) θ') (thShift θ p.2) *
          deriv (fun θ' => thShift θ' p.2) θ))
      = Jker ρ ε p * (deriv (fun θ' => f (zShift z p.1) θ') (thShift θ p.2) *
          (Real.sin (2 * θ) * deriv (fun θ' => thShift θ' p.2) θ)) := by ring
    _ = Jker ρ ε p * (deriv (fun θ' => f (zShift z p.1) θ') (thShift θ p.2) *
          Real.sin (2 * thShift θ p.2)) := by rw [hsin]
    _ = Jker ρ ε p * (Real.sin (2 * thShift θ p.2) *
          deriv (fun θ' => f (zShift z p.1) θ') (thShift θ p.2)) := by ring

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

open Work.FTS.StrongEps.JepsHkMem (aestronglyMeasurable_of_eq_zero_off shift_mem_Quad')

set_option maxHeartbeats 1000000

/-! ## A continuity fact for the `θ`-shift -/


/-! ## Continuity of the parametric integral at an interior point -/


/-! ## The requested statement -/


end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
end
end
