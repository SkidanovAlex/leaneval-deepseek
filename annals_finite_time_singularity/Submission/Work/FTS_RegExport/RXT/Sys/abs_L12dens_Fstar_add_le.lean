import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.ConstructionInstance.profileData_inhabited
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBasic
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.LWP.VorticityAPI
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.ConstructionInstance.bkm_divergence_of_st5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The Biot–Savart identity for the ansatz, on the physical interval.**  On `[0,T)` the
vorticity of the ansatz velocity is the constructed self-similar field `solVort P` (this is
`Tie.vorticity_ansatzV` transported from the window `preWindow T = (-2,T)` to `[0,T)`). -/
theorem vorticity_ansatzV_Ico {α : NNReal} (P : ProfileData α) (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ t ∈ Set.Ico 0 P.T, ∀ x : R3,
      vorticity (fun y => ansatzV P y t) x = solVort P x t :=
  fun t ht x => vorticity_ansatzV P hlaw t ⟨by linarith [ht.1], ht.2⟩ x

/-- **The `St5` lower bound for the ansatz**: `‖ω(·,t)‖_∞ ≥ (c₀α/2)/(T-t)` on `[0,T)`, where
`c₀ = c₀star α` is the explicit profile constant (`ProfileData.c₀star`).

The point where the vorticity is large is the `St5` witness of `Reduced.solVort_hansatz`
(the maximising profile scale `z = 1`, where the cut-off is transparent because
`λ̄(t)^{1/p} ≤ (2T)^{1/p} ≤ L`); the two remaining ingredients are the two-sided modulation bound
`λ̄(t) ≤ 2(T-t)` (`ProfileData.hlam_le`) and the positivity of `λ̄` on the window
(`ProfileData.hlam`). -/
theorem ansatzV_vortLinfLower {α : NNReal} (P : ProfileData α) (hlaw : Work.LWP.BiotSavartLaw) :
    Work.StabilityFar.VortLinfLower (ansatzV P) P.T (c₀star α * (α : ℝ) / 2) := by
  have hα : 0 < (α : ℝ) := P.hα
  have hc₀ : 0 < c₀star α := c₀star_pos P.hα P.hα13
  have hvort := vorticity_ansatzV_Ico P hlaw
  refine Work.StabilityFar.vortLinfLower_of_ansatz (u := ansatzV P) (T := P.T)
    (c₀ := c₀star α) (α := (α : ℝ)) (lam := P.lam) ?_ ?_ hc₀ hα ?_ ?_
  · -- `λ̄ > 0` on `[0,T)`
    intro t ht
    exact P.hlam t ⟨by linarith [ht.1], ht.2⟩
  · -- `λ̄(t) ≤ 2(T-t)` on `[0,T)`
    intro t ht
    exact P.hlam_le t ht
  · -- the slice sup is honest: bounded by `M/λ̄(t)`
    intro t ht
    refine ⟨P.M / P.lam t, ?_⟩
    rintro _ ⟨x, rfl⟩
    change ‖vorticity (fun y => ansatzV P y t) x‖ ≤ P.M / P.lam t
    rw [hvort t ht x]
    have hlt : 0 < P.lam t := P.hlam t ⟨by linarith [ht.1], ht.2⟩
    exact (le_div_iff₀ hlt).mpr
      (by rw [mul_comm]; exact solVort_bdd P t ⟨by linarith [ht.1], ht.2⟩ x)
  · -- the pointwise lower bound: the `St5` witness of the construction
    intro t ht
    obtain ⟨x, hx⟩ := solVort_hansatz P t ht
    exact ⟨x, by rwa [hvort t ht x]⟩

/-- **The quantitative half of the maximality residual**: the BKM integral of the self-similar
ansatz diverges as `t → T⁻`.

This is `St5` (`Work.StabilityFar.bkm_divergence_of_vortLinfLower`) applied to the two inputs
derived from the profile data and the Biot–Savart law: the pointwise lower bound
`ansatzV_vortLinfLower` and the interval-integrability of `t ↦ ‖ω(·,t)‖_∞`
(`intervalIntegrable_vortLInf_ansatzV`, from the continuity of that function on the strips). -/
theorem bkm_divergence_of_st5 {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlaw : Work.LWP.BiotSavartLaw) :
    Filter.Tendsto (Work.LWP.bkm (Work.ConstructionInstance.ansatzV P))
      (nhdsWithin P.T (Set.Iio P.T)) Filter.atTop := by
  have hc : 0 < c₀star α * (α : ℝ) / 2 := by
    have h1 : 0 < c₀star α := c₀star_pos P.hα P.hα13
    have h2 : 0 < (α : ℝ) := P.hα
    positivity
  exact Work.StabilityFar.bkm_divergence_of_vortLinfLower P.hT hc
    (ansatzV_vortLinfLower P hlaw) (intervalIntegrable_vortLInf_ansatzV P hlaw)

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.selfSimTimeHolderDeriv_profileData_inhabited =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

/-! ## The second `z`-derivative of the fundamental-model profile `F_*` -/

/-- `z ↦ 2(1-z)/(1+z)³`, the value of `deriv F_*` away from `z = -1`. -/
def FstarSlope (z : ℝ) : ℝ := 2 * (1 - z) / (1 + z) ^ 3

/-- `FstarSlope` is differentiable with derivative `4(z-2)/(1+z)⁴`. -/
theorem hasDerivAt_FstarSlope (z : ℝ) (hz : -1 < z) :
    HasDerivAt FstarSlope (4 * (z - 2) / (1 + z) ^ 4) z := by
  have hne : (1 + z) ^ 3 ≠ 0 := by
    have : (0 : ℝ) < 1 + z := by linarith
    positivity
  have hnum : HasDerivAt (fun z' : ℝ => 2 * (1 - z')) (-2) z := by
    have h : HasDerivAt (fun z' : ℝ => 1 - z') (-1) z := by
      simpa using (hasDerivAt_id z).const_sub 1
    simpa using h.const_mul 2
  have hden : HasDerivAt (fun z' : ℝ => (1 + z') ^ 3) (3 * (1 + z) ^ 2) z := by
    have h : HasDerivAt (fun z' : ℝ => 1 + z') 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    convert h.pow 3 using 1
    ring_nf
  have h := hnum.div hden hne
  unfold FstarSlope
  convert h using 1
  field_simp
  ring

/-- `deriv F_*` agrees with `FstarSlope` near any point of `(-1,∞)`. -/
theorem eventuallyEq_deriv_FM_Fstar (z : ℝ) (hz : -1 < z) :
    deriv Work.FM.Fstar =ᶠ[𝓝 z] FstarSlope := by
  refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) ?_
  intro z' hz'
  rw [FstarSlope, Work.FM.deriv_Fstar z' hz']

/-- `deriv F_*` is differentiable away from `z = -1`. -/
theorem hasDerivAt_deriv_FM_Fstar (z : ℝ) (hz : -1 < z) :
    HasDerivAt (deriv Work.FM.Fstar) (4 * (z - 2) / (1 + z) ^ 4) z :=
  (hasDerivAt_FstarSlope z hz).congr_of_eventuallyEq (eventuallyEq_deriv_FM_Fstar z hz)

/-- **The second derivative of the fundamental-model profile**: `∂_z²F_*(z) = 4(z-2)/(1+z)⁴`. -/
theorem deriv_deriv_FM_Fstar (z : ℝ) (hz : -1 < z) :
    deriv (deriv Work.FM.Fstar) z = 4 * (z - 2) / (1 + z) ^ 4 :=
  (hasDerivAt_deriv_FM_Fstar z hz).deriv

/-! ## The profile with the zero perturbation -/

/-- The angular coefficient of the profile with zero perturbation: on `θ ≥ 0` it is
`p·Γ(θ)/c(p)`, and `θ ↦ -θ` on the odd branch. -/
def thetaCoeff (p θ : ℝ) : ℝ :=
  if 0 ≤ θ then p * (Work.Spaces.Gam p θ / Work.Spaces.c p)
  else -(p * (Work.Spaces.Gam p (-θ) / Work.Spaces.c p))

/-- With the zero perturbation, the profile is the angular coefficient times `F_*`. -/
theorem profile_zeroPert_eq (p θ z : ℝ) :
    profile p (fun _ _ => (0 : ℝ)) z θ = thetaCoeff p θ * Work.FM.Fstar z := by
  rw [thetaCoeff]
  rcases le_or_gt 0 θ with h | h
  · rw [profile_of_nonneg h, ite_eq_left h, Work.Construction.Fstar]; ring
  · rw [profile_of_neg (not_le.mpr h), ite_eq_right (not_le.mpr h), Work.Construction.Fstar]; ring

/-- The `z`-derivative of the profile with zero perturbation. -/
theorem pz_profile_zeroPert (p θ z : ℝ) :
    Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ))) z θ
      = thetaCoeff p θ * deriv Work.FM.Fstar z := by
  rw [Work.Spaces.pz]
  have hfun : (fun z' => profile p (fun _ _ => (0 : ℝ)) z' θ)
      = fun z' => thetaCoeff p θ * Work.FM.Fstar z' :=
    funext (fun z' => profile_zeroPert_eq p θ z')
  rw [hfun, deriv_const_mul_field]

/-- The second `z`-derivative of the profile with zero perturbation. -/
theorem pz_pz_profile_zeroPert (p θ z : ℝ) :
    Work.Spaces.pz (Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ)))) z θ
      = thetaCoeff p θ * deriv (deriv Work.FM.Fstar) z := by
  rw [Work.Spaces.pz]
  have hfun : (fun z' => Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ))) z' θ)
      = fun z' => thetaCoeff p θ * deriv Work.FM.Fstar z' :=
    funext (fun z' => pz_profile_zeroPert p θ z')
  rw [hfun, deriv_const_mul_field]

/-- **The profile with zero perturbation is twice differentiable in `z`** with the second
`z`-derivative given by `pz (pz F)`. -/
theorem hasDerivAt_pz_profile_zeroPert {p θ z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ))) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ)))) z θ) z := by
  have hz1 : -1 < z := by linarith
  have hfun : (fun z' => Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ))) z' θ)
      = fun z' => thetaCoeff p θ * deriv Work.FM.Fstar z' :=
    funext (fun z' => pz_profile_zeroPert p θ z')
  have h1 : HasDerivAt (fun z' => thetaCoeff p θ * deriv Work.FM.Fstar z')
      (thetaCoeff p θ * (4 * (z - 2) / (1 + z) ^ 4)) z :=
    (hasDerivAt_deriv_FM_Fstar z hz1).const_mul (thetaCoeff p θ)
  rw [hfun, pz_pz_profile_zeroPert p θ z, deriv_deriv_FM_Fstar z hz1]
  exact h1

/-- **The weighted second-derivative box of the profile with zero perturbation**:
`|z²·∂_z²F| ≤ 80` on the quadrant, for `0 < p ≤ 1`. -/
theorem zsq_pz_pz_profile_zeroPert_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ)))) z θ| ≤ 80 := by
  intro z θ hz hθ
  rw [pz_pz_profile_zeroPert]
  have hz1 : -1 < z := by linarith
  rw [deriv_deriv_FM_Fstar z hz1]
  have hθnn : 0 ≤ θ := hθ.1
  have hk_eq : thetaCoeff p θ = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) := by
    rw [thetaCoeff, ite_eq_left hθnn]
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hGb := Work.Spaces.Gam_bounds p θ hp hθ
  have hkbound : |thetaCoeff p θ| ≤ 10 := by
    rw [hk_eq, abs_of_nonneg (mul_nonneg hp.le (div_nonneg hGb.1 hcpos.le))]
    have h1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
      rw [div_le_iff₀ hcpos]; nlinarith [hGb.2]
    nlinarith [hp1, hGb.1, hcpos]
  have hkey : z ^ 2 * |z - 2| ≤ 2 * (1 + z) ^ 4 := by
    have h1 : |z - 2| ≤ z + 2 := by
      rw [abs_le]; constructor <;> linarith
    calc z ^ 2 * |z - 2| ≤ z ^ 2 * (z + 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg z)
      _ ≤ 2 * (1 + z) ^ 4 := by nlinarith [sq_nonneg z, sq_nonneg (z ^ 2)]
  have h2 : |z ^ 2 * (4 * (z - 2) / (1 + z) ^ 4)| ≤ 8 := by
    have hpos : (0 : ℝ) < (1 + z) ^ 4 := by positivity
    rw [abs_mul, abs_of_nonneg (sq_nonneg z), abs_div, abs_of_pos hpos,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hreq : z ^ 2 * (4 * |z - 2| / (1 + z) ^ 4)
        = 4 * (z ^ 2 * |z - 2|) / (1 + z) ^ 4 := by ring
    rw [hreq, div_le_iff₀ hpos]
    nlinarith [hkey]
  calc |z ^ 2 * (thetaCoeff p θ * (4 * (z - 2) / (1 + z) ^ 4))|
      = |thetaCoeff p θ| * |z ^ 2 * (4 * (z - 2) / (1 + z) ^ 4)| := by
        rw [show z ^ 2 * (thetaCoeff p θ * (4 * (z - 2) / (1 + z) ^ 4))
              = thetaCoeff p θ * (z ^ 2 * (4 * (z - 2) / (1 + z) ^ 4)) by ring, abs_mul]
    _ ≤ 10 * 8 := by apply mul_le_mul hkbound h2 (abs_nonneg _) (by norm_num)
    _ = 80 := by norm_num

/-! ## The requested theorem -/


end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.Compactness =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false









end Work.FTS.Galerkin
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.DthFstarPoint =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1


end Work.FTS.Nonlinear.Pieces.Rl1
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNIdent =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.StrongEps.ClassCRHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem PB_eq_NBlk {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (w Φs Φg : Fn) :
    ∀ k ∈ Finset.range 20, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg k z θ = NBlk α w Φs Φg k z θ := by
  have h2ne : (1 : ℕ) + 1 ≠ 0 := by norm_num
  have hid0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 0 z θ = NBlk α w Φs Φg 0 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N1gg]
    ring
  have hid1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 1 z θ = NBlk α w Φs Φg 1 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N1gs]
    ring
  have hid2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 2 z θ = NBlk α w Φs Φg 2 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N1sg]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid3 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 3 z θ = NBlk α w Φs Φg 3 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N1ss]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid4 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 4 z θ = NBlk α w Φs Φg 4 z θ := by
    intro z θ _ hθ0 hθ1
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N2gg, Work.Spaces.Dth, Work.Construction.s2]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid5 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 5 z θ = NBlk α w Φs Φg 5 z θ := by
    intro z θ _ hθ0 hθ1
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N2gs, Work.Spaces.Dth, Work.Construction.s2]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 6 z θ = NBlk α w Φs Φg 6 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N2sg, Work.Spaces.Dth, Work.Construction.s2]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid7 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 7 z θ = NBlk α w Φs Φg 7 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hs : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N2ss, Work.Spaces.Dth, Work.Construction.s2]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid8 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 8 z θ = NBlk α w Φs Φg 8 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N3gg]
    ring
  have hid9 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 9 z θ = NBlk α w Φs Φg 9 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N3gs]
    ring
  have hid10 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 10 z θ = NBlk α w Φs Φg 10 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N3sg]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid11 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 11 z θ = NBlk α w Φs Φg 11 z θ := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    simp only [PB, NBlk, Work.FTS.Nonlin.N3ss]
    field_simp
    all_goals (try ring_nf)
    all_goals (try (intro _; trivial))
  have hid12 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 12 z θ = NBlk α w Φs Φg 12 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N4gg]
    ring
  have hid13 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 13 z θ = NBlk α w Φs Φg 13 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N4gs, Work.Spaces.Dth, Work.Construction.s2]
    ring
  have hid14 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 14 z θ = NBlk α w Φs Φg 14 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N4sg, Work.Spaces.Dth,
      Work.FTS.Nonlin.FK_Fstar hα0 hα1, Work.Spaces.hKer_apply]
    ring
  have hid15 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 15 z θ = NBlk α w Φs Φg 15 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N4ss, Work.Spaces.Dth, Work.Construction.s2]
    ring
  have hid16 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 16 z θ = NBlk α w Φs Φg 16 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N5gg]
    ring
  have hid17 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 17 z θ = NBlk α w Φs Φg 17 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N5gs]
    ring
  have hid18 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 18 z θ = NBlk α w Φs Φg 18 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N5sg]
    ring
  have hid19 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      PB α w Φs Φg 19 z θ = NBlk α w Φs Φg 19 z θ := by
    intro z θ _ _ _
    simp only [PB, NBlk, Work.FTS.Nonlin.N5ss]
    ring
  intro k hk z θ hz hθ0 hθ1
  have hk20 : k < 20 := Finset.mem_range.mp hk
  interval_cases k <;>
    first
      | exact hid0 z θ hz hθ0 hθ1
      | exact hid1 z θ hz hθ0 hθ1
      | exact hid2 z θ hz hθ0 hθ1
      | exact hid3 z θ hz hθ0 hθ1
      | exact hid4 z θ hz hθ0 hθ1
      | exact hid5 z θ hz hθ0 hθ1
      | exact hid6 z θ hz hθ0 hθ1
      | exact hid7 z θ hz hθ0 hθ1
      | exact hid8 z θ hz hθ0 hθ1
      | exact hid9 z θ hz hθ0 hθ1
      | exact hid10 z θ hz hθ0 hθ1
      | exact hid11 z θ hz hθ0 hθ1
      | exact hid12 z θ hz hθ0 hθ1
      | exact hid13 z θ hz hθ0 hθ1
      | exact hid14 z θ hz hθ0 hθ1
      | exact hid15 z θ hz hθ0 hθ1
      | exact hid16 z θ hz hθ0 hθ1
      | exact hid17 z θ hz hθ0 hθ1
      | exact hid18 z θ hz hθ0 hθ1
      | exact hid19 z θ hz hθ0 hθ1

end Work.FTS.StrongEps.ClassCRHS
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.Auxiliary.abs_L12_zero_le_of_pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L.aux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Two elementary integrals -/

/-- The integral of a constant over `Iθ = [0,π/2]` is the constant times `π/2`. -/
private theorem integral_Iθ_const (c : ℝ) :
    (∫ _θ in Work.Spaces.Iθ, c) = c * (Real.pi / 2) := by
  rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- `∫_0^∞ (1+s)^{-3/2} ds = 2`, with the antiderivative `-2(1+s)^{-1/2}`. -/
private theorem integral_Ioi_one_add_rpow :
    (∫ s : ℝ in Set.Ioi (0 : ℝ), (1 + s) ^ (-(3 : ℝ) / 2)) = 2 := by
  rw [show (∫ s : ℝ in Set.Ioi (0 : ℝ), (1 + s) ^ (-(3 : ℝ) / 2))
      = ∫ s : ℝ in Set.Ioi (0 : ℝ), (s + 1) ^ (-(3 : ℝ) / 2) from
        setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [add_comm]]
  have hd : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1) / (-(3 : ℝ) / 2 + 1))
        ((x + 1) ^ (-(3 : ℝ) / 2)) x := by
    intro x hx
    have hne : x + 1 ≠ 0 := by linarith [Set.mem_Ici.mp hx]
    have h1 : HasDerivAt (fun t : ℝ => t + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h2 : HasDerivAt (fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1))
        (1 * (-(3 : ℝ) / 2 + 1) * (x + 1) ^ (-(3 : ℝ) / 2 + 1 - 1)) x :=
      h1.rpow_const (Or.inl hne)
    have h3 := h2.div_const (-(3 : ℝ) / 2 + 1)
    convert h3 using 1
    ring_nf
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ (x + 1) ^ (-(3 : ℝ) / 2) :=
    fun x hx => Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp hx]) _
  have hlim : Filter.Tendsto
      (fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1) / (-(3 : ℝ) / 2 + 1))
      Filter.atTop (nhds 0) := by
    have hb : Filter.Tendsto (fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1))
        Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) Filter.atTop (nhds 0) :=
        tendsto_rpow_neg_atTop (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)
      have h3 : Filter.Tendsto (fun t : ℝ => (t + 1) ^ (-(1 / 2 : ℝ))) Filter.atTop (nhds 0) := by
        simpa only [Function.comp_def, id_eq] using
          h2.comp (Filter.tendsto_atTop_add_const_right _ 1 tendsto_id)
      convert h3 using 1
      ext t
      rw [show (-(3 : ℝ) / 2 + 1) = -(1 / 2 : ℝ) by norm_num]
    simpa using hb.div_const ((-(3 : ℝ) / 2 + 1))
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (g := fun t : ℝ => (t + 1) ^ (-(3 : ℝ) / 2 + 1) / (-(3 : ℝ) / 2 + 1))
    (g' := fun x : ℝ => (x + 1) ^ (-(3 : ℝ) / 2)) hd hpos hlim
  rw [key]
  norm_num

/-! ## The angular mean inequality for the density -/

/-- **The pointwise bound on the density of `L₁₂`.**  Under the standing majorant
`|f z θ| ≤ M · Rwt z` on `(0,∞) × Iθ` and for `s > 0`,

  `‖L₁₂dens(f)(s)‖ ≤ 3·(π/2)·(M · Rwt s / s)`,

from `|K| ≤ 3`, `vol(Iθ) = π/2` and the pointwise domination of the angular integrand. -/
private theorem dens_bound {f : ℝ → ℝ → ℝ} {M : ℝ}
    (hb : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |f z θ| ≤ M * Work.FTS_RegExport.RXT.L12Iter.Rwt z)
    {s : ℝ} (hs : 0 < s) :
    ‖Work.FM.L12dens Work.Spaces.K f s‖
      ≤ 3 * (Real.pi / 2) * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.Spaces.K θ * f s θ / s‖
        ≤ 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by
    intro θ hθ
    have hf : |f s θ| ≤ M * Work.FTS_RegExport.RXT.L12Iter.Rwt s := hb s θ hs hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three θ
    have hnum : |Work.Spaces.K θ| * |f s θ|
        ≤ 3 * (M * Work.FTS_RegExport.RXT.L12Iter.Rwt s) :=
      mul_le_mul hK hf (abs_nonneg _) (by norm_num)
    have h2 : 3 * (M * Work.FTS_RegExport.RXT.L12Iter.Rwt s) / s
        = 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by ring
    calc ‖Work.Spaces.K θ * f s θ / s‖ = |Work.Spaces.K θ| * |f s θ| / s := by
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hs]
      _ ≤ 3 * (M * Work.FTS_RegExport.RXT.L12Iter.Rwt s) / s :=
          div_le_div_of_nonneg_right hnum hs.le
      _ = 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := h2
  have hint : MeasureTheory.Integrable
      (fun _ : ℝ => 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)))
      (volume.restrict Work.Spaces.Iθ) := MeasureTheory.integrable_const _
  have h1 : ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ / s‖
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by
    refine MeasureTheory.norm_integral_le_of_norm_le
      (g := fun _ => 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s))) hint ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt θ hθ)
  have h2 : (∫ θ in Work.Spaces.Iθ, 3 * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)))
      = 3 * (Real.pi / 2) * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := by
    rw [integral_Iθ_const]
    ring
  rw [Work.FM.L12dens]
  calc ‖∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), Work.Spaces.K θ * f s θ / s‖
      = ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ / s‖ := rfl
    _ ≤ _ := h1
    _ = _ := h2

/-! ## The main bound -/

theorem abs_L12_zero_le_of_pointwise {f : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |f z θ| ≤ M * Work.FTS_RegExport.RXT.L12Iter.Rwt z) :
    |Work.Construction.L12 f 0| ≤ 3 * (Real.pi / 2) * M * 2 := by
  -- the density is dominated by `3·(π/2)·M·(1+s)^{-3/2}`
  have hle : ∀ s ∈ Set.Ioi (0 : ℝ),
      ‖Work.FM.L12dens Work.Spaces.K f s‖
        ≤ 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2) := by
    intro s hs
    have hs0 : 0 < s := hs
    have h1 := dens_bound hb hs0
    have h2 : Work.FTS_RegExport.RXT.L12Iter.Rwt s / s
        = s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 :=
      Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs0
    have h3 : s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ (1 + s) ^ (-(3 : ℝ) / 2) := by
      have hbase : (0 : ℝ) < 1 + s := by linarith
      have hroot : s ^ ((1 : ℝ) / 2) ≤ (1 + s) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hs0.le (by linarith) (by norm_num)
      have hdiv : s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2
          ≤ (1 + s) ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 :=
        div_le_div_of_nonneg_right hroot (by positivity)
      have heq : (1 + s) ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 = (1 + s) ^ (-(3 : ℝ) / 2) := by
        rw [← Real.rpow_natCast (1 + s) 2, ← Real.rpow_sub hbase]
        norm_num
      linarith [hdiv, le_of_eq heq]
    calc ‖Work.FM.L12dens Work.Spaces.K f s‖
        ≤ 3 * (Real.pi / 2) * (M * (Work.FTS_RegExport.RXT.L12Iter.Rwt s / s)) := h1
      _ = 3 * (Real.pi / 2) * (M * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by rw [h2]
      _ ≤ 3 * (Real.pi / 2) * (M * ((1 + s) ^ (-(3 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hM) (by positivity)
      _ = 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2) := by ring
  -- the majorant is integrable on `(0,∞)`
  have hmaj : MeasureTheory.Integrable
      (fun s : ℝ => 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h0 : MeasureTheory.Integrable (fun s : ℝ => (s + 1) ^ (-(3 : ℝ) / 2))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      integrableOn_add_rpow_Ioi_of_lt (a := -(3 : ℝ) / 2) (c := 0) (m := 1)
        (by norm_num) (by norm_num)
    have h1 : MeasureTheory.Integrable
        (fun s : ℝ => 3 * (Real.pi / 2) * M * (s + 1) ^ (-(3 : ℝ) / 2))
        (volume.restrict (Set.Ioi (0 : ℝ))) := h0.const_mul _
    refine h1.congr (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    rw [add_comm]
  have hle' : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Work.FM.L12dens Work.Spaces.K f s‖
        ≤ 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hle
  have hmain : ‖∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K f s‖
      ≤ ∫ s in Set.Ioi (0 : ℝ), 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2) :=
    MeasureTheory.norm_integral_le_of_norm_le hmaj hle'
  have hval : (∫ s in Set.Ioi (0 : ℝ), 3 * (Real.pi / 2) * M * (1 + s) ^ (-(3 : ℝ) / 2))
      = 3 * (Real.pi / 2) * M * 2 := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_one_add_rpow]
  have hgoal : |Work.Construction.L12 f 0|
      = ‖∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K f s‖ := by
    rw [Work.Construction.L12, Work.FM.L12, Real.norm_eq_abs]
  rw [hgoal]
  linarith [hmain, le_of_eq hval]

/-! ## The difference (τ-modulus) form -/


end Work.FTS_RegExport.RXR5L.aux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.L12Iter.Tower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.L12Iter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The tower identity.**  Let `f` be `C⁴` on the open quadrant with
`|D_z^k f| ≤ C₀ Rwt` for `k ≤ 2`, and suppose that `∂_z (Qang f k) = Qang f (k+1)/z` for
`k ≤ 1` (this is the content of `QangHasDerivAt`).  Then for `1 ≤ j ≤ 3` and `z > 0`,

  `D_z^j (L₁₂ f)(z) = - Qang f (j-1) z`. -/
theorem DzdIter_L12_eq_neg_Qang {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Rwt z)
    (hQA : ∀ {k : ℕ}, k ≤ 1 → ∀ {w : ℝ}, 0 < w →
      HasDerivAt (fun w => Work.Elliptic.Qang f k w) (Work.Elliptic.Qang f (k + 1) w / w) w)
    {j : ℕ} (hj : 1 ≤ j) (hj3 : j ≤ 3) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z
      = -(Work.Elliptic.Qang f (j - 1) z) := by
  -- level `1`, pointwise on `(0,∞)`
  have h1 : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z) w
        = -(Work.Elliptic.Qang f 0 w) := by
    intro w hw
    have hder := Construction_L12_hasDerivAt (f := f) hC0 h4 hbd hw
    have hval : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z) w
        = w * (-(Work.Construction.L12dens f w)) := by
      show w * deriv (fun z => Work.Construction.L12 f z) w
        = w * (-(Work.Construction.L12dens f w))
      rw [hder.deriv]
    rw [hval]
    have hdens : Work.Construction.L12dens f w = Work.Elliptic.Qang f 0 w / w :=
      L12dens_eq_Qang_zero f w
    rw [hdens, mul_neg, neg_inj, ← mul_div_assoc]
    exact mul_div_cancel_left₀ (Work.Elliptic.Qang f 0 w) (ne_of_gt hw)
  -- the induction step, using the eventual form of the identity at the previous level
  have hstep : ∀ {j : ℕ}, 1 ≤ j → j ≤ 2 → ∀ {z : ℝ}, 0 < z →
      (Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z)
        =ᶠ[𝓝 z] fun u => -(Work.Elliptic.Qang f (j - 1) u)) →
      Work.Elliptic.DzdIter (j + 1) (fun z => Work.Construction.L12 f z) z
        = -(Work.Elliptic.Qang f j z) := by
    intro j hj1 _ z hz' hev
    have hpred : (j - 1) + 1 = j := Nat.succ_pred_eq_of_pos hj1
    have hQA' : HasDerivAt (fun u => Work.Elliptic.Qang f (j - 1) u)
        (Work.Elliptic.Qang f j z / z) z := by
      have h := hQA (k := j - 1) (by omega) hz'
      rwa [hpred] at h
    have hfull : deriv (Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z)) z
        = -(Work.Elliptic.Qang f j z / z) := by
      rw [hev.deriv_eq]
      exact hQA'.neg.deriv
    show z * deriv (Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z)) z
      = -(Work.Elliptic.Qang f j z)
    rw [hfull, mul_neg, neg_inj, ← mul_div_assoc]
    exact mul_div_cancel_left₀ (Work.Elliptic.Qang f j z) (ne_of_gt hz')
  have h2 : ∀ {z : ℝ}, 0 < z →
      Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z) z
        = -(Work.Elliptic.Qang f 1 z) := by
    intro z hz'
    refine hstep (j := 1) (by omega) (by omega) hz' ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz'] with u hu
    exact h1 u hu
  have h3 : ∀ {z : ℝ}, 0 < z →
      Work.Elliptic.DzdIter 3 (fun z => Work.Construction.L12 f z) z
        = -(Work.Elliptic.Qang f 2 z) := by
    intro z hz'
    refine hstep (j := 2) (by omega) (by omega) hz' ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz'] with u hu
    exact h2 hu
  interval_cases j
  · exact h1 z hz
  · exact h2 hz
  · exact h3 hz

end Work.FTS_RegExport.RXT.L12Iter
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.KweightIntegralSub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

set_option autoImplicit false

/-! ## Elementary facts about the weight `K` and the interval `Iθ` -/

/-- `|K(θ)| = |3 sinθ cos²θ| ≤ 3` for every real `θ` (in particular on `Iθ`). -/
private theorem abs_K_le_three_prv (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hb : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg hb]
  have h1 : |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 := by
    calc |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 * 1 := mul_le_mul hs hc hb (by norm_num)
      _ = 1 := by ring
  nlinarith [h1, abs_nonneg (Real.sin θ)]

/-- The Lebesgue measure of `Iθ = [0, π/2]` is `π/2`. -/
private theorem volume_real_Iθ : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [MeasureTheory.Measure.real_def, Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
  ring

/-- The Lebesgue measure of `Iθ = [0, π/2]` is finite. -/
private theorem volume_Iθ_lt_top : MeasureTheory.volume Work.Spaces.Iθ < ⊤ := by
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-! ## The estimate -/

theorem KweightIntegralSub {F F' : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hint : MeasureTheory.Integrable (fun θ => Work.Spaces.K θ * F θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hint' : MeasureTheory.Integrable (fun θ => Work.Spaces.K θ * F' θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), |F θ - F' θ| ≤ C) :
    |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F θ)
      - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F' θ)| ≤ 3 * (Real.pi / 2) * C := by
  -- the difference of the two integrals is the integral of the difference
  have hdiff : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F θ)
      - (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * F' θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (F θ - F' θ) := by
    rw [← MeasureTheory.integral_sub hint hint']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro θ _
    ring
  rw [hdiff]
  -- the pointwise (a.e.) bound `‖K θ · (F θ - F' θ)‖ ≤ 3 C` on `Iθ`
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.K θ * (F θ - F' θ)‖ ≤ 3 * C := by
    filter_upwards [hbd] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_K_le_three_prv θ) hθ (abs_nonneg _) (by norm_num)
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
    (μ := MeasureTheory.volume) (s := Work.Spaces.Iθ)
    (f := fun θ => Work.Spaces.K θ * (F θ - F' θ)) (C := 3 * C)
    volume_Iθ_lt_top hae
  rw [Real.norm_eq_abs, volume_real_Iθ] at h
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (F θ - F' θ)| ≤ 3 * C * (Real.pi / 2) := h
    _ = 3 * (Real.pi / 2) * C := by ring

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Qang_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The angular-moment bound.**  If the `D_z`-iterates of `f` of order `≤ 2` obey the
standing weighted bound `|D_z^k f| ≤ C₀ · z^{3/2}/(1+z)²` in the open quadrant, then the
angular moment `Qang f k s = ∫_θ K(θ)·D_z^k f (s,θ) dθ` obeys the same bound (with the
extra factor `3·(π/2)` coming from `|K| ≤ 3` and the length `π/2` of `Iθ`).

The proof is the `θ`-integral mean inequality: `|K(θ)·D_z^k f (s,θ)| ≤ 3·C₀·Rwt s` on all of
`Iθ` (at the endpoints `K` vanishes, so only the interior hypothesis on `f` is needed). -/
theorem Qang_le {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    {k : ℕ} (hk : k ≤ 2) {s : ℝ} (hs : 0 < s) :
    |Work.Elliptic.Qang f k s| ≤ 3 * (Real.pi / 2) * (C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2)) := by
  have hbd' : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z := hbd
  have hint :=
    Work.FTS_RegExport.RXT.L12Iter.integrable_Ktheta_mul_DzIter hC0 h4 hbd' hk hs
  have hbnd := Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_mul_DzIter_le hC0 hbd' hk hs
  have h1 : ‖Work.Elliptic.Qang f k s‖
      ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f s θ‖ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h2 : (∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f s θ‖)
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt s) :=
    MeasureTheory.integral_mono_ae hint.norm (MeasureTheory.integrable_const _) hbnd
  have h3 : (∫ θ in Work.Spaces.Iθ, 3 * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt s))
      = 3 * (Real.pi / 2) * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt s) := by
    rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [Real.norm_eq_abs] at h1
  have h4' : |Work.Elliptic.Qang f k s|
      ≤ 3 * (Real.pi / 2) * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt s) :=
    le_trans h1 (le_trans h2 h3.le)
  simpa only [Work.FTS_RegExport.RXT.L12Iter.Rwt] using h4'

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

set_option maxHeartbeats 800000

/-- Pointwise bound of the `L₁₂`-density of `F_* + u` on `(0,∞)`, from a weighted bound of `u`.

PROOF RECIPE.  `L12dens (F_*+u) s = ∫ θ in Iθ, Ktheta θ * ((F_* s θ + u s θ)/s)`; bound the
norm of the integral by the integral of the norm
(`MeasureTheory.norm_integral_le_integral_norm`, unconditional), then bound the integrand a.e. in
`θ` (`0 < θ < π/2`, the two endpoints of `Iθ` being null) by the constant
`3*(20/(1+s)² + Cw*(s^{1/2}/(1+s)²))` and use
`MeasureTheory.integral_mono_of_nonneg` against `MeasureTheory.integrable_const` (no
integrability/measurability hypothesis on the integrand is needed, and there is NO need to split
`L12dens (F_*+u)` into its two summands).  Ingredients:
* `|Ktheta θ| ≤ 3` (`Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three`);
* `|Fstar α s θ| ≤ 10 * |FM.Fstar s|` for `θ ∈ Iθ`, i.e. `≤ 20*s/(1+s)²`: unfold
  `Construction.Fstar α s θ = α*(Work.Spaces.Gam α θ / Work.Spaces.c α)*FM.Fstar s`,
  use `Work.Spaces.Gam_bounds` (`0 ≤ Γ ≤ 1`) and `Work.Spaces.c_bounds` (`1/10 ≤ c`), so
  `|α*(Γ/c)| ≤ 10*α ≤ 10` for `0 < α ≤ 1`;
* `s^{3/2}/(1+s)²/s = s^{1/2}/(1+s)²` for `s > 0` (`Real.rpow_sub`, cf. `L12Iter.Rwt_div`);
* `∫ θ in Iθ, c = c*(π/2)`, as in the proved `Work.FTS_RegExport.RXT.L12Iter.abs_Qang_zero_le`
  (`Work.Elliptic.integral_Iθ_eq_interval` + `intervalIntegral.integral_const`). -/
theorem abs_L12dens_Fstar_add_le {α Cw : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCw : 0 ≤ Cw)
    {u : ℝ → ℝ → ℝ}
    (hu : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |u z θ| ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + u z θ) s|
      ≤ 3 * (Real.pi / 2)
          * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
  set C0 : ℝ := 3 * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) with hC0def
  have hden : (0 : ℝ) < (1 + s) ^ 2 := by positivity
  have hC0nn : 0 ≤ C0 := by
    rw [hC0def]
    have h1 : 0 ≤ 20 / (1 + s) ^ 2 := div_nonneg (by norm_num) hden.le
    have h2 : 0 ≤ Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) :=
      mul_nonneg hCw (div_nonneg (Real.rpow_nonneg hs.le _) hden.le)
    nlinarith [Real.pi_pos]
  have hvol_lt : MeasureTheory.volume (Set.Icc (0:ℝ) (Real.pi / 2)) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hvol : MeasureTheory.volume.real (Set.Icc (0:ℝ) (Real.pi / 2)) = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  -- `K` vanishes at the two endpoints of `Iθ`, where `hu` does not apply
  have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K]; norm_num
  have hKpi : Work.Spaces.K (Real.pi / 2) = 0 := by
    rw [Work.Spaces.K, Real.cos_pi_div_two]; norm_num
  have hKab : ∀ θ, |Work.Spaces.K θ| ≤ 3 := fun θ =>
    (by simpa [Work.Spaces.K, Work.Elliptic.Ktheta] using
      Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three θ)
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  -- the pointwise bound on the reference profile
  have hFstar : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2),
      |Work.Construction.Fstar α s θ| ≤ 20 * s / (1 + s) ^ 2 := by
    intro θ hθ
    have hGam := Work.Spaces.Gam_bounds α θ hα hθ
    have hΓc : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
      have hle : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 1 / ((1 : ℝ) / 10) :=
        div_le_div₀ (by norm_num) hGam.2 (by norm_num) hc
      rw [abs_of_nonneg (div_nonneg hGam.1 hcpos.le)]
      norm_num at hle ⊢
      linarith
    have hfac : |α * (Work.Spaces.Gam α θ / Work.Spaces.c α)| ≤ 10 := by
      rw [abs_mul, abs_of_nonneg hα.le]
      calc α * |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 1 * 10 :=
            mul_le_mul hα1 hΓc (abs_nonneg _) (by norm_num)
        _ = 10 := by ring
    have hFstar_eq : Work.Construction.Fstar α s θ
        = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * s / (1 + s) ^ 2) := by
      rw [Work.Construction.Fstar, Work.FM.Fstar]
    rw [hFstar_eq, abs_mul]
    have hFnn : 0 ≤ 2 * s / (1 + s) ^ 2 := div_nonneg (by linarith) hden.le
    rw [abs_of_nonneg hFnn]
    calc |α * (Work.Spaces.Gam α θ / Work.Spaces.c α)| * (2 * s / (1 + s) ^ 2)
        ≤ 10 * (2 * s / (1 + s) ^ 2) := mul_le_mul_of_nonneg_right hfac hFnn
      _ = 20 * s / (1 + s) ^ 2 := by ring
  -- dividing the weight `Rwt s = s^{3/2}/(1+s)²` by `s`
  have hsplit : (20 * s / (1 + s) ^ 2 + Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt s) / s
      = 20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
    have hA : 20 * s / (1 + s) ^ 2 / s = 20 / (1 + s) ^ 2 := by
      rw [div_div]; field_simp
    have hB : Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt s / s
        = Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
      rw [mul_div_assoc, Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs]
    rw [add_div, hA, hB]
  -- the uniform pointwise bound on the whole of `Iθ`
  have hpt : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2),
      ‖Work.Spaces.K θ * (Work.Construction.Fstar α s θ + u s θ) / s‖ ≤ C0 := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [hK0, zero_mul, zero_div, norm_zero]
      exact hC0nn
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        rw [hKpi, zero_mul, zero_div, norm_zero]
        exact hC0nn
      · have hX : |Work.Construction.Fstar α s θ + u s θ|
            ≤ 20 * s / (1 + s) ^ 2 + Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt s :=
          calc |Work.Construction.Fstar α s θ + u s θ|
              ≤ |Work.Construction.Fstar α s θ| + |u s θ| := abs_add_le _ _
            _ ≤ 20 * s / (1 + s) ^ 2 + Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt s :=
                add_le_add (hFstar θ hθ) (by
                  simpa only [Work.FTS_RegExport.RXT.L12Iter.Rwt] using hu s θ hs h0 h1)
        have hXdiv : |Work.Construction.Fstar α s θ + u s θ| / s
            ≤ 20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by
          have h := div_le_div_of_nonneg_right hX hs.le
          rwa [hsplit] at h
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul]
        calc |Work.Spaces.K θ| * |Work.Construction.Fstar α s θ + u s θ| / s
            = |Work.Spaces.K θ| * (|Work.Construction.Fstar α s θ + u s θ| / s) := by ring
          _ ≤ 3 * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) :=
              mul_le_mul (hKab θ) hXdiv (by positivity) (by norm_num)
          _ = C0 := by rw [hC0def]
  have hgoal : |Work.Construction.L12dens
        (fun z θ => Work.Construction.Fstar α z θ + u z θ) s|
      = ‖∫ θ in Set.Icc (0:ℝ) (Real.pi / 2),
          Work.Spaces.K θ * (Work.Construction.Fstar α s θ + u s θ) / s‖ := by
    rw [Real.norm_eq_abs, Work.Construction.L12dens, Work.FM.L12dens]
  calc |Work.Construction.L12dens (fun z θ => Work.Construction.Fstar α z θ + u z θ) s|
      = ‖∫ θ in Set.Icc (0:ℝ) (Real.pi / 2),
          Work.Spaces.K θ * (Work.Construction.Fstar α s θ + u s θ) / s‖ := hgoal
    _ ≤ C0 * MeasureTheory.volume.real (Set.Icc (0:ℝ) (Real.pi / 2)) :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hvol_lt hpt
    _ = C0 * (Real.pi / 2) := by rw [hvol]
    _ = 3 * (Real.pi / 2) * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
        rw [hC0def]; ring

end Work.FTS_RegExport.RXT.Sys
end
