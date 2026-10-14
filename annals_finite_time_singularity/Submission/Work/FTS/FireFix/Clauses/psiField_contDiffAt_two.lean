import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Physical.Omega
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradIntegral
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.RegPkgGal.R7d.support_strip
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.Regularity.profFullBounds
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.FTS.BSIdent.Bundle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology Real

namespace Work.FTS.BSIdent

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two bundles -/











/-! ## Inhabitation -/


end Work.FTS.BSIdent
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The decay of the ansatz field `psiField (merPsi … · t)`

Elgindi's reconstruction has the meridian stream function

  `merPsi α A B Φ C r z t = ρ(r,z)² · A(τ)⁻¹ · Φ̂(ρ(r,z)^{3α}/B(τ), θ(r,z), τ)`,  `τ = clockInv C t`,

and this file proves that the associated no-swirl field `psiField (merPsi … · t)` decays like
`1/‖x‖` at infinity — the `hdec` clause of the geometric bundle of the ansatz field
(`Work.FTS.BSIdent.AnsatzBundle`).

The proof is a direct computation.  Writing `G = Φ̂(·,·,τ)`, `ρ = rhoP r z`, `θ = thetaP r z`,
`w = ρ^{3α}/B(τ)`, the chain rule gives

  `∂_z ψ = 2 z c G(w,θ) + c (p z w ∂_wG(w,θ) + r ∂_θG(w,θ))`,
  `∂_r ψ = 2 r c G(w,θ) + c (p r w ∂_wG(w,θ) - z ∂_θG(w,θ))`

with `c = A(τ)⁻¹`, `p = 3α`; the hypothesis `hrate` bounds `G` by `(π/2-θ)^q (1+w)^{-λ}` and its
`w`- resp. `θ`-derivative by the same expression with one power of `(1+w)` resp. `(π/2-θ)`
removed.  Since `|z|, r ≤ ρ` and `(π/2-θ) ≤ π/2`, every term is bounded by
`C ρ (1+w)^{-λ} ≤ C · 2 max(1, b^λ)/(1+ρ)`, the last step using `p λ = 3αλ ≥ 3` (`hexp`).  The
term `ψ/r` is handled with the sharp form `π/2-θ ≤ (π/2) cos θ = (π/2) r/ρ` (Jordan's
inequality), which is what makes `ρ²/r · (π/2-θ)^q ≤ C ρ`.

The endpoints `z = 0` (where `θ = 0` and the odd extension need not be differentiable) and
`r = 0` are treated by a one-sided mean value argument, and `z < 0` by the oddness of `ψ` in `z`.
-/

noncomputable section

open scoped Topology

namespace Work.FTS.BSIdent.Cyl

set_option autoImplicit false

/-! ## The meridian stream function and its core -/

/-- The meridian stream function at time `t`, as a function of the meridian coordinates
`(r, x₃)`. -/
noncomputable def merPsiT (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ) : ℝ → ℝ → ℝ :=
  fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t

/-- The core of the meridian stream function: `ρ(r,z)² · c · G(ρ(r,z)^p/b, θ(r,z))`. -/
noncomputable def psiCore (p c b : ℝ) (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun r z => Work.Cyl.rhoP r z ^ 2 * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)

/-- `merPsiT` is the core `psiCore` with `G` the odd extension of `Φ(·,·,τ)`, `p = 3α`,
`c = A(τ)⁻¹` and `b = B(τ)`. -/
theorem merPsiT_eq_psiCore (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ) :
    merPsiT α A B Φ C t =
      psiCore (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹)
        (B (Physical.clockInv C t))
        (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ (Physical.clockInv C t)) := by
  funext r z
  simp only [merPsiT, psiCore, Work.FTS.BSIdent.merPsi_apply]

/-! ## The rate hypothesis on the profile -/

/-- **The rate hypothesis of the decay theorem**, as a named predicate: the profile `Φ(·,·,τ)`
and its first two partial derivatives are bounded by the powers of `(π/2-θ)` and `(1+w)` that the
chain rule produces.  It is the conjunction `hrate` of
`decay_psiField_merPsi_of_Phi_decay`, with the time argument made explicit. -/
def PhiRate (Φ : Work.FTS.BSIdent.Fam) (τ C₀ q lam : ℝ) : Prop :=
  ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
    |Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam) ∧
    |deriv (fun w' => Φ w' θ τ) w| ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam - 1) ∧
    |deriv (fun θ' => Φ w θ' τ) θ| ≤ C₀ * (Real.pi / 2 - θ) ^ (q - 1) * (1 + w) ^ (-lam) ∧
    |deriv (fun θ' => deriv (fun θ'' => Φ w θ'' τ) θ') θ|
      ≤ C₀ * (Real.pi / 2 - θ) ^ (q - 2) * (1 + w) ^ (-lam) ∧
    |deriv (fun θ' => deriv (fun w' => Φ w' θ' τ) w) θ|
      ≤ C₀ * (Real.pi / 2 - θ) ^ (q - 1) * (1 + w) ^ (-lam - 1) ∧
    |deriv (fun w' => deriv (fun w'' => Φ w'' θ τ) w') w|
      ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam - 2)

/-! ## The two constants -/

/-- The constant in the `(1+ρ)^{-1}` bound for the two partial derivatives of `ψ`. -/
noncomputable def decayKzr (p c C₀ q lam b : ℝ) : ℝ :=
  |c| * C₀ * (Real.pi / 2) ^ (q - 1)
    * (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1)
    * (2 * max 1 (b ^ lam))

/-- The constant in the `(1+ρ)^{-1}` bound for `ψ/r`. -/
noncomputable def decayKq (c C₀ q lam b : ℝ) : ℝ :=
  |c| * C₀ * (Real.pi / 2) ^ q * (2 * max 1 (b ^ lam))

theorem decayKzr_nonneg {p c C₀ q lam b : ℝ} (hC₀ : 0 ≤ C₀) (hp : 0 ≤ p) :
    0 ≤ decayKzr p c C₀ q lam b := by
  have h1 : (0 : ℝ) ≤ (Real.pi / 2) ^ (q - 1) := Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ 2 * (Real.pi / 2) + p * (Real.pi / 2) + 1 := by
    have := mul_nonneg hp (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    linarith [Real.pi_pos]
  have h3 : (0 : ℝ) ≤ 2 * max 1 (b ^ lam) :=
    mul_nonneg (by norm_num) (le_trans zero_le_one (le_max_left 1 (b ^ lam)))
  have h4 : (0 : ℝ) ≤ |c| := abs_nonneg c
  rw [decayKzr]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h4 hC₀) h1) h2) h3


/-! ## Elementary facts -/

/-- `‖r e_r‖ = r`. -/
theorem norm_radialVec_eq (x : Work.Cyl.R3) :
    ‖Work.Cyl.radialVec x‖ = Work.Cyl.radial x := by
  have h : ‖Work.Cyl.radialVec x‖ ^ 2 = Work.Cyl.radial x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, Work.Cyl.inner_radialVec_self, Work.Cyl.radial_sq]
  nlinarith [norm_nonneg (Work.Cyl.radialVec x), Work.Cyl.radial_nonneg x]

/-- `‖e₃‖ = 1`. -/
theorem norm_eZ_eq : ‖(Work.Cyl.eZ : Work.Cyl.R3)‖ = 1 := by
  simp [Work.Cyl.eZ, FiniteTimeSingularity.e]

/-- **An odd function has an even derivative.** -/
theorem deriv_odd_eq {f : ℝ → ℝ} (h : ∀ y, f (-y) = - f y) (z : ℝ) :
    deriv f z = deriv f (-z) := by
  have hf : ∀ y, f y = - f (-y) := fun y => by
    have := h (-y); rwa [neg_neg] at this
  by_cases hd : DifferentiableAt ℝ f (-z)
  · have hcomp : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-z) * (-1)) z :=
      (hd.hasDerivAt).comp z (hasDerivAt_neg z)
    have hneg : HasDerivAt (fun y : ℝ => - f (-y)) (-(deriv f (-z) * (-1))) z := hcomp.neg
    have hfe : f =ᶠ[𝓝 z] fun y : ℝ => - f (-y) := Filter.Eventually.of_forall hf
    have hf' : HasDerivAt f (-(deriv f (-z) * (-1))) z := hneg.congr_of_eventuallyEq hfe
    rw [hf'.deriv]; ring
  · have hz : ¬ DifferentiableAt ℝ f z := by
      intro hz'
      have hz'' : DifferentiableAt ℝ f (- -z) := by simpa using hz'
      have h1 : DifferentiableAt ℝ (fun y : ℝ => f (-y)) (-z) :=
        hz''.comp (-z) ((differentiableAt_id (x := -z)).neg)
      have h2 : DifferentiableAt ℝ (fun y : ℝ => - f (-y)) (-z) := h1.neg
      exact hd (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hf))
    rw [deriv_zero_of_not_differentiableAt hz, deriv_zero_of_not_differentiableAt hd]

/-- The odd extension inherits the rate of `Φ`, with `(π/2-|θ|)^q` sharpened to
`((π/2) cos θ)^q`. -/
theorem abs_PhiOdd_le_cos {Φ : Work.FTS.BSIdent.Fam} {τ C₀ q lam : ℝ} (hC₀ : 0 ≤ C₀)
    (hq : 0 ≤ q)
    (h0 : ∀ w, 0 < w → Φ w 0 τ = 0)
    (hrate : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      |Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) ^ q * (1 + w) ^ (-lam))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2) :
    |Work.FTS.BSIdent.PhiOdd Φ w θ τ|
      ≤ C₀ * (Real.pi / 2) ^ q * (Real.cos θ) ^ q * (1 + w) ^ (-lam) := by
  have habs := abs_lt.1 hθ
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨habs.1, habs.2⟩
  have h1 := DecayAux.abs_PhiOdd_le hC₀ h0 hrate hw hθ
  have h2 : (0 : ℝ) ≤ Real.pi / 2 - |θ| := by linarith [abs_nonneg θ, Real.pi_pos]
  have h3 : Real.pi / 2 - |θ| ≤ Real.pi / 2 * Real.cos θ :=
    DecayAux.pi_div_two_sub_abs_le_cos (le_of_lt hθ)
  have h5 : (Real.pi / 2 - |θ|) ^ q ≤ (Real.pi / 2 * Real.cos θ) ^ q :=
    Real.rpow_le_rpow h2 h3 hq
  have h6 : (Real.pi / 2 * Real.cos θ) ^ q = (Real.pi / 2) ^ q * (Real.cos θ) ^ q :=
    Real.mul_rpow (by positivity) hcos.le
  calc |Work.FTS.BSIdent.PhiOdd Φ w θ τ|
      ≤ C₀ * (Real.pi / 2 - |θ|) ^ q * (1 + w) ^ (-lam) := h1
    _ ≤ C₀ * ((Real.pi / 2) ^ q * (Real.cos θ) ^ q) * (1 + w) ^ (-lam) := by
        rw [h6] at h5
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hC₀)
          (Real.rpow_nonneg (by linarith) _)
    _ = C₀ * (Real.pi / 2) ^ q * (Real.cos θ) ^ q * (1 + w) ^ (-lam) := by ring

/-! ## Oddness of the meridian stream function in the axial variable -/

/-- `z ↦ ψ r z` is odd (for `r > 0`). -/
theorem merPsiT_odd_z {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {r z : ℝ} (hr : 0 < r) :
    merPsiT α A B Φ C t r (-z) = -merPsiT α A B Φ C t r z := by
  rw [merPsiT_eq_psiCore]
  simp only [psiCore, Work.Cyl.rhoP_neg, Work.Cyl.thetaP_neg]
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hB
  rw [DecayAux.PhiOdd_neg_theta_of_pos h0 hw]
  ring

/-! ## Elementary comparison lemmas -/

/-- `|z| ≤ ρ(r,z)`. -/
theorem abs_snd_le_rhoP (r z : ℝ) : |z| ≤ Work.Cyl.rhoP r z := by
  have h : (|z| : ℝ) ^ 2 ≤ Work.Cyl.rhoP r z ^ 2 := by
    rw [Work.Cyl.rhoP_sq, sq_abs]; nlinarith [sq_nonneg r]
  nlinarith [abs_nonneg z, Work.Cyl.rhoP_nonneg r z]

/-- `r ≤ ρ(r,z)` for `r ≥ 0`. -/
theorem le_rhoP (r z : ℝ) (hr : 0 ≤ r) : r ≤ Work.Cyl.rhoP r z := by
  have h : r ^ 2 ≤ Work.Cyl.rhoP r z ^ 2 := by
    rw [Work.Cyl.rhoP_sq]; nlinarith [sq_nonneg z]
  nlinarith [Work.Cyl.rhoP_nonneg r z]

/-- `θ(r,z) > 0` for `r, z > 0`. -/
theorem thetaP_pos_of_pos {r z : ℝ} (hr : 0 < r) (hz : 0 < z) : 0 < Work.Cyl.thetaP r z := by
  rw [Work.Cyl.thetaP]
  exact Real.arctan_pos.mpr (div_pos hz hr)

/-- `θ(r,z) < π/2`. -/
theorem thetaP_lt_pi_div_two (r z : ℝ) : Work.Cyl.thetaP r z < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two _

/-- `-π/2 < θ(r,z)`. -/
theorem neg_pi_div_two_lt_thetaP (r z : ℝ) : -(Real.pi / 2) < Work.Cyl.thetaP r z :=
  Real.neg_pi_div_two_lt_arctan _

/-- `|θ(r,z)| < π/2`. -/
theorem abs_thetaP_lt (r z : ℝ) : |Work.Cyl.thetaP r z| < Real.pi / 2 :=
  abs_lt.mpr ⟨neg_pi_div_two_lt_thetaP r z, thetaP_lt_pi_div_two r z⟩

/-- `Φ̂(·,·,τ)` is differentiable on the open quadrant, being `Φ(·,·,τ)` there. -/
theorem diffAt2_PhiOdd {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 3 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Cyl.DiffAt2 (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ := by
  have hmem : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w, θ) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hθ0
  have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝 (w, θ)]
      fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ := by
    filter_upwards [hmem] with p hp
    exact (Work.FTS.BSIdent.PhiOdd_of_nonneg hp.le).symm
  exact (((hsm w θ hw hθ0 hθ1).of_le (by decide)).differentiableAt_one).congr_of_eventuallyEq hev.symm

/-! ## The two chain rules for `psiCore` -/

theorem pdZ_psiCore_eq {G : ℝ → ℝ → ℝ} {p c b r z : ℝ}
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hr : 0 < r) :
    Work.Cyl.pdZ (psiCore p c b G) r z =
      2 * z * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + c * (p * z * (Work.Cyl.rhoP r z ^ p / b)
              * Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
            + r * Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)) := by
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hρne : Work.Cyl.rhoP r z ≠ 0 := ne_of_gt hρpos
  have hρ2ne : Work.Cyl.rhoP r z ^ 2 ≠ 0 := pow_ne_zero 2 hρne
  have hρ2 : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) (2 * z) z := by
    have hfun : (fun z' : ℝ => Work.Cyl.rhoP r z' ^ 2) = fun z' : ℝ => z' ^ 2 + r ^ 2 := by
      funext z'; rw [Work.Cyl.rhoP_sq]; ring
    rw [hfun]
    have h : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    simpa using h.add_const (r ^ 2)
  have hw : HasDerivAt (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / b)
      (p * (Work.Cyl.rhoP r z ^ p / b) * (z / Work.Cyl.rhoP r z ^ 2)) z :=
    Work.Cyl.hasDerivAt_rhoP_rpow_div_snd r p z b hr
  have hθ : HasDerivAt (fun z' : ℝ => Work.Cyl.thetaP r z') (r / Work.Cyl.rhoP r z ^ 2) z :=
    Work.Cyl.hasDerivAt_thetaP_snd r z hr
  have h2 : HasDerivAt (fun z' : ℝ => G (Work.Cyl.rhoP r z' ^ p / b) (Work.Cyl.thetaP r z'))
      (Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
          * (p * (Work.Cyl.rhoP r z ^ p / b) * (z / Work.Cyl.rhoP r z ^ 2))
        + Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
          * (r / Work.Cyl.rhoP r z ^ 2)) z :=
    Work.Cyl.hasDerivAt_comp_two G (fun z' : ℝ => Work.Cyl.rhoP r z' ^ p / b)
      (fun z' : ℝ => Work.Cyl.thetaP r z') _ _ z hG hw hθ
  have h3 : HasDerivAt (fun z' : ℝ =>
      (Work.Cyl.rhoP r z' ^ 2 * c) * G (Work.Cyl.rhoP r z' ^ p / b) (Work.Cyl.thetaP r z'))
      ((2 * z * c) * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + (Work.Cyl.rhoP r z ^ 2 * c)
          * (Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              * (p * (Work.Cyl.rhoP r z ^ p / b) * (z / Work.Cyl.rhoP r z ^ 2))
            + Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              * (r / Work.Cyl.rhoP r z ^ 2))) z := (hρ2.mul_const c).mul h2
  show deriv (fun z' : ℝ =>
      (Work.Cyl.rhoP r z' ^ 2 * c) * G (Work.Cyl.rhoP r z' ^ p / b)
        (Work.Cyl.thetaP r z')) z = _
  rw [h3.deriv]
  field_simp

theorem pdR_psiCore_eq {G : ℝ → ℝ → ℝ} {p c b r z : ℝ}
    (hG : Work.Cyl.DiffAt2 G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))
    (hr : 0 < r) :
    Work.Cyl.pdR (psiCore p c b G) r z =
      2 * r * c * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + c * (p * r * (Work.Cyl.rhoP r z ^ p / b)
              * Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
            + (-z) * Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)) := by
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hρne : Work.Cyl.rhoP r z ≠ 0 := ne_of_gt hρpos
  have hρ2ne : Work.Cyl.rhoP r z ^ 2 ≠ 0 := pow_ne_zero 2 hρne
  have hρ2 : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ 2) (2 * r) r := by
    have hfun : (fun r' : ℝ => Work.Cyl.rhoP r' z ^ 2) = fun r' : ℝ => r' ^ 2 + z ^ 2 := by
      funext r'; rw [Work.Cyl.rhoP_sq]
    rw [hfun]
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.add_const (z ^ 2)
  have hw : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b)
      (p * (Work.Cyl.rhoP r z ^ p / b) * (r / Work.Cyl.rhoP r z ^ 2)) r :=
    DecayAux.hasDerivAt_rhoP_rpow_div_fst r p z b hr
  have hθ : HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r :=
    DecayAux.hasDerivAt_thetaP_fst r z hr
  have h2 : HasDerivAt (fun r' : ℝ => G (Work.Cyl.rhoP r' z ^ p / b) (Work.Cyl.thetaP r' z))
      (Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
          * (p * (Work.Cyl.rhoP r z ^ p / b) * (r / Work.Cyl.rhoP r z ^ 2))
        + Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
          * (-z / Work.Cyl.rhoP r z ^ 2)) r :=
    Work.Cyl.hasDerivAt_comp_two G (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / b)
      (fun r' : ℝ => Work.Cyl.thetaP r' z) _ _ r hG hw hθ
  have h3 : HasDerivAt (fun r' : ℝ =>
      (Work.Cyl.rhoP r' z ^ 2 * c) * G (Work.Cyl.rhoP r' z ^ p / b) (Work.Cyl.thetaP r' z))
      ((2 * r * c) * G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
        + (Work.Cyl.rhoP r z ^ 2 * c)
          * (Work.Cyl.pdR G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              * (p * (Work.Cyl.rhoP r z ^ p / b) * (r / Work.Cyl.rhoP r z ^ 2))
            + Work.Cyl.pdZ G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)
              * (-z / Work.Cyl.rhoP r z ^ 2))) r := (hρ2.mul_const c).mul h2
  show deriv (fun r' : ℝ =>
      (Work.Cyl.rhoP r' z ^ 2 * c) * G (Work.Cyl.rhoP r' z ^ p / b)
        (Work.Cyl.thetaP r' z)) r = _
  rw [h3.deriv]
  field_simp


end Work.FTS.BSIdent.Cyl
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Defs.contDiffAt_psiField_merPsi_of_mem_Uax =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C¹` regularity of the ansatz field `psiField (merPsi … · t)` on `Uax`

`Work.Cyl.psiField ψ = cylField (∂_zψ) (-(ψ/r) - ∂_rψ)` is built from the polar data
`(r,z) ↦ (ψ, ∂_rψ, ∂_zψ)`.  Hence, off the axis (`r > 0`), `psiField ψ` is one order smoother
than `ψ`:

* if `ψ` is `C³` at `(r,z)`, then `psiField ψ` is `C²` at the corresponding point of `ℝ³`
  (`Work.FTS.FireFix.Clauses.psiField_contDiffAt_two`),
* if `ψ` is `C²` at `(r,z)`, then `psiField ψ` is `C¹` — the statement proved here
  (`psiField_contDiffAt_one`).

The second fact is what the Biot–Savart identification needs: the meridian slice of `merPsi` is
`C²` off the degenerate set `{r = 0} ∪ {z = 0}` (`contDiffAt_merPsi_slice`, from the `C²` hypothesis
`hsm` on the profile), and `Uax` is exactly the set on which the point coordinates give
`r > 0`, `z ≠ 0`.  Combining the two gives the `C¹`-clause of the geometric bundle of the ansatz
field on `Uax`.

The ingredient of the `C¹`-from-`C²` transfer is the pair
`contDiffAt_pdZ_uncurry_one`, `contDiffAt_pdR_uncurry_one`: the partial derivatives
`(r,z) ↦ ∂_zψ`, `(r,z) ↦ ∂_rψ` are `C¹` as soon as `ψ` is `C²`, because each of them is the
first derivative `fderiv ℝ (uncurry ψ)` evaluated in a fixed direction
(`Work.Cyl.fderiv_prod_apply_snd`, `Work.Cyl.fderiv_prod_apply_fst`) and `fderiv` of a `C²`
function is `C¹` (`ContDiffAt.fderiv_right`).
-/

set_option autoImplicit false

namespace Work.FTS.BSIdent.Defs

/-! ## The partial derivatives of a `C²` stream function -/

/-- The axial partial derivative `(r,z) ↦ ∂_zψ(r,z)` of a `C²` stream function is `C¹`. -/
theorem contDiffAt_pdZ_uncurry_one {ψ : ℝ → ℝ → ℝ} {r z : ℝ}
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Work.Cyl.pdZ ψ p.1 p.2) (r, z) := by
  -- `ψ` is differentiable on a neighbourhood of `(r,z)`
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  -- `fderiv ℝ ψ` is `C¹` at `(r,z)`
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 1) (by norm_num)
  -- evaluating it in the fixed direction `(0,1)` preserves smoothness
  have hΦ : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (0, 1)) (r, z) :=
    hfd.clm_apply contDiffAt_const
  -- and on a neighbourhood it agrees with `∂_zψ`
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (Work.Cyl.fderiv_prod_apply_snd ψ p.1 p.2 hp).symm

/-- The radial partial derivative `(r,z) ↦ ∂_rψ(r,z)` of a `C²` stream function is `C¹`. -/
theorem contDiffAt_pdR_uncurry_one {ψ : ℝ → ℝ → ℝ} {r z : ℝ}
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2) (r, z) := by
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 1) (by norm_num)
  have hΦ : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (1, 0)) (r, z) :=
    hfd.clm_apply contDiffAt_const
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (Work.Cyl.fderiv_prod_apply_fst ψ p.1 p.2 hp).symm

/-! ## `psiField` of a `C²` stream function is `C¹` off the axis -/

/-- `x ↦ radial x = √(x₀² + x₁²)` is `C¹` at `x` provided `radial x > 0`. -/
theorem contDiffAt_radial_one {x : Work.FTS.BSIdent.R3} (hx : 0 < Work.Cyl.radial x) :
    ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.radial y) x := by
  have hsq : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.radSq y) x := by
    show ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => y 0 ^ 2 + y 1 ^ 2) x
    fun_prop
  have hpos : 0 < Work.Cyl.radSq x := Real.sqrt_pos.mp hx
  exact (Real.contDiffAt_sqrt (ne_of_gt hpos)).comp x hsq

/-- **`psiField` of a `C²` stream function is `C¹` off the axis.** -/
theorem psiField_contDiffAt_one {ψ : ℝ → ℝ → ℝ} {x : Work.FTS.BSIdent.R3}
    (hx : 0 < Work.Cyl.radial x)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x)) :
    ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.psiField ψ y) x := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hx
  -- the polar data are `C¹` at `x`
  have hrad := contDiffAt_radial_one hx
  have hax : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.axial y) x := by
    show ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => y 2) x
    fun_prop
  have hP : ContDiffAt ℝ 1
      (fun y : Work.FTS.BSIdent.R3 => (Work.Cyl.radial y, Work.Cyl.axial y)) x :=
    hrad.prodMk hax
  -- the profile data are `C¹` at `(radial x, axial x)`
  have hpdZ : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Work.Cyl.pdZ ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := contDiffAt_pdZ_uncurry_one hψ
  have hpdR : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := contDiffAt_pdR_uncurry_one hψ
  have hψ1 : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := hψ.of_le (by norm_num)
  have hpdZc : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hpdZ.comp x hP using 1
    ext y; rfl
  have hpdRc : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hpdR.comp x hP using 1
    ext y; rfl
  have hψc : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hψ1.comp x hP using 1
    ext y; rfl
  -- the two components of `cylField`, as functions of `x`
  have hA : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y) x :=
    hpdZc.div hrad hrne
  have hB : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      -(ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
        - Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x :=
    (hψc.div hrad hrne).neg.sub hpdRc
  have hrv : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 => Work.Cyl.radialVec y) x := by
    rw [show Work.Cyl.radialVec = fun y : Work.FTS.BSIdent.R3 =>
        (y 0) • Work.Cyl.e0 + (y 1) • Work.Cyl.e1 from by
      funext y; ext i; fin_cases i <;>
        simp [Work.Cyl.radialVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]]
    fun_prop
  have hmain : ContDiffAt ℝ 1 (fun y : Work.FTS.BSIdent.R3 =>
      (Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
          • Work.Cyl.radialVec y
        + (-(ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
            - Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) • Work.Cyl.eZ) x :=
    (hA.smul hrv).add (hB.smul (contDiffAt_const (c := Work.Cyl.eZ)))
  refine hmain.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  simp only [Work.Cyl.psiField, Work.Cyl.cylField]

/-! ## The `C¹` clause of the ansatz bundle on `Uax` -/

theorem contDiffAt_psiField_merPsi_of_mem_Uax (α : ℝ) (A B : ℝ → ℝ)
    (Φ : Work.FTS.BSIdent.Fam) (C : Physical.PhysClock) (t : ℝ)
    (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    {x : Work.FTS.BSIdent.R3} (hx : x ∈ Work.FTS.BSIdent.Uax) :
    ContDiffAt ℝ 1
      (Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi α A B Φ C r z t)) x := by
  have hr : 0 < Work.Cyl.radial x := Work.FTS.BSIdent.radial_pos_of_mem_Uax hx
  have hz : Work.Cyl.axial x ≠ 0 := Work.FTS.BSIdent.axial_ne_zero_of_mem_Uax hx
  exact psiField_contDiffAt_one hr
    (Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice α A B Φ C t hB hsm hr hz)

end Work.FTS.BSIdent.Defs
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.continuous_psiFieldCorr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

open Filter Set
open scoped Topology

/-- **Continuity of the corrected stream-function field.**

The Lean field `Cyl.psiField ψ` is continuous off the axis (`hψ`) and has, at every point
`z • e₂` of the axis, the one-sided limit `-(2 L z) • e_Z` along the complement of the axis
(`hlim`).  The corrected field `psiFieldCorr ψ L` replaces the (junk) on-axis value of
`psiField` by exactly that limit; since the on-axis branch
`x ↦ -(2 L (axial x)) • e_Z` is continuous as soon as `L` is (`hL`), the piecewise field is
continuous everywhere.  Off the axis this is immediate; on the axis we use the decomposition
`𝓝 x = 𝓝[{r = 0}] x ⊔ 𝓝[{r ≠ 0}] x`. -/
theorem continuous_psiFieldCorr {ψ : ℝ → ℝ → ℝ} {L : ℝ → ℝ}
    (hψ : ContinuousOn (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.psiField ψ x)
        {x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0})
    (hL : Continuous L)
    (hlim : ∀ z : ℝ, Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.psiField ψ x)
        (nhdsWithin (z • FiniteTimeSingularity.e 2)
          {x : Work.FTS.BSIdent.R3 | Work.Cyl.radial x ≠ 0})
        (nhds ((-(2 * L z)) • Work.Cyl.eZ))) :
    Continuous (Work.FTS.BSIdent.psiFieldCorr ψ L) := by
  have hAx : Continuous (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.axial x) := by
    have h : (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.axial x) = fun x => x 2 := rfl
    rw [h]; fun_prop
  have hrad : Continuous (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radial x) := by
    have h : (fun x : Work.FTS.BSIdent.R3 => Work.Cyl.radial x)
        = fun x => Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by funext x; rfl
    rw [h]; fun_prop
  -- the on-axis branch is continuous
  have hA : Continuous (fun x : Work.FTS.BSIdent.R3 =>
      (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ) := by
    fun_prop
  -- axis ∪ off-axis = everything
  have hST : ({y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0} ∪
      {y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}) = Set.univ := by
    ext y; by_cases h : Work.Cyl.radial y = 0 <;> simp [h]
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : Work.Cyl.radial x = 0
  · -- on the axis: glue the two one-sided limits
    have hxval : Work.FTS.BSIdent.psiFieldCorr ψ L x
        = (-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ :=
      Work.FTS.BSIdent.psiFieldCorr_of_radial_eq hx
    -- a point of the axis is a multiple of `e₂`
    have hxe : x = (Work.Cyl.axial x) • FiniteTimeSingularity.e 2 := by
      have hzero : Work.Cyl.radSq x = 0 := by
        have := congrArg (fun t : ℝ => t ^ 2) hx
        rw [Work.Cyl.radial] at this
        rwa [Real.sq_sqrt (by simp only [Work.Cyl.radSq]; positivity),
          zero_pow (by norm_num)] at this
      have h02 : x 0 ^ 2 + x 1 ^ 2 = 0 := by simpa [Work.Cyl.radSq] using hzero
      have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      have h1' : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      ext i
      fin_cases i <;> simp [Work.Cyl.axial, h0, h1', FiniteTimeSingularity.e, Pi.single]
    -- along the axis the corrected field is the continuous branch
    have hEqS : (fun y : Work.FTS.BSIdent.R3 => (-(2 * L (Work.Cyl.axial y))) • Work.Cyl.eZ)
        =ᶠ[𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0}] x]
        Work.FTS.BSIdent.psiFieldCorr ψ L := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (Work.FTS.BSIdent.psiFieldCorr_of_radial_eq hy).symm
    have hAll : Tendsto (Work.FTS.BSIdent.psiFieldCorr ψ L)
        (𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0}] x)
        (𝓝 ((-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ)) :=
      Tendsto.congr' hEqS (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    -- off the axis the corrected field is `psiField ψ`, whose limit is the on-axis value
    have hEqC : (fun y => Work.Cyl.psiField ψ y)
        =ᶠ[𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}] x]
        Work.FTS.BSIdent.psiFieldCorr ψ L := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (Work.FTS.BSIdent.psiFieldCorr_of_radial_ne hy).symm
    have hlimx : Tendsto (fun y => Work.Cyl.psiField ψ y)
        (𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}] x)
        (𝓝 ((-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ)) := by
      have h := hlim (Work.Cyl.axial x)
      rwa [← hxe] at h
    have hAc : Tendsto (Work.FTS.BSIdent.psiFieldCorr ψ L)
        (𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}] x)
        (𝓝 ((-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ)) :=
      Tendsto.congr' hEqC hlimx
    have hcomb : Tendsto (Work.FTS.BSIdent.psiFieldCorr ψ L)
        (𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0}] x ⊔
          𝓝[{y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y ≠ 0}] x)
        (𝓝 ((-(2 * L (Work.Cyl.axial x))) • Work.Cyl.eZ)) :=
      tendsto_sup.mpr ⟨hAll, hAc⟩
    rw [← nhdsWithin_union, hST, nhdsWithin_univ] at hcomb
    rw [ContinuousAt, hxval]
    exact hcomb
  · -- off the axis, `psiFieldCorr` agrees locally with the continuous `psiField ψ`
    have hSclosed : IsClosed {y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0} :=
      isClosed_eq hrad continuous_const
    have hcontOn : ContinuousOn (Work.FTS.BSIdent.psiFieldCorr ψ L)
        ({y : Work.FTS.BSIdent.R3 | Work.Cyl.radial y = 0}ᶜ) :=
      hψ.congr (fun y hy => Work.FTS.BSIdent.psiFieldCorr_of_radial_ne hy)
    exact hcontOn.continuousAt (hSclosed.isOpen_compl.mem_nhds hx)

end Work.FTS.BSIdent.Weyl
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.physVel_neg_physOmega_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl

noncomputable section

open FiniteTimeSingularity Set MeasureTheory Filter Gradient
open scoped Topology

/-- **Weak divergence-freeness is stable under pointwise negation.**  If `∫ ⟪ω, ∇k⟫ = 0` for every
smooth compactly supported `k`, the same holds for `−ω`, since both the inner product
(`inner_neg_left`) and the integral (`integral_neg`) are additive in the field. -/
private theorem weakDivFree_neg {ω : R3 → R3} (h : Work.FTS.BSSwirl.WeakDivFree ω) :
    Work.FTS.BSSwirl.WeakDivFree (fun x => -ω x) := by
  intro k hk hks
  have h1 := h k hk hks
  have h2 : (fun x => inner ℝ (-ω x) (gradient k x))
      = fun x => -(inner ℝ (ω x) (gradient k x)) := by
    funext x
    rw [inner_neg_left]
  rw [h2, integral_neg, h1, neg_zero]


end

end Work.FTS.BSIdent.Weyl
end
-- ===== merged: Submission.Work.FTS.FireFix.BundleNeg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix

open Work.CoreResiduals (BSAdmissibleStrip BSAdmissibleStripFull TimeDerivStrip
  TimeDerivStripHolder)

/-- **The time derivative of a negated space-time field**: `∂ₜ(−f) = −∂ₜf`.  This is
`Work.FTS.Physical.timeDeriv_neg` (the frozen physical layer's instance of `deriv.neg`). -/
theorem timeDeriv_neg_field (f : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    timeDeriv (fun y s => - f y s) x t = - timeDeriv f x t :=
  Work.FTS.Physical.timeDeriv_neg f x t

/-- **The strip admissibility of a negated vorticity.**  Every clause of `BSAdmissibleStrip` is
invariant under `ω ↦ −ω`: `‖−a‖ = ‖a‖`, `dist (−a) (−b) = dist a b`, `−a ≠ 0 ↔ a ≠ 0`, and
negation preserves a.e. strong measurability. -/
theorem BSAdmissibleStrip_neg {α : ℝ≥0} {ω : R3 → ℝ → R3} {R S : ℝ}
    (h : BSAdmissibleStrip α ω R S) :
    BSAdmissibleStrip α (fun x t => - ω x t) R S := by
  obtain ⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩ := h
  refine ⟨hR, ?_, ⟨M, ?_⟩, ⟨H, ?_⟩, ⟨N, ?_⟩, ?_⟩
  · intro t ht x hx
    exact hsupp t ht x (by simpa using hx)
  · intro t ht y
    simpa using hM t ht y
  · intro t ht
    refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
    rw [dist_neg_neg]
    exact (hH t ht).dist_le x y
  · intro y t ht t' ht'
    rw [show - ω y t - - ω y t' = - (ω y t - ω y t') by abel, norm_neg]
    exact hN y t ht t' ht'
  · intro t ht
    exact (hmeas t ht).neg

/-- **The time-regularity of the slices of a negated vorticity**: `∂ₜ(−ω) = −∂ₜω`, so the
differentiability, the uniform bound and the measurability of the derivative slices all transport. -/
theorem TimeDerivStrip_neg {ω : R3 → ℝ → R3} {S : ℝ} (h : TimeDerivStrip ω S) :
    TimeDerivStrip (fun x t => - ω x t) S := by
  obtain ⟨hdiff, ⟨M₁, hM₁⟩, hmeas⟩ := h
  refine ⟨fun t ht y => ?_, ⟨M₁, fun t ht y => ?_⟩, fun t ht => ?_⟩
  · have h2 : timeDeriv (fun x s => - ω x s) y t = - timeDeriv ω y t :=
      timeDeriv_neg_field ω y t
    rw [h2]
    exact (hdiff t ht y).neg
  · rw [timeDeriv_neg_field, norm_neg]
    exact hM₁ t ht y
  · have h' : (fun y : R3 => timeDeriv (fun x s => - ω x s) y t)
        = fun y : R3 => - timeDeriv ω y t := by
      funext y
      rw [timeDeriv_neg_field]
    rw [h']
    exact (hmeas t ht).neg

/-- **The time-Hölder continuity of `∂_tω` for a negated vorticity**: invariant. -/
theorem TimeDerivStripHolder_neg {α : ℝ≥0} {ω : R3 → ℝ → R3} {S : ℝ}
    (h : TimeDerivStripHolder α ω S) :
    TimeDerivStripHolder α (fun x t => - ω x t) S := by
  obtain ⟨N₁, hN₁⟩ := h
  refine ⟨N₁, fun y t ht t' ht' => ?_⟩
  rw [timeDeriv_neg_field, timeDeriv_neg_field,
    show - timeDeriv ω y t - - timeDeriv ω y t' = - (timeDeriv ω y t - timeDeriv ω y t')
      by abel, norm_neg]
  exact hN₁ y t ht t' ht'

/-- **The full admissible-strip bundle of a negated vorticity** (design correction 1). -/
theorem BSAdmissibleStripFull_neg {α : ℝ≥0} {ω : R3 → ℝ → R3} {R S : ℝ}
    (h : BSAdmissibleStripFull α ω R S) :
    BSAdmissibleStripFull α (fun x t => - ω x t) R S := by
  obtain ⟨hstrip, htd, htdh⟩ := h
  exact ⟨BSAdmissibleStrip_neg hstrip, TimeDerivStrip_neg htd, TimeDerivStripHolder_neg htdh⟩

end Work.FTS.FireFix
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.Fstar_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise bounds for the fundamental profile `F_* = Fstar (3α)`

The reference profile of Elgindi's construction is `F_* = Fstar (3α)`, i.e.
`F_*(z,θ) = 3α · (Γ(θ)/c(3α)) · 2z/(1+z)²` with `Γ(θ) = (sin θ cos²θ)^α` (because
`Gam (3α) θ = (sin θ cos²θ)^((3α)/3) = (sin θ cos²θ)^α`) and `c(3α) ∈ [1/10, 10]`.

This module proves the three pointwise bounds of the *firing* of `F_*` into the physical
vorticity: the sup bound, the `z`-derivative bound, and the angular-derivative bound with the
singular weights `sin^{α-1}θ · cos^{2α-1}θ`, for `0 < α ≤ 1/3`.

The route: on `Iθ` the base `u = sin θ cos²θ` lies in `[0,1]` and `2z/(1+z)² ≤ 1/2` for
`z ≥ 0`, so `|F_*| ≤ 3α·10·1/2 = 15α`; the `z`-derivative is
`3α(Γ/c)·2(1-z)/(1+z)³` with `|2(1-z)/(1+z)³| ≤ 2`, giving `≤ 3α·10·2 = 60α`; and the
angular derivative is `3α·(2z/(1+z)²)/c · ∂_θΓ`, with (on the open quadrant)
`∂_θΓ = α·q(θ)·Γ/sin(2θ)` (`dthU_Gam`) where `q = cos2θ - 1/3` satisfies `|q| ≤ 4/3` and
`Γ/sin(2θ) = (1/2)·sin^{α-1}θ·cos^{2α-1}θ`, giving `≤ 3α·(1/2)·10·(2/3)α·(…) = 10α²·(…)`.

At the endpoints `θ = 0, π/2` the angular profile is `sin^αθ` resp. `cos^{2α}θ`-like, which is
*not* differentiable there (for `α < 1` resp. `2α < 1`); since Mathlib's `deriv` is `0` at
points of non-differentiability, the angular derivative vanishes at the endpoints, where the
right-hand side also vanishes.
-/

noncomputable section

open Filter Topology MeasureTheory
open scoped Real

namespace Work.FTS.FireFix.Clauses

/-! ## The angular profile `Γ(3α) = (sin θ cos²θ)^α` -/

/-- `Γ(3α) = (sin θ cos²θ)^α`: the exponent of `Gam` is `(3α)/3 = α`. -/
theorem gam_three (α θ : ℝ) :
    Work.Spaces.Gam (3 * α) θ = (Real.sin θ * Real.cos θ ^ 2) ^ α := by
  rw [Work.Spaces.Gam]
  congr 1
  ring

/-- The auxiliary angular coefficient `q(θ) = cos(2θ) - 1/3` of `D_θΓ = α q Γ` is bounded by
`4/3`. -/
theorem qfun_abs_le {θ : ℝ} : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
  rw [Work.Spaces.qfun_apply, abs_le]
  constructor <;> nlinarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]

/-- On the open quadrant, `Γ(3α) θ = sin^αθ · cos^{2α}θ`. -/
theorem gam_three_eq {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Gam (3 * α) θ = (Real.sin θ) ^ α * (Real.cos θ) ^ (2 * α) := by
  have hs : 0 ≤ Real.sin θ :=
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])).le
  have hc : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).le
  have hc2 : (Real.cos θ ^ 2) ^ α = (Real.cos θ) ^ (2 * α) := by
    rw [← Real.rpow_two (Real.cos θ), ← Real.rpow_mul hc (2 : ℝ) α]
  rw [gam_three, Real.mul_rpow hs (by positivity), hc2]

/-! ## The angular derivative of `Γ(3α)` on the open quadrant -/

/-- On the open quadrant `(0, π/2)` the angular derivative of `Γ(3α)` is bounded by
`2α sin^{α-1}θ cos^{2α-1}θ`. -/
theorem deriv_gam_three_bound {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |deriv (fun t : ℝ => Work.Spaces.Gam (3 * α) t) θ|
      ≤ 2 * α * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) := by
  have hα3 : 0 < 3 * α := by linarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hG0 : 0 ≤ Work.Spaces.Gam (3 * α) θ :=
    Real.rpow_nonneg (mul_nonneg hs.le (sq_nonneg _)) _
  have hdth := Work.Spaces.dthU_Gam (3 * α) θ hα3 hθ
  rw [Work.Spaces.dthU_apply] at hdth
  have hderiv : deriv (fun t : ℝ => Work.Spaces.Gam (3 * α) t) θ
      = 3 * α * Work.Spaces.qfun θ * Work.Spaces.Gam (3 * α) θ / Real.sin (2 * θ) := by
    rw [eq_div_iff (ne_of_gt hs2), mul_comm]
    exact hdth
  have hGid := gam_three_eq (α := α) (θ := θ) hθ
  have e1 : (Real.sin θ) ^ α = (Real.sin θ) ^ (α - 1) * Real.sin θ := by
    conv_lhs => rw [show α = (α - 1) + 1 from by ring]
    rw [Real.rpow_add hs (α - 1) 1, Real.rpow_one]
  have e2 : (Real.cos θ) ^ (2 * α) = (Real.cos θ) ^ (2 * α - 1) * Real.cos θ := by
    conv_lhs => rw [show 2 * α = (2 * α - 1) + 1 from by ring]
    rw [Real.rpow_add hc (2 * α - 1) 1, Real.rpow_one]
  have hA : 0 ≤ (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) :=
    mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hc.le _)
  have hkey : 3 * α * |Work.Spaces.qfun θ| ≤ 4 * α := by
    nlinarith [qfun_abs_le (θ := θ), hα, abs_nonneg (Work.Spaces.qfun θ)]
  rw [hderiv, abs_div, abs_of_pos hs2, abs_mul, abs_mul, abs_of_pos hα3, abs_of_nonneg hG0,
    div_le_iff₀ hs2, hGid, e1, e2, Real.sin_two_mul]
  have hB : 0 ≤ Real.sin θ * Real.cos θ := mul_nonneg hs.le hc.le
  nlinarith [hkey, hA, hB, mul_nonneg hA hB]

/-! ## Non-differentiability of `(sin t cos²t)^p` and `(cos t sin²t)^p` at `0`

Both functions have a cusp at `t = 0` (`t^p` resp. `t^{2p}` behaviour), hence Mathlib's
`deriv` (which is `0` at points of non-differentiability) vanishes there. This is what makes
the endpoint cases `θ = 0` and `θ = π/2` of the angular bound trivial. -/

/-- If `φ` vanishes at `0` and is bounded below by `c t^m` near `0⁺` with `m p < 1`, then
`t ↦ φ t ^ p` is not differentiable at `0`: its difference quotient dominates
`c^p t^{mp-1} → +∞`. -/
theorem not_differentiableAt_rpow_of_eventually_ge {φ : ℝ → ℝ} {c p m : ℝ}
    (hφ0 : φ 0 = 0) (hc : 0 < c) (hp : 0 < p) (hmp : m * p < 1)
    (hφ : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), c * t ^ m ≤ φ t) :
    ¬ DifferentiableAt ℝ (fun t => φ t ^ p) 0 := by
  intro hdiff
  have hslope : Tendsto (fun t => φ t ^ p / t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (deriv (fun t => φ t ^ p) 0)) := by
    have h := hdiff.hasDerivAt.tendsto_slope_zero_right
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, hφ0, sub_zero, smul_eq_mul, Real.zero_rpow hp.ne']
    ring
  have hlow : Tendsto (fun t => c ^ p * t ^ (m * p - 1)) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    Filter.Tendsto.const_mul_atTop (Real.rpow_pos_of_pos hc p)
      (tendsto_rpow_neg_nhdsGT_zero (by linarith))
  have hev : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), c ^ p * t ^ (m * p - 1) ≤ φ t ^ p / t := by
    filter_upwards [hφ, self_mem_nhdsWithin] with t hle ht
    have ht0 : 0 < t := ht
    have h1 : (c * t ^ m) ^ p ≤ (φ t) ^ p :=
      Real.rpow_le_rpow (by positivity) hle hp.le
    have h2 : (c * t ^ m) ^ p = c ^ p * t ^ (m * p) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg ht0.le m), Real.rpow_mul ht0.le m p]
    rw [h2] at h1
    have h3 : c ^ p * t ^ (m * p) / t = c ^ p * t ^ (m * p - 1) := by
      rw [Real.rpow_sub ht0 (m * p) 1, Real.rpow_one]
      ring
    rw [← h3]
    exact div_le_div_of_nonneg_right h1 ht0.le
  have hbig : Tendsto (fun t => φ t ^ p / t) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    rw [Filter.tendsto_atTop] at hlow ⊢
    intro b
    filter_upwards [hlow b, hev] with t hb hle
    linarith
  exact not_tendsto_nhds_of_tendsto_atTop hbig _ hslope

/-- `sin t / t → 1` at `0⁺` (the difference quotient of `sin` at `0`). -/
theorem sin_div_tendsto_zero :
    Tendsto (fun t : ℝ => Real.sin t / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
  rw [Real.cos_zero] at h
  refine h.congr' ?_
  filter_upwards with t
  simp only [zero_add, Real.sin_zero, sub_zero, smul_eq_mul]
  ring

/-- `cos t → 1` at `0⁺`. -/
theorem cos_tendsto_zero : Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h0 : Tendsto Real.cos (nhds 0) (nhds 1) := by
    rw [← Real.cos_zero]
    exact Real.continuous_cos.continuousAt (x := 0)
  exact h0.mono_left inf_le_left

/-- `cos²t → 1` at `0⁺`. -/
theorem cos_sq_tendsto_zero :
    Tendsto (fun t : ℝ => Real.cos t ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h : Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := cos_tendsto_zero
  simpa using h.pow 2

/-- `t ↦ (sin t cos²t)^p` is not differentiable at `0` for `0 < p < 1` (`sin t cos²t ∼ t`). -/
theorem not_differentiableAt_sinCosSq_rpow {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ¬ DifferentiableAt ℝ (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ p) 0 := by
  refine not_differentiableAt_rpow_of_eventually_ge
    (φ := fun t => Real.sin t * Real.cos t ^ 2) (c := 1 / 4) (m := 1)
    (by norm_num) (by norm_num) hp (by linarith) ?_
  filter_upwards [sin_div_tendsto_zero.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    cos_sq_tendsto_zero.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    self_mem_nhdsWithin] with t h1 h2 ht
  have ht0 : 0 < t := ht
  have hs : t / 2 < Real.sin t := by
    have := (lt_div_iff₀ ht0).mp h1
    linarith
  have hs' : 0 < Real.sin t := by linarith
  have hA : Real.sin t * (1 / 2) < Real.sin t * Real.cos t ^ 2 := mul_lt_mul_of_pos_left h2 hs'
  have hB : t / 2 * (1 / 2) < Real.sin t * (1 / 2) := mul_lt_mul_of_pos_right hs (by norm_num)
  rw [Real.rpow_one]
  nlinarith [hA, hB]

/-- `t ↦ (cos t sin²t)^p` is not differentiable at `0` for `0 < p` and `2p < 1`
(`cos t sin²t ∼ t²`). -/
theorem not_differentiableAt_cosSinSq_rpow {p : ℝ} (hp : 0 < p) (hp2 : 2 * p < 1) :
    ¬ DifferentiableAt ℝ (fun t : ℝ => (Real.cos t * Real.sin t ^ 2) ^ p) 0 := by
  refine not_differentiableAt_rpow_of_eventually_ge
    (φ := fun t => Real.cos t * Real.sin t ^ 2) (c := 1 / 8) (m := 2)
    (by norm_num) (by norm_num) hp (by linarith) ?_
  filter_upwards [sin_div_tendsto_zero.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    cos_tendsto_zero.eventually (isOpen_Ioi.mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    self_mem_nhdsWithin] with t h1 h2 ht
  have ht0 : 0 < t := ht
  have hs : t / 2 < Real.sin t := by
    have := (lt_div_iff₀ ht0).mp h1
    linarith
  have hs' : 0 < Real.sin t := by linarith
  have hA : t / 2 * (t / 2) < Real.sin t * Real.sin t := by nlinarith [hs, hs']
  have hB : Real.cos t * (t / 2 * (t / 2)) < Real.cos t * (Real.sin t * Real.sin t) :=
    mul_lt_mul_of_pos_left hA (by linarith)
  rw [Real.rpow_two]
  nlinarith [hB]

/-! ## The endpoint values of the angular derivative -/

/-- `∂_θ (sin θ cos²θ)^α = 0` at `θ = 0` for `0 < α < 1`. -/
theorem deriv_sinCosSq_rpow_zero {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    deriv (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α) 0 = 0 :=
  deriv_zero_of_not_differentiableAt (not_differentiableAt_sinCosSq_rpow hα hα1)

/-- The shifted profile `t ↦ (sin t cos²t)^α` equals `s ↦ (cos s sin²s)^α` composed with
`t ↦ π/2 - t`; hence it is not differentiable at `π/2`. -/
theorem deriv_gam_three_piHalf {α : ℝ} (hα : 0 < α) (hα2 : 2 * α < 1) :
    deriv (fun t : ℝ => Work.Spaces.Gam (3 * α) t) (π / 2) = 0 := by
  have hfun : (fun t : ℝ => Work.Spaces.Gam (3 * α) t)
      = fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α := funext fun t => gam_three α t
  have hshift : (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α)
      = fun t : ℝ => (Real.cos (π / 2 - t) * Real.sin (π / 2 - t) ^ 2) ^ α := by
    funext t
    rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [hfun, hshift]
  apply deriv_zero_of_not_differentiableAt
  have hcomp : (fun t : ℝ => (Real.cos (π / 2 - t) * Real.sin (π / 2 - t) ^ 2) ^ α)
      = (fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α) ∘ (fun t : ℝ => π / 2 - t) := rfl
  rw [hcomp]
  intro hd
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α) 0 := by
    have h1 : DifferentiableAt ℝ (((fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α)
        ∘ (fun t : ℝ => π / 2 - t)) ∘ (fun t : ℝ => π / 2 - t)) 0 :=
      DifferentiableAt.comp (x := 0) (by simpa using hd) (by fun_prop)
    have heq : (((fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α)
        ∘ (fun t : ℝ => π / 2 - t)) ∘ (fun t : ℝ => π / 2 - t))
        = (fun s : ℝ => (Real.cos s * Real.sin s ^ 2) ^ α) := by
      funext s
      simp only [Function.comp_apply]
      rw [show π / 2 - (π / 2 - s) = s from by ring]
    rwa [heq] at h1
  exact not_differentiableAt_cosSinSq_rpow hα hα2 hdiff

/-- `∂_θ (sin θ cos²θ)^α = 0` at `θ = π/2` for `2α < 1`. -/
theorem deriv_sinCosSq_rpow_piHalf {α : ℝ} (hα : 0 < α) (hα2 : 2 * α < 1) :
    deriv (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α) (π / 2) = 0 := by
  have hfun : (fun t : ℝ => Work.Spaces.Gam (3 * α) t)
      = fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α := funext fun t => gam_three α t
  rw [← hfun]
  exact deriv_gam_three_piHalf hα hα2

/-- The angular derivative bound in terms of the profile `t ↦ (sin t cos²t)^α`. -/
theorem deriv_sinCosSq_rpow_bound {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |deriv (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α) θ|
      ≤ 2 * α * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) := by
  have hfun : (fun t : ℝ => Work.Spaces.Gam (3 * α) t)
      = fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α := funext fun t => gam_three α t
  rw [← hfun]
  exact deriv_gam_three_bound hα hθ

/-! ## Bounds for the radial profile `F_{*,rad}(z) = 2z/(1+z)²` -/

/-- `2z/(1+z)² ≥ 0` for `z ≥ 0`. -/
theorem fm_fstar_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Work.FM.Fstar z := by
  rw [Work.FM.Fstar]; positivity

/-- `2z/(1+z)² ≤ 1/2` for `z ≥ 0`. -/
theorem fm_fstar_le_half {z : ℝ} (hz : 0 ≤ z) : Work.FM.Fstar z ≤ 1 / 2 := by
  rw [Work.FM.Fstar, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z)]

/-- `|∂_z (2z/(1+z)²)| = |2(1-z)/(1+z)³| ≤ 2` for `z ≥ 0`. -/
theorem abs_deriv_fm_fstar_le {z : ℝ} (hz : 0 ≤ z) : |deriv Work.FM.Fstar z| ≤ 2 := by
  have h1z : (-1 : ℝ) < z := by linarith
  rw [Work.FM.deriv_Fstar z h1z]
  have h3 : 0 < (1 + z) ^ 3 := by positivity
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos h3, div_le_iff₀ h3]
  have h4 : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  have h5 : (1 : ℝ) + z ≤ (1 + z) ^ 3 := by nlinarith [sq_nonneg z, hz]
  nlinarith [h4, h5]

/-- **The bounds for the fundamental profile `F_* = Fstar (3α)`.**  For `0 < α ≤ 1/3` the
profile and its `z`-derivative are bounded by `60α`, and its angular derivative by
`200α² sin^{α-1}θ cos^{2α-1}θ`, on `z ≥ 0`, `θ ∈ Iθ`. -/
theorem Fstar_bounds {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
        |Work.Construction.Fstar (3 * α) z θ| ≤ 60 * α) ∧
      (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
        |deriv (fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ) z| ≤ 60 * α) ∧
      (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
        |deriv (fun θ' : ℝ => Work.Construction.Fstar (3 * α) z θ') θ|
          ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)) := by
  have hα3 : 0 < 3 * α := by linarith
  have h3α1 : 3 * α ≤ 1 := by linarith
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c (3 * α) :=
    (Work.Spaces.c_bounds (3 * α) hα3 h3α1).1
  have hc0 : 0 < Work.Spaces.c (3 * α) := by linarith
  have hα1 : α < 1 := by linarith
  have hα2 : 2 * α < 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- the sup bound
    intro z θ hz hθ
    have hF0 : 0 ≤ Work.FM.Fstar z := fm_fstar_nonneg hz
    have hF1 : Work.FM.Fstar z ≤ 1 / 2 := fm_fstar_le_half hz
    have hK0 : 0 ≤ 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α) := by positivity
    have hK1 : 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α) ≤ 15 * α := by
      rw [div_le_iff₀ hc0]
      nlinarith [hF1, hc10, hF0, hα]
    have hB0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := (Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ).1
    have hB1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := (Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ).2
    have hBle : (Real.sin θ * Real.cos θ ^ 2) ^ α ≤ 1 := Real.rpow_le_one hB0 hB1 hα.le
    have hBnn : 0 ≤ (Real.sin θ * Real.cos θ ^ 2) ^ α := Real.rpow_nonneg hB0 α
    have hfac : Work.Construction.Fstar (3 * α) z θ
        = (3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α))
            * (Real.sin θ * Real.cos θ ^ 2) ^ α := by
      rw [Work.Construction.Fstar, gam_three]; ring
    rw [hfac, abs_mul, abs_of_nonneg hK0, abs_of_nonneg hBnn]
    calc 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α)
          * (Real.sin θ * Real.cos θ ^ 2) ^ α
        ≤ 15 * α * 1 := mul_le_mul hK1 hBle hBnn (by linarith)
      _ = 15 * α := by ring
      _ ≤ 60 * α := by linarith
  · -- the `z`-derivative bound
    intro z θ hz hθ
    have hG0 : 0 ≤ Work.Spaces.Gam (3 * α) θ := (Work.Spaces.Gam_bounds (3 * α) θ hα3 hθ).1
    have hG1 : Work.Spaces.Gam (3 * α) θ ≤ 1 := (Work.Spaces.Gam_bounds (3 * α) θ hα3 hθ).2
    have hK0 : 0 ≤ 3 * α * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) := by positivity
    have hKle : 3 * α * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) ≤ 3 * α * 10 := by
      have h1 : Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α) ≤ 10 := by
        rw [div_le_iff₀ hc0]; nlinarith [hG1, hc10]
      nlinarith [h1, hα]
    have hfun : (fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ)
        = fun z' => (3 * α * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)))
            * Work.FM.Fstar z' := by
      funext z'; rw [Work.Construction.Fstar]
    rw [hfun, deriv_const_mul_field, abs_mul, abs_of_nonneg hK0]
    calc 3 * α * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)) * |deriv Work.FM.Fstar z|
        ≤ 3 * α * 10 * 2 :=
          mul_le_mul hKle (abs_deriv_fm_fstar_le hz) (abs_nonneg _) (by linarith)
      _ = 60 * α := by ring
  · -- the angular-derivative bound
    intro z θ hz hθ
    have hF0 : 0 ≤ Work.FM.Fstar z := fm_fstar_nonneg hz
    have hF1 : Work.FM.Fstar z ≤ 1 / 2 := fm_fstar_le_half hz
    have hK0 : 0 ≤ 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α) := by positivity
    have hKle : 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α) ≤ 15 * α := by
      rw [div_le_iff₀ hc0]
      nlinarith [hF1, hc10, hF0, hα]
    have hfun : (fun θ' : ℝ => Work.Construction.Fstar (3 * α) z θ')
        = fun θ' => (3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α))
            * (Real.sin θ' * Real.cos θ' ^ 2) ^ α := by
      funext θ'; rw [Work.Construction.Fstar, gam_three]; ring
    rw [hfun, deriv_const_mul_field, abs_mul, abs_of_nonneg hK0]
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · -- `θ = 0`: the angular derivative vanishes
      rw [← h0, deriv_sinCosSq_rpow_zero hα hα1]
      have hz0 : (0 : ℝ) ^ (α - 1) = 0 := Real.zero_rpow (by linarith)
      simp [Real.sin_zero, Real.cos_zero, hz0]
    · rcases eq_or_lt_of_le hθ.2 with hpi | hpi
      · -- `θ = π/2`: the angular derivative vanishes
        rw [hpi, deriv_sinCosSq_rpow_piHalf hα hα2]
        have hz0 : (0 : ℝ) ^ (2 * α - 1) = 0 := Real.zero_rpow (by linarith)
        simp [Real.sin_pi_div_two, Real.cos_pi_div_two, hz0]
      · -- `0 < θ < π/2`: the honest bound
        have hθ' : θ ∈ Set.Ioo 0 (π / 2) := ⟨h0, hpi⟩
        have hb := deriv_sinCosSq_rpow_bound hα hθ'
        have hs1 : 0 ≤ (Real.sin θ) ^ (α - 1) :=
          Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2]⟩) _
        have hc1 : 0 ≤ (Real.cos θ) ^ (2 * α - 1) :=
          Real.rpow_nonneg (Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hθ.1, Real.pi_pos], by linarith [Real.pi_pos]⟩) _
        calc 3 * α * Work.FM.Fstar z / Work.Spaces.c (3 * α)
              * |deriv (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ α) θ|
            ≤ 15 * α * (2 * α * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1)) :=
              mul_le_mul hKle hb (abs_nonneg _) (by linarith)
          _ = 30 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) := by ring
          _ ≤ 200 * α ^ 2 * (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) := by
              have hX : 0 ≤ (Real.sin θ) ^ (α - 1) * (Real.cos θ) ^ (2 * α - 1) :=
                mul_nonneg hs1 hc1
              nlinarith [hX, sq_nonneg α]

end Work.FTS.FireFix.Clauses
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PsiWt.aesm_pth_abs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.FireFix.Clauses.PsiWt

theorem aesm_pth_abs {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) q.1 (|q.2|))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
  obtain ⟨Ng, hNg⟩ := h.hg
  have hα : 0 < α := h.hα
  -- the joint Hölder bound of the package, at the fixed strip time `τ`
  have hHold : ∀ x ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
      ∀ y ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
      |g x.1 x.2 τ - g y.1 y.2 τ| ≤ Ng * (|x.1 - y.1| + |x.2 - y.2|) ^ α := by
    intro x hx y hy
    have := hNg.2.2 x.1 y.1 x.2 y.2 τ τ hx.1 hy.1 hx.2 hy.2 hτ hτ
    simpa using this
  -- the vanishing of the slice on the boundary of the closed quadrant
  have h0 : ∀ p ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
      (p.1 = 0 ∨ p.2 = 0 ∨ p.2 = Real.pi / 2) → g p.1 p.2 τ = 0 := by
    intro p hp hb
    rcases hb with h1 | h2 | h3
    · rw [h1]
      exact h.hquad0 τ hτ p.2 ⟨hp.2.1, hp.2.2⟩
    · rw [h2]
      exact (h.hvt τ hτ).1 p.1
    · rw [h3]
      exact (h.hvt τ hτ).2 p.1
  -- continuity of the zero-extension of the slice
  have hcont : Continuous (fun p : ℝ × ℝ =>
      if p ∈ (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) then g p.1 p.2 τ else 0) :=
    Work.FTS.FireFix.Clauses.PsiWt.ZExt.continuous_zeroExt_of_holder
      hNg.1 hα (φ := fun p : ℝ × ℝ => g p.1 p.2 τ) hHold h0
  -- the a.e. identification of the derivatives
  have hae := Work.FTS.FireFix.Clauses.PsiWt.ZExt.ae_deriv_zeroExt_eq
    (Φ := fun z θ' => g z θ' τ)
  -- measurability of the parametrised derivative of the extension
  have hmeasF : Measurable (fun p : ℝ × ℝ =>
      deriv (fun θ' => (if p.1 ∈ Set.Ici (0 : ℝ) ∧ θ' ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
        then g p.1 θ' τ else 0)) p.2) := by
    refine measurable_deriv_with_param (𝕜 := ℝ) (F := ℝ) (α := ℝ)
      (f := fun z θ' => (if z ∈ Set.Ici (0 : ℝ) ∧ θ' ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
        then g z θ' τ else 0)) ?_
    exact hcont
  have hφ : Measurable (fun q : ℝ × ℝ => (q.1, |q.2|)) :=
    measurable_fst.prodMk ((measurable_abs (α := ℝ)).comp measurable_snd)
  have hmeas2 : Measurable (fun q : ℝ × ℝ =>
      deriv (fun θ' => (if q.1 ∈ Set.Ici (0 : ℝ) ∧ θ' ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
        then g q.1 θ' τ else 0)) (|q.2|)) := hmeasF.comp hφ
  exact ((hmeas2.aestronglyMeasurable.restrict).congr hae)

end Work.FTS.FireFix.Clauses.PsiWt
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_Dth_sq_sin_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `(D_θ (gSlice g τ))² · sin(2|θ|)^{-γ}` on the box `(0,∞) × (-π/2, π/2)`

The clause `PsiWt.integrableOn_Dth_sq_sin_rpow` of the FireFix pressure input.

**The mathematics.**  With `f = gSlice g τ` and `γ = gam (pExp α) = 1 + 3α/10 > 1`, the
integrand is `(D_θf)² · sin(2|θ|)^{-γ} = sin(2|θ|)^{2-γ} · (∂_θf)²` (since `D_θ = sin 2θ · ∂_θ`),
i.e. the angular derivative weighted by the integrability weight of the `ℋ⁴`-norm with the
radial weight `w²` removed.  Since `w(z) = (1+z)²/z² ≥ 1` for `z > 0`, removing it only makes
the integrand *smaller*, and `hH4 : HkMem (pExp α) 4 f` gives, through
`Work.Spaces.sq_le_HkIntegrand_mixed` applied to the slot `(i,j) = (1,0)` (whose base is
`mixed 0 1 f = D_θf`, definitionally), integrability of the dominating `ℋ⁴`-integrand.

**The formal difficulty** is *not* the estimate but the measurability bookkeeping: `HkMem` only
provides integrability of the *angular slices* `θ ↦ HkIntegrand … z θ` for each `z ∈ Iz` and of
the *partially integrated* `z ↦ ∫_θ HkIntegrand … z θ`, and the joint (product-measure) a.e.
strong measurability of the integrand is *not* implied by those two facts alone (see
`Submission/Work/Spaces/Slots/lintegral_DzIter_le_HkSq.lean` for a machine-checked diagnosis of
exactly this gap).  The way out is that the only genuinely `θ`-differentiated quantity occurring
is `D_θf = sin(2θ) ∂_θ (g z · τ)`, and the *parametric* derivative
`(z,θ) ↦ deriv (fun θ' => g z θ' τ) θ` **is** Borel measurable: `g` is `α`-Hölder on the box by
the `Jet` field, so (clamping both variables into the box) it extends to a *continuous* function
on `ℝ²`, and Mathlib's `measurable_deriv_with_param` then gives the measurability of the
parametric derivative.  With joint measurability of the integrand in hand, the
product-integrability criterion `MeasureTheory.integrable_prod_iff` needs exactly the two facts
`HkMem` provides (slice integrability and integrability of the partially integrated majorant) —
in that `z`-outer order, so no one-sided Tonelli exchange is required.  The lower half of the
`θ`-interval is handled by the reflection `θ ↦ -θ`.

**Layout.**  `clampθ` (the clamp into `Iθ`), the delegated `continuousOn_box_of_regPkg` (the
Hölder slice of `g`),
`Gclamp` (`g` clamped into the box, jointly continuous on `ℝ²`), `measurable_param_deriv`,
`deriv_Gclamp_eq_pth` (the parametric derivative computes `pth`), `aesm_Dth_sq` (joint
measurability of the integrand), `slice_bound` (the pointwise domination: its open-quadrant half
is the delegated `Dth_sq_sin_rpow_le_HkIntegrand`, the two endpoints give `0`),
`integrableOn_positive` (product integrability on the upper half `(0,∞) × (0,π/2)` through
`integrable_prod_iff`), `integrableOn_neg_snd_reflect` (the reflection transfer; the sibling
module `…PsiWt.integrableOn_neg_snd` declares the same statement under the requested name), and
the assembly.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology ENNReal NNReal

namespace Work.FTS.FireFix.Clauses.PsiWt

set_option autoImplicit false

/-! ## Auxiliary measure identities -/

/-- On `ℝ × ℝ` the Lebesgue measure is the product of the two Lebesgue measures, so
restrictions to a product of intervals split. -/
theorem prod_restrict_volume (s t : Set ℝ) :
    (volume.restrict s).prod (volume.restrict t) = volume.restrict (s ×ˢ t) := by
  rw [Measure.prod_restrict, show (volume.prod volume : Measure (ℝ × ℝ)) = volume from rfl]

/-! ## The clamp of `ℝ` into `Iθ = [0, π/2]` -/

/-- The clamp `θ ↦ max 0 (min θ (π/2))`, whose range is `Iθ`. -/
def clampθ (θ : ℝ) : ℝ := max 0 (min θ (Real.pi / 2))

theorem clampθ_mem (θ : ℝ) : clampθ θ ∈ Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc]
  exact ⟨le_max_left _ _, max_le (by linarith [Real.pi_pos]) (min_le_right _ _)⟩

theorem clampθ_eq_self {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : clampθ θ = θ := by
  simp only [clampθ, min_eq_left hθ.2.le, max_eq_right hθ.1.le]

theorem continuous_clampθ : Continuous clampθ := by
  unfold clampθ
  exact continuous_const.max (continuous_id.min continuous_const)


/-! ## Measurability of a real power -/

theorem measurable_rpow_const (c : ℝ) : Measurable (fun x : ℝ => x ^ c) := by
  refine measurable_of_continuousOn_compl_singleton (0 : ℝ) fun x hx => ?_
  exact (Real.continuousAt_rpow_const x c (Or.inl (by simpa using hx))).continuousWithinAt

/-! ## Joint continuity of a slice of `g` on the closed box -/

/-! ## The clamped profile and its parametric derivative -/

/-- `g(·,·,τ)` clamped into the closed box `Iz ×ˢ Iθ` in both variables.  On `z > 0`,
`θ ∈ (0, π/2)` it agrees with `g(·,·,τ)` on a neighbourhood of that point. -/
def Gclamp {g : ℝ → ℝ → ℝ → ℝ} (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => g (max z 0) (clampθ θ) τ

theorem continuous_uncurry_Gclamp {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Continuous (Function.uncurry (Gclamp (g := g) τ)) := by
  have hbox := continuousOn_box_of_regPkg h hτ
  have hmap : Continuous fun p : ℝ × ℝ => (max p.1 0, clampθ p.2) :=
    (continuous_fst.max continuous_const).prodMk (continuous_clampθ.comp continuous_snd)
  have hmaps : ∀ p : ℝ × ℝ, (max p.1 0, clampθ p.2) ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    fun p => ⟨by rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_max_right p.1 0,
      clampθ_mem p.2⟩
  have hcomp := hbox.comp_continuous hmap hmaps
  have hfun : (Function.uncurry (Gclamp (g := g) τ))
      = ((fun p : ℝ × ℝ => g p.1 p.2 τ) ∘ fun p : ℝ × ℝ => (max p.1 0, clampθ p.2)) := rfl
  rw [hfun]
  exact hcomp

/-- The parametric derivative of the clamped profile is Borel measurable on `ℝ²`. -/
theorem measurable_param_deriv {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Measurable (fun p : ℝ × ℝ => deriv (fun θ' => Gclamp (g := g) τ p.1 θ') p.2) :=
  measurable_deriv_with_param (𝕜 := ℝ) (f := Gclamp (g := g) τ) (continuous_uncurry_Gclamp h hτ)

/-- On the open quadrant the parametric derivative of the clamped profile is `∂_θ` of the slice
of `g`. -/
theorem deriv_Gclamp_eq_pth {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Gclamp (g := g) τ z θ') θ
      = Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z θ := by
  have h1 : (fun θ' => Gclamp (g := g) τ z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ' τ) :=
    eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hθ) (fun θ' hθ' => by
      simp only [Gclamp, max_eq_left hz.le, clampθ_eq_self hθ'])
  rw [h1.deriv_eq]
  rfl

/-! ## Joint measurability of the integrand on the upper half-box -/

/-- The integrand `(D_θf)²·sin(2θ)^{-γ}` (`f = gSlice g τ`) is a.e. strongly measurable for the
product measure on `(0,∞) × (0,π/2)`. -/
theorem aesm_Dth_sq {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    AEStronglyMeasurable (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 q.2) ^ 2
        * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α))))
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
  have hD := measurable_param_deriv h hτ
  have hsin : Measurable (fun q : ℝ × ℝ => Real.sin (2 * q.2)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_snd)
  have hnice : Measurable (fun q : ℝ × ℝ =>
      (Real.sin (2 * q.2) * deriv (fun θ' => Gclamp (g := g) τ q.1 θ') q.2) ^ 2
        * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α)))) :=
    ((hsin.mul hD).pow_const 2).mul ((measurable_rpow_const _).comp hsin)
  refine hnice.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with q hq
  rw [Work.Spaces.Dth, ← deriv_Gclamp_eq_pth (g := g) (τ := τ) hq.1 hq.2]


/-! ## The pointwise domination by the `ℋ⁴`-integrand -/

/-- The pointwise domination on the closed interval `[0, π/2]` (the two endpoints give `0`). -/
theorem slice_bound {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a))
      ≤ Work.Spaces.HkIntegrand a 4 f z θ := by
  have hgam : 0 < Work.Spaces.gam a := by rw [Work.Spaces.gam]; linarith
  by_cases hint : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · exact Dth_sq_sin_rpow_le_HkIntegrand ha f hz hint
  · have hfl : θ = 0 ∨ θ = Real.pi / 2 := by
      rw [Set.mem_Ioo, not_and_or] at hint
      rcases hint with h | h
      · exact Or.inl (le_antisymm (not_lt.mp h) hθ.1)
      · exact Or.inr (le_antisymm hθ.2 (not_lt.mp h))
    rcases hfl with h | h
    · subst h
      have hzero : (Real.sin (2 * (0 : ℝ))) ^ (-(Work.Spaces.gam a)) = 0 := by
        rw [show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
          Real.zero_rpow (x := -(Work.Spaces.gam a)) (by linarith)]
      rw [hzero, mul_zero]
      exact Work.Spaces.HkIntegrand_nonneg a 4 f z 0
    · subst h
      have hzero : (Real.sin (2 * (Real.pi / 2))) ^ (-(Work.Spaces.gam a)) = 0 := by
        rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
          Real.zero_rpow (x := -(Work.Spaces.gam a)) (by linarith)]
      rw [hzero, mul_zero]
      exact Work.Spaces.HkIntegrand_nonneg a 4 f z (Real.pi / 2)

/-! ## The product integrability on the upper half-box -/

/-- The integrand `(D_θf)² sin(2θ)^{-γ}` is integrable on `(0,∞) × (0,π/2)`. -/
theorem integrableOn_positive {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 q.2) ^ 2
        * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α))))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hα : 0 < α := h.hα
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hmem := h.hH4 τ hτ
  set F : ℝ × ℝ → ℝ := fun q =>
    (Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 q.2) ^ 2
      * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α))) with hF
  have hν : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hprod : (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict Work.Spaces.Iθ)
      = volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Measure.restrict_congr_set hν, prod_restrict_volume]
  have hFnn : ∀ z θ : ℝ, θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) → 0 ≤ F (z, θ) := fun z θ hθ => by
    rw [hF]
    refine mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have haesm : AEStronglyMeasurable F
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [hprod]
    exact aesm_Dth_sq h hτ
  have hslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun θ : ℝ => F (z, θ)) (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz, Set.mem_Ici]; exact hz.le
    have hKs : Integrable (fun θ => Work.Spaces.HkIntegrand (Work.FTS.Regularity.pExp α) 4
        (Work.FTS.Regularity.gSlice g τ) z θ) (volume.restrict Work.Spaces.Iθ) := hmem.1 z hzIz
    have hslice_meas : AEStronglyMeasurable (fun θ : ℝ => F (z, θ))
        (volume.restrict Work.Spaces.Iθ) := by
      have hderiv : Measurable (fun θ : ℝ => deriv
          (fun θ' => Work.FTS.Regularity.gSlice g τ z θ') θ) :=
        measurable_deriv (fun θ' => Work.FTS.Regularity.gSlice g τ z θ')
      have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.measurable_sin.comp (measurable_const.mul measurable_id)
      have hmeas : Measurable (fun θ : ℝ =>
          (Real.sin (2 * θ) * deriv (fun θ' => Work.FTS.Regularity.gSlice g τ z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α)))) :=
        (((hsin.mul hderiv).pow_const 2)).mul ((measurable_rpow_const _).comp hsin)
      have heq : (fun θ : ℝ => F (z, θ)) = (fun θ : ℝ =>
          (Real.sin (2 * θ) * deriv (fun θ' => Work.FTS.Regularity.gSlice g τ z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam (Work.FTS.Regularity.pExp α)))) := by
        funext θ
        simp only [hF, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq]
      exact hmeas.aestronglyMeasurable
    refine Integrable.mono' hKs hslice_meas ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      with θ hθ
    rw [Real.norm_of_nonneg (hFnn z θ hθ), hF]
    exact slice_bound hp0 _ hz hθ
  have houter : Integrable (fun z => ∫ θ, ‖F (z, θ)‖ ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hA : Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Regularity.gSlice g τ) z θ) (volume.restrict Work.Spaces.Iz) := hmem.2
    have hA' : Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Regularity.gSlice g τ) z θ) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      Integrable.mono_measure hA (Measure.restrict_mono Set.Ioi_subset_Ici_self le_rfl)
    refine Integrable.mono' hA' (haesm.norm.integral_prod_right') ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz, Set.mem_Ici]; exact hz.le
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, ‖F (z, θ)‖ :=
      integral_nonneg_of_ae (Eventually.of_forall fun θ => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => norm_nonneg _)
      (hmem.1 z hzIz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
      with θ hθ
    rw [Real.norm_of_nonneg (hFnn z θ hθ), hF]
    exact slice_bound hp0 _ hz hθ
  have key : Integrable F
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integrable_prod_iff (f := F) haesm).mpr ⟨hslice, houter⟩
  rw [IntegrableOn, ← hprod]
  exact key

/-! ## Reflection in the angular variable -/

/-- Integrability on the upper half-box transfers to the lower half-box by the reflection
`θ ↦ -θ`. -/
theorem integrableOn_neg_snd_reflect {f : ℝ × ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => f p)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => f (p.1, -p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0) := by
  have hpre : Neg.neg ⁻¹' Set.Ioo (0 : ℝ) (Real.pi / 2) = Set.Ioo (-(Real.pi / 2)) 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hneg : (volume.restrict (Set.Ioo (-(Real.pi / 2)) 0)).map Neg.neg
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := measurableEmbedding_neg.restrict_map (volume : Measure ℝ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2))
    rw [hpre, Measure.map_neg_eq_self (volume : Measure ℝ)] at h
    exact h.symm
  have he : MeasurableEmbedding (fun p : ℝ × ℝ => (p.1, -p.2)) := by
    have hfun : (fun p : ℝ × ℝ => (p.1, -p.2))
        = (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ) :
            ℝ × ℝ → ℝ × ℝ) := rfl
    rw [hfun]
    exact (MeasurableEquiv.prodCongr _ _).measurableEmbedding
  have hmap : (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)).map
        (fun p : ℝ × ℝ => (p.1, -p.2))
      = volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h2 : (fun p : ℝ × ℝ => (p.1, -p.2)) = Prod.map id Neg.neg := rfl
    rw [← prod_restrict_volume (Set.Ioi (0 : ℝ)) (Set.Ioo (-(Real.pi / 2)) 0), h2,
      ← Measure.map_prod_map (volume.restrict (Set.Ioi (0 : ℝ)))
        (volume.restrict (Set.Ioo (-(Real.pi / 2)) 0)) measurable_id measurable_neg,
      Measure.map_id, hneg]
    exact prod_restrict_volume _ _
  have hiff : Integrable f
        (Measure.map (fun p : ℝ × ℝ => (p.1, -p.2))
          (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)))
      ↔ Integrable (fun p : ℝ × ℝ => f (p.1, -p.2))
          (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)) :=
    MeasurableEmbedding.integrable_map_iff he
  rw [hmap] at hiff
  exact hiff.mp (by simpa only [IntegrableOn] using h)

/-! ## The target -/

theorem integrableOn_Dth_sq_sin_rpow {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) q.1 (|q.2|)) ^ 2
        * (Real.sin (2 * |q.2|)) ^ (- (Work.Spaces.gam (Work.FTS.Regularity.pExp α))))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  set p := Work.FTS.Regularity.pExp α with hp
  set f₀ := Work.FTS.Regularity.gSlice g τ with hf₀
  set F : ℝ × ℝ → ℝ := fun q =>
    (Work.Spaces.Dth f₀ q.1 (|q.2|)) ^ 2 * (Real.sin (2 * |q.2|)) ^ (-(Work.Spaces.gam p))
    with hF
  have hpos : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth f₀ q.1 q.2) ^ 2 * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam p)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := integrableOn_positive h hτ
  have h1 : MeasureTheory.IntegrableOn F (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hpos.congr_fun (fun q hq => by simp only [hF]; rw [abs_of_pos hq.2.1])
      (measurableSet_Ioi.prod measurableSet_Ioo)
  have hneg : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Work.Spaces.Dth f₀ q.1 (-q.2)) ^ 2 * (Real.sin (2 * (-q.2))) ^ (-(Work.Spaces.gam p)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0) := integrableOn_neg_snd_reflect hpos
  have h2 : MeasureTheory.IntegrableOn F (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0) :=
    hneg.congr_fun (fun q hq => by simp only [hF]; rw [abs_of_neg hq.2.2])
      (measurableSet_Ioi.prod measurableSet_Ioo)
  have hunion : MeasureTheory.IntegrableOn F
      ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
        ∪ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)) := h1.union h2
  have hsub : ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
        \ ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
          ∪ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)))
      ⊆ Set.univ ×ˢ ({0} : Set ℝ) := by
    intro q hq
    rw [Set.mem_sdiff] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq1
    refine ⟨trivial, ?_⟩
    simp only [Set.mem_singleton_iff]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hq2 (Or.inr (by
        rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
        exact ⟨hq1.1, hq1.2.1, hlt⟩))
    · exact hq2 (Or.inl (by
        rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
        exact ⟨hq1.1, hgt, hq1.2.2⟩))
  have hz : (volume : Measure (ℝ × ℝ)) (Set.univ ×ˢ ({0} : Set ℝ)) = 0 := by
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod,
      MeasureTheory.measure_singleton, mul_zero]
  have hsub2 : ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
        ∪ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0))
      ⊆ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) : Set (ℝ × ℝ)) := by
    intro q hq
    rw [Set.mem_union, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_prod, Set.mem_Ioi,
      Set.mem_Ioo] at hq
    rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    rcases hq with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨h1, by linarith, by linarith⟩
    · exact ⟨h1, by linarith, by linarith⟩
  have hae : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) : Set (ℝ × ℝ))
      =ᵐ[volume]
        ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
          ∪ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) 0)) := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨measure_mono_null hsub hz,
      by rw [Set.sdiff_eq_empty.mpr hsub2, measure_empty]⟩
  have hgoal : MeasureTheory.IntegrableOn F
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    rw [IntegrableOn, Measure.restrict_congr_set hae]
    exact hunion
  exact hgoal

end Work.FTS.FireFix.Clauses.PsiWt
end
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_cos_sq_sin_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of `cos²θ · sin(2|θ|)^{γ-2}` against a radial indicator

This module proves `Work.FTS.FireFix.Clauses.PsiWt.integrableOn_cos_sq_sin_rpow`:
for `1 < γ ≤ 2` and `L ≥ 0` the function

  `(q : ℝ × ℝ) ↦ cos(q.2)² · sin(2|q.2|)^{γ-2} · 1_{q.1 ≤ L}`

is integrable on the half-strip `(0,∞) × (-π/2, π/2)`.

The function is a product of a one-variable `θ`-factor and the half-line indicator
`1_{(-∞,L]}`; the latter is integrable on `(0,∞)` because `(0,∞) ∩ (-∞,L] = (0,L]` has
finite Lebesgue measure.  The `θ`-factor has only the endpoint singularities of
`sin(2θ)^{γ-2}` at `0` and `±π/2`, both integrable since `-1 < γ - 2`; on the right half
we dominate it by `2^{γ-2} sin^{γ-2}θ` using the identity
`sin(2θ) = 2 sinθ cosθ` together with `cos^γ θ ≤ 1`, then dominate `sin^{γ-2}θ` by a
constant times `θ^{γ-2}` (`sin x ≥ (2/π)x`), and transfer to the left half by evenness.
-/

set_option linter.unusedVariables false

namespace Work.FTS.FireFix.Clauses.PsiWt

open MeasureTheory Set

/-! ### Two elementary integrability facts -/

/-- The indicator of a halfline `(-∞, L]` is integrable on `(0, ∞)`: it is the indicator
of `(0, L]`, a set of finite Lebesgue measure. -/
lemma integrableOn_ite_le_Ioi (L : ℝ) :
    IntegrableOn (fun x : ℝ => if x ≤ L then (1 : ℝ) else 0) (Ioi (0 : ℝ)) := by
  have hEq : (fun x : ℝ => if x ≤ L then (1 : ℝ) else 0)
      = (Iic L).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ≤ L <;> simp [hx]
  rw [hEq, integrableOn_indicator_iff measurableSet_Iic, Iic_inter_Ioi]
  refine integrableOn_const (C := (1 : ℝ)) ?_
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

/-- `sin^r` is integrable on `(0, π/2)` when `-1 < r ≤ 0`: dominated by
`(2/π)^r θ^r` via `sin x ≥ (2/π) x`. -/
lemma integrableOn_sin_rpow_Ioo {r : ℝ} (hr : -1 < r) (hr0 : r ≤ 0) :
    IntegrableOn (fun θ : ℝ => Real.sin θ ^ r) (Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hdom : IntegrableOn (fun θ : ℝ => (2 / Real.pi) ^ r * θ ^ r)
      (Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := r) (t := Real.pi / 2) hpi2).2 hr).const_mul _
  rw [IntegrableOn] at hdom ⊢
  refine hdom.mono' ?_ ?_
  · refine (ContinuousOn.rpow_const Real.continuous_sin.continuousOn ?_).aestronglyMeasurable
      measurableSet_Ioo
    intro x hx
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1
      (by linarith [hx.2, Real.pi_pos])))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hsin_nonneg : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
    have hbase : (0 : ℝ) < 2 / Real.pi * x :=
      mul_pos (by positivity) hx.1
    have hle : 2 / Real.pi * x ≤ Real.sin x := Real.mul_le_sin hx.1.le hx.2.le
    have h1 : Real.sin x ^ r ≤ (2 / Real.pi * x) ^ r :=
      Real.rpow_le_rpow_of_nonpos hbase hle hr0
    have h2 : (2 / Real.pi * x) ^ r = (2 / Real.pi) ^ r * x ^ r :=
      Real.mul_rpow (by positivity) hx.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hsin_nonneg _)]
    exact h1.trans (le_of_eq h2)

/-! ### The `θ`-integrand on the right half `(0, π/2)` -/

/-- The bound `cos²θ · sin(2θ)^{γ-2} ≤ 2^{γ-2} sin^{γ-2}θ` for `θ ∈ (0, π/2)`, from
`sin(2θ) = 2 sinθ cosθ` and `cos^γ θ ≤ 1`. -/
lemma cos_sq_mul_sin_two_rpow_le {γ θ : ℝ} (hγ : 1 < γ)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.cos θ ^ 2 * Real.sin (2 * θ) ^ (γ - 2) ≤ (2 : ℝ) ^ (γ - 2) * Real.sin θ ^ (γ - 2) := by
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hgam0 : 0 ≤ γ := by linarith
  -- the `sin(2θ)^{γ-2}` factor, split into powers of `sin θ` and `cos θ`
  have e1 : Real.sin (2 * θ) ^ (γ - 2)
      = (2 : ℝ) ^ (γ - 2) * (Real.sin θ ^ (γ - 2) * Real.cos θ ^ (γ - 2)) := by
    rw [Real.sin_two_mul,
      Real.mul_rpow (by linarith [hsin_pos] : (0 : ℝ) ≤ 2 * Real.sin θ) hcos_pos.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hsin_pos.le]
    ring
  -- `cos²θ · cos^{γ-2}θ = cos^γ θ`
  have hC : Real.cos θ ^ 2 * Real.cos θ ^ (γ - 2) = Real.cos θ ^ γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hcos_pos]
    rw [show (((2 : ℕ) : ℝ) + (γ - 2)) = γ by push_cast; ring]
  have key : Real.cos θ ^ 2 * Real.sin (2 * θ) ^ (γ - 2)
      = (2 : ℝ) ^ (γ - 2) * (Real.sin θ ^ (γ - 2) * Real.cos θ ^ γ) := by
    rw [e1]
    calc Real.cos θ ^ 2 * ((2 : ℝ) ^ (γ - 2) * (Real.sin θ ^ (γ - 2) * Real.cos θ ^ (γ - 2)))
        = (2 : ℝ) ^ (γ - 2)
            * (Real.sin θ ^ (γ - 2) * (Real.cos θ ^ 2 * Real.cos θ ^ (γ - 2))) := by ring
      _ = (2 : ℝ) ^ (γ - 2) * (Real.sin θ ^ (γ - 2) * Real.cos θ ^ γ) := by rw [hC]
  rw [key]
  have hcos : Real.cos θ ^ γ ≤ 1 :=
    Real.rpow_le_one hcos_pos.le (Real.cos_le_one θ) hgam0
  have h1 : Real.sin θ ^ (γ - 2) * Real.cos θ ^ γ ≤ Real.sin θ ^ (γ - 2) := by
    simpa using mul_le_mul_of_nonneg_left hcos (Real.rpow_nonneg hsin_pos.le _)
  exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) _)

/-- **The `θ`-integrand is integrable on the right half.**  Domination by
`2^{γ-2} sin^{γ-2}θ` (whose exponent lies in `(-1, 0]` when `γ ≤ 2`). -/
lemma integrableOn_cos_sq_sin_two_rpow_Ioo {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) :
    IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * θ) ^ (γ - 2))
      (Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hdom : IntegrableOn (fun θ : ℝ => (2 : ℝ) ^ (γ - 2) * Real.sin θ ^ (γ - 2))
      (Ioo (0 : ℝ) (Real.pi / 2)) :=
    (integrableOn_sin_rpow_Ioo (r := γ - 2) (by linarith) (by linarith)).const_mul _
  rw [IntegrableOn] at hdom ⊢
  refine hdom.mono' ?_ ?_
  · refine ((Real.continuous_cos.continuousOn.pow 2).mul ?_).aestronglyMeasurable measurableSet_Ioo
    refine ContinuousOn.rpow_const
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn ?_
    intro x hx
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos])))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hsin_nonneg : 0 ≤ Real.sin (2 * x) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg hsin_nonneg _))]
    exact cos_sq_mul_sin_two_rpow_le hγ hx

/-! ### The even `θ`-integrand on the full interval -/

/-- `H θ = cos²θ · sin(2|θ|)^{γ-2}` is integrable on `(0, π/2)` (where `|θ| = θ`). -/
lemma integrableOn_cos_sq_sin_abs_pos {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) :
    IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      (Ioo (0 : ℝ) (Real.pi / 2)) :=
  (integrableOn_cos_sq_sin_two_rpow_Ioo hγ hγ2).congr_fun
    (fun x hx => by simp only [abs_of_pos hx.1]) measurableSet_Ioo

/-- `H θ = cos²θ · sin(2|θ|)^{γ-2}` is integrable on `(-π/2, 0)`: `H` is even, so this is
the substitution `θ ↦ -θ` of the previous lemma. -/
lemma integrableOn_cos_sq_sin_abs_neg {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) :
    IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      (Ioo (-(Real.pi / 2)) 0) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hI : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2)) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hpi2.le).2
      (integrableOn_cos_sq_sin_abs_pos hγ hγ2)
  have h2 := (IntervalIntegrable.iff_comp_neg
    (f := fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
    (a := 0) (b := Real.pi / 2)).1 hI
  have h3 : IntervalIntegrable
      (fun x : ℝ => Real.cos (-x) ^ 2 * Real.sin (2 * |-x|) ^ (γ - 2)) volume
      (-(Real.pi / 2)) 0 := by
    simpa using h2.symm
  have h4 : IntegrableOn (fun x : ℝ => Real.cos (-x) ^ 2 * Real.sin (2 * |-x|) ^ (γ - 2))
      (Ioo (-(Real.pi / 2)) 0) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (show -(Real.pi / 2) ≤ (0 : ℝ) by
      linarith [Real.pi_pos])).1 h3
  exact h4.congr_fun (fun x _ => by simp only [Real.cos_neg, abs_neg]) measurableSet_Ioo

/-- `H θ = cos²θ · sin(2|θ|)^{γ-2}` is integrable on the full interval `(-π/2, π/2)`. -/
lemma integrableOn_cos_sq_sin_abs_Ioo {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) :
    IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hsplit : Ioo (-(Real.pi / 2)) 0 ∪ {0} ∪ Ioo (0 : ℝ) (Real.pi / 2)
      = Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    ext x
    simp only [mem_union, mem_Ioo, mem_singleton_iff]
    constructor
    · rintro ((⟨h1, h2⟩ | h3) | ⟨h4, h5⟩)
      · exact ⟨h1, by linarith [Real.pi_pos]⟩
      · exact ⟨by rw [h3]; linarith [Real.pi_pos], by rw [h3]; linarith [Real.pi_pos]⟩
      · exact ⟨by linarith [Real.pi_pos], h5⟩
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨h, h2⟩
  have h1 := integrableOn_cos_sq_sin_abs_neg hγ hγ2
  have h2 : IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      ({0} : Set ℝ) := IntegrableOn.of_measure_zero (by simp)
  have h3 := integrableOn_cos_sq_sin_abs_pos hγ hγ2
  rw [← hsplit]
  exact (h1.union h2).union h3

/-! ### The theorem -/

theorem integrableOn_cos_sq_sin_rpow {γ L : ℝ} (hγ : 1 < γ) (hγ2 : γ ≤ 2) (hL : 0 ≤ L) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Real.cos q.2) ^ 2 * (Real.sin (2 * |q.2|)) ^ (γ - 2)
        * (if q.1 ≤ L then (1 : ℝ) else 0))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hG : IntegrableOn (fun x : ℝ => if x ≤ L then (1 : ℝ) else 0) (Ioi (0 : ℝ)) :=
    integrableOn_ite_le_Ioi L
  have hH : IntegrableOn (fun θ : ℝ => Real.cos θ ^ 2 * Real.sin (2 * |θ|) ^ (γ - 2))
      (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := integrableOn_cos_sq_sin_abs_Ioo hγ hγ2
  have hprod : IntegrableOn (fun q : ℝ × ℝ =>
      (if q.1 ≤ L then (1 : ℝ) else 0) * (Real.cos q.2 ^ 2 * Real.sin (2 * |q.2|) ^ (γ - 2)))
      (Ioi (0 : ℝ) ×ˢ Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    have h := hG.mul_prod hH
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  refine hprod.congr_fun ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro q hq
  ring

end Work.FTS.FireFix.Clauses.PsiWt
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_indic_Iic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.PsiWt

/-- The indicator of the half-plane `{q | q.1 ≤ L}` is integrable on the strip
`(0,∞) × (-π/2, π/2)`: its support there is contained in the rectangle
`(0, L] × (-π/2, π/2)`, which has finite Lebesgue measure. -/
theorem integrableOn_indic_Iic {L : ℝ} (hL : 0 ≤ L) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ => (if q.1 ≤ L then (1 : ℝ) else 0))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  set s : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) with hs
  have hsmeas : MeasurableSet s := measurableSet_Ioi.prod measurableSet_Ioo
  -- `u` is the support of the integrand inside the strip `s`.
  set u : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.1 ≤ L} ∩ s with hu
  have humeas : MeasurableSet u := (measurableSet_Iic.preimage measurable_fst).inter hsmeas
  -- On `s`, the integrand agrees with the indicator of `u`.
  have hEq : Set.EqOn (fun q : ℝ × ℝ => (if q.1 ≤ L then (1 : ℝ) else 0))
      (u.indicator (fun _ => (1 : ℝ))) s := by
    intro q hq
    have hmem : (q ∈ u) ↔ q.1 ≤ L := by
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, hq⟩
    simp only [Set.indicator_apply]
    by_cases h : q.1 ≤ L
    · simp [h, hmem.mpr h]
    · simp [h, hmem]
  -- `u` is contained in a rectangle of finite measure.
  have hfin : MeasureTheory.volume u < ⊤ := by
    have hsub : u ⊆ Set.Ioc 0 L ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      rintro ⟨x, y⟩ ⟨hx, hxs⟩
      simp only [hs, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hxs
      exact ⟨⟨hxs.1, hx⟩, hxs.2⟩
    calc MeasureTheory.volume u
        ≤ MeasureTheory.volume (Set.Ioc 0 L ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
          MeasureTheory.measure_mono hsub
      _ = MeasureTheory.volume (Set.Ioc (0 : ℝ) L)
            * MeasureTheory.volume (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
          rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
      _ = ENNReal.ofReal (L - 0) * ENNReal.ofReal (Real.pi / 2 - -(Real.pi / 2)) := by
          rw [Real.volume_Ioc, Real.volume_Ioo]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- The indicator of `u` is integrable on `s`, since `volume (u ∩ s) < ∞`.
  have hint : MeasureTheory.IntegrableOn (u.indicator (fun _ => (1 : ℝ))) s := by
    rw [MeasureTheory.integrableOn_indicator_iff humeas]
    have hle : MeasureTheory.volume (u ∩ s) ≤ MeasureTheory.volume u :=
      MeasureTheory.measure_mono Set.inter_subset_left
    exact MeasureTheory.integrableOn_const (ne_top_of_lt (lt_of_le_of_lt hle hfin))
  exact (MeasureTheory.integrableOn_congr_fun hEq hsmeas).2 hint

end Work.FTS.FireFix.Clauses.PsiWt
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PsiWt.integrableOn_sin_rpow_mul_cos_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

set_option linter.unusedVariables false

namespace Work.FTS.FireFix.Clauses.PsiWt

/-!
# Integrability of the ψ-weight singularity

The angular factor of the ψ-weight of the physical reconstruction is
`θ ↦ (sin |θ|)^{α-1} (cos θ)^{2α}`; the exponent `α - 1 ∈ (-1, 0)` makes it
non-integrable at the origin of the `θ`-line, and the radial cutoff
`z ↦ if z ≤ L then 1 else 0` makes the `z`-integral finite.  This file proves the
resulting two-dimensional integrability on `(0, ∞) × (-π/2, π/2)`.

The mathematical content is elementary: near `θ = 0` the integrand is comparable
to `|θ|^{α - 1}` (since `sin |θ| ≥ (2/π)|θ|`), which is integrable because
`α > 0`, and the cosine factor is bounded; the cutoff factor is the indicator of
the bounded interval `(0, L]`.
-/

/-- The angular factor `θ ↦ (sin |θ|)^{α-1} (cos θ)^{2α}` is integrable on the symmetric
interval `(-π/2, π/2)`: at the origin it is dominated by `(2/π)^{α-1} |θ|^{α-1}`, which is
integrable since `α - 1 > -1`, and the cosine factor is bounded by `1`. -/
theorem integrableOn_sin_abs_rpow_mul_cos_rpow_angle {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 3) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => (Real.sin |y|) ^ (α - 1) * (Real.cos y) ^ (2 * α))
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  -- the positive half, where `|y| = y`
  have hθpos : IntegrableOn (fun y : ℝ => (Real.sin |y|) ^ (α - 1) * (Real.cos y) ^ (2 * α))
      (Set.Ioo 0 (Real.pi / 2)) volume := by
    have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
    have hrpow : IntegrableOn (fun y : ℝ => y ^ (α - 1)) (Set.Ioo 0 (Real.pi / 2)) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hpi).mpr (by linarith)
    have hM : IntegrableOn (fun y : ℝ => (2 / Real.pi) ^ (α - 1) * y ^ (α - 1))
        (Set.Ioo 0 (Real.pi / 2)) volume := Integrable.const_mul hrpow _
    refine Integrable.mono' hM ?_ ?_
    · exact (((Real.measurable_sin.comp measurable_abs).pow_const (α - 1)).mul
        (Real.measurable_cos.pow_const (2 * α))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : (0 : ℝ) < t := ht.1
      have htp : t < Real.pi / 2 := ht.2
      rw [abs_of_pos ht0]
      have hsin_pos : 0 < Real.sin t :=
        Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
      have h2pi : (0 : ℝ) < 2 / Real.pi := by positivity
      have hsin_ge : 2 / Real.pi * t ≤ Real.sin t := Real.mul_le_sin ht0.le htp.le
      have hrpow_le : (Real.sin t) ^ (α - 1) ≤ (2 / Real.pi * t) ^ (α - 1) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos h2pi ht0) hsin_ge (by linarith)
      rw [Real.mul_rpow h2pi.le ht0.le] at hrpow_le
      have hcos_pos : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htp⟩
      have hcos_le : (Real.cos t) ^ (2 * α) ≤ 1 :=
        Real.rpow_le_one hcos_pos.le (Real.cos_le_one t) (by linarith)
      have hsin_nn : 0 ≤ (Real.sin t) ^ (α - 1) := Real.rpow_nonneg hsin_pos.le _
      have hcos_nn : 0 ≤ (Real.cos t) ^ (2 * α) := Real.rpow_nonneg hcos_pos.le _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsin_nn hcos_nn)]
      calc (Real.sin t) ^ (α - 1) * (Real.cos t) ^ (2 * α)
          ≤ ((2 / Real.pi) ^ (α - 1) * t ^ (α - 1)) * 1 :=
            mul_le_mul hrpow_le hcos_le hcos_nn
              (le_of_lt (mul_pos (Real.rpow_pos_of_pos h2pi _) (Real.rpow_pos_of_pos ht0 _)))
        _ = (2 / Real.pi) ^ (α - 1) * t ^ (α - 1) := by ring
  set f : ℝ → ℝ := fun y => (Real.sin |y|) ^ (α - 1) * (Real.cos y) ^ (2 * α) with hf
  have hpos' : IntegrableOn f (Set.Ioo 0 (Real.pi / 2)) := hθpos
  -- the negative half, obtained from the positive one by the reflection `y ↦ -y`, using
  -- that `f` is even
  have hneg : IntegrableOn f (Set.Ioo (-(Real.pi / 2)) 0) := by
    have hset : Neg.neg '' Set.Ioo 0 (Real.pi / 2) = Set.Ioo (-(Real.pi / 2)) 0 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
      · intro hx
        exact ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by simp⟩
    have hiff := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_image
      (Homeomorph.neg ℝ).measurableEmbedding (f := f) (s := Set.Ioo 0 (Real.pi / 2))
    rw [show Set.Ioo (-(Real.pi / 2)) 0 = Neg.neg '' Set.Ioo 0 (Real.pi / 2) from hset.symm]
    refine hiff.mpr ?_
    exact IntegrableOn.congr_fun hpos'
      (fun y _ => by simp [f, Function.comp_apply]) measurableSet_Ioo
  -- the origin is a null set
  have hsingle : IntegrableOn f ({0} : Set ℝ) := IntegrableOn.of_measure_zero (by simp)
  have hun : IntegrableOn f (Set.Ioo (-(Real.pi / 2)) 0 ∪ ({0} ∪ Set.Ioo 0 (Real.pi / 2))) :=
    IntegrableOn.union hneg (IntegrableOn.union hsingle hpos')
  have hset2 : Set.Ioo (-(Real.pi / 2)) 0 ∪ ({0} ∪ Set.Ioo 0 (Real.pi / 2))
      = Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro (⟨h1, h2⟩ | rfl | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      · exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h, h2⟩)
  rwa [hset2] at hun

/-- The cutoff factor `x ↦ if x ≤ L then 1 else 0` is integrable on the half line `(0, ∞)`:
it is the indicator of the bounded interval `(0, L]`. -/
theorem integrable_cutoff_Ioi (L : ℝ) :
    Integrable (fun x : ℝ => if x ≤ L then (1 : ℝ) else 0) (volume.restrict (Set.Ioi 0)) := by
  have hIoc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 L) volume := by
    apply integrableOn_const
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  have hkey : Set.Ioc (0 : ℝ) L ∩ Set.Ioi 0 = Set.Ioc 0 L := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩; exact h1
    · intro h; exact ⟨h, h.1⟩
  have h2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 L) (volume.restrict (Set.Ioi 0)) := by
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc, hkey]
    exact hIoc
  have h3 : Integrable ((Set.Ioc 0 L).indicator (fun _ : ℝ => (1 : ℝ)))
      (volume.restrict (Set.Ioi 0)) := (integrable_indicator_iff measurableSet_Ioc).2 h2
  refine Integrable.congr h3 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (0 : ℝ) < x := Set.mem_Ioi.mp hx
  have hiff : (x ∈ Set.Ioc (0 : ℝ) L) ↔ x ≤ L :=
    ⟨fun h => h.2, fun h => ⟨hx', h⟩⟩
  simp only [Set.indicator_apply]
  by_cases h : x ≤ L
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h (hiff.mp hc)), ite_eq_right h]

theorem integrableOn_sin_rpow_mul_cos_rpow {α L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 3)
    (hL : 0 ≤ L) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Real.sin |q.2|) ^ (α - 1) * (Real.cos q.2) ^ (2 * α)
        * (if q.1 ≤ L then (1 : ℝ) else 0))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hθ := integrableOn_sin_abs_rpow_mul_cos_rpow_angle hα hα1
  have hz := integrable_cutoff_Ioi L
  -- the product measure on the rectangle is the product of the restricted measures
  change Integrable _ ((Measure.prod volume volume).restrict
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
  rw [← Measure.prod_restrict]
  refine Integrable.congr (Integrable.mul_prod hz hθ) ?_
  filter_upwards with q
  exact mul_comm _ _

end Work.FTS.FireFix.Clauses.PsiWt
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.eTheta_deriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses

/-!
# The derivative bound for the angular frame vector `e_θ`

`e_θ = (1/r) • angularVec` with `r = radial x = √(x₀² + x₁²)` and `angularVec x = (-x₁, x₀, 0)`.
Off the axis (`0 < radial x`) the product rule gives the Fréchet derivative
(`Work.CoreResiduals.VorticityEquation.fderiv_eTheta`)

`fderiv ℝ e_θ x v = (-(x₀v₀ + x₁v₁)/r³) • angularVec x + (1/r) • angularVec v`,

so, since `‖angularVec y‖ = radial y ≤ ‖y‖` (`Work.Cyl.norm_angularVec`,
`Work.Cyl.radial_le_rho` + `Work.Cyl.rho_eq_norm`) and
`|x₀v₀ + x₁v₁| = |⟪angularVec x, angularVec v⟫| ≤ r · radial v`
(`Work.Cyl.inner_angularVec`, `Work.Cyl.abs_inner_angularVec_le`),

`‖fderiv ℝ e_θ x v‖ ≤ (radial v / r) + (radial v / r) ≤ 2‖v‖/r`.

The constant `2` is the one the paper's weighted Lipschitz bound
(`Work.Cyl.eTheta_sub_norm_mul_le`) uses; it is sharp in the sense that the two summands each
contribute `‖v‖/r` with the same weight.

The statement (and its name) is unchanged from the request.
-/

theorem eTheta_deriv_bound (x : EuclideanSpace ℝ (Fin 3)) (hr : 0 < Work.Cyl.radial x) :
    DifferentiableAt ℝ Work.Cyl.eTheta x ∧
      ‖fderiv ℝ Work.Cyl.eTheta x‖ ≤ 2 / Work.Cyl.radial x := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  -- `radial v ≤ ‖v‖`, so the `angularVec`-factor is dominated by the norm
  have hrv_le : ∀ v : Work.Cyl.R3, Work.Cyl.radial v ≤ ‖v‖ := fun v => by
    rw [← Work.Cyl.rho_eq_norm]
    exact Work.Cyl.radial_le_rho v
  -- `angularVec` is differentiable: it is the linear map `y ↦ (-y₁) • e₀ + y₀ • e₁`
  have hAng : DifferentiableAt ℝ (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) x := by
    have h : (fun y : Work.Cyl.R3 => Work.Cyl.angularVec y) =
        fun y : Work.Cyl.R3 => (-y 1) • Work.Cyl.e0 + (y 0) • Work.Cyl.e1 := by
      funext y
      apply Work.Cyl.ext_coord <;>
        simp [Work.Cyl.angularVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]
    rw [h]; fun_prop
  -- `e_θ = r⁻¹ • angularVec`
  have hE : Work.Cyl.eTheta =
      (fun y : Work.Cyl.R3 => (Work.Cyl.radial y)⁻¹) • Work.Cyl.angularVec := by
    funext y
    show (1 / Work.Cyl.radial y) • Work.Cyl.angularVec y
      = (Work.Cyl.radial y)⁻¹ • Work.Cyl.angularVec y
    rw [one_div]
  refine ⟨?_, ?_⟩
  · rw [hE]
    exact ((Work.Cyl.differentiableAt_radial x hrne).inv hrne).smul hAng
  · rw [ContinuousLinearMap.opNorm_le_iff (by positivity : (0 : ℝ) ≤ 2 / Work.Cyl.radial x)]
    intro v
    rw [Work.CoreResiduals.VorticityEquation.fderiv_eTheta x v hr]
    -- `|x₀v₀ + x₁v₁| ≤ r · radial v`
    have hb : |x 0 * v 0 + x 1 * v 1| ≤ Work.Cyl.radial x * Work.Cyl.radial v := by
      rw [← Work.Cyl.inner_angularVec x v]
      exact Work.Cyl.abs_inner_angularVec_le x v
    -- the derivative of the radial weight: `≤ radial v / r`
    have hφ1 : ‖(-(x 0 * v 0 + x 1 * v 1) / (Work.Cyl.radial x) ^ 3) • Work.Cyl.angularVec x‖
        ≤ Work.Cyl.radial v / Work.Cyl.radial x := by
      rw [norm_smul, Real.norm_eq_abs, Work.Cyl.norm_angularVec, abs_div, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < Work.Cyl.radial x ^ 3)]
      have key : |x 0 * v 0 + x 1 * v 1| / Work.Cyl.radial x ^ 3 * Work.Cyl.radial x
          = |x 0 * v 0 + x 1 * v 1| / Work.Cyl.radial x ^ 2 := by
        field_simp
      rw [key]
      have h := div_le_div_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ (Work.Cyl.radial x) ^ 2)
      have h2 : (Work.Cyl.radial x * Work.Cyl.radial v) / Work.Cyl.radial x ^ 2
          = Work.Cyl.radial v / Work.Cyl.radial x := by
        field_simp
      rwa [h2] at h
    -- the derivative of the linear factor: `≤ ‖v‖ / r`
    have hφ2 : ‖(Work.Cyl.radial x)⁻¹ • Work.Cyl.angularVec v‖ ≤ ‖v‖ / Work.Cyl.radial x := by
      rw [norm_smul, Real.norm_eq_abs, Work.Cyl.norm_angularVec,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Work.Cyl.radial x)⁻¹)]
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hrv_le v)
        (by positivity : (0 : ℝ) ≤ (Work.Cyl.radial x)⁻¹)
    calc ‖(-(x 0 * v 0 + x 1 * v 1) / (Work.Cyl.radial x) ^ 3) • Work.Cyl.angularVec x
            + (Work.Cyl.radial x)⁻¹ • Work.Cyl.angularVec v‖
        ≤ ‖(-(x 0 * v 0 + x 1 * v 1) / (Work.Cyl.radial x) ^ 3) • Work.Cyl.angularVec x‖
            + ‖(Work.Cyl.radial x)⁻¹ • Work.Cyl.angularVec v‖ := norm_add_le _ _
      _ ≤ Work.Cyl.radial v / Work.Cyl.radial x + ‖v‖ / Work.Cyl.radial x := add_le_add hφ1 hφ2
      _ ≤ ‖v‖ / Work.Cyl.radial x + ‖v‖ / Work.Cyl.radial x :=
          add_le_add (div_le_div_of_nonneg_right (hrv_le v) (le_of_lt hr)) le_rfl
      _ = 2 / Work.Cyl.radial x * ‖v‖ := by ring

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.fderiv_rho_theta_eTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular derivative of `x ↦ F(ρ(x), θ(x))`: the `e_θ` direction

For a two-variable function `F` and a point `x` off the symmetry axis (`0 < radial x`),

`fderiv ℝ (fun y ↦ F (rho y) (theta y)) x (eTheta x) = 0`.

Geometrically: `e_θ` is the unit vector of the rotation about the `x₃`-axis, so to first order
moving along `e_θ` changes neither the distance `r` to the axis nor the axial coordinate `x₃`.
Since `ρ = √(r² + x₃²)` and `θ = arctan(x₃/r)` are functions of `(r, x₃)` alone, both are
stationary in the `e_θ` direction; the derivative of any function of `(ρ, θ)` therefore
vanishes there.

Formally, the argument is the same as in the sibling `Work.Cyl.fderiv_rho_theta_eR` and
`Work.Cyl.fderiv_rho_theta_eZ`: rewrite `F (rho ·) (theta ·)` on the line `t ↦ x + t • eTheta x`
as the composite `H (radial ·) (axial ·)` with `H r' z' = F (rhoP r' z') (thetaP r' z')`,
observe that along this particular line `radial` has velocity `0` at `t = 0`
(`radial (x + t • eTheta x) = √(radial x ^ 2 + t ^ 2)`) and `axial` is constant, and apply the
two-variable chain rule.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix

namespace Work.FTS.FireFix.Clauses

open Work.Cyl

/-! ## The dictionary between `(rho, theta)` on `ℝ³` and `(rhoP, thetaP)` on the half plane -/

private lemma rho_eq_rhoP' (y : R3) : rho y = rhoP (radial y) (axial y) := by
  rw [rho, rhoP, radial_sq]

private lemma theta_eq_thetaP' (y : R3) : theta y = thetaP (radial y) (axial y) := rfl

/-- If `F` is differentiable as a function of two variables at `(ρ(r,z), θ(r,z))` and `0 < r`,
then so is the composite `(r',z') ↦ F (ρ(r',z')) (θ(r',z'))`: the pair `(ρ, θ)` is differentiable
there (`ρ` is a square root of a strictly positive quantity, `θ` is `arctan` of the
differentiable quotient `z'/r'`, legitimate since `r' = r ≠ 0`).  This is the same
differentiability input as in `Work.Cyl.pdR_comp_polar_rho`. -/
private lemma polar_comp_diffAt2 (F : ℝ → ℝ → ℝ) (r z : ℝ) (hr : 0 < r)
    (hF : DiffAt2 F (rhoP r z) (thetaP r z)) :
    DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z')) r z := by
  have hρ : DifferentiableAt ℝ (fun p : ℝ × ℝ => rhoP p.1 p.2) (r, z) := by
    have h : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (r, z) := by fun_prop
    have hne : (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (r, z) ≠ 0 := by
      simp only; positivity
    simpa [rhoP] using h.sqrt hne
  have hθ : DifferentiableAt ℝ (fun p : ℝ × ℝ => thetaP p.1 p.2) (r, z) := by
    have hinv : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.1)⁻¹) (r, z) :=
      differentiableAt_fst.inv (by simpa using hr.ne')
    have h : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.2 * (p.1)⁻¹) (r, z) :=
      differentiableAt_snd.mul hinv
    simpa [thetaP, div_eq_mul_inv] using h.arctan
  have hΦ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (rhoP p.1 p.2, thetaP p.1 p.2)) (r, z) :=
    hρ.prodMk hθ
  exact hF.comp (r, z) hΦ

/-! ## The line `t ↦ x + t • e_θ` and the polar coordinates on it -/

/-- Along the line in direction `e_θ` the distance to the axis moves as `t ↦ √(r² + t²)`: the
`e_θ` field is the infinitesimal generator of the rotation about the axis, which preserves `r`
to first order, so the quadratic `radSq` picks up a `t²` term. -/
private lemma radSq_add_smul_eTheta (x : R3) (hr : radial x ≠ 0) (t : ℝ) :
    radSq (x + t • eTheta x) = radial x ^ 2 + t ^ 2 := by
  have hs : radial x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by rw [radial_sq]; rfl
  have h0 : (x + t • eTheta x) 0 = x 0 - t * x 1 / radial x := by
    simp [div_eq_mul_inv]; ring
  have h1 : (x + t • eTheta x) 1 = x 1 + t * x 0 / radial x := by
    simp [div_eq_mul_inv]; ring
  change (x + t • eTheta x) 0 ^ 2 + (x + t • eTheta x) 1 ^ 2 = radial x ^ 2 + t ^ 2
  rw [h0, h1]
  field_simp
  nlinarith [hs]

/-- `ρ` is constant to first order along the `e_θ` line: `radial (x + t • eTheta x) =
√(radial x ^ 2 + t ^ 2)`. -/
private lemma radial_add_smul_eTheta (x : R3) (hr : radial x ≠ 0) (t : ℝ) :
    radial (x + t • eTheta x) = Real.sqrt (radial x ^ 2 + t ^ 2) := by
  rw [radial, radSq_add_smul_eTheta x hr t]

/-- The axial coordinate is exactly constant along the `e_θ` line (`e_θ` has no `x₃` component). -/
private lemma axial_add_smul_eTheta (x : R3) (t : ℝ) : axial (x + t • eTheta x) = axial x := by
  simp [axial]

/-- The derivative of the distance to the axis along the `e_θ` line vanishes at `t = 0`. -/
private lemma hasDerivAt_radial_line_eTheta (x : R3) (hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => radial (x + t • eTheta x)) 0 0 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  rw [show (fun t : ℝ => radial (x + t • eTheta x)) =
      fun t : ℝ => Real.sqrt (radial x ^ 2 + t ^ 2) from
    funext fun t => radial_add_smul_eTheta x hrne t]
  have hinner : HasDerivAt (fun t : ℝ => radial x ^ 2 + t ^ 2) 0 0 := by
    have h : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by simpa using hasDerivAt_pow 2 (0 : ℝ)
    simpa using h.const_add (radial x ^ 2)
  have hne : radial x ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by simpa using pow_ne_zero 2 hrne
  simpa using hinner.sqrt hne

/-- The derivative of the axial coordinate along the `e_θ` line vanishes at `t = 0`. -/
private lemma hasDerivAt_axial_line_eTheta (x : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • eTheta x)) 0 0 := by
  have h : (fun t : ℝ => axial (x + t • eTheta x)) = fun _ => axial x := by
    funext t; rw [axial_add_smul_eTheta]
  rw [h]
  exact hasDerivAt_const (0 : ℝ) (axial x)

/-! ## The main computation -/

theorem fderiv_rho_theta_eTheta (F : ℝ → ℝ → ℝ) (x : EuclideanSpace ℝ (Fin 3))
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rho x) (Work.Cyl.theta x)) (hr : 0 < Work.Cyl.radial x) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => F (Work.Cyl.rho y) (Work.Cyl.theta y)) x
      (Work.Cyl.eTheta x) = 0 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  -- `F` is differentiable at the polar coordinates of `x`
  have hF' : DiffAt2 F (rhoP (radial x) (axial x)) (thetaP (radial x) (axial x)) := by
    rw [← rho_eq_rhoP' x, ← theta_eq_thetaP' x]; exact hF
  have hH : DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z')) (radial x) (axial x) :=
    polar_comp_diffAt2 F (radial x) (axial x) hr hF'
  -- the polar coordinates of the shifted point move with velocity `(0, 0)`
  have hline : HasDerivAt (fun t : ℝ => (fun r' z' => F (rhoP r' z') (thetaP r' z'))
      (radial (x + t • eTheta x)) (axial (x + t • eTheta x))) 0 0 := by
    have hH0 : DiffAt2 (fun r' z' => F (rhoP r' z') (thetaP r' z'))
        (radial (x + (0 : ℝ) • eTheta x)) (axial (x + (0 : ℝ) • eTheta x)) := by
      simpa using hH
    have h := hasDerivAt_comp_two (fun r' z' => F (rhoP r' z') (thetaP r' z'))
      (fun t : ℝ => radial (x + t • eTheta x)) (fun t : ℝ => axial (x + t • eTheta x))
      0 0 0 hH0 (hasDerivAt_radial_line_eTheta x hr) (hasDerivAt_axial_line_eTheta x)
    simpa using h
  -- rewrite the `fderiv` as a one-dimensional derivative along the `e_θ` line
  rw [fderiv_apply_eq_deriv_line _ _ _ (differentiableAt_rho_theta_comp F x hF hr)]
  have hfun : (fun t : ℝ => F (rho (x + t • eTheta x)) (theta (x + t • eTheta x))) =
      fun t : ℝ => (fun r' z' => F (rhoP r' z') (thetaP r' z'))
        (radial (x + t • eTheta x)) (axial (x + t • eTheta x)) := by
    funext t
    rw [rho_eq_rhoP' (x + t • eTheta x), theta_eq_thetaP' (x + t • eTheta x)]
  rw [hfun, hline.deriv]

end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.opNorm_le_frame =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses


end Work.FTS.FireFix.Clauses
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `psiField ψ` is `C²` off the axis when `ψ` is `C³`

The stream-function velocity field `Work.Cyl.psiField ψ` is built from the polar data
`(ρ, x₃) ↦ (ψ, ∂_rψ, ∂_zψ)` of the two-variable stream function.  This module proves that the
composition stays as smooth as the data allows off the axis: if `ψ` is `C³` at
`(radial x, axial x)` and `radial x > 0`, then `psiField ψ` is `C²` at `x`.

The two ingredients are

* `contDiffAt_radial` — `x ↦ radial x = √(x₀² + x₁²)` is `C²` at `x` when `radial x > 0`
  (a neighbourhood of `x` lies in `radSq > 0`, where `√` is smooth);
* `contDiffAt_pdZ_uncurry`, `contDiffAt_pdR_uncurry` — the partial derivatives
  `(r,z) ↦ pdZ ψ r z`, `(r,z) ↦ pdR ψ r z` are `C²` at `(r,z)` as soon as `ψ` is `C³` there.
  Indeed both are the first derivative `fderiv ℝ (uncurry ψ)` evaluated in a fixed direction
  `(0,1)` resp. `(1,0)` (`Work.Cyl.fderiv_prod_apply_snd`, `Work.Cyl.fderiv_prod_apply_fst`), and
  `fderiv` of a `C³` function is `C²`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.FTS.FireFix.Clauses

/-- The axial partial derivative `(r,z) ↦ ∂_zψ(r,z)` of a `C³` stream function is `C²`. -/
theorem contDiffAt_pdZ_uncurry {ψ : ℝ → ℝ → ℝ} {r z : ℝ}
    (hψ : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.Cyl.pdZ ψ p.1 p.2) (r, z) := by
  -- `ψ` is differentiable on a neighbourhood of `(r,z)`
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  -- `fderiv ℝ ψ` is `C²` at `(r,z)`
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 2) (by norm_num)
  -- evaluating it in the fixed direction `(0,1)` preserves smoothness
  have hΦ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (0, 1)) (r, z) :=
    hfd.clm_apply contDiffAt_const
  -- and on a neighbourhood it agrees with `∂_zψ`
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (Work.Cyl.fderiv_prod_apply_snd ψ p.1 p.2 hp).symm

/-- The radial partial derivative `(r,z) ↦ ∂_rψ(r,z)` of a `C³` stream function is `C²`. -/
theorem contDiffAt_pdR_uncurry {ψ : ℝ → ℝ → ℝ} {r z : ℝ}
    (hψ : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2) (r, z) := by
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 2) (by norm_num)
  have hΦ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (1, 0)) (r, z) :=
    hfd.clm_apply contDiffAt_const
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (Work.Cyl.fderiv_prod_apply_fst ψ p.1 p.2 hp).symm

/-- `x ↦ radial x = √(x₀² + x₁²)` is `C²` at `x` provided `radial x > 0`. -/
theorem contDiffAt_radial_two {x : EuclideanSpace ℝ (Fin 3)}
    (hx : 0 < Work.Cyl.radial x) :
    ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.radial y) x := by
  have hsq : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.radSq y) x := by
    show ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => y 0 ^ 2 + y 1 ^ 2) x
    fun_prop
  have hpos : 0 < Work.Cyl.radSq x := Real.sqrt_pos.mp hx
  exact (Real.contDiffAt_sqrt (ne_of_gt hpos)).comp x hsq

theorem psiField_contDiffAt_two {ψ : ℝ → ℝ → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hx : 0 < Work.Cyl.radial x)
    (hψ : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => ψ p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x)) :
    ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.psiField ψ y) x := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hx
  -- the polar data are `C²` at `x`
  have hrad := contDiffAt_radial_two hx
  have hax : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.axial y) x := by
    show ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => y 2) x
    fun_prop
  have hP : ContDiffAt ℝ 2
      (fun y : EuclideanSpace ℝ (Fin 3) => (Work.Cyl.radial y, Work.Cyl.axial y)) x :=
    hrad.prodMk hax
  -- the profile data are `C²` at `(radial x, axial x)`
  have hpdZ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.Cyl.pdZ ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := contDiffAt_pdZ_uncurry hψ
  have hpdR : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := contDiffAt_pdR_uncurry hψ
  have hψ2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := hψ.of_le (by norm_num)
  have hpdZc : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hpdZ.comp x hP using 1
    ext y; rfl
  have hpdRc : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hpdR.comp x hP using 1
    ext y; rfl
  have hψc : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hψ2.comp x hP using 1
    ext y; rfl
  -- the two components of `cylField`, as functions of `x`
  have hA : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y) x :=
    hpdZc.div hrad hrne
  have hB : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      -(ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
        - Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x :=
    (hψc.div hrad hrne).neg.sub hpdRc
  have hrv : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.radialVec y) x := by
    rw [show Work.Cyl.radialVec = fun y : EuclideanSpace ℝ (Fin 3) =>
        (y 0) • Work.Cyl.e0 + (y 1) • Work.Cyl.e1 from by
      funext y; ext i; fin_cases i <;>
        simp [Work.Cyl.radialVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]]
    fun_prop
  have hmain : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      (Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
          • Work.Cyl.radialVec y
        + (-(ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
            - Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) • Work.Cyl.eZ) x :=
    (hA.smul hrv).add (hB.smul (contDiffAt_const (c := Work.Cyl.eZ)))
  refine hmain.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  simp only [Work.Cyl.psiField, Work.Cyl.cylField]

end Work.FTS.FireFix.Clauses
end
