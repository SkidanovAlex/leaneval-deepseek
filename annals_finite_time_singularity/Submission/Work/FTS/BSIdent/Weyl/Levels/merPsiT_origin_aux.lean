import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.FTS.BSIdent.Curl
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev11
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev5
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev7
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
-- ===== merged: Submission.Work.FTS.BSIdent.Curl.bslOp_eq_of_vorticity_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.BSIdent.Curl



end Work.FTS.BSIdent.Curl
end
-- ===== merged: Submission.Work.FTS.BSIdent.Ident =====
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

/-! ## Parity of the meridian stream function -/



variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Fam} {C : Physical.PhysClock} {g : ℝ → ℝ → ℝ → ℝ} {t : ℝ}

/-- **The vorticity of the ansatz field is the re-signed physical vorticity**, on `Uax`, under the
hypotheses of `vorticity_psiField_merPsi`. -/
theorem vorticity_psiField_merPsi_apply (hA : 0 < A (Physical.clockInv C t))
    (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    {x : R3} (hx : x ∈ Uax) :
    vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) x
      = -(Physical.physOmega α A B g C x t) := by
  have h := vorticity_psiField_merPsi (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (g := g)
    (t := t) hA hB hlaw hsm (x := x) hx
  rw [h]
  exact vorticity_psiField_merPsi_eq_neg_physOmega α A B C g t

/-- The a.e. equality of the vorticity of the ansatz field with `−physOmega`, as an `EventuallyEq`
over Lebesgue measure on `ℝ³`. -/
theorem vorticity_psiField_merPsi_ae (hA : 0 < A (Physical.clockInv C t))
    (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ)) :
    (fun x : R3 => vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure R3)]
      (fun x : R3 => -(Physical.physOmega α A B g C x t)) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine measure_mono_null (fun x hx => ?_) volume_Uax_compl
  simp only [Set.mem_setOf_eq] at hx
  intro hxu
  exact hx (vorticity_psiField_merPsi_apply hA hB hlaw hsm hxu)

/-- The vorticity of the ansatz field is integrable as soon as the reconstructed vorticity slice
is: the two agree off the null set `Uaxᶜ`. -/
theorem integrable_vorticity_psiField_merPsi (hA : 0 < A (Physical.clockInv C t))
    (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hint : Integrable (fun x : R3 => -(Physical.physOmega α A B g C x t))) :
    Integrable (fun x : R3 =>
      vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) x) :=
  hint.congr (vorticity_psiField_merPsi_ae hA hB hlaw hsm).symm

/-! ## The identification -/

/-- **THE IDENTIFICATION (audit §5 item 4), from the inverse Biot–Savart law.**  On `Uax` the
reconstructed physical velocity is the stream-function field of the fake-time solution:

  `physVel (−physOmega α A B g C) x t = psiField (merPsi α A B Φ C · · t) x`.

The hypotheses are the clock and elliptic data (`hA`, `hB`, `hlaw`, `hsm`), the inverse Biot–Savart
law `hInv`, the integrability of the reconstructed vorticity slice (`hint`) and the geometric
bundle of the ansatz field: `C¹` (`hC1`), decay `1/‖x‖` (`hdec`) and the off-axis slice smoothness
of the meridian stream function (`hsm2`, used only for the divergence-freeness of the field). -/
theorem hid_of_biotSavartInverse (hInv : Work.LWP.BiotSavartInverse)
    (hA : 0 < A (Physical.clockInv C t)) (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hsm2 : ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => merPsi α A B Φ C p.1 p.2 t) (r, z))
    (hC1 : ContDiff ℝ 1 (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)))
    (hdec : ∃ D : ℝ, ∀ x : R3,
      ‖Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x‖ ≤ D / (1 + ‖x‖))
    (hint : Integrable (fun x : R3 => -(Physical.physOmega α A B g C x t))) :
    ∀ x ∈ Uax, Physical.physVel (-(Physical.physOmega α A B g C)) x t
      = Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x := by
  intro x hx
  -- the field is divergence-free and its vorticity is integrable
  have hdiv : FiniteTimeSingularity.div
      (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) = 0 :=
    Cyl.div_psiField_merPsi α A B Φ C t hC1 hsm2
  have hint' := integrable_vorticity_psiField_merPsi (g := g) hA hB hlaw hsm hint
  -- the inverse Biot–Savart law at the ansatz field
  have hself := hInv _ hC1 (fun y => congrFun hdiv y) hint' hdec x
  -- transport the a.e. equality into the Biot–Savart integral
  have hae : (fun y : R3 => vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) y)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure R3)]
      (fun y : R3 => -(Physical.physOmega α A B g C y t)) :=
    vorticity_psiField_merPsi_ae hA hB hlaw hsm
  have hcongr := Liouville.biotSavart_congr_ae hae x
  change Work.LWP.biotSavart (fun y : R3 => -(Physical.physOmega α A B g C y t)) x
      = Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x
  rw [← hcongr]
  exact hself


end Work.FTS.BSIdent
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory Gradient
open scoped Topology Real NNReal

namespace Work.FTS.BSIdent

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The Weyl/Liouville pair lemma as a named input** (the statement of
`Work.FTS.PressureOn.weyl_pair`, whose proof is still in progress in that area): a continuous field
`Φ` and a continuous scalar `q`, both tending to `0` at infinity, whose divergence and curl vanish
weakly, satisfy `Φ = ∇q` pointwise. -/
def WeylPairPrinciple : Prop :=
  ∀ (q : R3 → ℝ) (Φ : R3 → R3), Continuous q → Continuous Φ →
    Filter.Tendsto q (Filter.cocompact R3) (nhds 0) → Filter.Tendsto Φ (Filter.cocompact R3) (nhds 0) →
    (∀ φ : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x) = -∫ x, q x * Work.FTS.PressureOn.laplaceTrace φ x) →
    (∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0) →
    ∀ x, HasFDerivAt q (innerSL ℝ (Φ x)) x

/-- A field whose `HasFDerivAt 0` datum is `innerSL ℝ (D x)` is zero at `x`. -/
theorem eq_zero_of_hasFDerivAt_zero {D : R3 → R3} {x : R3}
    (h : HasFDerivAt (fun _ : R3 => (0 : ℝ)) (innerSL ℝ (D x)) x) : D x = 0 := by
  have h2 : innerSL ℝ (D x) = 0 := by
    rw [← h.fderiv]
    simp
  have h3 : inner ℝ (D x) (D x) = 0 := by
    have h4 := congrArg (fun (L : R3 →L[ℝ] ℝ) => L (D x)) h2
    simpa [innerSL_apply_apply] using h4
  exact inner_self_eq_zero.mp h3

/-- **THE IDENTIFICATION BY WEYL (route C).**  Let `v` be the (corrected) stream-function field of
the reconstruction at time `t`, agreeing with `Cyl.psiField (merPsi … · t)` on `Uax`.  If the
difference `D = physVel (−physOmega …) · t − v` is continuous, tends to `0` at infinity, and its
divergence and curl vanish weakly, then the Weyl principle (with `q := 0`) makes `D ≡ 0`, and the
identification follows on `Uax`. -/
theorem hid_of_weyl (hweyl : WeylPairPrinciple) {α : ℝ} {A B : ℝ → ℝ}
    {g : ℝ → ℝ → ℝ → ℝ} {C : Physical.PhysClock} {Φ : Fam} {t : ℝ} {v : R3 → R3}
    (hv : ∀ x ∈ Uax, v x
      = Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x)
    (hcont : Continuous (fun x => Physical.physVel (-(Physical.physOmega α A B g C)) x t - v x))
    (hdec : Filter.Tendsto (fun x => Physical.physVel (-(Physical.physOmega α A B g C)) x t - v x)
      (Filter.cocompact R3) (nhds 0))
    (hdiv : ∀ φ : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ x, inner ℝ (Physical.physVel (-(Physical.physOmega α A B g C)) x t - v x)
        (gradient φ x) = 0)
    (hcurl : ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Physical.physVel (-(Physical.physOmega α A B g C)) x t - v x)
        (FiniteTimeSingularity.vorticity ψ x) = 0) :
    ∀ x ∈ Uax, Physical.physVel (-(Physical.physOmega α A B g C)) x t
      = Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x := by
  have hdiv' : ∀ φ : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ x, inner ℝ (Physical.physVel (-(Physical.physOmega α A B g C)) x t - v x)
        (gradient φ x)
        = -∫ x, (0 : ℝ) * Work.FTS.PressureOn.laplaceTrace φ x := by
    intro φ h1 h2
    rw [hdiv φ h1 h2]
    simp
  have h := hweyl 0 (fun x => Physical.physVel (-(Physical.physOmega α A B g C)) x t - v x)
    continuous_const hcont tendsto_const_nhds hdec hdiv' hcurl
  intro x hx
  have h0 : Physical.physVel (-(Physical.physOmega α A B g C)) x t - v x = 0 :=
    eq_zero_of_hasFDerivAt_zero (D := fun y => Physical.physVel (-(Physical.physOmega α A B g C)) y t - v y) (h x)
  rw [sub_eq_zero] at h0
  rw [h0, hv x hx]


end Work.FTS.BSIdent
end
end
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels.merPsiT_origin_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliaries for the vanishing of `ψ`, `∂_zψ`, `∂_rψ` at the origin

Part 1: the generic squeeze against `rhoP r z → 0`, the boundedness of the odd extension
against `cos θ`, the arithmetic core of the first-order bounds, and the pointwise bound for
`ψ/r`.  Consumed by `Work.FTS.BSIdent.Weyl.Levels.merPsiT_origin_profiles`.
-/

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

set_option maxHeartbeats 2000000

/-- If `|f r z| ≤ K·ρ(r,z)` on the half-plane `r > 0`, then `f → 0` at the origin along that
half-plane. -/
theorem tendsto_zero_of_rhoP_bound {f : ℝ × ℝ → ℝ} {K : ℝ}
    (h : ∀ r z : ℝ, 0 < r → |f (r, z)| ≤ K * Work.Cyl.rhoP r z) :
    Filter.Tendsto f (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hb : Filter.Tendsto (fun p : ℝ × ℝ => K * Work.Cyl.rhoP p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 0) := by
    have hc : Continuous fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2 := by
      change Continuous (fun p : ℝ × ℝ => Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
      fun_prop
    have h00 : Work.Cyl.rhoP 0 0 = 0 := by simp [Work.Cyl.rhoP]
    have h1 : Filter.Tendsto (fun p : ℝ × ℝ => Work.Cyl.rhoP p.1 p.2)
        (𝓝[{p : ℝ × ℝ | 0 < p.1}] ((0:ℝ), 0)) (𝓝 (Work.Cyl.rhoP 0 0)) :=
      (hc.tendsto ((0:ℝ), 0)).mono_left nhdsWithin_le_nhds
    rw [h00] at h1
    simpa using h1.const_mul K
  refine squeeze_zero' (Eventually.of_forall fun p => abs_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with p hp
  simpa [Real.norm_eq_abs] using h p.1 p.2 hp

/-- The odd extension loses one power of `π/2 - |θ|`; Jordan's inequality compares that with
`(π/2) cos θ`, which is the form needed to divide by `cos θ`. -/
theorem abs_GG_le_cos {Φ : Work.FTS.BSIdent.Fam} {τ C₀ lam : ℝ}
    (hC₀ : 0 ≤ C₀) (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2) :
    |Work.FTS.BSIdent.Weyl.Dev5.GG Φ τ w θ|
      ≤ C₀ * (Real.pi / 2) * Real.cos θ * (1 + w) ^ (-lam) := by
  have h1 := Work.FTS.BSIdent.Cyl.DecayAux.abs_PhiOdd_le (Φ := Φ) (τ := τ) (C₀ := C₀) (q := 1)
    (lam := lam) hC₀ h0
    (fun w θ hw hθ0 hθ1 => by
      simpa [Real.rpow_one] using hrate w θ hw.le hθ0.le hθ1) hw hθ
  rw [Real.rpow_one] at h1
  have hJ := Work.FTS.BSIdent.Cyl.DecayAux.pi_div_two_sub_abs_le_cos (le_of_lt hθ)
  have hrpow : 0 ≤ (1 + w) ^ (-lam) := Real.rpow_nonneg (by linarith) _
  calc |Work.FTS.BSIdent.Weyl.Dev5.GG Φ τ w θ|
      = |Work.FTS.BSIdent.PhiOdd Φ w θ τ| := rfl
    _ ≤ C₀ * (Real.pi / 2 - |θ|) * (1 + w) ^ (-lam) := h1
    _ ≤ C₀ * (Real.pi / 2 * Real.cos θ) * (1 + w) ^ (-lam) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ hC₀) hrpow
    _ = C₀ * (Real.pi / 2) * Real.cos θ * (1 + w) ^ (-lam) := by ring

/-- The abstract combination `2 Z c Gv + c (p Z w Gw + R Gt)` is `O(ρ)` when all the
coefficients are `O(ρ)`, the three profile quantities are bounded by the rate hypothesis, and
`(1+w)^{-lam} ≤ 1`. -/
theorem abs_chain_le {c p C₀ lam ρ θ w Z R Gv Gw Gt : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 ≤ p) (hθ0 : 0 ≤ θ)
    (hρ : 0 ≤ ρ) (hw : 0 ≤ w)
    (hZ : |Z| ≤ ρ) (hR : |R| ≤ ρ)
    (hval : |Gv| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    (hwd : |Gw| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1))
    (hth : |Gt| ≤ C₀ * (1 + w) ^ (-lam)) :
    |2 * Z * c * Gv + c * (p * Z * w * Gw + R * Gt)|
      ≤ |c| * C₀ * (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1) * ρ := by
  have h1w : (0:ℝ) < 1 + w := by linarith
  have hS : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith
  have hrpow1 : 0 ≤ (1 + w) ^ (-lam) := Real.rpow_nonneg h1w.le _
  have hrpow2 : 0 ≤ (1 + w) ^ (-lam - 1) := Real.rpow_nonneg h1w.le _
  have hpow1 : (1 + w) ^ (-lam) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hpow2 : w * (1 + w) ^ (-lam - 1) ≤ 1 := by
    have e : (1 + w) ^ (-lam - 1) = (1 + w) ^ (-1 : ℝ) * (1 + w) ^ (-lam) := by
      rw [show -lam - 1 = -1 + -lam by ring, Real.rpow_add h1w]
    have e2 : (1 + w) ^ (-1 : ℝ) = (1 + w)⁻¹ := Real.rpow_neg_one _
    have hw1 : w * (1 + w)⁻¹ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (show w ≤ 1 + w by linarith)
        (inv_nonneg.mpr h1w.le)
      rwa [mul_inv_cancel₀ (ne_of_gt h1w)] at h
    calc w * (1 + w) ^ (-lam - 1)
        = (w * (1 + w)⁻¹) * (1 + w) ^ (-lam) := by rw [e, e2]; ring
      _ ≤ 1 * 1 := mul_le_mul hw1 hpow1 hrpow1 (by norm_num)
      _ = 1 := one_mul 1
  have hv : |Gv| ≤ C₀ * (Real.pi / 2) * (1 + w) ^ (-lam) :=
    hval.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hC₀) hrpow1)
  have hwv : |Gw| ≤ C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1) :=
    hwd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hC₀) hrpow2)
  have hA : |2 * Z * c * Gv| ≤ 2 * |c| * C₀ * (Real.pi / 2) * ρ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc 2 * |Z| * |c| * |Gv|
        ≤ 2 * ρ * |c| * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam)) := by
          gcongr
      _ = 2 * |c| * C₀ * (Real.pi / 2) * (ρ * (1 + w) ^ (-lam)) := by ring
      _ ≤ 2 * |c| * C₀ * (Real.pi / 2) * ρ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [hpow1, hρ, hrpow1]
  have hB : |c * (p * Z * w * Gw + R * Gt)| ≤ |c| * (p * C₀ * (Real.pi / 2) + C₀) * ρ := by
    have hsum : |p * Z * w * Gw + R * Gt| ≤ (p * C₀ * (Real.pi / 2) + C₀) * ρ := by
      calc |p * Z * w * Gw + R * Gt| ≤ |p * Z * w * Gw| + |R * Gt| := abs_add_le _ _
        _ ≤ p * C₀ * (Real.pi / 2) * ρ + C₀ * ρ := by
            refine add_le_add ?_ ?_
            · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hw]
              calc p * |Z| * w * |Gw|
                  ≤ p * ρ * w * (C₀ * (Real.pi / 2) * (1 + w) ^ (-lam - 1)) := by gcongr
                _ = p * C₀ * (Real.pi / 2) * (ρ * (w * (1 + w) ^ (-lam - 1))) := by ring
                _ ≤ p * C₀ * (Real.pi / 2) * (ρ * 1) := by
                    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow2 hρ) ?_
                    positivity
                _ = p * C₀ * (Real.pi / 2) * ρ := by ring
            · rw [abs_mul]
              calc |R| * |Gt| ≤ ρ * (C₀ * (1 + w) ^ (-lam)) := by gcongr
                _ = C₀ * (ρ * (1 + w) ^ (-lam)) := by ring
                _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left (by nlinarith [hpow1, hρ, hrpow1]) hC₀
        _ = (p * C₀ * (Real.pi / 2) + C₀) * ρ := by ring
    calc |c * (p * Z * w * Gw + R * Gt)| = |c| * |p * Z * w * Gw + R * Gt| := by rw [abs_mul]
      _ ≤ |c| * ((p * C₀ * (Real.pi / 2) + C₀) * ρ) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg c)
      _ = |c| * (p * C₀ * (Real.pi / 2) + C₀) * ρ := by ring
  calc |2 * Z * c * Gv + c * (p * Z * w * Gw + R * Gt)|
      ≤ |2 * Z * c * Gv| + |c * (p * Z * w * Gw + R * Gt)| := abs_add_le _ _
    _ ≤ 2 * |c| * C₀ * (Real.pi / 2) * ρ + |c| * (p * C₀ * (Real.pi / 2) + C₀) * ρ :=
        add_le_add hA hB
    _ = |c| * C₀ * (2 * (Real.pi / 2) + p * (Real.pi / 2) + 1) * ρ := by ring

/-- The pointwise bound `|ψ/r| ≤ |c| C₀ (π/2) ρ` for `r > 0`. -/
theorem abs_div_merPsiT_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} {C₀ lam : ℝ}
    (hB : 0 < B (Physical.clockInv C t)) (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam)) :
    ∀ r z : ℝ, 0 < r →
      |Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z / r|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) * Work.Cyl.rhoP r z := by
  intro r z hr
  rw [Work.FTS.BSIdent.Weyl.Dev5.merPsiT_div_fst (τ := Physical.clockInv C t) (α := α)
    (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hr]
  have hρnn : 0 ≤ Work.Cyl.rhoP r z := Work.Cyl.rhoP_nonneg r z
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
      / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos hρpos _) hB
  have hθ : |Work.Cyl.thetaP r z| < Real.pi / 2 :=
    Work.FTS.BSIdent.Cyl.abs_thetaP_lt r z
  have hcos : 0 < Real.cos (Work.Cyl.thetaP r z) := Work.Cyl.cos_thetaP_pos hr z
  have hG := abs_GG_le_cos (Φ := Φ) (τ := Physical.clockInv C t) (C₀ := C₀) (lam := lam)
    hC₀ h0 hrate hw hθ
  have hdiv : |Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z) / Real.cos (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2)
        * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
            / B (Physical.clockInv C t)) ^ (-lam) := by
    rw [abs_div, abs_of_pos hcos, div_le_iff₀ hcos]
    calc |Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t)
          (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
          (Work.Cyl.thetaP r z)|
        ≤ C₀ * (Real.pi / 2) * Real.cos (Work.Cyl.thetaP r z)
            * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
                / B (Physical.clockInv C t)) ^ (-lam) := hG
      _ = (C₀ * (Real.pi / 2)
            * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
                / B (Physical.clockInv C t)) ^ (-lam)) * Real.cos (Work.Cyl.thetaP r z) := by
          ring
  have hle1 : (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
      / B (Physical.clockInv C t)) ^ (-lam) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hw]) (by linarith)
  calc |Work.Cyl.rhoP r z * (A (Physical.clockInv C t))⁻¹
        * (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t)
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
            (Work.Cyl.thetaP r z) / Real.cos (Work.Cyl.thetaP r z))|
      = Work.Cyl.rhoP r z * |(A (Physical.clockInv C t))⁻¹|
        * |Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t)
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
            (Work.Cyl.thetaP r z) / Real.cos (Work.Cyl.thetaP r z)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hρnn]
    _ ≤ Work.Cyl.rhoP r z * |(A (Physical.clockInv C t))⁻¹|
        * (C₀ * (Real.pi / 2)
            * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
                / B (Physical.clockInv C t)) ^ (-lam)) :=
        mul_le_mul_of_nonneg_left hdiv (mul_nonneg hρnn (abs_nonneg _))
    _ ≤ Work.Cyl.rhoP r z * |(A (Physical.clockInv C t))⁻¹| * (C₀ * (Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left
          (by
            have h := mul_le_mul_of_nonneg_left hle1
              (by positivity : (0:ℝ) ≤ C₀ * (Real.pi / 2))
            simpa using h)
          (mul_nonneg hρnn (abs_nonneg _))
    _ = |(A (Physical.clockInv C t))⁻¹| * C₀ * (Real.pi / 2) * Work.Cyl.rhoP r z := by ring

end Work.FTS.BSIdent.Weyl.Levels
end
