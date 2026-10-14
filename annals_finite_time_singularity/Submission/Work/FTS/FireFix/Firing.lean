import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.ResidDyn
import Submission.Work.FTS.MeridianDyn.Vort
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_BSIdentP.Slim.AbsPdZPdRPsiCoreLeOne
import Submission.Work.FTS_BSIdentP.Slim.MerPsiDecay
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddNegPi
import Submission.Work.FTS_BSIdentP.Slim.TendstoSliceQuotient
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
-- ===== merged: Submission.Work.FTS.BSIdent.Weyl.Levels._stub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
open Filter Set
open scoped Topology

-- Bridge module: re-exports the delegated lemmas under the `DevStub` names used by the
-- development files below (the real proofs live in the imported `Work.FTS.BSIdent.Weyl.Levels`
-- modules).
namespace Work.FTS.BSIdent.Weyl.DevStub

theorem tendsto_slice_quotient {f : ℝ → ℝ → ℝ} {w₀ θ₀ δ : ℝ} (hδ : 0 < δ)
    (hsm : ∀ w θ, |w - w₀| < δ → |θ - θ₀| < δ → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => f p.1 p.2) (w, θ))
    (hz : ∀ w, |w - w₀| < δ → f w θ₀ = 0) :
    Filter.Tendsto (fun p : ℝ × ℝ => f p.1 p.2 / (p.2 - θ₀))
      (𝓝[{p : ℝ × ℝ | |p.1 - w₀| < δ ∧ |p.2 - θ₀| < δ ∧ p.2 ≠ θ₀}] (w₀, θ₀))
      (𝓝 (deriv (fun θ => f w₀ θ) θ₀)) := by
  exact Work.FTS.BSIdent.Weyl.Levels.tendsto_slice_quotient hδ hsm hz

theorem tendsto_PhiOdd_div_cos_at_pi_div_two {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0)
    {w₀ : ℝ} (hw₀ : 0 < w₀) :
    Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2}] (w₀, Real.pi / 2))
      (𝓝 (-(deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2)))) := by
  exact Work.FTS.BSIdent.Weyl.Levels.tendsto_PhiOdd_div_cos_at_pi_div_two hsm hπ hw₀

theorem tendsto_PhiOdd_div_cos_at_neg_pi_div_two {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0)
    {w₀ : ℝ} (hw₀ : 0 < w₀) :
    Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ / Real.cos p.2)
      (𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ -Real.pi / 2 < p.2 ∧ p.2 < 0}] (w₀, -(Real.pi / 2)))
      (𝓝 (deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2))) := by
  exact Work.FTS.BSIdent.Weyl.Levels.tendsto_PhiOdd_div_cos_at_neg_pi_div_two hsm hπ hw₀

theorem continuousAt_pdZ_G_zero {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ =>
      Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) p.1 p.2)
      (w₀, 0) := by
  exact Work.FTS.BSIdent.Weyl.Levels.continuousAt_pdZ_G_zero hsm h0 hw₀

theorem rho_mul_rpow_weight_le_two {p lam b ρ : ℝ} (hp : 0 < p) (hlam : 0 < lam) (hb : 0 < b)
    (hρ : 0 ≤ ρ) (hpl : 2 ≤ p * lam) :
    ρ * (1 + ρ ^ p / b) ^ (-lam) ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
  exact Work.FTS.BSIdent.Weyl.Levels.rho_mul_rpow_weight_le_two hp hlam hb hρ hpl

theorem merPsiT_decay_bounds_ne {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r z : ℝ, 0 < r → z ≠ 0 →
      |Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z| / r ≤ K / (1 + Work.Cyl.rhoP r z) ∧
      |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ K / (1 + Work.Cyl.rhoP r z) ∧
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ K / (1 + Work.Cyl.rhoP r z) := by
  exact Work.FTS.BSIdent.Weyl.Levels.merPsiT_decay_bounds_ne hα hA hB hsm hzeroPlane hzeroAxis hlam hC₀ hexp hrate

end Work.FTS.BSIdent.Weyl.DevStub
end
-- ===== merged: Submission.Work.FTS.FireFix.Firing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix

open Work.FTS.Physical (PhysClock)
open Work.FTS.Regularity (pExp gSlice physVort)
open Work.FTS.MeridianDyn (MeridianEqOn)
open Work.FTS.FireFix.Clauses

/-- **THE FIRING THEOREM (design §1, item 7 of the physical bridge).**  From

* the *corrected* regularity package `RegPkg'` of the self-similar profile on every fake-time strip
  (`hreg`, proved by the `RegPkgGal` area),
* the clock normalisation `C.A = 2·A` of design correction 2 (`hAeq`),
* the smallness `|g| ≤ 3α/200` of the perturbation (`hsmall`),
* the swirl Biot–Savart law `BiotSavartSwirl` (`hBS`, proved by `BSSwirl`),
* the pressure reconstruction `PressureReconstructionOn α` (`hpress`, proved by `PressureOn`),
* the meridian form of the fake-time equation on `(0, C.T)` (`hmer`, proved by `MeridianDyn`),
* the identification of the reconstructed velocity with the stream-function field on `Uax`
  (`hid`, proved by `BSIdent`),
* the differentiability clauses of the meridian pair (`hΨ`, `hW`),

the reconstructed solution `(u, p) = (physVel (−physOmega …), p)` is a finite-time blow-up of the
incompressible Euler equations at the clock's blow-up time `C.T`, in node N0's interface
`Work.FTS.Top.BlowupAt α C.T`.

Here `merPsi` is the design's stream function
`ρ(r,z)²·A(τ(t))⁻¹·Φ̂(ρ(r,z)^{3α}/B(τ(t)), θ(r,z), τ(t))` of the reconstruction
(`Work.FTS.MeridianDyn.merPsi`, with `Φ` the caller's family — the natural instantiation passes the
odd extension in `θ`). -/
noncomputable def blowupAtTop_of_regPkg' {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {C : PhysClock} {Φ : ℝ → ℝ → ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
    (hAeq : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hsmall : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ 3 * (α : ℝ) / 200)
    (hBS : Work.FTS.BSSwirl.BiotSavartSwirl)
    (hpress : Work.FTS.PressureOn.PressureReconstructionOn α)
    (hmer : MeridianEqOn (Work.FTS.Physical.merProfile (α : ℝ) A B g C)
      (merPsi (α : ℝ) A B Φ C) C.T)
    (hid : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Uax,
      Work.FTS.Physical.physVel
        (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x)
    (hΨ : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      ContDiffAt ℝ 3 (fun p : ℝ × ℝ => merPsi (α : ℝ) A B Φ C p.1 p.2 t) (r, z))
    (hW : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      Work.Cyl.DiffAt2 (fun r z => Work.FTS.Physical.merProfile (α : ℝ) A B g C r z t) r z) :
    Work.FTS.Top.BlowupAt α C.T := by
  have hα : 0 < (α : ℝ) := (hreg 1 one_pos).hα
  have hα13 : (α : ℝ) ≤ 1 / 3 := (hreg 1 one_pos).hα13
  have hα1 : (α : ℝ) < 1 := by linarith
  have hTpos : 0 < C.T := Work.FTS.Physical.Clock.T_pos C
  -- the per-strip bundles, the curl/divergence, the parity and the datum
  have hbun := physOmega_bundle (α := α) (A := A) (B := B) (g := g) (C := C) hreg hAeq
  have hcd := neg_physOmega_curl_div (α := α) hα hα1 hBS hbun
  have hodd : ∀ t ∈ Set.Ico 0 C.T, IsOdd ((Work.FTS.Physical.physVel
      (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s)) · t) :=
    fun t ht => neg_physOmega_isOdd (α := α) (A := A) (B := B) (g := g) (C := C) hreg ht
  have hdat := neg_physOmega_datum_holder (α := α) hα hα1 hbun
  have hlow := negPhysOmega_lower (α := α) hα hα13 hreg hAeq hsmall
  -- the `Uax` clause of the pressure input
  have hUax : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Uax,
      ContDiffAt ℝ 2 ((Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s)) · t) x ∧
        ContDiffAt ℝ 1 ((fun y s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C y s) · t) x ∧
        timeDeriv (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) x t
          + directionalDeriv (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s)
              (Work.FTS.Physical.physVel
                (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s)) x t
          = directionalDeriv (Work.FTS.Physical.physVel
                (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s))
              (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) x t := by
    intro t ht x hx
    have hr : 0 < Work.Cyl.radial x := by
      rcases eq_or_lt_of_le (Work.Cyl.radial_nonneg x) with h | h
      · exfalso
        have h01 : x 0 = 0 ∧ x 1 = 0 := (Work.Cyl.radial_eq_zero_iff x).mp h.symm
        exact hx.2 (by rw [h01.1, h01.2]; norm_num)
      · exact h
    have hz : Work.Cyl.axial x ≠ 0 := hx.1
    -- the velocity is the stream-function field locally
    have hfun1 : (fun y : R3 => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y t)
        =ᶠ[𝓝 x] fun y : R3 =>
            Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) y := by
      filter_upwards [Work.FTS.PressureOn.isOpen_Uax.mem_nhds hx] with y hy
      exact hid t ht y hy
    -- the vorticity slice is the negated meridional swirl field
    have hfield : (fun y s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C y s)
        = fun y s => (fun r z s => - Work.FTS.Physical.merProfile (α : ℝ) A B g C r z s)
            (Work.Cyl.radial y) (Work.Cyl.axial y) s • Work.Cyl.eTheta y := by
      funext y s
      rw [Work.FTS.Physical.physOmega_eq_smul_eTheta, neg_smul]
    refine ⟨?_, ?_, ?_⟩
    · exact (psiField_contDiffAt_two (ψ := fun r z => merPsi (α : ℝ) A B Φ C r z t)
        hr (hΨ t ht _ _ hr hz)).congr_of_eventuallyEq hfun1
    · exact negPhysOmega_contDiffAt_one (α := α) (A := A) (B := B) (g := g)
        (Φ := fun r z t => merPsi (α : ℝ) A B Φ C r z t) (C := C)
        (fun t ht x hx => hid t ht x hx)
        (fun t ht r z hr' hz' => hΨ t ht r z hr' hz') (fun t ht x => hcd.1 t ht x) t ht x hx
    · -- the pointwise vorticity equation, from the meridian equation by linearity
      have hmer' := MeridianEqOn.neg_left (W := Work.FTS.Physical.merProfile (α : ℝ) A B g C)
        (ψ := merPsi (α : ℝ) A B Φ C) hmer
      have hvec := vorticityEquationOn_of_meridianEqOn
        (W := fun r z s => - Work.FTS.Physical.merProfile (α : ℝ) A B g C r z s)
        (ψ := fun r z s => merPsi (α : ℝ) A B Φ C r z s) (T := C.T) hmer'
        (fun t ht r z hr' hz' => (hW t ht r z hr' hz').neg)
        (fun t ht r z hr' hz' => (hΨ t ht r z hr' hz').of_le (by norm_num)) t ht x hx
      exact vorticityEquation_transfer
        (u := fun y s => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C x s) y s)
        (v := fun y s => Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z s) y)
        (ω := fun y s => - Work.FTS.Physical.physOmega (α : ℝ) A B g C y s)
        (η := fun y s => (fun r z s => - Work.FTS.Physical.merProfile (α : ℝ) A B g C r z s)
            (Work.Cyl.radial y) (Work.Cyl.axial y) s • Work.Cyl.eTheta y)
        hfun1 hfield hvec
  exact blowupAt_of_physical' (α := α) hα hα1 hTpos hbun hcd.1 hcd.2 hodd
    (physOmega_timeDeriv_continuous (α := (α : ℝ)) hα hreg)
    (physOmega_hasDerivWithinAt (α := (α : ℝ)) hα hreg)
    (physOmega_fderiv_locallyIntegrable (α := (α : ℝ)) hα hreg)
    hUax hdat hpress hlow

end Work.FTS.FireFix
end
