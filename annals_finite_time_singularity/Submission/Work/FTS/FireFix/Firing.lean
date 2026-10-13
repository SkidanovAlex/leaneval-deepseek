/-
# `Work.FTS.FireFix.Firing` — the firing theorem `blowupAtTop_of_regPkg'`

This is **design item 7 of the physical bridge** (`FTS_PHYS_BRIDGE.md` §1 and §5): the *corrected*
firing of the regularity package into the physical reconstruction,

  `Work.FTS.FireFix.blowupAtTop_of_regPkg'`,

concluding `Work.FTS.Top.BlowupAt α C.T` from the four analytic inputs of the sibling areas
(`BiotSavartSwirl`, `PressureReconstructionOn`, `MeridianEqOn`, `RegPkg'`) plus the smallness of the
perturbation, the clock normalisation `C.A = 2A` and the two differentiability clauses of the
meridian pair.

## The four changes of design §5 item 7 (relative to the delivered `blowupAtTop_of_regPkg`)

1. **a radius per strip** (`physOmega_bundle`, design correction 3): the per-strip bundle replaces
   the uniform support hypotheses `hZ`/`hb` and the fixed radius `R`;
2. **`hBS` in place of the false `hlaw`** (`BiotSavartSwirl`, `neg_physOmega_curl_div`): the curl
   and divergence clauses come from the swirl Biot–Savart law instead of `Work.LWP.BiotSavartLaw`
   (proved false in Lean, `FTS_NOTBSL.lean.txt`);
3. **a local vorticity equation through the pointwise scalar reduction**
   (`vorticityEquationOn_of_meridianEqOn`, `FireFix/VortEqLocal.lean`): the equation is available
   only on `Uax` and for `t ∈ (0, C.T)`, matching `MeridianEqOn`;
4. **the honest pressure input** `PressureReconstructionOn α`, fed through its exact hypothesis
   list: the strip `C^{1,α}` (from the bundles), `hcurl`, `hdivu`, the per-strip support radius,
   and the three analytic clauses `physOmega_timeDeriv_continuous`,
   `physOmega_hasDerivWithinAt`, `physOmega_fderiv_locallyIntegrable` (modules under
   `FireFix/Clauses/`), together with the `Uax` differentiability and equation clause assembled
   here.

The sign convention is **correction 1**: the physical vorticity is `ω := −physOmega α A B g C`, and
the meridian profile of the hypotheses is transported by linearity
(`Work.FTS.MeridianDyn.MeridianEqOn.neg_left`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FireFix.FiringData
import Submission.Work.FTS.FireFix.PhysFields
import Submission.Work.FTS.FireFix.VortEqLocal
import Submission.Work.FTS.FireFix.Reconstruct
import Submission.Work.FTS.FireFix.Clauses.physOmega_timeDeriv_continuous
import Submission.Work.FTS.FireFix.Clauses.physOmega_hasDerivWithinAt
import Submission.Work.FTS.FireFix.Clauses.physOmega_fderiv_locallyIntegrable
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two
import Submission.Work.FTS.FireFix.Clauses.negPhysOmega_contDiffAt_one

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
