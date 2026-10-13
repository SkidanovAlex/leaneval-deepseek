/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongEps.EComparison.HomClsSlotsZero` — the slots of the homogeneous class vanish

The main theorem of this file is `HomClsSlotsZero`: for `0 < α ≤ 1`, a `C^∞` function `w` on the
open quadrant that solves the homogeneous elliptic problem `bslOp α w = 0` (with the Dirichlet
data and the `z`-decay) and whose three *slots* `Rop α w`, `Uop α w / sin 2θ`, `Vop w` are in
`ℋ⁶` must have *all three slots vanishing identically* on the open quadrant `(0,∞) × (0,π/2)`.

## The route

The auxiliary function `Φ := Uop α w = -3w - α D_z w` is again a solution of the homogeneous
equation (because `bslOp α` commutes with `D_z`, `TT.bslOp_DzIter_eq`), it satisfies the
Dirichlet value condition `Φ(z,0) = 0`, and `Φ / sin 2θ` is exactly the `U`-slot of the
hypotheses (`HkMem α 6`).  The heart of the proof is then

* `SlotsZeroModeODE`: expanding `Φ` in the angular Dirichlet eigenbasis `eFam m` (`Lzero`'s
  Gegenbauer eigenfamily, eigenvalues `lam m = 2m(2m+5)`), each modal coefficient
  `z ↦ ∫ θ, Φ z θ * eFam m θ * cos θ` is a *weak* solution of the Euler ODE
  `α²z²u'' + α(5+α)z u' = (lam m) u` with the natural weight `z^((5-α)/α)`, and is `L²(z^{-4})`;
* `EulerWeakZero`: a locally integrable weak solution of that Euler equation with
  `∫ u² z^{-4} < ∞` vanishes a.e. (both indicial roots `2m/α` and `-(2m+5)/α` fail the
  integrability of `u²z^{-4}` at one of the two ends);
* `SlotsZeroComplete`: the vanishing of all modal moments a.e. in `z`, together with the
  continuity of `Φ` and the completeness of `eFam` in `L²(Iθ, cos θ dθ)`, gives `Φ ≡ 0` on the
  quadrant;
* `SlotsZeroRest`: from `Uop α w = 0` one gets `w = C(θ) z^{-3/α}`, whence `Vop w = z^{-3/α}A(C)`
  is killed by `HkMem α 6 (Vop w)` (the weight `z^{-6/α-4}` is not integrable at `0`), and
  `Rop α w = Vop w - tan θ · Uop α w = 0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.StrongEps.EComparison.HomClsZeroRefute
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeODE
import Submission.Work.FTS.StrongEps.EComparison.EulerWeakZero
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroComplete
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroRest
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.FTS.BSIdent.OddExt.bslOp_const_mul
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option autoImplicit false

/-- **The slots of the packages depend only on the source** (the pivot replacement of the refuted
`HomClsZero`).  The packages `EllPkgGo`/`EllPkgK` constrain a solution `Ψ` of the elliptic law with
source `F` only through the three *slots* `Rop α (PhiTil α F Ψ)`, `Uop α (PhiTil α F Ψ) / sin 2θ`,
`Vop (PhiTil α F Ψ)`; that is literally how `N` and `gRHS` consume the stream function:
`N α F Φ = 2·Rop(PhiTil) z θ·F - 2·Uop(PhiTil)·∂_θF - 2α·Vop(PhiTil)·D_zF - …`, so the whole
right-hand side of the scheme sees `Φ` only through the three slots.  Moreover *uniqueness* of `Ψ`
in that class is **false**: a sibling delegate proved
`Work.FTS.StrongEps.EComparison.HomClsZeroRefute.exists_counterexample`
(`Submission/Work/FTS/StrongEps/EComparison/HomClsZeroRefute.lean`, `sorry`-free), with the
homogeneous mode `z^{-3/α} / cos θ` (the special radial exponent `α s = -3`, for which
`Uop α (mode) ≡ 0`, `Vop (mode) ≡ 0`, `Rop α (mode) ≡ 0`, so the three `HkMem` hypotheses of the
class hold *vacuously*).

The assertion below is that the *slots*, unlike `Ψ` itself, are still pinned by the source
(equivalently, by the closure of `EllPkgCls` under differences, that every homogeneous element of
the class has vanishing slots on the open quadrant).  This is exactly the input that
`EComparison.E_sub_eq_of_uniq` needs in place of the refuted `Ψ`-uniqueness.

The conclusion is restricted to the *open* quadrant `θ ∈ (0, π/2)`, as two reviews required: the
five hypotheses only constrain `w` on `Q0`/`Iθ` (and `SmoothOpen`, `IsBslSol` and all three
`HkMem`-integrands see nothing outside `(0,∞) × (0,π/2)`), so an extension of a quadrant solution
that is non-trivial off `(0,π/2)` satisfies everything and breaks an unrestricted `∀ θ : ℝ`.  Nothing
is lost downstream: the slots are compared only through `HkSq`/`HkMem`, which integrate over `Iθ`.

Route.  `bslOp α w = 0` with the Dirichlet data and the `z`-decay; a separable homogeneous mode
`w = z^r ψ(θ)` must satisfy `α²r² + 5αr = λ` for an eigenvalue `λ` of the angular operator
`Lzero`, and then `Rop α w = z^r((2+αr) tan θ · ψ + ψ')` etc.: a mode whose slot does *not* vanish
has a `z`-profile whose exponent conflicts with the (non-vacuous) `HkMem` bound — the weight
`Work.Spaces.w(z)² ≍ z^{-4}` at `z → 0⁺` forces the slot's `z`-moment to be finite, while the decay
conjunct of `IsBslSol` forces the opposite growth.  A review checked the eigenfunction `tan θ` and
the combinations `a tanθ + b secθ`: their slots are `∝ z^{-3/α}` and fail `hR`/`hV`, while the
`αr = -3`, `ψ = 1/cos θ` mode has all three slots identically zero.  The class is not vacuous for
the *slots*: `w = z^{-5/α} sin 2θ` has `Rop α w = z^{-5/α}(2cos2θ - 6sin²θ) ≠ 0` and is correctly
excluded by `HkMem α 6 (Rop α w)`. -/
theorem HomClsSlotsZero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen w)
    (hsol : Work.Elliptic.IsBslSol α (fun _ _ => (0 : ℝ)) w)
    (hR : Work.Spaces.HkMem α 6 (Work.Construction.Rop α w))
    (hU : Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.Uop α w z θ / Work.Construction.s2 θ))
    (hV : Work.Spaces.HkMem α 6 (Work.Construction.Vop w)) :
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Rop α w z θ = 0) ∧
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0) ∧
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Vop w z θ = 0) := by
  -- ## The auxiliary homogeneous solution `Φ = Uop α w = -3w - α·D_z w`
  set Φ : ℝ → ℝ → ℝ := Work.Construction.Uop α w with hΦdef
  have hΦfun : Φ = fun z θ => (-3 : ℝ) • w z θ + (-α) • (Work.Spaces.Dz w) z θ := by
    funext z θ
    simp only [hΦdef, Work.Construction.Uop, Work.Spaces.Dz, Work.Spaces.pz, smul_eq_mul]
    ring
  have hsm' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry w) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall w).mp hsm n
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hsm.Dz
  -- `Φ` is `C^∞` on the open quadrant
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen Φ := by
    rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
    intro n
    have h1 : ContDiffOn ℝ n (Function.uncurry w) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm' n
    have h2 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz w))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dz w)).mp hDzsm n
    have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (-3 : ℝ) • Function.uncurry w p
        + (-α) • Function.uncurry (Work.Spaces.Dz w) p) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (h1.const_smul (-3)).add (h2.const_smul (-α))
    have hfun : Function.uncurry Φ = fun p : ℝ × ℝ => (-3 : ℝ) • Function.uncurry w p
        + (-α) • Function.uncurry (Work.Spaces.Dz w) p := by
      funext p
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry, hΦfun, Work.Spaces.Dz, Work.Spaces.pz, smul_eq_mul]
    rwa [hfun]
  have hΦcont : ContinuousOn (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hΦsm 0).continuousOn
  -- ## the equation for `Φ`
  have hw_eq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α w z θ = 0 := by
    intro z hz θ h0 h1
    have h := hsol.1 z hz θ h0 h1
    simpa using h
  have hΦsol : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = 0 := by
    intro z hz θ h0 h1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
    have hv : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩
    have hnb : (Work.FTS.EllipticEst.Q0 : Set (ℝ × ℝ)) ∈ 𝓝 (z, θ) :=
      Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hv
    have hD1 : Work.Elliptic.bslOp α (Work.Spaces.Dz w) z θ = 0 := by
      have h := Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α (fun _ _ => (0 : ℝ)) w 1
        hsm' hw_eq z hz θ h0 h1
      have hz0 : Work.Spaces.DzIter 1 (fun _ _ => (0 : ℝ)) z θ = 0 := by
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
          Work.Spaces.pz]
        simp
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] at h
      rw [h, hz0]
    have hAdd : Work.Elliptic.bslOp α Φ z θ
        = (-3 : ℝ) * Work.Elliptic.bslOp α w z θ
          + (-α) * Work.Elliptic.bslOp α (Work.Spaces.Dz w) z θ := by
      rw [hΦfun]
      have hb3 : Work.Elliptic.bslOp α (fun z θ => (-3 : ℝ) • w z θ) z θ
          = (-3 : ℝ) * Work.Elliptic.bslOp α w z θ := by
        simpa only [smul_eq_mul] using
          Work.FTS.BSIdent.OddExt.bslOp_const_mul α (-3) w z θ
      have hba : Work.Elliptic.bslOp α (fun z θ => (-α) • (Work.Spaces.Dz w) z θ) z θ
          = (-α) * Work.Elliptic.bslOp α (Work.Spaces.Dz w) z θ := by
        simpa only [smul_eq_mul] using
          Work.FTS.BSIdent.OddExt.bslOp_const_mul α (-α) (Work.Spaces.Dz w) z θ
      rw [Work.Elliptic.bslOp_add α (fun z θ => (-3 : ℝ) • w z θ)
        (fun z θ => (-α) • (Work.Spaces.Dz w) z θ) z θ hcos]
      · rw [hb3, hba]
      · exact ((hsm' 2).contDiffAt hnb).const_smul (-3)
      · exact (((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dz w)).mp hDzsm 2).contDiffAt
          hnb).const_smul (-α)
    rw [hAdd, hw_eq z hz θ h0 h1, hD1]
    ring
  -- ## the Dirichlet value at `θ = 0`
  have hΦ0 : ∀ z, Φ z 0 = 0 := by
    intro z
    have hw0 : w z 0 = 0 := hsol.2.1 z
    have hpz0 : Work.Spaces.pz w z 0 = 0 := by
      have hfun : (fun z' : ℝ => w z' 0) = fun _ => (0 : ℝ) :=
        funext fun z' => hsol.2.1 z'
      simp only [Work.Spaces.pz]
      rw [hfun, deriv_const]
    simp only [hΦdef, Work.Construction.Uop]
    rw [hw0, hpz0]
    ring
  -- ## the slot hypothesis for `Φ`
  have hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ) := hU
  -- ## the slice integrability
  have hInt : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Φ z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    SlotsZeroSliceInt hΦsm hΦ0 hHk
  -- ## all modal moments vanish for a.e. `z`
  have hMom : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) = 0 := by
    refine MeasureTheory.ae_all_iff.mpr (fun m => ?_)
    have hC1 := SlotsZeroModeODE (α := α) (Φ := Φ)
      (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hΦsm n) hΦsol hΦ0 hHk m
    exact EulerWeakZero (α := α) (L := Work.FTS.PhiStar.Gegenbauer.lam m) hα hC1.1 hC1.2.1 hC1.2.2
  -- ## `Φ` vanishes on the open quadrant
  have hΦzero : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = 0 :=
    SlotsZeroComplete (Φ := Φ) hΦcont hInt hMom
  have hUzero : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Construction.Uop α w z θ = 0 := by
    intro z hz θ hθ
    have h := hΦzero z hz θ hθ
    simpa only [← hΦdef] using h
  exact SlotsZeroRest hα hsm hUzero hV

end Work.FTS.StrongEps.EComparison
