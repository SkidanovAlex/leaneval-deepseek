/-
# `CexK5`: the machine-checked algebraic/analytic core of the counterexample to
`Work.FTS.EllSol.PkgK5.uopTransferK5`

`uopTransferK5` is **FALSE** for every `k ≥ 8`: see `NOTES_uopTransferK5_FALSE.md` for the full
refutation.  The analytic inputs are the standard (elementary) facts about the profile

  `lm(z) = ψ(z)·z^{-8}·cos z`  (`ψ` a smooth cutoff, `ψ ≡ 0` on `(0,1]`, `≡ 1` on `[2,∞)`),
  adjusted by a compactly supported smooth multiple so that `∫_0^∞ lm(r)/r dr = 0`,

namely `D_z^j lm = O(z^{j-8})` for `z → ∞` (so `w·D_z^j lm ∈ L²` for `j ≤ 7`) while
`D_z^8 lm = cos z + O(1/z) ∉ L²(w²)`, `w(z) = (1+z)²/z²`.

What is *machine-checked here* is the reduction of the target's first conjunct to that profile
fact.  With `g := lm(z)·sin 2θ`, `Φg := -Gsing α g·sin 2θ`:

* `PhiTil α g Φg = fun z θ => -Gbar α g z · sin 2θ` (proved in `PkgK5/CexRop.lean`);
* `F_*(g) = (4/15)·lm` (`fstar_radial_sin` below, and `PkgK5/_probe_cex.lean`);
* the quotient `q := Uop α (PhiTil α g Φg)/sin 2θ` is *radial* and equals
  `-2·Gbar α g - (1/5)·lm` on the open quadrant (`uop_witness_radial` below);

so the `i = 8` pure-radial slot of `HkIntegrand α 8 q` is `(D_z^8 q)² w² / sin(2θ)^η` with
`D_z^8 q = -2 D_z^8(Gbar α g) - (1/5) D_z^8 lm`, and `D_z^8(Gbar α g)` is a combination of
`Gbar α g` and `D_z^j F_*(g) = (4/15) D_z^j lm` for `j ≤ 7` (recursion
`D_z(Gbar α g) = -(5/α)Gbar α g - (3/(4α))F_*(g)`).  Hence `∫_0^∞ w²(D_z^8 q)² = ∞`, the outer
integral defining `HkMem α 8 q` is infinite, and the conclusion of `uopTransferK5` fails at
`k = 8`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.PkgK5.CexRop
import Submission.Work.FTS.EllipticEst.Gsing_deriv_rel
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.CexK5

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. The angular moment of the radial `sin 2θ` mode -/

/-- `Fstar` of a radial multiple of `sin 2θ` is `(4/15)` times the radial factor
(`∫_0^{π/2} sin 2θ · sin θ cos²θ dθ = 4/15`). -/
theorem fstar_radial_sin (lm : ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (fun z θ => lm z * Real.sin (2 * θ)) z = (4 / 15) * lm z := by
  rw [Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => (fun z θ => lm z * Real.sin (2 * θ)) z θ * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => lm z * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) from by
    funext θ; ring]
  rw [MeasureTheory.integral_const_mul, Work.Elliptic.integral_sin_two_mul_sinCos2]
  ring

/-! ## 2. The `sin 2θ`-direction of the quotient `U/sin 2θ` -/

/-- `U(Λ(z)·sin 2θ)/sin 2θ = -3Λ - α·z·Λ'` (the quotient is purely radial). -/
theorem uop_div_sin_radial (α : ℝ) (Λ : ℝ → ℝ) (Λ' z θ : ℝ)
    (hΛ : HasDerivAt Λ Λ' z) (hs : Real.sin (2 * θ) ≠ 0) :
    Work.Construction.Uop α (fun z θ => Λ z * Real.sin (2 * θ)) z θ / Work.Construction.s2 θ
      = -3 * Λ z - α * (z * Λ') := by
  have hpz : Work.Spaces.pz (fun z θ => Λ z * Real.sin (2 * θ)) z θ
      = Λ' * Real.sin (2 * θ) := by
    have h := hΛ.mul_const (Real.sin (2 * θ))
    simpa [Work.Spaces.pz] using h.deriv
  rw [Work.Construction.Uop, hpz, Work.Construction.s2]
  field_simp

/-! ## 3. The first-order relation of `Gbar` -/

/-- `HasDerivAt (Gbar α F) (DGbar α F z) z` from the primitive facts on `F_*`. -/
theorem hasDerivAt_Gbar_DGbar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hJ : HasDerivAt (Work.Elliptic.Jfun α F)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    HasDerivAt (Work.Elliptic.Gbar α F) (Work.Elliptic.DGbar α F z) z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hA : HasDerivAt (Work.Elliptic.Abar α) (Work.Elliptic.DAbar α z) z := by
    have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inl hz0)
    have h := hp.const_mul (-(3 / (4 * α)))
    convert h using 1
    · ext y; rfl
    · show (-(3 / (4 * α)) * (-(5 / α))) * z ^ (-(5 / α) - 1)
          = -(3 / (4 * α)) * (-(5 / α) * z ^ (-(5 / α) - 1))
      ring
  have h := hA.mul hJ
  have hfun : (Work.Elliptic.Abar α * Work.Elliptic.Jfun α F) = Work.Elliptic.Gbar α F := rfl
  rw [hfun] at h
  simpa only [Work.Elliptic.DGbar] using h

/-- **The first-order relation of `Ḡ`**:  `α·D_z(Ḡ α F) = -5·Ḡ α F - (3/4)·F_*(F)`, i.e.
`α·z·∂_z(Gbar α F) z = -5·Gbar α F z - (3/4)·Fstar F z` on `z > 0`.

This is `Gsing_deriv_rel` (`α z ∂_z Gsing = -5 Ḡ`, proved in
`Submission/Work/FTS/EllipticEst/Gsing_deriv_rel.lean`) together with
`α z ∂_z Gstar = (3/4)F_*`. -/
theorem Gbar_deriv_rel (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z)
    (hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z)
    (hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α * (z * Work.Elliptic.DGbar α F z)
        = -5 * Work.Elliptic.Gbar α F z - (3 / 4) * Work.Elliptic.Fstar F z := by
  intro z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hJz : HasDerivAt (Work.Elliptic.Jfun α F)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        = Work.Elliptic.Jfun α F := rfl
    rw [hfun] at h
    exact h
  have hGstar : HasDerivAt (Work.Elliptic.Gstar α F) (Work.Elliptic.DGstar α F z) z := by
    have h := (hL12 z hz).const_mul (-(1 / (4 * α)))
    have hfun : (fun z' => -(1 / (4 * α)) * Work.Elliptic.L12 F z') = Work.Elliptic.Gstar α F := rfl
    rw [hfun] at h
    simpa only [Work.Elliptic.DGstar] using h
  have hGbar : HasDerivAt (Work.Elliptic.Gbar α F) (Work.Elliptic.DGbar α F z) z :=
    hasDerivAt_Gbar_DGbar α F hz hJz
  -- the split of `deriv (Gsing α F)` and the proved relation for `Gsing`
  have hsum : deriv (Work.Elliptic.Gsing α F) z
      = Work.Elliptic.DGstar α F z + Work.Elliptic.DGbar α F z := by
    have hfun : Work.Elliptic.Gsing α F = Work.Elliptic.Gstar α F + Work.Elliptic.Gbar α F := rfl
    rw [hfun, deriv_add hGstar.differentiableAt hGbar.differentiableAt,
      hGstar.deriv, hGbar.deriv]
  have hrel := Work.FTS.EllipticEst.Gsing_deriv_rel α F hα hL12 hFc hJ z hz
  rw [hsum] at hrel
  -- `hrel : α * z * (DGstar + DGbar) = -5 * Gbar`
  have hdst : Work.Elliptic.DGstar α F z
      = 3 * Work.Elliptic.Fstar F z / (4 * α * z) := by
    rw [Work.Elliptic.DGstar]
    field_simp
  rw [hdst] at hrel
  have h3 : α * z * (3 * Work.Elliptic.Fstar F z / (4 * α * z) + Work.Elliptic.DGbar α F z)
      = α * z * (3 * Work.Elliptic.Fstar F z / (4 * α * z))
        + α * z * Work.Elliptic.DGbar α F z := by ring
  rw [h3] at hrel
  have h2 : α * z * (3 * Work.Elliptic.Fstar F z / (4 * α * z))
      = (3 / 4) * Work.Elliptic.Fstar F z := by
    field_simp
  rw [h2] at hrel
  linarith [hrel]

/-! ## 4. The quotient of the witness -/

/-- `HasDerivAt (fun z => -Gbar α F z) (-(DGbar α F z)) z`. -/
theorem hasDerivAt_neg_Gbar_DGbar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hJ : HasDerivAt (Work.Elliptic.Jfun α F)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    HasDerivAt (fun z' => -(Work.Elliptic.Gbar α F z')) (-(Work.Elliptic.DGbar α F z)) z :=
  (hasDerivAt_Gbar_DGbar α F hz hJ).neg

/-- **The counterexample identity**: for `Φg := -Gsing α g·sin 2θ` the quotient
`Uop α (PhiTil α g Φg)/sin 2θ` is the *radial* function `-2·Ḡ(α,g) - (3/4)·F_*(g)` on the open
quadrant. -/
theorem uop_witness (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z)
    (hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar g) (deriv (Work.Elliptic.Fstar g) z) z)
    (hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α (Work.Construction.PhiTil α g
          (fun z θ => -(Work.Elliptic.Gsing α g z) * Real.sin (2 * θ))) z θ
        / Work.Construction.s2 θ
        = -2 * Work.Elliptic.Gbar α g z - (3 / 4) * Work.Elliptic.Fstar g z := by
  intro z θ hz hθ hθ2
  have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
  have hs : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  rw [CexAlgebra.phiTil_witness]
  have hJz : HasDerivAt (Work.Elliptic.Jfun α g)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z := by
    have h := hJ z hz'
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
        = Work.Elliptic.Jfun α g := rfl
    rw [hfun] at h
    exact h
  rw [uop_div_sin_radial α (fun z' => -(Work.Elliptic.Gbar α g z'))
    (-(Work.Elliptic.DGbar α g z)) z θ (hasDerivAt_neg_Gbar_DGbar α g hz hJz) hs]
  have hrel := Gbar_deriv_rel α g hα hL12 hFc hJ z hz'
  linarith [hrel]

/-! ## 5. The witness with the explicit profile -/

/-- **The counterexample in its final form**: for `g := lm(z)·sin 2θ` the quotient is
`-2·Ḡ(α,g) - (1/5)·lm`, hence `D_z^8` of it contains `-(1/5)·D_z^8 lm` with a *nonzero*
coefficient, while `D_z^8(Gbar α g)` only sees `D_z^j lm` for `j ≤ 7`. -/
theorem uop_witness_radial (α : ℝ) (lm : ℝ → ℝ) (hα : 0 < α)
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 (fun z θ => lm z * Real.sin (2 * θ)))
        (-(3 * Work.Elliptic.Fstar (fun z θ => lm z * Real.sin (2 * θ)) z / z)) z)
    (hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar (fun z θ => lm z * Real.sin (2 * θ)))
        (deriv (Work.Elliptic.Fstar (fun z θ => lm z * Real.sin (2 * θ))) z) z)
    (hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α)
          * Work.Elliptic.Fstar (fun z θ => lm z * Real.sin (2 * θ)) s)
        (z ^ ((5 - α) / α)
          * Work.Elliptic.Fstar (fun z θ => lm z * Real.sin (2 * θ)) z) z) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α (Work.Construction.PhiTil α
          (fun z θ => lm z * Real.sin (2 * θ))
          (fun z θ => -(Work.Elliptic.Gsing α (fun z θ => lm z * Real.sin (2 * θ)) z)
            * Real.sin (2 * θ))) z θ
        / Work.Construction.s2 θ
        = -2 * Work.Elliptic.Gbar α (fun z θ => lm z * Real.sin (2 * θ)) z - (1 / 5) * lm z := by
  intro z θ hz hθ hθ2
  have h := uop_witness α (fun z θ => lm z * Real.sin (2 * θ)) hα hL12 hFc hJ z θ hz hθ hθ2
  rw [h, fstar_radial_sin lm z]
  ring

end Work.FTS.EllSol.PkgK5.CexK5
