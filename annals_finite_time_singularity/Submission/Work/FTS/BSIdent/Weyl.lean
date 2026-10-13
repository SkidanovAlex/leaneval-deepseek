/-
# `Work.FTS.BSIdent.Weyl` — the identification via Weyl on the difference (route C)

This is the route the lead prescribed for audit §5 item 4 (`FTS_HARD_DESIGN.md` §(C), message of
2026-10-08 01:30): instead of *Biotsing–Savart inversion* (route A) or the *div-curl Liouville*
route (route B), apply the Weyl/Liouville pair lemma of `Work.FTS.PressureOn` to the difference

  `D := physVel (−physOmega α A B g C) · t − v`,

where `v` is the stream-function field of the reconstruction at time `t`.  The point of route C is
that it needs **neither** `Work.LWP.BiotSavartInverse` **nor** `Physical.DivCurlLiouville`, and
**no `C¹`-regularity of the ansatz field at the axis**: continuity and decay, together with the
*weak* (distributional) vanishing of `div D` and `curl D`, suffice.

## The axis obstacle (a Lean artefact, and why `v` is a parameter here)

`Work.Cyl.psiField ψ` is **discontinuous at the axis** whenever `ψ r z / r` has a nonzero limit:
`psiField` computes `−ψ/r − ∂_rψ` with Lean's `0/0 = 0`, whereas the continuous extension of the
field is `−2·lim_{r→0} ψ(r,z)/r` in the `e_z` direction.  For instance
`psiField (fun r z => r)` is `−2·e_z` off the axis and `−e_z` *at* the axis.  For the genuine
reconstruction the stream function vanishes only *linearly* at `θ = π/2` (`Φ ≈ c(z)cos θ`,
`FTS_HARD_DESIGN.md` §(C)), so `ψ/r → |z|·c(z) ≠ 0` and the Lean field really is discontinuous at
the axis; consequently the Weyl package cannot be stated for `Cyl.psiField (merPsi …)` itself.

This module therefore takes the field `v` at time `t` as a **parameter**, with the single
hypothesis that `v` agrees with `Cyl.psiField (merPsi … · t)` on `Uax` (which is the only set on
which the design's `hid` is claimed, and where the corrected field and the Lean field agree
pointwise).  The task of exhibiting such a `v` — the *continuous extension* of the stream-function
field, together with its decay and the two weak equations — is the analytic content of route C and
is recorded in `NOTES.md`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Curl
import Submission.Work.FTS.PressureOn.Defs

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

/-- **ROUTE C IN THE DESIGN'S SHAPE.**  The time-quantified version of `hid_of_weyl`, with the
corrected ansatz field `v` given as a family in time (agreeing pointwise with
`Cyl.psiField (merPsi … · t)` on `Uax`) and the Weyl package of the difference supplied for every
`t ∈ (0,T)`.  This is the statement the firing theorem `blowupAtTop_of_regPkg'` needs for its `hid`
slot: it avoids both the (false) `BiotSavartInverse`/`DivCurlLiouville` inputs and the
(unprovable, by the axis artefact of the module docstring) `C¹`-hypothesis on `Cyl.psiField`. -/
theorem hid_of_weyl' (hweyl : WeylPairPrinciple) {α : ℝ≥0} {A B : ℝ → ℝ}
    {g : ℝ → ℝ → ℝ → ℝ} {C : Physical.PhysClock} {Φ : Fam} {v : ℝ → R3 → R3}
    (hv : ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax, v t x
      = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x)
    (hcont : ∀ t ∈ Set.Ioo 0 C.T, Continuous (fun x =>
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t - v t x))
    (hdec : ∀ t ∈ Set.Ioo 0 C.T, Filter.Tendsto (fun x =>
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t - v t x)
      (Filter.cocompact R3) (nhds 0))
    (hdiv : ∀ t ∈ Set.Ioo 0 C.T, ∀ φ : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) →
      HasCompactSupport φ →
      ∫ x, inner ℝ (Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t - v t x)
        (gradient φ x) = 0)
    (hcurl : ∀ t ∈ Set.Ioo 0 C.T, ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) →
      HasCompactSupport ψ →
      ∫ x, inner ℝ (Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t - v t x)
        (FiniteTimeSingularity.vorticity ψ x) = 0) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x :=
  fun t ht => hid_of_weyl hweyl (hv t ht) (hcont t ht) (hdec t ht) (hdiv t ht) (hcurl t ht)

end Work.FTS.BSIdent
