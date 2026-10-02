import Mathlib
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.nfRead_ne_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The determinate coorientation reference of the normal fibre

This file fixes the *geometric* reference against which the two halves of the sharp statement
`Work.ThomBordism.canonicalGauss_isLocalDegreeClass` are to be stated.  See
`Submission/Work/ThomBordism/NOTE_CANONICAL_SHARP.md` §§3–5 for the analysis; the point of this
file is the observation that **the reference must be a *determinate* class**:

* the tree's existing fibre generator `Work.ThomBordism.nfGen` is `(relCohMap (nfRead E ND x))` of
  `Work.ThomBordism.stdThomGen`, and `stdThomGen` is `(Classical.choice (thomClass_trivial_point …)).τ`
  — a `Nonempty`-choice, hence **model-dependent** (`τ` and `-τ` are both admissible).  Statements
  *against* `nfGen` therefore flip with that choice, which is exactly why F2-sharp
  (`nfRes U = nfGen`) is not derivable *nor* refutable from the API
  (`NOTE_SESSION41_UNIVERSAL.md` §2);
* the *explicit* model class `Work.Thom.Mpun` of the punctured trivial bundle is built from the
  **explicit induction** `Work.Thom.Mn` (`Mn 0 B` is the *unique* preimage of the unit class under
  the bijection `relToAbs … sphZero`, and `Mn (n+1) B = step B n (Mn n B)`), so `Mpun n B` — being
  the unique preimage of `Mn n B` under the bijective `jMap` — is **determinate**: every two
  witnesses of its defining property are *provably equal*.  Reading it in the σ-corrected frame
  `Work.ThomBordism.Gauss.gframe` (which is, by `Work.ThomBordism.sigmaTelescope_gauss`, *the*
  canonical coorientation of the normal bundle, with no orientation choice left) gives the
  determinate coorientation reference `Work.ThomBordism.coorFibre`.

The two halves of the sharp statement are then `(A1)`: *every* local-degree class has fibre reading
`coorFibre` (the localisation chapter: (a) the local class of the collapse at the zero-section point
is the ambient generator, (b) capping with the collapse class localises to the fibre, (d) the model
contraction in `ℝ^8 × ℝ^k`), and `(A2)`: the fibre reading of the canonical class `gtdUWith … Ucan`
is `coorFibre` (the frame half).  Both are *determinate* statements, and their conjunction implies
`canonicalGauss_isLocalDegreeClass` (because `nfRes` is injective on the rank-one fibre module and
the local-degree class is unique).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

/-! ## The determinate standard generator of `H^k(ℝ^k, ℝ^k∖0)` -/

/-- **The determinate standard generator of `H^k(ℝ^k, ℝ^k∖0)`**: the image of the *explicit* model
class `Work.Thom.Mpun k PUnit` under the canonical identification `ℝ^k ≅ PUnit × ℝ^k`.

Unlike `Work.ThomBordism.stdThomGen` (which is `(Classical.choice (thomClass_trivial_point …)).τ`,
a choice of a `Nonempty`), this class is determined by the property "it is `Mn k` in the model pair",
and `Work.Thom.Mpun_spec` *is* that property, with injectivity of the model inclusion forcing the
value. -/
noncomputable def stdModelGen (k : ℕ) :
    Work.Thom.RelCoh ℤ k (Work.Tubular.Euc k) ({0}ᶜ : Set (Work.Tubular.Euc k)) :=
  (Work.Thom.relCohMap
    (⟨fun v : Work.Tubular.Euc k => (PUnit.unit, v),
      continuous_const.prodMk continuous_id⟩)
    ({0}ᶜ : Set (Work.Tubular.Euc k))
    (Work.Thom.Punct PUnit k)
    (fun v hv => hv)
    ℤ k).hom (Work.Thom.Mpun k PUnit)

/-! ## The coorientation reference of the normal fibre -/

/-- **The coorientation reference of the normal fibre** `ν_x` of an embedding `E`, at a normal datum
`ND`: the reading of the determinate standard generator `stdModelGen k` in the **σ-corrected
(coorientation) frame** `Work.ThomBordism.Gauss.gframe` of the normal bundle, i.e. the pullback of
`stdModelGen k` along `Work.ThomBordism.nfRead`.

This is the class that the two halves of `canonicalGauss_isLocalDegreeClass` are stated against. -/
noncomputable def coorFibre {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Work.Thom.RelCoh ℤ k ↥(nfSet E x) (nfPunct E x) :=
  (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
    ({0}ᶜ : Set (Work.Tubular.Euc k))
    (fun p hp => nfRead_ne_zero hk E ND x p hp) ℤ k).hom (stdModelGen k)

/-- The defining equation of `coorFibre`. -/
theorem coorFibre_eq {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    coorFibre hk E ND x
      = (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
          ({0}ᶜ : Set (Work.Tubular.Euc k))
          (fun p hp => nfRead_ne_zero hk E ND x p hp) ℤ k).hom (stdModelGen k) := rfl

/-- **The model class `Mpun k PUnit` is determinate**: it is the *unique* preimage of `Mn k PUnit`
under the pair inclusion `(PUnit × ℝ^k, PUnit × S^{k-1}) → (PUnit × ℝ^k, PUnit × (ℝ^k∖0))`, whose
induced map on relative cohomology is bijective (`Work.Thom.bijective_jMap`).  Every witness of the
defining property is therefore provably equal to it — in particular no `Nonempty`-choice is
involved. -/
theorem Mpun_eq_of_spec (k : ℕ)
    {w : Work.Thom.RelCoh ℤ k (PUnit × Work.Tubular.Euc k) (Work.Thom.Punct PUnit k)}
    (hw : (Work.Thom.relCohMap (ContinuousMap.id (PUnit × Work.Tubular.Euc k))
        (Work.Thom.Sph PUnit k) (Work.Thom.Punct PUnit k)
        (Work.Thom.mem_Sph_punct PUnit k) ℤ k).hom w = Work.Thom.Mn k PUnit) :
    w = Work.Thom.Mpun k PUnit :=
  (Work.Thom.bijective_jMap PUnit k k).1 (by rw [hw, Work.Thom.Mpun_spec])

end

end Work.ThomBordism
