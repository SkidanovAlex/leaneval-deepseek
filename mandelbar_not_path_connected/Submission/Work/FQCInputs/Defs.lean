/-
# `Work.FQCInputs` — the two explicit inputs of `Work.FQC`: phase normalisation and
# simplicity transfer

The area `Submission/Work/FQC/` (the quasiconformal deformation of the attracting Écalle
cylinder of a root-parabolic parameter, Hubbard–Schleicher §2 / MNS Theorem 3.2) consumes three
explicit inputs (its `NOTES.md` §4):

1. `Work.FQC.PetalInput` — the `g`-invariant fundamental domain and the Abel equation
   (home area: `Submission/Work/FatouCoordFix/`);
2. **MNS's phase normalisation** `saw ((fl.φa (phasePoint d fl)).re) = 1/2`
   (`Re φa (tap) ≡ 1/4 mod 1`) — a *choice* of the Fatou coordinate;
3. **`Work.FQC.SimpleTransfer`** — the transported parabolic point is again simple.

This area discharges (2) and states (3) in the form in which (2) needs it.

## (2) The phase normalisation

A Fatou coordinate is determined only up to an additive constant; the *antiholomorphic*
equivariance `φa ∘ g = conj ∘ φa + 1/2` forces that constant to be **real** (`φa ↦ φa + s`,
`s : ℝ`).  The Écalle height `Im φa` is unchanged by such a shift, but the phase `Re φa` — and
with it the phase at which the MNS twist `ℓ_t` is read off — moves by `s`.

This file defines the *renormalised flower* `shiftFlower s fl` (same petal `Pa`, same repelling
coordinate `Ψ`, Fatou coordinate `φa + s`) and proves

* `shiftFlower_φa`, `shiftFlower_Pa`, `shiftFlower_Ψ`, `shiftFlower_enters_Pa` — the transport of
  the flower fields;
* `phase_normalised` / `exists_phase_normalised` — for `s = 1/4 - (φa (phasePoint d fl)).re` the
  normalisation `saw ((fl'.φa (phasePoint d fl')).re) = 1/2` holds (uses `Work.FQC.saw_quarter`);
* `critHeightAt_shiftFlower` — **the height depends only on `Im φa`**: the critical Écalle
  height is exactly invariant under the shift;
* `petalShift` — the petal input transports, including the measurability of `Pg.indicator φa`
  (the indicator of an open set is measurable, and the shift of a measurable function is
  measurable).

## (3) The simplicity transfer

`Work.FQC.SimpleTransfer d fl P t` says: any homeomorphism `θ = principal (muQC d fl P t)` that
conjugates `T_c` to `T_{c₂}` carries the parabolic point `z₁` to a *simple* parabolic point of
`T_{c₂}` (`iteratedDeriv 2 (F c₂) (θ z₁) ≠ 0`).

This area states that input in the shift-invariant form needed by (2) — `SimpleTransferPetal d`,
see `SimpleTransfer.lean` — and provides the transfer lemmas a proof of it needs
(`deriv_F_transfer`, `not_eventuallyEq_id_F`, `exists_poly_F`).

The *basin-topology* route to it (a topological petal count via the components of the parabolic
basin) is **withdrawn**: every formulation of it has been refuted (`HasOnePetal` was vacuous at a
fixed point; the petals of a multiplicity-`3` germ need not lie in distinct components of the
punctured basin; the "horn gate" fails for non-real cubic coefficient).  The route now followed is
*continuation in the deformation parameter* `t` (`θ_t = principal (muQC d fl Pg t)`): the set
`N = {t | iteratedDeriv 2 (F (θ_t c)) (θ_t z₁) = 0}` misses `0`, is closed and — by the local
Hurwitz/minimum-modulus argument — open, hence empty.  See `NOTES.md` §6 and the lead's design
note `Submission/Work/NOTES_LEAD_mandelbar_simple.md` §§3, 5.
-/
import Mathlib
import Submission.Work.FQC.Flower
import Submission.Work.FQC.Petal
import Submission.Work.FQC.Ell
import Submission.Work.FQC.saw_add_one
import Submission.Work.FQC.saw_add_half

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 1. The real shift of the Fatou coordinate -/

/-- **The renormalised flower.**  A Fatou coordinate is determined up to a real additive
constant; `shiftFlower s fl` is the same flower with `φa` replaced by `φa + s` and every other
field (the petal `Pa`, the repelling coordinate `Ψ`, the entry field) unchanged.

The additive constant must be **real**: `s : ℝ`.  This is exactly what the antiholomorphic
equivariance `φa ∘ g = conj ∘ φa + 1/2` allows. -/
def shiftFlower {F g : ℂ → ℂ} {z₀ : ℂ} (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) : Work.FatouCoord.ParabolicFlower F g z₀ where
  Pa := fl.Pa
  φa := fun z => fl.φa z + (s : ℂ)
  Ψ := fl.Ψ
  isOpen_Pa := fl.isOpen_Pa
  isPreconnected_Pa := fl.isPreconnected_Pa
  z₀_not_mem := fl.z₀_not_mem
  mapsTo_Pa := fl.mapsTo_Pa
  tendsto_Pa := fl.tendsto_Pa
  enters_Pa := fl.enters_Pa
  φa_fatou := by
    have hdiff : DifferentiableOn ℂ (fun z => fl.φa z + (s : ℂ)) fl.Pa :=
      fl.φa_fatou.1.2.1.add_const _
    refine ⟨⟨fl.φa_fatou.1.1, hdiff, ?_⟩, ?_⟩
    · intro z hz
      show fl.φa (g z) + (s : ℂ) = star (fl.φa z + (s : ℂ)) + 1 / 2
      have hs : star ((s : ℝ) : ℂ) = (s : ℂ) := by
        apply Complex.ext <;> simp
      rw [fl.φa_fatou.1.2.2 z hz, star_add, hs]
      ring
    · intro z hz z' hz' h
      refine fl.φa_fatou.2 hz hz' ?_
      have := congrArg (fun w : ℂ => w - (s : ℂ)) h
      simpa using this
  Ψ_diff := fl.Ψ_diff
  Ψ_shift := fl.Ψ_shift
  Ψ_anti := fl.Ψ_anti
  Ψ_small := fl.Ψ_small
  Ψ_inj := fl.Ψ_inj
  Ψ_ends := fl.Ψ_ends
  cover := fl.cover

@[simp] theorem shiftFlower_Pa {F g : ℂ → ℂ} {z₀ : ℂ} (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) :
    (shiftFlower s fl).Pa = fl.Pa := rfl

@[simp] theorem shiftFlower_φa {F g : ℂ → ℂ} {z₀ : ℂ} (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) :
    (shiftFlower s fl).φa = fun z => fl.φa z + (s : ℂ) := rfl

@[simp] theorem shiftFlower_φa_apply {F g : ℂ → ℂ} {z₀ : ℂ} (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) (z : ℂ) :
    (shiftFlower s fl).φa z = fl.φa z + (s : ℂ) := rfl

@[simp] theorem shiftFlower_Ψ {F g : ℂ → ℂ} {z₀ : ℂ} (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) :
    (shiftFlower s fl).Ψ = fl.Ψ := rfl

@[simp] theorem shiftFlower_enters_Pa {F g : ℂ → ℂ} {z₀ : ℂ} (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) :
    (shiftFlower s fl).enters_Pa = fl.enters_Pa := rfl

@[simp] theorem shiftFlower_mapsTo_Pa {F g : ℂ → ℂ} {z₀ : ℂ} (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) :
    (shiftFlower s fl).mapsTo_Pa = fl.mapsTo_Pa := rfl

@[simp] theorem shiftFlower_tendsto_Pa {F g : ℂ → ℂ} {z₀ : ℂ} (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) :
    (shiftFlower s fl).tendsto_Pa = fl.tendsto_Pa := rfl

/-- The iterated shift: shifting by `s` then by `t` is shifting by `s + t` on the values of
`φa`. -/
theorem shiftFlower_shiftFlower {F g : ℂ → ℂ} {z₀ : ℂ} (s t : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) :
    (shiftFlower t (shiftFlower s fl)).φa = (shiftFlower (s + t) fl).φa := by
  funext z
  simp only [shiftFlower_φa_apply]
  push_cast
  ring

/-! ## 2. The phase at the tap point

`Work.FQC.phasePoint d fl = (F c)^[Nat.find fl.enters_Pa] c` is the first point of the critical
orbit that lies in the petal `fl.Pa`; the MNS twist `ℓ_t` is read off at its phase
`Re (φa (phasePoint d fl))`.  Because the shift leaves `Pa` and `enters_Pa` untouched, the tap
point is *the same point* for the shifted flower. -/

theorem phasePoint_shiftFlower {c : ℂ} (d : RootParabolic c) (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    Work.FQC.phasePoint d (shiftFlower s fl) = Work.FQC.phasePoint d fl := rfl

/-- **The phase shift that normalises MNS's phase.**  `s = 1/4 - Re (φa (tap))`. -/
def phaseShift {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) : ℝ :=
  1 / 4 - (fl.φa (Work.FQC.phasePoint d fl)).re

/-- **The phase normalisation.**  For the shift `s = phaseShift d fl` the MNS phase of the tap
point is exactly `1/4`, so that `saw` takes the value `1/2` there.

This is MNS's normalisation (`Re φa (tap) ≡ 1/4 mod 1`) — *a choice of the Fatou coordinate*,
realised by the real additive constant `1/4 - Re φa (tap)`. -/
theorem phase_normalised {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    Work.FQC.saw (((shiftFlower (phaseShift d fl) fl).φa
      (Work.FQC.phasePoint d (shiftFlower (phaseShift d fl) fl))).re) = 1 / 2 := by
  have hpt : Work.FQC.phasePoint d (shiftFlower (phaseShift d fl) fl)
      = Work.FQC.phasePoint d fl := rfl
  rw [hpt, shiftFlower_φa_apply]
  have hre : (fl.φa (Work.FQC.phasePoint d fl) + ((phaseShift d fl : ℝ) : ℂ)).re = 1 / 4 := by
    simp only [Complex.add_re, Complex.ofReal_re, phaseShift]
    ring
  rw [hre, Work.FQC.saw_quarter]

/-- Existence form of `phase_normalised`: every flower admits a real shift making MNS's phase
normalisation hold. -/
theorem exists_phase_normalised {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    ∃ s : ℝ, Work.FQC.saw
      (((shiftFlower s fl).φa (Work.FQC.phasePoint d (shiftFlower s fl))).re) = 1 / 2 :=
  ⟨phaseShift d fl, phase_normalised d fl⟩

/-! ## 3. The height is invariant under the shift

The Écalle data of the shifted flower: the petal and the entry field are the same, the Fatou
coordinate is `φa + s`.  Consequently the first entry time and hence the critical Écalle height
are *unchanged*. -/

@[simp] theorem EcalleData_ofFlower_shiftFlower_Pa {c : ℂ} (d : RootParabolic c) (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    (Work.FQC.EcalleData.ofFlower d (shiftFlower s fl)).Pa = fl.Pa := rfl

@[simp] theorem EcalleData_ofFlower_shiftFlower_φa {c : ℂ} (d : RootParabolic c) (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    (Work.FQC.EcalleData.ofFlower d (shiftFlower s fl)).φa = fun z => fl.φa z + (s : ℂ) := rfl

/-- The first entry time of the critical orbit into the petal is unchanged by the shift. -/
theorem nEnter_shiftFlower {c : ℂ} (d : RootParabolic c) (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    Work.FQC.nEnter (Work.FQC.EcalleData.ofFlower d (shiftFlower s fl))
      = Work.FQC.nEnter (Work.FQC.EcalleData.ofFlower d fl) := rfl

/-- The tap point of the shifted Écalle data is the tap point of the original flower. -/
theorem tapPoint_shiftFlower {c : ℂ} (d : RootParabolic c) (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    Work.FQC.tapPoint d (Work.FQC.EcalleData.ofFlower d (shiftFlower s fl))
      = Work.FQC.tapPoint d (Work.FQC.EcalleData.ofFlower d fl) := rfl

/-- **The height depends only on `Im φa`.**  Shifting the Fatou coordinate by a real constant
does not change the critical Écalle height. -/
theorem critHeightAt_shiftFlower {c : ℂ} (d : RootParabolic c) (s : ℝ)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d (shiftFlower s fl))
      = Work.FQC.critHeightAt d (Work.FQC.EcalleData.ofFlower d fl) := by
  rw [Work.FQC.critHeightAt_eq_im, Work.FQC.critHeightAt_eq_im, tapPoint_shiftFlower]
  show (fl.φa (Work.FQC.tapPoint d (Work.FQC.EcalleData.ofFlower d fl)) + (s : ℂ)).im
      = (fl.φa (Work.FQC.tapPoint d (Work.FQC.EcalleData.ofFlower d fl))).im
  simp

/-! ## 4. The petal input transports along the shift

`Work.FQC.PetalInput d fl` records the `g`-invariant fundamental domain `Pg` together with the
Abel equation and the measurability of `Pg.indicator fl.φa`.  All of it transports to the
shifted flower; only measurability needs an argument (`Pg` is open, hence its indicator is
measurable, and the shifted indicator is `Pg.indicator φa` plus a real multiple of it). -/

theorem measurable_indicator_add_const {P : Set ℂ} (hP : IsOpen P) {φ : ℂ → ℂ}
    (hφ : Measurable (P.indicator φ)) (s : ℝ) :
    Measurable (P.indicator (fun z => φ z + (s : ℂ))) := by
  have h1 : P.indicator (fun z => φ z + (s : ℂ))
      = fun z => P.indicator φ z + ((s : ℝ) : ℂ) * P.indicator (fun _ => (1 : ℂ)) z := by
    funext z
    by_cases hz : z ∈ P <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [h1]
  exact hφ.add (measurable_const.mul (measurable_const.indicator hP.measurableSet))

/-- **The petal input of the shifted flower.**  The fundamental domain `Pg`, its `g`-invariance,
the no-early-return condition and the entry condition are literally unchanged; the Abel equation
transports because the additive constants on the two sides cancel; and the measurability of
`Pg.indicator φa` transports by `measurable_indicator_add_const`. -/
def petalShift {c : ℂ} {d : RootParabolic c}
    {fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁}
    (hfl : Work.FQC.PetalInput d fl) (s : ℝ) : Work.FQC.PetalInput d (shiftFlower s fl) where
  Pg := hfl.Pg
  Pg_sub := hfl.Pg_sub
  Pg_open := hfl.Pg_open
  Pg_preconnected := hfl.Pg_preconnected
  mapsTo_g_Pg := hfl.mapsTo_g_Pg
  no_early := hfl.no_early
  indicator_measurable := measurable_indicator_add_const hfl.Pg_open hfl.indicator_measurable s
  φa_shift := by
    intro z hz
    have h := hfl.φa_shift z hz
    show fl.φa ((F c) z) + (s : ℂ) = (fl.φa z + (s : ℂ)) + 1
    rw [h]
    ring
  enters_Pg := hfl.enters_Pg

@[simp] theorem petalShift_Pg {c : ℂ} {d : RootParabolic c}
    {fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁}
    (hfl : Work.FQC.PetalInput d fl) (s : ℝ) : (petalShift hfl s).Pg = hfl.Pg := rfl

@[simp] theorem petalShift_enters_Pg {c : ℂ} {d : RootParabolic c}
    {fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁}
    (hfl : Work.FQC.PetalInput d fl) (s : ℝ) :
    (petalShift hfl s).enters_Pg = hfl.enters_Pg := rfl

/-! ## 5. Simplicity -/

/-- **A simple parabolic germ**: fixed point with multiplier `1` and nonvanishing second
derivative — the analytic form of "multiplicity `2`", the condition under which the deformation of
`Work.FQC` transports the parabolic point (see `SimpleTransfer.lean`). -/
def IsSimpleParabolicGerm (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  f z₀ = z₀ ∧ deriv f z₀ = 1 ∧ iteratedDeriv 2 f z₀ ≠ 0

end Work.FQCInputs

end
