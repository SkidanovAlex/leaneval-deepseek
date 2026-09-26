import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.tiltedShadowDefs

/-!
# The fibre model of a level of the tilted sweep: vocabulary

`Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam` is Pardon's open box with the closed tilted
slab `{|⟪v,·⟫ - (⟪v,c⟫ + u)| ≤ h}` cut away on the side `{ℓ < lam}`.  Put

* `p := ⟪v,·⟫`, `q := ℓ`, `π := (p, q) : ℝ³ → ℝ × ℝ` (`levPair`), and let `ζ : ℝ³ →L[ℝ] ℝ` be a
  linear functional with `ker p ∩ ker q ∩ ker ζ = {0}` — i.e. `(π, ζ)` is a linear coordinate
  system on `ℝ³` (`HasTrivKernel`);
* `ClBox s c σ = closure (PBox s c σ)`, and `shadow v ℓ A = π '' A` (`boxShadow` for the closed
  box, the compact convex *shadow* `W` of the box);
* `fMax ζ ... X` / `fMin ζ ... X` are the maximal and minimal values of `ζ` on the fibre of the
  closed box over `X` (`= Work.Drive.Mono.fibreMax`/`fibreMin` at `X = closure (PBox)`).

Because `p` and `q` are linearly independent (`ℓ v = 0`, `ℓ ≠ 0`, `v ≠ 0`), the fibres of `π` are
lines and the fibre over `X` of the closed box is a nonempty compact interval *in the `ζ`
coordinate*, namely `[fMin X, fMax X]` over the shadow.  These are the height functions of the
"solid cylinder over the shadow"; the level's removed set is the solid over the planar shadow
chamber, cut out by the slab and the wall.

This file contains only definitions and elementary bookkeeping; the geometric content lives in the
sibling files of this directory.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono.FiberModel

noncomputable section

/-- The level's pair `(p, q) = (⟪v,·⟫, ℓ)` of linear functionals, read as a map to `ℝ × ℝ`. -/
def levPair (v : R3) (ℓ : R3 →L[ℝ] ℝ) : R3 → ℝ × ℝ := fun y => (inner ℝ v y, ℓ y)

/-- The level's pair of functionals as a continuous linear map. -/
def levPairCLM (v : R3) (ℓ : R3 →L[ℝ] ℝ) : R3 →L[ℝ] (ℝ × ℝ) :=
  (innerSL ℝ v).prod ℓ

theorem levPairCLM_apply (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) :
    levPairCLM v ℓ y = (inner ℝ v y, ℓ y) := rfl

/-- The pair `(⟪v,·⟫, ℓ)` as a plain function, the form used for the planar image. -/
theorem levPair_eq_levPairCLM (v : R3) (ℓ : R3 →L[ℝ] ℝ) :
    levPair v ℓ = levPairCLM v ℓ := rfl

/-- The shadow of a set under the level's pair of functionals. -/
def shadow (v : R3) (ℓ : R3 →L[ℝ] ℝ) (A : Set R3) : Set (ℝ × ℝ) := levPair v ℓ '' A

/-- The closed box of the sweep. -/
def ClBox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 := closure (Submission.PBox s c σ)

/-- The shadow `W` of the *closed* box: a compact convex set with nonempty interior. -/
def boxShadow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ) : Set (ℝ × ℝ) :=
  shadow v ℓ (ClBox s c σ)

/-- The slab parameter of the tilted sweep: `a = ⟪v,c⟫ + u`. -/
def slabA (u : ℝ) (c v : R3) : ℝ := inner ℝ v c + u

/-- `ζ` is transverse to the fibres of `π = (p,q)`: `(π, ζ)` is a linear coordinate system. -/
def HasTrivKernel (v : R3) (ℓ ζ : R3 →L[ℝ] ℝ) : Prop :=
  ∀ y : R3, inner ℝ v y = 0 → ℓ y = 0 → ζ y = 0 → y = 0

/-- The maximal value of `ζ` on the fibre of the closed box over `X`. -/
def fMax (ζ : R3 →L[ℝ] ℝ) (v : R3) (ℓ : R3 →L[ℝ] ℝ) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (X : ℝ × ℝ) : ℝ :=
  Work.Drive.Mono.fibreMax ζ (innerSL ℝ v) ℓ (ClBox s c σ) X

/-- The minimal value of `ζ` on the fibre of the closed box over `X`. -/
def fMin (ζ : R3 →L[ℝ] ℝ) (v : R3) (ℓ : R3 →L[ℝ] ℝ) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (X : ℝ × ℝ) : ℝ :=
  Work.Drive.Mono.fibreMin ζ (innerSL ℝ v) ℓ (ClBox s c σ) X

/-- The upper `ζ`-slice of the closed box over a plane point. -/
def fibre (v : R3) (ℓ : R3 →L[ℝ] ℝ) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (X : ℝ × ℝ) : Set R3 :=
  {y ∈ ClBox s c σ | levPair v ℓ y = X}

/-- The planar shadow chamber of the swept level: the plane set over which the removed set lives. -/
def chamber (a h lam : ℝ) : Set (ℝ × ℝ) := {X : ℝ × ℝ | |X.1 - a| > h ∨ lam ≤ X.2}

/-- The closed planar shadow chamber. -/
def chamberCl (a h lam : ℝ) : Set (ℝ × ℝ) := {X : ℝ × ℝ | h ≤ |X.1 - a| ∨ lam ≤ X.2}

/-- The planar image of the removed level set (the `Z` of the statement). -/
def planarImage (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set (ℝ × ℝ) :=
  shadow v ℓ (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)

/-- The "solid" whose frontier is the level's frontier: the closed box over the closure of the
planar image, in `ζ`-coordinates. -/
def solid (ζ : R3 →L[ℝ] ℝ) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {P : (ℝ × ℝ) × ℝ |
    P.1 ∈ closure (planarImage s c σ u v h ℓ lam) ∧
      fMin ζ v ℓ s c σ P.1 ≤ P.2 ∧ P.2 ≤ fMax ζ v ℓ s c σ P.1}

/-- The hypograph region of the height `h = fMax - fMin` over a plane set `K`. -/
def hypograph (K : Set (ℝ × ℝ)) (hh : ℝ × ℝ → ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {P : (ℝ × ℝ) × ℝ | P.1 ∈ K ∧ 0 ≤ P.2 ∧ P.2 ≤ hh P.1}


/-! ## The planar disc hypothesis and the pieces of the shadow chamber -/

/-- `K` is a plane disc: the image of the closed unit disc under an injective continuous map whose
boundary circle maps onto the frontier of `K`. -/
def IsPlaneDisc (K : Set (ℝ × ℝ)) : Prop :=
  ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℝ × ℝ), Function.Injective e ∧ Set.range e = K ∧
    Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K

/-- The `+` wing of the shadow chamber: the closure of the part of the shadow beyond the `+` slab
face. -/
def wingPlus (W : Set (ℝ × ℝ)) (a h : ℝ) : Set (ℝ × ℝ) :=
  closure (interior W ∩ {X : ℝ × ℝ | a + h < X.1})

/-- The `-` wing of the shadow chamber. -/
def wingMinus (W : Set (ℝ × ℝ)) (a h : ℝ) : Set (ℝ × ℝ) :=
  closure (interior W ∩ {X : ℝ × ℝ | X.1 < a - h})

/-- The level cap of the shadow chamber. -/
def cap0 (W : Set (ℝ × ℝ)) (lam : ℝ) : Set (ℝ × ℝ) :=
  closure (interior W ∩ {X : ℝ × ℝ | lam < X.2})

/-- The three pieces of the shadow chamber, as the pair of wings together with the level cap. -/
def chamberPieces (W : Set (ℝ × ℝ)) (a h lam : ℝ) : Set (ℝ × ℝ) :=
  wingPlus W a h ∪ wingMinus W a h ∪ cap0 W lam

end

end Work.Drive.Mono.FiberModel
