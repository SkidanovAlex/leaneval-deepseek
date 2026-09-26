import Mathlib
import Submission.Work.Drive.Final.tls_defs
import Submission.Work.Drive.Mono.fibreMax_continuous
import Submission.Work.Drive.Mono.exists_discParam_of_convex

/-!
# The trough of a level of the tilted sweep: the fibre model

Vocabulary for `Work.Drive.Final.tls_trough_disc`.

Write `p := ⟪v,·⟫`, `q := ℓ`, `π := (p,q)`, `cl B` for the closure of `PBox s c σ` and
`Q = π '' cl B` for its shadow.  The kernel of `π` is a line, `fibreDir v ℓ` spans it, and
`sectionL v ℓ hv hℓv hℓne` is a linear section of `π`.  Then every point of `cl B` over `x ∈ Q`
is `sectionL x + t • fibreDir` with `t` in the interval `[htl x, hth x]` cut out by the three box
constraints (`loB`, `hiB`); `Phi` is the corresponding parametrisation of `cl B` over its shadow.

The **arc** `arc = Q ∩ ∂R₀` (where `R₀ = chamberR` is the chamber cut out by the slab and the wall)
is the union of the three pieces `Sp`, `Sm`, `Ss`; the two `90`-degree rotations `rotR`, `rotL`
flatten it into the wall line `q = lam`, giving `Aflat`, inverted by `unflat`.  The **band**
`band` is the planar model of the trough and `bandToR3` is the corresponding map back into `ℝ³`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final.Trough

noncomputable section

/-! ## The pair of functionals and the shadow -/

/-- The pair `(⟪v,·⟫, ℓ)` as a linear map to the plane `ℝ × ℝ`. -/
def pairLM (v : R3) (ℓ : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] (ℝ × ℝ) := (innerSL ℝ v).prod ℓ

/-- The pair `(⟪v,·⟫, ℓ)` as a continuous linear map to the plane `ℝ × ℝ`. -/
def pair (v : R3) (ℓ : R3 →L[ℝ] ℝ) : R3 →L[ℝ] (ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap (pairLM v ℓ)

@[simp] theorem pairLM_apply (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) :
    pairLM v ℓ y = (inner ℝ v y, ℓ y) := rfl

@[simp] theorem pair_apply (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) :
    pair v ℓ y = (inner ℝ v y, ℓ y) := rfl

/-- The closure of Pardon's box, as the set cut out by the three box constraints. -/
def cbox (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  {y : R3 | ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s}

/-- The **shadow** of the closed box under `pair v ℓ`. -/
def shadow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ) :
    Set (ℝ × ℝ) := pair v ℓ '' cbox s c σ

theorem mem_shadow {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {ℓ : R3 →L[ℝ] ℝ}
    {x : ℝ × ℝ} : x ∈ shadow s c σ v ℓ ↔ ∃ y ∈ cbox s c σ, pair v ℓ y = x := Iff.rfl

/-! ## The transverse direction -/

/-- A non-zero vector in the kernel of `pair v ℓ`, chosen once and for all (it is `0` in the
degenerate cases where the kernel is trivial, which never happens under the hypotheses). -/
def fibreDir (v : R3) (ℓ : R3 →L[ℝ] ℝ) : R3 := by
  classical
  exact if h : ∃ w : R3, w ≠ 0 ∧ pair v ℓ w = 0 then Classical.choose h else 0

/-- A linear section of the pair map (it is `0` in the degenerate cases where the pair is not
surjective, which never happens under the hypotheses). -/
def sectionL (v : R3) (ℓ : R3 →L[ℝ] ℝ) : (ℝ × ℝ) →ₗ[ℝ] R3 := by
  classical
  exact if h : ∃ g : (ℝ × ℝ) →ₗ[ℝ] R3, ∀ x, pair v ℓ (g x) = x then Classical.choose h else 0

/-! ## The box parameters and the height functions of the fibres -/

/-- The half side length of the box in the `σ i`-coordinate. -/
def halfLen (s : ℝ) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : ℝ := Submission.boxSide i * s

/-- The coefficient of `t` in the `i`-th box constraint. -/
def kernCoef (v : R3) (ℓ : R3 →L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : ℝ :=
  fibreDir v ℓ (σ i)

/-- The constant term of the `i`-th box constraint along the fibre over `x`. -/
def baseCoord (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (i : Fin 3) (x : ℝ × ℝ) : ℝ := sectionL v ℓ x (σ i) - c (σ i)

/-- The lower bound on the fibre parameter coming from the `i`-th constraint. -/
def loB (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ) (i : Fin 3)
    (x : ℝ × ℝ) : ℝ :=
  if 0 < kernCoef v ℓ σ i then
    (-(halfLen s σ i) - baseCoord s c σ v ℓ i x) / kernCoef v ℓ σ i
  else (halfLen s σ i - baseCoord s c σ v ℓ i x) / kernCoef v ℓ σ i

/-- The upper bound on the fibre parameter coming from the `i`-th constraint. -/
def hiB (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ) (i : Fin 3)
    (x : ℝ × ℝ) : ℝ :=
  if 0 < kernCoef v ℓ σ i then
    (halfLen s σ i - baseCoord s c σ v ℓ i x) / kernCoef v ℓ σ i
  else (-(halfLen s σ i) - baseCoord s c σ v ℓ i x) / kernCoef v ℓ σ i

/-- The index set of the box constraints that involve the fibre parameter. -/
def nzIdx (v : R3) (ℓ : R3 →L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)) : Finset (Fin 3) :=
  Finset.univ.filter (fun i : Fin 3 => kernCoef v ℓ σ i ≠ 0)

/-- The minimal value of the fibre parameter (the lower end of the fibre). -/
def htl (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (x : ℝ × ℝ) : ℝ :=
  if h : (nzIdx v ℓ σ).Nonempty then
    (nzIdx v ℓ σ).sup' h (fun i => loB s c σ v ℓ i x) else 0

/-- The maximal value of the fibre parameter (the upper end of the fibre). -/
def hth (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (x : ℝ × ℝ) : ℝ :=
  if h : (nzIdx v ℓ σ).Nonempty then
    (nzIdx v ℓ σ).inf' h (fun i => hiB s c σ v ℓ i x) else 0

/-- **The parametrisation of the closed box over its shadow**: the point of the fibre over `x` at
relative height `τ`. -/
def Phi (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ)
    (x : ℝ × ℝ) (τ : ℝ) : R3 :=
  sectionL v ℓ x +
    ((1 - τ) * htl s c σ v ℓ x + τ * hth s c σ v ℓ x) • fibreDir v ℓ

/-! ## The chamber, the arc and its pieces -/

/-- The centre of the tilted slab. -/
def slabA (c v : R3) (u : ℝ) : ℝ := inner ℝ v c + u

/-- The chamber `{|p - a| ≤ h} ∩ {q ≤ lam}` of the `(p,q)`-plane. -/
def chamberR (a h lam : ℝ) : Set (ℝ × ℝ) := {x : ℝ × ℝ | |x.1 - a| ≤ h ∧ x.2 ≤ lam}

/-- The boundary of the chamber. -/
def bdryR (a h lam : ℝ) : Set (ℝ × ℝ) :=
  {x : ℝ × ℝ | |x.1 - a| = h ∧ x.2 ≤ lam} ∪ {x : ℝ × ℝ | |x.1 - a| ≤ h ∧ x.2 = lam}

/-- **The arc**: the shadow of the trough in the `(p,q)`-plane. -/
def arc (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set (ℝ × ℝ) :=
  shadow s c σ v ℓ ∩ bdryR (slabA c v u) h lam

/-- The upper slab face piece of the arc. -/
def Sp (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set (ℝ × ℝ) :=
  shadow s c σ v ℓ ∩ {x : ℝ × ℝ | x.1 = slabA c v u + h ∧ x.2 ≤ lam}

/-- The lower slab face piece of the arc. -/
def Sm (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set (ℝ × ℝ) :=
  shadow s c σ v ℓ ∩ {x : ℝ × ℝ | x.1 = slabA c v u - h ∧ x.2 ≤ lam}

/-- The wall piece of the arc. -/
def Ss (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set (ℝ × ℝ) :=
  shadow s c σ v ℓ ∩ {x : ℝ × ℝ | x.2 = lam ∧ |x.1 - slabA c v u| ≤ h}

/-! ## The flattening -/

/-- The `90`-degree rotation of the plane about the upper corner `(a+h, lam)`. -/
def rotR (a h lam : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (a + h - (x.2 - lam), lam + (x.1 - (a + h)))

/-- The `90`-degree rotation of the plane about the lower corner `(a-h, lam)`. -/
def rotL (a h lam : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (a - h + (x.2 - lam), lam - (x.1 - (a - h)))

/-- The flattened arc: the arc rotated into the wall line `q = lam`. -/
def Aflat (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set (ℝ × ℝ) :=
  rotR (slabA c v u) h lam '' Sp s c σ u h lam v ℓ ∪ Ss s c σ u h lam v ℓ ∪
    rotL (slabA c v u) h lam '' Sm s c σ u h lam v ℓ

/-- The unflattening of a point `s` of the flattened line: the point of the arc whose flattening
image has first coordinate `s`. -/
def unflat (a h lam : ℝ) (s : ℝ) : ℝ × ℝ :=
  if a + h ≤ s then (a + h, lam - (s - (a + h)))
  else if s ≤ a - h then (a - h, lam + (s - (a - h)))
  else (s, lam)

/-- **The band**: the flattened model of the trough, in the `(p, ζ)`-plane of the wall. -/
def band (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set (ℝ × ℝ) :=
  {w : ℝ × ℝ | (w.1, lam) ∈ Aflat s c σ u h lam v ℓ ∧
    htl s c σ v ℓ (unflat (slabA c v u) h lam w.1) ≤ w.2 ∧
    w.2 ≤ hth s c σ v ℓ (unflat (slabA c v u) h lam w.1)}

/-- The point of the box corresponding to a point of the band. -/
def bandToR3 (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) (w : ℝ × ℝ) : R3 :=
  sectionL v ℓ (unflat (slabA c v u) h lam w.1) + w.2 • fibreDir v ℓ

end

end Work.Drive.Final.Trough
