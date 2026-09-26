import Mathlib
import Submission.Work.Drive.Final.GoodSweepData
import Submission.Work.Drive.Mono.TiltedTraceData

/-!
# The dent datum: the local deformation that resolves one event

This is the second piece of the vocabulary of field (L) (the lead's `01:50` directive), the one
`Work.Drive.Final.dent_regular` needs before it can even be stated.

At an event `p` (a critical point of the sweep height, `Work.Drive.Final.IsEvent`) the level region of
the tilted sweep changes by a *neck*: locally the region `X λ` drops a piece of the slab as `λ` passes
the event's value.  The design resolves the event by pushing the region along a **dent**
`Ψ z = z ± a'·χ(‖z − centre‖/r)·d`: a bump of depth `a'`, supported in the ball `B(centre, r)` around
the event's image, cut off by `χ`, and pushed in the direction `d`.

This file fixes the *data* of such a dent (`DentDatum`) and the deformation it induces
(`dentDeform`).  The design's per-type choice of `d` — `n` at an interior event, the orthogonal
projection of `n` onto the face at a one-constraint event, `±v × e_{σi}` at a face/edge event, and
`±e_{σ2}` in the remaining case — is *not* fixed here: `DentDatum` is data, and the statement that
*good* data exist (with `d` tangent to every face through the ball and `⟪n,d⟫ > 0`) is the content
of the lead's `push` field and of the per-type case analysis, to be supplied by the consumer.

## What the fields say

* `χ` is the cutoff: continuous, `χ 0 = 1`, and `χ = 0` beyond `1`, so that `dentDeform` is the
  identity outside `B(centre, r)`;
* `centre` is the image of the event under the parametrisation (`Work.BoxShrink.Pinch.par ψ p`), and
  the ball `B(centre, r)` lies in the open box (`support_subset`), so the dent never reaches the box
  sphere — the region's frontier inside the ball consists only of the slab faces and the wall;
* `d` is **tangent to every face through the ball**: to the two slab faces, whose common normal is
  `v` (`d_orth_v`), and to the wall, whose normal is the level functional `ℓ` (`d_orth_ℓ` is
  *not* required: the push must move points *across* the wall, so `d` must have a nonzero
  `ℓ`-component); the direction of the push is recorded by `push_pos`;
* the depth `a'` is positive.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

noncomputable section

variable {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
  {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}

/-- **The deformation induced by a dent**: at the point `z`, move by `a'·χ(‖z − centre‖/r)` in the
direction `d`.  The sign of the push is carried by `d` (a dent *out* and a dent *in* are the two
choices `±`). -/
def dentDeform (χ : ℝ → ℝ) (centre d : R3) (r a' : ℝ) (z : R3) : R3 :=
  z + (a' * χ (‖z - centre‖ / r)) • d

/-- **The datum of one dent** at an event of a good tilted sweep.  See the module docstring for what
each field means and which parts of the design's per-type analysis are deliberately left to the
consumer. -/
structure DentDatum (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) where
  /-- the cutoff function of the dent -/
  χ : ℝ → ℝ
  /-- the cutoff is continuous -/
  χ_cont : Continuous χ
  /-- the cutoff is `1` at the centre of the dent -/
  χ_zero_apply : χ 0 = 1
  /-- the cutoff vanishes beyond radius `1` -/
  χ_eq_zero : ∀ t : ℝ, 1 ≤ t → χ t = 0
  /-- the cutoff is bounded by `1` (the design's cutoff has this normalization) -/
  χ_le_one : ∀ t : ℝ, |χ t| ≤ 1
  /-- **the cutoff is `1` on a neighbourhood of the centre** — the *core* of the dent.  This is how
  the design's cutoff is chosen; it is a datum property, and it is what makes the transport clause of
  `dent_regular` both statable and true: on the ball `‖z − centre‖ ≤ ε·r` the deformation is exactly
  the translation by `a'•d`, on a neighbourhood of every point of that ball, so frontiers correspond
  (see AUDIT §23.12). -/
  χ_eq_one_near : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → χ t = 1
  /-- the cutoff is differentiable -/
  χ_diff : Differentiable ℝ χ
  /-- the Lipschitz constant of the cutoff: the design's `‖χ'‖` -/
  κ : ℝ
  /-- the Lipschitz constant is positive -/
  κ_pos : 0 < κ
  /-- the derivative of the cutoff is bounded by `κ` (this is what makes the Lipschitz
  constant `κ`, and hence the design's threshold `a'' ≤ κ r / (2 ‖χ'‖)`), a referent) -/
  χ_deriv_bound : ∀ t : ℝ, |deriv χ t| ≤ κ
  /-- the parameter-plane point of the event -/
  p : ℝ × ℝ
  /-- the event is an event of the sweep -/
  isEvent : IsEvent ψ s c σ u v h ℓ p
  /-- the (physical) centre of the dent, the image of the event -/
  centre : R3
  /-- the centre is the image of the event under the parametrisation -/
  centre_eq : centre = Work.BoxShrink.Pinch.par ψ p
  /-- the radius of the dent -/
  r : ℝ
  /-- the radius is positive -/
  r_pos : 0 < r
  /-- the dent is supported in the open box -/
  support_subset : ∀ z : R3, ‖z - centre‖ ≤ r → z ∈ Submission.PBox s c σ
  /-- the direction of the push -/
  d : R3
  /-- `d` is a *direction*: unit -/
  d_norm : ‖d‖ = 1
  /-- `d` is tangent to the two slab faces (their common normal is `v`) -/
  d_orth_v : inner ℝ v d = 0
  /-- the push crosses the wall: `d` has a positive component along the level functional `ℓ` -/
  push_pos : 0 < ℓ d
  /-- the depth of the dent -/
  a' : ℝ
  /-- the depth is positive -/
  a'_pos : 0 < a'
  /-- **the room of the box around the dent**: the radius `r + δ` of a ball around the centre which
  still lies in the open box.  This is the box margin that `dent_box_margin` consumes as `hsupp`; it
  is a datum property (the design's smallness threshold `a'' ≤ κ r / (2‖χ'‖)` is what lets the depth
  be chosen inside it), and with `a'_le_δ` it makes `hsupp` a fact about the datum rather than an
  unprovable obligation — no radius-`r` support bound alone can give it, since `a'` is a free field. -/
  δ : ℝ
  /-- the room is positive -/
  δ_pos : 0 < δ
  /-- the ball of radius `r + δ` around the centre lies in the open box -/
  δ_subset : ∀ z : R3, ‖z - centre‖ ≤ r + δ → z ∈ Submission.PBox s c σ
  /-- the depth is bounded by the room of the box -/
  a'_le_δ : a' ≤ δ

/-- The deformation of a `DentDatum`, as a function of the physical space. -/
def DentDatum.deform (D : DentDatum ψ s c σ u v h R ℓ) : R3 → R3 :=
  dentDeform D.χ D.centre D.d D.r D.a'


/-! ## The two algebraic facts `dent_regular` consumes

The dent deforms the *space*, so every clause of `dent_regular` has to be read on the right object:
the level **surface** of the sweep (its frontier), whose two constraints are the slab
`{|⟪v,·⟫ − a| ≤ h}` and the wall `{ℓ ≤ λ}`, and only then transported to the region by
"region = the side of the frontier".  Two algebraic facts make that transport trivial, and both hold
by the fields of `DentDatum`:

* `dent_slab_invariant` — the deformation leaves the slab **exactly** invariant (`d_orth_v`), so it
  moves only the wall;
* `dent_wall_shift` — the level functional moves by `a'·χ(·)·ℓ d`, which is `a'·ℓ d > 0` on the core
  of the dent (`push_pos`).  Hence on the core the deformed region is the region at the *shifted*
  level `λ + a'·ℓ d`, which is the first clause of the design's `dent_regular`; the annulus clause
  (`C¹`-small) and the frontier/knot clauses are the analytic part and are left for its statement.

Both are proved below. -/

/-- **The dent leaves the slab invariant.**  Since `d` is orthogonal to `v`, the `⟪v,·⟫`-coordinate
of every point is unchanged, so the two slab faces `{|⟪v,·⟫ − (⟪v,c⟫ + u)| = h}` are preserved
pointwise. -/
theorem dent_slab_invariant (D : DentDatum ψ s c σ u v h R ℓ) (z : R3) :
    |inner ℝ v (D.deform z) - (inner ℝ v c + u)| =
      |inner ℝ v z - (inner ℝ v c + u)| := by
  simp only [DentDatum.deform, dentDeform, inner_add_right, inner_smul_right, D.d_orth_v,
    mul_zero, add_zero]

/-- **The displacement of the level functional under the dent.**  On the core of the dent, where
`χ = 1`, the level functional increases by `a'·ℓ d > 0`; this is the sense in which the dent
"pushes the wall". -/
theorem dent_wall_shift (D : DentDatum ψ s c σ u v h R ℓ) (z : R3) :
    ℓ (D.deform z) = ℓ z + (D.a' * D.χ (‖z - D.centre‖ / D.r)) * ℓ D.d := by
  simp only [DentDatum.deform, dentDeform, map_add, map_smul, smul_eq_mul]

/-- The push is strictly positive on the core of the dent. -/
theorem dent_push_pos_of_chi_eq_one (D : DentDatum ψ s c σ u v h R ℓ) {z : R3}
    (hz : D.χ (‖z - D.centre‖ / D.r) = 1) :
    0 < ℓ (D.deform z) - ℓ z := by
  rw [dent_wall_shift D z, hz, mul_one]
  linarith [mul_pos D.a'_pos D.push_pos]


/-- **The first clause of `dent_regular`: the core pullback of the removed set.**

Let `removed λ = {slab} ∩ {ℓ ≤ λ}` be the removed set of the sweep at the level `λ` — the set whose
frontier is the sweep's level surface, with the slab and the wall as its two constraints.  On the
**core** of the dent (where `χ = 1`, so the deformation is the translation by `a' • d`) the deformed
removed set is *exactly* the removed set at the **shifted** level `λ − a'·ℓ d`:

  `deform z ∈ removed λ  ↔  z ∈ removed (λ − a'·ℓ d)`  for `χ(‖z − centre‖/r) = 1`.

This is the design's "in the core the dented region IS the region at level `λ ∓ a''`", with the shift
made explicit and, by `dent_slab_invariant` (the slab is preserved pointwise, since `d ⊥ v`) and
`dent_wall_shift`, *proved* rather than assumed.  The remaining clauses of `dent_regular` — the
`C¹`-small change in the annulus (`a'' ≤ κr/(2‖χ'‖)`), the transport of the frontier surface, and
`K ∩ frontier` unchanged via `offK` — are the analytic part, stated on the frontier surface as
recorded in the module docstring. -/
theorem dent_regular_core (D : DentDatum ψ s c σ u v h R ℓ) (lam : ℝ) {z : R3}
    (hz : D.χ (‖z - D.centre‖ / D.r) = 1) :
    (|inner ℝ v (D.deform z) - (inner ℝ v c + u)| ≤ h ∧ ℓ (D.deform z) ≤ lam) ↔
      (|inner ℝ v z - (inner ℝ v c + u)| ≤ h ∧ ℓ z ≤ lam - D.a' * ℓ D.d) := by
  rw [dent_slab_invariant D z, dent_wall_shift D z, hz, mul_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩


/-! ## Item 2: the frontier vocabulary — the sweep's level surface

The clauses of `dent_regular` live on the sweep's **level surface**, not on the surface `F` (the
deformation moves points off `F`, see the object discipline of AUDIT §23.9–§23.10).  The level
surface is the frontier of the removed set of the level,

  `removedSet s c σ u v h ℓ λ  = PBox s c σ \ (slab ∩ {ℓ < λ})`,
  `levelSurface s c σ u v h ℓ λ = frontier (removedSet s c σ u v h ℓ λ)`,

whose two *constraints* are the slab `{|⟪v,·⟫ − (⟪v,c⟫ + u)| ≤ h}` and the wall `{ℓ ≤ λ}`; the region
of the sweep is the side of it (`Work.Drive.EpsFormSphere.openTiltedSweepRegion`).  This is the object
item 3 (`K ∩ frontier` invariance) and the transport clause of `dent_regular` are stated against. -/

/-- **The removed set of a level of the tilted sweep** (the naming of
`Work.Drive.Mono.tiltedLevelRemoved`, whose frontier is the sweep's level surface). -/
def removedSet (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam

/-- **The sweep's level surface** at the level `lam`: the frontier of the removed set.  This is the
surface the dents act on, and hence the object every clause of `dent_regular` is stated against. -/
def levelSurface (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  frontier (removedSet s c σ u v h ℓ lam)

/-- Membership in the level surface unfolds to membership in the frontier of the removed set. -/
theorem mem_levelSurface {y : R3} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3}
    {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} :
    y ∈ levelSurface s c σ u v h ℓ lam ↔
      y ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) :=
  Iff.rfl

/-- Membership in the removed set unfolds to the two constraints (box ∧ (slab ∧ wall)). -/
theorem mem_removedSet {y : R3} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3}
    {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} :
    y ∈ removedSet s c σ u v h ℓ lam ↔
      y ∈ Submission.PBox s c σ ∧
        ¬ (|inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y < lam) :=
  Iff.rfl


/-- **The box margin `hsupp` is a fact about the datum.**  The ball of radius `r + a'` around the
centre lies in the open box, because `a' ≤ δ` and the radius-`r + δ` ball does.  This is the
hypothesis `dent_box_margin` consumes, now *derived* from the datum's room `δ` rather than assumed;
the obligation it leaves is the design's smallness threshold, which is what lets `a'` be chosen
inside `δ`. -/
theorem dent_hsupp (D : DentDatum ψ s c σ u v h R ℓ) :
    ∀ z : R3, ‖z - D.centre‖ ≤ D.r + D.a' → z ∈ Submission.PBox s c σ :=
  fun z hz => D.δ_subset z (le_trans hz (by linarith [D.a'_le_δ]))


/-! ## The datum-level form of `offK`: the knot avoids the dent's ball

`dent_fixes_knot` shows that a dent whose ball is avoided by the knot acts as the identity on `K`, so
"`K ∩ frontier` is unchanged" is immediate.  Its hypothesis is however *global* ball avoidance, which
is strictly stronger than the design's per-event `offK` (critical points only): the reviews of
`dent_fixes_knot` flagged exactly this.  So — as with the room `δ` (§23.13) and the core
neighbourhood (§23.12) — it is a property of the *chosen* dent, and it is named here so that it can be
carried alongside them rather than reappearing as an assumption at each call site.  The obligation it
leaves is the choice of the radius: small enough that the ball around the (off-knot) event misses the
knot `K`. -/

/-- **The knot avoids the ball of radius `r` centred at `centre`.**  This is the datum-level form of
the `offK` clause: it is what makes the dent invisible to the knot (`dent_fixes_knot`), and it is a
property of the chosen radius, to be carried with the dent. -/
def KnotAvoids (K : Knot) (centre : R3) (r : ℝ) : Prop :=
  ∀ t : ℝ, r ≤ ‖K.curve t - centre‖

/-- Membership in `KnotAvoids` unfolds to the radius bound. -/
theorem knotAvoids_iff {K : Knot} {centre : R3} {r : ℝ} :
    KnotAvoids K centre r ↔ ∀ t : ℝ, r ≤ ‖K.curve t - centre‖ :=
  Iff.rfl

/-- **The datum-level `offK` of a dent**: the knot avoids the ball of the dent.  With it, the dent
fixes the knot pointwise (`dent_fixes_knot`), which is the honest carrier of "`K ∩ frontier` is
unchanged by the dent". -/
def DentDatum.knotAvoids (K : Knot) (D : DentDatum ψ s c σ u v h R ℓ) : Prop :=
  KnotAvoids K D.centre D.r


/-! ## Naming decision (item 3 / §23.11 rule): the capstone and its annulus companion

The rule of AUDIT §23.11 is that no capstone may *advertise* the design's `C¹`-small annulus clause
without containing it.  Settled here, so that no consumer has to guess:

* **`Work.Drive.Final.dent_regular`** is the capstone, and it is exactly the **clause bundle**: the
  core pullback (`dent_regular_core`), the box margin (`dent_hsupp`), the deformed ball in `PBox`
  (`dent_box_margin`), the knot fixed (`dent_fixes_knot`, under `DentDatum.knotAvoids`) and the
  frontier transport (`dent_transport_levelSurface`).  It advertises the *first four clauses plus the
  transport*, and nothing more.
* **`Work.Drive.Final.dent_annulus_lipschitz`** is the annulus clause — displacement `≤ a'` and the
  displacement map `a'·κ/r`-Lipschitz — and it **rides as its companion**.  It is deliberately *not*
  inside the capstone's statement, so that neither statement over-claims.
* A consumer that needs the analytic smallness **conjoins the two** (a single `∧`), e.g. when the
  queue reaches the dented region `Ω_k`.  The joinder adds no mathematics: both parts are proved, and
  the design's threshold `a' ≤ κ r / (2‖χ'‖)` is what the caller supplies to turn `a'·κ/r` into the
  `C¹`-smallness it wants (see `dent_annulus_lipschitz`).

So the name question is closed: capstone = the bundle, annulus = companion, joinder = one `∧` at the
point of use. -/


/-! ## The dented region `Ω_k`: the atomic step

The design's clause 4 processes the events at one level **one at a time**: `Ω_k` is obtained from the
level region `X λ` by applying the **dent-out** deformation at `p₁..p_k` and the **dent-in**
deformation at the remaining events.  This file records the *atomic* piece of that construction — one
signed dent applied to a set — so that the iteration is a composition of named maps rather than a
formula.

For one dent and a sign `σ ∈ {−1, +1}`, the image of `X` is the set of points
`x + (σ·a'·χ(‖x − centre‖/r)) • d` with `x ∈ X`.  With `σ = +1` this is the dent-out step; with
`σ = −1` the dent-in step.  A consumer iterating the events composes these steps over a finite family
of dents (pairwise disjoint supports, so the steps commute), and conjoins
`Work.Drive.Final.dent_regular` with `Work.Drive.Final.dent_annulus_lipschitz` at the point of use
(naming decision, §23.14): the capstone gives the clause bundle, the companion gives the analytic
smallness, and the joinder is a single `∧`. -/

/-- **The atomic dent step**: the image of a set `X` under the signed dent deformation.  `σ = +1` is
the dent-out step, `σ = −1` the dent-in step. -/
def dentStep (centre d : R3) (χ : ℝ → ℝ) (r a' : ℝ) (σ : ℝ) (X : Set R3) : Set R3 :=
  {y : R3 | ∃ x ∈ X, y = x + (σ * a' * χ (‖x - centre‖ / r)) • d}

/-- Membership in a dent step unfolds to the signed displacement. -/
theorem mem_dentStep {centre d : R3} {χ : ℝ → ℝ} {r a' σ : ℝ} {X : Set R3} {y : R3} :
    y ∈ dentStep centre d χ r a' σ X ↔
      ∃ x ∈ X, y = x + (σ * a' * χ (‖x - centre‖ / r)) • d :=
  Iff.rfl

/-- **The dent step of a `DentDatum`**: `dentStep` at the datum's cutoff, centre, direction, radius
and depth.  `D.dentStep σ X` is one step of the sequential resolution of the events. -/
def DentDatum.dentStep (D : DentDatum ψ s c σ u v h R ℓ) (sign : ℝ) (X : Set R3) : Set R3 :=
  Work.Drive.Final.dentStep D.centre D.d D.χ D.r D.a' sign X


/-! ## The composition `Ω_k`

The design's clause 4 resolves the events at one level **one at a time**: with `m` events and a step
index `k`, the region `Ω_k` is the level region `X λ` pushed by the **dent-out** step at the first `k`
events and by the **dent-in** step at the rest.  Both pieces are now named:

* `dentSign k` — the sign of the step at each event: `+1` for the first `k` events (dent-out), `−1`
  for the rest (dent-in);
* `dentedRegion D sign X` — the fold of `DentDatum.dentStep (sign i)` over the event family applied
  to `X`.

The fold's order is immaterial for the intended data (the dents have pairwise disjoint supports, so
the steps commute), which is why the *fold* — rather than any particular composition order — is the
right name; the order-independence is a separate lemma over the commutation hypothesis, to be stated
with the event data.  A consumer at the point of use conjoins `Work.Drive.Final.dent_regular` with
`Work.Drive.Final.dent_annulus_lipschitz` (naming decision, §23.14). -/

/-- **The sign pattern of the sequential resolution**: `+1` at the first `k` events (dent-out), `−1`
at the rest (dent-in). -/
def dentSign {m : ℕ} (k : ℕ) (i : Fin m) : ℝ :=
  if (i : ℕ) < k then 1 else -1

/-- **The dented region** `Ω_k` at the sign pattern `sign`: the fold of the signed dent steps over the
event family, applied to the region `X`.  `dentedRegion D (dentSign k) (X λ)` is the design's `Ω_k`. -/
def dentedRegion {m : ℕ} (D : Fin m → DentDatum ψ s c σ u v h R ℓ) (sign : Fin m → ℝ)
    (X : Set R3) : Set R3 :=
  (List.finRange m).foldr (fun i (Y : Set R3) => (D i).dentStep (sign i) Y) X

end

end Work.Drive.Final
