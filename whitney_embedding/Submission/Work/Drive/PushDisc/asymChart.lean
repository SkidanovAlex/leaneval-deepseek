import Mathlib
import Submission.Work.Drive.PushDisc.sweepClauses
import Submission.Work.Drive.Whitney.modelChart

/-!
# The *asymmetric* model chart of the Whitney move: the clause set from a one-sided normal form

The model chart `Work.Drive.Whitney.ModelChartData` straightens **both** sheets at once
(`f (σ p) = Θ (p.1, c p.1, 0, p.2)`): the second sheet is the graph `{y = c x, u = 0}`.  Producing
such a chart is the framing step (M3b) of the classical route and is where `OppositeType` and the
`ℤ/2` of `O (2n-2)` are spent.

This module isolates a **strictly weaker** geometric input, in which *only the first* sheet is
straightened and the second is merely a *graph over the `(x,v)`-coordinates*:

    f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2)

with arbitrary `h : ℝ × ℝ^k → ℝ × ℝ^k` in place of the pair `(c p.1, 0)`.

Why this suffices.  The push is the *coordinate shear* `mpsi` (M1) of the model, transported by the
coordinates: it changes only the `y`-coordinate by `2 m x l (‖v‖²)`.  Let `ξ = (x, y, u, v)` be the
coordinates of a **moved** point of the window, so that `y = (h p).1`, `u = (h p).2`, `v = p.2` with
`p ∈ asymReg`.  Its pushed value `ξ'` has the *same* `(x,u,v)` and `y' = y - 2 m x l (‖v‖²)`.
A collision of `Θ ξ'` with `f '' M` is then impossible for exactly two reasons:

* **second sheet**: a point of `M` mapping to `Θ ξ'` and lying on the second sheet would be read off
  from its own `(x,u,v)`-coordinates, i.e. would be `σ₂ p` itself, and `Φ (f (σ₂ p)) = ξ ≠ ξ'`;
* **first sheet**: the first sheet's tube `U₁` maps into the plane `{y = 0, v = 0}` (row `hU₁row`), so
  a collision there forces `v = 0` and `y' = 0`, i.e. `(h (x,0)).1 = 2 m x l 0` — forbidden by the row
  `havoid`.  This is where the opposite-sign hypothesis of the bigon is spent (the height of the core
  vanishes transversely at the two double points with *opposite* signs, so a bump `2 m x l` can be
  chosen to be strictly above it on the whole window and to vanish beyond it).

either on the first sheet or on the second one.  (An earlier version of the interface asked
the pushed values to lie within a fixed `δ` of a fixed compact anchor — rows `hnear`/`hiso`.  That
quantitative form is **false in general** — the moved points sweep the whole Whitney disc and `δ` is
bounded by the distance from the finger's image to the image of the complement of the tubes — and
the shadow branch of its propagation does not cover the moved points.  See the docstring of `hswept`
below and
`Work.Drive.PushDisc.isolation_of_compact_anchor` / `Work.Drive.PushDisc.hswept_of_hnear_hiso`.)

So the whole geometric content of the compact `n ≥ 3` case is: **flatten the first sheet, keep the
second one a graph over `(x,v)` on the window, control the height of its core, and know that the
moved values have no preimage outside the two tubes.**  Nothing here needs the two sheets to be
straightened simultaneously, and nothing needs the framing of the Whitney disc.

## History

The interface used to carry a `hsheets` row (a bounded *slab* of model points in which the image is
the first sheet together with the graph of `h`).  That row is **not** what the geometry provides: the
slab is a product of intervals and its `y`-extent must dominate `sup |(h ·).1 - 2 m · l|`, so it can
only be inside the ambient isolation neighbourhood of the loop if that quantity is small, and the
*pushed* points need not be near the image of the loop at all — they are near the image of the first
sheet's tube.  The rows `hU₁row`/`hnear`/`hiso` below are the honest, provable form.

## Main results

* `Work.Drive.PushDisc.AsymChartData` — the geometric input (a one-sided normal form).
* `Work.Drive.PushDisc.hasAmbientPushData_of_asymChartData` — it gives the clause set.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Metric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]


/-- **The transversality of the shear direction.**  If `P` (the plane of the flattened first sheet)
and `T` (a tangent plane of the second sheet) span the ambient space, then a linear functional
vanishing on both is zero.  Equivalently: *every* nonzero functional vanishing on `P` is nonzero on
`T`.  This is why the second sheet only needs to be a *graph* over `(x,u,v)` (not over `(x,v)`, which
would be a genuine straightening and needs the framing): the `y`-coordinate of the model shear can
never be constant along a tangent plane of the second sheet, so inside the window the second sheet is
a graph over `(x,u,v)`.  (Kept for reference; the current interface does not consume it.) -/
theorem eq_zero_of_vanishing_on_sup_top {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P T : Submodule ℝ E) (hPT : P ⊔ T = ⊤) {ℓ : E →ₗ[ℝ] ℝ}
    (hP : ∀ p ∈ P, ℓ p = 0) (hT : ∀ t ∈ T, ℓ t = 0) : ℓ = 0 := by
  ext v
  have hv : v ∈ P ⊔ T := by rw [hPT]; trivial
  obtain ⟨p, hp, t, ht, rfl⟩ := Submodule.mem_sup.mp hv
  have h : ℓ (p + t) = 0 := by rw [map_add, hP p hp, hT t ht, add_zero]
  exact h

/-- The parameter window of the second sheet: `|x| < X'` and `‖v‖ < 1`. -/
def asymReg (k : ℕ) (X' : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin k)) :=
  {p | |p.1| < X' ∧ ‖p.2‖ < 1}

/-- The *bounded* slab of the ambient model space `|x| < X'`, `‖v‖ < 1`, `|y| < Y`, `‖u‖ < U`.
**Unused**: the old `hsheets` row was stated with this slab as its hypothesis, but a slab-based
hypothesis is not what the geometry provides (see the module docstring, "History"); the isolation is
now carried by the row `hswept` of `AsymChartData`.  Kept because other notes refer to it. -/
def asymSlab (k : ℕ) (X' Y U : ℝ) : Set (Work.Drive.Whitney.Mdl k) :=
  {ξ | |ξ.1| < X' ∧ ‖ξ.2.2.2‖ < 1 ∧ |ξ.2.1| < Y ∧ ‖ξ.2.2.1‖ < U}

/-- **The model neighbourhood of the frontier** on which the shear acts trivially: with `m` vanishing
for `|x| ≥ X` and `l` for `t ≥ 1/2`, the open set `{|x| > X} ∪ {1/2 < ‖v‖²}` consists of model points
on which the shear's amplitude `m ξ.1 * l (‖ξ.2.2.2‖²)` vanishes.  It contains every model point with
`|x| = X' > X` or `‖v‖ = 1`, i.e. (for a parametrisation `σ₂` of the sheet-two tube by the `(x,v)`-
window) the image of the frontier of the finger — this is the model-level content of the rows
`Oo`, `hOfix` and `hOfront` of `AsymChartData`.  Note that `Oo` has to be given by the *strict*
inequalities: the vanishing sets `{m = 0}`, `{l = 0}` are closed, so no neighbourhood of a frontier
point with `|x| = X'` and `‖v‖ < 1/√2` can lie in them (there `m ≠ 0` is allowed for `|x| < X'`). -/
def asymOo (k : ℕ) (X : ℝ) : Set (Work.Drive.Whitney.Mdl k) :=
  {ξ | X < |ξ.1| ∨ 1 / 2 < ‖ξ.2.2.2‖ ^ 2}

theorem isOpen_asymOo (k : ℕ) (X : ℝ) : IsOpen (asymOo k X) := by
  have h1 : Continuous (fun ξ : Work.Drive.Whitney.Mdl k => |ξ.1|) :=
    continuous_abs.comp continuous_fst
  have h2 : Continuous (fun ξ : Work.Drive.Whitney.Mdl k => ‖ξ.2.2.2‖ ^ 2) :=
    ((continuous_norm.comp (by fun_prop :
      Continuous (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.2.2)))).pow 2
  exact (isOpen_Ioi.preimage h1).union (isOpen_Ioi.preimage h2)

theorem amplitude_zero_of_mem_asymOo {k : ℕ} {X : ℝ} {m l : ℝ → ℝ}
    (hmzero : ∀ x : ℝ, X ≤ |x| → m x = 0) (hlzero : ∀ t : ℝ, 1 / 2 ≤ t → l t = 0)
    {ξ : Work.Drive.Whitney.Mdl k} (hξ : ξ ∈ asymOo k X) :
    m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0 := by
  rcases hξ with h | h
  · rw [hmzero ξ.1 (le_of_lt h), zero_mul]
  · rw [hlzero _ (le_of_lt h), mul_zero]

theorem mem_asymOo_of_coords {k : ℕ} {X X' : ℝ} (hXX' : X < X')
    {x y : ℝ} {u v : EuclideanSpace ℝ (Fin k)} (h : |x| = X' ∨ ‖v‖ = 1) :
    (x, y, u, v) ∈ asymOo k X := by
  rcases h with h | h
  · left; rw [h]; exact hXX'
  · right; rw [h]; norm_num

/-- **The one-sided normal form of the Whitney move.**  `Φ` are the coordinates of the ambient
space in which the *first* sheet is exactly the plane `{y = 0, v = 0}` (parametrised by `σ₁` over the
window) and the *second* sheet is the graph of `h` over the `(x,v)`-window (parametrised by `σ₂`);
`m`, `l` are the amplitudes of the model shear, and `havoid` is the height condition on the core of
the second sheet. -/
structure AsymChartData (n : ℕ) {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) where
  k : ℕ
  hk : n = k + 1
  /-- the window width of the amplitude `m` and of the finger (with `1 < X < X'`) -/
  X : ℝ
  X' : ℝ
  h1X : 1 < X
  hXX' : X < X'
  m : ℝ → ℝ
  l : ℝ → ℝ
  hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m
  hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) l
  hmnn : ∀ x : ℝ, 0 ≤ m x
  hlnn : ∀ t : ℝ, 0 ≤ l t
  hmzero : ∀ x : ℝ, X ≤ |x| → m x = 0
  hlzero : ∀ t : ℝ, 1 / 2 ≤ t → l t = 0
  hl0 : l 0 ≠ 0
  /-- the tube around the flattened first sheet (`γ₁`); its image lies in the plane
  `{y = 0, v = 0}` -/
  U₁ : Set M
  /-- the coordinates of the ambient space -/
  Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k
  Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))
  hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ
  hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y
  hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ
  /-- the height of the second sheet over the `(x,v)`-window -/
  h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)
  /-- `h` is `C^∞` **on the window** (only there: it is produced by reading the second sheet's
  `(y,u)`-coordinates off the `(x,v)`-parametrisation, which is only smooth on its own source) -/
  hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X')
  /-- the parametrisation of the second sheet -/
  σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M
  hσ₂ : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2)
  hp₂ : σ₂ ((-1 : ℝ), 0) = p₂
  hq₂ : σ₂ ((1 : ℝ), 0) = q₂
  hW₀o : IsOpen (σ₂ '' asymReg k X')
  hW₀W : σ₂ '' asymReg k X' ⊆ W
  /-- an open set of model points on which the amplitude vanishes stably -/
  Oo : Set (Work.Drive.Whitney.Mdl k)
  hOo : IsOpen Oo
  hOfix : ∀ ξ ∈ Oo, m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0
  hOfront : f '' frontier (σ₂ '' asymReg k X') ⊆ Θ '' Oo
  /-- **the first sheet's tube maps into the plane `{y = 0, v = 0}`** -/
  hU₁row : ∀ x : M, x ∈ U₁ → (Φ (f x)).2.1 = 0 ∧ (Φ (f x)).2.2.2 = 0
  /-- **The swept row (the honest form of the quantitative geometry).**

  Every *moved* point's pushed value has no preimage at all outside the two tubes: if `z : M` maps
  to the pushed value of `p`, then `z` lies in the first sheet's tube `U₁` or in the finger
  `σ₂ '' asymReg`.

  Why this replaces the earlier rows `hnear`/`hiso`.  The moved points *sweep the whole Whitney
  disc* (the amplitude `l` passes through every value of `(0, l 0)`), so the quantitative row
  "the pushed points are within a fixed `δ` of a fixed compact anchor" is a **false** inequality in
  general (`δ` is bounded by the distance from the finger's image to the image of the complement of
  the tubes, which can be arbitrarily small), and the "shadow" branch does not cover the moved
  points (project lead's audit of 2026-09-25: for the amplitudes of `heightAmplitudesNear` the
  `hlone`/`hlsupp` pair of `hnearOfShadow` is unsatisfiable, and in any case the moved points sweep
  the disc).  The
  swept row is what the collision argument actually consumes, and it is produced by
  `Work.Drive.PushDisc.asymChartData_of_whitneyChart` from the Whitney disc through
  `Work.Drive.PushDisc.isolation_of_compact_anchor` and
  `Work.Drive.PushDisc.hswept_of_hnear_hiso` (the bridge back to the discarded rows). -/
  hswept : ∀ p ∈ asymReg k X', 2 * m p.1 * l (‖p.2‖ ^ 2) ≠ 0 → ∀ z : M,
    f z = Θ (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2) →
      z ∈ U₁ ∪ σ₂ '' asymReg k X'
  /-- **the height condition on the core of the second sheet** -/
  havoid : ∀ x : ℝ, |x| < X' → (h (x, 0)).1 ≠ 2 * m x * l 0
  /-- the coordinates of the two double points on the first sheet -/
  hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)
  hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0)

section Shear

variable {k : ℕ} (m l : ℝ → ℝ)

/-- The model shear is a left inverse of its partner. -/
theorem msigma_mpsi (ξ : Work.Drive.Whitney.Mdl k) :
    Work.Drive.Whitney.msigma m l (Work.Drive.Whitney.mpsi m l ξ) = ξ := by
  obtain ⟨x, y, u, v⟩ := ξ
  simp only [Work.Drive.Whitney.mpsi, Work.Drive.Whitney.msigma]
  norm_num

/-- The model shear is a right inverse of its partner. -/
theorem mpsi_msigma (ξ : Work.Drive.Whitney.Mdl k) :
    Work.Drive.Whitney.mpsi m l (Work.Drive.Whitney.msigma m l ξ) = ξ := by
  obtain ⟨x, y, u, v⟩ := ξ
  simp only [Work.Drive.Whitney.mpsi, Work.Drive.Whitney.msigma]
  norm_num

/-- The fixed set of the model shear. -/
theorem mpsi_eq_self_iff (ξ : Work.Drive.Whitney.Mdl k) :
    Work.Drive.Whitney.mpsi m l ξ = ξ ↔ m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0 := by
  obtain ⟨x, y, u, v⟩ := ξ
  simp only [Work.Drive.Whitney.mpsi]
  constructor
  · intro h
    have h2 : y - 2 * m x * l (‖v‖ ^ 2) = y := by
      simpa using congrArg (fun ζ : ℝ × ℝ × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        ζ.2.1) h
    have : 2 * (m x * l (‖v‖ ^ 2)) = 0 := by linarith [sub_eq_iff_eq_add.mp h2]
    rcases mul_eq_zero.mp this with h3 | h3
    · exact absurd h3 (by norm_num)
    · exact h3
  · intro h
    have h2 : 2 * (m x * l (‖v‖ ^ 2)) = 0 := by rw [h]; ring
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl rfl))
    show y - 2 * m x * l (‖v‖ ^ 2) = y
    linarith [h2]

end Shear

/-- The model shear is `C^∞` as soon as its two amplitudes are. -/
theorem contDiff_mpsi {k : ℕ} {m l : ℝ → ℝ}
    (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m)
    (hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) l) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.Whitney.mpsi (k := k) m l) := by
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : Work.Drive.Whitney.Mdl k => 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2)) := by
    have hx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => ξ.1) := contDiff_fst
    have hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.2.2) := contDiff_snd.snd.snd
    have hm' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => m ξ.1) := hm.comp hx
    have hl' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => l (‖ξ.2.2.2‖ ^ 2)) :=
      hl.comp (ContDiff.norm_sq (𝕜 := ℝ) hv)
    exact (contDiff_const (c := (2 : ℝ)).mul hm').mul hl'
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.1 - 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2)) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.1) := contDiff_snd.fst
    exact h.sub hA
  have hbody : Work.Drive.Whitney.mpsi (k := k) m l = fun ξ : Work.Drive.Whitney.Mdl k =>
      (ξ.1, ξ.2.1 - 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2), ξ.2.2.1, ξ.2.2.2) := rfl
  rw [hbody]
  exact ContDiff.prodMk contDiff_fst (ContDiff.prodMk hB
    (ContDiff.prodMk contDiff_snd.snd.fst contDiff_snd.snd.snd))

/-- The model shear's inverse is `C^∞` as soon as its two amplitudes are. -/
theorem contDiff_msigma {k : ℕ} {m l : ℝ → ℝ}
    (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m)
    (hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) l) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.Whitney.msigma (k := k) m l) := by
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : Work.Drive.Whitney.Mdl k => 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2)) := by
    have hx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => ξ.1) := contDiff_fst
    have hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.2.2) := contDiff_snd.snd.snd
    have hm' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => m ξ.1) := hm.comp hx
    have hl' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => l (‖ξ.2.2.2‖ ^ 2)) :=
      hl.comp (ContDiff.norm_sq (𝕜 := ℝ) hv)
    exact (contDiff_const (c := (2 : ℝ)).mul hm').mul hl'
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.1 + 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2)) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.1) := contDiff_snd.fst
    exact h.add hA
  have hbody : Work.Drive.Whitney.msigma (k := k) m l = fun ξ : Work.Drive.Whitney.Mdl k =>
      (ξ.1, ξ.2.1 + 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2), ξ.2.2.1, ξ.2.2.2) := rfl
  rw [hbody]
  exact ContDiff.prodMk contDiff_fst (ContDiff.prodMk hB
    (ContDiff.prodMk contDiff_snd.snd.fst contDiff_snd.snd.snd))


/-- **The clause set from the one-sided normal form.** -/
theorem hasAmbientPushData_of_asymChartData {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (D : AsymChartData n f W p₁ p₂ q₁ q₂) :
    Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂ := by
  classical
  obtain ⟨k, _hk, X, X', h1X, hXX', m, l, hm, hl, hmnn, hlnn, hmzero, hlzero, hl0,
    U₁, Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, h, hh, σ₂, hσ₂, hp₂σ, hq₂σ, hW₀o, hW₀W,
    Oo, hOo, hOfix, hOfront, hU₁row, hswept, havoid, hp₁c, hq₁c⟩ := D
  have h1lt : (1 : ℝ) < X' := lt_trans h1X hXX'
  have hΘinj : Function.Injective Θ := by
    intro a b hab
    have h := congrArg Φ hab
    rwa [hΦΘ, hΦΘ] at h
  set W₀ : Set M := σ₂ '' asymReg k X' with hW₀def
  set Psi : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => Θ (Work.Drive.Whitney.mpsi m l (Φ y)) with hPsim
  set Sig : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => Θ (Work.Drive.Whitney.msigma m l (Φ y)) with hSigm
  set O : Set (EuclideanSpace ℝ (Fin (2 * n))) := Θ '' Oo with hOdef
  have hmem1 : ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈ asymReg k X' := by
    refine ⟨?_, by simp⟩
    rw [abs_neg, abs_one]; exact h1lt
  have hmem0 : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈ asymReg k X' := by
    refine ⟨?_, by simp⟩
    rw [abs_one]; exact h1lt
  -- the two double values in coordinates
  have hfp₁ : f p₁ = Θ ((-1 : ℝ), 0, 0, 0) := hp₁c
  have hfq₁ : f q₁ = Θ ((1 : ℝ), 0, 0, 0) := hq₁c
  have hfp₂ : f p₂ = Θ ((-1 : ℝ), (h ((-1 : ℝ), 0)).1, (h ((-1 : ℝ), 0)).2, 0) := by
    rw [← hp₂σ]; exact hσ₂ _ hmem1
  have hfq₂ : f q₂ = Θ ((1 : ℝ), (h ((1 : ℝ), 0)).1, (h ((1 : ℝ), 0)).2, 0) := by
    rw [← hq₂σ]; exact hσ₂ _ hmem0
  -- the core values vanish at the two double points
  have hcore₁ : (h ((-1 : ℝ), 0)).1 = 0 ∧ (h ((-1 : ℝ), 0)).2 = 0 := by
    have h3 : Θ ((-1 : ℝ), (h ((-1 : ℝ), 0)).1, (h ((-1 : ℝ), 0)).2, 0)
        = Θ ((-1 : ℝ), 0, 0, 0) := hfp₂.symm.trans (hfp.symm.trans hfp₁)
    have h4 := hΘinj h3
    exact ⟨congrArg (fun ζ : Work.Drive.Whitney.Mdl k => ζ.2.1) h4,
           congrArg (fun ζ : Work.Drive.Whitney.Mdl k => ζ.2.2.1) h4⟩
  have hcore₀ : (h ((1 : ℝ), 0)).1 = 0 ∧ (h ((1 : ℝ), 0)).2 = 0 := by
    have h3 : Θ ((1 : ℝ), (h ((1 : ℝ), 0)).1, (h ((1 : ℝ), 0)).2, 0)
        = Θ ((1 : ℝ), 0, 0, 0) := hfq₂.symm.trans (hfq.symm.trans hfq₁)
    have h4 := hΘinj h3
    exact ⟨congrArg (fun ζ : Work.Drive.Whitney.Mdl k => ζ.2.1) h4,
           congrArg (fun ζ : Work.Drive.Whitney.Mdl k => ζ.2.2.1) h4⟩
  -- the double points belong to the finger
  have hp₂W₀ : p₂ ∈ W₀ := ⟨_, hmem1, hp₂σ⟩
  have hq₂W₀ : q₂ ∈ W₀ := ⟨_, hmem0, hq₂σ⟩
  have hp₁W₀ : p₁ ∉ W₀ := by
    rintro ⟨p, hpreg, hpx⟩
    have h1 : f p₁ = Θ (p.1, (h p).1, (h p).2, p.2) := by
      rw [← hpx]; exact hσ₂ p hpreg
    have h3 : (p.1, (h p).1, (h p).2, p.2) = ((-1 : ℝ), 0, 0, 0) :=
      hΘinj (h1.symm.trans hfp₁)
    have hp : p = ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      refine Prod.ext ?_ ?_
      · exact congrArg (fun ζ : Work.Drive.Whitney.Mdl k => ζ.1) h3
      · exact congrArg (fun ζ : Work.Drive.Whitney.Mdl k => ζ.2.2.2) h3
    exact hp₁p₂ (hpx.symm.trans (by rw [hp]; exact hp₂σ))
  have hq₁W₀ : q₁ ∉ W₀ := by
    rintro ⟨p, hpreg, hpx⟩
    have h1 : f q₁ = Θ (p.1, (h p).1, (h p).2, p.2) := by
      rw [← hpx]; exact hσ₂ p hpreg
    have h3 : (p.1, (h p).1, (h p).2, p.2) = ((1 : ℝ), 0, 0, 0) :=
      hΘinj (h1.symm.trans hfq₁)
    have hp : p = ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      refine Prod.ext ?_ ?_
      · exact congrArg (fun ζ : Work.Drive.Whitney.Mdl k => ζ.1) h3
      · exact congrArg (fun ζ : Work.Drive.Whitney.Mdl k => ζ.2.2.2) h3
    exact hq₁q₂ (hpx.symm.trans (by rw [hp]; exact hq₂σ))
  have hinjW₀ : ∀ x ∈ W₀, ∀ y ∈ W₀, f x = f y → x = y := by
    intro x hx y hy hxy
    rcases hclean x y (hW₀W hx) (hW₀W hy) hxy with h | h | h | h | h
    · exact h
    · exact absurd (h.1 ▸ hx) hp₁W₀
    · exact absurd (h.2 ▸ hy) hp₁W₀
    · exact absurd (h.1 ▸ hx) hq₁W₀
    · exact absurd (h.2 ▸ hy) hq₁W₀
  -- the coordinates of the pushed point
  have hmpsi_coord : ∀ p : ℝ × EuclideanSpace ℝ (Fin k),
      Work.Drive.Whitney.mpsi m l (p.1, (h p).1, (h p).2, p.2) =
        (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2) := fun p => rfl
  -- the moved points are off the image
  have hmoved : ∀ x ∈ W₀, Psi (f x) ≠ f x → Psi (f x) ∉ f '' (Set.univ : Set M) := by
    rintro x ⟨p, hpreg, rfl⟩ hmov ⟨x', -, hx'⟩
    have hΦfx : Φ (f (σ₂ p)) = (p.1, (h p).1, (h p).2, p.2) := by
      rw [hσ₂ p hpreg, hΦΘ]
    have hshift : 2 * m p.1 * l (‖p.2‖ ^ 2) ≠ 0 := by
      have hne : Work.Drive.Whitney.mpsi m l (Φ (f (σ₂ p))) ≠ Φ (f (σ₂ p)) := by
        intro heq
        refine hmov ?_
        rw [hPsim]
        show Θ (Work.Drive.Whitney.mpsi m l (Φ (f (σ₂ p)))) = f (σ₂ p)
        rw [heq, hΘΦ]
      have hfix := (mpsi_eq_self_iff m l (Φ (f (σ₂ p)))).not.mp hne
      rw [hΦfx] at hfix
      simpa using hfix
    -- the pushed point and its coordinates
    have hξ' : Φ (f x') = (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2) := by
      rw [hx', hPsim]
      show Φ (Θ (Work.Drive.Whitney.mpsi m l (Φ (f (σ₂ p))))) = _
      rw [hΦΘ, hΦfx]
      exact hmpsi_coord p
    -- the pushed value is the image of the model point shifted in `y` by the shear
    have hpush : Θ (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2) = f x' := by
      have hkey : Psi (f (σ₂ p))
          = Θ (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2) := by
        rw [hPsim]
        show Θ (Work.Drive.Whitney.mpsi m l (Φ (f (σ₂ p))))
          = Θ (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2)
        rw [hΦfx, hmpsi_coord p]
      rw [← hkey, hx']
    -- the swept row: any preimage of the pushed value already lies in one of the two tubes
    rcases hswept p hpreg hshift x' hpush.symm with hx'U₁ | hx'W₀
    · -- `x'` lies on the flattened first sheet: its coordinates are `(y, v) = (0, 0)`
      obtain ⟨h0, hv⟩ := hU₁row x' hx'U₁
      rw [hξ'] at h0 hv
      have hp2 : p.2 = (0 : EuclideanSpace ℝ (Fin k)) := hv
      have hpy : (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2) = 0 := h0
      have hpeq : p = (p.1, (0 : EuclideanSpace ℝ (Fin k))) := Prod.ext rfl hp2
      rw [hpeq] at hpy
      simp only [norm_zero, pow_two, mul_zero] at hpy
      exact havoid p.1 hpreg.1 (by linarith)
    · -- `x'` is the sheet-two point of its own `(x, v)`-parameter, which is `p`
      obtain ⟨q, hqreg, hxq⟩ := hx'W₀
      have hq1 : (Φ (f x')).1 = q.1 := by rw [← hxq, hσ₂ q hqreg, hΦΘ]
      have hq3 : (Φ (f x')).2.2.2 = q.2 := by rw [← hxq, hσ₂ q hqreg, hΦΘ]
      have hq1' : q.1 = p.1 := by rw [← hq1, hξ']
      have hq3' : q.2 = p.2 := by rw [← hq3, hξ']
      have hqp : q = p := Prod.ext hq1' hq3'
      have hval : f x' = f (σ₂ p) := by rw [← hxq, hqp]
      have hPsi : Psi (f (σ₂ p)) = f (σ₂ p) := by rw [← hx']; exact hval
      refine hshift ?_
      have h1 : Θ (Work.Drive.Whitney.mpsi m l (Φ (f (σ₂ p)))) = Θ (Φ (f (σ₂ p))) := by
        simp only [hPsim] at hPsi
        rw [show f (σ₂ p) = Θ (Φ (f (σ₂ p))) from (hΘΦ (f (σ₂ p))).symm] at hPsi
        rw [hΦΘ] at hPsi
        exact hPsi
      have h5 := congrArg (fun ζ : Work.Drive.Whitney.Mdl k => ζ.2.1) (hΘinj h1)
      rw [hΦfx, hmpsi_coord p] at h5
      simp only at h5
      linarith

  -- the two double points are moved
  have hml₁ : m (-1) * l 0 ≠ 0 := fun h0 =>
    havoid (-1) (by rw [abs_neg, abs_one]; exact h1lt) (by rw [hcore₁.1, mul_assoc, h0, mul_zero])
  have hml₀ : m 1 * l 0 ≠ 0 := fun h0 =>
    havoid 1 (by rw [abs_one]; exact h1lt) (by rw [hcore₀.1, mul_assoc, h0, mul_zero])
  have hp₂moved : Psi (f p₂) ≠ f p₂ := by
    intro hcon
    have hΦ : Φ (f p₂) = ((-1 : ℝ), 0, 0, 0) := by
      rw [hfp₂, hΦΘ, hcore₁.1, hcore₁.2]
    have hmpsi : Work.Drive.Whitney.mpsi m l (Φ (f p₂)) = Φ (f p₂) := by
      have hcon' : Θ (Work.Drive.Whitney.mpsi m l (Φ (f p₂))) = Θ (Φ (f p₂)) := by
        simp only [hPsim] at hcon
        rw [show f p₂ = Θ (Φ (f p₂)) from (hΘΦ (f p₂)).symm] at hcon
        rw [hΦΘ] at hcon
        exact hcon
      exact hΘinj hcon'
    have hfix := (mpsi_eq_self_iff m l (Φ (f p₂))).mp hmpsi
    rw [hΦ] at hfix
    simp only [norm_zero, pow_two, mul_zero] at hfix
    rcases mul_eq_zero.mp hfix with h0 | h0
    · exact hml₁ (by rw [h0, zero_mul])
    · exact hl0 h0
  have hq₂moved : Psi (f q₂) ≠ f q₂ := by
    intro hcon
    have hΦ : Φ (f q₂) = ((1 : ℝ), 0, 0, 0) := by
      rw [hfq₂, hΦΘ, hcore₀.1, hcore₀.2]
    have hmpsi : Work.Drive.Whitney.mpsi m l (Φ (f q₂)) = Φ (f q₂) := by
      have hcon' : Θ (Work.Drive.Whitney.mpsi m l (Φ (f q₂))) = Θ (Φ (f q₂)) := by
        simp only [hPsim] at hcon
        rw [show f q₂ = Θ (Φ (f q₂)) from (hΘΦ (f q₂)).symm] at hcon
        rw [hΦΘ] at hcon
        exact hcon
      exact hΘinj hcon'
    have hfix := (mpsi_eq_self_iff m l (Φ (f q₂))).mp hmpsi
    rw [hΦ] at hfix
    simp only [norm_zero, pow_two, mul_zero] at hfix
    rcases mul_eq_zero.mp hfix with h0 | h0
    · exact hml₀ (by rw [h0, zero_mul])
    · exact hl0 h0
  -- the push fixes a neighbourhood of the frontier
  have hOeq : O = Φ ⁻¹' Oo := by
    rw [hOdef]
    ext y
    constructor
    · rintro ⟨ξ, hξ, rfl⟩
      show Φ (Θ ξ) ∈ Oo
      rwa [hΦΘ]
    · intro hy
      exact ⟨Φ y, hy, hΘΦ y⟩
  have hOo' : IsOpen O := by
    rw [hOeq]
    exact hOo.preimage hΦsm.continuous
  have hOfront' : f '' frontier W₀ ⊆ O := by
    rw [hW₀def, hOdef]
    exact hOfront
  have hOid : ∀ y ∈ O, Psi y = y := by
    rintro y ⟨ξ, hξO, rfl⟩
    have hmp : Work.Drive.Whitney.mpsi m l ξ = ξ :=
      (mpsi_eq_self_iff m l ξ).mpr (hOfix ξ hξO)
    rw [hPsim]
    show Θ (Work.Drive.Whitney.mpsi m l (Φ (Θ ξ))) = Θ ξ
    rw [hΦΘ, hmp]
  have hsigpsi : ∀ y, Sig (Psi y) = y := by
    intro y
    rw [hSigm, hPsim]
    show Θ (Work.Drive.Whitney.msigma m l (Φ (Θ (Work.Drive.Whitney.mpsi m l (Φ y))))) = y
    rw [hΦΘ, msigma_mpsi m l, hΘΦ]
  have hpsisig : ∀ y, Psi (Sig y) = y := by
    intro y
    rw [hPsim, hSigm]
    show Θ (Work.Drive.Whitney.mpsi m l (Φ (Θ (Work.Drive.Whitney.msigma m l (Φ y))))) = y
    rw [hΦΘ, mpsi_msigma m l, hΘΦ]
  have hPsi_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Psi := by
    rw [hPsim]
    exact hΘsm.comp ((contDiff_mpsi hm hl).comp hΦsm)
  have hSig_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Sig := by
    rw [hSigm]
    exact hΘsm.comp ((contDiff_msigma hm hl).comp hΦsm)
  exact hasAmbientPushData_of_finger_off_image f W p₁ p₂ q₁ q₂ hfp hfq hclean hsep W₀ hW₀o
    hW₀W hp₂W₀ hq₂W₀ hp₁W₀ hq₁W₀ hinjW₀ Psi Sig O hOo' hOfront' hOid hsigpsi hpsisig
    hPsi_cd.contMDiff hSig_cd.contMDiff hmoved hp₂moved hq₂moved



set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Set

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]

/-- **The one-sided normal form exists for every configuration of the target** (the residual of the
compact `n ≥ 3` case in the asymmetric form). -/
def AsymChartAll (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    Nonempty (AsymChartData n f W p₁ p₂ q₁ q₂)

/-- **The target from the one-sided normal form.**  The compact `n ≥ 3` case of the signed smooth
push follows from `AsymChartAll`. -/
theorem hasPushSignedSmooth_of_asymChartAll (h : AsymChartAll n M) :
    Work.Drive.HasPushSignedSmooth n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂
    hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂
    hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  obtain ⟨D⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁
    hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  exact hasAmbientPushData_of_asymChartData f W p₁ p₂ q₁ q₂ hfp hfq hp₁p₂ hq₁q₂ hclean hsep D

/-- **The `Oo` rows of `AsymChartData` from the frontier hypothesis.**  If `m` vanishes for
`|x| ≥ X`, `l` for `t ≥ 1/2`, and every point of the finger's frontier has model coordinates with
`|x| = X' > X` or `‖v‖ = 1`, then the three rows `Oo`, `hOfix`, `hOfront` are satisfiable, with
`Oo := asymOo k X`.

The hypothesis `hfr` is what `σ₂` being an *open embedding* of the window supplies: the frontier of
`σ₂ '' asymReg k X'` is then the image of the frontier of `asymReg k X'`, i.e. of
`{|x| = X'} ∪ {‖v‖ = 1}`. -/
theorem exists_asymOo_rows {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (m l : ℝ → ℝ) (X X' : ℝ) (hXX' : X < X')
    (hmzero : ∀ x : ℝ, X ≤ |x| → m x = 0) (hlzero : ∀ t : ℝ, 1 / 2 ≤ t → l t = 0)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M)
    (hfr : ∀ x ∈ frontier (σ₂ '' asymReg k X'),
      X < |(Φ (f x)).1| ∨ 1 / 2 < ‖(Φ (f x)).2.2.2‖ ^ 2) :
    ∃ Oo : Set (Work.Drive.Whitney.Mdl k), IsOpen Oo ∧
      (∀ ξ ∈ Oo, m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0) ∧
      f '' frontier (σ₂ '' asymReg k X') ⊆ Θ '' Oo := by
  refine ⟨asymOo k X, isOpen_asymOo k X, ?_, ?_⟩
  · intro ξ hξ
    exact amplitude_zero_of_mem_asymOo hmzero hlzero hξ
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨Φ (f x), hfr x hx, hΘΦ (f x)⟩

end Work.Drive.PushDisc
