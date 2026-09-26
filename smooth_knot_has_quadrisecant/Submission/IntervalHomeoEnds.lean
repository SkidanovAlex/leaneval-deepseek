import Mathlib

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false

/-!
# S165 — end correspondence for homeomorphisms of open intervals (module
Submission/IntervalHomeoEnds.lean)

The first sub-lemma of the facing-normalization theorem (ROADMAP S163/S164,
step (3)(i)): a homeomorphism between open real intervals is strictly
monotone, and it maps the ends of the interval to ends.  Content (namespace
LeanEval.KnotTheory.Quadrisecant; PURE Mathlib):

1. **`intervalHomeoTotal`** — totalize the coordinate map of an interval
   homeo `e : (c,d) ≃ₜ (a,b)` (agreeing with `e` on `(c,d)`, arbitrary
   outside), with the value lemma `intervalHomeoTotal_eq`;
2. **`intervalHomeoTotal_contOn_injOn`** — the totalized map is continuous
   on `(c,d)` (restriction equals `val ∘ e`, via
   `continuousOn_iff_continuous_domRestrict`) and injective there;
3. **`intervalHomeo_coord_strictMono_or_anti`** — a homeo between open
   intervals of ℝ is strictly increasing or strictly decreasing (the
   monotonicity of continuous injective maps:
   `ContinuousOn.strictMonoOn_of_injOn_Ioo` of Mathlib);
4. **`intervalReflection`** (the order-reversing reflection `t ↦ c+d−t`,
   with `intervalReflection_apply` / `intervalReflection_involutive`);
5. **`intervalHomeo_left_end_reaches_endpoint`** — end correspondence at
   the LEFT end: as `t → c⁺`, `(e t : ℝ)` is eventually below `a + ε`
   (increasing case) or above `b − ε` (decreasing case) — i.e. the left
   end of the domain goes to the left or the right end of the range.
   Proof: surjectivity (`e.symm` hits the point `a+ε` / `b−ε`) +
   strict monotonicity + the trivial large-ε bound;
6. **`intervalHomeo_right_end_reaches_endpoint`** — the RIGHT-end
   analogue, derived from the left-end theorem by pre-composing with the
   reflection homeo.

These are the model-level inputs of the seam-inseparability argument
(step (3)(ii) of the S164 record): when both charts have a strict seam at
the same end of the overlap, the corresponding one-sided approach of the
transition homeo makes the two seam points inseparable.  Everything here
is verified (no axioms, no `sorry`).
-/
open Set
open scoped Topology

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-- Totalize the coordinate map of an interval homeo: agrees with `e` on `(c,d)`. -/
noncomputable def intervalHomeoTotal {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) : ℝ → ℝ :=
  fun r => if h : r ∈ Ioo c d then (e ⟨r, h⟩ : ℝ) else a

theorem intervalHomeoTotal_eq {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) {r : ℝ} (hr : r ∈ Ioo c d) :
    intervalHomeoTotal hab hcd e r = (e ⟨r, hr⟩ : ℝ) := by
  simp [intervalHomeoTotal, hr]

/-- The totalized coordinate map is continuous on `(c,d)` and injective there. -/
theorem intervalHomeoTotal_contOn_injOn {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) :
    ContinuousOn (intervalHomeoTotal hab hcd e) (Ioo c d) ∧
      InjOn (intervalHomeoTotal hab hcd e) (Ioo c d) := by
  have hcont : ContinuousOn (intervalHomeoTotal hab hcd e) (Ioo c d) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hpt : (Ioo c d).domRestrict (intervalHomeoTotal hab hcd e) =
        (fun x : {x : ℝ // x ∈ Ioo c d} => (e x : ℝ)) := by
      funext x
      dsimp [Set.domRestrict, intervalHomeoTotal]
      simp [x.2]
    rw [hpt]
    exact Continuous.subtype_val e.continuous
  have hinj : InjOn (intervalHomeoTotal hab hcd e) (Ioo c d) := by
    intro x hx y hy hxy
    have hx1 := intervalHomeoTotal_eq hab hcd e hx
    have hy1 := intervalHomeoTotal_eq hab hcd e hy
    have heq : (e ⟨x, hx⟩ : ℝ) = (e ⟨y, hy⟩ : ℝ) := by
      rw [← hx1, ← hy1]
      exact hxy
    have heqJ : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      exact heq
    have : (⟨x, hx⟩ : {r : ℝ // r ∈ Ioo c d}) = ⟨y, hy⟩ := e.injective heqJ
    exact congrArg Subtype.val this
  exact ⟨hcont, hinj⟩

/-- A homeo between open intervals of ℝ is strictly monotone or antitone (the
coordinate map, increasing or decreasing). -/
theorem intervalHomeo_coord_strictMono_or_anti {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) :
    StrictMono (fun x : ({x : ℝ // x ∈ Ioo c d}) => (e x : ℝ)) ∨
    StrictAnti (fun x : ({x : ℝ // x ∈ Ioo c d}) => (e x : ℝ)) := by
  have hci := intervalHomeoTotal_contOn_injOn hab hcd e
  have hma : StrictMonoOn (intervalHomeoTotal hab hcd e) (Ioo c d) ∨
      StrictAntiOn (intervalHomeoTotal hab hcd e) (Ioo c d) :=
    ContinuousOn.strictMonoOn_of_injOn_Ioo hcd hci.1 hci.2
  rcases hma with hm | ha
  · left
    intro x y hxy
    have hx1 := intervalHomeoTotal_eq hab hcd e x.2
    have hy1 := intervalHomeoTotal_eq hab hcd e y.2
    have hlt := hm x.2 y.2 hxy
    rw [hx1, hy1] at hlt
    exact hlt
  · right
    intro x y hxy
    have hx1 := intervalHomeoTotal_eq hab hcd e x.2
    have hy1 := intervalHomeoTotal_eq hab hcd e y.2
    have hlt := ha x.2 y.2 hxy
    rw [hx1, hy1] at hlt
    exact hlt


/-- **End correspondence (left end)**: a homeo between open intervals maps the
left end of the domain to the left end of the range (strictly increasing case)
or to the right end (strictly decreasing case).  Formally: as `t → c⁺`, the
coordinate `(e t : ℝ)` is eventually below `a + ε` (increasing) or above
`b − ε` (decreasing). -/
theorem intervalHomeo_left_end_reaches_endpoint {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
       ∀ t : {x : ℝ // x ∈ Ioo c d}, (t : ℝ) < c + δ → (e t : ℝ) < a + ε) ∨
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
       ∀ t : {x : ℝ // x ∈ Ioo c d}, (t : ℝ) < c + δ → b - ε < (e t : ℝ)) := by
  rcases intervalHomeo_coord_strictMono_or_anti hab hcd e with hm | ha
  · left
    intro ε hε
    by_cases hge : b - a ≤ ε
    · refine ⟨d - c, sub_pos.mpr hcd, ?_⟩
      intro t ht
      have hltb : (e t : ℝ) < b := (e t).2.2
      have hbe : b ≤ a + ε := by linarith
      linarith
    · have hlt : a + ε < b := by linarith
      let y : {x : ℝ // x ∈ Ioo a b} := ⟨a + ε, ⟨by linarith, hlt⟩⟩
      let t₀ : {x : ℝ // x ∈ Ioo c d} := e.symm y
      refine ⟨(t₀ : ℝ) - c, ?_, ?_⟩
      · have hc : c < (t₀ : ℝ) := t₀.2.1
        linarith
      · intro t ht
        have htlt : (t : ℝ) < (t₀ : ℝ) := by
          dsimp [t₀]
          linarith
        have hmono : (e t : ℝ) < (e t₀ : ℝ) := hm htlt
        have heq : (e t₀ : ℝ) = a + ε := by
          dsimp [t₀, y]
          exact congrArg (fun z : {x : ℝ // x ∈ Ioo a b} => (z : ℝ)) (e.apply_symm_apply y)
        rw [heq] at hmono
        exact hmono
  · right
    intro ε hε
    by_cases hge : b - a ≤ ε
    · refine ⟨d - c, sub_pos.mpr hcd, ?_⟩
      intro t ht
      have hgta : a < (e t : ℝ) := (e t).2.1
      have hbe : b - ε ≤ a := by linarith
      linarith
    · have hlt : a < b - ε := by linarith
      let y : {x : ℝ // x ∈ Ioo a b} := ⟨b - ε, ⟨hlt, by linarith⟩⟩
      let t₀ : {x : ℝ // x ∈ Ioo c d} := e.symm y
      refine ⟨(t₀ : ℝ) - c, ?_, ?_⟩
      · have hc : c < (t₀ : ℝ) := t₀.2.1
        linarith
      · intro t ht
        have htlt : (t : ℝ) < (t₀ : ℝ) := by
          dsimp [t₀]
          linarith
        have hanti : (e t₀ : ℝ) < (e t : ℝ) := ha htlt
        have heq : (e t₀ : ℝ) = b - ε := by
          dsimp [t₀, y]
          exact congrArg (fun z : {x : ℝ // x ∈ Ioo a b} => (z : ℝ)) (e.apply_symm_apply y)
        rw [heq] at hanti
        exact hanti

/-- The order-reversing reflection of the interval `(c,d)`. -/
noncomputable def intervalReflection (c d : ℝ) : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ
    ({x : ℝ // x ∈ Ioo c d}) := by
  let I := {x : ℝ // x ∈ Ioo c d}
  let F : I → I := fun x => ⟨c + d - (x : ℝ), by
    rcases x.2 with ⟨h1, h2⟩
    constructor <;> linarith⟩
  let G : I → I := fun x => ⟨c + d - (x : ℝ), by
    rcases x.2 with ⟨h1, h2⟩
    constructor <;> linarith⟩
  have hFG : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    ring
  have hGF : Function.RightInverse G F := by
    intro x
    apply Subtype.ext
    dsimp [F, G]
    ring
  have hFc : Continuous F := by
    dsimp [F]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  have hGc : Continuous G := by
    dsimp [G]
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_const.sub continuous_subtype_val
  let e : I ≃ I := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  exact Homeomorph.mk e hFc hGc

theorem intervalReflection_apply (c d : ℝ) (t : {x : ℝ // x ∈ Ioo c d}) :
    ((intervalReflection c d t) : ℝ) = c + d - (t : ℝ) := by
  rfl

theorem intervalReflection_involutive (c d : ℝ) (t : {x : ℝ // x ∈ Ioo c d}) :
    intervalReflection c d (intervalReflection c d t) = t := by
  apply (intervalReflection c d).injective
  apply Subtype.ext
  simp [intervalReflection_apply]

/-- **End correspondence (right end)**: as `t → d⁻`, the coordinate `(e t : ℝ)`
is eventually above `b − ε` (strictly increasing case) or below `a + ε`
(strictly decreasing case). -/
theorem intervalHomeo_right_end_reaches_endpoint {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b})) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
       ∀ t : {x : ℝ // x ∈ Ioo c d}, d - δ < (t : ℝ) → b - ε < (e t : ℝ)) ∨
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
       ∀ t : {x : ℝ // x ∈ Ioo c d}, d - δ < (t : ℝ) → (e t : ℝ) < a + ε) := by
  let ρ : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo c d}) := intervalReflection c d
  let eρ : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}) := ρ.trans e
  rcases intervalHomeo_left_end_reaches_endpoint hab hcd eρ with hl | hr
  · right
    intro ε hε
    rcases hl ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hρt : ((ρ t : {x : ℝ // x ∈ Ioo c d}) : ℝ) < c + δ := by
      have ht' : d - δ < (t : ℝ) := ht
      rw [intervalReflection_apply c d t]
      linarith
    have hval := hδ (ρ t) hρt
    have heq : (eρ (ρ t) : ℝ) = (e t : ℝ) := by
      have hρρ : ρ (ρ t) = t := intervalReflection_involutive c d t
      dsimp [eρ]
      rw [hρρ]
    rwa [heq] at hval
  · left
    intro ε hε
    rcases hr ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hρt : ((ρ t : {x : ℝ // x ∈ Ioo c d}) : ℝ) < c + δ := by
      rw [intervalReflection_apply c d t]
      linarith
    have hval := hδ (ρ t) hρt
    have heq : (eρ (ρ t) : ℝ) = (e t : ℝ) := by
      have hρρ : ρ (ρ t) = t := intervalReflection_involutive c d t
      dsimp [eρ]
      rw [hρρ]
    rwa [heq] at hval

/-- **Chart-orientation flip, coordinate level (S181)**: reflect the DOMAIN
coordinate of an interval homeo about the midpoint of `(0,1)`.  The
order-reversing map `s ↦ 1 − s` sends `(1−d, 1−c)`-coordinates to
`(c,d)`-coordinates (`reflectCoord`), and composing a DECREASING interval
homeo `e : (c,d) ≃ₜ (a,b)` (left end → `b`, right end → `a`) with it
produces a map with the INCREASING end behavior (new left end `(1−d)⁺` →
`a`, new right end `(1−c)⁻` → `b`).  This is the pure-coordinate core of
the S181 chart-orientation lemma: reversing a chart's orientation (its
coordinate reflection) turns a `TransitionDecreasing` transition into a
`TransitionIncreasing` one.

`reflectCoord` reflects the coordinate of an interval-type point:
`(1−d, 1−c)`-coordinates map to `(c,d)`-coordinates by `s ↦ 1 − s`. -/
noncomputable def reflectCoord (c d : ℝ) (t : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)}) :
    {x : ℝ // x ∈ Ioo c d} := by
  have h1 : 1 - d < (t : ℝ) := t.2.1
  have h2 : (t : ℝ) < 1 - c := t.2.2
  refine ⟨1 - (t : ℝ), ?_⟩
  constructor
  · linarith
  · linarith

/-- Value lemma for `reflectCoord`. -/
theorem reflectCoord_val (c d : ℝ) (t : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)}) :
    ((reflectCoord c d t : {x : ℝ // x ∈ Ioo c d}) : ℝ) = 1 - (t : ℝ) := by
  rfl

/-- **Coordinate core of the orientation flip**: a homeo `e : (c,d) ≃ₜ (a,b)`
with the DECREASING end behavior becomes INCREASING after precomposition
with `reflectCoord c d` — left end `(1−d)⁺` maps near `a`, right end
`(1−c)⁻` maps near `b`. -/
theorem increasing_ends_after_reflection {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}))
    (hdec : (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {x : ℝ // x ∈ Ioo c d}, (s : ℝ) < c + δ → b - ε < (e s : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s : {x : ℝ // x ∈ Ioo c d}, d - δ < (s : ℝ) → (e s : ℝ) < a + ε)) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ t : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)}, (t : ℝ) < (1 - d) + δ →
          (e (reflectCoord c d t) : ℝ) < a + ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ t : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)}, (1 - c) - δ < (t : ℝ) →
          b - ε < (e (reflectCoord c d t) : ℝ)) := by
  constructor
  · intro ε hε
    rcases hdec.2 ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hs : d - δ < ((reflectCoord c d t : {x : ℝ // x ∈ Ioo c d}) : ℝ) := by
      rw [reflectCoord_val]
      linarith
    exact hδ (reflectCoord c d t) hs
  · intro ε hε
    rcases hdec.1 ε hε with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hs : ((reflectCoord c d t : {x : ℝ // x ∈ Ioo c d}) : ℝ) < c + δ := by
      rw [reflectCoord_val]
      linarith
    exact hδ (reflectCoord c d t) hs
end LeanEval.KnotTheory.Quadrisecant

