/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS_EllLimOK` — the area (1) ∧ (1a) of `Final/Defs.Inputs.core`

This is the area file for the lead's **core field (1a)**, in the form fixed by the ruling
`FTS_EllLimOK/LEAD_ellim_3a.md` (curric-46, 2026-10-10):

* the elliptic solution operator `E` of the class `C` (`Work.FTS.ClassC.ClassC`) must satisfy
  `EllLimOK α E`: it must **pass to limits** of `ℋ⁶`-bounded class-`C` sequences that converge in
  the `C⁴`-slots on the open quadrant `Qd` (the limit itself being `C⁴` on `Qd` — the extra
  hypothesis installed by the lead in `StrongEps/EpsLimit.lean`, and available to the consumer as
  `EpsLimPkg.c4`);
* the packages on the class `C` alone do **not** give it: `E` is a Hamel extension and is free off
  the class (`Obstruction.lean`, confirmed by the ruling).  Hence the area's content is

  - the *interface* (`Defs.lean`, this file, `Locality.lean`): the vocabulary of the limit process,
    the flat ("invisible") directions, and the two structural consequences of `EllLimOK`
    (`Basic.lean`);
  - the *glue* (`Glue.lean`): the ruling's proved reduction, `ExistsEllSolC ∧ EllClosed →
    ExistsEllSolCLim`, whose only analytic input is `EllClosed α Ce` — for **every** linear
    operator carrying the two packages on the class `C`, the `C²`-jets of `E (fn n)` converge on
    `Qd` to those of a `C²` solution of `f`;
  - the *obligation* itself: `EllClosed` (open; route in `LEAD_ellim_3a.md` §A: compactness from
    the package bounds, then uniqueness in the Fatou package class).

`EllClosed` is what remains open in this area; everything else here is proved and
`[propext, Classical.choice, Quot.sound]`-clean.

## The definitions of this file

`EllLimOK` is a *verbatim copy* of `Work.FTS.StrongEps.EllLimOK` (same body ⇒ definitionally
equal: `Main.Lead_EllLimOK_iff`), kept here so that the area's own modules do not have to pay for
the heavy `StrongEps` import.  `LimSeq4` bundles its hypotheses, `JConv` its conclusion,
`ClosedE`/`EllClosed`/`ExistsEllSolCLim` are the ruling's vocabulary.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The statement of the area (a verbatim copy of the lead's `EllLimOK`) -/

/-- **`E` passes to limits of `ℋ⁶`-bounded class-`C` sequences** (ruling v2 + the ruling of
2026-10-10): *verbatim copy* of `Work.FTS.StrongEps.EllLimOK`, with the `C⁴`-on-`Qd` hypothesis on
the limit.  The two definitions have the same body, hence are definitionally equal. -/
def EllLimOK (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn) (B : ℝ),
    (∀ n, Work.FTS.ClassC.ClassC α (fn n)) →
    (∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) →
    ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd →
    (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) →
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (E f) z θ))

/-! ## Convergence of `C²`-jets on the quadrant -/

/-- **Convergence of the `C²`-jets on `Qd`** (the second half of `EllLimOK`'s conclusion). -/
def JConv (Ψn : ℕ → Fn) (Ψ : Fn) : Prop :=
  ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Tendsto (fun n => Work.Spaces.mixed j i (Ψn n) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i Ψ z θ))

/-- The hypotheses of `EllLimOK` as a structure (the ruling's `LimSeq4`). -/
structure LimSeq4 (α : ℝ) (fn : ℕ → Fn) (f : Fn) : Prop where
  /-- every member of the sequence lies in the class `C` -/
  classC : ∀ n, Work.FTS.ClassC.ClassC α (fn n)
  /-- uniform `ℋ⁶`-bound -/
  bound : ∃ B : ℝ, ∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B
  /-- the limit is `C⁴` on the open quadrant -/
  c4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd
  /-- convergence of all `C⁴`-slots on the open quadrant -/
  conv : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i f z θ))

/-- `EllLimOK` in the bundled form. -/
theorem ellLimOK_iff {α : ℝ} {E : Fn → Fn} :
    EllLimOK α E ↔ ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
      Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧ JConv (fun n => E (fn n)) (E f) := by
  constructor
  · intro h fn f hL
    obtain ⟨B, hB⟩ := hL.bound
    exact h fn f B hL.classC hB hL.c4 hL.conv
  · intro h fn f B h1 h2 h3 h4
    exact h fn f ⟨h1, ⟨B, h2⟩, h3, h4⟩

/-- The unbundled reading of `EllLimOK`. -/
theorem ellLimOK_of_LimSeq4 {α : ℝ} {E : Fn → Fn} (h : EllLimOK α E)
    {fn : ℕ → Fn} {f : Fn} (hL : LimSeq4 α fn f) :
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧ JConv (fun n => E (fn n)) (E f) :=
  (ellLimOK_iff.mp h) fn f hL

/-! ## The closure obligation -/

/-- **The analytic closure of an operator** — the ruling's `ClosedE`: along every `LimSeq4`, the
`C²`-jets of `E (fn n)` converge on `Qd` to those of *some* `C²` solution of the limit profile. -/
def ClosedE (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ Ψ : Fn, Work.FTS.StrongGlobal.IsBslSolPos α f Ψ ∧
      ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd ∧ JConv (fun n => E (fn n)) Ψ

/-- **The two elliptic packages on the class `C`, at one operator** (`EllPkgGo` at level `4` and
`EllPkgK` at level `6`): the shape in which every statement of the area carries its hypothesis. -/
def HasPkg (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g, Work.FTS.ClassC.ClassC α g →
    Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)

/-- **The obligation (owner `FTS_EllLimOK`)**: every linear operator carrying the two packages on
the class `C` is closed.  This is the *only* open statement of the area. -/
def EllClosed (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ClosedE α E

/-- **The strengthened existence statement**: one `E` with the packages *and* (1a). -/
def ExistsEllSolCLim : Prop :=
  ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∃ E : Fn →ₗ[ℝ] Fn, (∀ g, Work.FTS.ClassC.ClassC α g →
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)) ∧
      EllLimOK α E

/-! ## Flat ("invisible") directions -/

/-- **`γ` is invisible to the limit process**: it vanishes identically on some *open*
neighbourhood of the open quadrant.  These are exactly the directions in which `EllLimOK` cannot
distinguish two candidate limits: replacing a limit `f` by `f + γ` changes nothing in the
hypotheses of `EllLimOK` (all mixed derivatives of the two agree on `Qd` by *locality*), while
`E (f + γ)` may differ from `E f`. -/
def QdZero (γ : Fn) : Prop :=
  ∃ V : Set (ℝ × ℝ), IsOpen V ∧ Work.Construction.Qd ⊆ V ∧ ∀ z θ, (z, θ) ∈ V → γ z θ = 0

/-- `γ` is **flat on the open quadrant up to order four**: all its mixed derivatives of total
order `≤ 4` vanish on `Qd`.  This is the weaker *jet* form of `QdZero` (`QdZero.qdFlat`). -/
def QdFlat (γ : Fn) : Prop :=
  ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Spaces.mixed j i γ z θ = 0

/-- `0` is flat on the open quadrant in every order. -/
theorem qdFlat_zero : QdFlat (0 : Fn) :=
  fun j i _ _ _ _ => by
    rw [Work.FTS.EllipticEst.mixed_zero_fun j i]
    rfl

/-- `0` is invisible to the limit process. -/
theorem qdZero_zero : QdZero (0 : Fn) :=
  ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun _ _ _ => rfl⟩

/-- The open quadrant is open. -/
theorem isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## The limit points -/

/-- The functions that arise as `LimSeq4`-limits.  `E` is a Hamel extension, so its values here
are *not* constrained by the packages; this is where `EllClosed` has to do its work. -/
def LimPoint (α : ℝ) (f : Fn) : Prop := ∃ fn : ℕ → Fn, LimSeq4 α fn f

theorem limPoint_of {α : ℝ} {fn : ℕ → Fn} {f : Fn} (h : LimSeq4 α fn f) : LimPoint α f :=
  ⟨fn, h⟩

/-! ## Two test objects for the obstruction -/

/-- `junkTheta` is `1` for `θ ∉ (0,π/2)` and `0` inside: the `θ`-junk direction.  It is `QdZero`
(it vanishes on `Qd`), hence invisible to `EllLimOK`, while it is `C⁴` on `Qd` (it is `0` there)
and **no** class-`C` profile can be nonzero there (`classC_apply_eq_zero_of_not_mem`). -/
def junkTheta : Fn := fun _ θ => if θ ∈ Set.Ioo 0 (π / 2) then 0 else 1

/-- The evaluation functional `f ↦ f z₀ θ₀` (linear). -/
def evalAt (z₀ θ₀ : ℝ) : Fn →ₗ[ℝ] ℝ where
  toFun f := f z₀ θ₀
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] theorem evalAt_apply (z₀ θ₀ : ℝ) (f : Fn) : evalAt z₀ θ₀ f = f z₀ θ₀ := rfl

/-- Every class-`C` profile vanishes at every `θ ∉ (0,π/2)` (the class field `norm` is
`normTh g = g`, and `normTh` kills those points). -/
theorem classC_apply_eq_zero_of_not_mem {α : ℝ} {g : Fn} (hg : Work.FTS.ClassC.ClassC α g)
    {z θ : ℝ} (hθ : θ ∉ Set.Ioo 0 (π / 2)) : g z θ = 0 := by
  have h := congrFun (congrFun hg.norm z) θ
  rw [← h, Work.FTS.ClassC.normTh_apply_of_not_mem hθ]

/-- `2 ∉ (0,π/2)`, so every class-`C` profile vanishes at `(z,2)`: the evaluation functional
`evalAt z 2` annihilates the whole class. -/
theorem evalAt_two_classC_eq_zero {α : ℝ} {g : Fn} (hg : Work.FTS.ClassC.ClassC α g) (z : ℝ) :
    evalAt z 2 g = 0 := by
  rw [evalAt_apply]
  exact classC_apply_eq_zero_of_not_mem hg (by
    simp only [Set.mem_Ioo, not_and_or]
    exact Or.inr (by linarith [Real.pi_lt_four]))

end Work.FTS_EllLimOK
