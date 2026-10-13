/-
  Area E7: the **geometric inputs** of BV's fiber-cutting Lemma 8, isolated as definitions, and
  the first *provable* structural facts about the fibrewise frontier of a `Good` stratum.

  The four inputs (proved elsewhere, imported here only through these `def`s so that the assembly
  can be stated without them):

  * `FrontierDrop`  — the frontier dimension drop `(★)` of `NOTES_S13_fiber_cut.md` §2;
  * `CritDrop`      — the critical-side dimension drop (`stratum_j_lt_of_subset_crit`);
  * `CritWitness`   — the critical point with a witness over a closed fibre (Claim A);
  * `ClosureProj`   — the closure trick `π(fiberClosure Y) = π(Y)`.

  The *provable* content of this file is `frontier_h_zero`: the fibrewise frontier of a `Good`
  stratum lies in the zero set `{h = 0}` of its defining equations.  This is used in every
  discussion of the frontier step (the `S`-equations vanish on the fibres of any stratum in the
  fibrewise frontier, so the whole `S'`-fibre sits in the *level set* `{h_S = 0}` and is open
  there — the "germ equality" that the frontier analysis rests on).
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.eventually_mem_fiber_of_good
import Submission.Work.WilE9.EaD.eaEval_contDiff

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped Topology
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The geometric inputs -/

/-- **The frontier dimension drop** (BV's stratifications satisfy it; the frozen `Stratum.Good`
does not encode it, which is the one genuine gap — see `NOTES_S13_fiber_cut.md`): a `Good` stratum
lying in the fibrewise frontier of another `Good` stratum has strictly larger fibre codimension. -/
def FrontierDrop : Prop :=
  ∀ (p q : ℕ) (S S' : WilkiesDesign.E.Stratum p q), S.Good → S'.Good →
    S'.X.set ⊆ WilkiesDesign.E.fiberClosure S.X.set \ S.X.set → S'.X.set.Nonempty → S.j < S'.j

/-- **The critical-side dimension drop**: a `Good` stratum `S'` contained in `critSet S l` carrying a
point whose fibre component is not the constant level set of `y_l` has strictly larger fibre
codimension.  (`Work.WilE7.stratum_j_lt_of_subset_crit` is exactly this statement.) -/
def CritDrop : Prop :=
  ∀ (p q : ℕ) (S S' : WilkiesDesign.E.Stratum p q), S.Good → S'.Good →
    ∀ (l : Fin q), S.j < q → S'.X.set ⊆ (Work.WilE7.critSet S l).set →
      (∃ z ∈ S'.X.set, ∃ w ∈ WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z),
        w ∈ connectedComponentIn (WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z))
          (WilkiesDesign.E.projSnd p q z) ∧ w l ≠ z (Work.WilE7.fibDir p q l)) →
      S.j < S'.j

/-- **Critical points with a witness over closed fibres.**  If the fibre of a `Good` stratum `S`
over `x` is closed (equivalently, by boundedness, compact) and non-empty, then some coordinate
`y_l` has a `critSet S l`-point over `x` whose fibre component contains a point with a different
`y_l`-value.  (This is the "Claim A" of `NOTES_S13_fiber_cut.md`; it is what makes the recursion
close in the non-frontier case.) -/
def CritWitness : Prop :=
  ∀ (p q : ℕ) (S : WilkiesDesign.E.Stratum p q), S.Good → S.j < q → ∀ x : Fin p → ℝ,
    x ∉ WilkiesDesign.E.projFirst p q '' (WilkiesDesign.E.fiberClosure S.X.set \ S.X.set) →
    (WilkiesDesign.E.fiber S.X.set x).Nonempty →
    ∃ (l : Fin q) (z : Fin (p + q) → ℝ), z ∈ (Work.WilE7.critSet S l).set ∧
      WilkiesDesign.E.projFirst p q z = x ∧
      ∃ w ∈ WilkiesDesign.E.fiber S.X.set x,
        w ∈ connectedComponentIn (WilkiesDesign.E.fiber S.X.set x)
          (WilkiesDesign.E.projSnd p q z) ∧ w l ≠ z (Work.WilE7.fibDir p q l)

/-- The closure trick, as a hypothesis: `π(fiberClosure X) = π(X)`. -/
def ClosureProj : Prop :=
  ∀ (n m : ℕ) (Y : Set (Fin (n + m) → ℝ)),
    WilkiesDesign.E.projFirst n m '' WilkiesDesign.E.fiberClosure Y =
      WilkiesDesign.E.projFirst n m '' Y

/-! ## The fibrewise frontier lies in the zero set of the equations

For a `Good` stratum the defining equations vanish on the whole stratum, and the fibre of the
fibrewise closure over `x` is the closure of the fibre over `x`; continuity then forces the
equations to vanish on that closure as well. -/

/-- **The fibrewise closure of a `Good` stratum lies in the zero set of its equations.** -/
theorem fiberClosure_h_zero {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good) :
    ∀ z ∈ WilkiesDesign.E.fiberClosure S.X.set, ∀ a, WilkiesDesign.E.eaEval S.X.c (S.h a) z = 0 := by
  intro z hz a
  set x : Fin p → ℝ := WilkiesDesign.E.projFirst p q z with hx
  have hzero : ∀ y ∈ WilkiesDesign.E.fiber S.X.set x,
      WilkiesDesign.E.eaEval S.X.c (S.h a) (Fin.append x y) = 0 :=
    fun y hy => (hGood (Fin.append x y) hy).1 a
  have hcont : Continuous (fun y : Fin q → ℝ =>
      WilkiesDesign.E.eaEval S.X.c (S.h a) (Fin.append x y)) :=
    (Work.WilE9.EaD.eaEval_contDiff S.X.c (S.h a)).continuous.comp
      (continuous_finAppend_right x)
  have hclosed : IsClosed {y : Fin q → ℝ |
      WilkiesDesign.E.eaEval S.X.c (S.h a) (Fin.append x y) = 0} :=
    isClosed_eq hcont continuous_const
  have hmem : WilkiesDesign.E.projSnd p q z ∈ closure (WilkiesDesign.E.fiber S.X.set x) := hz
  have h1 : closure (WilkiesDesign.E.fiber S.X.set x) ⊆ {y : Fin q → ℝ |
      WilkiesDesign.E.eaEval S.X.c (S.h a) (Fin.append x y) = 0} :=
    hclosed.closure_subset_iff.mpr hzero
  have h2 : WilkiesDesign.E.eaEval S.X.c (S.h a)
      (Fin.append x (WilkiesDesign.E.projSnd p q z)) = 0 := h1 hmem
  have happ : Fin.append x (WilkiesDesign.E.projSnd p q z) = z := by
    funext i
    refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i <;>
      simp [hx, WilkiesDesign.E.projFirst, WilkiesDesign.E.projSnd,
        Fin.append_left, Fin.append_right]
  rwa [happ] at h2

/-- **The fibrewise frontier lies in the zero set of the equations** (the special case of
`fiberClosure_h_zero` for the frontier). -/
theorem frontier_h_zero {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good) :
    ∀ z ∈ WilkiesDesign.E.fiberClosure S.X.set \ S.X.set,
      ∀ a, WilkiesDesign.E.eaEval S.X.c (S.h a) z = 0 :=
  fun z hz => fiberClosure_h_zero S hGood z hz.1

/-- The `S`-equations vanish on a stratum lying in the fibrewise frontier of `S`. -/
theorem stratum_h_zero_of_subset_frontier {p q : ℕ} {S S' : WilkiesDesign.E.Stratum p q}
    (hGood : S.Good) (hsub : S'.X.set ⊆ WilkiesDesign.E.fiberClosure S.X.set \ S.X.set) :
    ∀ z ∈ S'.X.set, ∀ a, WilkiesDesign.E.eaEval S.X.c (S.h a) z = 0 :=
  fun z hz => frontier_h_zero S hGood z (hsub hz)

/-! ## The fibres of the frontier stratum are open in the level set of `S`

Combining the previous lemma with the third clause of `Good` for `S` shows that the fibre of
`S.X.set` over `x` contains a *neighbourhood in the level set* of every one of its points: the
fibre and the level set have the same germ at every point of the fibre. -/

/-- **The fibre of a `Good` stratum is open in the level set of its equations.** -/
theorem fiber_subset_levelSet_germ {p q : ℕ} (S : WilkiesDesign.E.Stratum p q)
    (hGood : S.Good) (x : Fin p → ℝ) {y : Fin q → ℝ}
    (hy : y ∈ WilkiesDesign.E.fiber S.X.set x) :
    ∀ᶠ y' in 𝓝 y, (∀ a, WilkiesDesign.E.eaEval S.X.c (S.h a) (Fin.append x y') = 0) →
      y' ∈ WilkiesDesign.E.fiber S.X.set x :=
  eventually_mem_fiber_of_good S hGood x y hy

end Work.WilE7
