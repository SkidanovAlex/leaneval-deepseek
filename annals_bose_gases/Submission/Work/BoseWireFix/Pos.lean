import ChallengeDeps
import Submission.Work.BoseWire.Consumers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseWireFix/Pos` — the box input with the scattering solution *universally
quantified*

This module carries the definition and the basic API of the wire's input predicate
`Work.BoseWireFix.LHYBoxBPos`, the `∀ h`-form of `Work.BoseWire.LHYBoxBInput`
(`Submission/Work/BoseWire/Consumers.lean`):

    LHYBoxBInput  v := ∃ h : ScatSol v, ∃ η₀ C, 1/2000 < η₀ ∧ η₀ ≤ 1/2 ∧ 0 ≤ C
                                          ∧ LHYBoxB v h η₀ C
    LHYBoxBPos    v := ∀ h : ScatSol v, 0 < a v → ∃ η₀ C, (same side conditions, same LHYBoxB)

**Why the second form is the right one** (audit item 2 of
`Submission/Work/BOSE_INTEGRATION_AUDIT.md` §4).  The only chain that has ever produced
FS `thm:LHY-Box` on the box is `Work.BoseFixGlue.Ports.LHYBoxB_of_grading`, whose signature is

    … (hav : 0 < BoseGases.a v) … (hg : NodeB2gB v h J J') (hr : NodeRestrictedB v h J' η₀ C) :
      LHYBoxB v h η₀ (C + 1)

— i.e. it is stated for a *general* scattering solution `h` and *requires* `0 < a v`.  So the
natural output of the B-side is a function of `(h, hav)`, not a bundle `∃ h`.  The bundle
`LHYBoxBInput` can only be *completed* if one can first find a witness `h : ScatSol v`, i.e. by
proving FS's T1 (existence of a radial scattering solution, the open
`Submission.ScatFacts.exists_radial_scattering_solution`), and that step is not part of the box
theorem at all.  Since

* `0 < a v` *does* produce a witness (`a_eq_zero_of_not_exists` plus
  `ScatSol v = ∃ w, IsRadial w ∧ IsScatteringSolution w v`), and
* `0 ≤ a v` is a theorem of the challenge's hypotheses
  (`Submission.BoseGases.av_nonneg`, reproduced here as `Work.BoseWireFix.av_nonneg`),

the `∀ h`-form costs nothing and removes T1 and the T2-side bundle from the wiring entirely:
`hpres_of_LHYBoxBPos` (`Submission/Work/BoseWireFix/hpres_of_LHYBoxBPos.lean`) case-splits on
`0 < a v`, and in the `a v = 0` branch consumes the corpus's unconditional
`Submission.BoseGases.hpres_of_av_zero`.

## Conventions

* `ScatSol v = Work.UBB.ScatSol v = ∃ w, IsRadial w ∧ IsScatteringSolution w v`.
* `LHYBoxB v h η₀ C = Work.BoseBoxFix.LHYBoxB` (`BOSE_BOXNODES_LEAD.md`), FS `thm:LHY-Box`.
* the window `1/2000 < η₀ ≤ 1/2` is the one of `Work.BoseTop.HBoxGpTarget`.
* everything is `noncomputable`, `autoImplicit false`, in namespace `Work.BoseWireFix`.

## Main declarations

| name | statement |
|---|---|
| `LHYBoxBPos v` | the input predicate, `∀ h : ScatSol v, 0 < a v → ∃ η₀ C, …` |
| `LHYBoxBPos.of_LHYBoxB` | introduction from a concrete `LHYBoxB v h η₀ C` |
| `LHYBoxBPos.exists_box` | the destructor at a given `h`, `hav` |
| `LHYBoxBPos.toInput` | `LHYBoxBPos v → ScatSol v → 0 < a v → LHYBoxBInput v` (the only direction that holds: the bundle is `LHYBoxBPos` *plus* a witness) |
| `exists_scatSol_of_av_pos` | `0 < a v → ScatSol v` (T1's only useful corollary) |
| `av_nonneg` | `0 ≤ a v` under the challenge's hypotheses (copy of `Submission.BoseGases.av_nonneg`) |
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseWireFix

open _root_.BoseGases Submission.BoseGases
open Work.UBB Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The input predicate -/

/-- **The wire's input, `∀ h`-form**: for *every* scattering solution `h` of `v` and every
`0 < a v`, FS `thm:LHY-Box` (`Work.BoseBoxFix.LHYBoxB`) holds at some error exponent
`1/2000 < η₀ ≤ 1/2` and some coefficient `C ≥ 0`.

This is the form in which the B-side chain actually delivers the box theorem (see the module
comment): `Work.BoseFixGlue.Ports.LHYBoxB_of_grading` takes `h : ScatSol v` and `hav : 0 < a v`
as hypotheses.  In contrast with `Work.BoseWire.LHYBoxBInput` it does **not** assert the
existence of `h` (FS T1), so `hpres_of_LHYBoxBPos` needs no T1. -/
def LHYBoxBPos (v : ℝ³ → ℝ) : Prop :=
  ∀ h : ScatSol v, 0 < a v →
    ∃ η₀ C : ℝ, 1 / 2000 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 0 ≤ C ∧ LHYBoxB v h η₀ C

/-- Introduction form: a concrete box theorem at a fixed `h`, valid for `0 < a v`, gives the
`∀ h`-input.  (This is the shape of `LHYBoxB_of_grading`'s conclusion.) -/
lemma LHYBoxBPos.of_LHYBoxB {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hC : 0 ≤ C) (hL : LHYBoxB v h η₀ C) :
    LHYBoxBPos v :=
  fun _ _ => ⟨η₀, C, hη₀, hη₀le, hC, hL⟩

/-- The destructor at a prescribed scattering solution. -/
lemma LHYBoxBPos.exists_box {v : ℝ³ → ℝ} (hIn : LHYBoxBPos v) (h : ScatSol v) (hav : 0 < a v) :
    ∃ η₀ C : ℝ, 1 / 2000 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 0 ≤ C ∧ LHYBoxB v h η₀ C :=
  hIn h hav

/-- **`LHYBoxBPos` + a witness gives the bundled `LHYBoxBInput`.**  This is the only direction
that holds in general: the bundle `LHYBoxBInput v = ∃ h, …` is `LHYBoxBPos` *plus* FS T1. -/
lemma LHYBoxBPos.toInput {v : ℝ³ → ℝ} (hIn : LHYBoxBPos v) (h : ScatSol v) (hav : 0 < a v) :
    Work.BoseWire.LHYBoxBInput v :=
  let ⟨η₀, C, h1, h2, h3, hL⟩ := hIn h hav
  Work.BoseWire.LHYBoxBInput.of_LHYBoxB h1 h2 h3 hL

/-- `LHYBoxBPos` transfers along a pointwise equality of potentials (recorded for callers who
rewrite `v`). -/
lemma LHYBoxBPos.congr {v v' : ℝ³ → ℝ} (hvv : v = v') (h : LHYBoxBPos v) : LHYBoxBPos v' :=
  hvv ▸ h

/-! ## 2. `0 < a v` supplies a scattering solution (T1's only useful corollary) -/

/-- **A positive scattering length implies the existence of a (radial) scattering solution.**
Immediate from the definition of `a` as a `dite` on `∃ w, IsRadial w ∧ IsScatteringSolution w v`
(`Submission.ScatteringDefs.a_eq_zero_of_not_exists`): if no witness existed then `a v = 0`.

This is the *only* consequence of FS's T1 that the wiring needs, and it is free. -/
theorem exists_scatSol_of_av_pos {v : ℝ³ → ℝ} (hav : 0 < a v) : ScatSol v := by
  by_contra h
  have h0 : a v = 0 := a_eq_zero_of_not_exists v h
  rw [h0] at hav
  exact lt_irrefl 0 hav

/-- The same fact as a `Nonempty` instance-form, for callers who want to `obtain` a witness
without naming the disjunction. -/
theorem nonempty_scatSol_of_av_pos {v : ℝ³ → ℝ} (hav : 0 < a v) : Nonempty (ScatSol v) :=
  ⟨exists_scatSol_of_av_pos hav⟩

/-! ## 3. Non-negativity of the scattering length (no dependence on `Submission.lean`) -/

/-- **`0 ≤ a v` under the challenge's hypotheses on `v`.**  Verbatim the proof of
`Submission.BoseGases.av_nonneg` (the `have hav0` of `BoseGases.theorem_1_2`): in the branch
where a radial scattering solution exists, `0 ≤ a v ≤ R` is
`Submission.ScatT3.chosen_av_bounds_weak`; otherwise `a v = 0`.

This copy exists because `Submission.lean` (where the corpus's `av_nonneg` lives) is precisely the
file this area is wired into, so importing it from under `Submission/Work/…` is the one import
that must not be made; the proof is three lines and reproduced verbatim. -/
theorem av_nonneg {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hv_radial : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) : 0 ≤ a v := by
  by_cases h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ IsScatteringSolution w v
  · exact (chosen_av_bounds_weak (v := v) (R := R) hR hv_nonneg hv_radial hv_supp h).1
  · rw [a_eq_zero_of_not_exists v h]

/-- **`a v = 0` from the failure of positivity**, given the challenge's hypotheses: the
`a v ≤ 0` half is `¬(0 < a v)` and the `0 ≤ a v` half is `Work.BoseWireFix.av_nonneg`.  This is
the exact rewrite the `a v = 0` branch of `hpres_of_LHYBoxBPos` performs. -/
theorem av_eq_zero_of_not_pos {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hv_radial : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : ¬ 0 < a v) :
    a v = 0 :=
  le_antisymm (not_lt.mp hav) (av_nonneg hv_nonneg hv_radial hR hv_supp)

end Work.BoseWireFix
