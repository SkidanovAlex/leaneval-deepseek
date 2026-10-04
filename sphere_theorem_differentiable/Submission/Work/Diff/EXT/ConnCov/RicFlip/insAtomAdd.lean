import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit
import Submission.Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM_addArg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.ConnCov.RicFlip.insAtomAdd`

**The additivity of the `δ`-atom in the reshuffled `(ord + 2)`-tuple form.**

`deltaTowerM G t ord` — the moving `δ`-tower `∇^{G t, ord}(∇^{G t} − ∇^{G 0})` — is a vector-valued
`(1,2)`-tensor with `ord` derivative slots and two section slots.  `deltaTowerM_addArg` proves that it
is additive in **each of its `ord + 2` slots separately** (on smooth fields).

The present lemma is the *reshuffled* form of that statement that the one-atom substitution calculus
consumes (`TermCalcMain.hatom_add_form`): the `ord + 2` slots are packaged into the single
`(ord + 2)`-tuple `v` (first `ord` entries = derivative slots via `Fin.castAdd 2`, last two entries
= the two section slots via `Fin.natAdd ord`), and one asks that replacing the `j`-th entry of `v` by
`W + W'` splits the tower into its value at `W` plus its value at `W'`.

The proof is a three-way splitting of `j ∈ Fin (ord + 2)` (`Fin.addCases` for `j < ord`, and then
`j = ord`, `j = ord + 1` for the two section slots) followed by the corresponding conjunct of
`deltaTowerM_addArg`; the only content of the bookkeeping is that `Function.update` at a slot of the
`(ord+2)`-tuple commutes with the projection onto the `ord` derivative slots and onto the two section
slots, which is the collection of `Function.update` / `Fin.castAdd` / `Fin.natAdd` lemmas below.
-/

namespace Work.Diff.EXT.ConnCov.RicFlip

/-! ## The `Fin`-bookkeeping for `Function.update` versus the projection to the slots -/

/-- Replacing the `l₀`-th of the first `k` entries of a `(k+2)`-tuple, then projecting onto the
first `k` entries, is the same as replacing the `l₀`-th entry of the projected `k`-tuple. -/
lemma insAtomAdd_upd_comp_castAdd {k : ℕ} {X : Type*} (v : Fin (k+2) → X) (l₀ : Fin k) (w : X) :
    (fun l : Fin k => (Function.update v (Fin.castAdd 2 l₀) w) (Fin.castAdd 2 l))
      = Function.update (fun l : Fin k => v (Fin.castAdd 2 l)) l₀ w := by
  funext l
  rw [Function.update_apply, Function.update_apply]
  by_cases h : l = l₀
  · subst h; simp
  · have h' : Fin.castAdd 2 l ≠ Fin.castAdd 2 l₀ :=
      fun hc => h ((Fin.castAdd_inj (n := 2)).mp hc)
    simp [h, h']

/-- Replacing the `l₀`-th of the first `k` entries of a `(k+2)`-tuple does not change the entry at
`Fin.natAdd k i`. -/
lemma insAtomAdd_upd_apply_castAdd_natAdd {k : ℕ} {X : Type*} (v : Fin (k+2) → X) (l₀ : Fin k)
    (i : Fin 2) (w : X) :
    (Function.update v (Fin.castAdd 2 l₀) w) (Fin.natAdd k i) = v (Fin.natAdd k i) := by
  apply Function.update_of_ne
  intro hc
  have h1 : (↑(Fin.natAdd k i) : ℕ) = ↑(Fin.castAdd 2 l₀) := congrArg Fin.val hc
  rw [Fin.val_castAdd, Fin.val_natAdd] at h1
  have h2 := l₀.isLt
  omega

/-- Replacing one of the last two entries of a `(k+2)`-tuple does not change the projection onto the
first `k` entries. -/
lemma insAtomAdd_upd_comp_natAdd {k : ℕ} {X : Type*} (v : Fin (k+2) → X) (i : Fin 2) (w : X) :
    (fun l : Fin k => (Function.update v (Fin.natAdd k i) w) (Fin.castAdd 2 l))
      = fun l : Fin k => v (Fin.castAdd 2 l) := by
  funext l
  apply Function.update_of_ne
  intro hc
  have h1 : (↑(Fin.castAdd 2 l) : ℕ) = ↑(Fin.natAdd k i) := congrArg Fin.val hc
  rw [Fin.val_castAdd, Fin.val_natAdd] at h1
  have h2 := l.isLt
  omega

/-- Replacing the entry at `Fin.natAdd k i` by `w` gives `w` there. -/
lemma insAtomAdd_upd_apply_natAdd_natAdd_self {k : ℕ} {X : Type*} (v : Fin (k+2) → X) (i : Fin 2)
    (w : X) : (Function.update v (Fin.natAdd k i) w) (Fin.natAdd k i) = w :=
  Function.update_self _ _ _

/-- Replacing the entry at `Fin.natAdd k i` by `w` does not change the entry at `Fin.natAdd k j`,
for `j ≠ i`. -/
lemma insAtomAdd_upd_apply_natAdd_natAdd_ne {k : ℕ} {X : Type*} (v : Fin (k+2) → X) {i j : Fin 2}
    (h : j ≠ i) (w : X) :
    (Function.update v (Fin.natAdd k i) w) (Fin.natAdd k j) = v (Fin.natAdd k j) := by
  apply Function.update_of_ne
  intro hc
  refine h (Fin.ext ?_)
  have h1 : (↑(Fin.natAdd k j) : ℕ) = ↑(Fin.natAdd k i) := congrArg Fin.val hc
  rw [Fin.val_natAdd, Fin.val_natAdd] at h1
  omega

/-- **The `δ`-atom's additivity in the reshuffled `(ord + 2)`-tuple form.**  This is the first
conjunct of `deltaTowerM_addArg` after splitting the slot `j` into the three cases
`j = l.castAdd 2` (`l : Fin ord`), `j = ord` and `j = ord + 1`. -/
theorem insAtomAdd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (ord : ℕ)
    (j : Fin (ord + 2))
    (v : Fin (ord + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (W W' : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (hv : ∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) (hW : Work.Diff.EXT.ATower.SmE I M W)
    (hW' : Work.Diff.EXT.ATower.SmE I M W') :
    Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t ord
        (fun l : Fin ord => (Function.update v j (W + W')) (Fin.castAdd 2 l))
        ((Function.update v j (W + W')) (Fin.natAdd ord 0))
        ((Function.update v j (W + W')) (Fin.natAdd ord 1))
      = Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t ord
          (fun l : Fin ord => (Function.update v j W) (Fin.castAdd 2 l))
          ((Function.update v j W) (Fin.natAdd ord 0)) ((Function.update v j W) (Fin.natAdd ord 1))
        + Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t ord
            (fun l : Fin ord => (Function.update v j W') (Fin.castAdd 2 l))
            ((Function.update v j W') (Fin.natAdd ord 0))
            ((Function.update v j W') (Fin.natAdd ord 1)) := by
  have H := deltaTowerM_addArg (I := I) (M := M) hLC G t ord
  obtain ⟨H1, H2, H3⟩ := H
  -- split `j : Fin (ord + 2)` into the `ord` derivative slots and the two section slots
  refine Fin.addCases (m := ord) (n := 2) (fun l => ?_) (fun i => ?_) j
  · -- `j = Fin.castAdd 2 l`: a derivative slot — use the additivity in that slot
    rw [insAtomAdd_upd_comp_castAdd v l (W + W'), insAtomAdd_upd_comp_castAdd v l W,
      insAtomAdd_upd_comp_castAdd v l W',
      insAtomAdd_upd_apply_castAdd_natAdd v l 0 (W + W'),
      insAtomAdd_upd_apply_castAdd_natAdd v l 0 W,
      insAtomAdd_upd_apply_castAdd_natAdd v l 0 W',
      insAtomAdd_upd_apply_castAdd_natAdd v l 1 (W + W'),
      insAtomAdd_upd_apply_castAdd_natAdd v l 1 W,
      insAtomAdd_upd_apply_castAdd_natAdd v l 1 W']
    funext x
    simp only [Pi.add_apply]
    exact H1 l (fun l' => v (Fin.castAdd 2 l')) W W' (v (Fin.natAdd ord 0)) (v (Fin.natAdd ord 1))
      (fun i => hv (Fin.castAdd 2 i)) hW hW' (hv (Fin.natAdd ord 0)) (hv (Fin.natAdd ord 1)) x
  · -- `j = Fin.natAdd ord i`: a section slot
    have hi : i = 0 ∨ i = 1 := by revert i; decide
    rcases hi with h | h
    · -- `j = ord`: the first section slot — use the additivity in `A`
      rw [h,
        insAtomAdd_upd_comp_natAdd v 0 (W + W'), insAtomAdd_upd_comp_natAdd v 0 W,
        insAtomAdd_upd_comp_natAdd v 0 W',
        insAtomAdd_upd_apply_natAdd_natAdd_self v 0 (W + W'),
        insAtomAdd_upd_apply_natAdd_natAdd_self v 0 W,
        insAtomAdd_upd_apply_natAdd_natAdd_self v 0 W',
        insAtomAdd_upd_apply_natAdd_natAdd_ne (v := v) (i := 0) (j := 1) (by decide) (W + W'),
        insAtomAdd_upd_apply_natAdd_natAdd_ne (v := v) (i := 0) (j := 1) (by decide) W,
        insAtomAdd_upd_apply_natAdd_natAdd_ne (v := v) (i := 0) (j := 1) (by decide) W']
      funext x
      simp only [Pi.add_apply]
      exact H2 (fun l' => v (Fin.castAdd 2 l')) W W' (v (Fin.natAdd ord 1))
        (fun i => hv (Fin.castAdd 2 i)) hW hW' (hv (Fin.natAdd ord 1)) x
    · -- `j = ord + 1`: the second section slot — use the additivity in `B`
      rw [h,
        insAtomAdd_upd_comp_natAdd v 1 (W + W'), insAtomAdd_upd_comp_natAdd v 1 W,
        insAtomAdd_upd_comp_natAdd v 1 W',
        insAtomAdd_upd_apply_natAdd_natAdd_ne (v := v) (i := 1) (j := 0) (by decide) (W + W'),
        insAtomAdd_upd_apply_natAdd_natAdd_ne (v := v) (i := 1) (j := 0) (by decide) W,
        insAtomAdd_upd_apply_natAdd_natAdd_ne (v := v) (i := 1) (j := 0) (by decide) W',
        insAtomAdd_upd_apply_natAdd_natAdd_self v 1 (W + W'),
        insAtomAdd_upd_apply_natAdd_natAdd_self v 1 W,
        insAtomAdd_upd_apply_natAdd_natAdd_self v 1 W']
      funext x
      simp only [Pi.add_apply]
      exact H3 (fun l' => v (Fin.castAdd 2 l')) (v (Fin.natAdd ord 0)) W W'
        (fun i => hv (Fin.castAdd 2 i)) (hv (Fin.natAdd ord 0)) hW hW' x

end Work.Diff.EXT.ConnCov.RicFlip
