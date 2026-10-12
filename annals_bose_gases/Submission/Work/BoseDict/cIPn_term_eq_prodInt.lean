import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `cIPn` term identity: splitting off one particle's slot

The box creation `boxCreOf` is the *symmetrised* sum `Σ_j η_w(x_j) Θ(x ∖ j)`, so the
cross term `⟨Θ, boxCreOf e w d Θ'⟩` of a symmetric `Θ` equals `(d+1)` times the same
pairing with a *single* slot selected.  To move from the `(d+1)`-particle integral to that
single-slot form one needs the change of variables `x ↦ (x j, x ∖ j)`; the target lemma is
the resulting identity

  `∫ x, conj(Θ x) * (η_w(x j) * Θ'(x ∖ j)) = ∫ p : Sp × Xn d, η_w(p.1) * conj(Θ (cons p.1 p.2)) * Θ' p.2`,

which holds because `p ↦ Fin.insertNth j p.1 p.2` is measure preserving (`Xn (d+1)` is a
product of `d+1` copies of `Sp`) and because the *symmetric* `Θ` cannot distinguish
`insertNth j z y` from `cons z y` — the two differ by the coordinate permutation of
`Fin (d+1)` that cyclically shifts the block `{0, …, j}` down by one.

## Contents

* `integral_insertNth_aux` — the change of variables (the measurable equivalence
  `MeasurableEquiv.piFinSuccAbove`, which is measure preserving by
  `MeasureTheory.volume_preserving_piFinSuccAbove`);
* `Theta_insertNth_eq_cons` — the pointwise identity `Θ (insertNth j z y) = Θ (cons z y)`
  for permutation-invariant `Θ`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Change of variables: the measurable equivalence `Xn (d+1) ≃ᵐ Sp × Xn d` given by
`x ↦ (x j, x ∖ j)` (whose inverse is `p ↦ Fin.insertNth j p.1 p.2`) is measure preserving,
so `∫ p, g (insertNth j p.1 p.2) = ∫ x, g x`. -/
private lemma integral_insertNth_aux {d : ℕ} (j : Fin (d + 1)) (g : Xn (d + 1) → ℂ) :
    ∫ p : Sp × Xn d, g (Fin.insertNth j p.1 p.2) = ∫ x : Xn (d + 1), g x := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Sp) j with he
  have hpt : ∀ p : Sp × Xn d, e.symm p = Fin.insertNth j p.1 p.2 := by
    intro p
    rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact funext (fun i => Fin.insertNthEquiv_apply _ _ _ i)
  have hmp : MeasurePreserving e.symm :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => Sp) j).symm
  have h' : (∫ p : Sp × Xn d, g (e.symm p)) = ∫ x : Xn (d + 1), g x :=
    hmp.integral_comp' g
  rw [show (fun p : Sp × Xn d => g (Fin.insertNth j p.1 p.2)) = (fun p => g (e.symm p))
      from funext (fun p => by rw [hpt p])]
  exact h'

/-- The coordinate permutation `σ` of `Fin (d+1)` with `σ j = 0` and
`σ (j.succAbove i) = i.succ` (the cyclic shift of the block `{0, …, j}`), built as the
inverse of `ρ : 0 ↦ j`, `i.succ ↦ j.succAbove i`.  Its defining property: inserting at `j`
is the same as inserting at `0` and then reindexing by `σ`. -/
private lemma Theta_insertNth_eq_cons {d : ℕ} (j : Fin (d + 1)) (Θ : Xn (d + 1) → ℂ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Xn (d + 1)), Θ (x ∘ σ) = Θ x) :
    ∀ (z : Sp) (y : Xn d), Θ (Fin.insertNth j z y) = Θ (Fin.cons z y) := by
  set rho : Fin (d + 1) → Fin (d + 1) :=
    Fin.insertNth (0 : Fin (d + 1)) j (fun i : Fin d => Fin.succAbove j i) with hrho
  set sig : Fin (d + 1) → Fin (d + 1) :=
    Fin.insertNth j (0 : Fin (d + 1)) (Fin.succ : Fin d → Fin (d + 1)) with hsig
  have hsig_j : sig j = 0 := by
    rw [hsig]
    exact Fin.insertNth_apply_same (α := fun _ : Fin (d + 1) => Fin (d + 1)) j (0 : Fin (d + 1))
      (Fin.succ : Fin d → Fin (d + 1))
  have hsig_sa : ∀ i : Fin d, sig (Fin.succAbove j i) = Fin.succ i := by
    intro i
    rw [hsig]
    exact Fin.insertNth_apply_succAbove (α := fun _ : Fin (d + 1) => Fin (d + 1)) j (0 : Fin (d + 1))
      (Fin.succ : Fin d → Fin (d + 1)) i
  have hrho_0 : rho 0 = j := by
    rw [hrho]
    exact Fin.insertNth_apply_same (α := fun _ : Fin (d + 1) => Fin (d + 1)) (0 : Fin (d + 1)) j
      (fun i : Fin d => Fin.succAbove j i)
  have hrho_s : ∀ i : Fin d, rho (Fin.succ i) = Fin.succAbove j i := by
    intro i
    rw [hrho]
    exact Fin.insertNth_apply_succAbove (α := fun _ : Fin (d + 1) => Fin (d + 1)) (0 : Fin (d + 1)) j
      (fun k : Fin d => Fin.succAbove j k) i
  have hleft : Function.LeftInverse sig rho := by
    intro k
    revert k
    refine (Fin.forall_iff_succAbove (0 : Fin (d + 1))).mpr ⟨?_, ?_⟩
    · rw [hrho_0, hsig_j]
    · intro i
      rw [Fin.zero_succAbove, hrho_s i, hsig_sa i]
  have hright : Function.RightInverse sig rho := by
    intro k
    revert k
    refine (Fin.forall_iff_succAbove j).mpr ⟨?_, ?_⟩
    · rw [hsig_j, hrho_0]
    · intro i
      rw [hsig_sa i, hrho_s i]
  have hbij : Function.Bijective sig :=
    Function.bijective_iff_has_inverse.mpr ⟨rho, hright, hleft⟩
  intro z y
  set σ : Equiv.Perm (Fin (d + 1)) := Equiv.ofBijective sig hbij with hσdef
  have hσ : ∀ k : Fin (d + 1), σ k = sig k := by
    intro k
    rw [hσdef]
    exact Equiv.ofBijective_apply sig hbij k
  have hcomp : (Fin.cons z y) ∘ σ = Fin.insertNth j z y := by
    funext k
    revert k
    refine (Fin.forall_iff_succAbove j).mpr ⟨?_, ?_⟩
    · rw [Function.comp_apply, hσ j, hsig_j, Fin.cons_zero]
      exact (Fin.insertNth_apply_same (α := fun _ : Fin (d + 1) => Sp) j z y).symm
    · intro i
      rw [Function.comp_apply, hσ (Fin.succAbove j i), hsig_sa i, Fin.cons_succ]
      exact (Fin.insertNth_apply_succAbove (α := fun _ : Fin (d + 1) => Sp) j z y i).symm
  rw [← hcomp]
  exact hΘsym σ (Fin.cons z y)

theorem cIPn_term_eq_prodInt {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (w : Fin m → ℝ) (j : Fin (d + 1))
    (Θ : Work.BoseDict.Xn (d + 1) → ℂ) (Θ' : Work.BoseDict.Xn d → ℂ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)), Θ (x ∘ σ) = Θ x) :
    ∫ x : Work.BoseDict.Xn (d + 1),
        (starRingEnd ℂ) (Θ x) * (Work.BoseDict.etaOf e w (x j) * Θ' (fun i : Fin d => x (Fin.succAbove j i)))
      = ∫ p : Work.BoseDict.Sp × Work.BoseDict.Xn d,
          Work.BoseDict.etaOf e w p.1 * (starRingEnd ℂ) (Θ (Fin.cons p.1 p.2)) * Θ' p.2 := by
  have hkey := Theta_insertNth_eq_cons (d := d) j Θ hΘsym
  refine (integral_insertNth_aux j (fun x : Xn (d + 1) =>
      (starRingEnd ℂ) (Θ x) * (etaOf e w (x j) * Θ' (fun i : Fin d => x (Fin.succAbove j i))))).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp only
  have hfun : (fun i : Fin d =>
        (Fin.insertNth (α := fun _ : Fin (d + 1) => Sp) j p.1 p.2) (Fin.succAbove j i)) = p.2 :=
    funext (fun i => Fin.insertNth_apply_succAbove (α := fun _ : Fin (d + 1) => Sp) j p.1 p.2 i)
  rw [Fin.insertNth_apply_same (α := fun _ : Fin (d + 1) => Sp) j p.1 p.2, hfun, hkey p.1 p.2]
  ring

end Work.BoseDict
