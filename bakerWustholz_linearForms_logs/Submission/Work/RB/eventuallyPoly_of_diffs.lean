import Mathlib
import Submission.Work.RB.Defs
import Submission.Work.RB.faulhaber
import Submission.Work.RB.sumPoly
import Submission.Work.RB.telescope_coord0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `IsEventuallyPoly` from polynomial first differences

If every first difference `d ↦ f (d + eᵢ) - f (d)` of `f : (Fin n →₀ ℕ) → ℚ` agrees with a
polynomial on the region `{d | ∀ j, M ≤ d j}` (uniformly in `i`), then `f` itself agrees with a
polynomial on a region of that form.

The proof is by strong induction on `n`.  At the inductive step the base point is taken to be
`Finsupp.cons M d'` (coordinate `0` set to `M`).  The auxiliary function
`hfun d' := f (Finsupp.cons M d')` on `ℕ^{n}` has polynomial first differences, so it is
eventually polynomial by the induction hypothesis.  For the remaining variation in coordinate
`0`, the sum of the `0`-th differences is packaged as a polynomial by `Work.RB.sumPoly`, and
`Work.RB.telescope_coord0` identifies that sum with `f d - f (Finsupp.cons M (tail d))`.
-/

namespace Work.RB

open MvPolynomial

noncomputable section

/-! ## Elementary substitution lemmas -/

/-- Composing `eval₂Hom C g` with `eval x` is evaluating after evaluating the `g i` at `x`. -/
private lemma eval_eval₂Hom_C {σ τ : Type*} (g : σ → MvPolynomial τ ℚ) (x : τ → ℚ)
    (p : MvPolynomial σ ℚ) :
    MvPolynomial.eval x (MvPolynomial.eval₂Hom MvPolynomial.C g p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (g i)) p := by
  rw [show MvPolynomial.eval x = MvPolynomial.eval₂Hom (RingHom.id ℚ) x from rfl]
  rw [← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  rw [show (MvPolynomial.eval₂Hom (RingHom.id ℚ) x).comp MvPolynomial.C = RingHom.id ℚ by
    ext r; simp]
  rfl

/-- Prepending to a `Finsupp` along coordinate `0` commutes with the unit step in coordinate
`i`. -/
private lemma cons_add_single {m : ℕ} (M : ℕ) (d : Fin m →₀ ℕ) (i : Fin m) :
    Finsupp.cons M (d + Finsupp.single i 1) =
      Finsupp.cons M d + Finsupp.single i.succ 1 := by
  ext j
  cases j using Fin.cases with
  | zero => simp [Finsupp.add_apply]
  | succ k => simp [Finsupp.add_apply, Finsupp.single_apply]

/-- Prepending `M` to the tail of `d` is `d` with coordinate `0` overwritten by `M`. -/
private lemma cons_tail_eq {m : ℕ} (M : ℕ) (d : Fin (m + 1) →₀ ℕ) :
    Finsupp.cons M (Finsupp.tail d) =
      d - Finsupp.single 0 (d 0) + Finsupp.single 0 M := by
  ext j
  cases j using Fin.cases with
  | zero => simp [Finsupp.add_apply]
  | succ k => simp [Finsupp.add_apply, Finsupp.tail_apply]

/-- Substitution putting the constant `M` in the variable `0` and shifting the rest. -/
private def psi {m : ℕ} (M : ℕ) : Fin (m + 1) → MvPolynomial (Fin m) ℚ :=
  fun k => Fin.cases (MvPolynomial.C (M : ℚ)) (fun j => MvPolynomial.X j) k

/-- If all the first differences `d ↦ f(d + eᵢ) - f(d)` of a function `f : ℕⁿ → ℚ` agree with a
polynomial on the region where all coordinates are `≥ M` (uniformly in `i`), then `f` itself
agrees with a polynomial on a region of that form. -/
theorem eventuallyPoly_of_diffs {n : ℕ} {f : (Fin n →₀ ℕ) → ℚ}
    (h : ∃ M : ℕ, ∀ i : Fin n, ∃ Q : MvPolynomial (Fin n) ℚ,
      ∀ d : Fin n →₀ ℕ, (∀ j, M ≤ d j) →
        f (d + Finsupp.single i 1) - f d = Q.eval (fun j => (d j : ℚ))) :
    IsEventuallyPoly f := by
  suffices H : ∀ n : ℕ, ∀ f : (Fin n →₀ ℕ) → ℚ,
      (∃ M : ℕ, ∀ i : Fin n, ∃ Q : MvPolynomial (Fin n) ℚ,
        ∀ d : Fin n →₀ ℕ, (∀ j, M ≤ d j) →
          f (d + Finsupp.single i 1) - f d = Q.eval (fun j => (d j : ℚ))) →
      IsEventuallyPoly f from H n f h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f h
    rcases n with _ | m
    · -- no variables: `Fin 0 →₀ ℕ` is a single point
      refine ⟨MvPolynomial.C (f 0), 0, ?_⟩
      intro d _
      have hd0 : d = 0 := by
        ext i
        exact Fin.elim0 i
      rw [hd0, MvPolynomial.eval_C]
    · -- inductive step
      obtain ⟨M, hQ⟩ := h
      choose QQ hQQ using hQ
      let hfun : (Fin m →₀ ℕ) → ℚ := fun d' => f (Finsupp.cons M d')
      have hdiff : ∃ M' : ℕ, ∀ i : Fin m, ∃ Q : MvPolynomial (Fin m) ℚ,
          ∀ d' : Fin m →₀ ℕ, (∀ j, M' ≤ d' j) →
            hfun (d' + Finsupp.single i 1) - hfun d' = Q.eval (fun j => (d' j : ℚ)) := by
        refine ⟨M, fun i => ⟨MvPolynomial.eval₂Hom MvPolynomial.C (psi M) (QQ i.succ), ?_⟩⟩
        intro d' hd'
        have hge : ∀ j : Fin (m + 1), M ≤ Finsupp.cons M d' j := by
          intro j
          cases j using Fin.cases with
          | zero => simp
          | succ k => simpa using hd' k
        have hdiff' := hQQ i.succ (Finsupp.cons M d') hge
        have hQ'eval : (MvPolynomial.eval₂Hom MvPolynomial.C (psi M) (QQ i.succ)).eval
              (fun j => (d' j : ℚ)) =
            (QQ i.succ).eval (fun k => (Finsupp.cons M d' k : ℚ)) := by
          rw [eval_eval₂Hom_C]
          have hpsi : (fun k => MvPolynomial.eval (fun j => (d' j : ℚ)) (psi M k)) =
              (fun k => (Finsupp.cons M d' k : ℚ)) := by
            funext k
            cases k using Fin.cases with
            | zero => simp [psi, Finsupp.cons_zero]
            | succ j => simp [psi, Finsupp.cons_succ]
          rw [hpsi]
        show f (Finsupp.cons M (d' + Finsupp.single i 1)) - f (Finsupp.cons M d') =
          (MvPolynomial.eval₂Hom MvPolynomial.C (psi M) (QQ i.succ)).eval (fun j => (d' j : ℚ))
        rw [cons_add_single M d' i, hdiff', ← hQ'eval]
      obtain ⟨Ph, Nh, hPh⟩ := ih m (Nat.lt_succ_self m) hfun hdiff
      obtain ⟨sumR, hsumR⟩ := sumPoly (QQ 0) M
      refine ⟨MvPolynomial.rename Fin.succ Ph + sumR, max Nh M, ?_⟩
      intro d hd
      have hdle : ∀ j : Fin (m + 1), M ≤ d j := fun j => le_trans (le_max_right _ _) (hd j)
      have hdtail : ∀ j : Fin m, Nh ≤ Finsupp.tail d j := by
        intro j
        rw [Finsupp.tail_apply]
        exact le_trans (le_max_left _ _) (hd j.succ)
      have key1 : (MvPolynomial.rename Fin.succ Ph).eval (fun i => (d i : ℚ)) =
          Ph.eval (fun j => (Finsupp.tail d j : ℚ)) := by
        rw [MvPolynomial.eval_rename]
        congr 1
      have key2 : hfun (Finsupp.tail d) = f (Finsupp.cons M (Finsupp.tail d)) := rfl
      have key3 : Ph.eval (fun j => (Finsupp.tail d j : ℚ)) = hfun (Finsupp.tail d) :=
        (hPh (Finsupp.tail d) hdtail).symm
      have key4 : sumR.eval (fun i => (d i : ℚ)) =
          f d - f (Finsupp.cons M (Finsupp.tail d)) := by
        rw [hsumR d (hdle 0)]
        rw [cons_tail_eq M d]
        exact (telescope_coord0 f (QQ 0) M (hQQ 0) d hdle).symm
      simp only [map_add, key1, key2, key3, key4]
      ring

end

end Work.RB
