import Mathlib
import Submission.Work.Serre.SkelPi.Concat

/-!
# The telescoping identity for `qconcat`

`qconcat p F` is the iterated composition of the quotient paths `F k : p k ⟶ p (k+1)`, a path from
`p 0` to `p (Fin.last n)`.  This file proves the telescoping identity: conjugating every factor
`F k` by the paths `c k : b ⟶ p k` (i.e. replacing `F k` by `(c k) · F k · (c (k+1))⁻¹`) produces
a loop at `b` whose class, conjugated back by `c 0` and `c (Fin.last n)`, is the class of
`qconcat p F`.

The proof is by induction on `n`; the auxiliary statement `qconcat_conj` (the "conjugated" form,
which is linear in the recursive definition of `qconcat`) is the induction hypothesis and the
target follows from it by the groupoid identities
`trans_assoc`, `symm_trans`, `refl_trans`, `trans_refl`.
-/

namespace Work.Serre.SkelPi

open scoped Topology unitInterval

/-- **The conjugated form of the telescoping identity.**  The loop at `b` obtained by composing the
conjugates `(c k.castSucc) · F k · (c k.succ)⁻¹` of the `F k` is `c 0 · qconcat p F · (c (last n))⁻¹`.
This is the statement that is stable under the recursion defining `qconcat`. -/
theorem qconcat_conj {X : Type} [TopologicalSpace X] (b : X) :
    ∀ (n : ℕ) (p : Fin (n + 1) → X) (c : (k : Fin (n + 1)) → Path.Homotopic.Quotient b (p k))
      (F : (k : Fin n) → Path.Homotopic.Quotient (p k.castSucc) (p k.succ)),
      qconcat (fun _ : Fin (n + 1) => b)
          (fun k : Fin n => (c k.castSucc).trans ((F k).trans ((c k.succ).symm))) =
        (c 0).trans ((qconcat p F).trans ((c (Fin.last n)).symm)) := by
  intro n
  induction n with
  | zero =>
      intro p c F
      simp [qconcat]
  | succ n ih =>
      intro p c F
      rw [qconcat_succ]
      -- reindex the family of loops produced by the recursion so that the induction hypothesis
      -- applies (the two families differ only in the `Fin`-index `k.castSucc.succ = k.succ.castSucc`)
      have hfam : (fun k : Fin n =>
            (fun k : Fin (n+1) => (c k.castSucc).trans ((F k).trans ((c k.succ).symm))) k.castSucc)
          = (fun k : Fin n =>
            ((fun j : Fin (n+1) => c j.castSucc) k.castSucc).trans
              (((fun j : Fin n => F j.castSucc) k).trans
                (((fun j : Fin (n+1) => c j.castSucc) k.succ).symm))) := by
        funext k
        simp only [Fin.castSucc_succ]
      rw [hfam, ih (fun j : Fin (n+1) => p j.castSucc) (fun j : Fin (n+1) => c j.castSucc)
            (fun j : Fin n => F j.castSucc)]
      -- abbreviations for the groupoid computation
      set Q : Path.Homotopic.Quotient (p 0) (p ((Fin.last n).castSucc)) :=
        qconcat (fun j : Fin (n+1) => p j.castSucc) (fun j : Fin n => F j.castSucc)
      set E : Path.Homotopic.Quotient b (p ((Fin.last n).castSucc)) := c ((Fin.last n).castSucc)
      set f : Path.Homotopic.Quotient (p ((Fin.last n).castSucc)) (p ((Fin.last n).succ)) :=
        F (Fin.last n)
      set E' : Path.Homotopic.Quotient b (p ((Fin.last n).succ)) := c ((Fin.last n).succ)
      rw [qconcat_succ p F]
      show ((c 0).trans (Q.trans E.symm)).trans (E.trans (f.trans E'.symm)) =
        (c 0).trans ((Q.trans f).trans E'.symm)
      rw [Path.Homotopic.Quotient.trans_assoc (c 0) (Q.trans E.symm)
        (E.trans (f.trans E'.symm))]
      rw [Path.Homotopic.Quotient.trans_assoc Q E.symm (E.trans (f.trans E'.symm)),
        ← Path.Homotopic.Quotient.trans_assoc E.symm E (f.trans E'.symm),
        Path.Homotopic.Quotient.symm_trans E,
        Path.Homotopic.Quotient.refl_trans (f.trans E'.symm)]
      rw [Path.Homotopic.Quotient.trans_assoc Q f E'.symm]

theorem qconcat_telescope {X : Type} [TopologicalSpace X] (b : X) {n : ℕ}
    (p : Fin (n + 1) → X) (c : (k : Fin (n + 1)) → Path.Homotopic.Quotient b (p k))
    (F : (k : Fin n) → Path.Homotopic.Quotient (p k.castSucc) (p k.succ)) :
    qconcat p F =
      (c 0).symm.trans
        ((qconcat (fun _ : Fin (n + 1) => b)
          (fun k : Fin n => (c k.castSucc).trans ((F k).trans ((c k.succ).symm)))).trans
            (c (Fin.last n))) := by
  rw [qconcat_conj (X := X) b n p c F]
  have h1 : ((c 0).trans ((qconcat p F).trans ((c (Fin.last n)).symm))).trans (c (Fin.last n)) =
      (c 0).trans (qconcat p F) := by
    rw [Path.Homotopic.Quotient.trans_assoc (c 0)
      ((qconcat p F).trans ((c (Fin.last n)).symm)) (c (Fin.last n))]
    rw [Path.Homotopic.Quotient.trans_assoc (qconcat p F) ((c (Fin.last n)).symm)
        (c (Fin.last n)),
      Path.Homotopic.Quotient.symm_trans (c (Fin.last n)),
      Path.Homotopic.Quotient.trans_refl (qconcat p F)]
  rw [h1]
  have h2 : (c 0).symm.trans ((c 0).trans (qconcat p F)) = qconcat p F := by
    rw [← Path.Homotopic.Quotient.trans_assoc (c 0).symm (c 0) (qconcat p F),
      Path.Homotopic.Quotient.symm_trans (c 0),
      Path.Homotopic.Quotient.refl_trans (qconcat p F)]
  rw [h2]

end Work.Serre.SkelPi
