import Mathlib
import Submission.Work.Diff.EXT.reactBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shuffle bookkeeping of the level-`0` reaction ladder

`Work.Diff.EXT.reaction0_jets` bounds the jets of the quadratic reaction `Q(Rm)`.  Its `j`-th jet is
a sum of `2^j` *monomials*, each of which is the contraction of `∇^a Rm` with `∇^b Rm` (`a + b = j`)
in an orthonormal frame, paired with the `4 + j` entries of the tuple.

The `j`-th covariant derivative is the iteration of `Work.Diff.EXT.extStep` (`Work.Diff.EXT.jetAll`),
and each `extStep` has *two* children: the new derivative direction is inserted either into the first
or into the second factor.  The bookkeeping of the two sums is encoded by a *binary word*
`ε : Fin n → Bool`: `ε t = true` means that the `t`-th derivative went into the first factor.

The tuple of the level-`n` monomial is `Fin (4+n)`, with the convention that position `0` carries the
*newest* derivative direction, …, position `n-1` the oldest, and positions `n … n+3` the four
`reactionMap`-slots.  `sPos n` gives the latter, and `dsf n ε r` (resp. `dsg n ε r`) the position of
the `r`-th `true` (resp. `false`) entry of `ε` — i.e. the position of the `r`-th slot of the first
(resp. second) factor.

The functions are total on `ℕ` (they return a junk value past the number of entries), which keeps the
recursion equations `dsf_cons_true_succ` etc. free of dependent-type casts.
-/

namespace Work.Diff.EXT.evX

open scoped BigOperators

/-- The positions of the four `reactionMap`-slots in the level-`n` tuple. -/
noncomputable def sPos (n : ℕ) : Fin 4 → Fin (4 + n) := fun t => ⟨n + t, by have := t.isLt; omega⟩

/-- The position of the `r`-th `true` entry of the word `ε` (junk past the number of `true`s). -/
noncomputable def dsf : (n : ℕ) → (Fin n → Bool) → ℕ → Fin (4 + n)
  | 0, _, _ => ⟨0, by omega⟩
  | n + 1, ε, r =>
      if ε 0 then
        (if r = 0 then ⟨0, by omega⟩ else (dsf n (fun t => ε t.succ) (r - 1)).succ)
      else (dsf n (fun t => ε t.succ) r).succ

/-- The position of the `r`-th `false` entry of the word `ε` (junk past the number of `false`s). -/
noncomputable def dsg : (n : ℕ) → (Fin n → Bool) → ℕ → Fin (4 + n)
  | 0, _, _ => ⟨0, by omega⟩
  | n + 1, ε, r =>
      if ε 0 then (dsg n (fun t => ε t.succ) r).succ
      else (if r = 0 then ⟨0, by omega⟩ else (dsg n (fun t => ε t.succ) (r - 1)).succ)

/-- The number of `true` entries of the word `ε`. -/
noncomputable def cntT : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, ε => cntT n (fun t => ε t.succ) + (ε 0).toNat

/-- The number of `false` entries of the word `ε`. -/
noncomputable def cntF : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, ε => cntF n (fun t => ε t.succ) + (!(ε 0)).toNat

theorem cntT_succ (n : ℕ) (ε : Fin (n + 1) → Bool) :
    cntT (n + 1) ε = cntT n (fun t => ε t.succ) + (ε 0).toNat := rfl

theorem cntF_succ (n : ℕ) (ε : Fin (n + 1) → Bool) :
    cntF (n + 1) ε = cntF n (fun t => ε t.succ) + (!(ε 0)).toNat := rfl

theorem dsf_cons_true_zero (n : ℕ) (ε : Fin n → Bool) :
    dsf (n + 1) (Fin.cons true ε) 0 = (⟨0, by omega⟩ : Fin (4 + (n+1))) := by
  simp only [dsf, Fin.cons_zero, Fin.cons_succ]; simp

theorem dsf_cons_true_succ (n : ℕ) (ε : Fin n → Bool) (r : ℕ) :
    dsf (n + 1) (Fin.cons true ε) (r + 1) = (dsf n ε r).succ := by
  simp only [dsf, Fin.cons_zero, Fin.cons_succ]; simp

theorem dsf_cons_false (n : ℕ) (ε : Fin n → Bool) (r : ℕ) :
    dsf (n + 1) (Fin.cons false ε) r = (dsf n ε r).succ := by
  simp only [dsf, Fin.cons_zero, Fin.cons_succ]; simp

theorem dsg_cons_false_zero (n : ℕ) (ε : Fin n → Bool) :
    dsg (n + 1) (Fin.cons false ε) 0 = (⟨0, by omega⟩ : Fin (4 + (n+1))) := by
  simp only [dsg, Fin.cons_zero, Fin.cons_succ]; simp

theorem dsg_cons_false_succ (n : ℕ) (ε : Fin n → Bool) (r : ℕ) :
    dsg (n + 1) (Fin.cons false ε) (r + 1) = (dsg n ε r).succ := by
  simp only [dsg, Fin.cons_zero, Fin.cons_succ]; simp

theorem dsg_cons_true (n : ℕ) (ε : Fin n → Bool) (r : ℕ) :
    dsg (n + 1) (Fin.cons true ε) r = (dsg n ε r).succ := by
  simp only [dsg, Fin.cons_zero, Fin.cons_succ]; simp

theorem cntT_cons_true (n : ℕ) (ε : Fin n → Bool) :
    cntT (n + 1) (Fin.cons true ε) = cntT n ε + 1 := rfl

theorem cntT_cons_false (n : ℕ) (ε : Fin n → Bool) :
    cntT (n + 1) (Fin.cons false ε) = cntT n ε := rfl

theorem cntF_cons_true (n : ℕ) (ε : Fin n → Bool) :
    cntF (n + 1) (Fin.cons true ε) = cntF n ε := rfl

theorem cntF_cons_false (n : ℕ) (ε : Fin n → Bool) :
    cntF (n + 1) (Fin.cons false ε) = cntF n ε + 1 := rfl

theorem cnt_add (n : ℕ) (ε : Fin n → Bool) : cntT n ε + cntF n ε = n := by
  induction n with
  | zero => simp [cntT, cntF]
  | succ n ih =>
    rw [cntT_succ, cntF_succ]
    cases h : ε 0
    · have ht : (false).toNat = 0 := rfl
      have hb : (!(false)).toNat = 1 := rfl
      simp only [ht, hb]
      have := ih (fun t => ε t.succ)
      omega
    · have ht : (true).toNat = 1 := rfl
      have hb : (!(true)).toNat = 0 := rfl
      simp only [ht, hb]
      have := ih (fun t => ε t.succ)
      omega

theorem sPos_succ (n : ℕ) (t : Fin 4) : sPos (n + 1) t = (sPos n t).succ := by
  ext; simp only [sPos, Fin.val_succ]; omega

theorem sPos_zero (t : Fin 4) : sPos 0 t = t := by
  ext; simp only [sPos]; omega

/-- The position of the `r`-th `true` entry of `ε`, as a function on `Fin (cntT n ε)`. -/
noncomputable def map₁ (n : ℕ) (ε : Fin n → Bool) : Fin (cntT n ε) → Fin (4 + n) :=
  fun r => dsf n ε r.val

/-- The position of the `r`-th `false` entry of `ε`, as a function on `Fin (cntF n ε)`. -/
noncomputable def map₂ (n : ℕ) (ε : Fin n → Bool) : Fin (cntF n ε) → Fin (4 + n) :=
  fun r => dsg n ε r.val

end Work.Diff.EXT.evX
