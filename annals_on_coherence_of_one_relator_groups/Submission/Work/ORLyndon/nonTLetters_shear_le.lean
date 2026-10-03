import Mathlib
import Submission.Work.ORLyndon.twoSidedShear
import Submission.Work.OROneRel.magnus_step_root
import Submission.Work.OROneRel.nonTLetters_Psi_le

/-!
# The two-sided shear does not increase the number of non-`t` letters

`Work.ORLyndon.shear t x m m'` is the Nielsen transformation of `F α` sending
`x ↦ t ^ (-m) * x * t ^ (-m')` and fixing every other generator
(`Submission.Work.ORLyndon.twoSidedShear`).  This file proves that it never increases the number of
letters different from `t`:

`Work.OROneRel.nonTLetters t (shear t x m m' u) ≤ Work.OROneRel.nonTLetters t u`.

Each letter of a reduced word representing `u` is replaced by a block whose reduced form contains at
most one letter different from `t` (namely the letter `x` itself, and none at all when `x = t`),
and neither multiplication in the free group nor free reduction can create letters different from
`t`.

## Implementation notes

The direct route (via the general estimate `nt_lift_le` of
`Submission.Work.OROneRel.nt_mmTrans_le`) is blocked: that module imports
`Submission.Work.OROneRel.mmTransvectionDefs`, which declares `Work.OROneRel.mmTransFun`, a name
that `Submission.Work.OROneRel.magnus_step_root` declares as well, so any module importing both cones
fails with `environment already contains 'Work.OROneRel.mmTransFun'`.  We therefore reproduce the
single estimate we need — a `FreeGroup.lift` whose generator images have at most one non-`t` letter
does not increase the number of non-`t` letters — directly, in the `sum`/`countP` normalisation of
`Submission.Work.OROneRel.nonTLetters_Psi_le`, using only `Submission.Work.OROneRel.ntDefs`.

The `nt`-lemmas of `Submission.Work.OROneRel.ntDefs` are stated for one fixed (classical)
`DecidableEq` instance; `nonTLetters` itself is instance-free, but its argument is not.  We
therefore prove the bound for an arbitrary instance `d` of the shear — the instance only decides
which branch of the generator map is taken — while evaluating the letter count with the classical
`toWord`; `DecidableEq` is a subsingleton, so the letter counts for distinct instances agree.
-/

namespace Work.ORLyndon

attribute [local instance] Classical.propDecidable

/-- The classical `DecidableEq` instance, written out in the exact shape in which the lemmas of
`Submission.Work.OROneRel.ntDefs` use it (a notation, so that terms compare syntactically). -/
local notation "dEq" α:max => (fun a b : α => Classical.propDecidable (a = b))

/-- The generator map of the two-sided shear, with the `DecidableEq` instance made explicit. -/
private noncomputable def shMap {α : Type*} (d : DecidableEq α) (t x : α) (m m' : ℤ) :
    α → FreeGroup α :=
  fun a => @ite (FreeGroup α) (a = x) (d a x)
    ((FreeGroup.of t) ^ (-m) * FreeGroup.of x * (FreeGroup.of t) ^ (-m')) (FreeGroup.of a)

/-- The two-sided shear is the lift of its generator map. -/
private lemma shear_apply {α : Type*} (d : DecidableEq α) (t x : α) (m m' : ℤ)
    (u : FreeGroup α) :
    @Work.ORLyndon.shear α d t x m m' u = (FreeGroup.lift (@shMap α d t x m m')) u := rfl

/-- **Each generator image of the two-sided shear has at most one letter different from `t`.** -/
private lemma nt_shMap_le {α : Type*} (t x : α) (m m' : ℤ) (a : α) (d : Decidable (a = x)) :
    Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α)
        (@ite (FreeGroup α) (a = x) d
          ((FreeGroup.of t) ^ (-m) * FreeGroup.of x * (FreeGroup.of t) ^ (-m'))
          (FreeGroup.of a)))
      ≤ if decide (a ≠ t) then 1 else 0 := by
  by_cases hat : a = t
  · -- `a = t`: the right hand side is `0`
    rw [show (if decide (a ≠ t) then (1 : ℕ) else 0) = 0 by simp [hat]]
    by_cases hax : a = x
    · -- `a = x = t`: the image is the power `of t ^ (-m) * of t * of t ^ (-m')`
      rw [if_pos hax]
      have hxt : x = t := hax.symm.trans hat
      have h1 : (FreeGroup.of t) ^ (-m) * FreeGroup.of x * (FreeGroup.of t) ^ (-m')
          = (FreeGroup.of t) ^ ((-m) + 1 + (-m')) := by
        rw [hxt, ← zpow_add_one, ← zpow_add]
      exact le_of_eq (by rw [h1, Work.OROneRel.nt_of_zpow])
    · -- `a = t ≠ x`: the image is `of t`
      rw [if_neg hax]
      exact le_of_eq (by
        rw [hat, @FreeGroup.toWord_of α (dEq α) t, Work.OROneRel.nt_singleton]
        simp)
  · -- `a ≠ t`: the right hand side is `1`
    rw [show (if decide (a ≠ t) then (1 : ℕ) else 0) = 1 by simp [hat]]
    by_cases hax : a = x
    · -- `a = x ≠ t`: the image is `t ^ (-m) * of x * t ^ (-m')`, whose only non-`t` letter is `x`
      rw [if_pos hax]
      have hxt : x ≠ t := fun h => hat (hax.trans h)
      calc Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α)
              ((FreeGroup.of t) ^ (-m) * FreeGroup.of x * (FreeGroup.of t) ^ (-m')))
          ≤ Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α)
              ((FreeGroup.of t) ^ (-m) * FreeGroup.of x))
            + Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) ((FreeGroup.of t) ^ (-m'))) :=
            Work.OROneRel.nt_mul_le t _ _
        _ ≤ (Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) ((FreeGroup.of t) ^ (-m)))
              + Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) (FreeGroup.of x)))
            + Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) ((FreeGroup.of t) ^ (-m'))) :=
            Nat.add_le_add_right (Work.OROneRel.nt_mul_le t _ _) _
        _ = 1 := by
            rw [Work.OROneRel.nt_of_zpow, Work.OROneRel.nt_of_zpow,
              @FreeGroup.toWord_of α (dEq α) x, Work.OROneRel.nt_singleton]
            simp [hxt]
    · -- `a ≠ x`, `a ≠ t`: the generator is fixed
      rw [if_neg hax]
      exact le_of_eq (by
        rw [@FreeGroup.toWord_of α (dEq α) a, Work.OROneRel.nt_singleton]
        simp [hat])

/-- A single letter of a word is sent to a block with at most one non-`t` letter. -/
private lemma nt_bif_le {α : Type*} (t : α) (g : α → FreeGroup α)
    (hg : ∀ a : α, Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) (g a))
      ≤ if decide (a ≠ t) then 1 else 0)
    (a : α) (b : Bool) :
    Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) (bif b then g a else (g a)⁻¹))
      ≤ if decide (a ≠ t) then 1 else 0 := by
  cases b
  · show Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) ((g a)⁻¹)) ≤ _
    rw [Work.OROneRel.nt_inv]
    exact hg a
  · show Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) (g a)) ≤ _
    exact hg a

/-- **A `FreeGroup.lift` whose generator images avoid `t` up to one letter does not increase the
number of letters different from `t`** (in the `sum`/`countP` normalisation of
`Submission.Work.OROneRel.nonTLetters_Psi_le`). -/
private lemma nt_lift_mk_le {α : Type*} (t : α) (g : α → FreeGroup α)
    (hg : ∀ a : α, Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) (g a))
      ≤ if decide (a ≠ t) then 1 else 0)
    (L : List (α × Bool)) :
    Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) ((FreeGroup.lift g) (FreeGroup.mk L)))
      ≤ Work.OROneRel.nt t L := by
  rw [FreeGroup.lift_mk]
  calc Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α)
        ((List.map (fun x : α × Bool => bif x.2 then g x.1 else (g x.1)⁻¹) L).prod))
      ≤ (List.map (fun x : FreeGroup α => Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α) x))
          (List.map (fun x : α × Bool => bif x.2 then g x.1 else (g x.1)⁻¹) L)).sum :=
        Work.OROneRel.nt_prod_le t _
    _ = (List.map (fun x : α × Bool =>
          Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α)
            (bif x.2 then g x.1 else (g x.1)⁻¹))) L).sum :=
        Work.OROneRel.sum_map_map _ _ _
    _ ≤ L.countP (fun x : α × Bool => decide (x.1 ≠ t)) :=
        Work.OROneRel.sum_map_le_countP (fun x : α × Bool => decide (x.1 ≠ t))
          (fun x : α × Bool => Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α)
            (bif x.2 then g x.1 else (g x.1)⁻¹))) L
          (fun x _ => nt_bif_le t g hg x.1 x.2)
    _ = Work.OROneRel.nt t L := (Work.OROneRel.nt_eq_countP t L).symm

/-- **The two-sided shear does not increase the number of letters different from `t`.** -/
theorem nonTLetters_shear_le {α : Type*} [DecidableEq α] (u : FreeGroup α) (t x : α) (m m' : ℤ) :
    Work.OROneRel.nonTLetters t (Work.ORLyndon.shear t x m m' u) ≤ Work.OROneRel.nonTLetters t u := by
  suffices key : ∀ d : DecidableEq α,
      Work.OROneRel.nonTLetters t (@Work.ORLyndon.shear α d t x m m' u)
        ≤ Work.OROneRel.nonTLetters t u from key _
  intro d
  rw [shear_apply d t x m m' u,
      Work.OROneRel.nonTLetters_eq_nt t ((FreeGroup.lift (@shMap α d t x m m')) u),
      Work.OROneRel.nonTLetters_eq_nt t u]
  have hmk : FreeGroup.mk (@FreeGroup.toWord α (dEq α) u) = u :=
    @FreeGroup.mk_toWord α (dEq α) (x := u)
  have hL : Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α)
          ((FreeGroup.lift (@shMap α d t x m m')) u))
      = Work.OROneRel.nt t (@FreeGroup.toWord α (dEq α)
          ((FreeGroup.lift (@shMap α d t x m m'))
            (FreeGroup.mk (@FreeGroup.toWord α (dEq α) u)))) := by
    rw [hmk]
  rw [hL]
  exact nt_lift_mk_le t (@shMap α d t x m m')
    (fun a => nt_shMap_le t x m m' a (d a x)) _

end Work.ORLyndon
