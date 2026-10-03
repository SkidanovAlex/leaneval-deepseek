import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.rewriteAux_append
import Submission.Work.OROneRel.sigma_mk

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- `FreeGroup.toWord` does not depend on the `DecidableEq` instance that is used to compute it. -/
theorem toWord_decEq_congr_aux (i j : DecidableEq α) (w : FreeGroup α) :
    @FreeGroup.toWord α i w = @FreeGroup.toWord α j w := by
  have h : i = j := Subsingleton.elim i j
  rw [h]

/-- The Magnus rewriting `rewriteAux t 0` of an `l`-fold concatenation of a word `L` of exponent
sum zero is the `l`-fold concatenation of the rewriting of `L`. -/
theorem rewriteAux_flatten_replicate (t : α) (L : List (α × Bool)) (h0 : sigmaList t L = 0)
    (l : ℕ) :
    rewriteAux t 0 (List.replicate l L).flatten =
      (List.replicate l (rewriteAux t 0 L)).flatten := by
  induction l with
  | zero =>
      rw [show (List.replicate 0 L).flatten = ([] : List (α × Bool)) from rfl,
        show (List.replicate 0 (rewriteAux t 0 L)).flatten
            = ([] : List (({a : α // a ≠ t} × ℤ) × Bool)) from rfl,
        rewriteAux.eq_1]
  | succ l ih =>
      rw [List.replicate_succ, List.flatten_cons, rewriteAux_append, h0, zero_add, ih,
        List.replicate_succ, List.flatten_cons]

/-- `FreeGroup.mk` of an `l`-fold concatenation of a word is the `l`-th power of the image of the
word. -/
theorem magRewRel_pow_mk_flatten_replicate (L : List (α × Bool)) (l : ℕ) :
    FreeGroup.mk (List.replicate l L).flatten = (FreeGroup.mk L) ^ l := by
  induction l with
  | zero =>
      rw [show (List.replicate 0 L).flatten = ([] : List (α × Bool)) from rfl,
        ← FreeGroup.one_eq_mk, pow_zero]
  | succ l ih =>
      rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

/-- `magRewRel` can be computed with any `DecidableEq` instance: the `FreeGroup.toWord` occurring in
its definition is instance-independent. -/
theorem magRewRel_eq_mk_rewrite (t : α) (i : DecidableEq α) (w : FreeGroup α) :
    magRewRel t w = FreeGroup.mk (rewrite t (@FreeGroup.toWord α i w)) := by
  have h : magRewRel t w
      = FreeGroup.mk (rewrite t (@FreeGroup.toWord α (Classical.decEq α) w)) := rfl
  rw [h, toWord_decEq_congr_aux (Classical.decEq α) i w]

theorem magRewRel_pow {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hsigma : Work.OROneRel.sigma t u = 1) :
    Work.OROneRel.magRewRel t (u ^ l) = (Work.OROneRel.magRewRel t u) ^ l := by
  -- the exponent sum of `t` in `u` vanishes, expressed with the local `DecidableEq` instance
  have h0 : sigmaList t (@FreeGroup.toWord α (inferInstance : DecidableEq α) u) = 0 := by
    have hsig : sigma t u = Multiplicative.ofAdd
        (sigmaList t (@FreeGroup.toWord α (inferInstance : DecidableEq α) u)) := by
      have hthis : sigma t (FreeGroup.mk
          (@FreeGroup.toWord α (inferInstance : DecidableEq α) u))
          = Multiplicative.ofAdd
            (sigmaList t (@FreeGroup.toWord α (inferInstance : DecidableEq α) u)) :=
        sigma_mk t (@FreeGroup.toWord α (inferInstance : DecidableEq α) u)
      rwa [@FreeGroup.mk_toWord α (inferInstance : DecidableEq α) u] at hthis
    exact ofAdd_eq_one.mp (by rw [← hsig]; exact hsigma)
  -- `u.toWord` is cyclically reduced, with the local instance
  have hcyc' : FreeGroup.IsCyclicallyReduced
      (@FreeGroup.toWord α (inferInstance : DecidableEq α) u) := by
    have hw := hcyc
    unfold Work.OROneRel.IsCyclicallyReducedRelator at hw
    rwa [toWord_decEq_congr_aux (Classical.decEq α) (inferInstance : DecidableEq α) u] at hw
  -- the reduced word of `u ^ l` is the `l`-fold concatenation of the reduced word of `u`
  have htw : (@FreeGroup.toWord α (inferInstance : DecidableEq α) (u ^ l))
      = (List.replicate l (@FreeGroup.toWord α (inferInstance : DecidableEq α) u)).flatten := by
    rw [FreeGroup.toWord_pow,
      FreeGroup.IsReduced.reduce_eq
        (FreeGroup.IsCyclicallyReduced.flatten_replicate hcyc' l).isReduced]
  rw [magRewRel_eq_mk_rewrite t (inferInstance : DecidableEq α) (u ^ l),
    magRewRel_eq_mk_rewrite t (inferInstance : DecidableEq α) u]
  have hrew : ∀ L : List (α × Bool), rewrite t L = rewriteAux t 0 L := fun L => rfl
  simp only [hrew]
  rw [htw, rewriteAux_flatten_replicate t
      (@FreeGroup.toWord α (inferInstance : DecidableEq α) u) h0 l]
  exact magRewRel_pow_mk_flatten_replicate (rewriteAux t 0
    (@FreeGroup.toWord α (inferInstance : DecidableEq α) u)) l

end Work.OROneRel
