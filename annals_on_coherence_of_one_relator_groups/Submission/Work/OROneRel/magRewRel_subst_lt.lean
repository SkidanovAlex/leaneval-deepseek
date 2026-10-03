/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Shorter Magnus rewriting after the Case-2 substitution

Case 2 of the Freiheitssatz (`freiheitssatz_case2`, `freiheitssatz_at`) reduces a relator `r` all of
whose letters have nonzero exponent sum to the exponent-sum-zero case by the Magnus/Putman
substitution

  `subst t x (σ_x r) (σ_t r) :  t ↦ t ^ (σ_x r),  x ↦ x * t ^ (-(σ_t r)),  others fixed`,

which arranges `σ_t (subst t x (σ_x r) (σ_t r) r) = 0`.  The induction hypothesis of the
Freiheitssatz is then applied to a *cyclically reduced conjugate* `v` of the substituted relator, so
we must know that the Magnus rewriting of `v` with respect to `t` is shorter than `r` itself:

  `relatorNorm (magRewRel t v) < relatorNorm r`  whenever `v` is cyclically reduced and conjugate to
  `subst t x (σ_x r) (σ_t r) r`.

This is the statement proved here.  Two letter counts are compared:

* `nt t L` is the number of letters of a word `L` that are different from `t`
  (`Submission.Work.OROneRel.ntDefs`); the Magnus rewriting of a reduced word has length `nt t L`, so
  `relatorNorm (magRewRel t v) = nt t v.toWord`;
* a cyclically reduced conjugate does not increase `nt`: if `v` is cyclically reduced and the
  substituted relator is `r' = c v c⁻¹`, then `nt t v.toWord ≤ nt t r'.toWord`.  This is
  `nt_le_nt_reduce_conj_aux` below: `r'.toWord` is `conj ++ RC ++ invRev conj` for a cyclic reduction
  `RC` of `r'.toWord` (Mathlib's `FreeGroup.reduceCyclically`), hence `nt t RC ≤ nt t r'.toWord`; on
  the other hand `mk v` and `mk RC` are conjugate, say `mk v = D * mk RC * D⁻¹`, so taking `m`-th
  powers and using that the powers of a cyclically reduced word concatenate without cancellation
  (`FreeGroup.IsCyclicallyReduced.flatten_replicate`),

    `m * nt t v.toWord ≤ 2 * nt t D.toWord + m * nt t RC`   for every `m ≥ 1`;

  choosing `m = 2 * nt t D.toWord + 1` forces `nt t v.toWord ≤ nt t RC`;
* the substitution itself does not increase `nt` (`nt_subst_toWord_le`), because it replaces every
  `t`-letter by a power of `t` and every other letter by a word with exactly one letter different
  from `t`;
* and `nt t r.toWord < relatorNorm r`, because every letter of `r.toWord` equal to `t` is not counted
  and `t` occurs in `r` (`nt_lt_relatorNorm`).

The hypotheses `hcyc`, `hx`, `htx`, `hσt`, `hσx` of the statement are part of the caller's setting
(they are needed to know that `subst t x (σ_x r) (σ_t r) r` has exponent sum zero in `t` and is a
genuine replacement for `r`), but the inequality itself only uses `ht`.
-/
import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.ntDefs
import Submission.Work.OROneRel.rewrite_length_lt
import Submission.Work.OROneRel.rewrite_isReduced
import Submission.Work.OROneRel.nt_subst_toWord_le
import Submission.Work.OROneRel.nt_lt_relatorNorm

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- Subadditivity of the letter count `nt` under multiplication, in the form needed here (the
instance `DecidableEq α` is an explicit parameter, so that the statement can be used inside a proof
that carries its own instance of it). -/
private theorem nt_mul_toWord_le [DecidableEq α] (t : α) (x y : FreeGroup α) :
    nt t (x * y).toWord ≤ nt t x.toWord + nt t y.toWord := by
  rw [FreeGroup.toWord_mul]
  exact le_trans (nt_red_le FreeGroup.reduce.red) (le_of_eq (nt_append t _ _))

/-- `nt` is invariant under inversion. -/
private theorem nt_inv_toWord [DecidableEq α] (t : α) (x : FreeGroup α) :
    nt t x⁻¹.toWord = nt t x.toWord := by
  rw [FreeGroup.toWord_inv, nt_invRev]

/-- Concatenating `m` copies of a word multiplies its `nt`-count by `m`. -/
private theorem nt_flatten_replicate (t : α) (L : List (α × Bool)) (m : ℕ) :
    nt t (List.replicate m L).flatten = m * nt t L := by
  induction m with
  | zero => simp [nt]
  | succ m ih => rw [List.replicate_succ, List.flatten_cons, nt_append, ih]; ring

/-- **A cyclically reduced conjugate does not increase the `nt`-count**: for a cyclically reduced
word `W`, the reduced form of `P ++ W ++ invRev P` has at least as many letters different from `t`
as `W` has.

`FreeGroup.reduceCyclically` writes the reduced word of the conjugate as `C ++ RC ++ invRev C` with
`RC` a cyclic reduction of it, so `nt t RC ≤ nt t (reduce (P ++ W ++ invRev P))`.  Since `mk RC` and
`mk W` are conjugate, say `mk W = D * mk RC * D⁻¹`, taking `m`-th powers gives
`m * nt t W ≤ 2 * nt t D.toWord + m * nt t RC` for every `m ≥ 1` -- because the powers of the
cyclically reduced word `W` concatenate without cancellation
(`FreeGroup.IsCyclicallyReduced.flatten_replicate`).  Choosing `m = 2 * nt t D.toWord + 1` forces
`nt t W ≤ nt t RC`. -/
private theorem nt_le_nt_reduce_conj_aux [DecidableEq α] (t : α) {W P : List (α × Bool)}
    (hW : FreeGroup.IsCyclicallyReduced W) :
    nt t W ≤ nt t (FreeGroup.reduce (P ++ W ++ FreeGroup.invRev P)) := by
  classical
  -- the group element of the reduced conjugate
  have hconj : FreeGroup.mk (P ++ W ++ FreeGroup.invRev P)
      = FreeGroup.mk P * FreeGroup.mk W * (FreeGroup.mk P)⁻¹ := by
    rw [List.append_assoc, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    group
  -- the reduced word of the conjugate, cyclically reduced, and split off its conjugator
  set M : List (α × Bool) := FreeGroup.reduce (P ++ W ++ FreeGroup.invRev P) with hM
  set RC : List (α × Bool) := FreeGroup.reduceCyclically M with hRC
  set C : List (α × Bool) := FreeGroup.reduceCyclically.conjugator M with hC
  have hMred : FreeGroup.IsReduced M :=
    FreeGroup.IsReduced.of_reduce_eq (by rw [hM]; exact FreeGroup.reduce.idem)
  have hRCcyc : FreeGroup.IsCyclicallyReduced RC := by
    rw [hRC]; exact FreeGroup.reduceCyclically.isCyclicallyReduced hMred
  have hMR : FreeGroup.mk M = FreeGroup.mk P * FreeGroup.mk W * (FreeGroup.mk P)⁻¹ := by
    rw [hM, FreeGroup.reduce.self, hconj]
  have hsplit : FreeGroup.mk M = FreeGroup.mk C * FreeGroup.mk RC * (FreeGroup.mk C)⁻¹ := by
    conv_lhs => rw [← FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically M]
    rw [List.append_assoc, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    rw [hC, hRC]
    group
  have hRCle : nt t RC ≤ nt t M := by
    conv_rhs => rw [← FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically M]
    rw [hRC, nt_append, nt_append, nt_invRev]
    omega
  -- a conjugating element between `mk W` and `mk RC`
  set D : FreeGroup α := (FreeGroup.mk P)⁻¹ * FreeGroup.mk C with hD
  have hWconj : FreeGroup.mk W = D * FreeGroup.mk RC * D⁻¹ := by
    have h1 : FreeGroup.mk P * FreeGroup.mk W * (FreeGroup.mk P)⁻¹
        = FreeGroup.mk C * FreeGroup.mk RC * (FreeGroup.mk C)⁻¹ := by rw [← hMR, hsplit]
    have h2 : D * FreeGroup.mk RC * D⁻¹
        = (FreeGroup.mk P)⁻¹ * (FreeGroup.mk C * FreeGroup.mk RC * (FreeGroup.mk C)⁻¹)
            * FreeGroup.mk P := by
      rw [hD]; group
    rw [h2, ← h1]; group
  -- the asymptotic inequality `m * nt t W ≤ 2 * nt t D.toWord + m * nt t RC` for all `m ≥ 1`
  have key : ∀ m : ℕ, 1 ≤ m → m * nt t W ≤ 2 * nt t D.toWord + m * nt t RC := by
    intro m _
    have hpowW : nt t ((FreeGroup.mk W) ^ m).toWord = m * nt t W := by
      rw [FreeGroup.toWord_pow, FreeGroup.toWord_mk,
        FreeGroup.IsReduced.reduce_eq hW.isReduced,
        FreeGroup.IsReduced.reduce_eq (hW.flatten_replicate m).isReduced,
        nt_flatten_replicate]
    have hpowRC : nt t ((FreeGroup.mk RC) ^ m).toWord ≤ m * nt t RC := by
      rw [FreeGroup.toWord_pow]
      calc nt t (FreeGroup.reduce (List.replicate m (FreeGroup.mk RC).toWord).flatten)
          ≤ nt t (List.replicate m (FreeGroup.mk RC).toWord).flatten :=
            nt_red_le FreeGroup.reduce.red
        _ = m * nt t (FreeGroup.mk RC).toWord := nt_flatten_replicate t _ m
        _ = m * nt t RC := by
              rw [FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hRCcyc.isReduced]
    have hpowD : nt t ((D * (FreeGroup.mk RC) ^ m * D⁻¹).toWord)
        ≤ 2 * nt t D.toWord + m * nt t RC := by
      calc nt t ((D * (FreeGroup.mk RC) ^ m * D⁻¹).toWord)
          ≤ nt t (D * (FreeGroup.mk RC) ^ m).toWord + nt t (D⁻¹).toWord :=
            nt_mul_toWord_le t _ _
        _ = nt t (D * (FreeGroup.mk RC) ^ m).toWord + nt t D.toWord := by rw [nt_inv_toWord]
        _ ≤ (nt t D.toWord + nt t ((FreeGroup.mk RC) ^ m).toWord) + nt t D.toWord :=
              Nat.add_le_add_right (nt_mul_toWord_le t D _) _
        _ ≤ (nt t D.toWord + m * nt t RC) + nt t D.toWord := by omega
        _ = 2 * nt t D.toWord + m * nt t RC := by ring
    calc m * nt t W = nt t ((FreeGroup.mk W) ^ m).toWord := hpowW.symm
      _ = nt t ((D * FreeGroup.mk RC * D⁻¹) ^ m).toWord := by rw [hWconj]
      _ = nt t ((D * (FreeGroup.mk RC) ^ m * D⁻¹)).toWord := by rw [conj_pow]
      _ ≤ 2 * nt t D.toWord + m * nt t RC := hpowD
  -- choose `m` large enough to beat the additive error `2 * nt t D.toWord`
  by_contra hcon
  push Not at hcon
  have hlt : nt t RC < nt t W := lt_of_le_of_lt hRCle hcon
  have hm : 1 ≤ 2 * nt t D.toWord + 1 := by omega
  have hk := key (2 * nt t D.toWord + 1) hm
  have h1 : (2 * nt t D.toWord + 1) * (nt t RC + 1) ≤ (2 * nt t D.toWord + 1) * nt t W :=
    Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hlt)
  have h2 : (2 * nt t D.toWord + 1) * (nt t RC + 1)
      = (2 * nt t D.toWord + 1) * nt t RC + (2 * nt t D.toWord + 1) := by ring
  omega

set_option linter.unusedVariables false in
/-- **The Magnus rewriting of a cyclically reduced conjugate of the substituted relator is shorter
than the original relator.**  If `r` is a relator with `t, x ∈ relatorLetters r`, and `v` is a
cyclically reduced conjugate of `subst t x (σ_x r) (σ_t r) r`, then `magRewRel t v` is a relator of
norm strictly smaller than `relatorNorm r` -- which is what lets the Freiheitssatz induction
hypothesis be applied to it. -/
theorem magRewRel_subst_lt {α : Type u} (r : FreeGroup α) (t x : α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hx : x ∈ Work.OROneRel.relatorLetters r)
    (htx : x ≠ t) (hσt : Work.OROneRel.sigma t r ≠ 1) (hσx : Work.OROneRel.sigma x r ≠ 1) :
    ∀ v : FreeGroup α, Work.OROneRel.IsCyclicallyReducedRelator v →
      IsConj v (Work.OROneRel.subst t x (Multiplicative.toAdd (Work.OROneRel.sigma x r))
        (Multiplicative.toAdd (Work.OROneRel.sigma t r)) r) →
      Work.OROneRel.relatorNorm (Work.OROneRel.magRewRel t v) < Work.OROneRel.relatorNorm r := by
  classical
  -- the Magnus rewriting lives in the free group on the decorated letters `{a // a ≠ t} × ℤ`
  letI : DecidableEq ({a : α // a ≠ t} × ℤ) := Classical.decEq _
  intro v hv hconj
  set m : ℤ := (sigma x r).toAdd with hm
  set n : ℤ := (sigma t r).toAdd with hn
  set r' : FreeGroup α := subst t x m n r with hr'
  have hconj' : IsConj v r' := by simpa only [hr', hm, hn] using hconj
  have hW : FreeGroup.IsCyclicallyReduced v.toWord := by
    simpa only [IsCyclicallyReducedRelator] using hv
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj'
  -- the reduced word of `r' = c * v * c⁻¹` as a reduced conjugate form of `v.toWord`
  have hB : FreeGroup.reduce (FreeGroup.invRev c.toWord) = FreeGroup.invRev c.toWord :=
    FreeGroup.IsReduced.reduce_eq (by rw [← FreeGroup.toWord_inv]; exact FreeGroup.isReduced_toWord)
  have hP : r'.toWord =
      FreeGroup.reduce (c.toWord ++ v.toWord ++ FreeGroup.invRev c.toWord) := by
    rw [hc.symm, FreeGroup.toWord_mul, FreeGroup.toWord_inv, FreeGroup.toWord_mul]
    conv_lhs => rw [← hB]
    rw [FreeGroup.reduce_append_reduce_reduce]
  -- conjugation down to `r'` does not lose non-`t` letters
  have h2 : nt t v.toWord ≤ nt t r'.toWord := by
    rw [hP]
    exact nt_le_nt_reduce_conj_aux t hW
  -- the substitution does not increase the number of letters different from `t`
  have h3 : nt t r'.toWord ≤ nt t r.toWord := by
    simpa only [hr'] using nt_subst_toWord_le t x m n r
  -- `t` occurs in `r`, so at least one letter of `r` is not counted by `nt`
  have h4 : nt t r.toWord < relatorNorm r := nt_lt_relatorNorm ht
  -- the Magnus rewriting of `v` has norm exactly `nt t v.toWord`
  have hred : FreeGroup.IsReduced (rewrite t v.toWord) :=
    rewrite_isReduced t (FreeGroup.isReduced_toWord (x := v))
  have h1 : relatorNorm (magRewRel t v) = nt t v.toWord := by
    have hA : relatorNorm (magRewRel t v) = (rewrite t v.toWord).length := by
      show FreeGroup.norm (magRewRel t v) = (rewrite t v.toWord).length
      rw [show magRewRel t v = FreeGroup.mk (rewrite t v.toWord) from rfl, FreeGroup.norm,
        FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq hred]
    have hB2 : (rewrite t v.toWord).length = nt t v.toWord := by
      rw [show rewrite t v.toWord = rewriteAux t 0 v.toWord from rfl, rewriteAux_length]
      simp only [nt]
    rw [hA, hB2]
  omega

end Work.OROneRel
