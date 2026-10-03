/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Magnus rewriting of a word in the letters of `rho`

This file provides the word-theoretic device that shows that the Magnus map `rho` (the `zeta` of
`FreiheitssatzDefs.lean`, defined in `magnus_moldavanskii_at.lean` as the homomorphism
`F((α \ {t}) × ℤ) →* F α` sending `(x, i)` to `t ^ i * x * t ^ (-i)`) is injective.

Given a word `L` over the set `({x : α // x ≠ t} × ℤ) × Bool` of decorated letters, `rewAux t cur L`
writes down the corresponding word in the original generators: a decorated letter `((x, i), b)`
becomes `t ^ (i - cur) * x ^ b`, and the running decoration `cur` is updated to `i`; at the end the
remaining power of `t` is emitted.  With the initial decoration `0` this is `rewRho t L`.

The point of the merging of the `t`-powers is that `rewRho t L` is a *reduced* word as soon as `L` is,
and it is nonempty as soon as `L` is: these are the two facts (proved in
`Submission.Work.OROneRel.rho_injective`) that make `mk (rewRho t L) ≠ 1` for `L ≠ []` reduced, whence
`rho` is injective.  The group-theoretic identity `mk (rewAux t cur L) = t ^ (-cur) * rho (mk L)` is
`Submission.Work.OROneRel.mk_rewAux`.
-/
import Mathlib
import Submission.Work.OROneRel.MagnusRewrite

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The word `t ^ n`, as a list of letters: `n` copies of `t` if `n ≥ 0` and `|n|` copies of `t⁻¹`
otherwise. -/
noncomputable def zword (t : α) (n : ℤ) : List (α × Bool) :=
  if 0 ≤ n then List.replicate n.natAbs (t, true) else List.replicate n.natAbs (t, false)

/-- The word in the generators `α` obtained from a word in the decorated letters
`({x : α // x ≠ t} × ℤ) × Bool` by replacing a decorated letter `((x, i), b)` by
`t ^ (i - cur) * x ^ b`, where `cur` is the running value of the decoration; at the end the remaining
power `t ^ (-cur)` is emitted. -/
noncomputable def rewAux (t : α) : ℤ → List (({x : α // x ≠ t} × ℤ) × Bool) → List (α × Bool)
  | cur, [] => zword t (0 - cur)
  | cur, (((s, i), b) :: tl) => zword t (i - cur) ++ ((s : α), b) :: rewAux t i tl

/-- The Magnus rewriting of a word in the decorated letters, with initial decoration `0`. -/
noncomputable def rewRho (t : α) (L : List (({x : α // x ≠ t} × ℤ) × Bool)) : List (α × Bool) :=
  rewAux t 0 L

lemma zword_eq_replicate (t : α) (n : ℤ) :
    zword t n = List.replicate n.natAbs (t, decide (0 ≤ n)) := by
  rw [zword]
  split <;> rename_i h
  · simp [h]
  · simp [h]

lemma zword_nil_iff (t : α) (n : ℤ) : zword t n = [] ↔ n = 0 := by
  rw [zword]
  split <;> rename_i h
  · rw [List.replicate_eq_nil_iff, Int.natAbs_eq_zero]
  · rw [List.replicate_eq_nil_iff, Int.natAbs_eq_zero]

lemma zword_mem (t : α) (n : ℤ) {a : α × Bool} (ha : a ∈ zword t n) : a.1 = t := by
  rw [zword] at ha
  split at ha <;> rename_i h
  · rw [List.mem_replicate] at ha; rw [ha.2]
  · rw [List.mem_replicate] at ha; rw [ha.2]

lemma isReduced_zword (t : α) (n : ℤ) : FreeGroup.IsReduced (zword t n) := by
  rw [zword]
  split <;> rename_i h
  · rw [FreeGroup.IsReduced, List.isChain_iff_getElem]
    intro i hi
    simp
  · rw [FreeGroup.IsReduced, List.isChain_iff_getElem]
    intro i hi
    simp

lemma zword_head (t : α) (n : ℤ) {c : α × Bool} (h : (zword t n).head? = some c) : c.1 = t :=
  zword_mem t n (List.mem_of_mem_head? h)

lemma zword_getLast (t : α) (n : ℤ) {c : α × Bool} (h : (zword t n).getLast? = some c) : c.1 = t :=
  zword_mem t n (List.mem_of_mem_getLast? h)

lemma zword_ne_nil_of_ne_zero {t : α} {n : ℤ} (hn : n ≠ 0) : zword t n ≠ [] := by
  rw [ne_eq, zword_nil_iff]; exact hn

lemma zword_ne_zero_head {t : α} {n : ℤ} (_hn : n ≠ 0) {c : α × Bool}
    (h : (zword t n).head? = some c) : c.1 = t :=
  zword_head t n h

/-- The rewriting of any word computes the group-theoretic element `t ^ (-cur) * rho (mk L)`. -/
lemma mk_zword (t : α) (n : ℤ) : FreeGroup.mk (zword t n) = FreeGroup.of t ^ n := by
  rw [zword]
  split <;> rename_i h
  · have hk : ((n.natAbs : ℕ) : ℤ) = n := by rw [Int.natCast_natAbs, abs_of_nonneg h]
    calc FreeGroup.mk (List.replicate n.natAbs (t, true))
        = FreeGroup.lift FreeGroup.of (FreeGroup.mk (List.replicate n.natAbs (t, true))) :=
            (FreeGroup.lift_of_apply _).symm
      _ = (List.map (fun x => bif x.2 then FreeGroup.of x.1 else (FreeGroup.of x.1)⁻¹)
            (List.replicate n.natAbs (t, true))).prod := FreeGroup.lift_mk
      _ = (FreeGroup.of t) ^ n.natAbs := by simp
      _ = FreeGroup.of t ^ n := by rw [← zpow_natCast, hk]
  · have hk : ((n.natAbs : ℕ) : ℤ) = -n := by
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge h)]
    calc FreeGroup.mk (List.replicate n.natAbs (t, false))
        = FreeGroup.lift FreeGroup.of (FreeGroup.mk (List.replicate n.natAbs (t, false))) :=
            (FreeGroup.lift_of_apply _).symm
      _ = (List.map (fun x => bif x.2 then FreeGroup.of x.1 else (FreeGroup.of x.1)⁻¹)
            (List.replicate n.natAbs (t, false))).prod := FreeGroup.lift_mk
      _ = (FreeGroup.of t)⁻¹ ^ n.natAbs := by simp
      _ = FreeGroup.of t ^ n := by rw [inv_pow, ← zpow_natCast, ← zpow_neg, hk, neg_neg]

end Work.OROneRel
