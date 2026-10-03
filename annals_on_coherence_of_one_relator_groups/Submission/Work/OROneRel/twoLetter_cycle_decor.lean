/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2) of the
formalisation of Jaikin-Zapirain--Linton, "On the coherence of one-relator groups
and their group algebras".

# The decoration of the two-letter cycle `x ^ p * y ^ q`

Let `c : Fin 2 → ℤ` be the weight `c 0 = q`, `c 1 = -p`, and let
`w = FreeGroup.of 0 ^ p * FreeGroup.of 1 ^ q` be the two-letter cyclically reduced word
(`p, q ≥ 1`, `p` coprime to `q`).  This file computes the decorated word
`decor c 0 (wordOf w)` of `MagnusGenDefs`: reading `w` from left to right, the running weight
starts at `0`, increases by `q` at every one of the `p` copies of the first letter and decreases by
`p` at every one of the `q` copies of the second letter; the total weight `p * q - q * p` vanishes,
so the decoration is *closed*.

Explicitly
`decor c 0 (wordOf w) = [(0, i * q) : i < p] ++ [(1, p * q - j * p) : j < q]`,
i.e. the levels occurring are `{0, q, ..., (p-1) * q}` (from the first block) and
`{p, 2p, ..., q * p}` (from the second block).  Since `p` and `q` are coprime and
`0 ≤ i < p`, `1 ≤ q - j ≤ q`, the two level sets are disjoint, so exactly `p + q` distinct levels
occur and, the generator being determined by the block, the decorated word has no repeated letter.

This is the "two-letter" case of the cyclic decomposition of the Magnus rewriting: the decorated
word is the cycle of the cover of the one-relator group `⟨0, 1 | w⟩` over the two generators.
-/

import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.decor_pow_flatMap
import Submission.Work.OROneRel.int_level_sep
import Submission.Work.OROneRel.wordOf_of_pow_mul_of_pow

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### The decoration of a block of repeated positive letters -/

/-- The `c`-weight of a block of `n` copies of the positive letter `(a, true)` is `n * c a`. -/
theorem lsig_replicate_true (c : α → ℤ) (a : α) (n : ℕ) :
    lsig c (List.replicate n (a, true)) = n * c a := by
  induction n with
  | zero => simp [lsig]
  | succ n ih => rw [List.replicate_succ, decor_lsig_cons_true, ih]; push_cast; ring

/-- The decoration of a block of `n` copies of the positive letter `(a, true)`, read starting at
level `i`: the `j`-th copy is decorated at level `i + j * c a`. -/
theorem decor_replicate_true (c : α → ℤ) (a : α) (n : ℕ) (i : ℤ) :
    decor c i (List.replicate n (a, true)) =
      List.ofFn (fun j : Fin n => ((a, i + (j : ℤ) * c a), true)) := by
  induction n generalizing i with
  | zero => simp [decor, List.ofFn_zero]
  | succ n ih =>
    rw [List.replicate_succ, decor, ih, List.ofFn_succ]
    congr 1
    · simp
    · rw [List.ofFn_injective.eq_iff]
      funext j
      congr 1
      simp [Fin.val_succ]
      ring

/-! ### The decorated two-letter cycle -/

/-- The decorated word of the two-letter relator `x ^ p * y ^ q` with weights `q` and `-p`: the
first block `x ^ p` is decorated at the levels `0, q, 2 q, …, (p-1) q` and the second block `y ^ q`
at the levels `p q, p (q-1), …, p`. -/
theorem decor_two_letter (p q : ℕ) :
    decor (fun x : Fin 2 => if x = 0 then (q : ℤ) else -(p : ℤ)) 0
        (List.replicate p ((0 : Fin 2), true) ++ List.replicate q ((1 : Fin 2), true))
      = List.ofFn (fun j : Fin p => (((0 : Fin 2), (j : ℤ) * (q : ℤ)), true))
        ++ List.ofFn (fun k : Fin q =>
            (((1 : Fin 2), (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)), true)) := by
  classical
  let c : Fin 2 → ℤ := fun x => if x = 0 then (q : ℤ) else -(p : ℤ)
  have hc0 : c 0 = (q : ℤ) := by simp [c]
  have hc1 : c 1 = -(p : ℤ) := by
    simp only [c]
    rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
  change decor c 0 (List.replicate p ((0 : Fin 2), true) ++ List.replicate q ((1 : Fin 2), true))
      = List.ofFn (fun j : Fin p => (((0 : Fin 2), (j : ℤ) * (q : ℤ)), true))
        ++ List.ofFn (fun k : Fin q =>
            (((1 : Fin 2), (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)), true))
  rw [decor_append, decor_replicate_true, decor_replicate_true, lsig_replicate_true, hc0, hc1]
  congr 1
  · rw [List.ofFn_injective.eq_iff]
    funext j
    simp
  · rw [List.ofFn_injective.eq_iff]
    funext k
    simp only [Prod.mk.injEq, true_and, and_true, zero_add]
    ring

/-! ### The target -/

/-- **The decorated two-letter cycle is a `(p + q)`-cycle.**  For `p, q ≥ 1` coprime, the
decoration of the two-letter relator `x ^ p * y ^ q` by the weights `q`, `-p` has no repeated letter,
and exactly `p + q` distinct levels occur along it. -/
theorem twoLetter_cycle_decor (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    (Work.OROneRel.decor (fun x : Fin 2 => if x = 0 then (q : ℤ) else -(p : ℤ)) 0
        (Work.OROneRel.wordOf (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q))).Nodup ∧
      ((Work.OROneRel.decor (fun x : Fin 2 => if x = 0 then (q : ℤ) else -(p : ℤ)) 0
        (Work.OROneRel.wordOf (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q))).map
          (fun s => s.1.2)).toFinset.card = p + q := by
  classical
  have hword : wordOf (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q)
      = List.replicate p ((0 : Fin 2), true) ++ List.replicate q ((1 : Fin 2), true) :=
    wordOf_of_pow_mul_of_pow (0 : Fin 2) (1 : Fin 2) (by decide) p q
  rw [hword, decor_two_letter]
  set X : List ((Fin 2 × ℤ) × Bool) :=
    List.ofFn (fun j : Fin p => (((0 : Fin 2), (j : ℤ) * (q : ℤ)), true)) with hX
  set Y : List ((Fin 2 × ℤ) × Bool) :=
    List.ofFn (fun k : Fin q => (((1 : Fin 2), (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)), true))
    with hY
  have hq0 : (q : ℤ) ≠ 0 := by omega
  have hp0 : (p : ℤ) ≠ 0 := by omega
  have hXnod : (X.map (fun s : (Fin 2 × ℤ) × Bool => s.1.2)).Nodup := by
    rw [hX, List.map_ofFn, List.nodup_ofFn]
    intro j₁ j₂ h
    have h' : (j₁ : ℤ) * (q : ℤ) = (j₂ : ℤ) * (q : ℤ) := by simpa using h
    have h'' : (j₁ : ℤ) = (j₂ : ℤ) := mul_right_cancel₀ hq0 h'
    exact Fin.ext (by exact_mod_cast h'')
  have hYnod : (Y.map (fun s : (Fin 2 × ℤ) × Bool => s.1.2)).Nodup := by
    rw [hY, List.map_ofFn, List.nodup_ofFn]
    intro k₁ k₂ h
    have h' : (p : ℤ) * (q : ℤ) - (k₁ : ℤ) * (p : ℤ)
        = (p : ℤ) * (q : ℤ) - (k₂ : ℤ) * (p : ℤ) := by simpa using h
    have h'' : (k₁ : ℤ) * (p : ℤ) = (k₂ : ℤ) * (p : ℤ) := by linarith
    have h''' : (k₁ : ℤ) = (k₂ : ℤ) := mul_right_cancel₀ hp0 h''
    exact Fin.ext (by exact_mod_cast h''')
  constructor
  · rw [hX, hY]
    refine List.Nodup.append ?_ ?_ ?_
    · rw [List.nodup_ofFn]
      intro j₁ j₂ h
      have h' : (j₁ : ℤ) * (q : ℤ) = (j₂ : ℤ) * (q : ℤ) := by simpa using h
      have h'' : (j₁ : ℤ) = (j₂ : ℤ) := mul_right_cancel₀ hq0 h'
      exact Fin.ext (by exact_mod_cast h'')
    · rw [List.nodup_ofFn]
      intro k₁ k₂ h
      have h' : (p : ℤ) * (q : ℤ) - (k₁ : ℤ) * (p : ℤ)
          = (p : ℤ) * (q : ℤ) - (k₂ : ℤ) * (p : ℤ) := by simpa using h
      have h'' : (k₁ : ℤ) * (p : ℤ) = (k₂ : ℤ) * (p : ℤ) := by linarith
      have h''' : (k₁ : ℤ) = (k₂ : ℤ) := mul_right_cancel₀ hp0 h''
      exact Fin.ext (by exact_mod_cast h''')
    · intro a ha hb
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp ha
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hb
      have hj' : (j : ℤ) * (q : ℤ) = a.1.2 := by
        simpa using congrArg (fun s : (Fin 2 × ℤ) × Bool => s.1.2) hj
      have hk' : (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ) = a.1.2 := by
        simpa using congrArg (fun s : (Fin 2 × ℤ) × Bool => s.1.2) hk
      have heq : (j : ℤ) * (q : ℤ) = ((p * q : ℕ) : ℤ) - (k : ℤ) * (p : ℤ) := by
        rw [Nat.cast_mul]
        exact hj'.trans hk'.symm
      exact absurd heq (int_level_sep p q hp hq hcop j k j.isLt k.isLt)
  · have hXcard : ((X.map (fun s : (Fin 2 × ℤ) × Bool => s.1.2)).toFinset).card = p := by
      rw [List.toFinset_card_of_nodup hXnod, hX, List.map_ofFn, List.length_ofFn]
    have hYcard : ((Y.map (fun s : (Fin 2 × ℤ) × Bool => s.1.2)).toFinset).card = q := by
      rw [List.toFinset_card_of_nodup hYnod, hY, List.map_ofFn, List.length_ofFn]
    have hdisj : Disjoint ((X.map (fun s : (Fin 2 × ℤ) × Bool => s.1.2)).toFinset)
        ((Y.map (fun s : (Fin 2 × ℤ) × Bool => s.1.2)).toFinset) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      rw [hX, List.mem_toFinset, List.map_ofFn, List.mem_ofFn] at hx
      rw [hY, List.mem_toFinset, List.map_ofFn, List.mem_ofFn] at hy
      obtain ⟨j, hj⟩ := hx
      obtain ⟨k, hk⟩ := hy
      have hj' : (j : ℤ) * (q : ℤ) = x := by simpa using hj
      have hk' : (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ) = x := by simpa using hk
      have heq : (j : ℤ) * (q : ℤ) = ((p * q : ℕ) : ℤ) - (k : ℤ) * (p : ℤ) := by
        rw [Nat.cast_mul]
        exact hj'.trans hk'.symm
      exact absurd heq (int_level_sep p q hp hq hcop j k j.isLt k.isLt)
    rw [List.map_append, List.toFinset_append, Finset.card_union_of_disjoint hdisj, hXcard, hYcard]

end Work.OROneRel
