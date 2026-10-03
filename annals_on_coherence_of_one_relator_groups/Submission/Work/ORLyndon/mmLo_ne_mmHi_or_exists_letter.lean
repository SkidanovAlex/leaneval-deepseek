/-
Copyright: subproject `ORLyndon` -- the extremal decorated symbols of the Magnus rewriting.

# The extremal decorations of a letter are not both trivial

Let `u` be a cyclically reduced relator of norm `≥ 2` which is not a proper power, let `t` be a
letter of exponent sum `0` in `u`, and let `x ≠ t` be another letter of `u`.  Then *either* the
occurrences of `x` in the Magnus rewriting `mmList t u` carry at least two different decorations
(`mmLo t u x ≠ mmHi t u x`), *or* there is a letter of `u` different from both `t` and `x`.

Equivalently: the set of extremal decorated symbols `(x, mmLo t u x)`, `(x, mmHi t u x)` of the
letters `x ≠ t` occurring in `u` has at least two elements.

## The argument

Write `γ : MMAlpha t = {a // a ≠ t} × ℤ` for the decorated alphabet and `w := of t ^ k * of x * of t ^ (-k)`
for the decorated letter, `k := mmLo t u ⟨x, hxt⟩`.

Assume towards a contradiction that every letter of `u` is `t` or `x`, and that all occurrences of
`x` carry the *same* decoration `k` (`mmLo = mmHi`).  Since `x` occurs, `mmDecs t u ⟨x,hxt⟩` is
nonempty, so the two assumptions together say:

  every element of `mmList t u` equals `((⟨x, hxt⟩, k), b)` for some `b : Bool`.

Writing `s` for the exponent sum of the list `mmList t u` (the number of positive signs minus the
number of negative ones), the product of the decorated letters is the single element
`of (⟨x,hxt⟩, k) ^ s` of `F(MMAlpha t)`, and `magnusMap t` — the homomorphism sending the decorated
letter `(y,i)` to the conjugate `t ^ i * y * t ^ (-i)` — turns this into

  `u = (of t ^ k * of x * of t ^ (-k)) ^ s`  (Telescoping/Magnus rewriting identity, `he`).

Now distinguish three cases:

* `s = 0`: then `u = 1`, and `1 = 1 ^ 2` is a proper power, contradicting `hpp`.
* `k = 0`: then `u = of x ^ s`; since `2 ≤ relatorNorm u = |s|` (`hn`), the element `of x ^ s` is a
  proper power (`|s| ≥ 2`), again contradicting `hpp`.
* `k ≠ 0` and `s ≠ 0`: then `u = of t ^ k * of x ^ s * of t ^ (-k)`, whose reduced word is
  `t ^ k x ^ s t ^ (-k)`; its first and last letters have the same generator `t` but opposite signs,
  so it is *not* cyclically reduced — contradicting `hcyc`.

So the negation of the first alternative forces a letter other than `t` and `x`, which is the second
alternative.
-/
import Mathlib
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.Basic
import Submission.Work.ORLyndon.not_isCyclicallyReduced_toWord_conj
import Submission.Work.ORLyndon.relatorNorm_of_zpow
import Submission.Work.ORLyndon.isProperPower_of_zpow
import Submission.Work.ORLyndon.mk_eq_of_forall_fst_eq
import Submission.Work.ORLyndon.fst_mem_relatorLetters_of_mem_mmList

namespace Work.ORLyndon

theorem mmLo_ne_mmHi_or_exists_letter {α : Type*} [DecidableEq α] (t x : α) (u : FreeGroup α)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u) (he : Work.OROneRel.eps t u = 0)
    (hx : x ∈ Work.OROneRel.relatorLetters u) (hxt : x ≠ t) :
    Work.OROneRel.mmLo t u ⟨x, hxt⟩ ≠ Work.OROneRel.mmHi t u ⟨x, hxt⟩ ∨
      ∃ y ∈ Work.OROneRel.relatorLetters u, y ≠ t ∧ y ≠ x := by
  classical
  by_cases hB : ∃ y ∈ Work.OROneRel.relatorLetters u, y ≠ t ∧ y ≠ x
  · exact Or.inr hB
  · refine Or.inl ?_
    -- every letter of `u` is `t` or `x`
    have hB' : ∀ y, y ∈ Work.OROneRel.relatorLetters u → y = t ∨ y = x := by
      intro y hy
      by_cases h1 : y = t
      · exact Or.inl h1
      · by_cases h2 : y = x
        · exact Or.inr h2
        · exact absurd ⟨y, hy, h1, h2⟩ hB
    intro hEq
    -- the common decoration of the occurrences of `x`
    set k : ℤ := Work.OROneRel.mmLo t u ⟨x, hxt⟩ with hkdef
    -- every decorated letter in the Magnus rewriting is `((x, k), b)`
    have hconst : ∀ p ∈ Work.OROneRel.mmList t u, p.1 = (⟨x, hxt⟩, k) := by
      rintro ⟨⟨y, i⟩, b⟩ hp
      have hlet : (y : α) ∈ Work.OROneRel.relatorLetters u :=
        fst_mem_relatorLetters_of_mem_mmList t u hp
      have hp1 : y = (⟨x, hxt⟩ : {a : α // a ≠ t}) := by
        refine Subtype.ext ?_
        rcases hB' (y : α) hlet with h | h
        · exact absurd h y.2
        · exact h
      have hdec : i ∈ Work.OROneRel.mmDecs t u ⟨x, hxt⟩ :=
        (Work.OROneRel.mem_mmDecs_iff t u ⟨x, hxt⟩ i).mpr ⟨b, by rwa [hp1] at hp⟩
      have h1 : k ≤ i := by
        rw [hkdef, Work.OROneRel.mmLo, dif_pos ⟨i, hdec⟩]
        exact Finset.min'_le _ _ hdec
      have h2 : i ≤ k := by
        rw [hEq, Work.OROneRel.mmHi, dif_pos ⟨i, hdec⟩]
        exact Finset.le_max' _ _ hdec
      exact Prod.ext hp1 (le_antisymm h2 h1)
    -- the exponent sum `s` of the Magnus rewriting
    set s : ℤ :=
      ((Work.OROneRel.mmList t u).map (fun p => if p.2 then (1 : ℤ) else -1)).sum with hsdef
    have hmk : FreeGroup.mk (Work.OROneRel.mmList t u) = FreeGroup.of (⟨x, hxt⟩, k) ^ s := by
      rw [hsdef]
      exact mk_eq_of_forall_fst_eq hconst
    -- the telescoping (Magnus rewriting) identity
    have hu : u = (FreeGroup.of t ^ k * FreeGroup.of x * FreeGroup.of t ^ (-k)) ^ s := by
      have h1 : u = Work.OROneRel.magnusMap t (FreeGroup.of (⟨x, hxt⟩, k) ^ s) := by
        rw [← Work.OROneRel.magnusMap_mmList t u he, hmk]
      have h2 : Work.OROneRel.magnusMap t (FreeGroup.of (⟨x, hxt⟩, k)) =
          FreeGroup.of t ^ k * FreeGroup.of x * FreeGroup.of t ^ (-k) :=
        Work.OROneRel.magnusMap_apply t ⟨x, hxt⟩ k
      rw [h1, map_zpow, h2]
    rcases eq_or_ne s 0 with hs0 | hs0
    · -- `u = 1` is a proper power
      have hu1 : u = 1 := by rw [hu, hs0, zpow_zero]
      exact hpp (by rw [hu1]; exact Work.OROneRel.isProperPower_one)
    · rcases eq_or_ne k 0 with hk0 | hk0
      · -- `u = of x ^ s` with `|s| ≥ 2` is a proper power
        have hu' : u = FreeGroup.of x ^ s := by
          rw [hu, hk0]
          simp
        have h2 : 2 ≤ s.natAbs := by
          rw [← relatorNorm_of_zpow x s, ← hu']
          exact hn
        exact hpp (by rw [hu']; exact isProperPower_of_zpow x h2)
      · -- `u = of t ^ k * of x ^ s * of t ^ (-k)` is not cyclically reduced
        have hw : (FreeGroup.of t ^ k * FreeGroup.of x * FreeGroup.of t ^ (-k)) ^ s
            = FreeGroup.of t ^ k * FreeGroup.of x ^ s * FreeGroup.of t ^ (-k) := by
          rw [show FreeGroup.of t ^ (-k) = (FreeGroup.of t ^ k)⁻¹ from zpow_neg (FreeGroup.of t) k,
            ← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
        have hcycX : Work.OROneRel.IsCyclicallyReducedRelator
            (FreeGroup.of t ^ k * FreeGroup.of x ^ s * FreeGroup.of t ^ (-k)) := by
          rw [← hw, ← hu]
          exact hcyc
        have hcycF : FreeGroup.IsCyclicallyReduced
            (@FreeGroup.toWord α (Classical.decEq α)
              (FreeGroup.of t ^ k * FreeGroup.of x ^ s * FreeGroup.of t ^ (-k))) :=
          hcycX
        exact @not_isCyclicallyReduced_toWord_conj α (Classical.decEq α) t x k s hxt hk0 hs0 hcycF

end Work.ORLyndon
