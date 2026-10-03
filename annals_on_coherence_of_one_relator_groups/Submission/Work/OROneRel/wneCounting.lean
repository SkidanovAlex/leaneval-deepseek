import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.occ_le_of_isSubwordOf_pow
import Submission.Work.OROneRel.exists_two_mem_relatorLetters_ne
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.letterCountHalfAux
import Submission.Work.OROneRel.exists_rotate_subword_decomposition

/-!
# A letter in which a short subword of a relator drops

Let `T` be a cyclically reduced relator which is not a proper power, of length `≥ 2`, and let `w ≠ 1`
be a subword of a power `T ^ k` of `T` with `2 * |w| ≤ |T|`.  Then there is a generator `y`
occurring in `T` such that the number of letters of `w` different from `y` is *strictly* smaller
than the number of letters of `T` different from `y`.

The point is the following.  Since `w` is shorter than `T`, its reduced word `V` is a prefix of some
rotation of the reduced word `W` of `T`, with a reduced complement `S` of length
`|T| - |w| ≥ |w|`.  Writing `tcount y ·` for the number of `y`-letters, the two quantities to
compare are `|w| - tcount y V` and `|T| - tcount y W = (|V| + |S|) - (tcount y V + tcount y S)`,
so the strict inequality is *equivalent* to `tcount y S < |S|`, i.e. to `S` containing a letter whose
generator is not `y`.  The complementary arc `S` is non-empty (it is at least as long as `w`), so it
contains some letter `p`; since `T` is not a proper power of one generator, it has at least two
generators, and we may choose `y ≠ p.1` among them.

## Main declarations

* `Work.OROneRel.wneCounting`.
-/

namespace Work.OROneRel

universe u

theorem wneCounting {β : Type u} (T : FreeGroup β) {k : ℕ} (w : FreeGroup β)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator T)
    (hpp : ¬ Work.OROneRel.IsProperPower T)
    (hrpos : 2 ≤ Work.OROneRel.relatorNorm T)
    (hsub : Work.OROneRel.IsSubwordOf w (T ^ k))
    (hhalf : 2 * Work.OROneRel.relatorNorm w ≤ Work.OROneRel.relatorNorm T) (hw1 : w ≠ 1) :
    ∃ y ∈ Work.OROneRel.relatorLetters T,
      Work.OROneRel.letterCountNot y w < Work.OROneRel.letterCountNot y T := by
  classical
  -- `w ≠ 1` gives `1 ≤ relatorNorm w`, hence `w` is strictly shorter than `T`
  have hwpos : 1 ≤ Work.OROneRel.relatorNorm w := by
    refine Nat.one_le_iff_ne_zero.mpr fun h0 => hw1 ?_
    exact FreeGroup.norm_eq_zero.mp (by simpa [Work.OROneRel.relatorNorm] using h0)
  have hlen : Work.OROneRel.relatorNorm w < Work.OROneRel.relatorNorm T := by omega
  -- the complementary arc `S` of `w` in the cyclic word of `T`
  obtain ⟨j, S, hVS, hSlen, _hSred⟩ :=
    Work.OROneRel.exists_rotate_subword_decomposition (r := T) (v := w) (k := k) hcyc hsub hlen
  have hS1 : 0 < S.length := by omega
  obtain ⟨p, hpS⟩ := List.exists_mem_of_ne_nil S (List.length_pos_iff.mp hS1)
  -- a generator of `T` different from the generator of `p`
  obtain ⟨x0, hx0, z0, hz0, hx0z0⟩ := Work.OROneRel.exists_two_mem_relatorLetters_ne T hrpos hpp
  have hchoose : ∃ y ∈ Work.OROneRel.relatorLetters T, y ≠ p.1 := by
    by_cases h : x0 ≠ p.1
    · exact ⟨x0, hx0, h⟩
    · push Not at h
      exact ⟨z0, hz0, fun hz => hx0z0 (h.trans hz.symm)⟩
  obtain ⟨y, hy, hyp⟩ := hchoose
  refine ⟨y, hy, ?_⟩
  -- rewrite both letter counts in terms of `tcount`
  have hVw : FreeGroup.mk (FreeGroup.toWord w) = w := FreeGroup.mk_toWord
  have hTmk : FreeGroup.mk (FreeGroup.toWord T) = T := FreeGroup.mk_toWord
  have hVred : FreeGroup.IsReduced (FreeGroup.toWord w) := FreeGroup.isReduced_toWord
  have hWred : FreeGroup.IsReduced (FreeGroup.toWord T) := FreeGroup.isReduced_toWord
  have hcntV : Work.OROneRel.letterCountNot y w =
      (FreeGroup.toWord w).length - Work.OROneRel.tcount y (FreeGroup.toWord w) := by
    have h := Work.OROneRel.letterCountNot_mk_of_isReduced y hVred
    rw [hVw] at h
    exact h
  have hcntT : Work.OROneRel.letterCountNot y T =
      (FreeGroup.toWord T).length - Work.OROneRel.tcount y (FreeGroup.toWord T) := by
    have h := Work.OROneRel.letterCountNot_mk_of_isReduced y hWred
    rw [hTmk] at h
    exact h
  -- the `y`-letters of `T` are those of `w` together with those of the complementary arc
  have hcountW : Work.OROneRel.tcount y (FreeGroup.toWord T) =
      Work.OROneRel.tcount y (FreeGroup.toWord w) + Work.OROneRel.tcount y S := by
    have h1 : Work.OROneRel.tcount y (FreeGroup.toWord w ++ S) =
        Work.OROneRel.tcount y ((FreeGroup.toWord T).rotate j) := by rw [hVS]
    rw [Work.OROneRel.tcount_append, Work.OROneRel.tcount_rotate] at h1
    exact h1.symm
  -- the complementary arc has a letter other than `y`
  have hSlt : Work.OROneRel.tcount y S < S.length := by
    refine lt_of_le_of_ne (Work.OROneRel.tcount_le_length y S) ?_
    intro hcon
    have hall := (Work.OROneRel.tcount_eq_length_iff y S).mp hcon
    exact hyp (hall p hpS).symm
  have hWsum : (FreeGroup.toWord T).length = (FreeGroup.toWord w).length + S.length := by
    have h := congrArg List.length hVS
    rw [List.length_append, List.length_rotate] at h
    omega
  rw [hcntV, hcntT, hcountW, hWsum]
  have hle := Work.OROneRel.tcount_le_length y (FreeGroup.toWord w)
  omega

end Work.OROneRel
