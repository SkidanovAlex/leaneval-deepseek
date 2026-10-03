import Mathlib
import Submission.Work.OROneRel.exists_complement_of_isSubwordOf_pow
import Submission.Work.OROneRel.isReduced_rotate_of_isCyclicallyReduced

set_option linter.style.haveILetI false

namespace Work.OROneRel

universe u

/-- `FreeGroup.toWord` does not depend on the chosen `DecidableEq` instance: any two decidable
equality instances on `α` are equal (`DecidableEq α` is a subsingleton). -/
theorem toWord_eq_of_decEq {α : Type u} (d₁ d₂ : DecidableEq α) (x : FreeGroup α) :
    @FreeGroup.toWord α d₁ x = @FreeGroup.toWord α d₂ x :=
  congrArg (fun i => @FreeGroup.toWord α i x) (Subsingleton.elim d₁ d₂)

/-- If `v` is a subword of a power of a cyclically reduced relator `r`, and `v` is strictly shorter
than `r`, then the reduced word of `v` is a prefix of some rotation of the reduced word of `r`, with
reduced complement `S` of the expected length.

This is the word-level counterpart of `exists_complement_of_isSubwordOf_pow`: the complement `S` is
the complementary suffix of the rotation, so it is automatically reduced (being a subword of a
rotation of a cyclically reduced word). -/
theorem exists_rotate_subword_decomposition {α : Type u} [DecidableEq α] {r v : FreeGroup α} {k : ℕ}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hsub : Work.OROneRel.IsSubwordOf v (r ^ k))
    (hlen : Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm r) :
    ∃ (j : ℕ) (S : List (α × Bool)),
      FreeGroup.toWord v ++ S = (FreeGroup.toWord r).rotate j ∧
      S.length = Work.OROneRel.relatorNorm r - Work.OROneRel.relatorNorm v ∧
      FreeGroup.IsReduced S := by
  classical
  -- The definitions in `Basic` use the classical `DecidableEq` instance; prove the statement with
  -- that instance and transfer to the ambient one at the end.
  have key : ∃ (j : ℕ) (S : List (α × Bool)),
      @FreeGroup.toWord α (Classical.decEq α) v ++ S =
        (@FreeGroup.toWord α (Classical.decEq α) r).rotate j ∧
      S.length = Work.OROneRel.relatorNorm r - Work.OROneRel.relatorNorm v ∧
      FreeGroup.IsReduced S := by
    letI : DecidableEq α := Classical.decEq α
    obtain ⟨L1, L2, hL⟩ := hsub
    set W := FreeGroup.toWord r with hW
    set Vw := FreeGroup.toWord v with hVw
    have hrcyc : FreeGroup.IsCyclicallyReduced W := by
      show FreeGroup.IsCyclicallyReduced (FreeGroup.toWord r)
      exact hcyc
    -- the reduced word of `r ^ k` is `W ++ W ++ ... ++ W`
    have hflat : FreeGroup.toWord (r ^ k) = (List.replicate k W).flatten := by
      rw [FreeGroup.toWord_pow, ← hW]
      exact (FreeGroup.isReduced_iff_reduce_eq).mp (hrcyc.flatten_replicate k).isReduced
    have hmain : (List.replicate k W).flatten = L1 ++ Vw ++ L2 := by rw [← hflat, hL]
    have hlt : Vw.length < W.length := by
      have h' := hlen
      simp only [relatorNorm, FreeGroup.norm] at h'
      rwa [← hVw, ← hW] at h'
    -- `Vw` is the length `|Vw|` initial segment of the rotation of `W` at position `L1.length`
    have htake : Vw = (W.rotate L1.length).take Vw.length :=
      eq_rotate_take_of_flatten_replicate_eq hmain (le_of_lt hlt)
    have hnorm_r : relatorNorm r = W.length := by
      simp only [relatorNorm, FreeGroup.norm, ← hW]
    have hnorm_v : relatorNorm v = Vw.length := by
      simp only [relatorNorm, FreeGroup.norm, ← hVw]
    refine ⟨L1.length, (W.rotate L1.length).drop Vw.length, ?_, ?_, ?_⟩
    · -- `Vw` is a prefix of the rotation, so appending the complementary suffix recovers it
      nth_rewrite 1 [htake]
      exact List.take_append_drop Vw.length (W.rotate L1.length)
    · -- length bookkeeping
      rw [List.length_drop, List.length_rotate, hnorm_r, hnorm_v]
    · -- the complement is reduced, being a suffix of a reduced rotation
      exact (isReduced_rotate_of_isCyclicallyReduced hrcyc L1.length).infix
        ⟨Vw, [], by
          rw [List.append_nil]
          nth_rewrite 1 [htake]
          exact List.take_append_drop Vw.length (W.rotate L1.length)⟩
  obtain ⟨j, S, h1, h2, h3⟩ := key
  refine ⟨j, S, ?_, h2, h3⟩
  rw [toWord_eq_of_decEq (inferInstance : DecidableEq α) (Classical.decEq α) v,
    toWord_eq_of_decEq (inferInstance : DecidableEq α) (Classical.decEq α) r]
  exact h1

end Work.OROneRel
