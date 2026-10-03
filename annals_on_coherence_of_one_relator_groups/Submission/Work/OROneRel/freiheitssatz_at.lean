/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Freiheitssatz (Magnus 1930)

`Work.OROneRel.freiheitssatz_at`: for every `r : FreeGroup α`, if `r` is cyclically reduced and
`T ⊆ α` is a set of generators that does not generate `r`, then the canonical map
`F(T) →* ⟨α | r⟩` is injective.

The proof is by strong induction on `relatorNorm r`, following Magnus' argument in the form given by
McCool--Schupp and Putman: reduce to `T = α \ {x}` for a letter `x` of `r`, and then

* if some letter `t` of `r` has exponent sum zero in `r`, decompose `⟨α | r⟩` as an HNN extension
  over the one-relator group obtained by Magnus rewriting `r` with respect to `t`
  (`Work.OROneRel.freiheitssatz_zero_expsum_engine`: the stable letter is `t`, and the letter `x`
  outside `T` controls the "strip" of the base used in the decomposition);
* otherwise substitute `t ↦ t ^ (σ_x r)`, `x ↦ x * t ^ (-σ_t r)` to reach the exponent-sum-zero case
  (`Work.OROneRel.freiheitssatz_case2`).

Everything is assembled here; the case engines and the auxiliary word-combinatorics lemmas are in
the sibling files of this directory.  Note that the induction hypothesis
`FreiheitssatzBelow (relatorNorm r)` is *not* an induction hypothesis about `α` alone: the HNN step
passes to the generating type `(α \ {t}) × ℤ`, so the hypothesis is formulated for all generating
types in the universe (`Work.OROneRel.FreiheitssatzBelow`).
-/
import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.rewrite_length_lt
import Submission.Work.OROneRel.rewrite_isReduced
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.injective_presentedGroupMap_of_disjoint
import Submission.Work.OROneRel.presentedGroupMap_injective_mono
import Submission.Work.OROneRel.injective_presentedGroupMap_of_isConj
import Submission.Work.OROneRel.free_subst_basis_corrected
import Submission.Work.OROneRel.freiheitssatz_zero_expsum_engine
import Submission.Work.OROneRel.magRewRel_subst_lt
import Submission.Work.OROneRel.case2_substitution

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- A letter of `r` outside `T`, from the failure of support. -/
theorem exists_letter_of_not_supportedOn {r : FreeGroup α} {T : Set α} (h : ¬ SupportedOn r T) :
    ∃ a ∈ relatorLetters r, a ∉ T := by
  by_contra hcon
  exact h fun a ha => by_contra fun haT => hcon ⟨a, ha, haT⟩

/-- The Magnus rewriting of a relator is strictly shorter, provided the letter occurs in it. -/
theorem relatorNorm_magRewRel_lt {r : FreeGroup α} {t : α} (ht : t ∈ relatorLetters r) :
    relatorNorm (magRewRel t r) < relatorNorm r := by
  classical
  letI : DecidableEq ({a : α // a ≠ t} × ℤ) := Classical.decEq _
  obtain ⟨b, hb⟩ : ∃ b : Bool, (t, b) ∈ r.toWord := ht
  have hle : relatorNorm (magRewRel t r) ≤ (rewrite t r.toWord).length := FreeGroup.norm_mk_le
  have hlt : (rewrite t r.toWord).length < r.toWord.length := by
    refine rewrite_length_lt t (L := r.toWord) ?_
    cases b
    · exact Or.inr hb
    · exact Or.inl hb
  have hnorm : relatorNorm r = (FreeGroup.toWord r).length := rfl
  omega

/-- The Freiheitssatz holds for a relator of norm `≤ n` as soon as it holds below `n + 1`. -/
theorem freiheitssatzBelow_of_le (n : ℕ)
    (ih : ∀ (β : Type u) (s : FreeGroup β), relatorNorm s ≤ n → FreiheitssatzAt s) :
    FreiheitssatzBelow.{u} (n + 1) := by
  intro β s hs
  exact ih β s (by omega)

/-- **The induction step of the Freiheitssatz.** -/
theorem freiheitssatz_step (r : FreeGroup α) (hcyc : IsCyclicallyReducedRelator r) (T : Set α)
    (hT : r ∉ Subgroup.closure (FreeGroup.of '' T))
    (IH : FreiheitssatzBelow.{u} (relatorNorm r)) :
    Function.Injective (presentedGroupMap r T) := by
  classical
  have hr1 : r ≠ 1 := fun h => hT (by rw [h]; exact Subgroup.one_mem _)
  have hnotsup : ¬ SupportedOn r T := fun h => hT ((letters_closure_iff r T).mpr h)
  obtain ⟨x, hxl, hxT⟩ := exists_letter_of_not_supportedOn hnotsup
  -- it suffices to prove the statement for `T' = α \ {x}`
  set T' : Set α := {a | a ≠ x} with hT'def
  refine presentedGroupMap_injective_mono (r := r) (T := T) (T' := T')
    (fun a ha => show a ≠ x from fun h => hxT (h ▸ ha)) ?_
  have hT'mem : r ∉ Subgroup.closure (FreeGroup.of '' T') :=
    fun h => (letters_closure_iff r T').mp h hxl rfl
  by_cases hdisj : ∀ a ∈ relatorLetters r, a ∉ T'
  · exact injective_presentedGroupMap_of_disjoint r T' hdisj
  · push_neg at hdisj
    obtain ⟨y, hyl, hyT'⟩ := hdisj
    have hyx : y ≠ x := hyT'
    by_cases hzero : ∃ t ∈ relatorLetters r, sigma t r = 1
    · -- **Case 1**: some letter `t` has exponent sum zero; the HNN engine applies.
      obtain ⟨t, htl, ht0⟩ := hzero
      by_cases htx : t = x
      · -- `t = x ∉ T'`: the stable letter is `t`, the strip letter is `y ∈ T'`
        have hxT' : x ∉ T' := by rw [hT'def]; exact fun h => h rfl
        have htT' : t ∉ T' := by rw [htx]; exact hxT'
        have hyt : y ≠ t := fun h => hyx (h.trans htx)
        exact (freiheitssatz_zero_expsum_engine (t := t) (x := y) hyt (relatorNorm r)) r T'
          hcyc htl hyl ht0 (Or.inr htT') hT'mem (relatorNorm_magRewRel_lt htl) IH
      · -- `t ≠ x`: the stable letter is `t`, the strip letter is `x ∉ T'`
        have hxt : x ≠ t := fun h => htx h.symm
        have hxT' : x ∉ T' := by rw [hT'def]; exact fun h => h rfl
        exact (freiheitssatz_zero_expsum_engine (t := t) (x := x) hxt (relatorNorm r)) r T'
          hcyc htl hxl ht0 (Or.inl hxT') hT'mem (relatorNorm_magRewRel_lt htl) IH
    · -- **Case 2**: no letter has exponent sum zero; substitute and apply Case 1.
      push_neg at hzero
      have hT'' : r ∉ Subgroup.closure (FreeGroup.of '' {a : α | a ≠ x}) := hT'mem
      exact case2_substitution (t := y) (x := x) (r := r) hcyc hyl hxl (fun h => hyx h.symm)
        hT'' hzero IH
        (fun N => freiheitssatz_zero_expsum_engine (t := y) (x := x) (fun h => hyx h.symm) N)
        (fun u s U h hU => injective_presentedGroupMap_of_isConj h hU)
        (fun v hv hc => magRewRel_subst_lt (t := y) (x := x) r hcyc hyl hxl (fun h => hyx h.symm)
          (hzero y hyl) (hzero x hxl) v hv hc)
        (fun p hp => free_subst_basis_corrected x y (fun h => hyx h.symm) p hp)

/-- **The Freiheitssatz** (Magnus 1930), by strong induction on the length of the relator. -/
theorem freiheitssatz_uncond (n : ℕ) :
    ∀ (α : Type u) (r : FreeGroup α), relatorNorm r ≤ n → FreiheitssatzAt r := by
  induction n with
  | zero =>
    intro α r hr hcyc T hT
    classical
    have h1 : r = 1 := FreeGroup.norm_eq_zero.mp (Nat.eq_zero_of_le_zero hr)
    exact absurd (by rw [h1]; exact Subgroup.one_mem _) hT
  | succ n ih =>
    intro α r hr hcyc T hT
    by_cases hle : relatorNorm r ≤ n
    · exact ih α r hle hcyc T hT
    · have hnr : relatorNorm r = n + 1 := by omega
      refine freiheitssatz_step r hcyc T hT ?_
      rw [hnr]
      exact freiheitssatzBelow_of_le n ih

theorem freiheitssatz_at {α : Type u} (r : FreeGroup α) :
    Work.OROneRel.FreiheitssatzAt r :=
  freiheitssatz_uncond (relatorNorm r) α r le_rfl

end Work.OROneRel
