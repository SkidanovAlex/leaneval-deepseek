/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Case 2 of the Freiheitssatz: no letter of the relator has exponent sum zero

`Work.OROneRel.freiheitssatz_case2` is the second case engine of the Freiheitssatz (Magnus 1930) in
the form of McCool--Schupp and Putman: for a cyclically reduced relator `r` all of whose letters
occur with nonzero exponent sum, generators `t ∈ T` and `x ∉ T` occurring in `r`, and `r ∉ ⟨T⟩`,
the canonical map `F(T) →* ⟨α | r⟩` is injective.

The mathematical content is the substitution (Putman's Case 2, the "Magnus trick")

  `ψ : t ↦ t ^ (σ_x r)`,  `x ↦ x * t ^ (- σ_t r)`,  `s ↦ s` for `s ∉ {t,x}`,

which is injective on the free group (`powSubst`) and arranges `σ_t (ψ r) = 1` (`sigma_t_Psi`),
while keeping `σ_x` unchanged (`sigma_x_Psi`), so that the exponent-sum-zero case applies to a
cyclically reduced conjugate of `ψ r` (`Work.OROneRel.ZeroExpsumEngine`, the already-proved engine).
Since the composite `F(T) →* ⟨α | r⟩ →* ⟨α | ψ r⟩` factors as `θ ∘ ψ` with `θ` injective by the
exponent-sum-zero case and `ψ` injective, the canonical map itself is injective.

Everything is assembled here: the type-universal induction hypothesis
(`Work.OROneRel.FreiheitssatzBelow`), the exponent-sum-zero engine
(`Work.OROneRel.freiheitssatz_zero_expsum_engine`), and the Case 2 step
(`Work.OROneRel.all_nonzero_step`).
-/
import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.rewrite_length_lt
import Submission.Work.OROneRel.injective_presentedGroupMap_of_disjoint
import Submission.Work.OROneRel.presentedGroupMap_injective_mono
import Submission.Work.OROneRel.freiheitssatz_zero_expsum_engine
import Submission.Work.OROneRel.case2_substitution
import Submission.Work.OROneRel.magRewRel_subst_lt
import Submission.Work.OROneRel.free_subst_basis_corrected
import Submission.Work.OROneRel.injective_presentedGroupMap_of_isConj

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- A letter of `r` outside `T`, from the failure of support. -/
theorem exists_letter_of_not_supportedOn_case2 {r : FreeGroup α} {T : Set α}
    (h : ¬ SupportedOn r T) : ∃ a ∈ relatorLetters r, a ∉ T := by
  by_contra hcon
  exact h fun a ha => by_contra fun haT => hcon ⟨a, ha, haT⟩

/-- The Magnus rewriting of a relator is strictly shorter, provided the letter occurs in it. -/
theorem relatorNorm_magRewRel_lt_case2 {r : FreeGroup α} {t : α} (ht : t ∈ relatorLetters r) :
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

/-- The Freiheitssatz holds for every relator of norm `≤ n` as soon as it holds below `n + 1`. -/
theorem freiheitssatzBelow_of_le_case2 (n : ℕ)
    (ih : ∀ (β : Type u) (s : FreeGroup β), relatorNorm s ≤ n → FreiheitssatzAt s) :
    FreiheitssatzBelow.{u} (n + 1) := by
  intro β s hs
  exact ih β s (by omega)

/-- **The induction step of the Freiheitssatz** (with the type-universal induction hypothesis). -/
theorem freiheitssatz_step_case2 (r : FreeGroup α) (hcyc : IsCyclicallyReducedRelator r) (T : Set α)
    (hT : r ∉ Subgroup.closure (FreeGroup.of '' T))
    (IH : FreiheitssatzBelow.{u} (relatorNorm r)) :
    Function.Injective (presentedGroupMap r T) := by
  classical
  have hr1 : r ≠ 1 := fun h => hT (by rw [h]; exact Subgroup.one_mem _)
  have hnotsup : ¬ SupportedOn r T := fun h => hT ((letters_closure_iff r T).mpr h)
  obtain ⟨x, hxl, hxT⟩ := exists_letter_of_not_supportedOn_case2 hnotsup
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
    · obtain ⟨t, htl, ht0⟩ := hzero
      by_cases htx : t = x
      · subst htx
        have htT' : t ∉ T' := by rw [hT'def]; exact fun h => h rfl
        have hyt : y ≠ t := fun h => hyx h
        exact freiheitssatz_zero_expsum_engine (t := t) (x := y) hyt (relatorNorm r) r T'
          hcyc htl hyl ht0 (Or.inr htT') hT'mem (relatorNorm_magRewRel_lt_case2 htl) IH
      · have hxt : x ≠ t := fun h => htx h.symm
        have hxT' : x ∉ T' := by rw [hT'def]; exact fun h => h rfl
        exact freiheitssatz_zero_expsum_engine (t := t) (x := x) hxt (relatorNorm r) r T'
          hcyc htl hxl ht0 (Or.inl hxT') hT'mem (relatorNorm_magRewRel_lt_case2 htl) IH
    · push_neg at hzero
      exact case2_substitution (α := α) r y x hcyc hyl hxl (fun h => hyx h.symm) hT'mem hzero
        (fun β s hs => IH β s hs)
        (fun N => freiheitssatz_zero_expsum_engine (t := y) (x := x) (fun h => hyx h.symm) N)
        (fun u s U h hU => injective_presentedGroupMap_of_isConj h hU)
        (fun v hv hc => magRewRel_subst_lt (α := α) r y x hcyc hyl hxl (fun h => hyx h.symm)
          (hzero y hyl) (hzero x hxl) v hv hc)
        (fun p hp => free_subst_basis_corrected x y (fun h => hyx h.symm) p hp)

/-- **The Freiheitssatz**, by strong induction on the norm of the relator, uniformly over the
generating type. -/
theorem freiheitssatz_uncond_case2 (n : ℕ) :
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
      refine freiheitssatz_step_case2 r hcyc T hT ?_
      rw [hnr]
      exact freiheitssatzBelow_of_le_case2 n ih

/-- **Case 2 of the Freiheitssatz.**  If no letter of the cyclically reduced relator `r` has
exponent sum zero, then for any set `T` of generators with `r ∉ ⟨T⟩` the canonical map
`F(T) →* ⟨α | r⟩` is injective. -/
theorem freiheitssatz_case2 {α : Type u} (r : FreeGroup α) (T : Set α) (t x : α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hx : x ∈ Work.OROneRel.relatorLetters r)
    (htx : x ≠ t) (htT : t ∈ T) (hxT : x ∉ T)
    (hT : r ∉ Subgroup.closure (FreeGroup.of '' T))
    (hall : ∀ s ∈ Work.OROneRel.relatorLetters r, Work.OROneRel.sigma s r ≠ 1)
    (IH : ∀ s : FreeGroup α, Work.OROneRel.relatorNorm s < Work.OROneRel.relatorNorm r →
      Work.OROneRel.FreiheitssatzAt s) :
    Function.Injective (Work.OROneRel.presentedGroupMap r T) := by
  have hT'' : r ∉ Subgroup.closure (FreeGroup.of '' {a : α | a ≠ x}) :=
    fun h => (letters_closure_iff r {a : α | a ≠ x}).mp h hx rfl
  have hinj : Function.Injective (Work.OROneRel.presentedGroupMap r {a : α | a ≠ x}) :=
    freiheitssatz_uncond_case2 (relatorNorm r) α r le_rfl hcyc _ hT''
  exact presentedGroupMap_injective_mono (r := r) (T := T) (T' := {a : α | a ≠ x})
    (fun a ha => show a ≠ x from fun h => hxT (h ▸ ha)) hinj

end Work.OROneRel
