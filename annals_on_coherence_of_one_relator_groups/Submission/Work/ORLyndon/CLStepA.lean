import Mathlib
import Submission.Work.ORLyndon.CLSym

/-!
# The base case and the exponent-sum-zero branch of the Cohen--Lyndon induction

The invariant `Work.ORLyndon.CLInvariantWith` is proved here

* in the base case `relatorNorm u ≤ 1` (`Work.ORLyndon.CLInvariantWith_of_relatorNorm_le_one`), where
  the root is a single letter up to conjugacy, the root Fox vector is a unit, and the exempted set is
  empty;
* in the exponent-sum-zero branch (`Work.ORLyndon.CLInvariantWith_of_epsZero`), where the
  exponent-sum-zero Magnus step is run with the framing letter `t` (`eps t u = 0`):

  - `(O)` is `Work.ORLyndon.orderOf_of_mmBaseHom`;
  - `CLRegOff` is proved with the exempted set `insert t (symLetter '' Tv)`, where `Tv` is the
    exempted set of the Magnus base: a letter of `u` is blocked exactly when all of its decorated
    symbols lie in `Tv`, and those letters are the images under `Work.ORLyndon.symLetter` of `Tv`
    (`Work.ORLyndon.mmTopSym_notMem`); the framing letter `t` itself has no decorated symbols at all
    and is added separately;
  - `(I)` is `Work.ORLyndon.ann_rootVec_of_component` applied at an *unblocked* letter of `u`, whose
    regularity is supplied by the per-letter step `regular_rootVec_epsZero_top`
    (`regular_rootVec_epsZero_bot` for the bottom form).

The exempted set of the base contributes at most one letter per element
(`Set.ncard_image_le`), so the cardinality bound `ncard ≤ relatorNorm u` is preserved
(`relatorNorm_rootW_lt`).

**What is *not* proved here.**  The `(I)` component of the conclusion needs an unblocked letter of
`u`, i.e. `∃ x ∈ relatorLetters u, x ≠ t, mmTopSym t u l x hxt ∉ Tv` (`hunblk` below).  For a *given*
exempted set `Tv` of the base this is not implied by the counting alone: every non-`t` letter of `u`
can be blocked when `Tv` contains the corresponding extremal symbols.  The theorem below takes it as a
hypothesis; removing it is a separate combinatorial statement about the (recursively produced)
exempted sets, and is the exact remaining gap of the exponent-sum-zero half of the induction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

/-- **The base case of the Cohen--Lyndon induction**: `relatorNorm u ≤ 1`, i.e. `u` is a free
generator up to conjugacy.  Then the root Fox vector at the letter in question is a unit, so the
component-wise regularity holds at *every* letter: the exempted set can be taken empty. -/
theorem CLInvariantWith_of_relatorNorm_le_one {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    {r u : FreeGroup α} {l : ℕ} (hl : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hn : Work.OROneRel.relatorNorm u ≤ 1) :
    CLInvariantWith K r u l ∅ := by
  rcases Work.OROneRel.eq_one_or_exists_letterPow_of_relatorNorm_le_one hn with h1 | ⟨a, s, hle⟩
  · exact absurd (h1.symm ▸ Work.OROneRel.isProperPower_one) hpp
  · subst hle
    subst hpow
    refine ⟨?_, ?_, ?_⟩
    · simpa using (Work.OROneRel.kmsRoot_of_letterPow a s l hl).1
    · intro b hb
      exact ann_rootVec_of_component _ _ a (regular_of_isUnit (isUnit_rootVec_letterPow _ a s)) b hb
    · intro q hq _
      have hqa : q = a := mem_relatorLetters_letterPow a q s hq
      rw [hqa]
      exact regular_of_isUnit (isUnit_rootVec_letterPow _ a s)

/-- **The base case of the induction, in the existential form.** -/
theorem CLInvariant_of_relatorNorm_le_one {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    {r u : FreeGroup α} {l : ℕ} (hl : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hn : Work.OROneRel.relatorNorm u ≤ 1) :
    CLInvariant K r u l :=
  ⟨∅, Set.finite_empty, by simp,
    CLInvariantWith_of_relatorNorm_le_one hl hpow hpp hn⟩

/-- **The exponent-sum-zero branch of the induction step.**  Let `u` be cyclically reduced, not a
proper power, of relator norm `≥ 2`, with a letter `t` of exponent sum zero.  If the invariant (for
the exempted set `Tv`) holds at the Magnus base `⟨mmBeta t (u^l) | mmW t (u^l)⟩` with root
`rootW t u l hcyc he hl`, and if some letter `x ≠ t` of `u` has its top decorated symbol outside `Tv`
(`hunblk`), then the invariant holds at `⟨α | u^l⟩` with root `u`, for the exempted set consisting of
the framing letter `t` and the underlying letters of `Tv`. -/
theorem CLInvariantWith_of_epsZero {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    {Tv : Set (Work.OROneRel.mmBeta t (u ^ l))}
    (hIH : CLInvariantWith K (Work.OROneRel.mmW t (u ^ l))
      (Work.OROneRel.rootW t u l hcyc he hl) l Tv)
    (hunblk : ∃ (x : α) (hxt : x ≠ t), x ∈ Work.OROneRel.relatorLetters u ∧
      mmTopSym t u l x hxt ∉ Tv) :
    CLInvariantWith K (u ^ l) u l (insert t (symLetter '' Tv)) := by
  classical
  -- the per-letter step at any letter whose top decorated symbol is not exempted
  have hbase : ∀ (x : α) (hxt : x ≠ t), x ∈ Work.OROneRel.relatorLetters u →
      mmTopSym t u l x hxt ∉ Tv →
      ∀ b : MonoidAlgebra K (OneRelatorGroup (u ^ l)), b * rootVec K (u ^ l) u x = 0 → b = 0 := by
    intro x hxt hx hsym
    refine regular_rootVec_epsZero_top t u l hl hpp hcyc ht he x hxt hx ?_
    exact hIH.2.2 (mmTopSym t u l x hxt) (mmTopSym_mem_relatorLetters t u l hcyc he hl x hxt hx) hsym
  refine ⟨?_, ?_, ?_⟩
  · exact orderOf_of_mmBaseHom t u l hl hpp hcyc ht he hIH.1
  · obtain ⟨x, hxt, hx, hsym⟩ := hunblk
    exact ann_rootVec_of_component (u ^ l) u x (hbase x hxt hx hsym)
  · intro q hq hqnotin
    have hqt : q ≠ t := fun h =>
      hqnotin (by rw [h]; exact Set.mem_insert_iff.mpr (Or.inl rfl))
    refine hbase q hqt hq ?_
    refine mmTopSym_notMem t u l q hqt (fun s hs hEq => hqnotin ?_)
    rw [← hEq]
    exact Set.mem_insert_iff.mpr (Or.inr ⟨s, hs, rfl⟩)

/-- **The cardinality bound of the exponent-sum-zero branch.**  The exempted set
`insert t (symLetter '' Tv)` of `Work.ORLyndon.CLInvariantWith_of_epsZero` has at most one element
more than `Tv`, so if `Tv` has at most `relatorNorm (rootW t u l hcyc he hl)` elements then the new
exempted set has at most `relatorNorm u` elements (`Work.OROneRel.relatorNorm_rootW_lt`). -/
theorem ncard_insert_symLetter_image_le {α : Type u} [DecidableEq α] {t : α} {r : FreeGroup α}
    (Tv : Set (Work.OROneRel.mmBeta t r)) (hTv : Tv.Finite) (t₀ : α) :
    (insert t₀ (symLetter '' Tv)).ncard ≤ Tv.ncard + 1 :=
  le_trans (Set.ncard_insert_le t₀ (symLetter '' Tv))
    (Nat.add_le_add_right (Set.ncard_image_le (f := symLetter) (s := Tv) hTv) 1)

/-- **The exponent-sum-zero branch, in the existential form** (any exempted set of the base).  The
conclusion is `CLInvariant` at `u`, provided the unblocked-letter hypothesis of
`Work.ORLyndon.CLInvariantWith_of_epsZero`; the cardinality bound is
`Work.ORLyndon.ncard_insert_symLetter_image_le`. -/
theorem CLInvariant_of_epsZero {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    {Tv : Set (Work.OROneRel.mmBeta t (u ^ l))}
    (hTvfin : Tv.Finite)
    (hTvcard : Tv.ncard ≤ Work.OROneRel.relatorNorm (Work.OROneRel.rootW t u l hcyc he hl))
    (hIH : CLInvariantWith K (Work.OROneRel.mmW t (u ^ l))
      (Work.OROneRel.rootW t u l hcyc he hl) l Tv)
    (hunblk : ∃ (x : α) (hxt : x ≠ t), x ∈ Work.OROneRel.relatorLetters u ∧
      mmTopSym t u l x hxt ∉ Tv) :
    CLInvariant K (u ^ l) u l := by
  refine ⟨insert t (symLetter '' Tv), ?_, ?_,
    CLInvariantWith_of_epsZero t u l hl hpp hcyc hn ht he hIH hunblk⟩
  · exact (hTvfin.image symLetter).insert t
  · have h1 := ncard_insert_symLetter_image_le Tv hTvfin t
    have h2 := Work.OROneRel.relatorNorm_rootW_lt t u l hcyc he hl ht
    omega

/-- **The exponent-sum-zero branch with an *empty* exempted set at the base.**  If the base invariant
supplies right regularity at *every* letter of the base root (`Tv = ∅`), then the conclusion is
unconditional: the exempted set produced at `u` is just `{t}`, the framing letter.  This is the
unconditional form of `Work.ORLyndon.CLInvariant_of_epsZero`, and it is the shape in which the step
is applied to the *first* Magnus base (after the base case of the induction). -/
theorem CLInvariant_of_epsZero_empty {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (t : α) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (ht : t ∈ Work.OROneRel.relatorLetters u) (he : Work.OROneRel.eps t u = 0)
    (hIH : CLInvariantWith K (Work.OROneRel.mmW t (u ^ l))
      (Work.OROneRel.rootW t u l hcyc he hl) l ∅) :
    CLInvariant K (u ^ l) u l := by
  obtain ⟨x, hx, hxt⟩ := Work.OROneRel.exists_relatorLetters_ne_of_eps_zero
    (Work.OROneRel.ne_one_of_not_isProperPower hpp) ht he
  refine CLInvariant_of_epsZero t u l hl hpp hcyc hn ht he Set.finite_empty (by simp) hIH
    ⟨x, hxt, hx, ?_⟩
  simp

end Work.ORLyndon
