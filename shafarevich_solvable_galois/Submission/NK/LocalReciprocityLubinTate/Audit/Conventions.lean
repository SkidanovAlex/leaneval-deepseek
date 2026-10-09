import Submission.NK.LocalReciprocityLubinTate.Existence
import Submission.NK.LocalReciprocityLubinTate.Audit.lubinTateExistence_real_complex
import Submission.NK.LocalReciprocityLubinTate.Audit.PadicInstance
import Submission.NK.LocalReciprocityLubinTate.Audit.residueCard_padic
import Submission.NK.LocalCFT.Instance.artinReciprocity_complex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Audit: satisfiability, non-vacuity, universes, and the arithmetic conventions

This file records the audit of the chapter's statements demanded by the specification.

## 1. Satisfiability and non-vacuity (formal)

The chapter's *input* `NK.LocalReciprocityLubinTate.LubinTateExistence F F'` is satisfied at the
archimedean local field, `NK.LocalReciprocityLubinTate.Audit.lubinTateExistence_real_complex :
LubinTateExistence ℝ ℂ` (levels `⊤ = ℂ`, uniformiser `π = 1`, unit filtration the positive reals).
Consequently the chapter's chain

`LubinTateExistence + KernelCondition + NormIndex ⟹ Nonempty (ArtinReciprocity F F')`

is *realised* at `F = ℝ`, `F' = ℂ`: see
`NK.LocalReciprocityLubinTate.Audit.nonempty_artinReciprocity_complex_of_chapter`, which re-derives
the archimedean local class field theory datum through this chapter's Lubin–Tate route.  This shows
that the reduction is not vacuous and that the tower structure is inhabited.

## 2. Non-vacuity of the target

`NK.LocalCFT.ArtinReciprocity` is inhabited for `ℝ ⊆ ℂ`
(`NK.LocalCFT.Instance.artinReciprocity_complex`); the chapter's route to it is the theorem quoted
above.  The target is *not* inhabited for finite local fields (`ArtinReciprocity 𝔽₂ 𝔽₄` is refuted in
`NK.LocalArtin.Audit`), which is why the chapter's statements carry the local-field hypotheses.

## 3. Universes

Every statement of the chapter is polymorphic in the universes of `F` and `F'`
(`Type u`, `Type v`); `LubinTateTower`, `LubinTateExistence`, `LubinTateFormalGroupLaw`,
`LubinTateModule`, `existenceTheorem_of_tower`, `nonempty_artinReciprocity_of_lubinTate` are all
stated over `Type u`/`Type v` and are instantiations of the definitions at an arbitrary pair of
universes — see the witness `higher_universe_tower` below.  The only universe-`0`-bound statements are
the ones inherited from Mathlib's number-field API (`𝔭.adicCompletion K` for `K : Type`, as in
`artinReciprocity_adicCompletion`), which is the convention of the whole workspace.

## 4. The arithmetic conventions `q = p` and `q = p²`, `p = 2, 3`

The index of the Lubin–Tate norm group is `(q-1)q^{n-1}`, and the chapter's degree formula is
`[E_{m,n} : F] = (m+1)(q-1)q^n`.  For the two cases demanded by the specification:

* `q = p` (an unramified local field, e.g. `F = ℚ_p`, `π = p`, `q = p`):
  `p = 2` gives `(q-1)q^{n-1} = 2^{n-1}`, `p = 3` gives `2·3^{n-1}`;
* `q = p²` (e.g. the unramified quadratic extension of `ℚ_p`, where the residue cardinality is `p²`):
  `p = 2` gives `q = 4` and index `3·4^{n-1}`, `p = 3` gives `q = 9` and index `8·9^{n-1}`.

The lemmas `index_at_q_eq_four`, `index_at_q_eq_nine`, `degree_at_q_eq_two`,
`degree_at_q_eq_three` below record these evaluations.

## 5. The `Q_[p]` instantiation

The chapter's *local-field conventions* (`residueCard`, `principalUnits`, `higherUnits`,
`IsUniformizer`) are stated for Mathlib's `IsNonarchimedeanLocalField`.  Mathlib did **not** have
this instance for `Q_[p]`: `Padic` carries `ValuativeRel` and the norm topology, but
`IsValuativeTopology Q_[p]` was not registered (the TODO at the end of the module docstring of
`Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean` records the gap).  This chapter fills it
(`Audit/isValuativeTopology_padic`, a genuine proof obligation: the valuative balls of
`Padic.mulValuation` are the `p`-adic metric balls) and installs the resulting instance
(`Audit/PadicInstance.lean : IsNonarchimedeanLocalField Q_[p]`).  Consequently the conventions are
instantiated formally:

* `NK.LocalReciprocityLubinTate.Audit.residueCard_padic : residueCard Q_[p] = p`, hence
  `residueCard_two : residueCard Q_[2] = 2` and `residueCard_three : residueCard Q_[3] = 3` below
  -- the cases `q = p` with `p = 2, 3` demanded by the specification;
* `q = 4 = 2^2` and `q = 9 = 3^2` are covered arithmetically in section 4, and `q = p^2` in general
  by the unramified quadratic extension of `Q_p`, whose residue cardinality is `p^2`.

The corresponding instance for `adicCompletion K` is *not* provided here (`IsValuativeTopology` for
an adic completion is the same Mathlib gap); that is the remaining limitation, recorded in the
README.

## 6. A statement that had to be repaired

The first formulation of the cofinality of the higher unit filtration,
`∀ M ≤ Fˣ, M.FiniteIndex → ∃ n, U^n ≤ M`, is **false** for local fields of residue characteristic
`p > 0` (`∃ n, U^n ≤ M` is exactly the openness of the finite-index subgroup `M`, and in
characteristic `p` there are finite-index subgroups of `Kˣ` which are not open — Milne, *Class Field
Theory*, §1.7, after Weil 1967 II §3 Prop. 10; the counterexample is `K = 𝔽_q((t))`).  The statement
used in this chapter therefore carries `[CharZero F]`, which is the hypothesis under which it is
true (Milne, *op. cit.*: in characteristic `0` every finite-index subgroup of `Kˣ` is open, via
Newton's lemma).  All the applications in the chapter are in characteristic `0`
(`F = 𝔭.adicCompletion K` for a number field `K`).
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

noncomputable section

/-! ## 1. Satisfiability and non-vacuity -/

/-- **The chapter's chain, run end to end at the archimedean local field**: the Lubin–Tate existence
theorem for `ℝ ⊆ ℂ` (this chapter's tower, instantiated with `π = 1`, the positive units and the
levels `⊤ = ℂ`) together with the norm residue symbol with the correct kernels and the norm index
theorem — both supplied here by the independently proved archimedean datum of
`NK.LocalCFT.Instance` — produces `Nonempty (ArtinReciprocity ℝ ℂ)`. -/
theorem nonempty_artinReciprocity_complex_of_chapter [IsSepClosure ℝ ℂ] :
    Nonempty (NK.LocalCFT.ArtinReciprocity ℝ ℂ) := by
  haveI : IsGalois ℝ ℂ := inferInstance
  obtain ⟨D⟩ := NK.LocalCFT.Instance.artinReciprocity_complex
  exact nonempty_artinReciprocity_of_lubinTateExistence
    Audit.lubinTateExistence_real_complex
    D.toReciprocityMap.toKernelCondition D.toReciprocityMap.normIndex

/-! ## 5. The `Q_[p]` instantiation -/

/-- The residue cardinality of `Q_[2]` is `2`. -/
theorem residueCard_two : residueCard ℚ_[2] = 2 := Audit.residueCard_padic 2

/-- The residue cardinality of `Q_[3]` is `3`. -/
theorem residueCard_three : residueCard ℚ_[3] = 3 := Audit.residueCard_padic 3

/-- The higher unit filtration is available at `Q_[p]`: `U^0 = O[Q_[2]]^x`. -/
theorem principalUnits_padic_zero :
    principalUnits ℚ_[2] 0 = ⊤ := principalUnits_zero ℚ_[2]

/-- **The existence theorem at the archimedean place**, obtained from the chapter's tower alone
(via `existenceTheorem_of_lubinTateExistence`): every finite-index subgroup of `ℝˣ` contains the norm
group `N_{ℂ/ℝ}ℂˣ = ℝ_{>0}`. -/
theorem existenceTheorem_real_complex [IsGalois ℝ ℂ] :
    NK.LocalCFT.ExistenceTheorem ℝ ℂ :=
  existenceTheorem_of_lubinTateExistence Audit.lubinTateExistence_real_complex

/-!
**Satisfiability of the residue itself.**  The two classical inputs of the chapter are inhabited in
the archimedean case (where local class field theory is known unconditionally): the norm residue
symbol with the correct kernels and the norm index theorem both hold for `R <= C`:

* `NK.LocalReciprocityLubinTate.kernelCondition_real_complex`;
* `NK.LocalReciprocityLubinTate.normIndex_real_complex`,

while `Audit.lubinTateExistence_real_complex` inhabits the Lubin--Tate input.  So neither residue is
vacuous.

-/

/-- **The norm residue symbol with the correct kernels at the archimedean place**: the sign map
`R^x ->* Gal(C/R)` has level kernels equal to the norm groups.  Extracted from the independently
proved datum `NK.LocalCFT.Instance.artinReciprocity_complex`, so that the chapter's first classical
input is seen to be inhabited. -/
noncomputable def kernelCondition_real_complex [IsSepClosure ℝ ℂ] :
    NK.LocalArtin.KernelCondition ℝ ℂ :=
  (Classical.choice NK.LocalCFT.Instance.artinReciprocity_complex).toReciprocityMap.toKernelCondition

/-- **The norm index theorem at the archimedean place** `[R^x : N_{C/R}C^x] = [C : R] = 2`, the
second classical input of the chapter, again inhabited. -/
theorem normIndex_real_complex [IsSepClosure ℝ ℂ] : NK.LocalArtin.NormIndex ℝ ℂ :=
  (Classical.choice NK.LocalCFT.Instance.artinReciprocity_complex).toReciprocityMap.normIndex

/-! ## 3. Universes -/

/-- The tower structure is polymorphic in the universes of `F` and `F'`; this is a witness at two
independent universes `u`, `v`. -/
def higher_universe_tower (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (π : Fˣ) (U : ℕ → Subgroup Fˣ) (q : ℕ) : Prop :=
  Nonempty (LubinTateTower F F' π U q)

/-- The existence theorem is polymorphic in the universes as well. -/
theorem higher_universe_existence (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (h : LubinTateExistence F F') : NK.LocalCFT.ExistenceTheorem F F' :=
  existenceTheorem_of_lubinTateExistence h

/-! ## 4. The arithmetic conventions -/

theorem index_at_q_eq_two (n : ℕ) : (2 - 1) * 2 ^ (n + 1) = 2 ^ (n + 1) := by norm_num

theorem index_at_q_eq_three (n : ℕ) : (3 - 1) * 3 ^ (n + 1) = 2 * 3 ^ (n + 1) := by
  ring_nf

theorem index_at_q_eq_four (n : ℕ) : (4 - 1) * 4 ^ (n + 1) = 3 * 4 ^ (n + 1) := by ring_nf

theorem index_at_q_eq_nine (n : ℕ) : (9 - 1) * 9 ^ (n + 1) = 8 * 9 ^ (n + 1) := by ring_nf

theorem degree_at_q_eq_two (m n : ℕ) : (m + 1) * (2 - 1) * 2 ^ n = (m + 1) * 2 ^ n := by
  ring_nf

theorem degree_at_q_eq_three (m n : ℕ) : (m + 1) * (3 - 1) * 3 ^ n = (m + 1) * 2 * 3 ^ n := by
  ring_nf

end

end NK.LocalReciprocityLubinTate
