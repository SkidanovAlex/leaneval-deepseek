import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormCorrespondence
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_lubinTateTower_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion

/-!
# Cofinality of the Lubin–Tate levels under the norm-subgroup correspondence

Let `K` be a number field, `Q` a finite place of `K`, `F = Q.adicCompletion K` the corresponding
`p`-adic field, `F' = ` a separable closure of `F`, and `T` a Lubin–Tate tower over `F` with
uniformiser `π` and the higher unit filtration `U^n = higherUnits F n`.

The main result of this file is

`NK.LocalReciprocityLubinTate.Unramified.exists_level_ge_of_normCorrespondence`:

*every* finite abelian Galois level `L ≤ F^{ab}` is contained in some Lubin–Tate level
`T.level m n`.

This is the cofinality statement that converts the explicit reciprocity law — the norm-group
description `N_{E_{m,n}/F} E_{m,n}ˣ = ⟨π^{m+1}⟩ · U^{n+1}` of the levels, which is part of the
datum `T` — into the statement that the levels exhaust the finite abelian extensions. It is the
first half of the "`Nm(Lˣ) ⊇ U_{n,m} ⟹ L ⊆ K_{n,m}`" step in Milne, *Class Field Theory*,
§I.1.15 (the proof of local Kronecker–Weber), and Neukirch, *Algebraic Number Theory*, V.1.7/V.5.5.

## The argument

The norm-group correspondence (`NormCorrespondence`, the `Normensatz`/Umkehrsatz) is the
hypothesis `hcorr`: a containment of norm groups reverses the containment of fields.  So it is
enough to exhibit `m, n` with

`N_{E_{m,n}/F} E_{m,n}ˣ = ⟨π^{m+1}⟩ · U^{n+1} ≤ N_{L/F} Lˣ =: N`,

i.e. to fit the generating pieces of the level's norm group into the norm group of `L`:

* **the higher units.**  `N` has finite index in `Fˣ` — the norm index theorem
  `NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion` gives
  `[Fˣ : N] = [L : F] < ∞` — and the higher unit filtration is cofinal among the finite-index
  subgroups (`NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal`), so `U^{n₀} ≤ N` for some
  `n₀`; then `U^{n+1} ≤ U^{n₀} ≤ N` for `n = n₀`.
* **the powers of the uniformiser.**  In the *abelian* group `Fˣ` one has `x ^ [Fˣ : N] ∈ N` for
  every `x` (`Subgroup.pow_index_mem`); taking `x = π` and `m + 1 = [Fˣ : N]` gives
  `π^{m+1} = π^{[Fˣ : N]} ∈ N`, hence `⟨π^{m+1}⟩ ≤ N`.

Both pieces lying in `N`, so does their supremum, and the correspondence applied with
`L₁ = E_{m,n}`, `L₂ = L` yields `L ≤ E_{m,n}`.
-/

set_option linter.style.haveILetI false

namespace NK.LocalReciprocityLubinTate.Unramified

theorem exists_level_ge_of_normCorrespondence {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K))
    (T : NK.LocalReciprocityLubinTate.LubinTateTower (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π
      (NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K)))
    (hcorr : NK.LocalReciprocityLubinTate.NormCorrespondence (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)))
    (L : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[Q.adicCompletion K] ↥L, σ * τ = τ * σ) :
    ∃ m n : ℕ, L ≤ T.level m n := by
  classical
  -- the norm group of `L`
  let N : Subgroup (Q.adicCompletion K)ˣ :=
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L
  -- the norm index theorem: `[Fˣ : N] = [L : F]`
  have hIdx : N.index = Module.finrank (Q.adicCompletion K) ↥L :=
    NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q L
  have hpos : 0 < N.index := by rw [hIdx]; exact Module.finrank_pos
  have hfin : N.FiniteIndex := Subgroup.finiteIndex_iff.mpr (ne_of_gt hpos)
  -- cofinality of the higher unit filtration
  obtain ⟨n₀, hn₀⟩ := NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal
    (Q.adicCompletion K) N hfin
  refine ⟨N.index - 1, n₀, ?_⟩
  -- the level is finite and normal over `F` by the tower datum
  haveI hfdL : FiniteDimensional (Q.adicCompletion K) ↥(T.level (N.index - 1) n₀) :=
    T.finiteDimensional _ _
  haveI hnorL : Normal (Q.adicCompletion K) ↥(T.level (N.index - 1) n₀) := T.normal _ _
  -- the norm correspondence reduces the claim to a containment of norm groups
  refine hcorr (T.level (N.index - 1) n₀) L (T.commutative _ _) hcomm ?_
  show NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(T.level (N.index - 1) n₀) ≤ N
  -- the explicit reciprocity law: the norm group of the level is `⟨π^{m+1}⟩ · U^{n+1}`
  rw [T.normGroup_eq]
  refine sup_le ?_ ?_
  · rw [Nat.sub_add_cancel hpos]
    exact Subgroup.zpowers_le.mpr (Subgroup.pow_index_mem N π)
  · exact le_trans (NK.LocalReciprocityLubinTate.higherUnits_antitone (Q.adicCompletion K)
      (Nat.le_succ n₀)) hn₀

end NK.LocalReciprocityLubinTate.Unramified
