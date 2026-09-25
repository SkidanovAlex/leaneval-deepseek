import Mathlib
import Submission.Work.AbstractDictionary.Defs
import Submission.Work.AbstractDictionary.Arithmetic

/-!
# `Work.AbstractDictionary` -- the minimal hypotheses of the dictionary

**Namespace** `Work.AbstractDictionary`; module `Submission.Work.AbstractDictionary.Sharp`.

`Work.AbstractDictionary.Main` reduces `Work.RelatorRank.GaschutzCohomologicalValue Γ` to

* the **closed** Gaschütz value theorem for every dense generating five-family
  (`Work.AbstractDictionary.GaschutzProP2Value`, which decomposes into
  `Work.HopfGaschutz.ProPHopfCohomologicalInput` and `ProPHopfCohomologicalBound`), and
* the residual `2`-finiteness side condition `ResidualTwoFinitenessPresentations`.

That side condition is *equivalent*, in this setting, to the statement that the closed relation
condition determines the abstract relation kernel
(`Work.AbstractDictionary.residualTwoFinitenessPresentations_iff_kernelEquality`); it is a genuine
condition, as `Γ = ℤ/2`, `gen` the generator, `S = {x⁶}` shows
(`Work.HopfGaschutz.Counterexample`).  A caller who does not want to assume it -- for instance
because it is a `∀`-statement over *all* relator sets satisfying the closed condition, hence
potentially stronger than what the classical construction delivers for the relator set it
actually produces -- can instead use the *minimal* hypotheses recorded here:

* `ProPHopfCohomologicalBound 5 gen` for every dense `gen` -- the *easy* half of the value theorem
  (a closed presentation with `r` relators bounds `dim_{𝔽₂} H²_cont` by `r`), a pro-`2` five-term
  sequence statement, true for every generating family; and
* `GaschutzPresentationExists Γ` -- *some* dense generating five-family on which the cohomological
  bound produces an **abstract** presentation with that many relators.  This is the half of the
  classical Gaschütz/Shafarevich--Koch theorem that is genuinely hard, stated in the normalisation
  of `Work.RelatorRank.RelatorRankLe` (abstract normal closure) and only for a family that is
  produced by the classical construction -- so it makes no claim about "wild" generating families,
  and in particular no claim of finiteness of the normal generation number for arbitrary
  families.

`gaschutzCohomologicalValue_of_bound_and_presentationExists` proves the dictionary from those two,
and `gaschutzCohomologicalValue_of_inputs` (`Main.lean`) is the same theorem along the
closed-normalisation route.  Both are stated for `GeneratorRank Γ = 5`; in the arithmetic setting
that is `Work.TameSalle.generatorRank_eq_five_of_isMaximalTamePro2`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.AbstractDictionary

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **The `⟸`-half of the dictionary for *one* generating family, in the minimal form.**

There is a densely generating five-family `gen` of `Γ` such that every cohomological bound
`dim_{𝔽₂} H²_cont(Γ,𝔽₂) ≤ r` produces a relator set of at most `r` elements whose **abstract**
normal closure is the relation kernel `ker (FreeGroup.lift gen)`.

This is the half of the classical Gaschütz/Shafarevich--Koch relation count that is genuinely hard,
in the normalisation `Work.RelatorRank.RelatorRankLe` uses.  It is stated for a *suitable* family
only, which is exactly what the arithmetic constructions produce
(`Work.TameArithmetic.TamePro2Presentation` is such a family together with its relators); it
therefore assumes nothing about the finiteness of the normal generator number of the relation
kernel of an arbitrary densely generating family. -/
def GaschutzPresentationExists (Γ : Type*) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] : Prop :=
  ∃ gen : Fin 5 → Γ, Work.RelatorRank.DenseGenerating gen ∧
    ∀ r : ℕ, Work.RelatorRank.ContH2DimLe Γ r →
      ∃ rel : Finset (FreeGroup (Fin 5)), rel.card ≤ r ∧
        MonoidHom.ker (FreeGroup.lift gen) =
          Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5)))

/-- **The dictionary from the minimal hypotheses.**  For a pro-`2` group with `GeneratorRank Γ = 5`:
the easy half of the closed value theorem for every dense generating five-family, plus the hard half
for one suitable family, give `Work.RelatorRank.GaschutzCohomologicalValue Γ`.

No residual `2`-finiteness side condition is needed: the hard half is assumed directly in the
abstract normalisation for the family it is produced by. -/
theorem gaschutzCohomologicalValue_of_bound_and_presentationExists
    (hgr : Work.RelatorRank.GeneratorRank Γ = 5)
    (hbound : ∀ gen : Fin 5 → Γ, Work.RelatorRank.DenseGenerating gen →
      ProPHopfCohomologicalBound 5 gen)
    (hex : GaschutzPresentationExists Γ) :
    Work.RelatorRank.GaschutzCohomologicalValue Γ := by
  obtain ⟨gen₀, hgen₀, hpres₀⟩ := hex
  intro r
  constructor
  · -- presentation `⟹` cohomology: feed the given relators to the easy half
    intro h
    have h' : Work.RelatorRank.HasProP2Presentation Γ (Work.RelatorRank.GeneratorRank Γ) r :=
      Work.RelatorRank.relatorRankLe_iff.mp h
    rw [hgr] at h'
    obtain ⟨P⟩ := h' 
    refine (hbound P.gen P.dense) r ⟨P.rel, P.card_le, ?_, ?_⟩
    · intro s hs
      rw [← MonoidHom.mem_ker, P.ker_eq]
      exact Subgroup.subset_normalClosure hs
    · intro Q _ _ hQ φ hφ
      rw [P.ker_eq]
      exact Subgroup.normalClosure_le_normal fun s hs => MonoidHom.mem_ker.mpr (hφ s hs)
  · -- cohomology `⟹` presentation: use the family supplied by `GaschutzPresentationExists`
    intro h
    obtain ⟨rel, hcard, hker⟩ := hpres₀ r h
    refine Work.RelatorRank.relatorRankLe_iff.mpr ?_
    rw [hgr]
    exact ⟨gen₀, rel, hgen₀, hcard, hker⟩

/-! ## The arithmetic normalisation -/

variable {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]

/-- **The dictionary for a maximal tame pro-`2` extension, from the minimal hypotheses.**  The
generator rank `d(Γ) = 5` is *proved* here (`Work.TameSalle`), so the only inputs are the easy half
of the closed value theorem for every dense generating five-family and the hard half for one
suitable family (`GaschutzPresentationExists`). -/
theorem gaschutzCohomologicalValue_of_bound_and_presentationExists_tame
    (hK : Work.TameArithmetic.IsMaximalTamePro2 K)
    (hbound : ∀ gen : Fin 5 → (K ≃ₐ[ℚ] K), Work.RelatorRank.DenseGenerating gen →
      ProPHopfCohomologicalBound 5 gen)
    (hex : GaschutzPresentationExists (K ≃ₐ[ℚ] K)) :
    Work.RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K) :=
  gaschutzCohomologicalValue_of_bound_and_presentationExists
    (Work.TameSalle.generatorRank_eq_five_of_isMaximalTamePro2 K hK) hbound hex

end Work.AbstractDictionary
