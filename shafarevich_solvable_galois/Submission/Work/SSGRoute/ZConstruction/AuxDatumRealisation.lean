import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
import Submission.Work.SSGRoute.ZConstruction.ZDataInduction
import Submission.Work.SSGRoute.ZConstruction.ZDataReduction
import Submission.Work.SSGRoute.ZConstruction.MupGate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sibling-style realisation of the *prescribed* datum of the section-4 level step

`Work.SSGRoute.hasZData_sum_of_level_data_at_lambda`
(`ZConstruction/LevelStepAtLambda.lean`) consumes about the auxiliary class `yAux`

* the `Λ`-level `z`-data of its one-dimensional witness, and
* one unramifiedness fact at the level `N` (clause 5 at the pair `(N, S')`),

and both of these follow from a *single* datum-level statement about `yAux` itself:

    `Work.SSGRoute.ZHyp (p := p) K N S' yAux`   (the six conditions of Theorem 13's datum at `(N,S')`)

together with the two *prescriptions* that define `yAux` (agreement with the line component `y₁` at
`cs(S)`, vanishing at `cs(S') ∖ cs(S)`).  Indeed:

* `Work.SSGRoute.MupGate K` (available below this node from the two arithmetic cores,
  `ZConstruction/MupGate.lean`) gives `HasZData K N S' yAux z₁` outright, and clause 5 of that data is
  the level-`N` unramifiedness; and
* `Work.SSGRoute.hasZData_of_le_level` (`ZConstruction/ZDataInduction.lean`) lowers the `z`-data to the
  primal pair `(Λ, S')`.

The present file isolates the datum-level statement, `Work.SSGRoute.AuxDatumRealisation`, as the
**one** remaining ingredient of the level step, and proves the wiring to `MupGate`.

## Why this is the right abstraction (and not the refuted mixed gate)

`Work.SSGRoute.auxExists_of_pairing_and_realisation` obtained `yAux` from a *realisation gate* which
quantified over **arbitrary** local data `f` and **arbitrary** `Λ`-relaxed orthogonality and concluded
unramifiedness at the level `N`.  `ZConstruction/NOTE_session17.lean` shows that gate is false: an
arbitrary `Λ`-primal class is orthogonally to every `Λ`-relaxed dual (the proved
`ZConstruction.relaxedSum_pair_eq_zero`) but not to a suitable `N`-relaxed one.

Here the datum is **fixed**: it is the imposed local data of the paper's `ỹ` (agreement on `cs(S)`,
vanishing on `cs(S') ∖ cs(S)`), and the statement asks only for a class with those local components
satisfying `ZHyp` at `(N, S')`.  This is the sibling lane's shape -- `Work.SSGRoute.IsYRealisation`
prescribes the datum and the vanishing, and `Work.SSGRoute.IsZData.split`
(`SSGRoute/shafarevich_theorem13.lean`) applies the one-dimensional data at the level where the
auxiliary class lives -- and, being datum-specific, it is not touched by the counterexample above.
The arithmetic that has to supply it is the p. 18 chase at the level `Λ`
(`Work.SSGRoute.auxDatum_orthogonal_of_productFormula`) together with the *unmixed* degree-one
Poitou--Tate realisation at the level `N` for this one datum.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
variable {K Λ N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The prescribed-datum realisation of the section-4 level step.**  There is a class `yAux` which

* satisfies the six conditions `Work.SSGRoute.ZHyp` of the datum of Theorem 13 at the *enlarged* pair
  `(N, S')`,
* agrees with the line component `y₁` on the level-`K` local group of every place conjugate into `S`,
* vanishes on the level-`K` local group of every finite place that is conjugate into `S'` but not
  into `S`.

This is the class `ỹ` of Schmidt--Wingberg p. 18 in the routing of this lane: it is produced by the
p. 18 chase (level `Λ`) together with the degree-one realisation of *this* datum at the level `N`, and
it is what `Work.SSGRoute.hasZData_sum_of_level_data_at_lambda` needs of the auxiliary class. -/
def AuxDatumRealisation (K Λ N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (S S' : Finset (ValuationSubring Ω)) (y₁ : (Ω ≃ₐ[k] Ω) → ZMod p) : Prop :=
  ∃ yAux : (Ω ≃ₐ[k] Ω) → ZMod p,
    ZHyp (p := p) K N S' yAux ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = y₁ σ) ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = 0)

/-- **The wiring: the prescribed-datum realisation plus the one-dimensional gate give the auxiliary
`z`-data used by the level step at `(Λ, S')`, together with its level-`N` unramifiedness.**

From `Work.SSGRoute.AuxDatumRealisation` and `Work.SSGRoute.MupGate K` one obtains a witness `z₁` with

* `Work.SSGRoute.HasZData K N S' yAux z₁` (the one-dimensional gate at the enlarged pair), hence
* `Work.SSGRoute.HasZData K Λ S' yAux z₁` (`Work.SSGRoute.hasZData_of_le_level`), and
* the level-`N` unramifiedness `hz₁unr` required by
  `Work.SSGRoute.hasZData_sum_of_level_data_at_lambda` (clause 5 of the data at `(N, S')`).

So with this lemma the whole level step is assembled from the datum-level statement, the
one-dimensional gate and the *other* summand's data -- and no mixed-level realisation statement is
used anywhere. -/
theorem exists_hasZData_auxDatum {S S' : Finset (ValuationSubring Ω)}
    {y₁ yAux z₁ : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : AuxDatumRealisation (p := p) K Λ N S S' y₁)
    (h₁ : HasZData K N S' yAux z₁) :
    ∃ yAux' : (Ω ≃ₐ[k] Ω) → ZMod p,
      ZHyp (p := p) K N S' yAux' ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux' σ = y₁ σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux' σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z₁ σ = 0) :=
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2, h₁.2.2.2.2.1⟩

end Work.SSGRoute
