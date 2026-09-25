import Mathlib
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le
import Submission.Work.ShafarevichKoch.isGalois_of_finrank_eq_two
import Submission.Work.ShafarevichKoch.card_vTwo_mod_squares

/-!
# `Work.ShafarevichKoch.finite_quadraticLevel`

**The unramified quadratic levels of `F_∅/F` are finite in number.**

`QuadraticLevel F M` is the type of intermediate fields `F ⊆ L ⊆ M.K` of `F`-dimension `2`,
where `M.K = F_∅` is the maximal unramified pro-`2` extension of a number field `F`.  The goal
of this file is

`Work.ShafarevichKoch.finite_quadraticLevel : Finite (QuadraticLevel F M)`,

which is what makes `#ProTwoChar F M = #(QuadraticLevel F M) + 1` a statement about `ℕ` rather
than about cardinals, and hence makes the generator rank `d(G_∅) = log₂ #ProTwoChar F M`
computable.

Mathematically the finiteness is the classical classification of the exponent-`2` unramified
extensions of `F` by the Kummer two-descent

`1 → 𝓞_Fˣ/(𝓞_Fˣ)² → V_∅/Fˣ² → Cl(F)[2] → 1`,

which shows that there are at most `2 ^ (d₂(𝓞_Fˣ) + rank₂ Cl(F))` of them; the corresponding
*counter* is already available as
`Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le`.

## The formalisation

The counting lemma `card_unramifiedQuadraticLevels_le` bounds the cardinality of a *finite*
injective family of quadratic levels, so it is applied here contrapositively: were
`QuadraticLevel F M` infinite, it would contain finite subsets of every cardinality, and each
such subset would inject into `IntermediateField F M.K` while satisfying all the hypotheses of
the counting lemma — contradicting the bound.  Concretely, the bound on all finite subsets is
turned into a `Fintype` instance by `fintypeOfFinsetCardLe`, whence `Finite`.

The three instance hypotheses of the counting lemma are supplied by the elementary facts:

* `quadraticLevel_finiteDimensional` — `L` has `F`-dimension `2`, hence is finite dimensional;
* `quadraticLevel_numberField` — an intermediate field of a number field of finite degree is a
  number field;
* `quadraticLevel_isGalois` — in characteristic zero an intermediate field of degree `2` is
  Galois over the base (`isGalois_of_finrank_eq_two`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **A quadratic level is finite dimensional over `F`** (it has `F`-dimension `2`). -/
theorem quadraticLevel_finiteDimensional (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) (L : QuadraticLevel F M) :
    FiniteDimensional F (L : IntermediateField F M.K) :=
  Module.finite_of_finrank_pos (R := F) (M := ↥(L : IntermediateField F M.K))
    (by rw [L.2]; norm_num)

/-- **A quadratic level is a number field**: it is finite dimensional over the number field
`F`, hence finite dimensional over `ℚ` (and it is a field). -/
theorem quadraticLevel_numberField (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) (L : QuadraticLevel F M) :
    NumberField ↥(L : IntermediateField F M.K) := by
  haveI := quadraticLevel_finiteDimensional F M L
  exact NumberField.of_module_finite F ↥(L : IntermediateField F M.K)

/-- **A quadratic level is Galois over `F`**: in characteristic zero every intermediate field of
degree `2` is Galois over its base. -/
theorem quadraticLevel_isGalois (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) (L : QuadraticLevel F M) :
    IsGalois F (L : IntermediateField F M.K) :=
  isGalois_of_finrank_eq_two F M.K (L : IntermediateField F M.K) L.2

/-- **The number of unramified quadratic levels of `F_∅/F` is finite.**

Every finite family of levels is a family of degree-`2` unramified Galois extensions of `F`
inside `F_∅`, so it obeys the Kummer two-descent bound
`#QuadraticLevel ≤ 2 ^ (d₂(𝓞_Fˣ) + rank₂ Cl(F))` of
`card_unramifiedQuadraticLevels_le`; bounding all finite subsets yields the `Fintype` instance,
hence finiteness. -/
theorem finite_quadraticLevel (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) :
    Finite (Work.ShafarevichKoch.QuadraticLevel F M) := by
  classical
  haveI : Fintype (QuadraticLevel F M) :=
    fintypeOfFinsetCardLe
      (2 ^ (Work.ClassFieldTower.unitTwoRank F + Work.ClassFieldTower.classGroupTwoRank F))
      (fun s => by
        -- the counting lemma applied to the finite set `s` of levels
        have h := card_unramifiedQuadraticLevels_le F M
          (fun i : ↥s => ((i : QuadraticLevel F M) : IntermediateField F M.K))
          (fun i => quadraticLevel_numberField F M _)
          (fun i => quadraticLevel_finiteDimensional F M _)
          (fun i => quadraticLevel_isGalois F M _)
          (fun i => (i : QuadraticLevel F M).2)
          (fun i j hij => Subtype.ext (Subtype.ext hij))
        rwa [Fintype.card_coe s] at h)
  exact Finite.of_fintype _

end Work.ShafarevichKoch
