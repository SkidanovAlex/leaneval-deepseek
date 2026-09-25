import Mathlib
import Submission.NumberField.ProThreeTowerAssembly
import Submission.NumberField.MaximalProPOutsideS
import Submission.Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces

open scoped NumberField
open NumberField
open IntermediateField

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

/-!
# The last mile of the Golod--Shafarevich route for `p = 2`: an infinite unramified pro-2
# extension of a totally real number field yields Martinet's tower

**STATUS: sorry-free.**  CHAIN C (the Golod--Shafarevich route), pro-`2` branch.  Off the
`Submission.lean` proof path.

`Submission/NumberField/ProThreeTowerAssembly.lean` extracted an infinite tower of
unramified steps from an infinite unramified pro-`3` extension of a totally real base
field.  This module does the same for `p = 2`; the ONLY difference is the source of total
reality of the levels:

* for odd `p`, total reality of a finite pro-`p` unramified extension of a totally real
  field is forced by the arithmetic of the local degree (`2` versus `p ^ k`);
* for `p = 2` one must impose unramifiedness at the INFINITE places, which is exactly the
  extra condition built into the commons construction
  `Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf`.

The content is therefore

* `proTowerFam_totallyReal_two` -- the levels of the pro-`2` tower are totally real (from
  `IsUnramifiedAtInfinitePlaces` and the totally real base, via the commons lemma
  `isTotallyReal_of_isUnramifiedAtInfinitePlaces`);
* `exists_unramifiedTowerData_of_infinite_unramified_protwo` -- an infinite Galois
  extension `K / F` of a totally real number field `F` whose finite dimensional Galois
  subextensions are unramified at every finite prime, unramified at the infinite places,
  and pro-`2` produces `Submission.Towers.UnramifiedTowerData`, hence Martinet's theorem;
* `HilbertTowerWall` -- the resulting arithmetic wall in named form: the maximal
  unramified pro-`2` extension of a totally real number field is infinite.  This route
  needs NO class field theory beyond the (CFT-free, already formalized) sup-construction of
  the maximal extension: the whole analytic input is the Golod--Shafarevich argument
  (`Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich`), and the
  arithmetic input is the relation rank of the unramified pro-`2` group.
-/

namespace Submission.NumberField

noncomputable section

variable {F K : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F] [Field K]
  [Algebra F K] [IsGalois F K]

/-- **The levels of the pro-`2` tower are totally real.**  Total reality is inherited from
the totally real base through unramifiedness at the infinite places. -/
theorem proTowerFam_totallyReal_two (hinf : Infinite (K ≃ₐ[F] K))
    (hunrInf : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsUnramifiedAtInfinitePlaces F ↥L) (n : ℕ) :
    NumberField.IsTotallyReal ((proTowerFam hinf) n) := by
  haveI hfd : FiniteDimensional F ((proTowerFam hinf) n) := proTowerFam_finite hinf n
  haveI hgal : IsGalois F ((proTowerFam hinf) n) := proTowerFam_galois hinf n
  haveI hnum : NumberField ((proTowerFam hinf) n) := proTowerFam_numberField hinf n
  haveI : IsUnramifiedAtInfinitePlaces F ((proTowerFam hinf) n) := hunrInf _ hfd hgal
  exact Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces F _

/-- **The Golod--Shafarevich assembly, `p = 2`.**  An infinite unramified pro-`2` Galois
extension of a totally real number field yields an infinite everywhere-unramified tower of
totally real number fields with steps of degree at least two -- exactly the
`UnramifiedTowerData` interface consumed by `Submission.Towers.milestone_unramified_tower`. -/
theorem exists_unramifiedTowerData_of_infinite_unramified_protwo (hinf : Infinite (K ≃ₐ[F] K))
    (hunr : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤)
    (hunrInf : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsUnramifiedAtInfinitePlaces F ↥L)
    (hpro : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsPGroup 2 (L ≃ₐ[F] L)) :
    ∃ Fam : ℕ → Type, Nonempty (Submission.Towers.UnramifiedTowerData Fam) := by
  haveI hfd : ∀ n : ℕ, FiniteDimensional F ((proTowerFam hinf) n) := proTowerFam_finite hinf
  haveI hnf : ∀ n : ℕ, NumberField ((proTowerFam hinf) n) := proTowerFam_numberField hinf
  haveI htr : ∀ n : ℕ, NumberField.IsTotallyReal ((proTowerFam hinf) n) :=
    proTowerFam_totallyReal_two hinf hunrInf
  letI halg : ∀ n : ℕ, Algebra ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) :=
    proTowerAlg hinf
  letI hmod : ∀ n : ℕ, Module ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) := fun n => by
    letI := proTowerAlg hinf n
    infer_instance
  refine ⟨fun n => proTowerFam hinf n,
    ⟨{ alg := halg, unram_step := ?_, deg := ?_ }⟩⟩
  · intro n
    haveI hNFn : NumberField ((proTowerFam hinf) n) := proTowerFam_numberField hinf n
    haveI hNF1 : NumberField ((proTowerFam hinf) (n+1)) := proTowerFam_numberField hinf (n+1)
    have hmid : rootDiscr ((proTowerFam hinf) n) = rootDiscr F :=
      proTowerFam_rootDiscr_base hinf hunr n
    have htop : rootDiscr ((proTowerFam hinf) (n+1)) = rootDiscr F :=
      proTowerFam_rootDiscr_base hinf hunr (n+1)
    exact Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_rootDiscr_eq
      (htop.trans hmid.symm)
  · intro n
    haveI hst : IsScalarTower F ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) :=
      proTowerFam_scalarTower hinf n
    exact step_deg (galoisChain_le_succ hinf n) (galoisChain_deg hinf n)

/-- **Martinet's theorem from an infinite unramified pro-`2` extension of a totally real
field.** -/
theorem exists_totallyReal_discr_le_of_infinite_unramified_protwo (hinf : Infinite (K ≃ₐ[F] K))
    (hunr : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤)
    (hunrInf : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsUnramifiedAtInfinitePlaces F ↥L)
    (hpro : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsPGroup 2 (L ≃ₐ[F] L)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : NumberField.IsTotallyReal K'),
        Module.finrank ℚ K' = d ∧ |(NumberField.discr K' : ℝ)| ≤ C ^ d := by
  obtain ⟨Fam, hT⟩ :=
    exists_unramifiedTowerData_of_infinite_unramified_protwo hinf hunr hunrInf hpro
  exact Submission.Towers.exists_totallyReal_discr_le_of_unramified_tower hT.some

/-- **An infinite Galois group from unbounded finite Galois subextensions.**  If the finite
dimensional Galois subextensions of `K / F` have unbounded `F`-degree, then `Gal(K/F)` is
infinite: a finite Galois group `Gal(K/F)` restricts surjectively onto `Gal(L/F)` for every
finite Galois intermediate field `L`, and `Nat.card (L ≃ₐ[F] L) = [L : F]`. -/
theorem infinite_algEquiv_of_forall_finrank_ge
    (h : ∀ N : ℕ, ∃ L : IntermediateField F K,
      FiniteDimensional F L ∧ IsGalois F L ∧ N ≤ Module.finrank F L) :
    Infinite (K ≃ₐ[F] K) := by
  rw [← not_finite_iff_infinite]
  intro hfin
  haveI : Finite (K ≃ₐ[F] K) := hfin
  obtain ⟨L, hfd, hgal, hdeg⟩ := h (Nat.card (K ≃ₐ[F] K) + 1)
  haveI : FiniteDimensional F L := hfd
  haveI : IsGalois F L := hgal
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (E := ↥L) (K₁ := K) :
        (K ≃ₐ[F] K) → (↥L ≃ₐ[F] ↥L)) :=
    AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) (E := K)
  have hle : Nat.card (↥L ≃ₐ[F] ↥L) ≤ Nat.card (K ≃ₐ[F] K) :=
    Nat.card_le_card_of_surjective _ hsurj
  rw [IsGalois.card_aut_eq_finrank F ↥L] at hle
  omega

/-- **THE HILBERT-TOWER WALL** (Route 1, in E-seam-free form).  There are a totally real
number field `F` and an infinite Galois extension `K / F` all of whose finite dimensional
Galois subextensions are pro-`2`, unramified at every finite prime and unramified at the
infinite places.  Equivalently: the maximal unramified pro-`2` extension of `F` -- which
exists unconditionally, with no class field theory
(`Submission.NumberField.exists_maximal_proP_field_unramifiedOutside_inf`) -- is infinite.

This is the arithmetic wall of the Golod--Shafarevich route; by the corrected criterion
`Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich` it is enough to
produce a presentation of `Gal(K/F)` with `d` generators and `r` relators with
`4 * r ≤ d ^ 2` and the finite `p`-group Golod--Shafarevich inequality. -/
def HilbertTowerWall : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyReal F)
    (K : Type) (_ : Field K) (_ : Algebra F K) (_ : IsGalois F K),
    Infinite (K ≃ₐ[F] K) ∧
    (∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L → IsGalois F L →
      IsPGroup 2 (L ≃ₐ[F] L) ∧ differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤ ∧
        IsUnramifiedAtInfinitePlaces F ↥L)

/-- **The benchmark statement follows from the Hilbert-tower wall.** -/
theorem exists_totallyReal_discr_le_of_hilbertTowerWall (h : HilbertTowerWall) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : NumberField.IsTotallyReal K'),
        Module.finrank ℚ K' = d ∧ |(NumberField.discr K' : ℝ)| ≤ C ^ d := by
  classical
  obtain ⟨F, iF, iNF, hTR, K, iK, iA, iG, hinf, hlev⟩ := h
  letI : Field F := iF
  letI : NumberField F := iNF
  letI : NumberField.IsTotallyReal F := hTR
  letI : Field K := iK
  letI : Algebra F K := iA
  letI : IsGalois F K := iG
  exact exists_totallyReal_discr_le_of_infinite_unramified_protwo hinf
    (fun L _ hfd hgal => (hlev L hfd hgal).2.1)
    (fun L _ hfd hgal => (hlev L hfd hgal).2.2)
    (fun L _ hfd hgal => (hlev L hfd hgal).1)

end

end Submission.NumberField
