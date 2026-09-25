import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist

/-!
# The local form of the level comparison `levelCompareOfTop`

`NK.NUV2.LC.OddTwist.levelCompareOfTop` identifies the level cohomology with coefficients in the
cyclotomic twist `μ_p(L)` with the level cohomology with the *trivial* coefficients `Z/p`, at a
level `L` at which `μ_p(L) = μ_p(K')` and for a subgroup `V` acting trivially on `μ_p(K')`.

This file proves that the same comparison, performed at the *local* level group
`(V ⊓ D_A) ⧸ ((V ⊓ D_A) ⊓ Gal(K'/L))`, intertwines the localisation maps of the two theories:

`localCmp (locLevel^tw (cmp.symm a)) = locLevel^triv a`

for every `a : H²(V ⧸ (V ⊓ Gal(K'/L)), Z/p)`.  Since `localCmp` is an equivalence (and carries `0`
to `0`), this gives the requested statement

`locLevel^tw (cmp.symm a) = 0 ↔ locLevel^triv a = 0`.

The proof follows `OddTwist.levelCompareOfTop_levelMap`, with the level group
`V ⧸ (V ⊓ Gal(K'/L))` replaced by the local level group `(V ⊓ D_A) ⧸ ((V ⊓ D_A) ⊓ Gal(K'/L))` and
the coefficient inclusion by the coefficient morphism `locCoeff`.  The only structural input is that
`V ⊓ D_A ≤ V` acts trivially on `μ_p(K')`, which is the hypothesis `hV` of the statement.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

universe u

namespace NK.NUV2.LC.RouteB

open CategoryTheory Representation
open NK.NUV2.LC.OddTwist

section Generic

variable {k k' : Type u} [CommRing k] [CommRing k'] {G : Type u} [Group G]

/-- **`H2congr` vanishes exactly on the zero class**: it is the underlying function of an
equivalence (`NK.IndecomposedDeep.H2congrEquiv`) which carries `0` to `0`
(`NK.IndecomposedDeep.H2congr_zero`). -/
lemma H2congr_eq_zero_iff {A : Rep k G} {B : Rep k' G} (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (y : A.V), e (A.ρ g y) = B.ρ g (e y))
    (x : groupCohomology.H2 A) :
    NK.IndecomposedDeep.H2congr e he x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hx : x = NK.IndecomposedDeep.H2congr e.symm
        (NK.IndecomposedDeep.equivariance_symm e he)
        (NK.IndecomposedDeep.H2congr e he x) :=
      ((NK.IndecomposedDeep.H2congrEquiv e he).symm_apply_apply x).symm
    rw [h, NK.IndecomposedDeep.H2congr_zero e.symm
      (NK.IndecomposedDeep.equivariance_symm e he)] at hx
    exact hx
  · intro h
    rw [h]
    exact NK.IndecomposedDeep.H2congr_zero e he

end Generic

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## 0. The local level representation, with universes pinned -/

/-- The local level representation of the cyclotomic twist `μ_p` — the library definition
`NK.BrauerTwist.localLevelRep`, with all universes pinned to `u` so that the coefficient
comparison `muAddEquivTop` (also living in `u`) applies without universe metavariables. -/
noncomputable abbrev localLevelRepP (p : ℕ) (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} NK.BrauerTwist.CoeffInt (NK.BrauerHasse.LocalLevelGroup V A L) :=
  NK.BrauerTwist.localLevelRep p V A L

/-- The trivial representation of the local level group on `Z/p`, universes pinned. -/
noncomputable abbrev trivLocalLevelRep (p : ℕ) (V : Subgroup Gal(K'/K))
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K') :
    Rep.{u,u,u} (NK.BrauerHasse.Coeff.{u} p) (NK.BrauerHasse.LocalLevelGroup V A L) :=
  Rep.trivial (NK.BrauerHasse.Coeff.{u} p) (NK.BrauerHasse.LocalLevelGroup V A L)
    (NK.BrauerHasse.Coeff.{u} p)

/-! ## 1. The local level group acts trivially on `μ_p(K')`

This is the local analogue of `OddTwist.levelRep_rho_eq_of_fixing_mu`: the local level group is a
quotient of `V ⊓ D_A ≤ V`, and `V` acts trivially on `μ_p(K')` by hypothesis. -/

/-- The action of the local level group on `μ_p(L)`, computed on a representative. -/
lemma localLevelRep_ρ_mk (p : ℕ) (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K')
    (u : ↥(V ⊓ NK.BrauerHasse.stabSubgroup A))
    (y : Additive ↥(NK.BrauerTwist.muLevel p L)) :
    (localLevelRepP p V A L).ρ
        (QuotientGroup.mk u : NK.BrauerHasse.LocalLevelGroup V A L) y =
      (u : Gal(K'/K)) • y := by
  simp only [localLevelRepP, NK.BrauerTwist.localLevelRep, MonoidHom.comp_apply]
  rw [NK.BrauerTwist.levelGroupHom_mk, NK.BrauerTwist.muRep_ρ_apply]

/-- **The local level group acts trivially on the cyclotomic module** `μ_p(L)`, provided `V` does. -/
theorem localLevelRep_rho_eq_of_fixing_mu (p : ℕ) (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (g : NK.BrauerHasse.LocalLevelGroup V A L)
    (y : Additive ↥(NK.BrauerTwist.muLevel p L)) :
    (localLevelRepP p V A L).ρ g y = y := by
  induction g using QuotientGroup.induction_on with
  | H u =>
    rw [localLevelRep_ρ_mk p V A L u y]
    apply Additive.toMul.injective
    rw [show Additive.toMul ((u : Gal(K'/K)) • y) =
      (u : Gal(K'/K)) • Additive.toMul y from rfl]
    apply Subtype.ext
    change (u : Gal(K'/K)) •
        (((Additive.toMul y : ↥(NK.BrauerTwist.muLevel p L)) : rootsOfUnity p K')) =
      (((Additive.toMul y : ↥(NK.BrauerTwist.muLevel p L)) : rootsOfUnity p K'))
    exact hV (u : Gal(K'/K)) u.2.1
      ((Additive.toMul y : ↥(NK.BrauerTwist.muLevel p L)) : rootsOfUnity p K')

/-! ## 2. The coefficient comparison is equivariant at the local level -/

/-- **Equivariance of the coefficient comparison at the local level**: the local analogue of
`OddTwist.muAddEquivTop_equivariance`. -/
lemma muAddEquivTop_local_equivariance (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (hL : NK.BrauerTwist.muLevel p L = ⊤) :
    ∀ (g : NK.BrauerHasse.LocalLevelGroup V A L)
      (y : Additive ↥(NK.BrauerTwist.muLevel p L)),
      muAddEquivTop p ζ hζ L hL ((localLevelRepP p V A L).ρ g y) =
        (trivLocalLevelRep p V A L).ρ g (muAddEquivTop p ζ hζ L hL y) := by
  intro g y
  show muAddEquivTop p ζ hζ L hL ((localLevelRepP p V A L).ρ g y) =
    muAddEquivTop p ζ hζ L hL y
  rw [localLevelRep_rho_eq_of_fixing_mu p V hV A L g y]

/-! ## 3. The coefficient morphism `locCoeff` is the identity -/

/-- The morphism `locCoeff` of the twisted level system acts by the (identity) coefficient
inclusion, hence is carried by `muAddEquivTop` to the identity — the trivial representation of the
local level group has, literally, identity coefficient maps. -/
lemma muAddEquivTop_locCoeff (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤)
    (x : (Rep.res (NK.BrauerHasse.localInclHom V A L) (levelRepP p V L)).V) :
    muAddEquivTop p ζ hζ L hL ((NK.BrauerTwist.locCoeff p V A L).hom x) =
      (NK.BrauerHasse.trivHom (NK.BrauerHasse.localInclHom V A L)).hom
        (muAddEquivTop p ζ hζ L hL x) := by
  change muAddEquivTop p ζ hζ L hL (NK.BrauerTwist.muInclAddHom (le_refl L) x) =
    muAddEquivTop p ζ hζ L hL x
  exact muAddEquivTop_muIncl p ζ hζ (le_refl L) hL hL x

/-! ## 4. The local level comparison and its compatibility with the localisation maps -/

/-- **The local level comparison** `H²((V ⊓ D_A)/(...), μ_p) ≃ H²((V ⊓ D_A)/(...), Z/p)`. -/
noncomputable def localLevelCompareOfTop (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (A : ValuationSubring K') :
    ∀ (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤),
      NK.BrauerTwist.LocalLevelH2 p V A L ≃ NK.BrauerHasse.LocalLevelH2 p V A L :=
  fun L hL => NK.IndecomposedDeep.H2congrEquiv
    (A := localLevelRepP p V A L) (B := trivLocalLevelRep p V A L)
    (muAddEquivTop p ζ hζ L hL) (muAddEquivTop_local_equivariance p ζ hζ V hV A L hL)

/-- **The local comparison intertwines the two localisation maps.** -/
lemma localLevelCompareOfTop_locLevel (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤)
    (A : ValuationSubring K') (a : NK.BrauerHasse.LevelH2 p V L) :
    localLevelCompareOfTop p ζ hζ V hV A L hL
        (NK.BrauerTwist.locLevel p V A L ((levelCompareOfTop p ζ hζ V hV L hL).symm a)) =
      NK.BrauerHasse.locLevel p V A L a := by
  have h := NK.IndecomposedDeep.H2congr_map
    (f := NK.BrauerHasse.localInclHom V A L)
    (NK.BrauerTwist.locCoeff p V A L)
    (NK.BrauerHasse.trivHom (NK.BrauerHasse.localInclHom V A L))
    (muAddEquivTop p ζ hζ L hL) (muAddEquivTop p ζ hζ L hL)
    (muAddEquivTop_equivariance p ζ hζ V hV L hL)
    (muAddEquivTop_local_equivariance p ζ hζ V hV A L hL)
    (fun x => muAddEquivTop_locCoeff p ζ hζ V A L hL x)
    ((levelCompareOfTop p ζ hζ V hV L hL).symm a)
  have h' : NK.IndecomposedDeep.H2congr (muAddEquivTop p ζ hζ L hL)
      (muAddEquivTop_equivariance p ζ hζ V hV L hL)
      ((levelCompareOfTop p ζ hζ V hV L hL).symm a) = a :=
    Equiv.apply_symm_apply (levelCompareOfTop p ζ hζ V hV L hL) a
  rw [h'] at h
  exact h

/-- The local comparison carries `0` to `0` and reflects it (it is an equivalence). -/
lemma localLevelCompareOfTop_eq_zero_iff (p : ℕ) [NeZero p] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (A : ValuationSubring K') (L : FiniteGaloisIntermediateField K K')
    (hL : NK.BrauerTwist.muLevel p L = ⊤) (z : NK.BrauerTwist.LocalLevelH2 p V A L) :
    localLevelCompareOfTop p ζ hζ V hV A L hL z = 0 ↔ z = 0 := by
  have hz := H2congr_eq_zero_iff (A := localLevelRepP p V A L) (B := trivLocalLevelRep p V A L)
    (muAddEquivTop p ζ hζ L hL) (muAddEquivTop_local_equivariance p ζ hζ V hV A L hL) z
  exact hz

/-! ## 5. The requested statement -/

theorem locLevel_levelCompareOfTop (p : ℕ) [NeZero p]
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K))
    (hV : ∀ σ : Gal(K'/K), σ ∈ V → ∀ x : rootsOfUnity p K', σ • x = x)
    (L : FiniteGaloisIntermediateField K K') (hL : NK.BrauerTwist.muLevel p L = ⊤)
    (A : ValuationSubring K') (a : NK.BrauerHasse.LevelH2 p V L) :
    (NK.BrauerTwist.locLevel p V A L)
        ((NK.NUV2.LC.OddTwist.levelCompareOfTop p ζ hζ V hV L hL).symm a) = 0 ↔
      (NK.BrauerHasse.locLevel p V A L) a = 0 := by
  have h := localLevelCompareOfTop_locLevel p ζ hζ V hV L hL A a
  have hz := localLevelCompareOfTop_eq_zero_iff p ζ hζ V hV A L hL
    (NK.BrauerTwist.locLevel p V A L ((levelCompareOfTop p ζ hζ V hV L hL).symm a))
  rw [← h]
  exact hz.symm

end NK.NUV2.LC.RouteB
