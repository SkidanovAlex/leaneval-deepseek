import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.HassePrinciple.UnitsLevel
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.HassePrinciple.LevelDictionary
import Submission.NK.NUV2.ABHN.h2Twist_muColim_equiv
import Submission.NK.NUV2.LC.units_finite_support

/-!
# Auxiliaries for `level_kills_of_loc_eq_zero`: the level-group / number-field dictionary

This file collects the *definite* transports comparing the `LevelGroup`-based level cohomology
(`NK.HassePrinciple.UnitsLevelH2 V L = H²(LevelGroup V L, Lˣ)`) with the *number-field* cohomology
`H²(Gal(L/(L ⊓ K'^V)), Lˣ)` in which the relative Hasse–Brauer–Noether theorem
`NK.HassePrinciple.HBNUnits` (Milne CFT VII.7.1, unconditional) and the localisation
`NK.HassePrinciple.locUnits` are stated.

The transports are built with `groupCohomology.mapIso` along the level-group dictionary
`NK.HassePrinciple.levelGroupMulEquivLevelGalois`, exactly as the transports
`NK.NUV2.LC.unitsEquiv` (for `V = ⊤`) are built in `Submission/Work/NUV2/LC/crux_loc_twist.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

universe u

namespace NK.NUV2.LC.RouteB

open CategoryTheory

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The base field of a level**: `L ⊓ K'^V`, realised as the fixed field of the image of `V` in
`Gal(L/K)`.  The dictionary `NK.HassePrinciple.levelGroupMulEquivLevelGalois` identifies
`LevelGroup V L` with the Galois group of `L` over this field. -/
noncomputable abbrev levelBase (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    IntermediateField K (↥L) :=
  IntermediateField.fixedField (V.map (NK.HassePrinciple.levelRestrict L))

/-- The level-group dictionary: `LevelGroup V L` is the Galois group of `L` over the base field
`levelBase V L`.  This is `NK.HassePrinciple.levelGroupMulEquivLevelGalois`, restated with the
base field named. -/
noncomputable def levelGroupEquiv (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.LevelGroup V L ≃* Gal(↥L/↥(levelBase V L)) :=
  NK.HassePrinciple.levelGroupMulEquivLevelGalois V L


/-- **The definite transport between the `LevelGroup`-based units level cohomology and the
number-field units cohomology.**  For a level `L` of `K'/K`, the level group
`LevelGroup V L` is the Galois group of `L` over the base field `levelBase V L = L ⊓ K'^V`
(`levelGroupEquiv`), and both sides carry the same coefficient module `Lˣ` (with the natural Galois
action).  The transport is built from `groupCohomology.mapIso`, hence definite: it is the map on
`H²` induced by the group isomorphism and by the identity on the coefficients. -/
noncomputable def unitsLift (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L ≃+
      (groupCohomology (NK.HassePrinciple.unitsRep (↥(levelBase V L)) (↥L)) 2) := by
  refine ((groupCohomology.mapIso (A := NK.HassePrinciple.unitsRep (↥(levelBase V L)) (↥L))
    (B := NK.HassePrinciple.unitsLevelRep V L)
    (levelGroupEquiv (K := K) (K' := K') V L)
    (LinearEquiv.refl NK.HassePrinciple.CoeffInt (Additive (↥L)ˣ)) ?_ 2).toLinearEquiv).toAddEquiv
  intro g
  induction g using QuotientGroup.induction_on with
  | H v => simp only [NK.HassePrinciple.levelGroupRestrictHom_mk]; rfl

section Base

variable (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')

/-- The level group is the Galois group of the level over its base field, with the computation
rule: on the class of `v` it is the restriction of `v`. -/
lemma levelGroupEquiv_apply (g : NK.BrauerHasse.LevelGroup V L) (x : ↥L) :
    (((levelGroupEquiv (K := K) (K' := K') V L) g :
        ↥L ≃ₐ[↥(levelBase (K := K) V L)] ↥L) x) =
      (((NK.HassePrinciple.levelGroupRestrictHom V L g) : ↥L ≃ₐ[K] ↥L) x) := by
  induction g using QuotientGroup.induction_on with
  | H v => simp only [levelGroupEquiv, NK.HassePrinciple.levelGroupRestrictHom_mk]; rfl
end Base

/-- **Monotonicity of the level-wise localisation in the level**: once a level kills the
localisation of a class, every larger level does too. -/
theorem locLevel_eq_zero_of_le (p : ℕ) (V : Subgroup Gal(K'/K))
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (L : FiniteGaloisIntermediateField K K') (c : NK.BrauerTwist.LevelH2 p V L)
    {M₀ M : FiniteGaloisIntermediateField K K'} (h₀ : L ≤ M₀) (h : L ≤ M) (hM : M₀ ≤ M)
    (h0 : NK.BrauerTwist.locLevel p V A.1 M₀
      (NK.BrauerTwist.levelMap p V h₀ c) = 0) :
    NK.BrauerTwist.locLevel p V A.1 M (NK.BrauerTwist.levelMap p V h c) = 0 := by
  have hcomp : (NK.BrauerTwist.levelMap p V h₀) ≫ (NK.BrauerTwist.levelMap p V hM) =
      NK.BrauerTwist.levelMap p V (h₀.trans hM) :=
    NK.BrauerTwist.levelMap_comp (p := p) (U := V) h₀ hM
  have h1 : (NK.BrauerTwist.levelMap p V h) c =
      (NK.BrauerTwist.levelMap p V hM) ((NK.BrauerTwist.levelMap p V h₀) c) := by
    rw [Subsingleton.elim h (h₀.trans hM)]
    have := congrArg (fun (k : NK.BrauerTwist.LevelH2 p V L ⟶
      NK.BrauerTwist.LevelH2 p V M) => k.hom c) hcomp
    simpa [ModuleCat.comp_apply] using this.symm
  rw [h1, NK.BrauerTwist.levelMap_locLevel_apply p V A.1 hM, h0, map_zero]

/-- The zero of `MuLevelH2` is mapped to zero by the level comparison. -/
lemma levelCompare_zero (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    (NK.NUV2.ABHN.levelCompare p V L) (0 : NK.HassePrinciple.MuLevelH2 p V L) = 0 := by
  show NK.NUV2.ABHN.H2congr _ _ 0 = 0
  exact NK.NUV2.ABHN.H2congr_zero _ _

/-- **The leaf `level_kills_of_loc_eq_zero` from its `μ_p` (`MuLevelH2`) form.**  The two statements
are equivalent through the level comparison `NK.NUV2.ABHN.levelCompare` and its naturality
`levelCompare_nat`. -/
theorem level_kills_of_muLevel (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (hV : NK.NUV2.LC.RouteB.IsMuOpen (K := K) (K' := K') ζ V)
    (hmain : ∀ (L : FiniteGaloisIntermediateField K K')
      (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L),
      (∀ A : NK.BrauerTwist.OverFinitePrime K K',
        NK.BrauerTwist.H2Twist.loc p V
          (NK.BrauerTwist.H2Twist.ofLevel p V L
            (NK.NUV2.ABHN.levelCompare p V L c)) A = 0) →
      ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
        NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V
          ((FiniteGaloisIntermediateField.le_iff L M).mp hLM) c = 0)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.BrauerTwist.LevelH2 p V L)
    (h : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc p V
        (NK.BrauerTwist.H2Twist.ofLevel p V L a) A = 0) :
    ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
      NK.BrauerTwist.levelMap p V hLM a = 0 := by
  set c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L :=
    (NK.NUV2.ABHN.levelCompare p V L).symm a with hc
  have hca : (NK.NUV2.ABHN.levelCompare p V L) c = a := Equiv.apply_symm_apply _ a
  have h' : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc p V
        (NK.BrauerTwist.H2Twist.ofLevel p V L
          (NK.NUV2.ABHN.levelCompare p V L c)) A = 0 := by
    intro A
    rw [hca]
    exact h A
  obtain ⟨M, hLM, hM⟩ := hmain L c h'
  have hnat := NK.NUV2.ABHN.levelCompare_nat p V hLM c
  rw [hM, hca] at hnat
  refine ⟨M, hLM, ?_⟩
  rw [← hnat]
  exact levelCompare_zero (K := K) (K' := K') p V M

/-- **The `LevelGroup`-based units localisation**: the localisation `locUnits` of the level class,
transported through `unitsLift`.  By construction, `locL` is the conjugate of `locUnits` under the
transport, so all the structural facts about `locUnits` (in particular the Hasse principle
`HBNUnits`) transfer verbatim. -/
noncomputable abbrev locL (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (w : NK.GlobalCFT.Place ↥L)
    (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L) :=
  (NK.HassePrinciple.locUnits (↥(levelBase V L)) (↥L) w).hom ((unitsLift V L) b)

/-- **The relative Hasse–Brauer–Noether theorem in the `LevelGroup` vocabulary**: a units level
class whose `locL` localisations vanish at every place is zero.  This is the transport of
`NK.GlobalCFTdeep.hbnUnits` (Milne CFT VII.7.1) along the definite equivalence `unitsLift`. -/
theorem unitsLevelH2_eq_zero_of_locL_eq_zero (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K')
    (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L)
    (h : ∀ w : NK.GlobalCFT.Place ↥L, locL (K := K) (K' := K') V L w b = 0) : b = 0 := by
  have hb := (NK.GlobalCFTdeep.hbnUnits (F := ↥(levelBase V L)) (E := ↥L)) ((unitsLift V L) b)
    (by intro w; exact h w)
  refine (unitsLift V L).injective ?_
  rw [hb, map_zero]

/-- **Finite support of the `LevelGroup`-based units localisation** (the transport of
`NK.NUV2.LC.units_finite_support` along `unitsLift`): for a units level class, the set of places
whose `locL` localisation does not vanish is finite. -/
theorem finite_support_locL (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (b : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L) :
    {w : NK.GlobalCFT.Place ↥L | locL (K := K) (K' := K') V L w b ≠ 0}.Finite := by
  have h := NK.NUV2.LC.units_finite_support (K := ↥(levelBase V L)) (L := ↥L)
    ((unitsLift (K := K) (K' := K') V L) b)
  simpa [locL] using h

end NK.NUV2.LC.RouteB
