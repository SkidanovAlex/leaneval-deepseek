import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupH1locLcHoms
import Submission.Work.SSGRoute.ZDataMup.mupLocalVocab
import Submission.Work.SSGRoute.ZDataMup.LT_localGaloisTransport
import Submission.Work.SSGRoute.LT_lcHoms_factor_through_abGal_lc
import Submission.Work.SSGRoute.ZConstruction.levelK_modelIsoCanonical
import Submission.Work.SSGRoute.ZConstruction.levelK_localGalTransportCanonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical (`μ_p` local Tate) pairing at the level-`K` local groups

This module *defines* the canonical family of local pairings that the gate
`Work.SSGRoute.ZConstruction.levelK_pairing_productFormula` asks for, in the vocabulary in which
its three properties can be stated and (separately) proved:

`levelKCanonPairing A hA hAK x y  =  (χ_x ∘ rec_A)(β_y)   ∈ ZMod p`

where, for a finite place `A` of `Ω` over `k` and the level-`K` local group
`H_A = decomp k A ⊓ K.fixingSubgroup`,

* `x ∈ V_A = H1loc p k Ω K (ZMod p) H_A` is a level-`K` local `H¹`-class;
* `χ_x` is the locally constant character of `G_{κ_A} = Gal(κ̄_A/κ_A)` attached to `x`
  (`mupH1locLcHoms` gives the character of the level-`K` local group, `LT_lcHoms_levelK_localGalois`
  transports it to the completion along the canonical homeomorphism `mupLocalGalEquiv`, and
  `LT_lcHoms_factor_through_abGal_lc` factors it through the abelianisation `AbGal κ̄_A κ_A`);
* `rec_A = mupRec` is the *honest* local Artin map of the completion `κ_A = 𝔭_A.adicCompletion ↥K`,
  the canonical local reciprocity datum of local class field theory
  (`NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`);
* `β_y` is the local Kummer class of `y`, read off through the level-`K` local Kummer dictionary
  `mupKummerEquiv`.

Equivalently, on global classes this is the (transposed) `p`-th power **Hilbert symbol**
`⟨β_y, α_x⟩_A`, which is the canonical local Tate pairing; the transposition is harmless because
Hilbert reciprocity is symmetric.

## The three properties, and where they are proved

The gate needs the family to have

* **(1) first-variable non-degeneracy** at every level-`K` local group,
* **(2) the reciprocity sum** `∑_{A ∈ T'} F_{H_A}[a][b] = 0` for global cocycles unramified outside
  `T'`, and
* **(3) the unramified orthogonality** `F_{H_A}` vanishing on `U_A × U_A` (`U_A` =
  `ZSplit.unramifiedSubgroup`).

They are stated below as `levelKCanonPairing_nondegenerate` (1),
`levelKCanon_rec (2)` and `levelKCanon_unramifiedOrthogonal` (3), and they are *not* proved in this
module: (1) is the density of the local Artin image (`LT_abGal_kills_of_artin`), (3) is the local
statement `Br(κ_A^{un}/κ_A) = 0` (equivalently: the unramified local Kummer classes are the classes
of units, and the local Artin map sends units to the inertia), and (2) is Hilbert reciprocity in
the `μ_p` form, i.e. the statement that the glued local-global Artin map kills `Kˣ`
(`Work.SSGRoute.ZDataMup.gluedMap_kills_principalIdele`), together with the local-global
compatibility of the Artin map at the ramified places.  Splitting the gate this way is what makes
the three pieces independently attackable; the assembly is in the target file.

## The hypothesis `A.comap (algebraMap ↥K Ω) ≠ ⊤`

The dictionary `mupKummerEquiv` and the local Artin map `mupRec` are attached to the prime
`𝔭 = NeukirchUchida.primeOf A hAK` of `↥K` below `A`, which requires the valuation to be non-trivial
on `↥K`.  We carry this as the explicit hypothesis `hAK`; it follows from `IsFinPlace k A`
(`isFinPlace_of_isFinPlace_below` below), since `k ≤ K` and the valuation is already non-trivial
on `k`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p}
  {A : ValuationSubring Ω}

/-- **The level-`K` local group at the place `A`**: `H_A = decomp k A ⊓ K.fixingSubgroup`, the
stabiliser of `A` inside `G_K = K.fixingSubgroup`. -/
abbrev levelKLocalGroup (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup

/-- **A finite place of `k` is a finite place of any intermediate field.**  `IsFinPlace` is
`A.comap (algebraMap · Ω) ≠ ⊤`, and the valuation is already non-trivial on `k ≤ K`. -/
theorem isFinPlace_of_isFinPlace_below (hA : _root_.SSGRoute.IsFinPlace k A) :
    A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
  intro h
  apply hA
  have hval : ∀ x : ↥K, algebraMap ↥K Ω x ∈ A := by
    intro x
    have hx : x ∈ A.comap (algebraMap ↥K Ω) := by rw [h]; exact ValuationSubring.mem_top x
    rwa [ValuationSubring.mem_comap] at hx
  refine le_antisymm (ValuationSubring.le_top (A.comap (algebraMap k Ω))) ?_
  intro x _
  rw [ValuationSubring.mem_comap]
  simpa only [IsScalarTower.algebraMap_apply k ↥K Ω] using hval (algebraMap k ↥K x)

/-- **The model identification** `V_A ≅ ↥(lcHoms p ↥(decomp (k := ↥K) A))`: the level-`K` local
`H¹`-classes *are* the locally constant characters of the level-`K` local group
(`mupH1locLcHoms`), chosen once and for all. -/
noncomputable def levelKModelIso (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A) →
      ↥(Work.SSGRoute.lcHoms p ↥(_root_.SSGRoute.decomp (k := ↥K) A)) :=
  levelKModelIsoCanon (p := p) (k := k) (Ω := Ω) (K := K) (A := A)

/-- The chosen model identification is bijective. -/
theorem levelKModelIso_bijective (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A) :
    Function.Bijective (levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA) :=
  levelKModelIsoCanon_bijective (p := p) (k := k) (Ω := Ω) (K := K) (A := A)

/-- The chosen model identification is additive on `H¹` and multiplicative on characters. -/
theorem levelKModelIso_add (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (x y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA (x + y) =
      levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x *
        levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA y :=
  levelKModelIsoCanon_add (p := p) (k := k) (Ω := Ω) (K := K) (A := A) x y

/-- The chosen model identification kills `0`. -/
theorem levelKModelIso_zero (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A) :
    levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA 0 = 1 :=
  levelKModelIsoCanon_zero (p := p) (k := k) (Ω := Ω) (K := K) (A := A)

/-- **The character of a level-`K` local class, at the completion**: the model identification
followed by the transport along the canonical homeomorphism `decomp (k := ↥K) A ≃* Gal(κ̄_A/κ_A)`
(`LT_lcHoms_levelK_localGalois`). -/
noncomputable def levelKCharLevelKToGal (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    ↥(Work.SSGRoute.lcHoms p
      ((SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)) ≃ₐ[
        Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK]
        (SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)))) :=
  levelKLocalGalTransport (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hAK
    (levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x)

/-- **The computation rule of the character at the completion**: it is the character of the level-`K`
local group composed with `(mupLocalGalEquiv A hAK).symm` — by definition of the canonical transport
`levelKLocalGalTransport`. -/
theorem levelKCharLevelKToGal_apply (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    (levelKCharLevelKToGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x).1 =
      (levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x).1.comp
        (Work.SSGRoute.ZDataMup.mupLocalGalEquiv (p := p) (k := k) (Ω := Ω) (K := K) (A := A)
          hAK).symm.toMonoidHom :=
  levelKLocalGalTransport_apply (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hAK _

/-- **The character of a level-`K` local class, on the abelianisation**: the factorisation of
`levelKCharLevelKToGal` through `Gal(κ_A^ab/κ_A)` (`LT_lcHoms_factor_through_abGal_lc`). -/
noncomputable def levelKCharToAbGal (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    ↥(Work.SSGRoute.lcHoms p
      (NK.LocalCFT.AbGal (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)
        (SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)))) :=
  Classical.choose (Work.SSGRoute.LT_lcHoms_factor_through_abGal_lc p
    (levelKCharLevelKToGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x))

/-- The defining property of the abelianised character. -/
theorem levelKCharToAbGal_spec (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    ∀ σ : (SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)) ≃ₐ[
        Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK]
        (SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)),
      (levelKCharToAbGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x).1
          (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)
            (K₁ := SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK))
            (NK.LocalReciprocity.maxAbelianSubext
              (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)
              (SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK))) σ)
        = (levelKCharLevelKToGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x).1 σ :=
  fun σ => Classical.choose_spec (Work.SSGRoute.LT_lcHoms_factor_through_abGal_lc p
    (levelKCharLevelKToGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x)) σ

/-- **The local Kummer class of a level-`K` local class**: read off through the level-`K` local
Kummer dictionary `mupKummerEquiv` from the character of the class. -/
noncomputable def levelKLocalClass (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ ⧸
      (powMonoidHom p : (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ →*
        (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ).range :=
  (Work.SSGRoute.ZDataMup.mupKummerEquiv (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ζ) (hζ := hζ) (A := A) hA hAK).symm
    (levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA y)

/-- `Multiplicative (ZMod p)` has exponent `p`. -/
theorem levelK_pow_eq_one (z : Multiplicative (ZMod p)) : z ^ p = 1 := by
  have h : Multiplicative.toAdd (z ^ p) =
      Multiplicative.toAdd (1 : Multiplicative (ZMod p)) := by
    simp only [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  exact h

/-- **The `μ_p` local pairing, multiplicatively in the first variable**: the character of `x`
evaluated at the Artin image of a Kummer class of `κ_Aˣ`.  Well defined because
`Multiplicative (ZMod p)` has exponent `p`. -/
noncomputable def levelKPairMul (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ ⧸
        (powMonoidHom p : (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ →*
          (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ).range →*
      Multiplicative (ZMod p) :=
  QuotientGroup.lift _
    ((levelKCharToAbGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x).1.comp
      (Work.SSGRoute.ZDataMup.mupRec (K := K) A hAK))
    (fun a ha => by
      obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp ha
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, powMonoidHom_apply, map_pow, map_pow]
      exact levelK_pow_eq_one _)

/-- **The canonical `μ_p` local Tate pairing** at the level-`K` local group at `A`: the character
of `x` evaluated at the local Artin image of the Kummer class of `y`. -/
noncomputable def levelKCanonPairing (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) : ZMod p :=
  (levelKPairMul (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x
    (levelKLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA hAK y)).toAdd

/-- **The canonical pairing as a function of the place only**, with the (unnecessary) finiteness
hypothesis discharged internally: this is the shape in which the reciprocity sum
`∑_{A ∈ T'} F_{H_A}[a][b]` of the product formula is stated. -/
noncomputable def levelKCanonPairingAt (A : ValuationSubring Ω)
    (x y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) : ZMod p := by
  classical
  exact if hA : _root_.SSGRoute.IsFinPlace k A then
    levelKCanonPairing (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA
      (isFinPlace_of_isFinPlace_below (K := K) (A := A) hA) x y
  else 0

end

end Work.SSGRoute.ZConstruction
