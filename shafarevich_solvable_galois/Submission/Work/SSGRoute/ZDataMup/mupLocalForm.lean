import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.LocallyConstant.Basic
import Submission.Work.SSGRoute.ZDataMup.eq_one_of_forall_artin_eq_one
import Submission.Work.SSGRoute.ZDataMup.exists_factor_of_homeomorph
import Submission.Work.SSGRoute.ZDataMup.isLocallyConstant_factor_restrictNormalHom
import Submission.Work.SSGRoute.ZDataMup.mupH1locLcHoms
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `μ_p` local Tate pairing at a finite place

The bilinear pairing `F_A(x, y) = x'(rec_A(α_y))` on the level-`K` local `H¹`-group
`V_A = H1loc p k Ω K (ZMod p) (decomp k A ⊓ K.fixingSubgroup)`, where

* `α_y` is the local Kummer class of `y` (`mupLocalClass`, via the chosen dictionary
  `mupKummerEquiv`),
* `x' : Gal(κ_A^ab/κ_A) →* Multiplicative (ZMod p)` is the character of `x` (the model
  identification `mupH1locLcHoms`, the local Galois identification `mupLocalGalEquiv`, and the
  factorisation through the abelianisation `exists_factor_of_homeomorph`),
* `rec_A` is the local Artin map of the completion (`mupRec`).

The key design point: the **first** variable is the character and the **second** the Kummer
element.  First-variable non-degeneracy is then the *density* of `rec_A(κ_Aˣ)` in
`Gal(κ_A^ab/κ_A)` (`eq_one_of_forall_artin_eq_one`); no symmetry of the Hilbert symbol and no
injectivity of `rec_A` is needed.

On global classes the pairing is the *transposed* Hilbert symbol
`χ_α(rec_A(β_A)) = ⟨β_A, α_A⟩_A`, whose product formula is the crux.
-/

namespace Work.SSGRoute.ZDataMup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

open _root_.SSGRoute

noncomputable section

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {A : ValuationSubring Ω}

/-- The level-`K` local group at the place `A`. -/
abbrev mupLocalGroup (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup

/-- `Multiplicative (ZMod p)` has exponent `p`. -/
theorem mup_pow_eq_one (z : Multiplicative (ZMod p)) : z ^ p = 1 := by
  have h : Multiplicative.toAdd (z ^ p) = Multiplicative.toAdd (1 : Multiplicative (ZMod p)) := by
    simp only [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  exact h

/-- **The model identification** `V_A ≅ ↥(lcHoms p ↥(decomp (k := ↥K) A))`, chosen once and for
all. -/
noncomputable def mupModelIso (hA : _root_.SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A) →
      ↥(Work.SSGRoute.lcHoms p ↥(_root_.SSGRoute.decomp (k := ↥K) A)) :=
  Classical.choose (mupH1locLcHoms (p := p) (k := k) (Ω := Ω) (K := K) A hA)

/-- The chosen model identification is bijective. -/
theorem mupModelIso_bijective (hA : _root_.SSGRoute.IsFinPlace k A) :
    Function.Bijective (mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA) :=
  (Classical.choose_spec (mupH1locLcHoms (p := p) (k := k) (Ω := Ω) (K := K) A hA)).1

/-- The chosen model identification is additive on `H¹` and multiplicative on characters. -/
theorem mupModelIso_add (hA : _root_.SSGRoute.IsFinPlace k A)
    (x y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA (x + y) =
      mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x *
        mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA y :=
  (Classical.choose_spec (mupH1locLcHoms (p := p) (k := k) (Ω := Ω) (K := K) A hA)).2.1 x y

/-- The chosen model identification kills `0`. -/
theorem mupModelIso_zero (hA : _root_.SSGRoute.IsFinPlace k A) :
    mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA 0 = 1 :=
  (Classical.choose_spec (mupH1locLcHoms (p := p) (k := k) (Ω := Ω) (K := K) A hA)).2.2.1

/-- **The model identification on cocycles**: the image of the class of a global cocycle is the
character of its restriction to the level-`K` local group. -/
theorem mupModelIso_toClass (hA : _root_.SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → ZMod p)
    (ha : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) K.fixingSubgroup)
    (g : ↥(mupLocalGroup k Ω K A)) :
    ((mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (mupLocalGroup k Ω K A) a)).1
      (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd = a ↑g :=
  (Classical.choose_spec (mupH1locLcHoms (p := p) (k := k) (Ω := Ω) (K := K) A hA)).2.2.2 a ha g

/-- **The map `D_A →* Gal(κ_A^ab/κ_A)`** through the local Galois identification and the
abelianisation. -/
noncomputable def mupAbMap (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    ↥(_root_.SSGRoute.decomp (k := ↥K) A) →*
      NK.LocalCFT.AbGal (mupCompletion (K := K) A hAK)
        (SeparableClosure (mupCompletion (K := K) A hAK)) :=
  MonoidHom.mk' (fun d => AlgEquiv.restrictNormalHom
    (F := mupCompletion (K := K) A hAK)
    (K₁ := SeparableClosure (mupCompletion (K := K) A hAK))
    ↥(NK.LocalReciprocity.maxAbelianSubext (mupCompletion (K := K) A hAK)
      (SeparableClosure (mupCompletion (K := K) A hAK)))
    ((mupLocalGalEquiv (p := p) (K := K) A hAK) d))
    (fun a b => by rw [map_mul, map_mul])

/-- The map `D_A →* Gal(κ_A^ab/κ_A)` is surjective. -/
theorem mupAbMap_surjective (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    Function.Surjective (mupAbMap (p := p) (K := K) (A := A) hAK) :=
  (AlgEquiv.restrictNormalHom_surjective (F := mupCompletion (K := K) A hAK)
    (K₁ := ↥(NK.LocalReciprocity.maxAbelianSubext (mupCompletion (K := K) A hAK)
      (SeparableClosure (mupCompletion (K := K) A hAK))))
    (E := SeparableClosure (mupCompletion (K := K) A hAK))).comp
    (mupLocalGalEquiv (p := p) (K := K) A hAK).surjective

/-- **The abelianised character of a local class**, built from the character of the model
identification by the factorisation through the abelianisation. -/
noncomputable def mupCharToAbGal (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    NK.LocalCFT.AbGal (mupCompletion (K := K) A hAK)
      (SeparableClosure (mupCompletion (K := K) A hAK)) →* Multiplicative (ZMod p) :=
  Classical.choose (exists_factor_of_homeomorph (p := p)
    (F := mupCompletion (K := K) A hAK)
    (F' := SeparableClosure (mupCompletion (K := K) A hAK))
    (G := ↥(_root_.SSGRoute.decomp (k := ↥K) A))
    (mupLocalGalEquiv (p := p) (K := K) A hAK)
    (isHomeomorph_mupLocalGalEquiv (p := p) (K := K) A hAK)
    ((mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x).1)
    ((mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x).2))

/-- The defining property of the abelianised character. -/
theorem mupCharToAbGal_comp (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    (mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x).comp (mupAbMap (p := p) (K := K) (A := A) hAK) =
      (mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x).1 :=
  Classical.choose_spec (exists_factor_of_homeomorph (p := p)
    (F := mupCompletion (K := K) A hAK)
    (F' := SeparableClosure (mupCompletion (K := K) A hAK))
    (G := ↥(_root_.SSGRoute.decomp (k := ↥K) A))
    (mupLocalGalEquiv (p := p) (K := K) A hAK)
    (isHomeomorph_mupLocalGalEquiv (p := p) (K := K) A hAK)
    ((mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x).1)
    ((mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x).2))

/-- The abelianised character of a local class is locally constant. -/
theorem mupCharToAbGal_isLocallyConstant (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    IsLocallyConstant (mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x) :=
  isLocallyConstant_factor_restrictNormalHom (p := p)
    (F := mupCompletion (K := K) A hAK)
    (F' := SeparableClosure (mupCompletion (K := K) A hAK))
    (G := ↥(_root_.SSGRoute.decomp (k := ↥K) A))
    (mupLocalGalEquiv (p := p) (K := K) A hAK)
    (isHomeomorph_mupLocalGalEquiv (p := p) (K := K) A hAK)
    ((mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x).1)
    ((mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x).2)
    (mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x)
    (mupCharToAbGal_comp (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x)

/-- **Additivity of the abelianised character** in the local class. -/
theorem mupCharToAbGal_add (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x x' : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    mupCharToAbGal (p := p) (K := K) (A := A) hA hAK (x + x') =
      mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x *
        mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x' := by
  have key : ∀ y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A),
      (mupCharToAbGal (p := p) (K := K) (A := A) hA hAK y).comp
          (mupAbMap (p := p) (K := K) (A := A) hAK) =
        (mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA y).1 :=
    fun y => mupCharToAbGal_comp (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK y
  have hcomp : (mupCharToAbGal (p := p) (K := K) (A := A) hA hAK (x + x')).comp
        (mupAbMap (p := p) (K := K) (A := A) hAK) =
      ((mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x) *
        (mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x')).comp
        (mupAbMap (p := p) (K := K) (A := A) hAK) := by
    rw [key (x + x'), MonoidHom.mul_comp, key x, key x']
    have h := congrArg Subtype.val
      (mupModelIso_add (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x x')
    simpa using h
  refine MonoidHom.ext fun b => ?_
  obtain ⟨d, hd⟩ := mupAbMap_surjective (p := p) (K := K) (A := A) hAK b
  subst hd
  simpa using DFunLike.congr_fun hcomp d

/-- **The local Kummer class of a local class.** -/
noncomputable def mupLocalClass (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    (mupCompletion (K := K) A hAK)ˣ ⧸
      (powMonoidHom p : (mupCompletion (K := K) A hAK)ˣ →*
        (mupCompletion (K := K) A hAK)ˣ).range :=
  (mupKummerEquiv (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) hA hAK).symm
    (mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA y)

/-- `mupLocalClass` is surjective. -/
theorem mupLocalClass_surjective (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    Function.Surjective (mupLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA hAK) :=
  (mupKummerEquiv (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) hA hAK).symm.surjective.comp
    (mupModelIso_bijective (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA).2

/-- **Multiplicativity of the local Kummer class map** (additivity on `H¹`). -/
theorem mupLocalClass_add (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (y y' : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    mupLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK
        (y + y') =
      mupLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK y *
        mupLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK
          y' := by
  rw [mupLocalClass, mupLocalClass, mupLocalClass, mupModelIso_add, map_mul]

/-- **The `μ_p` local Tate pairing**, multiplicatively in the first variable. -/
noncomputable def mupPairMul (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    (mupCompletion (K := K) A hAK)ˣ ⧸
        (powMonoidHom p : (mupCompletion (K := K) A hAK)ˣ →*
          (mupCompletion (K := K) A hAK)ˣ).range →* Multiplicative (ZMod p) :=
  QuotientGroup.lift _
    ((mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x).comp (mupRec (K := K) A hAK))
    (fun a ha => by
      obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp ha
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, powMonoidHom_apply, map_pow, map_pow]
      exact mup_pow_eq_one _)

/-- The value of the pairing on the class of a unit. -/
theorem mupPairMul_localPowClass (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A))
    (α : (mupCompletion (K := K) A hAK)ˣ) :
    mupPairMul (p := p) (K := K) (A := A) hA hAK x
        (QuotientGroup.mk' (powMonoidHom p : (mupCompletion (K := K) A hAK)ˣ →*
          (mupCompletion (K := K) A hAK)ˣ).range α) =
      mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x (mupRec (K := K) A hAK α) := by
  rw [mupPairMul]
  exact QuotientGroup.lift_mk' _ _ α

/-- **The `μ_p` local Tate pairing**: `F_A(x, y) = x'(rec_A(α_y))`. -/
noncomputable def mupHilb (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) : ZMod p :=
  (mupPairMul (p := p) (K := K) (A := A) hA hAK x
    (mupLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK
      y)).toAdd

/-- **Additivity of the pairing in the first variable.** -/
theorem mupHilb_add_left (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x x' y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    mupHilb (p := p) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK (x + x') y =
      mupHilb (p := p) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK x y +
        mupHilb (p := p) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK x' y := by
  rw [mupHilb, mupHilb, mupHilb]
  obtain ⟨α, hα⟩ := QuotientGroup.mk'_surjective
    ((powMonoidHom p : (mupCompletion (K := K) A hAK)ˣ →*
      (mupCompletion (K := K) A hAK)ˣ).range)
    (mupLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK y)
  rw [← hα, mupPairMul_localPowClass, mupPairMul_localPowClass, mupPairMul_localPowClass,
    mupCharToAbGal_add, MonoidHom.mul_apply, toAdd_mul]

/-- **Additivity of the pairing in the second variable.** -/
theorem mupHilb_add_right (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x y y' : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A)) :
    mupHilb (p := p) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK x (y + y') =
      mupHilb (p := p) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK x y +
        mupHilb (p := p) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK x y' := by
  rw [mupHilb, mupHilb, mupHilb, mupLocalClass_add, map_mul, toAdd_mul]

/-- **First-variable non-degeneracy of the local pairing.** -/
theorem mupHilb_nondegenerate (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (mupLocalGroup k Ω K A))
    (h : ∀ y, mupHilb (p := p) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA hAK x y = 0) : x = 0 := by
  have h1 : ∀ q : (mupCompletion (K := K) A hAK)ˣ ⧸
      (powMonoidHom p : (mupCompletion (K := K) A hAK)ˣ →*
        (mupCompletion (K := K) A hAK)ˣ).range,
      mupPairMul (p := p) (K := K) (A := A) hA hAK x q = 1 := by
    intro q
    obtain ⟨y, rfl⟩ := mupLocalClass_surjective (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (A := A) hA hAK q
    exact h y
  have h2 : ∀ α : (mupCompletion (K := K) A hAK)ˣ,
      mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x (mupRec (K := K) A hAK α) = 1 := fun α => by
    have hα := h1 (QuotientGroup.mk' (powMonoidHom p : (mupCompletion (K := K) A hAK)ˣ →*
      (mupCompletion (K := K) A hAK)ˣ).range α)
    rwa [mupPairMul_localPowClass] at hα
  have h3 := eq_one_of_forall_artin_eq_one (p := p)
    (mupArtinReciprocity (K := K) A hAK)
    (mupCharToAbGal (p := p) (K := K) (A := A) hA hAK x)
    (mupCharToAbGal_isLocallyConstant (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x)
    h2
  have h4 : (mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x).1 = 1 := by
    rw [← mupCharToAbGal_comp (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x, h3]
    ext b
    simp
  have h5 : mupModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x = 1 :=
    Subtype.ext h4
  exact (mupModelIso_bijective (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA).1
    (by rw [h5, mupModelIso_zero])

end

end Work.SSGRoute.ZDataMup
