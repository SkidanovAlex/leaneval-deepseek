import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.NK.HassePrinciple.LocalUnitsSub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Poitou–Tate `Ext` core — shared vocabulary (DEFINITIONS ONLY; lead-written, do not edit)

To be created as `Submission/Work/SSGRoute/PTDefs.lean` with the three imports above.
Namespace: `SSGRoute.PTExt` (inside the `SSGRoute` vocabulary namespace of `Interfaces.lean`).
Nothing here is `sorry`; every definition is a thin wrapper around Mathlib / NK.

Design (see `requests/ssg4/DESIGN_EXT.md`):

* All modules are `Rep Coeff G` with `Coeff = NK.HassePrinciple.CoeffInt = ULift ℤ`, the
  coefficient ring NK uses for `Lˣ`, `𝕀_L`, `C_L`, `L_wˣ`, `𝒪_wˣ`.
* `Ext` is Mathlib's derived-category `Abelian.Ext` (Yoneda products `Ext.comp`, `Ext.mk₀`,
  `ShortExact.extClass`, the long exact sequences of `DerivedCategory/Ext/ExactSequences`,
  `Ext.mapExactFunctor`), valued in `Type` through `hasExt_of_enoughProjectives`.
* Cohomology in the `Ext` core is `extH A n = Ext^n_G(Coeff, A)`; the comparison with
  `groupCohomology` is the node `E0b`.
* **Generator-free.** No fundamental class, invariant map or `ℚ/ℤ` is chosen: every pairing takes
  values in `extH C_L 2 = H²(Gal(L/k), C_L)` itself.  Nonvanishing of such a value does not depend
  on any normalisation, which is all that injectivity statements need.
-/

open CategoryTheory

noncomputable section

namespace SSGRoute.PTExt

/-- The coefficient ring of the `Ext` core: NK's `ℤ` (lifted to `ULift ℤ`, universe `0`). -/
abbrev Coeff : Type := NK.HassePrinciple.CoeffInt.{0}

/-- `Ext` groups in `Rep Coeff G`, valued in `Type` (`Rep Coeff G` has enough projectives). -/
instance hasExt (G : Type) [Group G] : HasExt.{0} (Rep.{0} Coeff G) :=
  hasExt_of_enoughProjectives.{0} (Rep.{0} Coeff G)

section Generic

variable {G : Type} [Group G]

/-- A `G`-module given as a type with a distributive action, as an object of `Rep Coeff G`. -/
abbrev modRep (G M : Type) [Group G] [AddCommGroup M] [DistribMulAction G M] : Rep.{0} Coeff G :=
  Rep.ofDistribMulAction Coeff G M

/-- The trivial module `Coeff = ℤ`. -/
abbrev unitRep (G : Type) [Group G] : Rep.{0} Coeff G := Rep.trivial Coeff G Coeff

/-- `Ext`-cohomology `Hⁿ(G, A) := Extⁿ_G(ℤ, A)`. -/
abbrev extH (A : Rep.{0} Coeff G) (n : ℕ) : Type := Abelian.Ext.{0} (unitRep G) A n

/-- Change of group along `f : H →* G` (restriction / inflation) on `Ext`: the exact functor
`Rep.resFunctor f` applied to an `Ext` class. -/
def extRes {H : Type} [Group H] (f : H →* G) {X Y : Rep.{0} Coeff G} {n : ℕ}
    (x : Abelian.Ext.{0} X Y n) : Abelian.Ext.{0} (Rep.res f X) (Rep.res f Y) n :=
  x.mapExactFunctor (Rep.resFunctor f)

/-- The identity `ℤ → ℤ` from the trivial `H`-module to the restriction of the trivial
`G`-module. -/
def unitRes {H : Type} [Group H] (f : H →* G) : unitRep H ⟶ Rep.res f (unitRep G) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- The identity of `V` from the trivial `H`-module to the restriction of the trivial `G`-module. -/
def trivRes {H : Type} [Group H] (f : H →* G) (V : Type) [AddCommGroup V] [Module Coeff V] :
    Rep.trivial Coeff H V ⟶ Rep.res f (Rep.trivial Coeff G V) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- The identity of `V` from the restriction of the trivial `G`-module to the trivial
`H`-module. -/
def trivResInv {H : Type} [Group H] (f : H →* G) (V : Type) [AddCommGroup V] [Module Coeff V] :
    Rep.res f (Rep.trivial Coeff G V) ⟶ Rep.trivial Coeff H V :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- Change of group on `Ext`-cohomology along `f : H →* G`, followed by a coefficient map
`ι : res f A ⟶ B` (for `f` surjective this is inflation, for `f` injective restriction). -/
def extHMap {H : Type} [Group H] (f : H →* G) {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {n : ℕ} (y : extH A n) : extH B n :=
  (Abelian.Ext.mk₀ (unitRes f)).comp ((extRes f y).comp (Abelian.Ext.mk₀ ι) (add_zero n))
    (zero_add n)

/-- **The Yoneda pairing at one level**: `x ∈ Ext^r_G(M, A)` and `h ∈ H^s(G, M)` give
`h ∘ x ∈ H^{s+r}(G, A)`. -/
def yonedaPair {M A : Rep.{0} Coeff G} {r s : ℕ} (x : Abelian.Ext.{0} M A r) (h : extH M s) :
    extH A (s + r) :=
  h.comp x rfl

/-- **The pairing across levels**: `x ∈ Ext^r_G(M, A)` at the level `G`, pulled back along
`f : H →* G` and pushed along the coefficient map `ι : res f A ⟶ B`, paired with
`h ∈ H^s(H, res f M)`; the value lies in `H^{s+r}(H, B)`. -/
def levelPair {H : Type} [Group H] (f : H →* G) {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r) (h : extH (Rep.res f M) s) :
    extH B (s + r) :=
  h.comp ((extRes f x).comp (Abelian.Ext.mk₀ ι) (add_zero r)) rfl

/-- Restriction of `Ext`-cohomology to a subgroup `D ≤ G`. -/
def extHRestrict (D : Subgroup G) {A : Rep.{0} Coeff G} {n : ℕ} (y : extH A n) :
    extH (Rep.res D.subtype A) n :=
  extHMap D.subtype (𝟙 _) y

/-- `h ∈ H^s(G, M)` is *locally trivial* on a family of subgroups (decomposition groups). -/
def IsLocTrivialOn {ι : Type} (D : ι → Subgroup G) {M : Rep.{0} Coeff G} {s : ℕ}
    (h : extH M s) : Prop :=
  ∀ i, extHRestrict (D i) h = 0

end Generic

/-! ## The class formation at one level `K / k` -/

section Level

open NK.GlobalCFT NK.HassePrinciple

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- `Kˣ` as a `Gal(K/k)`-module (NK `unitsRep`). -/
abbrev unitsK : Rep.{0} Coeff (K ≃ₐ[k] K) := NK.HassePrinciple.unitsRep k K

/-- `𝕀_K` as a `Gal(K/k)`-module (NK `ideleRep`). -/
abbrev idelesK : Rep.{0} Coeff (K ≃ₐ[k] K) := NK.HassePrinciple.ideleRep k K

/-- `C_K = 𝕀_K / Kˣ` as a `Gal(K/k)`-module (NK `classGroupRep`). -/
abbrev classesK : Rep.{0} Coeff (K ≃ₐ[k] K) := NK.HassePrinciple.classGroupRep k K

/-- The class formation `0 → Kˣ → 𝕀_K → C_K → 0` (short exact: NK `ideleShortComplex_shortExact`). -/
abbrev sesK : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)) := NK.HassePrinciple.ideleShortComplex k K

variable {k K}

/-- Postcomposition with `Kˣ → 𝕀_K`. -/
def extToIdeles {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (x : Abelian.Ext.{0} M (unitsK k K) r) :
    Abelian.Ext.{0} M (idelesK k K) r :=
  x.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K)) (add_zero r)

/-- Postcomposition with `𝕀_K → C_K`. -/
def extToClasses {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (x : Abelian.Ext.{0} M (idelesK k K) r) : Abelian.Ext.{0} M (classesK k K) r :=
  x.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k K)) (add_zero r)

/-- **The connecting map** `δ : Ext^r_G(M, C_K) → Ext^{r+1}_G(M, Kˣ)` of the class formation
(Yoneda product with the class of `0 → Kˣ → 𝕀_K → C_K → 0`). -/
def extDelta {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (x : Abelian.Ext.{0} M (classesK k K) r) :
    Abelian.Ext.{0} M (unitsK k K) (r + 1) :=
  x.comp (NK.HassePrinciple.ideleShortComplex_shortExact k K).extClass rfl

/-- The pairing at the level `K` itself: `Ext^r_G(M, C_K) × H^s(G, M) → H^{s+r}(G, C_K)`. -/
def pairK {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ} (x : Abelian.Ext.{0} M (classesK k K) r)
    (h : extH M s) : extH (classesK k K) (s + r) :=
  yonedaPair x h

variable [FiniteDimensional k K] [IsGalois k K]

/-- The decomposition group `D_w ≤ Gal(K/k)` of a place `w` of `K` (NK convention). -/
abbrev decompK (w : Place K) : Subgroup (K ≃ₐ[k] K) := MulAction.stabilizer (K ≃ₐ[k] K) w

/-- `K_wˣ` as a `D_w`-module (NK `localUnitsRep`). -/
abbrev localUnitsK (w : Place K) : Rep.{0} Coeff (decompK (k := k) w) :=
  NK.HassePrinciple.localUnitsRep k K w

/-- **Localisation of `Ext` with idèle coefficients** at the place `w`:
`Ext^r_G(M, 𝕀_K) → Ext^r_{D_w}(M, K_wˣ)` (restrict to `D_w`, then take the `w`-component). -/
def extLoc (w : Place K) {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (x : Abelian.Ext.{0} M (idelesK k K) r) :
    Abelian.Ext.{0} (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) r :=
  (extRes (decompK (k := k) w).subtype x).comp
    (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleToLocalUnits k K w)) (add_zero r)

/-- A local class is **unramified** if it comes from the integral units `𝒪_wˣ`. -/
def IsUnramifiedExt (w : Place K) {M : Rep.{0} Coeff (decompK (k := k) w)} {r : ℕ}
    (y : Abelian.Ext.{0} M (localUnitsK (k := k) w) r) : Prop :=
  ∃ z : Abelian.Ext.{0} M (NK.HassePrinciple.localUnitsSubRep k K w) r,
    y = z.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsIncl (K := k) (L := K) w))
      (add_zero r)

/-- `h ∈ H^s(Gal(K/k), M)` is locally trivial at every place of `K`. -/
def IsLocTrivial {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {s : ℕ} (h : extH M s) : Prop :=
  IsLocTrivialOn (fun w : Place K => decompK (k := k) w) h

end Level

/-! ## Two levels `k ⊆ K ⊆ L` -/

section TwoLevels

open NK.GlobalCFT

variable (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional k K] [IsGalois k K]

/-- The restriction `Gal(L/k) →* Gal(K/k)`. -/
abbrev galRes : (L ≃ₐ[k] L) →* (K ≃ₐ[k] K) := AlgEquiv.restrictNormalHom K

/-- `ι : res C_K ⟶ C_L` is **the canonical inclusion of idèle class groups**: it is induced by an
idèle map `𝕀_K → 𝕀_L` whose `w`-component is the local embedding `K_{u w} → L_w`. -/
def IsCanonicalClassIncl
    (ι : Rep.res (galRes k K L) (classesK k K) ⟶ classesK k L) : Prop :=
  ∃ (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w)) (φ : Idele K →* Idele L),
    (∀ (x : Idele K) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))) ∧
    ∀ x : Idele K, ι.hom (Additive.ofMul (IdeleClassGroup.mk K x)) =
      Additive.ofMul (IdeleClassGroup.mk L (φ x))

open Classical in
/-- **The inclusion `C_K → C_L`** as a morphism of `Gal(L/k)`-modules (the canonical one; its
existence is the node `E0c`, `0` is a junk value never used). -/
def classIncl : Rep.res (galRes k K L) (classesK k K) ⟶ classesK k L :=
  if h : ∃ ι, IsCanonicalClassIncl k K L ι then Classical.choose h else 0

variable {k K L}

/-- **`φ` at the level `L`** (generator-free): for `x ∈ Ext^r_{Gal(K/k)}(M, C_K)` and
`h ∈ H^s(Gal(L/k), M)`, the value `h ∘ infl(x) ∈ H^{s+r}(Gal(L/k), C_L)`.  For `r + s = 2` this is
`φ^r_M(x)(h)` of the design, before any identification `H²(Gal(L/k), C_L) ≅ ℤ/[L:k]`. -/
def phiAt {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ} (x : Abelian.Ext.{0} M (classesK k K) r)
    (h : extH (Rep.res (galRes k K L) M) s) : extH (classesK k L) (s + r) :=
  levelPair (galRes k K L) (classIncl k K L) x h

/-- Inflation `H^n(Gal(K/k), C_K) → H^n(Gal(L/k), C_L)`. -/
def inflC {n : ℕ} (y : extH (classesK k K) n) : extH (classesK k L) n :=
  extHMap (galRes k K L) (classIncl k K L) y

/-- Inflation of `Ext`-cohomology of a `Gal(K/k)`-module to `Gal(L/k)`. -/
def inflH {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {n : ℕ} (y : extH M n) :
    extH (Rep.res (galRes k K L) M) n :=
  extHMap (galRes k K L) (𝟙 _) y

/-- `φ` for a *trivial* module `V` (e.g. `V = ZMod p`): `h ∈ H^s(Gal(L/k), V)` is viewed in the
cohomology of the restricted trivial `Gal(K/k)`-module. -/
def phiTriv (V : Type) [AddCommGroup V] [Module Coeff V] {r s : ℕ}
    (x : Abelian.Ext.{0} (Rep.trivial Coeff (K ≃ₐ[k] K) V) (classesK k K) r)
    (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) V) s) : extH (classesK k L) (s + r) :=
  phiAt (k := k) (K := K) (L := L) x
    (h.comp (Abelian.Ext.mk₀ (trivRes (galRes k K L) V)) (add_zero s))

/-- Inflation of `H^n(Gal(K/k), V)` to `H^n(Gal(L/k), V)` for a trivial module `V`. -/
def inflTriv (V : Type) [AddCommGroup V] [Module Coeff V] {n : ℕ}
    (h : extH (Rep.trivial Coeff (K ≃ₐ[k] K) V) n) : extH (Rep.trivial Coeff (L ≃ₐ[k] L) V) n :=
  extHMap (galRes k K L) (trivResInv (galRes k K L) V) h

end TwoLevels

/-! ## Three levels `k ⊆ K ⊆ L ⊆ L'`: inflation of cohomology of a `Gal(K/k)`-module -/

section ThreeLevels

variable {k K L L' : Type} [Field k] [Field K] [Field L] [Field L'] [Algebra k K] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L] [Algebra k L'] [Algebra K L'] [IsScalarTower k K L']
  [Algebra L L'] [IsScalarTower k L L'] [IsScalarTower K L L'] [Normal k K] [Normal k L]

/-- Restriction to `K` factors through restriction to `L` (helper for `resResHom`). -/
theorem galRes_trans (σ : L' ≃ₐ[k] L') :
    AlgEquiv.restrictNormalHom K (AlgEquiv.restrictNormalHom L σ) =
      AlgEquiv.restrictNormalHom K σ := by
  ext x
  apply (algebraMap K L').injective
  show algebraMap K L' ((AlgEquiv.restrictNormal (AlgEquiv.restrictNormal σ L) K) x) =
    algebraMap K L' ((AlgEquiv.restrictNormal σ K) x)
  rw [IsScalarTower.algebraMap_apply K L L', AlgEquiv.restrictNormal_commutes,
    AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes,
    ← IsScalarTower.algebraMap_apply]

/-- The identity of `M`, from the `Gal(L'/k)`-module restricted in two steps to the one restricted
in one step. -/
def resResHom (M : Rep.{0} Coeff (K ≃ₐ[k] K)) :
    Rep.res (AlgEquiv.restrictNormalHom (K₁ := L') L)
        (Rep.res (AlgEquiv.restrictNormalHom (K₁ := L) K) M) ⟶
      Rep.res (AlgEquiv.restrictNormalHom (K₁ := L') K) M :=
  eqToHom (by
    have h : (M.ρ.comp (AlgEquiv.restrictNormalHom (K₁ := L) K)).comp
        (AlgEquiv.restrictNormalHom (K₁ := L') L) =
        M.ρ.comp (AlgEquiv.restrictNormalHom (K₁ := L') K) := by
      ext σ : 1
      exact congrArg M.ρ (galRes_trans σ)
    dsimp only [Rep.res, Rep.resFunctor]
    rw [h])

/-- Inflation `H^n(Gal(L/k), M) → H^n(Gal(L'/k), M)` for a `Gal(K/k)`-module `M`. -/
def inflHLevel {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {n : ℕ}
    (h : extH (Rep.res (AlgEquiv.restrictNormalHom (K₁ := L) K) M) n) :
    extH (Rep.res (AlgEquiv.restrictNormalHom (K₁ := L') K) M) n :=
  extHMap (AlgEquiv.restrictNormalHom (K₁ := L') L) (resResHom (L := L) (L' := L') M) h

end ThreeLevels

/-! ## Inertia and unramified classes at a finite place of a level `L` -/

section Inertia

variable {k L : Type} [Field k] [Field L] [NumberField L] [Algebra k L]

/-- `σ ∈ Gal(L/k)` lies in the inertia group of the finite place `q` of `L`. -/
def IsInertiaAt (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[k] L) : Prop :=
  ∀ x : NumberField.RingOfIntegers L, q.valuation L (σ (x : L) - (x : L)) < 1

/-- `h ∈ H^s(Gal(L/k), M)` is unramified at `q`: its restriction to (every subgroup of) the
inertia group of `q` vanishes. -/
def IsUnramifiedClassAt (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {M : Rep.{0} Coeff (L ≃ₐ[k] L)} {s : ℕ} (h : extH M s) : Prop :=
  ∀ D : Subgroup (L ≃ₐ[k] L), (∀ σ ∈ D, IsInertiaAt q σ) → extHRestrict D h = 0

end Inertia

/-- **`φ¹` has trivial kernel at `x`**: `x ∈ Ext^1_{Gal(K/k)}(M, C_K)` pairs to zero with every
class `h ∈ H¹(Gal(L/k), M)` at every finite Galois level `L ⊇ K`. -/
def PhiOneVanishes (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (x : Abelian.Ext.{0} M (classesK k K) 1) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L] (h : extH (Rep.res (galRes k K L) M) 1),
    phiAt (k := k) (K := K) (L := L) x h = 0

end SSGRoute.PTExt
