import Mathlib
import ChallengeDeps

/-!
# Blueprint interfaces for `derived_solidification_free_CW_homology`

One `Prop` per area. Every area may ASSUME the other areas' Props as hypotheses; the final
holes are a composition (see `HANDOFF.md` for the map and `Submission.lean` for the wiring).

Conventions:
* `LightCondAb`, `Solid`, `isSolid`, `P`, `oneMinusShift`, `DLightCondAb`, `DSolid`,
  `derivedInclusion`, `freeLightCondAbOfTop(Functor)`, `CWTopCat`, singular-chain functors come
  from `ChallengeDeps` (namespace `LightCondensed` / `LightCondensed.Solid`).
* Cohomological indexing everywhere (`ComplexShape.up ℤ`); singular chains sit in degrees `≤ 0`.
* "Solid-cofibrant" (`SolidCofibrant`) replaces "K-projective" (LightCondAb has too few
  projectives); "solid-equivalence" (`SolidEquiv`) replaces "becomes an iso after `L■`".
  Both are stated with Hom into the derived inclusion of solid objects, so they do not depend
  on which solidification functor is chosen.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Submission.Blueprint

open _root_.LightCondensed _root_.LightCondensed.Solid

universe u

/-! ## Objects -/

/-- The inclusion of solid objects, applied degreewise to cochain complexes. -/
abbrev ιC : CochainComplex Solid ℤ ⥤ CochainComplex LightCondAb ℤ :=
  isSolid.ι.mapHomologicalComplex (ComplexShape.up ℤ)

/-- A cochain complex as an object of the homotopy category. -/
abbrev hq (K : CochainComplex LightCondAb ℤ) : HomotopyCategory LightCondAb (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).obj K

/-- `K` is *solid-cofibrant*: homotopy classes of chain maps from `K` into the degreewise
inclusion of any complex of solid objects are the same as morphisms in `D(LightCondAb)`.
(K-projective complexes are solid-cofibrant; the free objects `ℤ[S]` are the key new examples.) -/
def SolidCofibrant (K : CochainComplex LightCondAb ℤ) : Prop :=
  ∀ N : CochainComplex Solid ℤ,
    Function.Bijective (fun f : hq K ⟶ hq (ιC.obj N) => DerivedCategory.Qh.map f)

/-- `f` is a *solid-equivalence*: it induces bijections on morphisms into the derived inclusion
of every object of `D(Solid)` (all shifts included). Equivalently `L■ f` is an isomorphism. -/
def SolidEquiv {X Y : DLightCondAb} (f : X ⟶ Y) : Prop :=
  ∀ N : DSolid, Function.Bijective (fun g : Y ⟶ derivedInclusion.obj N => f ≫ g)

/-- The free light condensed abelian group on a light profinite set, as a single complex in
degree `n`. -/
abbrev atom (S : LightProfinite.{0}) (n : ℤ) : CochainComplex LightCondAb ℤ :=
  (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) n).obj ((free ℤ).obj S.toCondensed)

/-- Map of free objects on topological spaces, placed in degree `0` of the derived category. -/
abbrev dFree {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X) ⟶
      (DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop Y) :=
  (DerivedCategory.singleFunctor LightCondAb 0).map (freeLightCondAbOfTopFunctor.map f)

/-- The inclusion `Y → Y × [0,1]`, `y ↦ (y, 0)`. -/
def i₀ (Y : TopCat.{0}) : Y ⟶ TopCat.of (Y × unitInterval) :=
  TopCat.ofHom ⟨fun y => (y, 0), by fun_prop⟩

/-- Inclusion of a subspace. -/
def inclTop {X : TopCat.{0}} (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Inclusion of subspaces `A ⊆ B`. -/
def incl {X : TopCat.{0}} {A B : Set X} (h : A ⊆ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

/-- Integral singular chains (Mathlib), as `ℕ`-graded chain complexes of abelian groups. -/
abbrev singC : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-! ## Area REFL (holes 1–3) -/

/-- **AREA REFL.** Solid objects form a reflective subcategory. -/
def ReflProp : Prop := isSolid.ι.IsRightAdjoint

section Package

variable [isSolid.ι.IsRightAdjoint]

/-- The solidification functor determined by `ReflProp` (hole 1 is defined to be this). -/
abbrev sol : LightCondAb ⥤ Solid := isSolid.ι.leftAdjoint

/-- The solidification adjunction (hole 3 is defined to be this). -/
def solAdj : sol ⊣ isSolid.ι := Adjunction.ofIsRightAdjoint _

instance sol_additive : sol.Additive := solAdj.left_adjoint_additive

/-- Degreewise solidification of cochain complexes. -/
abbrev solC : CochainComplex LightCondAb ℤ ⥤ CochainComplex Solid ℤ :=
  sol.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Everything the rest of the proof needs to know about derived solidification
(holes 4–7 are the fields `L`, `α`, `isLeft`, `adj`). -/
structure DerivedPackage where
  /-- derived solidification (hole 4) -/
  L : DLightCondAb ⥤ DSolid
  /-- its counit (hole 5) -/
  α : DerivedCategory.Q ⋙ L ⟶ solC ⋙ DerivedCategory.Q
  /-- hole 6 -/
  isLeft : L.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))
  /-- hole 7 -/
  adj : L ⊣ derivedInclusion
  /-- the counit is an isomorphism on solid-cofibrant complexes -/
  iso_of_cofibrant : ∀ K, SolidCofibrant K → IsIso (α.app K)

end Package

/-! ## The crux: derived solidification (holes 4–7) -/

/-- **AREA ATOM.** Free objects on light profinite sets are solid-cofibrant. -/
def AtomProp : Prop := ∀ (S : LightProfinite.{0}) (n : ℤ), SolidCofibrant (atom S n)

/-- **AREA FLAT.** Free light condensed abelian groups are flat (so `P ⊗ -` is exact). -/
def FlatProp : Prop :=
  ∀ T : LightCondSet.{0}, PreservesFiniteLimits (tensorLeft ((free ℤ).obj T))

/-- **AREA RESOL.** Functorial solid-cofibrant resolutions of unbounded complexes, and
K-projective complexes are solid-cofibrant. -/
def ResolutionProp : Prop :=
  (∃ (ρ : CochainComplex LightCondAb ℤ ⥤ CochainComplex LightCondAb ℤ) (ε : ρ ⟶ 𝟭 _),
      (∀ K, SolidCofibrant (ρ.obj K)) ∧ ∀ K, QuasiIso (ε.app K)) ∧
    ∀ (K : CochainComplex LightCondAb ℤ), K.IsKProjective → SolidCofibrant K

/-- **AREA DERFORMAL.** The derived package exists (for the solidification of `ReflProp`), and
solid-equivalences are exactly the maps inverted by `L`. -/
def DerivedProp : Prop :=
  ∀ [isSolid.ι.IsRightAdjoint], Nonempty DerivedPackage ∧
    ∀ (D : DerivedPackage) {X Y : DLightCondAb} (f : X ⟶ Y), SolidEquiv f ↔ IsIso (D.L.map f)

/-! ## Toolkit for solid-equivalences -/

/-- **AREA TOOLKIT.** Closure properties of solid-equivalences. -/
structure ToolkitProp : Prop where
  comp : ∀ {X Y Z : DLightCondAb} (f : X ⟶ Y) (g : Y ⟶ Z), SolidEquiv f → SolidEquiv g →
    SolidEquiv (f ≫ g)
  of_comp_left : ∀ {X Y Z : DLightCondAb} (f : X ⟶ Y) (g : Y ⟶ Z), SolidEquiv f →
    SolidEquiv (f ≫ g) → SolidEquiv g
  of_comp_right : ∀ {X Y Z : DLightCondAb} (f : X ⟶ Y) (g : Y ⟶ Z), SolidEquiv g →
    SolidEquiv (f ≫ g) → SolidEquiv f
  of_iso : ∀ {X Y : DLightCondAb} (f : X ⟶ Y), IsIso f → SolidEquiv f
  /-- two-out-of-three along a morphism of short exact sequences of complexes -/
  ses₂ : ∀ {S₁ S₂ : ShortComplex (CochainComplex LightCondAb ℤ)} (_ : S₁.ShortExact)
    (_ : S₂.ShortExact) (φ : S₁ ⟶ S₂), SolidEquiv (DerivedCategory.Q.map φ.τ₁) →
      SolidEquiv (DerivedCategory.Q.map φ.τ₃) → SolidEquiv (DerivedCategory.Q.map φ.τ₂)
  ses₃ : ∀ {S₁ S₂ : ShortComplex (CochainComplex LightCondAb ℤ)} (_ : S₁.ShortExact)
    (_ : S₂.ShortExact) (φ : S₁ ⟶ S₂), SolidEquiv (DerivedCategory.Q.map φ.τ₁) →
      SolidEquiv (DerivedCategory.Q.map φ.τ₂) → SolidEquiv (DerivedCategory.Q.map φ.τ₃)
  ses₁ : ∀ {S₁ S₂ : ShortComplex (CochainComplex LightCondAb ℤ)} (_ : S₁.ShortExact)
    (_ : S₂.ShortExact) (φ : S₁ ⟶ S₂), SolidEquiv (DerivedCategory.Q.map φ.τ₂) →
      SolidEquiv (DerivedCategory.Q.map φ.τ₃) → SolidEquiv (DerivedCategory.Q.map φ.τ₁)
  /-- arbitrary (small) coproducts -/
  sigma : ∀ (J : Type) (K L : J → CochainComplex LightCondAb ℤ) [HasCoproduct K]
    [HasCoproduct L] (f : ∀ j, K j ⟶ L j), (∀ j, SolidEquiv (DerivedCategory.Q.map (f j))) →
      SolidEquiv (DerivedCategory.Q.map (Limits.Sigma.map f))
  /-- sequential colimits along monomorphisms -/
  seqColim : ∀ (F G : ℕ ⥤ CochainComplex LightCondAb ℤ) (τ : F ⟶ G),
    (∀ n, Mono (F.map (homOfLE (Nat.le_succ n)))) → (∀ n, Mono (G.map (homOfLE (Nat.le_succ n)))) →
    (∀ n, SolidEquiv (DerivedCategory.Q.map (τ.app n))) →
      SolidEquiv (DerivedCategory.Q.map (colim.map τ))
  /-- degreewise criterion for complexes concentrated in degrees `≤ 0` -/
  levelwise : ∀ (K L : CochainComplex LightCondAb ℤ) (f : K ⟶ L),
    (∀ q : ℤ, 0 < q → IsZero (K.X q)) → (∀ q : ℤ, 0 < q → IsZero (L.X q)) →
    (∀ q : ℤ, SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map (f.f q))) →
      SolidEquiv (DerivedCategory.Q.map f)

/-! ## Analytic core -/

/-- **AREA ANALYTIC (subproject).** Homotopy invariance of `ℤ[-]` up to solid-equivalence:
for every Hausdorff space `Y`, `ℤ[Y] → ℤ[Y × [0,1]]` (at `0`) is a solid-equivalence. -/
def HIProp : Prop := ∀ (Y : TopCat.{0}) [T2Space Y], SolidEquiv (dFree (i₀ Y))

/-- **AREA DISC.** Discrete light condensed abelian groups are solid, and discrete free
abelian groups are projective. -/
def DiscProp : Prop :=
  (∀ M : ModuleCat.{0} ℤ, isSolid ((LightCondensed.discrete (ModuleCat ℤ)).obj M)) ∧
    ∀ (J : Type), Projective ((LightCondensed.discrete (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ (J →₀ ℤ)))

/-! ## Topology inputs -/

/-- **AREA CONDMV.** Mayer–Vietoris for free light condensed abelian groups on open covers. -/
def CondMVProp : Prop :=
  ∀ (X : TopCat.{0}) (U V : Set X), IsOpen U → IsOpen V → U ∪ V = Set.univ →
    Mono (freeLightCondAbOfTopFunctor.map (incl (Set.inter_subset_left : U ∩ V ⊆ U))) ∧
    IsPushout (freeLightCondAbOfTopFunctor.map (incl (Set.inter_subset_left : U ∩ V ⊆ U)))
      (freeLightCondAbOfTopFunctor.map (incl (Set.inter_subset_right : U ∩ V ⊆ V)))
      (freeLightCondAbOfTopFunctor.map (inclTop U)) (freeLightCondAbOfTopFunctor.map (inclTop V))

/-- **AREA SINGMV.** Mayer–Vietoris (small simplices) for singular chains on open covers:
the chains of `U` and `V` glued along `U ∩ V` compute the chains of `X`. -/
def SingMVProp : Prop :=
  ∀ (X : TopCat.{0}) (U V : Set X), IsOpen U → IsOpen V → U ∪ V = Set.univ →
    QuasiIso (pushout.desc (singC.map (inclTop U)) (singC.map (inclTop V))
      (by rw [← Functor.map_comp, ← Functor.map_comp]; rfl) :
        pushout (singC.map (incl (Set.inter_subset_left : U ∩ V ⊆ U)))
          (singC.map (incl (Set.inter_subset_right : U ∩ V ⊆ V))) ⟶ singC.obj X)

/-- Closure axioms for a class of Hausdorff spaces. -/
structure CWClosed (G : TopCat.{0} → Prop) : Prop where
  point : G (TopCat.of PUnit)
  empty : G (TopCat.of PEmpty)
  of_homotopyEquiv : ∀ (X Y : TopCat.{0}) [T2Space X] [T2Space Y],
    ContinuousMap.HomotopyEquiv X Y → G Y → G X
  sigma : ∀ (J : Type) (X : J → TopCat.{0}) [∀ j, T2Space (X j)], (∀ j, G (X j)) →
    G (TopCat.of (Σ j, X j))
  mv : ∀ (X : TopCat.{0}) [T2Space X] (U V : Set X), IsOpen U → IsOpen V → U ∪ V = Set.univ →
    G (TopCat.of U) → G (TopCat.of V) → G (TopCat.of (U ∩ V : Set X)) → G X
  exhaust : ∀ (X : TopCat.{0}) [T2Space X] (A : ℕ → Set X), Monotone A →
    (∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n) → (∀ n, G (TopCat.of (A n))) → G X

/-- **AREA CWTOP.** Every Hausdorff CW complex lies in every class satisfying `CWClosed`. -/
def CWTopProp : Prop :=
  ∀ G : TopCat.{0} → Prop, CWClosed G →
    ∀ (X : TopCat.{0}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)], G X

/-! ## Assembly of holes 10–11 -/

/-- **AREA CWIND (hole 10).** For any derived package, the natural comparison with singular
chains on Hausdorff CW complexes. -/
def CWIsoProp : Prop :=
  ∀ [isSolid.ι.IsRightAdjoint] (D : DerivedPackage),
    Nonempty (CWTopCat.toTopCat ⋙ freeLightCondAbOfTopFunctor ⋙
        DerivedCategory.singleFunctor LightCondAb 0 ⋙ D.L ⋙ derivedInclusion ≅
      singularChainsLightCondAbCWDerivedFunctor)

/-- **AREA HOMOL (hole 11 inputs).** Homology of singular chains and of the derived inclusion. -/
def HomologyProp : Prop :=
  (∀ (X : TopCat.{0}) (n : ℕ), Nonempty ((DerivedCategory.homologyFunctor LightCondAb (-(n : ℤ))).obj
      (singularChainsLightCondAbDerivedFunctor.obj X) ≅ singularHomologyLightCondAb X n)) ∧
    ∀ (K : DSolid) (k : ℤ), Nonempty (isSolid.ι.obj ((DerivedCategory.homologyFunctor Solid k).obj K) ≅
      (DerivedCategory.homologyFunctor LightCondAb k).obj (derivedInclusion.obj K))

/-! ## Composition (sanity check that the Props suffice) -/

/-- Holes 4–7 and 10–11 follow from the area Props. -/
theorem holes_of_areas (hR : ReflProp) (hD : DerivedProp) (hC : CWIsoProp) (hH : HomologyProp) :
    ∃ (_ : isSolid.ι.IsRightAdjoint) (D : DerivedPackage),
      Nonempty (CWTopCat.toTopCat ⋙ freeLightCondAbOfTopFunctor ⋙
        DerivedCategory.singleFunctor LightCondAb 0 ⋙ D.L ⋙ derivedInclusion ≅
          singularChainsLightCondAbCWDerivedFunctor) ∧
      ∀ (X : TopCat.{0}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)] (n : ℕ),
        Nonempty (isSolid.ι.obj ((DerivedCategory.homologyFunctor Solid (-(n : ℤ))).obj
          (D.L.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj
            (freeLightCondAbOfTop X)))) ≅ singularHomologyLightCondAb X n) := by
  let _ : isSolid.ι.IsRightAdjoint := hR
  obtain ⟨D⟩ := (hD).1
  obtain ⟨e⟩ := hC D
  refine ⟨hR, D, ⟨e⟩, ?_⟩
  intro X _ _ n
  let Xc : CWTopCat := ⟨X, inferInstance, ⟨inferInstance⟩⟩
  obtain ⟨h₂⟩ := hH.2 (D.L.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj
    (freeLightCondAbOfTop X))) (-(n : ℤ))
  obtain ⟨h₁⟩ := hH.1 X n
  exact ⟨h₂ ≪≫ (DerivedCategory.homologyFunctor LightCondAb (-(n : ℤ))).mapIso (e.app Xc) ≪≫ h₁⟩

end Submission.Blueprint
