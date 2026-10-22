/-
# AREA CONDMV — `X_cond` is the colimit of an open exhaustion

For an increasing sequence `A : ℕ → Set X` of subsets of a topological space `X` such that every
compact subset of `X` is contained in some `A n`, the light condensed set `X_cond` is the colimit
of the light condensed sets `(A n)_cond`.

The proof is a direct verification of the universal property of the colimit.  Given a cocone `c`
with point `Z`, the map `X_cond ⟶ Z` is constructed as follows: a section of `X_cond` over a light
profinite set `S` is a continuous map `f : S → X`; since `S` is compact, the image of `f` is
compact, hence contained in some `A n` (this is where `hex` is used).  Lifting `f` along
`A n ⊆ X` and applying `c_n` produces a section of `Z` over `S`.  The construction is independent
of the choice of `n` by the compatibility of the cocone maps, and it is natural in `S`.

Uniqueness is immediate from the componentwise description of composition of morphisms of sheaves.

Note that this is exactly the place where the compactness condition `hex` replaces the missing
statement "`X_cond` is the colimit of its compact subspaces": no clopen partitions are needed,
since a continuous image of a compact light profinite set lies in a single `A n`.
-/
import Submission.Work.CONDMV.Pushout
import Submission.Work.CONDMV.ExhaustSetup

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.CONDMV.Exhaust

variable {X : TopCat.{0}}

/-! ## Index bookkeeping -/

/-- The morphism `m ⟶ n` of the preorder `ℕ`, used for the exhaustion diagram. -/
def natHom {m n : ℕ} (h : m ≤ n) : m ⟶ n := ULift.up (PLift.up h)

lemma leOfHom_natHom {m n : ℕ} (h : m ≤ n) : leOfHom (natHom h) = h := rfl

/-- `n` is large enough for a section `f : S → X` if the image of `f` lies in `A n`. -/
def Good (A : ℕ → Set X) (n : ℕ) (S : LightProfinite.{0}) (f : C(↥S, ↥X)) : Prop :=
  ∀ a : ↥S, f a ∈ A n

lemma good_exists (A : ℕ → Set X) (hex : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n)
    (S : LightProfinite.{0}) (f : C(↥S, ↥X)) : ∃ n, Good A n S f := by
  obtain ⟨n, hn⟩ := hex (Set.range f) (isCompact_range f.continuous)
  exact ⟨n, fun a => hn ⟨a, rfl⟩⟩

/-- A large enough index for a section, chosen classically. -/
noncomputable def goodIndex (A : ℕ → Set X) (hex : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n)
    (S : LightProfinite.{0}) (f : C(↥S, ↥X)) : ℕ :=
  Classical.choose (good_exists A hex S f)

lemma goodIndex_spec (A : ℕ → Set X) (hex : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n)
    (S : LightProfinite.{0}) (f : C(↥S, ↥X)) : Good A (goodIndex A hex S f) S f :=
  Classical.choose_spec (good_exists A hex S f)

/-! ## The section of the cocone point induced by a section of `X_cond` -/

section Section

variable (A : ℕ → Set X) (hmono : Monotone A) (hex : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n)

/-- The lift of a section whose image lies in `A n`, as a continuous map to `A n`. -/
def lift' (S : LightProfinite.{0}) (f : C(↥S, ↥X)) (n : ℕ) (h : Good A n S f) :
    C(↥S, ↥(A n)) :=
  ⟨fun a => ⟨f a, h a⟩, f.continuous.subtype_mk h⟩

lemma lift'_congr {S : LightProfinite.{0}} {f : C(↥S, ↥X)} {n : ℕ} (h₁ h₂ : Good A n S f) :
    lift' A S f n h₁ = lift' A S f n h₂ := by
  apply ContinuousMap.ext
  intro a
  exact Subtype.ext rfl

/-- The component of the exhaustion cocone on sections is postcomposition with the inclusion. -/
lemma exhaustCocone_ι_app (n : ℕ) (S : LightProfinite.{0})
    (x : (setCond (A n)).obj.obj (op S)) :
    (ConcreteCategory.hom (((exhaustCocone A hmono).ι.app n).hom.app (op S))) x
      = (Submission.Blueprint.inclTop (A n)).hom.comp (asUMap (A n) x) := rfl

lemma inclTop_comp_lift' (S : LightProfinite.{0}) (f : C(↥S, ↥X)) (n : ℕ)
    (h : Good A n S f) :
    (Submission.Blueprint.inclTop (A n)).hom.comp (lift' A S f n h) = f := by
  apply ContinuousMap.ext
  intro a
  rfl

/-- The lift of a section which is already a map into `A n`. -/
lemma lift'_comp_inclTop (S : LightProfinite.{0}) (n : ℕ) (x : C(↥S, ↥(A n))) :
    lift' A S ((Submission.Blueprint.inclTop (A n)).hom.comp x) n (fun a => (x a).2) = x := by
  apply ContinuousMap.ext
  intro a
  exact Subtype.ext rfl

/-- The component of the exhaustion diagram at `n` is postcomposition with the inclusion. -/
lemma exhaustFunctor_map_app (S : LightProfinite.{0}) {m n : ℕ} (h : m ≤ n)
    (g : C(↥S, ↥(A m))) :
    ((exhaustFunctor A hmono).map (natHom h)).hom.app (op S) g
      = (Submission.Blueprint.incl (hmono h)).hom.comp g := rfl

lemma exhaustFunctor_map_lift' (S : LightProfinite.{0}) {m n : ℕ} (h : m ≤ n)
    (f : C(↥S, ↥X)) (hm : Good A m S f) :
    ((exhaustFunctor A hmono).map (natHom h)).hom.app (op S) (lift' A S f m hm)
      = lift' A S f n (fun a => hmono h (hm a)) := by
  change (Submission.Blueprint.incl (hmono h)).hom.comp (lift' A S f m hm)
    = lift' A S f n (fun a => hmono h (hm a))
  apply ContinuousMap.ext
  intro a
  rfl

/-- The cocone condition, in terms of the lifts of a fixed section. -/
lemma cocone_step (s : Cocone (exhaustFunctor A hmono)) (S : LightProfinite.{0})
    (f : C(↥S, ↥X)) {m n : ℕ} (h : m ≤ n) (hm : Good A m S f) :
    (s.ι.app m).hom.app (op S) (lift' A S f m hm)
      = (s.ι.app n).hom.app (op S) (lift' A S f n (fun a => hmono h (hm a))) := by
  have hnm : (exhaustFunctor A hmono).map (natHom h) ≫ s.ι.app n = s.ι.app m := by
    have hnat := CategoryTheory.NatTrans.naturality s.ι (natHom h)
    simp only [CategoryTheory.Functor.const_obj_map] at hnat
    exact hnat
  calc (s.ι.app m).hom.app (op S) (lift' A S f m hm)
      = ((exhaustFunctor A hmono).map (natHom h) ≫ s.ι.app n).hom.app (op S)
          (lift' A S f m hm) := by rw [hnm]
    _ = (s.ι.app n).hom.app (op S)
          (((exhaustFunctor A hmono).map (natHom h)).hom.app (op S)
            (lift' A S f m hm)) := rfl
    _ = (s.ι.app n).hom.app (op S) (lift' A S f n (fun a => hmono h (hm a))) := by
          rw [exhaustFunctor_map_lift']

/-- Two large enough indices give the same value. -/
lemma descVal_comp (s : Cocone (exhaustFunctor A hmono)) (S : LightProfinite.{0})
    (f : C(↥S, ↥X)) {m n : ℕ} (hm : Good A m S f) (hn : Good A n S f) :
    (s.ι.app m).hom.app (op S) (lift' A S f m hm)
      = (s.ι.app n).hom.app (op S) (lift' A S f n hn) := by
  rw [cocone_step A hmono s S f (le_max_left m n) hm,
    cocone_step A hmono s S f (le_max_right m n) hn]

/-- The section of the cocone point over `S` induced by a section `f : S → X`. -/
noncomputable def descApp (s : Cocone (exhaustFunctor A hmono)) (S : LightProfinite.{0})
    (f : C(↥S, ↥X)) : s.pt.obj.obj (op S) :=
  (s.ι.app (goodIndex A hex S f)).hom.app (op S)
    (lift' A S f (goodIndex A hex S f) (goodIndex_spec A hex S f))

/-- `descApp` only depends on the section, not on the chosen large enough index. -/
lemma descApp_eq (s : Cocone (exhaustFunctor A hmono)) (S : LightProfinite.{0})
    (f : C(↥S, ↥X)) {n : ℕ} (hn : Good A n S f) :
    descApp A hmono hex s S f = (s.ι.app n).hom.app (op S) (lift' A S f n hn) :=
  descVal_comp A hmono s S f (goodIndex_spec A hex S f) hn

/-- `descApp` applied to a section coming from `(A n)_cond` is the cocone map. -/
lemma descApp_leg (s : Cocone (exhaustFunctor A hmono)) (n : ℕ) (S : LightProfinite.{0})
    (x : (setCond (A n)).obj.obj (op S)) :
    descApp A hmono hex s S
        ((Submission.Blueprint.inclTop (A n)).hom.comp (asUMap (A n) x))
      = (s.ι.app n).hom.app (op S) x := by
  rw [descApp_eq A hmono hex s S
    ((Submission.Blueprint.inclTop (A n)).hom.comp (asUMap (A n) x))
    (n := n) (hn := fun a => (asUMap (A n) x a).2)]
  rw [lift'_comp_inclTop]
  rfl

/-- Naturality of the cocone legs. -/
lemma cocone_natural (s : Cocone (exhaustFunctor A hmono)) (n : ℕ)
    {S₀ S₁ : LightProfinite.{0}} (k : S₀ ⟶ S₁) (y : (setCond (A n)).obj.obj (op S₁)) :
    s.pt.obj.map k.op ((s.ι.app n).hom.app (op S₁) y)
      = (s.ι.app n).hom.app (op S₀) ((setCond (A n)).obj.map k.op y) :=
  (CategoryTheory.NatTrans.naturality_apply (s.ι.app n).hom k.op y).symm

/-- Precomposition of a lifted section along a map of light profinite sets. -/
lemma setCond_map_lift' (S₀ S₁ : LightProfinite.{0}) (k : S₀ ⟶ S₁) (f : C(↥S₁, ↥X))
    (n : ℕ) (hn : Good A n S₁ f) :
    ((setCond (A n)).obj.map k.op (lift' A S₁ f n hn) : C(↥S₀, ↥(A n)))
      = lift' A S₀ ((condOf X).obj.map k.op f) n (fun a => hn (k a)) := by
  apply ContinuousMap.ext
  intro a
  exact Subtype.ext rfl

/-- Naturality of `descApp`. -/
lemma descApp_natural (s : Cocone (exhaustFunctor A hmono)) {S₀ S₁ : LightProfinite.{0}}
    (k : S₀ ⟶ S₁) (f : C(↥S₁, ↥X)) :
    s.pt.obj.map k.op (descApp A hmono hex s S₁ f)
      = descApp A hmono hex s S₀ ((condOf X).obj.map k.op f) := by
  rw [descApp_eq A hmono hex s S₁ f (goodIndex_spec A hex S₁ f)]
  rw [cocone_natural A hmono s (goodIndex A hex S₁ f) k
    (lift' A S₁ f (goodIndex A hex S₁ f) (goodIndex_spec A hex S₁ f))]
  rw [descApp_eq A hmono hex s S₀ ((condOf X).obj.map k.op f)
    (n := goodIndex A hex S₁ f) (hn := fun a => goodIndex_spec A hex S₁ f (k a))]
  rw [setCond_map_lift' A S₀ S₁ k f (goodIndex A hex S₁ f)
    (goodIndex_spec A hex S₁ f)]

/-- The natural transformation whose components are the sections `descApp`. -/
noncomputable def descNatTrans (s : Cocone (exhaustFunctor A hmono)) :
    (condOf X).obj ⟶ s.pt.obj where
  app S := ↾fun f => descApp A hmono hex s (unop S) (asCMap f)
  naturality S T g := by
    ext f
    exact (descApp_natural A hmono hex s (unop g) (asCMap f)).symm

/-- The morphism `X_cond ⟶ Z` induced by a cocone with point `Z`. -/
noncomputable def desc (s : Cocone (exhaustFunctor A hmono)) : condOf X ⟶ s.pt :=
  Sheaf.homEquiv.symm (descNatTrans A hmono hex s)

lemma desc_hom (s : Cocone (exhaustFunctor A hmono)) :
    (desc A hmono hex s).hom = descNatTrans A hmono hex s := rfl

@[simp]
lemma desc_apply (s : Cocone (exhaustFunctor A hmono)) (S : LightProfinite.{0})
    (f : (condOf X).obj.obj (op S)) :
    (desc A hmono hex s).hom.app (op S) f = descApp A hmono hex s S (asCMap f) := rfl

/-- The defining property of the induced morphism. -/
lemma desc_fac (s : Cocone (exhaustFunctor A hmono)) (n : ℕ) :
    (exhaustCocone A hmono).ι.app n ≫ desc A hmono hex s = s.ι.app n := by
  apply LightCondensed.hom_ext
  intro S
  cases S with
  | op T =>
    ext x
    show descApp A hmono hex s T
        ((Submission.Blueprint.inclTop (A n)).hom.comp (asUMap (A n) x))
      = (s.ι.app n).hom.app (op T) x
    exact descApp_leg A hmono hex s n T x

/-- Uniqueness of the induced morphism. -/
lemma desc_uniq (s : Cocone (exhaustFunctor A hmono)) (m : condOf X ⟶ s.pt)
    (hm : ∀ n, (exhaustCocone A hmono).ι.app n ≫ m = s.ι.app n) :
    m = desc A hmono hex s := by
  apply LightCondensed.hom_ext
  intro S
  cases S with
  | op T =>
    ext f
    show (ConcreteCategory.hom (m.hom.app (op T))) f
      = (ConcreteCategory.hom ((desc A hmono hex s).hom.app (op T))) f
    rw [desc_apply]
    have hn : Good A (goodIndex A hex T (asCMap f)) T (asCMap f) :=
      goodIndex_spec A hex T (asCMap f)
    have hleg : (ConcreteCategory.hom
          (((exhaustCocone A hmono).ι.app (goodIndex A hex T (asCMap f))).hom.app (op T)))
        (lift' A T (asCMap f) (goodIndex A hex T (asCMap f)) hn) = f := by
      rw [exhaustCocone_ι_app A hmono (goodIndex A hex T (asCMap f)) T
        (lift' A T (asCMap f) (goodIndex A hex T (asCMap f)) hn)]
      exact inclTop_comp_lift' A T (asCMap f) (goodIndex A hex T (asCMap f)) hn
    calc (ConcreteCategory.hom (m.hom.app (op T))) f
        = (ConcreteCategory.hom (m.hom.app (op T)))
            ((ConcreteCategory.hom
              (((exhaustCocone A hmono).ι.app (goodIndex A hex T (asCMap f))).hom.app
                (op T)))
              (lift' A T (asCMap f) (goodIndex A hex T (asCMap f)) hn)) :=
          congrArg (fun z => (ConcreteCategory.hom (m.hom.app (op T))) z) hleg.symm
      _ = ((exhaustCocone A hmono).ι.app (goodIndex A hex T (asCMap f)) ≫ m).hom.app (op T)
            (lift' A T (asCMap f) (goodIndex A hex T (asCMap f)) hn) := rfl
      _ = (s.ι.app (goodIndex A hex T (asCMap f))).hom.app (op T)
            (lift' A T (asCMap f) (goodIndex A hex T (asCMap f)) hn) := by
            rw [hm (goodIndex A hex T (asCMap f))]
      _ = descApp A hmono hex s T (asCMap f) :=
            (descApp_eq A hmono hex s T (asCMap f) hn).symm

/-- The exhaustion cocone is a colimit cocone. -/
noncomputable def exhaustIsColimit : IsColimit (exhaustCocone A hmono) :=
  IsColimit.mk (fun s => desc A hmono hex s)
    (fun s n => desc_fac A hmono hex s n)
    (fun s m hm => desc_uniq A hmono hex s m hm)

end Section

theorem isColimit_exhaustCocone {X : TopCat.{0}} (A : ℕ → Set X) (hmono : Monotone A)
    (hex : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n) :
    Nonempty (CategoryTheory.Limits.IsColimit (Work.CONDMV.exhaustCocone A hmono)) :=
  ⟨exhaustIsColimit A hmono hex⟩

end Work.CONDMV.Exhaust
