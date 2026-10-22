import Submission.Blueprint.Interfaces

/-!
# AREA DISC — discrete objects are solid; discrete free groups are projective

Vocabulary for the DISC area: the free light condensed abelian group `ℤ[S]` on a light
profinite set, the discrete light condensed abelian group `ΔM` on an abelian group `M`,
the "null sequence" model of the sections of `ΔM^P`, and the basic comparison isomorphisms
(`ℤ[S] ⊗ ℤ[T] ≅ ℤ[S ⊗ T]`, `Hom(ℤ[S], A) ≅ A(S)`).

Main deliverable: `Work.DISC.disc_prop` in `Submission/Work/DISC/Main.lean`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.DISC

/-! ## Basic objects -/

/-- The functor `S ↦ ℤ[S]` from light profinite sets to light condensed abelian groups. -/
abbrev zfreeFunctor : LightProfinite.{0} ⥤ LightCondAb :=
  lightProfiniteToLightCondSet ⋙ LightCondensed.free ℤ

/-- The free light condensed abelian group `ℤ[S]` on a light profinite set `S`. -/
abbrev zfree (S : LightProfinite.{0}) : LightCondAb := zfreeFunctor.obj S

/-- The discrete light condensed abelian group `ΔM` on an abelian group `M`. -/
abbrev disc (M : ModuleCat.{0} ℤ) : LightCondAb :=
  (LightCondensed.discrete (ModuleCat ℤ)).obj M

/-- The internal hom `A^P = ihom P A`, where `P = ℤ[ℕ∪{∞}]/ℤ[∞]`. -/
abbrev ihomP (A : LightCondAb) : LightCondAb := (CategoryTheory.ihom (C := LightCondAb) P).obj A

/-- The endomorphism `(1 - shift)^*` of `A^P` whose invertibility defines solidity. -/
abbrev oneMinusShiftStar (A : LightCondAb) : ihomP A ⟶ ihomP A :=
  (MonoidalClosed.pre oneMinusShift).app A

/-! ## The space `S × (ℕ∪{∞})` and the shift -/

/-- The map `S × (ℕ∪{∞}) → S × (ℕ∪{∞})`, `(s,n) ↦ (s, n+1)`, `(s,∞) ↦ (s,∞)`. -/
def shiftProd (S : LightProfinite.{0}) : C(↥S × ↥(ℕ∪{∞}), ↥S × ↥(ℕ∪{∞})) where
  toFun x := (x.1, LightProfinite.shift x.2)
  continuous_toFun := by fun_prop

@[simp]
lemma shiftProd_apply (S : LightProfinite.{0}) (x : ↥S × ↥(ℕ∪{∞})) :
    shiftProd S x = (x.1, LightProfinite.shift x.2) := rfl

@[simp]
lemma shiftProd_infty (S : LightProfinite.{0}) (s : ↥S) :
    shiftProd S (s, ∞) = (s, ∞) := by
  rw [shiftProd_apply, Prod.mk.injEq]
  exact ⟨rfl, rfl⟩

/-- The "shift-difference" map `f ↦ f - f ∘ (id × shift)` on locally constant functions. -/
def shiftDiffLC (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ)
    (f : LocallyConstant (↥S × ↥(ℕ∪{∞})) ↥M) : LocallyConstant (↥S × ↥(ℕ∪{∞})) ↥M :=
  f - LocallyConstant.comap (shiftProd S) f

/-- Locally constant functions on `S × (ℕ∪{∞})` which vanish on `S × {∞}`. -/
def Vanishing (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) : Type :=
  {f : LocallyConstant (↥S × ↥(ℕ∪{∞})) ↥M // ∀ s : ↥S, f (s, ∞) = 0}

namespace Vanishing

variable {S : LightProfinite.{0}} {M : ModuleCat.{0} ℤ}

/-- The shift-difference map `f ↦ f - f ∘ (id × shift)` on `Vanishing S M`. -/
def shiftDiff (f : Vanishing S M) : Vanishing S M :=
  ⟨shiftDiffLC S M f.1, by
    intro s
    change f.1 (s, ∞) - f.1 (shiftProd S (s, ∞)) = 0
    rw [shiftProd_infty, f.2 s, sub_zero]⟩

@[simp]
lemma shiftDiff_val (f : Vanishing S M) : (shiftDiff f).1 = shiftDiffLC S M f.1 := rfl

end Vanishing

/-! ## Null sequences -/

/-- The type of *null sequences* in a discrete abelian group `M` over a light profinite set `S`:
sequences of locally constant maps `S → M` that are eventually zero. -/
def NullSeq (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) : Type :=
  {a : ℕ → LocallyConstant ↥S ↥M // ∃ N, ∀ n ≥ N, a n = 0}

namespace NullSeq

variable {S : LightProfinite.{0}} {M : ModuleCat.{0} ℤ}

/-- The difference of consecutive terms `(a_n) ↦ (a_n - a_{n+1})`. -/
def diff (a : NullSeq S M) : NullSeq S M :=
  ⟨fun n => a.1 n - a.1 (n + 1), by
    obtain ⟨N, hN⟩ := a.2
    exact ⟨N, fun n hn => by
      rw [sub_eq_zero]
      exact (hN n hn).trans (hN (n + 1) (by omega)).symm⟩⟩

/-- A chosen vanishing bound of a null sequence. -/
def bound (a : NullSeq S M) : ℕ := Classical.choose a.2

lemma bound_spec (a : NullSeq S M) : ∀ n ≥ a.bound, a.1 n = 0 := Classical.choose_spec a.2

/-- The inverse of the difference map: `(b_n) ↦ (Σ_{k < N} b_{n+k})`. -/
def tailSum (b : NullSeq S M) : NullSeq S M :=
  ⟨fun n => ∑ k ∈ Finset.range b.bound, b.1 (n + k), by
    refine ⟨b.bound, fun n hn => Finset.sum_eq_zero fun k hk => ?_⟩
    exact b.bound_spec (n + k) (by have := Finset.mem_range.mp hk; omega)⟩

end NullSeq

/-! ## Basic comparison isomorphisms -/

/-- `ℤ[S] ⊗ ℤ[T] ≅ ℤ[S ⊗ T]`: the free functor is monoidal. -/
def freeTensorIso (S T : LightProfinite.{0}) : zfree S ⊗ zfree T ≅ zfree (S ⊗ T) :=
  Functor.Monoidal.μIso (LightCondensed.free ℤ) S.toCondensed T.toCondensed ≪≫
    (LightCondensed.free ℤ).mapIso (Functor.Monoidal.μIso lightProfiniteToLightCondSet S T)

/-- `Hom(ℤ[S], A) ≅ A(S)`, by the free-forget adjunction and Yoneda. -/
def homFreeEquiv (S : LightProfinite.{0}) (A : LightCondAb) :
    (zfree S ⟶ A) ≃ ↥(A.obj.obj (op S)) :=
  ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed A).trans
    ((coherentTopology LightProfinite).yonedaEquiv)

end Work.DISC
