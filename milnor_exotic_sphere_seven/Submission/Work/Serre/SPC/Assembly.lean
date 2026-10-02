import Mathlib
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Serre.SPC.Square
import Submission.Work.Serre.SPC.pullbackPairComparison
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.Assembly.pairMapOf_isIso
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.RatHurewicz.ConnectivityBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Assembly of `Work.Serre.serrePairComparison` from the pieces

This file assembles the pair comparison of the Serre exact sequence in the stable range from

* the CW model of the base (`Work.Serre.CWModel.towerA`) and its homotopy properties,
* the tower comparison (`Work.Serre.SPC.towerComparison`),
* the two comparison theorems `Work.Serre.CWModel.pairMapOf` / `pullbackPairMap`
  (`Work.Serre.Assembly.pairMapOf_isIso`, `Work.Serre.SPC.pullbackPairComparison`),
* the `b = 1` case (`Work.Serre.SPC.b1Comparison`).

The main point of the assembly is the *one degree of slack*: with the model's `π`-bijectivity
available up to degree `b + f + 1`, the two comparison theorems are isomorphisms up to degree
`b + f` (hence surjective there), while the tower comparison is an isomorphism below `b + f` and
surjective at `b + f`; composing them along the commutative square of the pullback displays
`relPairMap p b₀` as an isomorphism below `b + f` and an epimorphism at `b + f`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

open Work.Serre.CWModel

/-- **The homotopy groups of the model tower's top stage.**  For a `(b-1)`-connected `B` (`b ≥ 2`)
and any `N`, the structure map `g` of the stage `Work.Serre.CWModel.towerA B b₀ b hb hconn (N+2)`
induces a bijection on `π_i` for every `i ≤ N` at *every* base point. -/
theorem towerA_piMapN_bijective {B : Type} [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) (N : ℕ) :
    ∀ i : ℕ, i ≤ N → ∀ x : (towerA B b₀ b hb hconn (N + 2)).Y,
      Function.Bijective (Work.Serre.piMapN (towerA B b₀ b hb hconn (N + 2)).g i x) := by
  set s := towerA B b₀ b hb hconn (N + 2) with hs
  haveI hΓ : PathConnectedSpace s.Y := s.conn
  haveI hZΓ : Subsingleton (ZerothHomotopy s.Y) :=
    ⟨fun a c => by
      obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
      obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective c
      obtain ⟨γ⟩ := PathConnectedSpace.joined x y
      exact ZerothHomotopy.sound γ⟩
  haveI hZB : Subsingleton (ZerothHomotopy B) := by
    haveI h := hconn 0 (by omega)
    refine ⟨fun a c => ?_⟩
    exact (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := b₀)).symm.injective
      (Subsingleton.elim _ _)
  intro i hi x
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    haveI h1 : Subsingleton (HomotopyGroup (Fin 0) s.Y x) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := s.Y) (x := x)).injective.subsingleton
    haveI h2 : Subsingleton (HomotopyGroup (Fin 0) B (s.g x)) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := s.g x)).injective.subsingleton
    exact ⟨fun a c _ => h1.elim a c, fun y => ⟨default, h2.elim _ _⟩⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact Work.Serre.bijective_piMapN_of_joined s.g (PathConnectedSpace.joined s.y₀ x) (j + 1)
      (s.bij j (by omega))

/-! ## The assembly of the target

The pair comparison `(E, p⁻¹b₀) → (B, {b₀})` is put between the two comparison theorems of the
pullback square and the pullback comparison, with *one degree of slack*: if the base comparison
`g : Γ → B` is a `π`-bijection up to degree `b + f + 1`, then both `pairMapOf g` and
`pullbackPairMap g p` are isomorphisms up to degree `b + f`, while the pullback pair comparison of
`g` is an isomorphism below `b + f` and surjective at `b + f`.  The square then displays
`relPairMap p b₀` as the composite of an isomorphism with these two maps, which gives the
isomorphism statement below `b + f` and the surjectivity statement at `b + f`.
-/

/-- **Solving a commutative square for the fourth map.**  In any category, if `f` is invertible and
`f ≫ r = g ≫ h`, then `r = f⁻¹ ≫ (g ≫ h)`. -/
theorem eq_inv_comp_of_comp_eq {C : Type*} [Category C] {X Y Z W : C}
    (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) (r : Y ⟶ W) [IsIso f]
    (hsq : f ≫ r = g ≫ h) : r = inv f ≫ (g ≫ h) := by
  calc r = 𝟙 Y ≫ r := (Category.id_comp r).symm
    _ = (inv f ≫ f) ≫ r := by rw [IsIso.inv_hom_id]
    _ = inv f ≫ (f ≫ r) := Category.assoc _ _ _
    _ = inv f ≫ (g ≫ h) := by rw [hsq]

/-- **The pair comparison of a Serre fibration from a comparison of the base with one degree of
slack.**

Let `p : E → B` be a Serre fibration, `b₀ ∈ B`, and let `g : Γ → B` be a map from a path-connected
space `Γ` which is a `π`-bijection in every degree `≤ b + f + 1` at every base point.  If the pair
comparison of the pullback of `p` along `g`,

`(Γ ×_B E, q⁻¹γ₀) → (Γ, {γ₀})`,

is an isomorphism on integral homology in degrees `< b + f` and surjective in degree `b + f`, then
the pair comparison `(E, p⁻¹b₀) → (B, {b₀})` is an isomorphism in degrees `< b + f` and
surjective in degree `b + f`. -/
theorem serrePairComparison_of {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    (g : C(Γ, B)) (γ₀ : Γ) (hbase : g γ₀ = b₀) (b f : ℕ)
    (hΓ : PathConnectedSpace Γ) (hB : PathConnectedSpace B)
    (hg : ∀ i : ℕ, i ≤ b + f + 1 → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x))
    (htow : (∀ i : ℕ, i < b + f → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) i)) ∧
      Function.Surjective (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) (b + f)).hom) :
    (∀ i : ℕ, i < b + f → CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)) ∧
      Function.Surjective
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) (b + f)).hom := by
  -- The two comparison theorems of the pullback square, with one degree of slack.
  have hpb := Work.Serre.SPC.pullbackPairComparison g p γ₀ b₀ hbase hp (b + f + 1) hΓ hB hg
  have hbs := Work.Serre.Assembly.pairMapOf_isIso g γ₀ b₀ hbase (b + f + 1) hΓ hB hg
  constructor
  · intro i hi
    haveI hisoP : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase) i) := hpb i (by omega)
    haveI hisoM : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) i) := htow.1 i hi
    haveI hisoT : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase) i) := hbs i (by omega)
    rw [eq_inv_comp_of_comp_eq
      (HomologicalComplex.homologyMap (Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase) i)
      (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) i)
      (HomologicalComplex.homologyMap (Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase) i)
      (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)
      (pullbackSquare_homology g p γ₀ b₀ hbase i)]
    infer_instance
  · have hEp : CategoryTheory.Epi (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) (b + f)) :=
      (ModuleCat.epi_iff_surjective _).mpr htow.2
    haveI hisoP : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase) (b + f)) := hpb (b + f) (by omega)
    haveI hisoM : CategoryTheory.Epi (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) (b + f)) := hEp
    haveI hisoT : CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase) (b + f)) := hbs (b + f) (by omega)
    rw [eq_inv_comp_of_comp_eq
      (HomologicalComplex.homologyMap
        (Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase) (b + f))
      (HomologicalComplex.homologyMap
        (Work.StemsB.relPairMap (Work.StemsB.pullbackFst g p) γ₀) (b + f))
      (HomologicalComplex.homologyMap (Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase) (b + f))
      (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) (b + f))
      (pullbackSquare_homology g p γ₀ b₀ hbase (b + f))]
    exact (ModuleCat.epi_iff_surjective _).mp (by infer_instance)

end

end Work.Serre.SPC
