import Mathlib
import Submission.Work.Serre.B1Rel.Model
import Submission.Work.Serre.ratPullbackComparison
import Submission.Work.Serre.ratSerrePairAssembly

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# From the model to the pair comparison of `p`

This file assembles the rational pair comparison of a Serre fibration `p : E → B` over a path
connected base out of

* the relative invariant `Work.Serre.B1Rel.RelGoodQ` at the top stage of the `b = 1` model
  (`Work.Serre.B1Rel.relGoodQ_model`),
* the base-change comparison `Work.Serre.RatPullbackComparison` (proved),
* the comparison `(Γ, {γ₀}) → (B, {b₀})` of the model (`Work.Serre.isIso_pairMapOfRat`, proved),

glued along the commutative square of the three pair maps (`pullbackSquareRat`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.B1Rel

noncomputable section

variable {B E : Type} [TopologicalSpace B] [TopologicalSpace E]

/-! ## Functoriality of the rational pair map -/

/-- Congruence of `Work.Serre.relChainsRPairMap` in the continuous map. -/
theorem relChainsRPairMap_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) {f f' : C(X, Y)} (h : f = f')
    (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f' A B) :
    Work.Serre.relChainsRPairMap A B f hf = Work.Serre.relChainsRPairMap A B f' hf' := by
  subst h
  exact congrArg (fun w => Work.Serre.relChainsRPairMap A B f w)
    (Subsingleton.elim hf hf')

/-- **Functoriality of `Work.Serre.relChainsRPairMap`** in a composite of continuous maps. -/
theorem relChainsRPairMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (A : Set X) (Bm : Set Y) (C : Set Z) (f : C(X, Y)) (g : C(Y, Z))
    (hf : Set.MapsTo f A Bm) (hg : Set.MapsTo g Bm C) (hgf : Set.MapsTo (g.comp f) A C) :
    Work.Serre.relChainsRPairMap A Bm f hf ≫ Work.Serre.relChainsRPairMap Bm C g hg
      = Work.Serre.relChainsRPairMap A C (g.comp f) hgf := by
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A))).1
  unfold Work.Serre.relChainsRPairMap
  rw [← Category.assoc, Work.Serre.cokernel_π_csrRelMapOf, Category.assoc,
    Work.Serre.cokernel_π_csrRelMapOf, ← Category.assoc,
    ← Work.Cohomology.chainMap_comp_relChains, Work.Serre.cokernel_π_csrRelMapOf]
  congr 2

/-- **The commutative square of the three rational pair maps.** -/
theorem pullbackSquareRat {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.Serre.pullbackPairMapRat g p γ₀ b₀ hbase ≫ Work.Serre.relPairMapRat p b₀
      = Work.Serre.stagePairMapRat g p γ₀ ≫ Work.Serre.pairMapOfRat g γ₀ b₀ hbase := by
  have hA : (Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)
      = ((Work.StemsB.pullbackFst g p) ⁻¹' {γ₀} : Set (Work.StemsB.Pullback g p)) := rfl
  set A : Set (Work.StemsB.Pullback g p) := (Work.StemsB.pullbackFst g p) ⁻¹' {γ₀} with hAdef
  have hps : Set.MapsTo (Work.StemsB.pullbackSnd g p) A (p ⁻¹' {b₀}) := by
    intro x hx
    have hx' : (Work.StemsB.pullbackFst g p) x = γ₀ := hx
    show p x.1.2 = b₀
    calc p x.1.2 = g ((Work.StemsB.pullbackFst g p) x) := x.2.symm
      _ = g γ₀ := by rw [hx']
      _ = b₀ := hbase
  have hpf : Set.MapsTo (Work.StemsB.pullbackFst g p) A ({γ₀} : Set Γ) := fun _ hx => hx
  have hgp : Set.MapsTo g ({γ₀} : Set Γ) ({b₀} : Set B) := by
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hbase
  have hp : Set.MapsTo p (p ⁻¹' {b₀}) ({b₀} : Set B) := fun _ hx => hx
  have hmaps1 : Set.MapsTo (p.comp (Work.StemsB.pullbackSnd g p)) A ({b₀} : Set B) := by
    intro x hx
    have hx' : (Work.StemsB.pullbackFst g p) x = γ₀ := hx
    show p (Work.StemsB.pullbackSnd g p x) = b₀
    calc p (Work.StemsB.pullbackSnd g p x) = g ((Work.StemsB.pullbackFst g p) x) := (x.2).symm
      _ = g γ₀ := by rw [hx']
      _ = b₀ := hbase
  have hmaps2 : Set.MapsTo (g.comp (Work.StemsB.pullbackFst g p)) A ({b₀} : Set B) := by
    intro x hx
    have hx' : (Work.StemsB.pullbackFst g p) x = γ₀ := hx
    show g ((Work.StemsB.pullbackFst g p) x) = b₀
    rw [hx']
    exact hbase
  have h1 : Work.Serre.pullbackPairMapRat g p γ₀ b₀ hbase ≫ Work.Serre.relPairMapRat p b₀
      = Work.Serre.relChainsRPairMap A ({b₀} : Set B) (p.comp (Work.StemsB.pullbackSnd g p))
          hmaps1 :=
    relChainsRPairMap_comp A (p ⁻¹' {b₀}) ({b₀} : Set B) (Work.StemsB.pullbackSnd g p) p
      hps hp hmaps1
  have h2 : Work.Serre.stagePairMapRat g p γ₀ ≫ Work.Serre.pairMapOfRat g γ₀ b₀ hbase
      = Work.Serre.relChainsRPairMap A ({b₀} : Set B) (g.comp (Work.StemsB.pullbackFst g p))
          hmaps2 :=
    relChainsRPairMap_comp A ({γ₀} : Set Γ) ({b₀} : Set B) (Work.StemsB.pullbackFst g p) g
      hpf hgp hmaps2
  rw [h1, h2]
  exact relChainsRPairMap_congr A ({b₀} : Set B) (Work.Serre.pullbackSnd_comp_eq g p)
    hmaps1 hmaps2

/-! ## The pair comparison of `p` -/

/-- **The pair comparison of a Serre fibration over a path connected base, in the rational stable
range `i < R`**, from the sharp fibre hypotheses: the fibres of `p` are rationally acyclic below
`φ` (`0 < j < φ`) and rationally connected, and `R ≤ φ + 1`. -/
theorem relPairMapRat_isIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B)
    [PathConnectedSpace B] (R φ : ℕ) (hRφ : R ≤ φ + 1)
    (hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j))
    (h0 : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ)) :
    ∀ i : ℕ, i < R → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b₀) i) := by
  set s := Work.Serre.E3aModel.towerB B b₀ (Work.Serre.E3aModel.baseState B b₀) (R + 1) with hs
  have hgbij : ∀ i : ℕ, i ≤ R → ∀ x : s.Y, Function.Bijective (Work.Serre.piMapN s.g i x) :=
    Work.Serre.E3aModel.towerB_piMapN_bijective B b₀ (Work.Serre.E3aModel.baseState B b₀) R
  have hmodel := relGoodQ_model p hp b₀ R φ hRφ hfib h0
  intro i hi
  haveI hpb : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.pullbackPairMapRat s.g p s.y₀ b₀ s.gbase) i) :=
    Work.Serre.ratPullbackComparison s.g p s.y₀ b₀ s.gbase hp R
      (fun k hk x => hgbij k hk x) i hi
  haveI hpm : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.pairMapOfRat s.g s.y₀ b₀ s.gbase) i) :=
    Work.Serre.isIso_pairMapOfRat b₀ s hgbij i hi
  haveI hst : IsIso (HomologicalComplex.homologyMap (Work.Serre.stagePairMapRat s.g p s.y₀) i) :=
    hmodel.1 i hi
  have hsq := congrArg (fun m => HomologicalComplex.homologyMap m i)
    (pullbackSquareRat s.g p s.y₀ b₀ s.gbase)
  simp only [HomologicalComplex.homologyMap_comp] at hsq
  haveI hcomp : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.pullbackPairMapRat s.g p s.y₀ b₀ s.gbase) i
      ≫ HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b₀) i) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap (Work.Serre.pullbackPairMapRat s.g p s.y₀ b₀ s.gbase) i)
    (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b₀) i)

end

end Work.Serre.B1Rel
