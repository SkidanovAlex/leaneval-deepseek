import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSSR.Statements
import Submission.Work.SSSR.StemsB.SerreFiltration
import Submission.Work.SSSR.Cohomology.Chains
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped Topology
namespace Work.SSSR

noncomputable section

/-- The singular simplicial set of `E`. -/
abbrev sE (E : Type) [TopologicalSpace E] : SSet := TopCat.toSSet.obj (TopCat.of E)

/-- The map of singular simplicial sets induced by a continuous map. -/
def sSingMap {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    sE E ⟶ sE B :=
  TopCat.toSSet.map (TopCat.ofHom p)

/-- The singular chain complex of a simplicial set, with `ℤ` coefficients. -/
abbrev sChain (X : SSet) : ChainComplex (ModuleCat R) ℕ :=
  ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X



/-- The `s`-th term of the (shifted) Serre filtration: the preimage of the `(s+1)`-skeleton. -/
abbrev serreSub {X Y : SSet} (f : X ⟶ Y) (s : ℕ) : X.Subcomplex :=
  Work.SSSR.StemsB.serreSubcomplex f (s + 1)

/-- The (shifted) Serre filtration of a simplicial set along a morphism `f`: the `s`-th term is
the preimage of the `(s+1)`-skeleton. -/
abbrev serreFiltShift {X Y : SSet} (f : X ⟶ Y) : ℕ ⥤ SSet where
  obj s := (serreSub f s).toSSet
  map {s t} h := (serreSub f s).homOfLE (Work.SSSR.StemsB.serreSubcomplex_mono f
    (Nat.succ_le_succ (leOfHom h)))
  map_id P := SSet.Subcomplex.homOfLE_refl _
  map_comp h₁ h₂ := by rw [SSet.Subcomplex.homOfLE_comp]

variable {X Y : SSet} {g : X ⟶ Y}

/-- The degreewise component of the chain map induced by a degreewise injective morphism of
simplicial sets is a monomorphism. -/
theorem mono_chainComplexMap_f (n : ℕ)
    (hg : Function.Injective (g.app (Opposite.op (SimplexCategory.mk n)))) :
    Mono ((SSet.chainComplexMap g (ModuleCat.of R R)).f n) := by
  classical
  have hsplit : ∃ s : (Y.chainComplex (ModuleCat.of R R)).X n ⟶
      (X.chainComplex (ModuleCat.of R R)).X n,
      (SSet.chainComplexMap g (ModuleCat.of R R)).f n ≫ s = 𝟙 _ := by
    let s : (Y.chainComplex (ModuleCat.of R R)).X n ⟶ (X.chainComplex (ModuleCat.of R R)).X n :=
      Cofan.IsColimit.desc (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n)
        (fun y => if h : ∃ x : X _⦋n⦌, g.app (Opposite.op (SimplexCategory.mk n)) x = y
          then X.ιChainComplex (Classical.choose h) else 0)
    refine ⟨s, ?_⟩
    apply X.chainComplex_hom_ext
    intro x
    have hassoc : X.ιChainComplex x ≫ (SSet.chainComplexMap g (ModuleCat.of R R)).f n ≫ s =
        (X.ιChainComplex x ≫ (SSet.chainComplexMap g (ModuleCat.of R R)).f n) ≫ s :=
      (Category.assoc _ _ _).symm
    rw [hassoc, SSet.ι_chainComplexMap_f]
    have hfac : Y.ιChainComplex (g.app (Opposite.op (SimplexCategory.mk n)) x) ≫ s =
        (if h : ∃ x' : X _⦋n⦌, g.app (Opposite.op (SimplexCategory.mk n)) x' =
            g.app (Opposite.op (SimplexCategory.mk n)) x
          then X.ιChainComplex (Classical.choose h) else 0) :=
      Cofan.IsColimit.fac (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n) _ _
    rw [hfac, dif_pos ⟨x, rfl⟩]
    congr 1
    exact (hg) (Classical.choose_spec (show ∃ x' : X _⦋n⦌,
      g.app (Opposite.op (SimplexCategory.mk n)) x' = g.app (Opposite.op (SimplexCategory.mk n)) x
        from ⟨x, rfl⟩))
  obtain ⟨s, hs⟩ := hsplit
  haveI : IsSplitMono ((SSet.chainComplexMap g (ModuleCat.of R R)).f n) := ⟨s, hs⟩
  exact inferInstance

/-- The degreewise component of the chain map induced by a degreewise surjective morphism of
simplicial sets is an epimorphism. -/
theorem epi_chainComplexMap_f (n : ℕ)
    (hg : Function.Surjective (g.app (Opposite.op (SimplexCategory.mk n)))) :
    Epi ((SSet.chainComplexMap g (ModuleCat.of R R)).f n) := by
  classical
  have hsplit : ∃ s : (Y.chainComplex (ModuleCat.of R R)).X n ⟶
      (X.chainComplex (ModuleCat.of R R)).X n,
      s ≫ (SSet.chainComplexMap g (ModuleCat.of R R)).f n = 𝟙 _ := by
    let s : (Y.chainComplex (ModuleCat.of R R)).X n ⟶
        (X.chainComplex (ModuleCat.of R R)).X n :=
      Cofan.IsColimit.desc (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n)
        (fun y => X.ιChainComplex (Classical.choose (hg y)))
    refine ⟨s, ?_⟩
    apply Y.chainComplex_hom_ext
    intro y
    have hassoc : Y.ιChainComplex y ≫ s ≫ (SSet.chainComplexMap g (ModuleCat.of R R)).f n =
        (Y.ιChainComplex y ≫ s) ≫ (SSet.chainComplexMap g (ModuleCat.of R R)).f n :=
      (Category.assoc _ _ _).symm
    rw [hassoc]
    have hfac : Y.ιChainComplex y ≫ s = X.ιChainComplex (Classical.choose (hg y)) :=
      Cofan.IsColimit.fac (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n) _ _
    rw [hfac, SSet.ι_chainComplexMap_f, Category.comp_id]
    exact congrArg Y.ιChainComplex (Classical.choose_spec (hg y))
  obtain ⟨s, hs⟩ := hsplit
  haveI : IsSplitEpi ((SSet.chainComplexMap g (ModuleCat.of R R)).f n) := ⟨s, hs⟩
  exact inferInstance

/-- The chain map induced by a degreewise injective morphism of simplicial sets is a
monomorphism. -/
theorem mono_chainMap_of_injective
    (hf : ∀ n, Function.Injective (g.app (Opposite.op (SimplexCategory.mk n)))) :
    Mono (((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map g) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact mono_chainComplexMap_f n (hf n)

/-- The Serre filtration of the singular chain complex of `E` along `p : E → B`, as a functor
`ℕ ⥤ ChainComplex (ModuleCat ℤ) ℕ`. -/
abbrev serreChainFilt {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    ℕ ⥤ ChainComplex (ModuleCat R) ℕ :=
  serreFiltShift (sSingMap p) ⋙ (SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)

/-- **The Serre filtration of `C_*(E)` along a continuous map `p : E → B`**, as an element of
`Work.SSSR.Filtration`: the `s`-th term is the singular chain complex of the preimage under `Sing p`
of the `(s+1)`-skeleton of `Sing B`. -/
def serreFiltrationOf {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    Filtration R (Work.SSSR.Cohomology.singularChains R (TopCat.of E)) where
  F := serreChainFilt p
  mono s := mono_chainMap_of_injective (fun n => (mono_iff_injective _).mp inferInstance)
  incl s := ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
    ((serreSub (sSingMap p) s).ι)
  mono_incl s := mono_chainMap_of_injective (fun n => (mono_iff_injective _).mp inferInstance)
  compat {s t} h := by
    have hle : serreSub (sSingMap p) s ≤ serreSub (sSingMap p) t :=
      Work.SSSR.StemsB.serreSubcomplex_mono (sSingMap p) (Nat.succ_le_succ h)
    have hmap : (serreChainFilt p).map (homOfLE h) =
        ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
          ((serreSub (sSingMap p) s).homOfLE hle) := rfl
    rw [hmap]
    erw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  sat n := by
    let inc : (serreChainFilt p).obj n ⟶
        Work.SSSR.Cohomology.singularChains R (TopCat.of E) :=
      ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
        ((serreSub (sSingMap p) n).ι)
    change IsIso (inc.f n)
    haveI hmono : Mono (inc.f n) :=
      mono_chainComplexMap_f (g := (serreSub (sSingMap p) n).ι) n
        ((mono_iff_injective _).mp inferInstance)
    haveI hepi : Epi (inc.f n) :=
      epi_chainComplexMap_f (g := (serreSub (sSingMap p) n).ι) n (by
        intro x
        refine ⟨⟨x, ?_⟩, rfl⟩
        rw [Work.SSSR.StemsB.mem_serreSubcomplex]
        exact SSet.mem_skeleton _ _ (by omega))
    exact isIso_of_mono_of_epi _

end

end Work.SSSR
