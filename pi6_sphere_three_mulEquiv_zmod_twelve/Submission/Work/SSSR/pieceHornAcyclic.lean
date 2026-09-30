import Mathlib
import Submission.Work.SSSR.serreE1PieceDefs
import Submission.Work.SSSR.cokernelAcyclicOfHomotopy
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

/-- The functor `S ↦ ∐_{s : S} ℤ` sending a type to the free `ℤ`-module on its elements.  This is
the degreewise functor whose `alternatingFaceMapComplex` is the singular chain complex of a
simplicial set, so that `(sCC R X).X n` is `(freeModFun R).obj (X _⦋n⦌)` definitionally. -/
abbrev freeModFun (R : Type) [CommRing R] [Nontrivial R] : Type ⥤ ModuleCat R :=
  (Limits.sigmaConst (C := ModuleCat R)).obj (ModuleCat.of R R)

/-- **The `k`-th summand of the chain homotopy kills the horn.**  If `H` is a simplicial homotopy
from the identity of `X` to `g` which maps the subcomplex `Λ` into itself levelwise, then the
`k`-th summand `(freeModFun R).map (H.h k)` of the induced chain homotopy
(`Homotopy.ToChainHomotopy.hom_eq`) is killed by the cokernel projection along `Λ.ι`:
`(sCCMap R Λ.ι).f i ≫ (freeModFun R).map (H.h k) ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1) = 0`.

Indeed, `H.h k` maps `Λ_i` into `Λ_{i+1}`, so `Λ.ι`'s component at `i` followed by `H.h k` factors
through `Λ.ι`'s component at `i+1`, and `Λ.ι ≫ cokernel.π (Λ.ι) = 0`. -/
theorem hornComponent (R : Type) [CommRing R] [Nontrivial R] {X : SSet.{0}} (Λ : X.Subcomplex) {g : X ⟶ X}
    (H : CategoryTheory.SimplicialObject.Homotopy (𝟙 X) g)
    (hH : ∀ (n : ℕ) (i : Fin (n+1)) (x : X _⦋n⦌), x ∈ Λ.obj (op ⦋n⦌) → H.h i x ∈ Λ.obj (op ⦋n+1⦌))
    (i : ℕ) :
    (sCCMap R Λ.ι).f i
      ≫ (H.sSetChainComplexMap (ModuleCat.of R R)).hom i (i+1)
      ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1) = 0 := by
  have hcond : (sCCMap R Λ.ι).f (i+1) ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1) = 0 := by
    have hh := congrArg (fun φ => φ.f (i+1)) (cokernel.condition (sCCMap R Λ.ι))
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hh
    exact hh
  let M : Fin (i+1) → ((sCC R X).X i ⟶ (sCC R X).X (i+1)) := fun k => (freeModFun R).map (H.h k)
  have hK : (H.sSetChainComplexMap (ModuleCat.of R R)).hom i (i+1)
      = -∑ k : Fin (i+1), ((-1 : ℤ) ^ (k : ℕ)) • M k := by
    rw [show (H.sSetChainComplexMap (ModuleCat.of R R)).hom i (i+1) =
        CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
          (H.whiskerRight (freeModFun R)) i (i+1) from rfl]
    rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
    simp only [CategoryTheory.SimplicialObject.Homotopy.whiskerRight_h]
    rfl
  have hterm : ∀ k : Fin (i+1),
      (sCCMap R Λ.ι).f i ≫ M k ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1) = 0 := by
    intro k
    let α : (Λ.toSSet).obj (op ⦋i⦌) ⟶ (Λ.toSSet).obj (op ⦋i+1⦌) :=
      ConcreteCategory.ofHom (TypeCat.Fun.mk (fun x => ⟨H.h k x.1, hH i k x.1 x.2⟩))
    let A : (sCC R Λ).X i ⟶ (sCC R Λ).X (i+1) := (freeModFun R).map α
    have hα : ((Λ.ι).app (op ⦋i⦌)) ≫ (H.h k) = α ≫ ((Λ.ι).app (op ⦋i+1⦌)) := by
      ext x
      rfl
    have hstepF : (freeModFun R).map ((Λ.ι).app (op ⦋i⦌)) ≫ (freeModFun R).map (H.h k)
        = (freeModFun R).map α ≫ (freeModFun R).map ((Λ.ι).app (op ⦋i+1⦌)) := by
      rw [← Functor.map_comp, hα, Functor.map_comp]
    have hstepA : (sCCMap R Λ.ι).f i ≫ M k = A ≫ (sCCMap R Λ.ι).f (i+1) := hstepF
    have h1 : (sCCMap R Λ.ι).f i ≫ M k ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1)
        = (A ≫ (sCCMap R Λ.ι).f (i+1)) ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1) :=
      congrArg (fun t => t ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1)) hstepA
    have h2 : (A ≫ (sCCMap R Λ.ι).f (i+1)) ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1) = 0 := by
      rw [Category.assoc, hcond, comp_zero]
    exact h1.trans h2
  rw [hK]
  have hdistr : (sCCMap R Λ.ι).f i
        ≫ (-∑ k : Fin (i+1), ((-1 : ℤ) ^ (k : ℕ)) • M k)
        ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1)
      = -∑ k : Fin (i+1), ((-1 : ℤ) ^ (k : ℕ)) •
          ((sCCMap R Λ.ι).f i ≫ M k ≫ (cokernel.π (sCCMap R Λ.ι)).f (i+1)) := by
    simp only [Preadditive.neg_comp, Preadditive.sum_comp, Preadditive.zsmul_comp,
      Preadditive.comp_neg, Preadditive.comp_sum, Preadditive.comp_zsmul]
  rw [hdistr, Finset.sum_eq_zero (fun k _ => by rw [hterm k, smul_zero]), neg_zero]

/-- **Acyclicity of `C(T_σ)/C(Λ)` from a contraction of the pair.**  Suppose `g : T_σ ⟶ T_σ` and
`H : SimplicialObject.Homotopy (𝟙 T_σ) g` are such that `g` maps every simplex into the horn
subcomplex `Λ` and every `H.h i` preserves `Λ` levelwise (the data produced by
`Work.SSSR.pieceContraction`).  Then the quotient complex `pieceHornC R (sSingP p) σ` has vanishing
homology in every degree: the simplicial homotopy induces a chain homotopy (Mathlib's
`CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap`), which descends to the quotient
because both `H.h i` and `g` preserve `Λ`; since `g` induces the zero map on the quotient, the
identity of the quotient complex is null-homotopic. -/
theorem pieceHornAcyclic (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (g : Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ ⟶ Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
    (H : CategoryTheory.SimplicialObject.Homotopy (𝟙 _) g)
    (hg : ∀ (n : ℕ)
        (x : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).obj (Opposite.op (SimplexCategory.mk n))),
        g.app _ x ∈ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).obj _)
    (hH : ∀ (n : ℕ) (i : Fin (n+1))
        (x : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).obj (Opposite.op (SimplexCategory.mk n))),
        x ∈ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).obj _ →
        H.h i x ∈ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).obj _)
    (m : ℕ) :
    Subsingleton ((Work.SSSR.pieceHornC R (Work.SSSR.sSingP p) σ).homology m) := by
  have hle : SSet.Subcomplex.range g ≤ pieceHorn (sSingP p) σ := by
    rw [Subfunctor.le_def]
    intro U x hx
    rw [Subfunctor.range_obj] at hx
    obtain ⟨y, rfl⟩ := hx
    exact hg U.unop.len y
  let g' : pullAlong (sSingP p) σ ⟶ (pieceHorn (sSingP p) σ).toSSet := SSet.Subcomplex.lift g hle
  have hg' : g' ≫ (pieceHorn (sSingP p) σ).ι = g := SSet.Subcomplex.lift_ι g hle
  haveI hmono : Mono (SSet.chainComplexMap (pieceHorn (sSingP p) σ).ι (ModuleCat.of R R)) :=
    sChainMap_mono R _ inferInstance
  have hid : SSet.chainComplexMap (𝟙 (pullAlong (sSingP p) σ)) (ModuleCat.of R R)
      = 𝟙 (sCC R (pullAlong (sSingP p) σ)) := by
    rw [show SSet.chainComplexMap (𝟙 (pullAlong (sSingP p) σ)) (ModuleCat.of R R)
        = ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map
            (𝟙 (pullAlong (sSingP p) σ)) from rfl,
      CategoryTheory.Functor.map_id]
  let K : Homotopy (𝟙 (sCC R (pullAlong (sSingP p) σ)))
      (SSet.chainComplexMap g (ModuleCat.of R R)) :=
    (Homotopy.ofEq hid.symm).trans (H.sSetChainComplexMap (ModuleCat.of R R))
  have hKhom : ∀ i j, K.hom i j = (H.sSetChainComplexMap (ModuleCat.of R R)).hom i j := by
    intro i j
    simp [K, Homotopy.trans, Homotopy.ofEq]
  have hf : SSet.chainComplexMap g' (ModuleCat.of R R)
        ≫ SSet.chainComplexMap (pieceHorn (sSingP p) σ).ι (ModuleCat.of R R)
      = SSet.chainComplexMap g (ModuleCat.of R R) := by
    rw [← Functor.map_comp, hg']
  have hcomp : ∀ i : ℕ,
      (SSet.chainComplexMap (pieceHorn (sSingP p) σ).ι (ModuleCat.of R R)).f i
        ≫ K.hom i (i + 1)
        ≫ (cokernel.π (SSet.chainComplexMap (pieceHorn (sSingP p) σ).ι (ModuleCat.of R R))).f (i + 1) = 0 := by
    intro i
    rw [hKhom i (i+1)]
    exact hornComponent R (pieceHorn (sSingP p) σ) H hH i
  exact ModuleCat.subsingleton_of_isZero
    (cokernelAcyclicOfHomotopy
      (SSet.chainComplexMap (pieceHorn (sSingP p) σ).ι (ModuleCat.of R R))
      K hf hcomp m)

end

end Work.SSSR
