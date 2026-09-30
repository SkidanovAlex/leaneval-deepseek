import Mathlib
import Submission.Work.SSSR.piszDefs
import Submission.Work.SSSR.hornCok_genC_eq_zero
import Submission.Work.SSSR.hornSimp_aMap23_mem
import Submission.Work.SSSR.iotaTLift_last_eq
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]


/-! ## Elementary transports of chains along degree equalities -/

/-- `castElem` in `eqToHom` form. -/
lemma castElem_eqToHom_apply {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j)
    (x : K.X i) : (eqToHom (congr_arg K.X h)).hom x = castElem K h x := by
  subst h; simp [castElem]

/-- Composition of morphisms of modules, on an element. -/
lemma hom_comp_apply' {M N K : ModuleCat R} (f : M ⟶ N) (g : N ⟶ K) (x : M) :
    (ModuleCat.Hom.hom g) ((ModuleCat.Hom.hom f) x) = (ModuleCat.Hom.hom (f ≫ g)) x := by
  rw [ModuleCat.hom_comp]; rfl

/-- The commutation of a chain map with the differentials, on an element. -/
lemma chainMap_comm_apply_elem {C D : ChainComplex (ModuleCat R) ℕ} (φ : C ⟶ D) {i j : ℕ}
    (x : C.X i) :
    (ModuleCat.Hom.hom (D.d i j)) ((ModuleCat.Hom.hom (φ.f i)) x)
      = (ModuleCat.Hom.hom (φ.f j)) ((ModuleCat.Hom.hom (C.d i j)) x) := by
  have h := HomologicalComplex.Hom.comm φ i j
  have h2 := congrArg (fun (g : C.X i ⟶ D.X j) => (ModuleCat.Hom.hom g) x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- Composition of two chain maps, on an element. -/
lemma chainMap_comp_apply {C D E : ChainComplex (ModuleCat R) ℕ} (φ : C ⟶ D) (ψ : D ⟶ E)
    {n : ℕ} (x : C.X n) :
    (ModuleCat.Hom.hom (ψ.f n)) ((ModuleCat.Hom.hom (φ.f n)) x)
      = (ModuleCat.Hom.hom ((φ ≫ ψ).f n)) x := by
  rw [HomologicalComplex.comp_f, hom_comp_apply']

/-! ## Simplicial generators -/

/-- The chain map induced by a simplicial map on a generator. -/
lemma sCCMap_genC_eq {X Y : SSet.{0}} (g : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    (sCCMap R g).f n (Work.SSSR.KunnethEZ.genC X x) = Work.SSSR.KunnethEZ.genC Y (g.app (op ⦋n⦌) x) := by
  have h := SSet.ι_chainComplexMap_f X Y g (ModuleCat.of R R) (n := n) x
  have h2 := congrArg (fun (φ : ModuleCat.of R R ⟶ (Y.chainComplex (ModuleCat.of R R)).X n) =>
    φ.hom (1 : R)) h
  simpa only [Work.SSSR.KunnethEZ.genC, ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The chain map induced by a simplicial map on a product generator. -/
lemma sCCMap_genP_eq {X X' Y : SSet.{0}} (g : X ⊗ X' ⟶ Y) {n : ℕ}
    (a : X _⦋n⦌) (b : X' _⦋n⦌) :
    (sCCMap R g).f n (Work.SSSR.KunnethEZ.genP R a b)
      = Work.SSSR.KunnethEZ.genC Y (g.app (op ⦋n⦌) (a, b)) := by
  rw [show Work.SSSR.KunnethEZ.genP R a b = Work.SSSR.KunnethEZ.genC (X ⊗ X') (a, b) from rfl]
  exact sCCMap_genC_eq g (a, b)

/-- The first projection of the cartesian monoidal structure on `SSet` is the first coordinate. -/
lemma fst_app_pair_eq {X Y : SSet.{0}} {k : ℕ} (x : X _⦋k⦌) (y : Y _⦋k⦌) :
    (SemiCartesianMonoidalCategory.fst X Y).app (op ⦋k⦌) (x, y) = x := by
  rw [SemiCartesianMonoidalCategory.fst_def]
  rfl

/-- The first projection of a lift of the pullback, on a pair of simplices. -/
lemma pullback_fst_app_pair {E Y F : SSet.{0}} {P : ℕ}
    (f : E ⟶ Y) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F) ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst
      (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F)
    {n : ℕ} (x : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) _⦋n⦌)
    (y : F _⦋n⦌) :
    (pullback.fst σ f).app (op ⦋n⦌) ((ez.app (op ⦋n⦌)) (x, y)) = x := by
  have h1 : (pullback.fst σ f).app (op ⦋n⦌) ((ez.app (op ⦋n⦌)) (x, y))
      = ((ez ≫ pullback.fst σ f).app (op ⦋n⦌)) (x, y) := rfl
  rw [h1, hez]
  exact fst_app_pair_eq x y

/-- Precomposing the `i`-th face of the fundamental simplex with a shuffle map keeps it in the
horn, for `i` not the last vertex. -/
lemma hornSimp_map_aHom_mem (P t : ℕ) (S : Work.SSSR.Cohomology.Crux33.PShuffle P t)
    (i : Fin (P+2)) (hi : i ≠ Fin.last (P+1)) :
    (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).map
        (Work.SSSR.Cohomology.Crux33.aHom S.1 S.2).op
        ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).δ i
          (Work.SSSR.stdIdSimplex (P+1)))
      ∈ (Work.SSSR.hornSimp (P+1)).obj (op ⦋P+t⦌) := by
  rw [Work.SSSR.hornSimp_eq_horn_last, SSet.mem_horn_iff_notMem_range]
  refine ⟨i, hi, ?_⟩
  rintro ⟨k, hk⟩
  have hk' : ⇑((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).map
        (Work.SSSR.Cohomology.Crux33.aHom S.1 S.2).op
        ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).δ i
          (Work.SSSR.stdIdSimplex (P+1)))) k
      = Fin.succAbove i (⇑(Work.SSSR.Cohomology.Crux33.aHom S.1 S.2) k) := by
    rw [show ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).δ i
        (Work.SSSR.stdIdSimplex (P+1)))
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) from by
      rw [Work.SSSR.stdIdSimplex, SSet.stdSimplex.δ_objEquiv_symm_apply]
      simp]
    rw [SSet.stdSimplex.map_apply]
    simp only [Equiv.apply_symm_apply, Opposite.unop_op]
    rw [SSet.stdSimplex.objEquiv_symm_apply, SimplexCategory.comp_toOrderHom]
    rfl
  rw [hk'] at hk
  exact Fin.succAbove_ne i (⇑(Work.SSSR.Cohomology.Crux33.aHom S.1 S.2) k) hk

/-- The boundary of the EZ shuffle chain when the fibre simplex has degree `0`. -/
lemma ezGen_bdry_faces_zero {X F : SSet.{0}} (P : ℕ) (σ : X _⦋P+1⦌) (τ : F _⦋0⦌) :
    (ModuleCat.Hom.hom ((Work.SSSR.sCC R (X ⊗ F)).d ((P+1)+0) (P+0)))
      (Work.SSSR.Cohomology.Crux33.ezGen (P+1) 0 X F σ τ)
    = ∑ i : Fin (P+2), ((-1 : ℤ) ^ (i : ℕ)) •
        Work.SSSR.Cohomology.Crux33.ezGen P 0 X F (X.δ i σ) τ := by
  change (ModuleCat.Hom.hom ((Work.SSSR.sCC R (X ⊗ F)).d (P+1) P))
      (Work.SSSR.Cohomology.Crux33.ezGen (P+1) 0 X F σ τ) = _
  rw [← Work.SSSR.KunnethEZ.ezChain_gen (P+1) 0 X F σ τ]
  rw [Work.SSSR.KunnethEZ.ezChain_d_right0 P X F (Work.SSSR.KunnethEZ.genC X σ) (Work.SSSR.KunnethEZ.genC F τ)]
  rw [Work.SSSR.KunnethEZ.d_genC P X σ]
  rw [Work.SSSR.KunnethEZ.ezChain_sum_left_zsmul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Work.SSSR.KunnethEZ.ezChain_gen]

/-! ## The horn quotient of the individual face terms -/

/-- **The non-last face terms die in the horn quotient.** -/
theorem hornCokpi_ezGen_face {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Work.SSSR.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) ⟶ Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSSR.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋t⦌)
    (i : Fin (P+2)) (hi : i ≠ Fin.last (P+1)) :
    (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f (P+t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f (P+t)))
        (Work.SSSR.Cohomology.Crux33.ezGen P t
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
          (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).δ i
            (Work.SSSR.stdIdSimplex (P+1))) τ)) = 0 := by
  have hmem : ∀ S : Work.SSSR.Cohomology.Crux33.PShuffle P t,
      (ez.app (op ⦋P+t⦌))
        (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).map
            (Work.SSSR.Cohomology.Crux33.aHom S.1 S.2).op
            (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).δ i
              (Work.SSSR.stdIdSimplex (P+1)))),
          ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
            (Work.SSSR.Cohomology.Crux33.bHom S.1 S.2).op τ))
        ∈ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).obj (op ⦋P+t⦌) := by
    intro S
    change (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋P+t⦌)
      ((ez.app (op ⦋P+t⦌))
        ((((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).map
            (Work.SSSR.Cohomology.Crux33.aHom S.1 S.2).op
            (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).δ i
              (Work.SSSR.stdIdSimplex (P+1)))),
          ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
            (Work.SSSR.Cohomology.Crux33.bHom S.1 S.2).op τ)))
      ∈ (Work.SSSR.hornSimp (P+1)).obj (op ⦋P+t⦌)
    rw [pullback_fst_app_pair (Work.SSSR.sSingP p) σ ez hez]
    exact hornSimp_map_aHom_mem P t S i hi
  rw [Work.SSSR.Cohomology.Crux33.ezGen]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_eq_zero (fun S _ => ?_)
  erw [sCCMap_genP_eq]
  rw [Work.SSSR.hornCok_genC_eq_zero (Work.SSSR.sSingP p) σ _ (hmem S)]
  exact zsmul_zero _

end Work.SSSR
