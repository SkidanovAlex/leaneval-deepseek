import Mathlib
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.hornCok_genC_eq_zero
import Submission.Work.SSS.hornSimp_aMap23_mem
import Submission.Work.SSS.iotaTLift_last_eq

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]


/-! ## Elementary transports of chains along degree equalities -/

/-- `castElem` in `eqToHom` form. -/
lemma castElem_eqToHom_apply {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (x : K.X i) : (eqToHom (congr_arg K.X h)).hom x = castElem K h x := by
  subst h; simp [castElem]

/-- A degree transport along `i = i` is the identity. -/
lemma castElem_self_eq {K : ChainComplex (ModuleCat ℤ) ℕ} {i : ℕ} (h : i = i) (x : K.X i) :
    castElem K h x = x := by
  rw [Subsingleton.elim h rfl]; simp [castElem]

/-- Composition of two degree transports. -/
lemma castElem_trans_eq {K : ChainComplex (ModuleCat ℤ) ℕ} {i j l : ℕ} (h : i = j) (h' : j = l)
    (x : K.X i) : castElem K h' (castElem K h x) = castElem K (h.trans h') x := by
  subst h; subst h'; simp [castElem]

/-- Differentials whose target indices agree differ by the degree transport. -/
lemma d_eqToHom_d (K : ChainComplex (ModuleCat ℤ) ℕ) {i j j' : ℕ} (h : j' = j)
    (rij : (ComplexShape.down ℕ).Rel i j) (rij' : (ComplexShape.down ℕ).Rel i j') (x : K.X i) :
    (eqToHom (congr_arg K.X h)).hom (K.d i j' x) = K.d i j x := by
  have hh0 : h = (ComplexShape.down ℕ).next_eq rij' rij := Subsingleton.elim _ _
  rw [hh0]
  have h2 := congrArg (fun (g : K.X i ⟶ K.X j) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.d_comp_eqToHom K rij rij')
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- Composition of morphisms of modules, on an element. -/
lemma hom_comp_apply' {M N K : ModuleCat ℤ} (f : M ⟶ N) (g : N ⟶ K) (x : M) :
    (ModuleCat.Hom.hom g) ((ModuleCat.Hom.hom f) x) = (ModuleCat.Hom.hom (f ≫ g)) x := by
  rw [ModuleCat.hom_comp]; rfl

/-- The commutation of a chain map with the differentials, on an element. -/
lemma chainMap_comm_apply_elem {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) {i j : ℕ}
    (x : C.X i) :
    (ModuleCat.Hom.hom (D.d i j)) ((ModuleCat.Hom.hom (φ.f i)) x)
      = (ModuleCat.Hom.hom (φ.f j)) ((ModuleCat.Hom.hom (C.d i j)) x) := by
  have h := HomologicalComplex.Hom.comm φ i j
  have h2 := congrArg (fun (g : C.X i ⟶ D.X j) => (ModuleCat.Hom.hom g) x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- Composition of two chain maps, on an element. -/
lemma chainMap_comp_apply {C D E : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (ψ : D ⟶ E)
    {n : ℕ} (x : C.X n) :
    (ModuleCat.Hom.hom (ψ.f n)) ((ModuleCat.Hom.hom (φ.f n)) x)
      = (ModuleCat.Hom.hom ((φ ≫ ψ).f n)) x := by
  rw [HomologicalComplex.comp_f, hom_comp_apply']

/-! ## Simplicial generators -/

/-- The chain map induced by a simplicial map on a generator. -/
lemma sCCMap_genC_eq {X Y : SSet.{0}} (g : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    (sCCMap g).f n (Work.KunnethEZ.genC X x) = Work.KunnethEZ.genC Y (g.app (op ⦋n⦌) x) := by
  have h := SSet.ι_chainComplexMap_f X Y g (ModuleCat.of ℤ ℤ) (n := n) x
  have h2 := congrArg (fun (φ : ModuleCat.of ℤ ℤ ⟶ (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
    φ.hom (1 : ℤ)) h
  simpa only [Work.KunnethEZ.genC, ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The chain map induced by a simplicial map on a product generator. -/
lemma sCCMap_genP_eq {X X' Y : SSet.{0}} (g : X ⊗ X' ⟶ Y) {n : ℕ}
    (a : X _⦋n⦌) (b : X' _⦋n⦌) :
    (sCCMap g).f n (Work.KunnethEZ.genP a b)
      = Work.KunnethEZ.genC Y (g.app (op ⦋n⦌) (a, b)) := by
  rw [show Work.KunnethEZ.genP a b = Work.KunnethEZ.genC (X ⊗ X') (a, b) from rfl]
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
lemma hornSimp_map_aHom_mem (P t : ℕ) (S : Work.Cohomology.Crux33.PShuffle P t)
    (i : Fin (P+2)) (hi : i ≠ Fin.last (P+1)) :
    (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).map
        (Work.Cohomology.Crux33.aHom S.1 S.2).op
        ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).δ i
          (Work.SSS.stdIdSimplex (P+1)))
      ∈ (Work.SSS.hornSimp (P+1)).obj (op ⦋P+t⦌) := by
  rw [Work.SSS.hornSimp_eq_horn_last, SSet.mem_horn_iff_notMem_range]
  refine ⟨i, hi, ?_⟩
  rintro ⟨k, hk⟩
  have hk' : ⇑((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).map
        (Work.Cohomology.Crux33.aHom S.1 S.2).op
        ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).δ i
          (Work.SSS.stdIdSimplex (P+1)))) k
      = Fin.succAbove i (⇑(Work.Cohomology.Crux33.aHom S.1 S.2) k) := by
    rw [show ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).δ i
        (Work.SSS.stdIdSimplex (P+1)))
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) from by
      rw [Work.SSS.stdIdSimplex, SSet.stdSimplex.δ_objEquiv_symm_apply]
      simp]
    rw [SSet.stdSimplex.map_apply]
    simp only [Equiv.apply_symm_apply, Opposite.unop_op]
    rw [SSet.stdSimplex.objEquiv_symm_apply, SimplexCategory.comp_toOrderHom]
    rfl
  rw [hk'] at hk
  exact Fin.succAbove_ne i (⇑(Work.Cohomology.Crux33.aHom S.1 S.2) k) hk

/-! ## The Eilenberg–Zilber boundary formula -/

/-- The `X`-boundary shuffle chain of a face is the EZ chain of that face, transported to the
degree `(P+1)+k`. -/
lemma rawX_eq_castElem_ezGen {X F : SSet.{0}} (P k : ℕ) (σ : X _⦋P⦌) (τ : F _⦋k+1⦌)
    (h : P+(k+1) = (P+1)+k) :
    Work.KunnethEZ.rawX P k X F (Work.KunnethEZ.genC X σ) (Work.KunnethEZ.genC F τ)
      = castElem (Work.SSS.sCC (X ⊗ F)) h
          (Work.Cohomology.Crux33.ezGen P (k+1) X F σ τ) := by
  rw [Work.KunnethEZ.rawX_eq_ezChain P k X F (by omega : P+(k+1) = (P+1)+(k+1)-1)
    (Work.KunnethEZ.genC X σ) (Work.KunnethEZ.genC F τ), Work.KunnethEZ.ezChain_gen]
  rw [castElem_eqToHom_apply]

/-- The boundary of the EZ shuffle chain when the fibre simplex has degree `0`. -/
lemma ezGen_bdry_faces_zero {X F : SSet.{0}} (P : ℕ) (σ : X _⦋P+1⦌) (τ : F _⦋0⦌) :
    (ModuleCat.Hom.hom ((Work.SSS.sCC (X ⊗ F)).d ((P+1)+0) (P+0)))
      (Work.Cohomology.Crux33.ezGen (P+1) 0 X F σ τ)
    = ∑ i : Fin (P+2), ((-1 : ℤ) ^ (i : ℕ)) •
        Work.Cohomology.Crux33.ezGen P 0 X F (X.δ i σ) τ := by
  change (ModuleCat.Hom.hom ((Work.SSS.sCC (X ⊗ F)).d (P+1) P))
      (Work.Cohomology.Crux33.ezGen (P+1) 0 X F σ τ) = _
  rw [← Work.KunnethEZ.ezChain_gen (P+1) 0 X F σ τ]
  rw [Work.KunnethEZ.ezChain_d_right0 P X F (Work.KunnethEZ.genC X σ) (Work.KunnethEZ.genC F τ)]
  rw [Work.KunnethEZ.d_genC P X σ]
  rw [Work.KunnethEZ.ezChain_sum_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Work.KunnethEZ.ezChain_gen]

/-- The boundary of the EZ shuffle chain when the fibre simplex has degree `k+1`. -/
lemma ezGen_bdry_faces_succ {X F : SSet.{0}} (P k : ℕ) (σ : X _⦋P+1⦌) (τ : F _⦋k+1⦌)
    (hτ : (ModuleCat.Hom.hom ((Work.SSS.sCC F).d (k+1) ((ComplexShape.down ℕ).next (k+1))))
      (((F.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ)).hom 1) = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.sCC (X ⊗ F)).d ((P+1)+(k+1)) (P+(k+1))))
      (Work.Cohomology.Crux33.ezGen (P+1) (k+1) X F σ τ)
    = ∑ i : Fin (P+2), ((-1 : ℤ) ^ (i : ℕ)) •
        Work.Cohomology.Crux33.ezGen P (k+1) X F (X.δ i σ) τ := by
  have hτ' : (ModuleCat.Hom.hom ((Work.SSS.sCC F).d (k+1) k))
      (Work.KunnethEZ.genC F τ) = 0 := by
    have h := hτ
    rw [ChainComplex.next_nat_succ] at h
    simpa using h
  have htr : (ModuleCat.Hom.hom ((Work.SSS.sCC (X ⊗ F)).d ((P+1)+(k+1)) (P+(k+1))))
      (Work.Cohomology.Crux33.ezGen (P+1) (k+1) X F σ τ)
      = (eqToHom (congr_arg (Work.SSS.sCC (X ⊗ F)).X
          (show (P+1)+k = P+(k+1) by omega))).hom
        ((ModuleCat.Hom.hom ((Work.SSS.sCC (X ⊗ F)).d ((P+1)+(k+1)) ((P+1)+(k+1)-1)))
          (Work.Cohomology.Crux33.ezGen (P+1) (k+1) X F σ τ)) :=
    (d_eqToHom_d (Work.SSS.sCC (X ⊗ F)) (i := (P+1)+(k+1)) (j := P+(k+1))
      (j' := (P+1)+k) (by omega)
      (by show (P+(k+1)) + 1 = (P+1)+(k+1); omega)
      (by show ((P+1)+k) + 1 = (P+1)+(k+1); omega)
      (Work.Cohomology.Crux33.ezGen (P+1) (k+1) X F σ τ)).symm
  rw [htr]
  rw [Work.KunnethEZ.d_ezGen P k X F σ τ]
  rw [Work.KunnethEZ.d_genC P X σ]
  rw [Work.KunnethEZ.rawX_sum_left]
  have hy : Work.KunnethEZ.rawY P k X F (Work.KunnethEZ.genC X σ)
      ((ModuleCat.Hom.hom ((Work.SSS.sCC F).d (k+1) k)) (Work.KunnethEZ.genC F τ)) = 0 := by
    rw [hτ', Work.KunnethEZ.rawY, map_zero, map_zero]
  rw [hy, zsmul_zero, add_zero]
  rw [map_sum]
  simp only [map_zsmul]
  have h2 : P+(k+1) = (P+1)+k := by omega
  have hh : (P+1)+k = P+(k+1) := h2.symm
  have key : ∀ (b : (Work.SSS.sCC (X ⊗ F)).X (P+(k+1))),
      (eqToHom (congr_arg (Work.SSS.sCC (X ⊗ F)).X hh)).hom
        (castElem (Work.SSS.sCC (X ⊗ F)) h2 b) = b := by
    intro b
    rw [castElem_eqToHom_apply hh]
    exact (castElem_trans_eq (K := Work.SSS.sCC (X ⊗ F)) h2 hh b).trans
      (castElem_self_eq (h2.trans hh) b)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [rawX_eq_castElem_ezGen P k (X.δ i σ) τ h2]
  rw [key]

/-- **The boundary of the Eilenberg–Zilber shuffle chain.** -/
theorem ezGen_bdry_faces {X F : SSet.{0}} (P t : ℕ) (σ : X _⦋P+1⦌) (τ : F _⦋t⦌)
    (hτ : (ModuleCat.Hom.hom ((Work.SSS.sCC F).d t ((ComplexShape.down ℕ).next t)))
      (((F.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ)).hom 1) = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.sCC (X ⊗ F)).d ((P+1)+t) (P+t)))
      (Work.Cohomology.Crux33.ezGen (P+1) t X F σ τ)
    = ∑ i : Fin (P+2), ((-1 : ℤ) ^ (i : ℕ)) •
        Work.Cohomology.Crux33.ezGen P t X F (X.δ i σ) τ := by
  rcases t with _ | k
  · exact ezGen_bdry_faces_zero P σ τ
  · exact ezGen_bdry_faces_succ P k σ τ hτ

/-! ## The horn quotient of the individual face terms -/

/-- **The non-last face terms die in the horn quotient.** -/
theorem hornCokpi_ezGen_face {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋t⦌)
    (i : Fin (P+2)) (hi : i ≠ Fin.last (P+1)) :
    (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (P+t)))
        (Work.Cohomology.Crux33.ezGen P t
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b))
          (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).δ i
            (Work.SSS.stdIdSimplex (P+1))) τ)) = 0 := by
  have hmem : ∀ S : Work.Cohomology.Crux33.PShuffle P t,
      (ez.app (op ⦋P+t⦌))
        (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).map
            (Work.Cohomology.Crux33.aHom S.1 S.2).op
            (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).δ i
              (Work.SSS.stdIdSimplex (P+1)))),
          ((Work.SSS.sSing (Work.StemsB.fibre p b)).map
            (Work.Cohomology.Crux33.bHom S.1 S.2).op τ))
        ∈ (Work.SSS.pieceHorn (Work.SSS.sSingP p) σ).obj (op ⦋P+t⦌) := by
    intro S
    change (pullback.fst σ (Work.SSS.sSingP p)).app (op ⦋P+t⦌)
      ((ez.app (op ⦋P+t⦌))
        ((((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).map
            (Work.Cohomology.Crux33.aHom S.1 S.2).op
            (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).δ i
              (Work.SSS.stdIdSimplex (P+1)))),
          ((Work.SSS.sSing (Work.StemsB.fibre p b)).map
            (Work.Cohomology.Crux33.bHom S.1 S.2).op τ)))
      ∈ (Work.SSS.hornSimp (P+1)).obj (op ⦋P+t⦌)
    rw [pullback_fst_app_pair (Work.SSS.sSingP p) σ ez hez]
    exact hornSimp_map_aHom_mem P t S i hi
  rw [Work.Cohomology.Crux33.ezGen]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_eq_zero (fun S _ => ?_)
  erw [sCCMap_genP_eq]
  rw [Work.SSS.hornCok_genC_eq_zero (Work.SSS.sSingP p) σ _ (hmem S)]
  exact zsmul_zero _

/-- **The last face term is the push-forward along the last-face pasting map.** -/
theorem hornCokpi_ezGen_last {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋t⦌) :
    (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (P+t)))
        (Work.Cohomology.Crux33.ezGen P t
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b))
          (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).δ (Fin.last (P+1))
            (Work.SSS.stdIdSimplex (P+1))) τ))
    = (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap
                (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
              (Work.Cohomology.Crux33.ezGen P t
                (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ)))) := by
  have hcomp : ((SSet.stdSimplex.δ (n := P) (Fin.last (P+1))) ⊗ₘ 𝟙
        (Work.SSS.sSing (Work.StemsB.fibre p b))) ≫ ez
      = Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1))
          ≫ Work.SSS.pullFaceIncl (Work.SSS.sSingP p) σ (Fin.last (P+1)) :=
    (Work.SSS.faceLift_pullFaceIncl (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1))).symm
  have hgen : Work.Cohomology.Crux33.ezGen P t
        (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
        (Work.SSS.sSing (Work.StemsB.fibre p b))
        (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})).δ (Fin.last (P+1))
          (Work.SSS.stdIdSimplex (P+1))) τ
      = (ModuleCat.Hom.hom ((Work.SSS.sCCMap ((SSet.stdSimplex.δ (n := P) (Fin.last (P+1))) ⊗ₘ
            𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))).f (P+t)))
          (Work.Cohomology.Crux33.ezGen P t
            (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
            (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ) := by
    rw [Work.SSS.delta_stdIdSimplex_eq P (Fin.last (P+1))]
    exact Work.KunnethEZ.ezGen_map_fst P t (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)))
      (Work.SSS.stdIdSimplex P) τ
  have hchain : (ModuleCat.Hom.hom ((Work.SSS.sCCMap
        (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1))
          ≫ Work.SSS.pullFaceIncl (Work.SSS.sSingP p) σ (Fin.last (P+1)))).f (P+t)))
        (Work.Cohomology.Crux33.ezGen P t
          (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ)
      = (ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap
                (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
              (Work.Cohomology.Crux33.ezGen P t
                (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ))) := by
    have h1 : Work.SSS.sCCMap (Work.SSS.pullFaceIncl (Work.SSS.sSingP p) σ (Fin.last (P+1)))
        = Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ
            ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ :=
      (Work.SSS.lastFaceChain_comp_TIncl (Work.SSS.sSingP p) P σ).symm
    rw [Work.SSS.sCCMap_comp', h1]
    rw [← chainMap_comp_apply (Work.SSS.sCCMap
      (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1))))
      (Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ ≫ Work.SSS.TIncl (Work.SSS.sSingP p) σ)]
    rw [← chainMap_comp_apply (Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ)
      (Work.SSS.TIncl (Work.SSS.sSingP p) σ)]
  rw [hgen, sCCMap_comp_apply, hcomp, hchain]

/-- **The boundary of a lifted Eilenberg–Zilber chain modulo the horn.**

For `f = sSingP p` (a Serre fibration `p`), a simplex `σ : Δ[P+1] ⟶ Sing B`, a lift
`ez : Δ[P+1] ⊗ F ⟶ T_σ` of `pr₁ ≫ σ` (`hez`), and a cycle `τ` of the fibre `F = Sing (p⁻¹b)` in
degree `t`, the class in `C(T_σ)/C(Λ)` (Λ = `pieceHorn`) of `∂(ez_*(EZ(P+1,t,[id],τ)))` is
`(-1)^(P+1)` times the class of the push-forward along `TIncl ≫ lastFaceChain` of the EZ chain
`EZ(P,t,[id],τ)` pushed along the *face restriction* `faceLift` of `ez`.

The already proved specialisations `Work.SSS.iotaTBdryHorn` (fibre degree `Q+1`) and
`Work.SSS.iotaTBdryHornZero` (fibre degree `0`) have exactly this shape with
`ez = ezSimplex p (liftFam p hfib) (liftFam_proj p hfib)`, and their proofs (Eilenberg–Zilber
boundary formula, `Work.SSS.hornCok_genC_eq_zero`, `Work.SSS.hornSimp_aMap23_mem`,
`Work.SSS.faceLift_pullFaceIncl`, `Work.SSS.lastFaceChain_comp_TIncl`) adapt verbatim, with
`hez` replacing `Work.SSS.ezSimplex_fst`. -/
theorem hornCok_d_faceLift (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋t⦌)
    (hτ : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))).d t
        ((ComplexShape.down ℕ).next t)))
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0) :
    (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)))
        ((ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d
            ((P+1)+t) (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f ((P+1)+t)))
            (Work.Cohomology.Crux33.ezGen (P+1) t
              (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (P+1)) τ)))
      = (-1 : ℤ)^(P+1) •
          (ModuleCat.Hom.hom ((Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f (P+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) P σ).f (P+t)))
                ((ModuleCat.Hom.hom ((Work.SSS.sCCMap
                    (Work.SSS.faceLift (Work.SSS.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
                  (Work.Cohomology.Crux33.ezGen P t
                    (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                    (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) τ)))) := by
  rw [chainMap_comm_apply_elem (Work.SSS.sCCMap ez)]
  rw [ezGen_bdry_faces P t (Work.SSS.stdIdSimplex (P+1)) τ hτ]
  simp only [map_sum, map_zsmul]
  rw [Finset.sum_eq_single (Fin.last (P+1))]
  · rw [Fin.val_last]
    congr 1
    exact hornCokpi_ezGen_last p P t b σ ez hez τ
  · intro i _ hi
    rw [hornCokpi_ezGen_face p P t b σ ez hez τ i hi, zsmul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem


end Work.SSS
