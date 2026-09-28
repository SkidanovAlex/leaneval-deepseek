import Mathlib
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.KunnethEZ.ez23_eq_ezGen
import Submission.Work.KunnethEZ.ezChain_isCycle
import Submission.Work.KunnethEZ.ezGen_map_fst
import Submission.Work.SSS.hornSimp_preimage_delta_last
import Submission.Work.SSS.mem_boundary_map_stdIdSimplex
import Submission.Work.SSS.iota_comp_piecepiOf_eq_zero
import Submission.Work.SSS.pieceBdryHornIso
import Submission.Work.SSS.hornCok_genC_eq_zero

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## Elementary helpers -/

/-- The composite of two chain maps induced by simplicial maps, on an element. -/
private lemma sCCMap_f_comp {X Y Z : SSet.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) {n : ℕ}
    (x : (Work.SSS.sCC X).X n) :
    (Work.SSS.sCCMap h).f n ((Work.SSS.sCCMap g).f n x) = (Work.SSS.sCCMap (g ≫ h)).f n x := by
  rw [Work.SSS.sCCMap_comp', HomologicalComplex.comp_f]
  rfl

/-- The composite of two chain maps applied to an element. -/
private lemma chainMap_f_comp {C D E : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (ψ : D ⟶ E)
    {n : ℕ} (x : C.X n) : ψ.f n (φ.f n x) = (φ ≫ ψ).f n x := by
  rw [HomologicalComplex.comp_f]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]

/-- `lastFaceChain ≫ TIncl` is the chain map induced by the last-face pasting map. -/
private lemma lastFaceChain_comp_TIncl' {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    Work.SSS.lastFaceChain f t σ ≫ Work.SSS.TIncl f σ
      = Work.SSS.sCCMap (Work.SSS.pullFaceIncl f σ (Fin.last (t+1))) := by
  simp only [Work.SSS.TIncl, Work.SSS.lastFaceChain]
  rw [Category.assoc, ← Work.SSS.sCCMap_comp', ← Work.SSS.sCCMap_comp']
  rw [Subfunctor.homOfLe_ι, SSet.Subcomplex.toRange_ι, Work.SSS.lastFaceMap_eq_pullFaceIncl]

/-- The first projection of the monoidal structure on `SSet` is the first coordinate. -/
private lemma fst_app_pair' {X Y : SSet.{0}} {k : ℕ} (x : X _⦋k⦌) (y : Y _⦋k⦌) :
    (SemiCartesianMonoidalCategory.fst X Y).app (op ⦋k⦌) (x, y) = x := by
  rw [SemiCartesianMonoidalCategory.fst_def]
  rfl

/-- The chain map induced by a simplicial map on a generator. -/
private lemma sCCMap_genC {X Y : SSet.{0}} (g : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    (Work.SSS.sCCMap g).f n (Work.KunnethEZ.genC X x)
      = Work.KunnethEZ.genC Y (g.app (op ⦋n⦌) x) := by
  have h := SSet.ι_chainComplexMap_f X Y g (ModuleCat.of ℤ ℤ) (n := n) x
  have h2 := congrArg (fun (φ : ModuleCat.of ℤ ℤ ⟶ (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
    φ.hom (1 : ℤ)) h
  simpa only [Work.KunnethEZ.genC, ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The chain map induced by a simplicial map on a product generator. -/
private lemma sCCMap_genP {X X' Y : SSet.{0}} (g : X ⊗ X' ⟶ Y) {n : ℕ}
    (a : X _⦋n⦌) (b : X' _⦋n⦌) :
    (Work.SSS.sCCMap g).f n (Work.KunnethEZ.genP a b)
      = Work.KunnethEZ.genC Y (g.app (op ⦋n⦌) (a, b)) := by
  rw [show Work.KunnethEZ.genP a b = Work.KunnethEZ.genC (X ⊗ X') (a, b) from rfl]
  exact sCCMap_genC g (a, b)

/-- Naturality of the shuffle chain in the first variable, with the target degree spelled `t`. -/
private lemma ezGen_map_fst_t {A Z Y : SSet.{0}} (t : ℕ) (u : A ⟶ Z) (σ : A _⦋t⦌)
    (τ : Y _⦋0⦌) :
    Work.Cohomology.Crux33.ezGen t 0 Z Y (u.app (op ⦋t⦌) σ) τ
      = (Work.SSS.sCCMap (u ⊗ₘ 𝟙 Y)).f t (Work.Cohomology.Crux33.ezGen t 0 A Y σ τ) := by
  simpa using Work.KunnethEZ.ezGen_map_fst (A := A) (Z := Z) (Y := Y) t 0 u σ τ

/-- The `i`-th face of the fundamental `(t+1)`-simplex is the coface applied to the fundamental
`t`-simplex. -/
private lemma delta_stdIdSimplex_eq_aux (t : ℕ) (i : Fin (t+2)) :
    (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).δ i (Work.SSS.stdIdSimplex (t+1))
      = (SSet.stdSimplex.δ (n := t) i).app (op ⦋t⦌) (Work.SSS.stdIdSimplex t) := by
  rw [show (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).δ i
        (Work.SSS.stdIdSimplex (t+1))
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i) from by
    rw [Work.SSS.stdIdSimplex]
    rw [SSet.stdSimplex.δ_objEquiv_symm_apply (f := 𝟙 (SimplexCategory.mk (t+1)))]
    rw [Category.comp_id]]
  rw [show (SSet.stdSimplex.δ (n := t) i) = SSet.stdSimplex.map (SimplexCategory.δ i) from rfl]
  have hh := SSet.yonedaEquiv_comp (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk t)))
    (SSet.stdSimplex.map (SimplexCategory.δ i))
  rw [Category.id_comp] at hh
  have hid : Work.SSS.stdIdSimplex t
      = SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk t))) := by
    rw [Work.SSS.stdIdSimplex]
    exact (SSet.yonedaEquiv_map (𝟙 (SimplexCategory.mk t))).symm
  rw [hid, ← hh, SSet.yonedaEquiv_map]

/-- A simplex of `Δ[n+1]` obtained by precomposing the fundamental simplex with a monotone map
that misses a vertex `i ≠ Fin.last n` lies in the horn `Work.SSS.hornSimp (n+1)`. -/
private lemma hornSimp_aHom_stdId (t : ℕ) (u : ⦋t⦌ ⟶ ⦋t+1⦌) (i : Fin (t+2))
    (hui : ∀ k : Fin (t+1), (ConcreteCategory.hom u) k ≠ i) (hi : i ≠ Fin.last (t+1)) :
    (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).map u.op
        (Work.SSS.stdIdSimplex (t+1))
      ∈ (Work.SSS.hornSimp (t+1)).obj (op ⦋t⦌) := by
  rw [Work.SSS.hornSimp_eq_horn_last, SSet.mem_horn_iff_notMem_range]
  refine ⟨i, hi, ?_⟩
  rintro ⟨k, hk⟩
  have h1 : ⇑((SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).map u.op
      (Work.SSS.stdIdSimplex (t+1))) k = (ConcreteCategory.hom u) k := by
    rw [Work.SSS.stdIdSimplex, SSet.stdSimplex.map_apply]
    simp only [SSet.stdSimplex.objEquiv.apply_symm_apply, Category.comp_id, Opposite.unop_op]
    rw [SSet.stdSimplex.objEquiv_symm_apply]
    rfl
  rw [h1] at hk
  exact hui k hk

/-! ## The `(t+1,0)` boundary formula -/

/-- **The boundary of the `(t+1,0)`-shuffle chain.** -/
private theorem ezGen_bdry_zero_right_aux (t : ℕ) (F : SSet.{0}) (τ : F _⦋0⦌) :
    (((SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⊗ F).chainComplex
        (ModuleCat.of ℤ ℤ)).d (t+1) t
      (Work.Cohomology.Crux33.ezGen (t+1) 0
        (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) F
        (Work.SSS.stdIdSimplex (t+1)) τ)
    = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
        (Work.SSS.sCCMap ((SSet.stdSimplex.δ (n := t) i) ⊗ₘ 𝟙 F)).f t
          (Work.Cohomology.Crux33.ezGen t 0
            (SSet.stdSimplex.obj (SimplexCategory.mk t) : SSet.{0}) F
            (Work.SSS.stdIdSimplex t) τ) := by
  have h1 : Work.Cohomology.Crux33.ezGen (t+1) 0
        (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) F
        (Work.SSS.stdIdSimplex (t+1)) τ
      = Work.KunnethEZ.ezChain (t+1) 0
          (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) F
          (Work.KunnethEZ.genC (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0})
            (Work.SSS.stdIdSimplex (t+1)))
          (Work.KunnethEZ.genC F τ) :=
    (Work.KunnethEZ.ezChain_gen (t+1) 0
      (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) F
      (Work.SSS.stdIdSimplex (t+1)) τ).symm
  rw [h1, Work.KunnethEZ.ezChain_d_right0 t
      (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) F
      (Work.KunnethEZ.genC (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0})
        (Work.SSS.stdIdSimplex (t+1))) (Work.KunnethEZ.genC F τ),
    Work.KunnethEZ.d_genC t (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0})
      (Work.SSS.stdIdSimplex (t+1)),
    Work.KunnethEZ.ezChain_sum_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Work.KunnethEZ.ezChain_gen, delta_stdIdSimplex_eq_aux t i,
    ezGen_map_fst_t t (SSet.stdSimplex.δ (n := t) i) (Work.SSS.stdIdSimplex t) τ]

/-! ## The last-face comparison -/

/-- **The last-face term of the `(t+1,0)` boundary formula dies in the horn quotient.** -/
private theorem iotaTBdry_last_term_aux {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋0⦌) :
    (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f t
      ((Work.SSS.sCCMap (((SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) ⊗ₘ
          𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
          ≫ Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
              (t+1) b σ h)).f t
        (Work.Cohomology.Crux33.ezGen t 0
          (SSet.stdSimplex.obj (SimplexCategory.mk t) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex t) τ))
    = (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f t
        ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f t
          ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ).f t
            (Work.SSS.iotaTLift p hfib t b
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' 0 τ))) := by
  have hface := Work.SSS.ezSimplex_liftFam_coface p hfib t b σ h (Fin.last (t+1))
    (by simp [Fin.last]) h'
  have hL : (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f t
      ((Work.SSS.sCCMap (((SSet.stdSimplex.δ (n := t) (Fin.last (t+1))) ⊗ₘ
          𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
          ≫ Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
              (t+1) b σ h)).f t
        (Work.Cohomology.Crux33.ezGen t 0
          (SSet.stdSimplex.obj (SimplexCategory.mk t) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex t) τ))
    = (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f t
        ((Work.SSS.sCCMap (Work.SSS.lastFaceMap (Work.SSS.sSingP p) t σ)).f t
          (Work.SSS.iotaTLift p hfib t b
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' 0 τ)) := by
    rw [hface, ← Work.SSS.lastFaceMap_eq_pullFaceIncl, Work.SSS.sCCMap_comp',
      ← chainMap_f_comp]
    rfl
  have hR : (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f t
        ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f t
          ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ).f t
            (Work.SSS.iotaTLift p hfib t b
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' 0 τ)))
    = (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f t
        ((Work.SSS.sCCMap (Work.SSS.lastFaceMap (Work.SSS.sSingP p) t σ)).f t
          (Work.SSS.iotaTLift p hfib t b
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' 0 τ)) := by
    rw [chainMap_f_comp (Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ)
      (Work.SSS.TIncl (Work.SSS.sSingP p) σ)]
    rw [lastFaceChain_comp_TIncl', ← Work.SSS.lastFaceMap_eq_pullFaceIncl]
    rfl
  rw [hL, hR]

/-! ## The `i ≠ last` terms die -/

/-- The `i`-th summand of the `(t+1,0)` boundary formula (with `i ≠ last`) lies over the horn. -/
private lemma mem_pieceHorn_delta {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋0⦌)
    (i : Fin (t+2)) (hi : (i : ℕ) < t+1) :
    (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (t+1) b σ h).app
        (op ⦋t⦌)
      ((SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).map
          (Work.Cohomology.Crux33.aHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2).op
          ((SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).δ i
            (Work.SSS.stdIdSimplex (t+1))),
        (Work.SSS.sSing (Work.StemsB.fibre p b)).map
          (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2).op τ)
      ∈ (Work.SSS.pieceHorn (Work.SSS.sSingP p) σ).obj (op ⦋t⦌) := by
  let A := (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).map
      (Work.Cohomology.Crux33.aHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2).op
      ((SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).δ i
        (Work.SSS.stdIdSimplex (t+1)))
  let B := (Work.SSS.sSing (Work.StemsB.fibre p b)).map
      (Work.Cohomology.Crux33.bHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2).op τ
  have hfst : (pullback.fst σ (Work.SSS.sSingP p)).app (op ⦋t⦌)
      ((Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (t+1) b σ h).app
        (op ⦋t⦌) (A, B)) = A := by
    have hc : ((Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
        (t+1) b σ h) ≫ pullback.fst σ (Work.SSS.sSingP p)).app (op ⦋t⦌) (A, B)
        = (SemiCartesianMonoidalCategory.fst
            (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0})
            (Work.SSS.sSing (Work.StemsB.fibre p b))).app (op ⦋t⦌) (A, B) :=
      congrArg (fun (φ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⊗
          (Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶
          (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0})) => φ.app (op ⦋t⦌) (A, B))
        (Work.SSS.ezSimplex_fst (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
          (t+1) b σ h)
    exact hc.trans (fst_app_pair' A B)
  have hmem : A ∈ (Work.SSS.hornSimp (t+1)).obj (op ⦋t⦌) := by
    rw [show A = (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}).map
        (Work.Cohomology.Crux33.aHom (Work.KunnethEZ.zSh0 t).1 (Work.KunnethEZ.zSh0 t).2
          ≫ SimplexCategory.δ i).op (Work.SSS.stdIdSimplex (t+1)) from by
      rw [Work.KunnethEZ.map_op_comp]
      rfl]
    exact hornSimp_aHom_stdId t _ i
      (fun k hk => by
        rw [SimplexCategory.δ] at hk
        exact Fin.succAbove_ne i _ hk)
      (by
        intro hh
        have h2 := congrArg Fin.val hh
        simp only [Fin.val_last] at h2
        omega)
  change (pullback.fst σ (Work.SSS.sSingP p)).app (op ⦋t⦌)
      ((Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
        (t+1) b σ h).app (op ⦋t⦌) (A, B))
    ∈ (Work.SSS.hornSimp (t+1)).obj (op ⦋t⦌)
  rw [hfst]
  exact hmem

/-- **The `i ≠ last` summands of the `(t+1,0)` boundary formula die in the horn quotient.** -/
private theorem iotaTBdry_term_dies_aux {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋0⦌)
    (i : Fin (t+2)) (hi : (i : ℕ) < t+1) :
    (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f t
      ((Work.SSS.sCCMap (((SSet.stdSimplex.δ (n := t) i) ⊗ₘ
          𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
          ≫ Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
              (t+1) b σ h)).f t
        (Work.Cohomology.Crux33.ezGen t 0
          (SSet.stdSimplex.obj (SimplexCategory.mk t) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex t) τ)) = 0 := by
  rw [← sCCMap_f_comp]
  rw [← ezGen_map_fst_t t (SSet.stdSimplex.δ (n := t) i)
    (Work.SSS.stdIdSimplex t) τ]
  rw [← delta_stdIdSimplex_eq_aux t i]
  rw [Work.KunnethEZ.ezGen_zero_single_right]
  rw [sCCMap_genP]
  exact Work.SSS.hornCok_genC_eq_zero (Work.SSS.sSingP p) σ _
    (mem_pieceHorn_delta p hfib t b σ h τ i hi)

/-! ## The assembly -/

/-- **The boundary of `ι_σ τ` in fibre degree `0`, as an explicit sum.** -/
theorem iotaTBdry_zero_sum {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋0⦌) :
    ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d (t+1) t)
      (Work.SSS.iotaTLift p hfib (t+1) b σ h 0 τ)
    = ∑ i : Fin (t+2), ((-1 : ℤ) ^ (i : ℕ)) •
        (Work.SSS.sCCMap (((SSet.stdSimplex.δ (n := t) i) ⊗ₘ
            𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
            ≫ Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
                (t+1) b σ h)).f t
          (Work.Cohomology.Crux33.ezGen t 0
            (SSet.stdSimplex.obj (SimplexCategory.mk t) : SSet.{0})
            (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex t) τ) := by
  have hL : ((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d (t+1) t)
        (Work.SSS.iotaTLift p hfib (t+1) b σ h 0 τ)
      = (Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
            (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f t
          (((Work.SSS.sCC ((SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⊗
              Work.SSS.sSing (Work.StemsB.fibre p b))).d (t+1) t)
            (Work.Cohomology.Crux33.ezGen (t+1) 0
              (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0})
              (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (t+1)) τ)) := by
    have hcm := congrArg (fun (φ : (Work.SSS.sCC ((SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) :
          SSet.{0}) ⊗ Work.SSS.sSing (Work.StemsB.fibre p b))).X (t+1) ⟶
        (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X t) => φ.hom
        (Work.Cohomology.Crux33.ezGen (t+1) 0
          (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex (t+1)) τ))
      ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib)
        (t+1) b σ h)).comm (t+1) t)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcm
    exact hcm
  rw [hL]
  rw [ezGen_bdry_zero_right_aux t (Work.SSS.sSing (Work.StemsB.fibre p b)) τ]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  exact sCCMap_f_comp ((SSet.stdSimplex.δ (n := t) i) ⊗ₘ 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
    (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)
    (Work.Cohomology.Crux33.ezGen t 0 (SSet.stdSimplex.obj (SimplexCategory.mk t) : SSet.{0})
      (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex t) τ)

/-- **The `q = 0` case of the boundary formula modulo the horn.**  Same statement as
`Work.SSS.iotaTBdryHorn` with the fibre degree `Q+1` replaced by `0`.  Here the cycle condition on
`τ` is automatic (`d 0 (next 0) = 0`, the shape condition), and no degree transport is needed since
`t + 0 = t = (t+1) + 0 - 1`. -/
theorem iotaTBdryHornZero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋0⦌) :
    (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f t
      (((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d (t+1) t)
        (Work.SSS.iotaTLift p hfib (t+1) b σ h 0 τ))
    = (-1 : ℤ)^(t+1) • (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f t
        ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f t
          ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ).f t
            (Work.SSS.iotaTLift p hfib t b
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' 0 τ))) := by
  rw [iotaTBdry_zero_sum p hfib t b σ h τ]
  simp only [map_sum, map_zsmul]
  rw [Finset.sum_eq_single (Fin.last (t+1))]
  · rw [Fin.val_last]
    congr 1
    exact iotaTBdry_last_term_aux p hfib t b σ h h' τ
  · intro i _ hi
    have hi' : (i : ℕ) < t+1 := by
      rcases lt_or_ge (i : ℕ) (t + 1) with hlt | hge
      · exact hlt
      · exact absurd (Fin.ext (by simp only [Fin.val_last]; omega)) hi
    rw [iotaTBdry_term_dies_aux p hfib t b σ h τ i hi', zsmul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ (Fin.last (t+1))) hmem

end

end Work.SSS
