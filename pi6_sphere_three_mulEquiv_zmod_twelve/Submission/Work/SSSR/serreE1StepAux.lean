import Mathlib
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.iotaTBdryHorn
import Submission.Work.SSSR.pieceBdryHornIsoIso_inv

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

namespace StepAux

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## `castElem` -/

/-- The transport of an element of a chain complex along an equality of degrees is natural for
chain maps. -/
lemma castElem_map {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j)
    (x : K.X i) : castElem L h ((φ.f i) x) = (φ.f j) (castElem K h x) := by
  subst h
  simp [castElem]

lemma castElem_zsmul {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j) (c : ℤ)
    (x : K.X i) : castElem K h (c • x) = c • castElem K h x := by
  subst h
  simp [castElem]

lemma castElem_trans {K : ChainComplex (ModuleCat R) ℕ} {i j k : ℕ} (h : i = j) (h' : j = k)
    (x : K.X i) : castElem K h' (castElem K h x) = castElem K (h.trans h') x := by
  subst h; subst h'
  simp [castElem]

/-- Element-level naturality of degree transport for a chain map, in the `sCC R` spelling. -/
lemma sCCMap_castElem {X Y : SSet.{0}} (φ : X ⟶ Y) {i j : ℕ} (h : i = j)
    (x : (Work.SSSR.sCC R X).X i) :
    (Work.SSSR.sCCMap R φ).f j (Work.SSSR.castElem (Work.SSSR.sCC R X) h x)
      = Work.SSSR.castElem (Work.SSSR.sCC R Y) h ((Work.SSSR.sCCMap R φ).f i x) := by
  subst h
  simp [Work.SSSR.castElem]

/-- Composition of chain maps applied to an element. -/
lemma sCCMap_comp_apply {X Y Z : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ}
    (x : (Work.SSSR.sCC R X).X n) :
    (Work.SSSR.sCCMap R k).f n ((Work.SSSR.sCCMap R g).f n x) = (Work.SSSR.sCCMap R (g ≫ k)).f n x := by
  rw [Work.SSSR.sCCMap_comp']; rfl

/-! ## `castCycles` -/

/-- Transport of an element of the cycles of a chain complex along an equality of degrees. -/
def castCycles (K : ChainComplex (ModuleCat R) ℕ) {i j : ℕ} (h : i = j) (x : K.cycles i) :
    K.cycles j :=
  h ▸ x

/-! ## Cycles, homology classes and degree transport -/

lemma iCycles_cyclesMk (K : ChainComplex (ModuleCat R) ℕ) {i : ℕ}
    (j : ℕ) (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.iCycles i (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) x j hj hx

lemma iCycles_castCycles (K : ChainComplex (ModuleCat R) ℕ) {i j : ℕ} (h : i = j)
    (z : K.cycles i) : K.iCycles j (castCycles K h z) = castElem K h (K.iCycles i z) := by
  subst h; rfl

/-- `homologyMap` on a class, elementwise. -/
lemma homologyMap_homologyπ {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (i : ℕ)
    (x : K.cycles i) :
    (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) x)
      = (L.homologyπ i) ((HomologicalComplex.cyclesMap φ i) x) := by
  have h := HomologicalComplex.homologyπ_naturality φ i
  exact congrArg (fun (f : K.cycles i ⟶ L.homology i) => f x) h

/-- The transport of a homology class along an equality of degrees. -/
lemma eqToIso_homologyπ {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j)
    (x : K.cycles i) :
    (eqToIso (congrArg (fun m => K.homology m) h)).hom ((K.homologyπ i) x)
      = (K.homologyπ j) (castCycles K h x) := by
  subst h
  simp [castCycles]

/-- Stripping the `forget₂ (ModuleCat ℤ) Ab` from the element-level description. -/
lemma forget2_Ab_hom_apply {M N : ModuleCat R} (f : M ⟶ N) (x : M) :
    (ConcreteCategory.hom ((forget₂ (ModuleCat R) Ab).map f)) x = (ConcreteCategory.hom f) x :=
  rfl

lemma castElem_irrel {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h h' : i = j) (x : K.X i) :
    castElem K h x = castElem K h' x := by
  rw [Subsingleton.elim h h']

/-- The differential at a degree is the differential at a propositionally equal degree, up to the
degree transport. -/
lemma d_eq_castElem (K : ChainComplex (ModuleCat R) ℕ) {i j j' : ℕ} (h : j = j') (x : K.X i) :
    K.d i j' x = castElem K h (K.d i j x) := by
  subst h
  simp [castElem]

/-! ## The value of `iotaT` / `iotaF` on a generator -/

/-- The morphism `eltHom z` evaluated at `1` is `z`. -/
lemma eltHom_apply_one {M : ModuleCat R} (z : M) : (Work.SSSR.eltHom z).hom 1 = z := by
  rw [Work.SSSR.eltHom, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one]

/-- The value of `iotaT` on the generator of a simplex is the Eilenberg–Zilber lift. -/
lemma iotaT_gen_apply (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋q⦌) :
    (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) P b σ h q)
        (((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of R R) τ).hom 1)
      = Work.SSSR.iotaTLift p hfib P b σ h q τ := by
  have h1 := Work.SSSR.iotaT_gen (R := R) (p := p) (Work.SSSR.liftFam p hfib)
    (Work.SSSR.liftFam_proj p hfib) P b σ h q τ
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (P+q)) => g.hom (1 : R)) h1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [Work.SSSR.eltHom, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one] at h2
  simpa only [Work.SSSR.iotaTLift] using h2

/-! ## The two explicit chain maps of the σ-descent -/

/-- The inclusion `C(∂T_σ) ⟶ C(T_σ)` is a monomorphism. -/
instance mono_TIncl {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Mono (Work.SSSR.TIncl (R := R) f σ) := by
  change Mono (Work.SSSR.sChainMap R (Work.SSSR.bdryAlong f σ).ι)
  exact Work.SSSR.sChainMap_mono R _ inferInstance

/-- The first map `C(T_σ)/C(Λ) ⟶ C(T_σ)/C(∂T_σ)` of the σ-descent. -/
noncomputable def snakeG {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    cokernel (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl (R := R) f σ) ⟶ cokernel (Work.SSSR.TIncl f σ) :=
  cokernel.map (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl f σ) (Work.SSSR.TIncl f σ)
    (Work.SSSR.bdryIncl f σ) (𝟙 _) (by rw [Category.comp_id])

/-- The second map `C(∂T_σ)/C(Λ) ⟶ C(T_σ)/C(Λ)` of the σ-descent. -/
noncomputable def snakeF {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    cokernel (Work.SSSR.bdryIncl f σ) ⟶ cokernel (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl (R := R) f σ) :=
  cokernel.map (Work.SSSR.bdryIncl f σ) (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl f σ)
    (𝟙 _) (Work.SSSR.TIncl f σ) (by rw [Category.id_comp])

/-- The projection formula for `snakeG`. -/
lemma snakeG_π {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    cokernel.π (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl f σ) ≫ snakeG f t σ
      = 𝟙 (Work.SSSR.sCC R (Work.SSSR.pullAlong f σ)) ≫ cokernel.π (Work.SSSR.TIncl f σ) := by
  rw [snakeG, cokernel.map, cokernel.π_desc]

/-- The projection formula for `snakeF`. -/
lemma snakeF_π {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    cokernel.π (Work.SSSR.bdryIncl f σ) ≫ snakeF (R := R) f t σ
      = Work.SSSR.TIncl f σ ≫ cokernel.π (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl f σ) := by
  rw [snakeF, cokernel.map, cokernel.π_desc]

/-! ## The connecting map of the σ-descent on a class -/

/-- **The connecting map `Work.SSSR.pieceConnectingIsoIso` on a class**, computed by
`ShortComplex.ShortExact.δ_apply`.  In the notation of `serreE1PieceIotaDefs`,
`T_σ = pullAlong f σ`, `Λ = pieceHorn f σ`, and `snakeG`, `snakeF` are the two chain maps of the
short exact sequence `C(Λ) ⊆ C(∂T_σ) ⊆ C(T_σ)`.  Given elements `x₃`, `x₂`, `x₁` of the three
cokernels with `snakeG x₂ = x₃` and `snakeF x₁ = d_{X₂} x₂`, the connecting map sends the class of
the cycle `x₃` to the class of the cycle `x₁`. -/
theorem eA_apply {X Y : SSet.{0}} (f : X ⟶ Y) (t m : ℕ) (hm : 1 ≤ m)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y)
    (hi : IsZero ((Work.SSSR.pieceHornC R f σ).homology m))
    (hj : IsZero ((Work.SSSR.pieceHornC R f σ).homology (m-1)))
    (x3 : (Work.SSSR.pieceAlong R f σ).X m)
    (hx3 : (Work.SSSR.pieceAlong R f σ).d m ((ComplexShape.down ℕ).next m) x3 = 0)
    (x2 : (cokernel (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl f σ)).X m)
    (hx2 : (snakeG f t σ).f m x2 = x3)
    (x1 : (Work.SSSR.pieceBdryHornC R f σ).X (m-1))
    (hx1 : (snakeF f t σ).f (m-1) x1
            = (cokernel (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl f σ)).d m (m-1) x2)
    (hx1c : (Work.SSSR.pieceBdryHornC R f σ).d (m-1) ((ComplexShape.down ℕ).next (m-1)) x1 = 0) :
    (Work.SSSR.pieceConnectingIsoIso f t σ m hm hi hj).hom
        (HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R f σ) m
          (HomologicalComplex.cyclesMk (Work.SSSR.pieceAlong R f σ) x3
            ((ComplexShape.down ℕ).next m) rfl hx3))
      = HomologicalComplex.homologyπ (Work.SSSR.pieceBdryHornC R f σ) (m-1)
          (HomologicalComplex.cyclesMk (Work.SSSR.pieceBdryHornC R f σ) x1
            ((ComplexShape.down ℕ).next (m-1)) rfl hx1c) := by
  haveI : Mono (Work.SSSR.TIncl f σ) := mono_TIncl (R := R) f σ
  set S : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
    (kernelCokernelCompSequence.snakeInput (Work.SSSR.bdryIncl f σ) (Work.SSSR.TIncl f σ)).L₃ with hSdef
  have hS : S.ShortExact :=
    Work.SSSR.cokernelComp_shortExact (Work.SSSR.bdryIncl f σ) (Work.SSSR.TIncl f σ)
  have hij : (ComplexShape.down ℕ).Rel m (m-1) :=
    ComplexShape.down_mk (j := m) (i := m-1) (by omega)
  have hnext : (ComplexShape.down ℕ).next m = m - 1 :=
    ComplexShape.next_eq' (ComplexShape.down ℕ) hij
  have hSg : S.g = snakeG f t σ := by with_unfolding_all rfl
  have hSf : S.f = snakeF f t σ := by with_unfolding_all rfl
  have hx3' : S.X₃.d m (m-1) x3 = 0 := by rw [← hnext]; exact hx3
  have hx2' : (S.g).f m x2 = x3 := by rw [hSg]; exact hx2
  have hx1' : (S.f).f (m-1) x1 = S.X₂.d m (m-1) x2 := by rw [hSf]; exact hx1
  have hδ := ShortComplex.ShortExact.δ_apply hS m (m-1) hij x3 hx3' x2 hx2' x1 hx1'
    ((ComplexShape.down ℕ).next (m-1)) rfl
  have hif : (Work.SSSR.pieceConnectingIsoIso f t σ m hm hi hj).hom = hS.δ m (m-1) hij := rfl
  have hconv3 : HomologicalComplex.homologyπ S.X₃ m
        (HomologicalComplex.cyclesMk S.X₃ x3 ((ComplexShape.down ℕ).next m) rfl hx3)
      = S.X₃.homologyπ m
          (S.X₃.cyclesMk x3 (m-1) (ComplexShape.next_eq' (ComplexShape.down ℕ) hij) hx3') := by
    congr 1
  change (Work.SSSR.pieceConnectingIsoIso f t σ m hm hi hj).hom
        (HomologicalComplex.homologyπ S.X₃ m
          (HomologicalComplex.cyclesMk S.X₃ x3 ((ComplexShape.down ℕ).next m) rfl hx3))
      = S.X₁.homologyπ (m-1)
          (S.X₁.cyclesMk x1 ((ComplexShape.down ℕ).next (m-1)) rfl hx1c)
  rw [hif, hconv3]
  simp only [forget2_Ab_hom_apply] at hδ
  refine hδ.trans ?_
  congr 1

set_option backward.isDefEq.respectTransparency false

/-! ## The last-face isomorphism on a class -/

/-- The `hom`-direction of `Work.SSSR.pieceBdryHornIsoIso` on the explicit element
`(bdryHornProj f σ) ((lastFaceChain f t σ) y0)`. -/
lemma pieceBdryHornIsoIso_hom_apply {X Y : SSet.{0}} (f : X ⟶ Y) (t n : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y)
    (y0 : (Work.SSSR.sCC R (Work.SSSR.pullAlong f
      (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).X n) :
    (Work.SSSR.pieceBdryHornIsoIso f t σ).hom.f n
        ((Work.SSSR.bdryHornProj f σ).f n ((Work.SSSR.lastFaceChain f t σ).f n y0))
      = (cokernel.π (Work.SSSR.TIncl f
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).f n y0 := by
  have hkey : cokernel.π (Work.SSSR.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
      ≫ (Work.SSSR.pieceBdryHornIsoIso f t σ).inv
      = Work.SSSR.lastFaceChain f t σ ≫ Work.SSSR.bdryHornProj (R := R) f σ :=
    Work.SSSR.pieceBdryHornIsoIso_inv f t σ
  have hkey2 : cokernel.π (Work.SSSR.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
      = Work.SSSR.lastFaceChain f t σ ≫ Work.SSSR.bdryHornProj (R := R) f σ
          ≫ (Work.SSSR.pieceBdryHornIsoIso f t σ).hom := by
    have h2 : cokernel.π (Work.SSSR.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
        ≫ ((Work.SSSR.pieceBdryHornIsoIso (R := R) f t σ).inv ≫ (Work.SSSR.pieceBdryHornIsoIso f t σ).hom)
        = cokernel.π (Work.SSSR.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) := by
      rw [Iso.inv_hom_id, Category.comp_id]
    rw [← h2, ← Category.assoc, hkey, Category.assoc]
  rw [hkey2]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl



end StepAux

end

end Work.SSSR
