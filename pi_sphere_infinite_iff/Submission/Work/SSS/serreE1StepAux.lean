import Mathlib
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.iotaTBdryHorn
import Submission.Work.SSS.pieceBdryHornIsoIso_inv

/-!
# Auxiliary homological lemmas for the induction step `serreE1PieceIso_iota_step`

Elementary lemmas relating the degree transport `castElem` of
`Submission/Work/SSS/serreE1PieceIotaDefs.lean` to chain maps, cycles and homology classes, the
computations of `Work.SSS.iotaT` / `Work.SSS.iotaF` on generators, the two explicit chain maps of
the short exact sequence of the σ-descent, and the two computations of the connecting maps
`Work.SSS.pieceConnectingIsoIso` and `Work.SSS.pieceBdryHornIsoIso` on a class.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

namespace StepAux

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## `castElem` -/

/-- The transport of an element of a chain complex along an equality of degrees is natural for
chain maps. -/
lemma castElem_map {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j)
    (x : K.X i) : castElem L h ((φ.f i) x) = (φ.f j) (castElem K h x) := by
  subst h
  simp [castElem]

lemma castElem_zsmul {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j) (c : ℤ)
    (x : K.X i) : castElem K h (c • x) = c • castElem K h x := by
  subst h
  simp [castElem]

lemma castElem_add {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j) (x y : K.X i) :
    castElem K h (x + y) = castElem K h x + castElem K h y := by
  subst h
  simp [castElem]

lemma castElem_symm {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j) (x : K.X i) :
    castElem K h.symm (castElem K h x) = x := by
  subst h
  simp [castElem]

lemma castElem_trans {K : ChainComplex (ModuleCat ℤ) ℕ} {i j k : ℕ} (h : i = j) (h' : j = k)
    (x : K.X i) : castElem K h' (castElem K h x) = castElem K (h.trans h') x := by
  subst h; subst h'
  simp [castElem]

lemma castElem_zero {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j) :
    castElem K h (0 : K.X i) = 0 := by
  subst h; simp [castElem]

/-- Element-level naturality of degree transport for a chain map, in the `sCC` spelling. -/
lemma sCCMap_castElem {X Y : SSet.{0}} (φ : X ⟶ Y) {i j : ℕ} (h : i = j)
    (x : (Work.SSS.sCC X).X i) :
    (Work.SSS.sCCMap φ).f j (Work.SSS.castElem (Work.SSS.sCC X) h x)
      = Work.SSS.castElem (Work.SSS.sCC Y) h ((Work.SSS.sCCMap φ).f i x) := by
  subst h
  simp [Work.SSS.castElem]

/-- Composition of chain maps applied to an element. -/
lemma sCCMap_comp_apply {X Y Z : SSet.{0}} (g : X ⟶ Y) (k : Y ⟶ Z) {n : ℕ}
    (x : (Work.SSS.sCC X).X n) :
    (Work.SSS.sCCMap k).f n ((Work.SSS.sCCMap g).f n x) = (Work.SSS.sCCMap (g ≫ k)).f n x := by
  rw [Work.SSS.sCCMap_comp']; rfl

/-! ## `castCycles` -/

/-- Transport of an element of the cycles of a chain complex along an equality of degrees. -/
def castCycles (K : ChainComplex (ModuleCat ℤ) ℕ) {i j : ℕ} (h : i = j) (x : K.cycles i) :
    K.cycles j :=
  h ▸ x

lemma castCycles_self (K : ChainComplex (ModuleCat ℤ) ℕ) {i : ℕ} (h : i = i) (x : K.cycles i) :
    castCycles K h x = x := by
  rw [Subsingleton.elim h rfl]
  simp [castCycles]

lemma castCycles_map {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ} (h : i = j)
    (x : K.cycles i) :
    HomologicalComplex.cyclesMap φ j (castCycles K h x)
      = castCycles L h (HomologicalComplex.cyclesMap φ i x) := by
  subst h
  simp [castCycles]

lemma castCycles_castCycles {K : ChainComplex (ModuleCat ℤ) ℕ} {i j k : ℕ} (h : i = j) (h' : j = k)
    (x : K.cycles i) : castCycles K h' (castCycles K h x) = castCycles K (h.trans h') x := by
  subst h; subst h'
  simp [castCycles]

/-! ## Cycles, homology classes and degree transport -/

lemma iCycles_cyclesMk (K : ChainComplex (ModuleCat ℤ) ℕ) {i : ℕ}
    (j : ℕ) (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0) :
    K.iCycles i (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) x j hj hx

lemma iCycles_castCycles (K : ChainComplex (ModuleCat ℤ) ℕ) {i j : ℕ} (h : i = j)
    (z : K.cycles i) : K.iCycles j (castCycles K h z) = castElem K h (K.iCycles i z) := by
  subst h; rfl

/-- `homologyMap` on a class, elementwise. -/
lemma homologyMap_homologyπ {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (i : ℕ)
    (x : K.cycles i) :
    (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) x)
      = (L.homologyπ i) ((HomologicalComplex.cyclesMap φ i) x) := by
  have h := HomologicalComplex.homologyπ_naturality φ i
  exact congrArg (fun (f : K.cycles i ⟶ L.homology i) => f x) h

/-- The transport of a homology class along an equality of degrees. -/
lemma eqToIso_homologyπ {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h : i = j)
    (x : K.cycles i) :
    (eqToIso (congrArg (fun m => K.homology m) h)).hom ((K.homologyπ i) x)
      = (K.homologyπ j) (castCycles K h x) := by
  subst h
  simp [castCycles]

lemma cyclesMap_cyclesMk {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i : ℕ}
    (j : ℕ) (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0)
    (hy : L.d i j (φ.f i x) = 0) :
    HomologicalComplex.cyclesMap φ i (K.cyclesMk x j hj hx) = L.cyclesMk (φ.f i x) j hj hy := by
  have hcm : L.iCycles i (HomologicalComplex.cyclesMap φ i (K.cyclesMk x j hj hx)) = φ.f i x := by
    have hh := congrArg (fun (g : K.cycles i ⟶ L.X i) => g (K.cyclesMk x j hj hx))
      (HomologicalComplex.cyclesMap_i (φ := φ) (i := i))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    rw [iCycles_cyclesMk K j hj x hx] at hh
    exact hh
  refine (Preadditive.mono_iff_injective (L.iCycles i)).1 inferInstance ?_
  exact hcm.trans (iCycles_cyclesMk L j hj (φ.f i x) hy).symm

/-- `cyclesMk` does not depend on the chosen proof of cyclicity. -/
lemma cyclesMk_proof_irrel (K : ChainComplex (ModuleCat ℤ) ℕ) {i : ℕ}
    (j : ℕ) (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx hx' : K.d i j x = 0) :
    K.cyclesMk x j hj hx = K.cyclesMk x j hj hx' := by
  unfold HomologicalComplex.cyclesMk
  congr 1

/-- `cyclesMk` does not depend on the description of the target degree. -/
lemma cyclesMk_congr (K : ChainComplex (ModuleCat ℤ) ℕ) {i : ℕ}
    (j : ℕ) (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i) (hx : K.d i j x = 0)
    (j' : ℕ) (hj' : (ComplexShape.down ℕ).next i = j') (hx' : K.d i j' x = 0) :
    K.cyclesMk x j hj hx = K.cyclesMk x j' hj' hx' := by
  unfold HomologicalComplex.cyclesMk
  congr 1

/-- Transport of the cyclicity of an element along a change of the target degree. -/
lemma d_eq_zero_congr (K : ChainComplex (ModuleCat ℤ) ℕ) {i j j' : ℕ}
    (h : j' = j) (x : K.X i) (hx : K.d i j x = 0) : K.d i j' x = 0 := by
  subst h
  exact hx


/-- Stripping the `forget₂ (ModuleCat ℤ) Ab` from the element-level description. -/
lemma forget2_Ab_hom_apply {M N : ModuleCat ℤ} (f : M ⟶ N) (x : M) :
    (ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map f)) x = (ConcreteCategory.hom f) x :=
  rfl

lemma castElem_irrel {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ} (h h' : i = j) (x : K.X i) :
    castElem K h x = castElem K h' x := by
  rw [Subsingleton.elim h h']

lemma castElem_self {K : ChainComplex (ModuleCat ℤ) ℕ} {i : ℕ} (h : i = i) (x : K.X i) :
    castElem K h x = x := by
  rw [Subsingleton.elim h rfl]; simp [castElem]

/-- The differential at a degree is the differential at a propositionally equal degree, up to the
degree transport. -/
lemma d_eq_castElem (K : ChainComplex (ModuleCat ℤ) ℕ) {i j j' : ℕ} (h : j = j') (x : K.X i) :
    K.d i j' x = castElem K h (K.d i j x) := by
  subst h
  simp [castElem]

/-- `cyclesMk` is compatible with scalar multiplication. -/
lemma cyclesMk_zsmul (K : ChainComplex (ModuleCat ℤ) ℕ) {i : ℕ} (j : ℕ)
    (hj : (ComplexShape.down ℕ).next i = j) (c : ℤ) (x : K.X i)
    (hx : K.d i j x = 0) (hxc : K.d i j (c • x) = 0) :
    K.cyclesMk (c • x) j hj hxc = c • K.cyclesMk x j hj hx := by
  apply (Preadditive.mono_iff_injective (K.iCycles i)).1 inferInstance
  simp only [forget2_Ab_hom_apply]
  rw [map_zsmul, iCycles_cyclesMk K j hj x hx, iCycles_cyclesMk K j hj (c • x) hxc]

/-- `castCycles` of `cyclesMk` is `cyclesMk` of the transported element. -/
lemma castCycles_cyclesMk (K : ChainComplex (ModuleCat ℤ) ℕ) {i i' j j' : ℕ} (h : i = i')
    (hj : (ComplexShape.down ℕ).next i = j) (hj' : (ComplexShape.down ℕ).next i' = j')
    (x : K.X i) (hx : K.d i j x = 0)
    (hx' : K.d i' j' (castElem K h x) = 0) :
    castCycles K h (K.cyclesMk x j hj hx) = K.cyclesMk (castElem K h x) j' hj' hx' := by
  subst h
  exact cyclesMk_congr K j hj x hx j' hj' hx'

/-! ## The value of `iotaT` / `iotaF` on a generator -/

/-- The morphism `eltHom z` evaluated at `1` is `z`. -/
lemma eltHom_apply_one {M : ModuleCat ℤ} (z : M) : (Work.SSS.eltHom z).hom 1 = z := by
  rw [Work.SSS.eltHom, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one]

/-- The value of `iotaT` on the generator of a simplex is the Eilenberg–Zilber lift. -/
lemma iotaT_gen_apply (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋q⦌) :
    (Work.SSS.iotaT p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) P b σ h q)
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1)
      = Work.SSS.iotaTLift p hfib P b σ h q τ := by
  have h1 := Work.SSS.iotaT_gen (p := p) (Work.SSS.liftFam p hfib)
    (Work.SSS.liftFam_proj p hfib) P b σ h q τ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
      (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).X (P+q)) => g.hom (1 : ℤ)) h1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [Work.SSS.eltHom, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one] at h2
  simpa only [Work.SSS.iotaTLift] using h2

/-- The value of `iotaF` on the generator of a simplex: `ι_σ τ` is the class of the Eilenberg–Zilber
lift `iotaTLift`. -/
lemma iotaF_gen_apply (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋q⦌) :
    (Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) P b σ h q).hom
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1)
      = (Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (P+q)
          (Work.SSS.iotaTLift p hfib P b σ h q τ) := by
  have h1 := Work.SSS.iotaF_gen (p := p) (Work.SSS.liftFam p hfib)
    (Work.SSS.liftFam_proj p hfib) P b σ h q τ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
      (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).X (P+q)) => g.hom (1 : ℤ)) h1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [Work.SSS.eltHom, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one] at h2
  simpa only [Work.SSS.iotaTLift] using h2

/-! ## The two explicit chain maps of the σ-descent -/

/-- The inclusion `C(∂T_σ) ⟶ C(T_σ)` is a monomorphism. -/
instance mono_TIncl {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Mono (Work.SSS.TIncl f σ) := by
  change Mono (Work.SSS.sChainMap ℤ (Work.SSS.bdryAlong f σ).ι)
  exact Work.SSS.sChainMap_mono ℤ _ inferInstance

/-- The composite `bdryIncl ≫ TIncl` is the horn inclusion. -/
lemma bdryIncl_comp_TIncl {X Y : SSet.{0}} (f : X ⟶ Y) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) :
    Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ
      = Work.SSS.sCCMap (Work.SSS.pieceHorn f σ).ι :=
  (Work.SSS.sCCMap_pieceHorn_ι_eq f σ).symm

/-- The first map `C(T_σ)/C(Λ) ⟶ C(T_σ)/C(∂T_σ)` of the σ-descent. -/
noncomputable def snakeG {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    cokernel (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ) ⟶ cokernel (Work.SSS.TIncl f σ) :=
  cokernel.map (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ) (Work.SSS.TIncl f σ)
    (Work.SSS.bdryIncl f σ) (𝟙 _) (by rw [Category.comp_id])

/-- The second map `C(∂T_σ)/C(Λ) ⟶ C(T_σ)/C(Λ)` of the σ-descent. -/
noncomputable def snakeF {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    cokernel (Work.SSS.bdryIncl f σ) ⟶ cokernel (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ) :=
  cokernel.map (Work.SSS.bdryIncl f σ) (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ)
    (𝟙 _) (Work.SSS.TIncl f σ) (by rw [Category.id_comp])

/-- The projection formula for `snakeG`. -/
lemma snakeG_π {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    cokernel.π (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ) ≫ snakeG f t σ
      = 𝟙 (Work.SSS.sCC (Work.SSS.pullAlong f σ)) ≫ cokernel.π (Work.SSS.TIncl f σ) := by
  rw [snakeG, cokernel.map, cokernel.π_desc]

/-- The projection formula for `snakeF`. -/
lemma snakeF_π {X Y : SSet.{0}} (f : X ⟶ Y) (t : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y) :
    cokernel.π (Work.SSS.bdryIncl f σ) ≫ snakeF f t σ
      = Work.SSS.TIncl f σ ≫ cokernel.π (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ) := by
  rw [snakeF, cokernel.map, cokernel.π_desc]

/-! ## The connecting map of the σ-descent on a class -/

/-- **The connecting map `Work.SSS.pieceConnectingIsoIso` on a class**, computed by
`ShortComplex.ShortExact.δ_apply`.  In the notation of `serreE1PieceIotaDefs`,
`T_σ = pullAlong f σ`, `Λ = pieceHorn f σ`, and `snakeG`, `snakeF` are the two chain maps of the
short exact sequence `C(Λ) ⊆ C(∂T_σ) ⊆ C(T_σ)`.  Given elements `x₃`, `x₂`, `x₁` of the three
cokernels with `snakeG x₂ = x₃` and `snakeF x₁ = d_{X₂} x₂`, the connecting map sends the class of
the cycle `x₃` to the class of the cycle `x₁`. -/
theorem eA_apply {X Y : SSet.{0}} (f : X ⟶ Y) (t m : ℕ) (hm : 1 ≤ m)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y)
    (hi : IsZero ((Work.SSS.pieceHornC f σ).homology m))
    (hj : IsZero ((Work.SSS.pieceHornC f σ).homology (m-1)))
    (x3 : (Work.SSS.pieceAlong f σ).X m)
    (hx3 : (Work.SSS.pieceAlong f σ).d m ((ComplexShape.down ℕ).next m) x3 = 0)
    (x2 : (cokernel (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ)).X m)
    (hx2 : (snakeG f t σ).f m x2 = x3)
    (x1 : (Work.SSS.pieceBdryHornC f σ).X (m-1))
    (hx1 : (snakeF f t σ).f (m-1) x1
            = (cokernel (Work.SSS.bdryIncl f σ ≫ Work.SSS.TIncl f σ)).d m (m-1) x2)
    (hx1c : (Work.SSS.pieceBdryHornC f σ).d (m-1) ((ComplexShape.down ℕ).next (m-1)) x1 = 0) :
    (Work.SSS.pieceConnectingIsoIso f t σ m hm hi hj).hom
        (HomologicalComplex.homologyπ (Work.SSS.pieceAlong f σ) m
          (HomologicalComplex.cyclesMk (Work.SSS.pieceAlong f σ) x3
            ((ComplexShape.down ℕ).next m) rfl hx3))
      = HomologicalComplex.homologyπ (Work.SSS.pieceBdryHornC f σ) (m-1)
          (HomologicalComplex.cyclesMk (Work.SSS.pieceBdryHornC f σ) x1
            ((ComplexShape.down ℕ).next (m-1)) rfl hx1c) := by
  haveI : Mono (Work.SSS.TIncl f σ) := mono_TIncl f σ
  set S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    (kernelCokernelCompSequence.snakeInput (Work.SSS.bdryIncl f σ) (Work.SSS.TIncl f σ)).L₃ with hSdef
  have hS : S.ShortExact :=
    Work.SSS.cokernelComp_shortExact (Work.SSS.bdryIncl f σ) (Work.SSS.TIncl f σ)
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
  have hif : (Work.SSS.pieceConnectingIsoIso f t σ m hm hi hj).hom = hS.δ m (m-1) hij := rfl
  have hconv3 : HomologicalComplex.homologyπ S.X₃ m
        (HomologicalComplex.cyclesMk S.X₃ x3 ((ComplexShape.down ℕ).next m) rfl hx3)
      = S.X₃.homologyπ m
          (S.X₃.cyclesMk x3 (m-1) (ComplexShape.next_eq' (ComplexShape.down ℕ) hij) hx3') := by
    congr 1
  change (Work.SSS.pieceConnectingIsoIso f t σ m hm hi hj).hom
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

/-- The `hom`-direction of `Work.SSS.pieceBdryHornIsoIso` on the explicit element
`(bdryHornProj f σ) ((lastFaceChain f t σ) y0)`. -/
lemma pieceBdryHornIsoIso_hom_apply {X Y : SSet.{0}} (f : X ⟶ Y) (t n : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y)
    (y0 : (Work.SSS.sCC (Work.SSS.pullAlong f
      (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).X n) :
    (Work.SSS.pieceBdryHornIsoIso f t σ).hom.f n
        ((Work.SSS.bdryHornProj f σ).f n ((Work.SSS.lastFaceChain f t σ).f n y0))
      = (cokernel.π (Work.SSS.TIncl f
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).f n y0 := by
  have hkey : cokernel.π (Work.SSS.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
      ≫ (Work.SSS.pieceBdryHornIsoIso f t σ).inv
      = Work.SSS.lastFaceChain f t σ ≫ Work.SSS.bdryHornProj f σ :=
    Work.SSS.pieceBdryHornIsoIso_inv f t σ
  have hkey2 : cokernel.π (Work.SSS.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
      = Work.SSS.lastFaceChain f t σ ≫ Work.SSS.bdryHornProj f σ
          ≫ (Work.SSS.pieceBdryHornIsoIso f t σ).hom := by
    have h2 : cokernel.π (Work.SSS.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
        ≫ ((Work.SSS.pieceBdryHornIsoIso f t σ).inv ≫ (Work.SSS.pieceBdryHornIsoIso f t σ).hom)
        = cokernel.π (Work.SSS.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) := by
      rw [Iso.inv_hom_id, Category.comp_id]
    rw [← h2, ← Category.assoc, hkey, Category.assoc]
  rw [hkey2]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl



/-- **The isomorphism `Work.SSS.pieceBdryHornIsoIso` on a class**: its `.hom` sends the class of
`(bdryHornProj f σ) ((lastFaceChain f t σ) y)` to the class of `(cokernel.π (TIncl f σ')) y`, where
`σ' = d_last σ`.  This is the `hom`-direction of `Work.SSS.pieceBdryHornIsoIso_inv`. -/
theorem eC_apply {X Y : SSet.{0}} (f : X ⟶ Y) (t n : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Y)
    (y0 : (Work.SSS.sCC (Work.SSS.pullAlong f
      (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).X n)
    (hL : (Work.SSS.pieceBdryHornC f σ).d n ((ComplexShape.down ℕ).next n)
        ((Work.SSS.bdryHornProj f σ).f n ((Work.SSS.lastFaceChain f t σ).f n y0)) = 0)
    (hR : (Work.SSS.pieceAlong f
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)).d n
        ((ComplexShape.down ℕ).next n)
        ((cokernel.π (Work.SSS.TIncl f
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).f n y0) = 0) :
    (HomologicalComplex.homologyMap (Work.SSS.pieceBdryHornIsoIso f t σ).hom n)
        (HomologicalComplex.homologyπ (Work.SSS.pieceBdryHornC f σ) n
          (HomologicalComplex.cyclesMk (Work.SSS.pieceBdryHornC f σ)
            ((Work.SSS.bdryHornProj f σ).f n ((Work.SSS.lastFaceChain f t σ).f n y0))
            ((ComplexShape.down ℕ).next n) rfl hL))
      = HomologicalComplex.homologyπ
          (Work.SSS.pieceAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) n
          (HomologicalComplex.cyclesMk
            (Work.SSS.pieceAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
            ((cokernel.π (Work.SSS.TIncl f
              (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).f n y0)
            ((ComplexShape.down ℕ).next n) rfl hR) := by
  rw [homologyMap_homologyπ]
  have hkey : cokernel.π (Work.SSS.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
      ≫ (Work.SSS.pieceBdryHornIsoIso f t σ).inv
      = Work.SSS.lastFaceChain f t σ ≫ Work.SSS.bdryHornProj f σ :=
    Work.SSS.pieceBdryHornIsoIso_inv f t σ
  have hkey2 : cokernel.π (Work.SSS.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
      = Work.SSS.lastFaceChain f t σ ≫ Work.SSS.bdryHornProj f σ
          ≫ (Work.SSS.pieceBdryHornIsoIso f t σ).hom := by
    have h2 : cokernel.π (Work.SSS.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
        ≫ ((Work.SSS.pieceBdryHornIsoIso f t σ).inv ≫ (Work.SSS.pieceBdryHornIsoIso f t σ).hom)
        = cokernel.π (Work.SSS.TIncl f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)) := by
      rw [Iso.inv_hom_id, Category.comp_id]
    rw [← h2, ← Category.assoc, hkey, Category.assoc]
  have hw : (Work.SSS.pieceBdryHornIsoIso f t σ).hom.f n
        ((Work.SSS.bdryHornProj f σ).f n ((Work.SSS.lastFaceChain f t σ).f n y0))
      = (cokernel.π (Work.SSS.TIncl f
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).f n y0 := by
    rw [hkey2]
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  have hcy : HomologicalComplex.cyclesMap (Work.SSS.pieceBdryHornIsoIso f t σ).hom n
        (HomologicalComplex.cyclesMk (Work.SSS.pieceBdryHornC f σ)
          ((Work.SSS.bdryHornProj f σ).f n ((Work.SSS.lastFaceChain f t σ).f n y0))
          ((ComplexShape.down ℕ).next n) rfl hL)
      = HomologicalComplex.cyclesMk
          (Work.SSS.pieceAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
          ((cokernel.π (Work.SSS.TIncl f
            (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).f n y0)
          ((ComplexShape.down ℕ).next n) rfl hR := by
    apply (Preadditive.mono_iff_injective
      ((Work.SSS.pieceAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)).iCycles n)).1
      inferInstance
    simp only [StepAux.forget2_Ab_hom_apply]
    have h := congrArg (fun (g : (Work.SSS.pieceBdryHornC f σ).cycles n ⟶
        (Work.SSS.pieceAlong f (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)).X n) =>
        g (HomologicalComplex.cyclesMk (Work.SSS.pieceBdryHornC f σ)
          ((Work.SSS.bdryHornProj f σ).f n ((Work.SSS.lastFaceChain f t σ).f n y0))
          ((ComplexShape.down ℕ).next n) rfl hL))
      (HomologicalComplex.cyclesMap_i (φ := (Work.SSS.pieceBdryHornIsoIso f t σ).hom) (i := n))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [StepAux.iCycles_cyclesMk (Work.SSS.pieceBdryHornC f σ) ((ComplexShape.down ℕ).next n) rfl
      ((Work.SSS.bdryHornProj f σ).f n ((Work.SSS.lastFaceChain f t σ).f n y0)) hL] at h
    rw [StepAux.iCycles_cyclesMk (Work.SSS.pieceAlong f
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))
        ((ComplexShape.down ℕ).next n) rfl
        ((cokernel.π (Work.SSS.TIncl f
          (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ))).f n y0) hR]
    rw [h, hw]
  rw [hcy]
end StepAux

end

end Work.SSS
