import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.grFMap
import Submission.Work.SSSR.coherentLiftDefs
import Submission.Work.SSSR.exists_coherentLiftFamily
import Submission.Work.SSSR.KunnethEZ.ezGen_boundary
import Submission.Work.SSSR.KunnethEZ.ezGen_map_fst
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory
noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The identity simplex `[id_P]` of `Δ[P]` (the fundamental `P`-simplex). -/
def stdIdSimplex (P : ℕ) : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) _⦋P⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk P))

variable (p : C(E, B))

/-- **The lift of the pullback `T_σ` induced by the lift family.**  Given a family `Φ` of lifts of
`pr₁ ≫ σ : Δ[P] ⊗ Sing F_{σ(v₀)} ⟶ Sing B` (with `Φ` lying over `pr₁ ≫ σ`), the pairing
`(pr₁, Φ)` factors through the pullback `T_σ = Δ[P] ×_{Sing B} Sing E`. -/
def ezSimplex
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.SSSR.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗
        sSing (Work.SSSR.StemsB.fibre p b)) ⟶ pullAlong (sSingP p) σ :=
  pullback.lift (SemiCartesianMonoidalCategory.fst _ _) (Φ P b σ h)
    (hproj P b σ h).symm

variable {p}

@[simp] lemma ezSimplex_fst
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.SSSR.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ezSimplex p Φ hproj P b σ h ≫ pullback.fst σ (sSingP p)
      = SemiCartesianMonoidalCategory.fst _ _ :=
  pullback.lift_fst _ _ _

@[simp] lemma ezSimplex_snd
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.SSSR.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ezSimplex p Φ hproj P b σ h ≫ pullback.snd σ (sSingP p) = Φ P b σ h :=
  pullback.lift_snd _ _ _

/-- The morphism `ℤ ⟶ M` sending `1` to an element `z` of a `ℤ`-module `M`. -/
def eltHom {M : ModuleCat R} (z : M) : (ModuleCat.of R R) ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M z)

/-- Postcomposition of `eltHom z` is `eltHom` of the image. -/
lemma eltHom_comp {M N : ModuleCat R} (z : M) (g : M ⟶ N) :
    eltHom z ≫ g = eltHom (g z) := by
  ext
  simp [eltHom, ModuleCat.ofHom, LinearMap.toSpanSingleton]

variable (p : C(E, B))

/-- **The chain-level `ι_σ`.**  For a simplex `τ` of the fibre `F_{σ(v₀)}` in degree `q`, the
element `ezGen P q [id_P] τ` of `C_{P+q}(Δ[P] ⊗ F)` is pushed into the pullback `T_σ` along
`ezSimplex_σ`; extended linearly in `τ`.  The result lives in degree `q + P` of `C_*(T_σ)`, i.e.
`iotaT σ` is a chain map of degree `P`. -/
def iotaT
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.SSSR.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) :
    (sCC R (sSing (Work.SSSR.StemsB.fibre p b))).X q ⟶ (sCC R (pullAlong (sSingP p) σ)).X (P + q) :=
  Sigma.desc (fun τ : (sSing (Work.SSSR.StemsB.fibre p b)) _⦋q⦌ =>
    eltHom ((sCCMap R (ezSimplex p Φ hproj P b σ h)).f (P + q)
      (Work.SSSR.Cohomology.Crux33.ezGen P q (SSet.stdSimplex.obj (SimplexCategory.mk P))
        (sSing (Work.SSSR.StemsB.fibre p b)) (stdIdSimplex P) τ)))

variable {p}

/-- The value of `iotaT` on a generator: the Eilenberg–Zilber shuffle chain of the fundamental
`P`-simplex of `Δ[P]` and `τ`, pushed into the pullback `T_σ`. -/
lemma iotaT_gen (Φ) (hproj) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) (τ : (sSing (Work.SSSR.StemsB.fibre p b)) _⦋q⦌) :
    (sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of R R) τ ≫
        iotaT p Φ hproj P b σ h q
      = eltHom ((sCCMap R (ezSimplex p Φ hproj P b σ h)).f (P + q)
          (Work.SSSR.Cohomology.Crux33.ezGen P q (SSet.stdSimplex.obj (SimplexCategory.mk P))
            (sSing (Work.SSSR.StemsB.fibre p b)) (stdIdSimplex P) τ)) :=
  Sigma.ι_desc _ _



/-- The projection `C(T_σ) ⟶ piece_σ` for an *arbitrary* simplex `σ` of the base (the
`nIndex`-indexed `Work.SSSR.pieceπ R` only applies to `σ = nIndexSigma Y d y`). -/
noncomputable def pieceπOf {X Y : SSet.{0}} (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) :
    sCC R (pullAlong f σ) ⟶ pieceAlong R f σ :=
  cokernel.π (sCCMap R (bdryAlong f σ).ι)

@[simp] lemma pieceπOf_eq {X Y : SSet.{0}} (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) :
    pieceπOf f σ = cokernel.π (sCCMap R (bdryAlong f σ).ι) := rfl

variable (p : C(E, B))

/-- **The σ-piece chain map `ι_σ`.**  The chain-level `iotaT`, which is a map of degree `P` into
`C_*(T_σ)`, followed by the projection to the σ-piece `piece_σ = C(T_σ)/C(∂T_σ)` (the face terms of
its boundary lie in `C(∂T_σ)`, so it becomes a genuine map of degree `P` of chain complexes). -/
def iotaF
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.SSSR.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) :
    (sCC R (sSing (Work.SSSR.StemsB.fibre p b))).X q
      ⟶ (pieceAlong R (sSingP p) σ).X (P + q) :=
  iotaT p Φ hproj P b σ h q ≫ (pieceπOf (sSingP p) σ).f (P + q)

variable {p}

/-- The value of `iotaF` on a generator: the shuffle chain of the fundamental `P`-simplex of
`Δ[P]` and `τ`, pushed into `T_σ` and projected into the σ-piece. -/
lemma iotaF_gen (Φ) (hproj) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) (τ : (sSing (Work.SSSR.StemsB.fibre p b)) _⦋q⦌) :
    (sSing (Work.SSSR.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of R R) τ ≫
        iotaF p Φ hproj P b σ h q
      = eltHom ((pieceπOf (sSingP p) σ).f (P + q)
          ((sCCMap R (ezSimplex p Φ hproj P b σ h)).f (P + q)
            (Work.SSSR.Cohomology.Crux33.ezGen P q (SSet.stdSimplex.obj (SimplexCategory.mk P))
              (sSing (Work.SSSR.StemsB.fibre p b)) (stdIdSimplex P) τ))) := by
  rw [iotaF, ← Category.assoc, iotaT_gen, eltHom_comp]

/-- The inclusion of the `i`-th face `T_{d_iσ} ⟶ T_σ` of the pullback, for `σ : Δ[Q+1] → Y`. -/
def pullFaceIncl {X Y : SSet.{0}} (f : X ⟶ Y) {Q : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (Q+1)) : SSet.{0}) ⟶ Y) (i : Fin (Q+2)) :
    pullAlong f (SSet.stdSimplex.δ (n := Q) i ≫ σ) ⟶ pullAlong f σ :=
  pullback.lift (pullback.fst _ _ ≫ SSet.stdSimplex.δ (n := Q) i) (pullback.snd _ _)
    (by rw [Category.assoc]; exact pullback.condition)

@[simp] lemma pullFaceIncl_fst {X Y : SSet.{0}} (f : X ⟶ Y) {Q : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (Q+1)) : SSet.{0}) ⟶ Y) (i : Fin (Q+2)) :
    pullFaceIncl f σ i ≫ pullback.fst σ f
      = pullback.fst (SSet.stdSimplex.δ (n := Q) i ≫ σ) f ≫ SSet.stdSimplex.δ (n := Q) i :=
  pullback.lift_fst _ _ _

@[simp] lemma pullFaceIncl_snd {X Y : SSet.{0}} (f : X ⟶ Y) {Q : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (Q+1)) : SSet.{0}) ⟶ Y) (i : Fin (Q+2)) :
    pullFaceIncl f σ i ≫ pullback.snd σ f
      = pullback.snd (SSet.stdSimplex.δ (n := Q) i ≫ σ) f :=
  pullback.lift_snd _ _ _



variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The coherent lift family of a Serre fibration (`Work.SSSR.exists_coherentLiftFamily`), chosen
once and for all. -/
noncomputable def liftFam (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) :
    ∀ (n : ℕ) (b' : B)
      (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
      (sigmaVert σ = b') →
      (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
        sSing (Work.SSSR.StemsB.fibre p b')) ⟶ sSing E) :=
  fun n b' σ h => Classical.choose (Work.SSSR.exists_coherentLiftFamily p hfib b') n b' σ h

/-- The chosen lift family lies over `pr₁ ≫ σ`. -/
theorem liftFam_proj (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (n : ℕ) (b' : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b') :
    liftFam p hfib n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ :=
  (Classical.choose_spec (Work.SSSR.exists_coherentLiftFamily p hfib b')).1 n b' σ h

/-- The chosen lift family restricts to the fibre inclusion on `{v₀} ⊗ Sing F`. -/
theorem liftFam_vert (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (n : ℕ) (b' : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b') :
    vertIncl p b' n ≫ liftFam p hfib n b' σ h = sSingP (Work.SSSR.StemsB.fibreIncl p b') :=
  (Classical.choose_spec (Work.SSSR.exists_coherentLiftFamily p hfib b')).2.1 n b' σ h

/-- The chosen lift family is coherent under the cofaces `δ i` with `i ≠ 0`. -/
theorem liftFam_coh (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (n : ℕ) (b' : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b') (i : Fin (n+2)) (hi : i ≠ 0)
    (h' : sigmaVert (SSet.stdSimplex.δ (n := n) i ≫ σ) = b') :
    (SSet.stdSimplex.δ (n := n) i ⊗ₘ 𝟙 (sSing (Work.SSSR.StemsB.fibre p b')))
        ≫ liftFam p hfib (n+1) b' σ h
      = liftFam p hfib n b' (SSet.stdSimplex.δ (n := n) i ≫ σ) h' :=
  (Classical.choose_spec (Work.SSSR.exists_coherentLiftFamily p hfib b')).2.2 n b' σ h i hi h'


end

end Work.SSSR
