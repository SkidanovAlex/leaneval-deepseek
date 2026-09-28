import Mathlib
import Submission.Work.SSS.serreE1Defs
import Submission.Work.SSS.grFMap
import Submission.Work.SSS.coherentLiftDefs
import Submission.Work.SSS.exists_coherentLiftFamily
import Submission.Work.KunnethEZ.ezGen_boundary
import Submission.Work.KunnethEZ.ezGen_map_fst
import Submission.Work.KunnethEZ.ezGen_map_snd

/-!
# The Eilenberg–Zilber chain map `ι_σ` of a simplex of the base

For a map `p : E → B` (a Serre fibration in the applications), a simplex `σ : Δ[P] ⟶ Sing B` of
the base and a *coherent lift family* `Φ` (`Work.SSS.exists_coherentLiftFamily`), this file builds
the Eilenberg–Zilber chain map

  `ι_σ : C_*(F_{σ(v₀)}) ⟶ (C(T_σ)/C(∂T_σ))⟦P⟧`

of `REFS/NOTES_LEAD_SSS.md` §1(c): on a simplex `τ` of the fibre it is the shuffle chain
`ezGen P q [id_P] τ` of the fundamental `P`-simplex of `Δ[P]` and `τ`, pushed into the pullback
`T_σ = Δ[P] ×_{Sing B} Sing E` along the lift `ezSimplex_σ` of `pr₁ ≫ σ`, and then projected to the
σ-piece `C(T_σ)/C(∂T_σ)`.

The degree convention is *not* the naive one: `(ι_σ)` in chain degree `q` is a map
`C_q(F) ⟶ (piece_σ)_{q+P}` (a chain map of degree `P`, encoded below by the `⟦P⟧`-shifted target
`pieceShift`).  Its two key properties are

* `Work.SSS.iotaF_d` — `ι_σ` is a chain map (`∂ ι_σ = (-1)^P ι_σ ∂`); the face terms of the
  Eilenberg–Zilber boundary formula lie in `C(∂T_σ)` and die in the quotient;
* `Work.SSS.iotaT_boundary` — the boundary formula *before* quotienting,
  `∂ (ι_σ τ) = Σ_i (-1)^i (face-i of ι_σ τ) + (-1)^P ι_σ (∂τ)`, which is what the computation of
  the first differential `d¹` of the Serre filtration uses.

The `i = 0` face has base point `σ(v₁)` (`Work.SSS.IotaFace`), so the comparison with the
coordinate `ι_{d₀σ}` requires the fibre transport along the edge `σ|_{[v₀,v₁]}`; this is handled by
the separate statement `Work.SSS.iotaT_face_zero` (see `REFS/NOTES_LEAD_SSS_d1.md`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSS

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
          sSing (Work.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗
        sSing (Work.StemsB.fibre p b)) ⟶ pullAlong (sSingP p) σ :=
  pullback.lift (SemiCartesianMonoidalCategory.fst _ _) (Φ P b σ h)
    (hproj P b σ h).symm

variable {p}

@[simp] lemma ezSimplex_fst
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.StemsB.fibre p b')) ⟶ sSing E))
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
          sSing (Work.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) :
    ezSimplex p Φ hproj P b σ h ≫ pullback.snd σ (sSingP p) = Φ P b σ h :=
  pullback.lift_snd _ _ _

/-- The morphism `ℤ ⟶ M` sending `1` to an element `z` of a `ℤ`-module `M`. -/
def eltHom {M : ModuleCat ℤ} (z : M) : (ModuleCat.of ℤ ℤ) ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M z)

/-- Postcomposition of `eltHom z` is `eltHom` of the image. -/
lemma eltHom_comp {M N : ModuleCat ℤ} (z : M) (g : M ⟶ N) :
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
          sSing (Work.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) :
    (sCC (sSing (Work.StemsB.fibre p b))).X q ⟶ (sCC (pullAlong (sSingP p) σ)).X (P + q) :=
  Sigma.desc (fun τ : (sSing (Work.StemsB.fibre p b)) _⦋q⦌ =>
    eltHom ((sCCMap (ezSimplex p Φ hproj P b σ h)).f (P + q)
      (Work.Cohomology.Crux33.ezGen P q (SSet.stdSimplex.obj (SimplexCategory.mk P))
        (sSing (Work.StemsB.fibre p b)) (stdIdSimplex P) τ)))

variable {p}

/-- The value of `iotaT` on a generator: the Eilenberg–Zilber shuffle chain of the fundamental
`P`-simplex of `Δ[P]` and `τ`, pushed into the pullback `T_σ`. -/
lemma iotaT_gen (Φ) (hproj) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) (τ : (sSing (Work.StemsB.fibre p b)) _⦋q⦌) :
    (sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ ≫
        iotaT p Φ hproj P b σ h q
      = eltHom ((sCCMap (ezSimplex p Φ hproj P b σ h)).f (P + q)
          (Work.Cohomology.Crux33.ezGen P q (SSet.stdSimplex.obj (SimplexCategory.mk P))
            (sSing (Work.StemsB.fibre p b)) (stdIdSimplex P) τ)) :=
  Sigma.ι_desc _ _



/-- The projection `C(T_σ) ⟶ piece_σ` for an *arbitrary* simplex `σ` of the base (the
`nIndex`-indexed `Work.SSS.pieceπ` only applies to `σ = nIndexSigma Y d y`). -/
noncomputable def pieceπOf {X Y : SSet.{0}} (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) :
    sCC (pullAlong f σ) ⟶ pieceAlong f σ :=
  cokernel.π (sCCMap (bdryAlong f σ).ι)

@[simp] lemma pieceπOf_eq {X Y : SSet.{0}} (f : X ⟶ Y) {P : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Y) :
    pieceπOf f σ = cokernel.π (sCCMap (bdryAlong f σ).ι) := rfl

variable (p : C(E, B))

/-- **The σ-piece chain map `ι_σ`.**  The chain-level `iotaT`, which is a map of degree `P` into
`C_*(T_σ)`, followed by the projection to the σ-piece `piece_σ = C(T_σ)/C(∂T_σ)` (the face terms of
its boundary lie in `C(∂T_σ)`, so it becomes a genuine map of degree `P` of chain complexes). -/
def iotaF
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
        (sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          sSing (Work.StemsB.fibre p b')) ⟶ sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
        (h : sigmaVert σ = b'),
        Φ n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B) (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) :
    (sCC (sSing (Work.StemsB.fibre p b))).X q
      ⟶ (pieceAlong (sSingP p) σ).X (P + q) :=
  iotaT p Φ hproj P b σ h q ≫ (pieceπOf (sSingP p) σ).f (P + q)

variable {p}

/-- The value of `iotaF` on a generator: the shuffle chain of the fundamental `P`-simplex of
`Δ[P]` and `τ`, pushed into `T_σ` and projected into the σ-piece. -/
lemma iotaF_gen (Φ) (hproj) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b) (q : ℕ) (τ : (sSing (Work.StemsB.fibre p b)) _⦋q⦌) :
    (sSing (Work.StemsB.fibre p b)).ιChainComplex (R := ModuleCat.of ℤ ℤ) τ ≫
        iotaF p Φ hproj P b σ h q
      = eltHom ((pieceπOf (sSingP p) σ).f (P + q)
          ((sCCMap (ezSimplex p Φ hproj P b σ h)).f (P + q)
            (Work.Cohomology.Crux33.ezGen P q (SSet.stdSimplex.obj (SimplexCategory.mk P))
              (sSing (Work.StemsB.fibre p b)) (stdIdSimplex P) τ))) := by
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



/-! ## The lift family of a Serre fibration, extracted from `exists_coherentLiftFamily` -/

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The coherent lift family of a Serre fibration (`Work.SSS.exists_coherentLiftFamily`), chosen
once and for all. -/
noncomputable def liftFam (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) :
    ∀ (n : ℕ) (b' : B)
      (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B),
      (sigmaVert σ = b') →
      (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
        sSing (Work.StemsB.fibre p b')) ⟶ sSing E) :=
  fun n b' σ h => Classical.choose (Work.SSS.exists_coherentLiftFamily p hfib b') n b' σ h

/-- The chosen lift family lies over `pr₁ ≫ σ`. -/
theorem liftFam_proj (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (n : ℕ) (b' : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b') :
    liftFam p hfib n b' σ h ≫ sSingP p = SemiCartesianMonoidalCategory.fst _ _ ≫ σ :=
  (Classical.choose_spec (Work.SSS.exists_coherentLiftFamily p hfib b')).1 n b' σ h

/-- The chosen lift family restricts to the fibre inclusion on `{v₀} ⊗ Sing F`. -/
theorem liftFam_vert (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (n : ℕ) (b' : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b') :
    vertIncl p b' n ≫ liftFam p hfib n b' σ h = sSingP (Work.StemsB.fibreIncl p b') :=
  (Classical.choose_spec (Work.SSS.exists_coherentLiftFamily p hfib b')).2.1 n b' σ h

/-- The chosen lift family is coherent under the cofaces `δ i` with `i ≠ 0`. -/
theorem liftFam_coh (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (n : ℕ) (b' : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⟶ sSing B)
    (h : sigmaVert σ = b') (i : Fin (n+2)) (hi : i ≠ 0)
    (h' : sigmaVert (SSet.stdSimplex.δ (n := n) i ≫ σ) = b') :
    (SSet.stdSimplex.δ (n := n) i ⊗ₘ 𝟙 (sSing (Work.StemsB.fibre p b')))
        ≫ liftFam p hfib (n+1) b' σ h
      = liftFam p hfib n b' (SSet.stdSimplex.δ (n := n) i ≫ σ) h' :=
  (Classical.choose_spec (Work.SSS.exists_coherentLiftFamily p hfib b')).2.2 n b' σ h i hi h'


end

/-! ## Two identities of `grFMap.lean` used by the assembly -/

/-- `mapPhiY` followed by `mapPsi` is the coprojection of the `y`-summand. -/
lemma mapPhiY_comp_mapPsi {X Y : SSet.{0}} (f : X ⟶ Y) (d : ℕ) (y : nIndex Y d) :
    mapPhiY f d y ≫ mapPsi f d =
      Sigma.ι (fun y : nIndex Y d => pieceAlong f (nIndexSigma Y d y)) y := by
  have h : Sigma.ι (fun y : nIndex Y d => pieceAlong f (nIndexSigma Y d y)) y ≫ mapPhi f d
      = mapPhiY f d y := by
    rw [mapPhi]; exact Sigma.ι_desc _ y
  rw [← h, Category.assoc, mapPhi_comp_mapPsi, Category.comp_id]

/-- **The Eilenberg–Zilber section on a chain of a σ-piece.**  For a nondegenerate simplex `y` of
the base and a chain `w` of the pullback `T_y`, the `Theta`-section of the chain pushed forward by
the second projection `T_y ⟶ X` is the class of `w` in the `y`-summand of the coproduct.
This is the bridge that turns the `σ`-component of `d¹` into the corresponding component of the
σ-piece
(used in the computation of the first differential, `REFS/NOTES_LEAD_SSS_d1.md` §1.3). -/
lemma sCCMap_sndToR_comp_Theta {X Y : SSet.{0}} (f : X ⟶ Y) (d : ℕ) (y : nIndex Y d) :
    sCCMap (sndToR f y) ≫ Theta f d =
      pieceπ f d y ≫ Sigma.ι (fun y : nIndex Y d => pieceAlong f (nIndexSigma Y d y)) y := by
  calc sCCMap (sndToR f y) ≫ Theta f d
      = sCCMap (sndToR f y) ≫ (grFι f d ≫ mapPsi f d) := by rw [mapPsi_toTheta]
    _ = (sCCMap (sndToR f y) ≫ grFι f d) ≫ mapPsi f d := by rw [Category.assoc]
    _ = (pieceπ f d y ≫ mapPhiY f d y) ≫ mapPsi f d := by rw [← mapPhiY_apply, pieceπ_eq]
    _ = pieceπ f d y ≫ (mapPhiY f d y ≫ mapPsi f d) := by rw [Category.assoc]
    _ = pieceπ f d y ≫ Sigma.ι (fun y : nIndex Y d => pieceAlong f (nIndexSigma Y d y)) y := by
          rw [mapPhiY_comp_mapPsi]


end Work.SSS
