import Mathlib
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSSR.mem_boundary_map_stdIdSimplex
import Submission.Work.SSSR.iota_comp_piecepiOf_eq_zero
import Submission.Work.SSSR.serreE1StepAux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- **The `X`-face part of the boundary of the Eilenberg–Zilber shuffle chain.**  For a simplex
`σ` of `X` in degree `n+1` and a simplex `τ` of `F` in degree `q+1`, this is the sum
`∑_i (-1)^i ∑_T shufSignN T • genP R (X ∘ a_T ∘ δ_i σ) (F ∘ b_T τ)` over the faces `i` of the
fundamental `(n+1)`-simplex and the `(n+1,q+1)`-shuffles `T`: the `X`-boundary part of
`∂ (ezGen (n+1) (q+1) X F σ τ)`, which lives in the same degree `(n+1)+q`. -/
def xChain (n q : ℕ) (X F : SSet.{0}) (σ : X _⦋n+1⦌) (τ : F _⦋q+1⦌) :
    ((X ⊗ F).chainComplex (Work.SSSR.KunnethEZ.eZR R)).X ((n+1)+q) :=
  ∑ i : Fin (n+2), ((-1 : ℤ) ^ (i : ℕ)) • ∑ T : Work.SSSR.KunnethEZ.Sh23 (n+1) (q+1),
    Work.SSSR.KunnethEZ.shufSignN T.1 •
      Work.SSSR.KunnethEZ.genP R (X.map (Work.SSSR.KunnethEZ.aMap23 (n+1) (q+1) T).op (X.δ i σ))
        (F.map (Work.SSSR.KunnethEZ.bMap23 (n+1) (q+1) T).op τ)

/-- **The `Y`-face part of the boundary of the Eilenberg–Zilber shuffle chain.**  For a simplex
`σ` of `X` in degree `n` and a simplex `τ` of `F` in degree `q+1`, this is the sum
`∑_j (-1)^j ∑_U shufSignN U • genP R (X ∘ a_U σ) (F ∘ b_U ∘ δ_j τ)`: the `Y`-boundary part of
`∂ (ezGen n (q+1) X F σ τ)`, in degree `n+q`.  It is `∑_j (-1)^j ezGen n q X F σ (F.δ_j τ)`
(`yChain_eq_ezGen`). -/
def yChain (n q : ℕ) (X F : SSet.{0}) (σ : X _⦋n⦌) (τ : F _⦋q+1⦌) :
    ((X ⊗ F).chainComplex (Work.SSSR.KunnethEZ.eZR R)).X (n+q) :=
  ∑ j : Fin (q+2), ((-1 : ℤ) ^ (j : ℕ)) • ∑ U : Work.SSSR.KunnethEZ.Sh32 n (q+1),
    Work.SSSR.KunnethEZ.shufSignN U.1 •
      Work.SSSR.KunnethEZ.genP R (X.map (Work.SSSR.KunnethEZ.aMap32 n (q+1) U).op σ)
        (F.map (Work.SSSR.KunnethEZ.bMap32 n (q+1) U).op (F.δ j τ))

/-- **The boundary of the Eilenberg–Zilber shuffle chain in the successor shape.**  This is
`Work.SSSR.KunnethEZ.ezGen_boundary` with its parameters `(P,Q)` instantiated at `(n,q)`, rewritten
through the pinned abbreviations `xChain` and `yChain`. -/
theorem ezGen_boundary_succ (n q : ℕ) (X F : SSet) (σ : X _⦋n+1⦌) (τ : F _⦋q+1⦌) :
    (((X ⊗ F).chainComplex (Work.SSSR.KunnethEZ.eZR R)).d ((n+1)+(q+1)) ((n+1)+(q+1)-1)).hom
        (Work.SSSR.Cohomology.Crux33.ezGen (n+1) (q+1) X F σ τ)
      = xChain n q X F σ τ + ((-1:ℤ)^(n+1)) • yChain (n+1) q X F σ τ := by
  simp only [xChain, yChain]
  exact Work.SSSR.KunnethEZ.ezGen_boundary X F σ τ

/-- **The `Y`-boundary part of the shuffle chain is `∑_j (-1)^j` of the shuffle chains of the
faces.**  The `Sh32`-indexed sum is the `(n,q)`-Eilenberg–Zilber shuffle chain of the face
`F.δ_j τ` (`Work.SSSR.KunnethEZ.ez32_eq_ezGen`). -/
theorem yChain_eq_ezGen (n q : ℕ) (X F : SSet) (σ : X _⦋n⦌) (τ : F _⦋q+1⦌) :
    yChain (R := R) n q X F σ τ
      = ∑ j : Fin (q+2), ((-1 : ℤ) ^ (j : ℕ)) •
          Work.SSSR.Cohomology.Crux33.ezGen n q X F σ (F.δ j τ) := by
  rw [yChain]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1

/-- **The boundary of the Eilenberg–Zilber shuffle chain in the degenerate `n = 0` shape.**  This
is the `Q`-degenerate case `Work.SSSR.KunnethEZ.ezChain_d_left0` of the chain-level derivation identity,
linearised: the boundary of the shuffle chain of a vertex of `X` and a simplex `τ` of `F` is the
shuffle chain of the vertex and of the boundary of `τ`. -/
theorem ezGen_boundary_zero (q : ℕ) (X F : SSet) (σ : X _⦋0⦌) (τ : F _⦋q+1⦌) :
    (((X ⊗ F).chainComplex (Work.SSSR.KunnethEZ.eZR R)).d (0 + (q+1)) (0 + q)).hom
        (Work.SSSR.Cohomology.Crux33.ezGen 0 (q+1) X F σ τ)
      = ∑ j : Fin (q+2), ((-1:ℤ)^(j:ℕ)) •
          Work.SSSR.Cohomology.Crux33.ezGen 0 q X F σ (F.δ j τ) := by
  rw [← Work.SSSR.KunnethEZ.ezChain_gen 0 (q+1) X F σ τ,
    Work.SSSR.KunnethEZ.ezChain_d_left0 q X F ((X.ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) σ).hom 1)
      ((F.ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) τ).hom 1),
    Work.SSSR.KunnethEZ.d_genC q F τ, Work.SSSR.KunnethEZ.ezChain_sum_right_zsmul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Work.SSSR.KunnethEZ.ezChain_gen]


variable {Xf Yf F : SSet.{0}}

/-- **The σ-piece chain map `ι_σ` of degree `P`, for an abstract lift `ez : Δ[P] ⊗ F ⟶ T_σ`.**
It is `Work.SSSR.iotaT` (the shuffle chain of the fundamental `P`-simplex of `Δ[P]` and a simplex of
`F`, pushed along `ez`) followed by the projection to the σ-piece. -/
def iotaFGen (f : Xf ⟶ Yf) (P q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F) ⟶ pullAlong f σ) :
    (sCC R F).X q ⟶ (pieceAlong R f σ).X (P+q) :=
  Sigma.desc (fun τ : F _⦋q⦌ =>
      eltHom (((sCCMap R ez).f (P+q))
        (Work.SSSR.Cohomology.Crux33.ezGen P q
          (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) τ)))
    ≫ (pieceπOf f σ).f (P+q)

/-- The value of `iotaFGen` on a generator. -/
lemma iotaFGen_gen (f : Xf ⟶ Yf) (P q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F) ⟶ pullAlong f σ)
    (τ : F _⦋q⦌) :
    (F.ιChainComplex (R := ModuleCat.of R R) τ) ≫ iotaFGen f P q σ ez
      = eltHom (((pieceπOf f σ).f (P+q)) (((sCCMap R ez).f (P+q))
          (Work.SSSR.Cohomology.Crux33.ezGen P q
            (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) τ))) := by
  rw [iotaFGen, ← Category.assoc, SSet.ιChainComplex, Sigma.ι_desc, eltHom_comp]

/-- `eltHom z` evaluated at `1` is `z`. -/
lemma eltHom_apply_one {M : ModuleCat R} (z : M) : (eltHom z).hom 1 = z := by
  rw [eltHom, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one]

/-- `eltHom` is additive and `ℤ`-linear in the target. -/
lemma eltHom_sum {M : ModuleCat R} {ι : Type*} (s : Finset ι) (c : ι → ℤ) (z : ι → M) :
    (∑ i ∈ s, c i • eltHom (z i)) = eltHom (∑ i ∈ s, c i • z i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [eltHom, ModuleCat.hom_sum, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ModuleCat.hom_zsmul]
  change c i • (ModuleCat.Hom.hom (eltHom (z i))) 1 = c i • z i
  rw [eltHom, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one]

/-- `eltHom` and scalar multiplication: `c • eltHom z = eltHom (c • z)`. -/
lemma eltHom_zsmul {M : ModuleCat R} (c : ℤ) (z : M) : c • eltHom z = eltHom (c • z) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [eltHom, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one]
  rw [ModuleCat.hom_zsmul]
  change c • (ModuleCat.Hom.hom (eltHom z)) 1 = c • z
  rw [eltHom, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply_one]

/-- The value of `iotaFGen` on a generator, as an element. -/
lemma iotaFGen_gen_apply (f : Xf ⟶ Yf) (P q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F) ⟶ pullAlong f σ)
    (τ : F _⦋q⦌) :
    (iotaFGen f P q σ ez).hom ((F.ιChainComplex (R := ModuleCat.of R R) τ).hom 1)
      = ((pieceπOf f σ).f (P+q)).hom (((sCCMap R ez).f (P+q)).hom
          (Work.SSSR.Cohomology.Crux33.ezGen P q
            (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) τ)) := by
  have h := congrArg (fun (g : Work.SSSR.KunnethEZ.eZR R ⟶ (pieceAlong R f σ).X (P+q)) => g.hom (1 : R))
    (iotaFGen_gen f P q σ ez τ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, eltHom_apply_one]

/-- **The chain-map property of `iotaFGen`.**  Given the boundary formula for the shuffle chain
`ezGen P (q+1) Δ[P] F (stdIdSimplex P) τ` -- its `X`-boundary part `XT τ` lies in the preimage of
`∂Δ[P]` (killed by `pieceπOf`), and its `Y`-boundary part is the shuffle chain of `∂τ` -- the map
`iotaFGen f P (q+1) σ ez` is a chain map up to the sign `(-1)^P`. -/
theorem iotaFGen_chainMap (f : Xf ⟶ Yf) (P : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F) ⟶ pullAlong f σ)
    (q : ℕ) (XT : (F _⦋q+1⦌) → ((sCC R (pullAlong f σ)).X (P+q)))
    (Hbd : ∀ τ : F _⦋q+1⦌,
        ((sCC R (pullAlong f σ)).d (P + (q+1)) (P + q)).hom
            (((sCCMap R ez).f (P + (q+1))).hom
              (Work.SSSR.Cohomology.Crux33.ezGen P (q+1)
                (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) τ))
          = XT τ + ((-1:ℤ)^P) • (((sCCMap R ez).f (P + q)).hom
              (∑ j : Fin (q+2), ((-1:ℤ)^(j:ℕ)) •
                Work.SSSR.Cohomology.Crux33.ezGen P q
                  (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) (F.δ j τ))))
    (HXT : ∀ τ : F _⦋q+1⦌, ((pieceπOf f σ).f (P+q)).hom (XT τ) = 0) :
    iotaFGen f P (q+1) σ ez ≫ (pieceAlong R f σ).d (P + (q+1)) (P + q)
      = ((-1:ℤ)^P) • ((sCC R F).d (q+1) q ≫ iotaFGen f P q σ ez) := by
  apply SSet.chainComplex_hom_ext
  intro τ
  have hL : (F.ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) τ) ≫
        (iotaFGen f P (q+1) σ ez ≫ (pieceAlong R f σ).d (P+(q+1)) (P+q))
      = eltHom (((pieceAlong R f σ).d (P+(q+1)) (P+q)).hom
          (((pieceπOf f σ).f (P+(q+1))).hom (((sCCMap R ez).f (P+(q+1))).hom
            (Work.SSSR.Cohomology.Crux33.ezGen P (q+1)
              (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) τ)))) := by
    rw [← Category.assoc, iotaFGen_gen, eltHom_comp]
  have hR : (F.ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) τ) ≫
        (((-1:ℤ)^P) • ((sCC R F).d (q+1) q ≫ iotaFGen f P q σ ez))
      = eltHom (((-1:ℤ)^P) • (∑ j : Fin (q+2), ((-1:ℤ)^(j:ℕ)) •
          ((pieceπOf f σ).f (P+q)).hom (((sCCMap R ez).f (P+q)).hom
            (Work.SSSR.Cohomology.Crux33.ezGen P q
              (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) (F.δ j τ))))) := by
    rw [Preadditive.comp_zsmul, ← Category.assoc, SSet.ιChainComplex_d]
    have hsum : (∑ j : Fin (q+2), ((-1:ℤ)^(j:ℕ)) •
          (F.ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) (F.δ j τ))) ≫ iotaFGen f P q σ ez
        = ∑ j : Fin (q+2), ((-1:ℤ)^(j:ℕ)) •
            ((F.ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) (F.δ j τ)) ≫ iotaFGen f P q σ ez) := by
      rw [Preadditive.sum_comp]
      exact Finset.sum_congr rfl (fun j _ => Preadditive.zsmul_comp _ _ _)
    rw [hsum]
    have hsum2 : (∑ j : Fin (q+2), ((-1:ℤ)^(j:ℕ)) •
          ((F.ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) (F.δ j τ)) ≫ iotaFGen f P q σ ez))
        = ∑ j : Fin (q+2), ((-1:ℤ)^(j:ℕ)) • eltHom
            (((pieceπOf f σ).f (P+q)).hom (((sCCMap R ez).f (P+q)).hom
              (Work.SSSR.Cohomology.Crux33.ezGen P q
                (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) (F.δ j τ)))) := by
      exact Finset.sum_congr rfl (fun j _ => congrArg _ (iotaFGen_gen f P q σ ez (F.δ j τ)))
    rw [hsum2]
    rw [eltHom_sum, eltHom_zsmul]
  rw [hL, hR]
  congr 1
  unfold pieceAlong pieceπOf at *
  have hπ : ((cokernel (sCCMap R (bdryAlong f σ).ι)).d (P + (q+1)) (P + q)).hom
        (((cokernel.π (sCCMap R (bdryAlong f σ).ι)).f (P+(q+1))).hom (((sCCMap R ez).f (P + (q+1))).hom
          (Work.SSSR.Cohomology.Crux33.ezGen P (q+1)
            (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) τ)))
      = ((cokernel.π (sCCMap R (bdryAlong f σ).ι)).f (P+q)).hom
          (((sCC R (pullAlong f σ)).d (P + (q+1)) (P + q)).hom (((sCCMap R ez).f (P + (q+1))).hom
          (Work.SSSR.Cohomology.Crux33.ezGen P (q+1)
            (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) τ))) := by
    have h := congrArg (fun (g : (sCC R (pullAlong f σ)).X (P+(q+1)) ⟶
          (cokernel (sCCMap R (bdryAlong f σ).ι)).X (P+q)) =>
        g.hom (((sCCMap R ez).f (P + (q+1))).hom
          (Work.SSSR.Cohomology.Crux33.ezGen P (q+1)
            (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P) τ)))
      ((cokernel.π (sCCMap R (bdryAlong f σ).ι)).comm (P+(q+1)) (P+q))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  rw [hπ, Hbd τ, LinearMap.map_add, map_zsmul, HXT τ, zero_add]
  congr 1
  simp only [map_sum, map_zsmul]

/-! ## The chain-map statement for `Work.SSSR.iotaF`

The abstract `iotaFGen_chainMap` is applied to the concrete data `f = sSingP p`,
`ez = ezSimplex p Φ hproj P b σ h`, with the boundary formula supplied as a hypothesis. -/

/-- **`iotaF` is a chain map of degree `P`**, conditional on the boundary formula for the shuffle
chain (the hypotheses `Hbd`, `HXT`); the two cases `P = 0` and `P = n+1` of the main theorem supply
them via `ezGen_boundary_zero` and `ezGen_boundary_succ` + `xChain_piecePi_eq_zero`. -/
theorem iotaF_chainMap_gen {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B),
        (Work.SSSR.sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b')) ⟶ Work.SSSR.sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B)
        (h : Work.SSSR.sigmaVert σ = b'),
        Φ n b' σ h ≫ Work.SSSR.sSingP p
          = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (q : ℕ)
    (XT : ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) _⦋q+1⦌) →
        ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (P+q)))
    (Hbd : ∀ τ : (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) _⦋q+1⦌,
        ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (P + (q+1)) (P + q)).hom
            (((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p Φ hproj P b σ h)).f (P + (q+1))).hom
              (Work.SSSR.Cohomology.Crux33.ezGen P (q+1)
                (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P) τ))
          = XT τ + ((-1:ℤ)^P) •
              (((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p Φ hproj P b σ h)).f (P + q)).hom
                (∑ j : Fin (q+2), ((-1:ℤ)^(j:ℕ)) •
                  Work.SSSR.Cohomology.Crux33.ezGen P q
                    (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                    (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P)
                    ((Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).δ j τ))))
    (HXT : ∀ τ : (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) _⦋q+1⦌,
        ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f (P+q)).hom (XT τ) = 0) :
    Work.SSSR.iotaF p Φ hproj P b σ h (q + 1) ≫
        (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (P + (q + 1)) (P + q)
      = ((-1 : ℤ) ^ P) •
          ((Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))).d (q + 1) q ≫
            Work.SSSR.iotaF p Φ hproj P b σ h q) :=
  iotaFGen_chainMap (Work.SSSR.sSingP p) P σ (Work.SSSR.ezSimplex p Φ hproj P b σ h) q XT Hbd HXT


end

namespace IotaAux

/-- The standard simplex `Δ[P]`, as a simplicial set. -/
abbrev stdSS (P : ℕ) : SSet.{0} := SSet.stdSimplex.obj (SimplexCategory.mk P)

/-- The first projection of the monoidal structure on `SSet` is the first coordinate. -/
lemma fst_app_pair {X Y : SSet.{0}} {k : ℕ} (x : X _⦋k⦌) (y : Y _⦋k⦌) :
    (SemiCartesianMonoidalCategory.fst X Y).app (op ⦋k⦌) (x, y) = x := by
  rw [SemiCartesianMonoidalCategory.fst_def]
  rfl

/-- The coface `δ i` as a map on vertices. -/
lemma delta_hom_apply {m : ℕ} (i : Fin (m+2)) (k : Fin (m+1)) :
    (ConcreteCategory.hom (SimplexCategory.δ (n := m) i)) k = i.succAbove k := by
  rw [SimplexCategory.δ]
  rfl

/-- The coface `δ i` misses the vertex `i`. -/
lemma delta_hom_apply_ne {m : ℕ} (i : Fin (m+2)) (k : Fin (m+1)) :
    (ConcreteCategory.hom (SimplexCategory.δ (n := m) i)) k ≠ i := by
  rw [delta_hom_apply]
  exact Fin.succAbove_ne i k

/-- The simplex of `T_σ` carried by the `(i,T)`-summand of `xChain` lies over the boundary
`∂Δ[n+1]`. -/
lemma ez_pair_mem_bdryAlong {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (n q : ℕ)
    (σ : stdSS (n+1) ⟶ Yf)
    (ez : stdSS (n+1) ⊗ F ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst (stdSS (n+1)) F)
    (τ : F _⦋q+1⦌) (i : Fin (n+2)) (T : Work.SSSR.KunnethEZ.Sh23 (n+1) (q+1)) :
    ez.app (op ⦋(n+1)+q⦌)
      ((stdSS (n+1)).map (Work.SSSR.KunnethEZ.aMap23 (n+1) (q+1) T).op
          ((stdSS (n+1)).δ i (stdIdSimplex (n+1))),
        F.map (Work.SSSR.KunnethEZ.bMap23 (n+1) (q+1) T).op τ)
      ∈ (bdryAlong f σ).obj (op ⦋(n+1)+q⦌) := by
  set XX : (stdSS (n+1)) _⦋(n+1)+q⦌ :=
    (stdSS (n+1)).map (Work.SSSR.KunnethEZ.aMap23 (n+1) (q+1) T).op
      ((stdSS (n+1)).δ i (stdIdSimplex (n+1))) with hXX
  set yy : F _⦋(n+1)+q⦌ := F.map (Work.SSSR.KunnethEZ.bMap23 (n+1) (q+1) T).op τ with hyy
  change (pullback.fst σ f).app (op ⦋(n+1)+q⦌) (ez.app (op ⦋(n+1)+q⦌) (XX, yy))
      ∈ (SSet.boundary (n+1)).obj (op ⦋(n+1)+q⦌)
  have h1 : (pullback.fst σ f).app (op ⦋(n+1)+q⦌) (ez.app (op ⦋(n+1)+q⦌) (XX, yy)) = XX := by
    have hc : (ez ≫ pullback.fst σ f).app (op ⦋(n+1)+q⦌) (XX, yy)
        = (SemiCartesianMonoidalCategory.fst (stdSS (n+1)) F).app (op ⦋(n+1)+q⦌) (XX, yy) :=
      congrArg (fun (φ : stdSS (n+1) ⊗ F ⟶ stdSS (n+1)) =>
        φ.app (op ⦋(n+1)+q⦌) (XX, yy)) hez
    exact hc.trans (fst_app_pair XX yy)
  rw [h1]
  have hx : XX = (stdSS (n+1)).map
      (Work.SSSR.KunnethEZ.aMap23 (n+1) (q+1) T ≫ SimplexCategory.δ i).op
      (stdIdSimplex (n+1)) := by
    rw [hXX, SimplicialObject.δ_def]
    exact (Work.SSSR.KunnethEZ.map_op_comp (Work.SSSR.KunnethEZ.aMap23 (n+1) (q+1) T)
      (SimplexCategory.δ i) (stdIdSimplex (n+1))).symm
  rw [hx]
  exact mem_boundary_map_stdIdSimplex _ i
    (fun k hk => delta_hom_apply_ne i ((ConcreteCategory.hom
      (Work.SSSR.KunnethEZ.aMap23 (n+1) (q+1) T)) k) hk)

/-- A chain-level generator of `C(Δ[P] ⊗ F)` whose pushforward along `ez` has underlying simplex in
`∂T_σ` is killed by the projection to the σ-piece. -/
lemma sCCMap_piecepiOf_elt_eq_zero {X Y F : SSet.{0}} (f : X ⟶ Y) {P : ℕ}
    (σ : stdSS P ⟶ Y) (ez : stdSS P ⊗ F ⟶ pullAlong f σ)
    {k : ℕ} (z : (stdSS P ⊗ F) _⦋k⦌)
    (hz : ez.app (op ⦋k⦌) z ∈ (bdryAlong f σ).obj (op ⦋k⦌)) :
    ((pieceπOf f σ).f k).hom (((sCCMap R ez).f k).hom
        (((stdSS P ⊗ F).ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) z).hom 1)) = 0 := by
  have h2 : (stdSS P ⊗ F).ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) z ≫ (sCCMap R ez).f k
      = (pullAlong f σ).ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) (ez.app (op ⦋k⦌) z) :=
    SSet.ι_chainComplexMap_f (stdSS P ⊗ F) (pullAlong f σ) ez (ModuleCat.of R R) (n := k) z
  have h3 : (pullAlong f σ).ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) (ez.app (op ⦋k⦌) z)
        ≫ (pieceπOf f σ).f k = 0 :=
    iota_comp_piecepiOf_eq_zero f σ (ez.app (op ⦋k⦌) z) hz
  have hcomp : ((pieceπOf f σ).f k).hom (((sCCMap R ez).f k).hom
        (((stdSS P ⊗ F).ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) z).hom 1))
      = (((stdSS P ⊗ F).ιChainComplex (R := Work.SSSR.KunnethEZ.eZR R) z
          ≫ (sCCMap R ez).f k ≫ (pieceπOf f σ).f k).hom 1) := by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hcomp, ← Category.assoc, h2, h3]
  simp

/-- The `(i,T)`-summand of `xChain` is killed by the projection to the σ-piece. -/
lemma sCCMap_piecepiOf_genP_eq_zero {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (n q : ℕ)
    (σ : stdSS (n+1) ⟶ Yf)
    (ez : stdSS (n+1) ⊗ F ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst (stdSS (n+1)) F)
    (τ : F _⦋q+1⦌) (i : Fin (n+2)) (T : Work.SSSR.KunnethEZ.Sh23 (n+1) (q+1)) :
    ((pieceπOf f σ).f ((n+1)+q)).hom (((sCCMap R ez).f ((n+1)+q)).hom
      (Work.SSSR.KunnethEZ.genP R
        ((stdSS (n+1)).map (Work.SSSR.KunnethEZ.aMap23 (n+1) (q+1) T).op
          ((stdSS (n+1)).δ i (stdIdSimplex (n+1))))
        (F.map (Work.SSSR.KunnethEZ.bMap23 (n+1) (q+1) T).op τ))) = 0 :=
  sCCMap_piecepiOf_elt_eq_zero f σ ez _
    (ez_pair_mem_bdryAlong f n q σ ez hez τ i T)

/-- A double sum of scalar multiples of vanishing terms vanishes. -/
lemma sum_smul_sum_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ] {M : ModuleCat R}
    (c : ι → ℤ) (d : ι → κ → ℤ) (f : ι → κ → M) (h : ∀ i T, f i T = 0) :
    ∑ i, c i • ∑ T, d i T • f i T = 0 := by
  simp only [h, zsmul_zero, Finset.sum_const_zero]

/-- **The `X`-boundary part of the shuffle chain dies in the σ-piece** (see the module docstring of
`Submission/Work/SSS/xChain_piecePi_eq_zero.lean`). -/
theorem xChain_piecePi_eq_zero {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (n q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⟶ Yf)
    (ez : CategoryTheory.MonoidalCategoryStruct.tensorObj
            (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) F ⟶ pullAlong f σ)
    (hez : CategoryTheory.CategoryStruct.comp ez (CategoryTheory.Limits.pullback.fst σ f)
        = CategoryTheory.SemiCartesianMonoidalCategory.fst
            (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) F)
    (τ : F.obj (Opposite.op (SimplexCategory.mk (q+1)))) :
    (ModuleCat.Hom.hom ((pieceπOf f σ).f ((n+1)+q)))
        ((ModuleCat.Hom.hom ((sCCMap R ez).f ((n+1)+q)))
          (xChain n q (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) F
            (stdIdSimplex (n+1)) τ))
      = 0 := by
  rw [xChain]
  simp only [map_sum, map_zsmul]
  exact sum_smul_sum_eq_zero _ _ _
    (fun i T => sCCMap_piecepiOf_genP_eq_zero f n q σ ez hez τ i T)

end IotaAux

/-- **`iotaF` is a chain map of degree `P`.**  The Eilenberg–Zilber shuffle chain map
`Work.SSSR.iotaF p Φ hproj P b σ h` (built in `Submission/Work/SSS/serreE1EZ.lean`) sends a `q`-chain
of the fibre `F_b` (`b = σ(v₀)`) to a `(P+q)`-chain of the σ-piece `piece_σ = C(T_σ)/C(∂T_σ)`.
It is a chain map up to the degree shift sign `(-1)^P`: `∂ (ι_σ τ) = (-1)^P ι_σ (∂ τ)`.

The proof is the Eilenberg–Zilber boundary formula (`Work.SSSR.KunnethEZ.ezGen_boundary`, which gives
`∂ (ezGen P q [id_P] τ) = Σ_i (-1)^i (i-th shuffle face terms) + (-1)^P (∂τ-terms)`) pushed through
the chain map `sCCMap R (ezSimplex_σ)` and projected by `Work.SSSR.pieceπOf`:
the `i`-th face term of the boundary of `ezGen P q [id_P] τ` has `Δ[P]`-component a shuffle map `a`
followed by the coface `δ_i`, hence misses the vertex `i` and lies in the preimage of `∂Δ[P]`, so the
corresponding simplex of `T_σ` lies in `∂T_σ`; such generators are killed by the projection to the
σ-piece (`Work.SSSR.iota_bdry_comp_pi_eq_zero` is the corresponding statement for `pieceπ R`).  The
remaining `∂τ`-terms are exactly `(-1)^P` times `iotaF` of `∂τ` by linearity of `iotaF` in `τ`
(`SSet.ιChainComplex_d`).  The case `P = 0` needs a separate argument: there `∂Δ[0] = ⊥`, so
`pieceπOf` is an isomorphism and `ezGen 0 q` is the shuffle chain of the vertex. -/
theorem iotaF_chainMap {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (Φ : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B),
        (Work.SSSR.sigmaVert σ = b') →
        (((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
          Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b')) ⟶ Work.SSSR.sSing E))
    (hproj : ∀ (n : ℕ) (b' : B)
        (σ : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⟶ Work.SSSR.sSing B)
        (h : Work.SSSR.sigmaVert σ = b'),
        Φ n b' σ h ≫ Work.SSSR.sSingP p
          = SemiCartesianMonoidalCategory.fst _ _ ≫ σ)
    (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) (q : ℕ) :
    Work.SSSR.iotaF p Φ hproj P b σ h (q + 1) ≫
        (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (P + (q + 1)) (P + q)
      = ((-1 : ℤ) ^ P) • ((Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))).d (q + 1) q ≫
          Work.SSSR.iotaF p Φ hproj P b σ h q)    := by
  rcases P with _ | n
  · -- ## the degenerate case `P = 0`: the shuffle chain of the vertex
    refine iotaF_chainMap_gen p Φ hproj 0 b σ h q (fun _ => 0) ?_ ?_
    · intro τ
      have hcm := congrArg (fun (g : (Work.SSSR.sCC R
              ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗
                Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))).X (0+(q+1)) ⟶
            (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (0+q)) =>
          g.hom (Work.SSSR.Cohomology.Crux33.ezGen 0 (q+1)
            (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) τ))
        ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p Φ hproj 0 b σ h)).comm (0+(q+1)) (0+q))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcm
      rw [hcm, Work.SSSR.ezGen_boundary_zero q
        (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0})
        (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex 0) τ]
      rw [show ((-1:ℤ)^0) = (1:ℤ) from pow_zero (-1), one_zsmul]
      exact (zero_add _).symm
    · intro τ
      exact map_zero _
  · -- ## the main case `P = n+1`
    refine iotaF_chainMap_gen p Φ hproj (n+1) b σ h q
      (fun τ => ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p Φ hproj (n+1) b σ h)).f ((n+1)+q)).hom
        (xChain n q (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (n+1)) τ)) ?_ ?_
    · intro τ
      have hcm := congrArg (fun (g : (Work.SSSR.sCC R
              ((SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⊗
                Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))).X ((n+1)+(q+1)) ⟶
            (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((n+1)+q)) =>
          g.hom (Work.SSSR.Cohomology.Crux33.ezGen (n+1) (q+1)
            (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (n+1)) τ))
        ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p Φ hproj (n+1) b σ h)).comm
          ((n+1)+(q+1)) ((n+1)+q))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcm
      rw [hcm]
      rw [show ((Work.SSSR.sCC R ((SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⊗
            Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))).d ((n+1)+(q+1)) ((n+1)+q)).hom
            (Work.SSSR.Cohomology.Crux33.ezGen (n+1) (q+1)
              (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (n+1)) τ)
          = xChain n q (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (n+1)) τ
            + ((-1:ℤ)^(n+1)) • yChain (n+1) q
              (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (n+1)) τ from
        ezGen_boundary_succ n q
          (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (n+1)) τ]
      rw [map_add, map_zsmul]
      congr 1
    · intro τ
      exact IotaAux.xChain_piecePi_eq_zero (Work.SSSR.sSingP p) n q σ
        (Work.SSSR.ezSimplex p Φ hproj (n+1) b σ h)
        (Work.SSSR.ezSimplex_fst Φ hproj (n+1) b σ h) τ


end Work.SSSR
