import Mathlib
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.KunnethEZ.ez23_eq_ezGen
import Submission.Work.KunnethEZ.ezChain_isCycle
import Submission.Work.SSS.iotaTLift_derivation
import Submission.Work.SSS.iotaTLift_last_eq

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
## Auxiliary lemmas for `Work.SSS.iotaTBdryHorn`

The boundary of `ι_σ τ` in `C(T_σ)` is, by `Work.SSS.iotaTLift_derivation`, the alternating sum
over the faces `i : Fin (t+2)` of `Δ[t+1]` of the shuffle chains
`rawX t Q Δ[t+1] F ((Δ[t+1]).δ i (stdIdSimplex (t+1))) τ`, pushed forward along the lift
`ezSimplex`.  The lemmas below show that

* (`Work.SSS.hornSimp_aMap23_mem'`) for `i ≠ Fin.last (t+1)` every shuffle summand of the `i`-th
  face term lies over a simplex of the horn `hornSimp (t+1)`, hence in `C(Λ)`, and
* (`Work.SSS.hornCokπ_rawX_eq_zero`) consequently the whole `i`-th face term dies in the quotient
  `C(T_σ)/C(Λ)`;
* (`Work.SSS.iotaTLift_last_eq`, from the parallel development) the last face term
  `i = Fin.last (t+1)` is the push-forward of `ι_{d_last σ} τ` along `lastFaceChain`.

The final assembly is then the linear algebra of the cokernel projection together with
`Finset.sum_eq_single`.
-/

/-- **The chain map on a pair generator.**  For a morphism `φ : X ⊗ Y ⟶ Z` of simplicial sets and
simplices `x ∈ X_n`, `y ∈ Y_n`, the generator `genP x y` of `C_n(X ⊗ Y)` is sent to the generator
of `C_n(Z)` attached to `φ (x,y)`. -/
lemma sCCMap_genP {X Y Z : SSet.{0}} (φ : X ⊗ Y ⟶ Z) {n : ℕ}
    (x : X _⦋n⦌) (y : Y _⦋n⦌) :
    (Work.SSS.sCCMap φ).f n (Work.KunnethEZ.genP x y)
      = Work.KunnethEZ.genC Z (φ.app (op ⦋n⦌) (x, y)) := by
  have h := SSet.ι_chainComplexMap_f (X := X ⊗ Y) (Y := Z) φ (R := ModuleCat.of ℤ ℤ) (n := n)
    (x := (x, y))
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (Z.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
    g.hom (1 : ℤ)) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, Work.KunnethEZ.genP, Work.KunnethEZ.genC,
    Work.SSS.sCCMap] using h2

/-- **The generator of a subcomplex.**  For a subcomplex `A ⊆ X`, a simplex `z ∈ A_n` and the
inclusion `A.ι`, the generator of `C_n(A)` attached to `z` maps to the generator of `C_n(X)`
attached to `z`. -/
lemma genC_subcomplex_ι {X : SSet.{0}} (A : X.Subcomplex) {n : ℕ} (z : X.obj (op ⦋n⦌))
    (hz : z ∈ A.obj (op ⦋n⦌)) :
    Work.KunnethEZ.genC X z
      = (Work.SSS.sCCMap A.ι).f n (Work.KunnethEZ.genC A ⟨z, hz⟩) := by
  have hh := SSet.ι_chainComplexMap_f (X := A) (Y := X) A.ι (R := ModuleCat.of ℤ ℤ) (n := n)
    (x := ⟨z, hz⟩)
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (X.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
    g.hom (1 : ℤ)) hh
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Subfunctor.ι_app, Work.KunnethEZ.genC,
    Work.SSS.sCCMap, Work.SSS.sCC] at h2 ⊢
  exact h2.symm

/-- **The cokernel projection kills the image**: for a chain map `φ : K ⟶ L` and a chain `y`, the
class of `φ y` in the cokernel of `φ` is zero. -/
lemma cokernel_π_comp_apply_zero {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {n : ℕ}
    (y : K.X n) : (cokernel.π φ).f n (φ.f n y) = 0 := by
  have h : φ.f n ≫ (cokernel.π φ).f n = 0 := by
    have hc := cokernel.condition φ
    have hh := congrArg (fun (g : K ⟶ cokernel φ) => g.f n) hc
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using hh
  have h2 := congrArg (fun (g : K.X n ⟶ (cokernel φ).X n) => g.hom y) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h2

/-- **The `i`-th face of the shuffle vertex map of `stdIdSimplex (t+1)` lies in the horn.**  The
simplex `(Δ[t+1]).map (aMap23 (t+1) (Q+1) T).op ((Δ[t+1]).δ i (stdIdSimplex (t+1)))` corresponds to
the monotone map `⦋t+Q+1⦌ ⟶ ⦋t⦌ ⟶ ⦋t+1⦌`; as `aMap23` takes values in `Fin (t+1) = {0,…,t}`,
the composite misses the vertex `i` whenever `i ≠ Fin.last (t+1)`. -/
lemma hornSimp_aMap23_mem' (t Q : ℕ) (T : Work.KunnethEZ.Sh23 (t+1) (Q+1)) (i : Fin (t+2))
    (hi : i ≠ Fin.last (t+1)) :
    (Δ[t+1] : SSet).map (Work.KunnethEZ.aMap23 (t+1) (Q+1) T).op
        ((Δ[t+1] : SSet).δ i (Work.SSS.stdIdSimplex (t+1)))
      ∈ (Work.SSS.hornSimp (t+1)).obj (op ⦋(t+1)+Q⦌) := by
  rw [Work.SSS.hornSimp_eq_horn_last, SSet.mem_horn_iff_notMem_range]
  refine ⟨i, hi, ?_⟩
  rintro ⟨k, hk⟩
  simp only [Work.SSS.stdIdSimplex, SSet.stdSimplex.map_apply] at hk
  exact Fin.succAbove_ne i _ hk

/-- **Every non-last face term of the derivation dies in the horn quotient.** -/
lemma hornCokπ_rawX_eq_zero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) (hfib : Work.StemsB.IsSerreFibration p) (t Q : ℕ) (b : B)
    (σ : Δ[t+1] ⟶ Work.SSS.sSing B) (h : Work.SSS.sigmaVert σ = b)
    (i : Fin (t+2)) (hi : i ≠ Fin.last (t+1))
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋Q+1⦌) :
    (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)
      ((Work.SSS.sCCMap (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
        (Work.KunnethEZ.rawX t Q Δ[t+1] (Work.SSS.sSing (Work.StemsB.fibre p b))
          (Work.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))))
          (Work.KunnethEZ.genC (Work.SSS.sSing (Work.StemsB.fibre p b)) τ))) = 0 := by
  have hfst : ∀ (T : Work.KunnethEZ.Sh23 (t+1) (Q+1)),
      (pullback.fst σ (Work.SSS.sSingP p)).app (op ⦋(t+1)+Q⦌)
        ((Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (t+1) b σ h).app
          (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))),
            (Work.SSS.sSing (Work.StemsB.fibre p b)).map
              (Work.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ))
        = (Δ[t+1]).map (Work.KunnethEZ.aMap23 (t+1) (Q+1) T).op
            ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))) := by
    intro T
    have h1 : (pullback.fst σ (Work.SSS.sSingP p)).app (op ⦋(t+1)+Q⦌)
        ((Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (t+1) b σ h).app
          (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))),
            (Work.SSS.sSing (Work.StemsB.fibre p b)).map
              (Work.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ))
        = (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (t+1) b σ h ≫
            pullback.fst σ (Work.SSS.sSingP p)).app (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))),
            (Work.SSS.sSing (Work.StemsB.fibre p b)).map
              (Work.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ) := rfl
    rw [h1, Work.SSS.ezSimplex_fst]
    rfl
  have hmem : ∀ (T : Work.KunnethEZ.Sh23 (t+1) (Q+1)),
      (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (t+1) b σ h).app
          (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))),
            (Work.SSS.sSing (Work.StemsB.fibre p b)).map
              (Work.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ)
        ∈ (Work.SSS.pieceHorn (Work.SSS.sSingP p) σ).obj (op ⦋(t+1)+Q⦌) := by
    intro T
    change (pullback.fst σ (Work.SSS.sSingP p)).app (op ⦋(t+1)+Q⦌)
        ((Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (t+1) b σ h).app
          (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSS.stdIdSimplex (t+1))),
            (Work.SSS.sSing (Work.StemsB.fibre p b)).map
              (Work.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ))
        ∈ (Work.SSS.hornSimp (t+1)).obj (op ⦋(t+1)+Q⦌)
    rw [hfst T]
    exact hornSimp_aMap23_mem' t Q T i hi
  rw [Work.KunnethEZ.rawX_gen, map_sum]
  simp only [map_zsmul]
  rw [map_sum]
  simp only [map_zsmul]
  refine Finset.sum_eq_zero (fun T _ => ?_)
  rw [sCCMap_genP]
  rw [genC_subcomplex_ι _ _ (hmem T)]
  rw [Work.SSS.sCCMap_pieceHorn_ι_eq]
  rw [cokernel_π_comp_apply_zero (Work.SSS.bdryIncl (Work.SSS.sSingP p) σ ≫
    Work.SSS.TIncl (Work.SSS.sSingP p) σ) _]
  exact zsmul_zero _

/-- **The boundary of `ι_σ τ` modulo the horn.**  For `σ : Δ[t+1] ⟶ Sing B`, a point `b : B` and a
cycle `τ` of the fibre `F_b = p⁻¹(b)` in degree `Q+1`, the class of `∂(ι_σ τ)` in `C(T_σ)/C(Λ)`
(where `Λ = pieceHorn f σ` is the horn) is `(-1)^{t+1}` times the class of the push-forward of
`ι_{d_lastσ} τ` along the last-face pasting map `lastFaceChain f t σ`.

Proof route: `Work.KunnethEZ.ezChain_derivation` (at `(p,q) = (t,Q)`) expresses the boundary of the
shuffle chain of two chains as `rawX` of `(∂u, v)` plus `(-1)^{t+1}` times `rawY` of `(u, ∂v)`; the
second term vanishes because `∂τ = 0`.  Pushing `rawX t Q Δ[t+1] F (∂u) v` through `sCCMap
ezSimplex` (using `Work.KunnethEZ.rawX_gen`, linearity `rawX_sum_left` and `d_genC`) produces the
sum `Σ_{i : Fin (t+2)} (-1)^i` of the shuffle chains of the simplices
`(Δ[t+1]).δ i (stdIdSimplex (t+1))`.  For `i.val < t+1` the simplex `X.map (aMap23 … T).op (X.δ i σ)`
misses the vertex `i` (it is `[aMap23 … T ≫ δ i]`), hence lies in the horn `hornSimp (t+1)`, so the
corresponding generator of `T_σ` lies in `C(Λ)` and dies in `C(T_σ)/C(Λ)` (via
`Work.SSS.sCCMap_pieceHorn_ι_eq` and `cokernel.condition`).  For `i = Fin.last (t+1)` the shuffle
term is the push-forward of `ezGen t (Q+1) [id] τ` along `(stdSimplex.δ (Fin.last (t+1)) ⊗ 𝟙)`,
which by `Work.SSS.ezSimplex_liftFam_coface` equals the push-forward along the last-face pasting
map.  The degree bookkeeping `t + (Q+1) = (t+1) + Q` is handled by `Work.SSS.castElem` and the
homological `eqToHom`-naturality of chain maps. -/
theorem iotaTBdryHorn {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (t Q : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (h' : Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) = b)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋Q+1⦌)
    (hτ : (Work.SSS.fibreCC p b).d (Q+1) Q
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0) :
    (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)
      (((Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p) σ)).d ((t+1)+(Q+1)) ((t+1)+Q))
        (Work.SSS.iotaTLift p hfib (t+1) b σ h (Q+1) τ))
    = (-1 : ℤ)^(t+1) • (Work.SSS.hornCokπ (Work.SSS.sSingP p) σ).f ((t+1)+Q)
        ((Work.SSS.TIncl (Work.SSS.sSingP p) σ).f ((t+1)+Q)
          ((Work.SSS.lastFaceChain (Work.SSS.sSingP p) t σ).f ((t+1)+Q)
            (Work.SSS.castElem
              (Work.SSS.sCC (Work.SSS.pullAlong (Work.SSS.sSingP p)
                (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ)))
              (by omega : t + (Q+1) = (t+1)+Q)
              (Work.SSS.iotaTLift p hfib t b
                (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) h' (Q+1) τ)))) := by
  have hderiv := Work.SSS.iotaTLift_derivation p hfib t Q b σ h τ hτ
  have hlast := Work.SSS.iotaTLift_last_eq p hfib t Q b σ h h' τ
  rw [hderiv, map_sum]
  simp only [map_zsmul]
  rw [Finset.sum_eq_single (Fin.last (t+1))]
  · rw [hlast]
    norm_num
  · intro i _ hi
    rw [hornCokπ_rawX_eq_zero p hfib t Q b σ h i hi τ, zsmul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

end Work.SSS
