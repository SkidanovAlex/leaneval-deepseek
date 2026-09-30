import Mathlib
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSSR.KunnethEZ.ezChain_isCycle
import Submission.Work.SSSR.iotaTLift_derivation
import Submission.Work.SSSR.iotaTLift_last_eq
import Submission.Work.SSSR.iotaTBdryHornZero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
## Auxiliary lemmas for `Work.SSSR.iotaTBdryHorn`

The boundary of `ι_σ τ` in `C(T_σ)` is, by `Work.SSSR.iotaTLift_derivation`, the alternating sum
over the faces `i : Fin (t+2)` of `Δ[t+1]` of the shuffle chains
`rawX t Q Δ[t+1] F ((Δ[t+1]).δ i (stdIdSimplex (t+1))) τ`, pushed forward along the lift
`ezSimplex`.  The lemmas below show that

* (`Work.SSSR.hornSimp_aMap23_mem'`) for `i ≠ Fin.last (t+1)` every shuffle summand of the `i`-th
  face term lies over a simplex of the horn `hornSimp (t+1)`, hence in `C(Λ)`, and
* (`Work.SSSR.hornCokπ_rawX_eq_zero`) consequently the whole `i`-th face term dies in the quotient
  `C(T_σ)/C(Λ)`;
* (`Work.SSSR.iotaTLift_last_eq`, from the parallel development) the last face term
  `i = Fin.last (t+1)` is the push-forward of `ι_{d_last σ} τ` along `lastFaceChain`.

The final assembly is then the linear algebra of the cokernel projection together with
`Finset.sum_eq_single`.
-/

/-- **The chain map on a pair generator.**  For a morphism `φ : X ⊗ Y ⟶ Z` of simplicial sets and
simplices `x ∈ X_n`, `y ∈ Y_n`, the generator `genP R x y` of `C_n(X ⊗ Y)` is sent to the generator
of `C_n(Z)` attached to `φ (x,y)`. -/
lemma sCCMap_genP {X Y Z : SSet.{0}} (φ : X ⊗ Y ⟶ Z) {n : ℕ}
    (x : X _⦋n⦌) (y : Y _⦋n⦌) :
    (Work.SSSR.sCCMap R φ).f n (Work.SSSR.KunnethEZ.genP R x y)
      = Work.SSSR.KunnethEZ.genC Z (φ.app (op ⦋n⦌) (x, y)) := by
  have h := SSet.ι_chainComplexMap_f (X := X ⊗ Y) (Y := Z) φ (R := ModuleCat.of R R) (n := n)
    (x := (x, y))
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ (Z.chainComplex (ModuleCat.of R R)).X n) =>
    g.hom (1 : R)) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, Work.SSSR.KunnethEZ.genP, Work.SSSR.KunnethEZ.genC,
    Work.SSSR.sCCMap] using h2

/-- **The generator of a subcomplex.**  For a subcomplex `A ⊆ X`, a simplex `z ∈ A_n` and the
inclusion `A.ι`, the generator of `C_n(A)` attached to `z` maps to the generator of `C_n(X)`
attached to `z`. -/
lemma genC_subcomplex_ι {X : SSet.{0}} (A : X.Subcomplex) {n : ℕ} (z : X.obj (op ⦋n⦌))
    (hz : z ∈ A.obj (op ⦋n⦌)) :
    Work.SSSR.KunnethEZ.genC X z
      = (Work.SSSR.sCCMap R A.ι).f n (Work.SSSR.KunnethEZ.genC A ⟨z, hz⟩) := by
  have hh := SSet.ι_chainComplexMap_f (X := A) (Y := X) A.ι (R := ModuleCat.of R R) (n := n)
    (x := ⟨z, hz⟩)
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ (X.chainComplex (ModuleCat.of R R)).X n) =>
    g.hom (1 : R)) hh
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Subfunctor.ι_app, Work.SSSR.KunnethEZ.genC,
    Work.SSSR.sCCMap, Work.SSSR.sCC] at h2 ⊢
  exact h2.symm

/-- **The cokernel projection kills the image**: for a chain map `φ : K ⟶ L` and a chain `y`, the
class of `φ y` in the cokernel of `φ` is zero. -/
lemma cokernel_π_comp_apply_zero {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {n : ℕ}
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
lemma hornSimp_aMap23_mem' (t Q : ℕ) (T : Work.SSSR.KunnethEZ.Sh23 (t+1) (Q+1)) (i : Fin (t+2))
    (hi : i ≠ Fin.last (t+1)) :
    (Δ[t+1] : SSet).map (Work.SSSR.KunnethEZ.aMap23 (t+1) (Q+1) T).op
        ((Δ[t+1] : SSet).δ i (Work.SSSR.stdIdSimplex (t+1)))
      ∈ (Work.SSSR.hornSimp (t+1)).obj (op ⦋(t+1)+Q⦌) := by
  rw [Work.SSSR.hornSimp_eq_horn_last, SSet.mem_horn_iff_notMem_range]
  refine ⟨i, hi, ?_⟩
  rintro ⟨k, hk⟩
  simp only [Work.SSSR.stdIdSimplex, SSet.stdSimplex.map_apply] at hk
  exact Fin.succAbove_ne i _ hk

/-- **Every non-last face term of the derivation dies in the horn quotient.** -/
lemma hornCokπ_rawX_eq_zero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (t Q : ℕ) (b : B)
    (σ : Δ[t+1] ⟶ Work.SSSR.sSing B) (h : Work.SSSR.sigmaVert σ = b)
    (i : Fin (t+2)) (hi : i ≠ Fin.last (t+1))
    (τ : Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) _⦋Q+1⦌) :
    (Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f ((t+1)+Q)
      ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h)).f ((t+1)+Q)
        (Work.SSSR.KunnethEZ.rawX t Q Δ[t+1] (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
          (Work.SSSR.KunnethEZ.genC Δ[t+1] ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))))
          (Work.SSSR.KunnethEZ.genC (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) τ))) = 0 := by
  have hfst : ∀ (T : Work.SSSR.KunnethEZ.Sh23 (t+1) (Q+1)),
      (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋(t+1)+Q⦌)
        ((Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h).app
          (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.SSSR.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))),
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
              (Work.SSSR.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ))
        = (Δ[t+1]).map (Work.SSSR.KunnethEZ.aMap23 (t+1) (Q+1) T).op
            ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))) := by
    intro T
    have h1 : (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋(t+1)+Q⦌)
        ((Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h).app
          (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.SSSR.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))),
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
              (Work.SSSR.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ))
        = (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h ≫
            pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.SSSR.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))),
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
              (Work.SSSR.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ) := rfl
    rw [h1, Work.SSSR.ezSimplex_fst]
    rfl
  have hmem : ∀ (T : Work.SSSR.KunnethEZ.Sh23 (t+1) (Q+1)),
      (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h).app
          (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.SSSR.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))),
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
              (Work.SSSR.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ)
        ∈ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).obj (op ⦋(t+1)+Q⦌) := by
    intro T
    change (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋(t+1)+Q⦌)
        ((Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) (t+1) b σ h).app
          (op ⦋(t+1)+Q⦌)
          ((Δ[t+1]).map (Work.SSSR.KunnethEZ.aMap23 (t+1) (Q+1) T).op
              ((Δ[t+1]).δ i (Work.SSSR.stdIdSimplex (t+1))),
            (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)).map
              (Work.SSSR.KunnethEZ.bMap23 (t+1) (Q+1) T).op τ))
        ∈ (Work.SSSR.hornSimp (t+1)).obj (op ⦋(t+1)+Q⦌)
    rw [hfst T]
    exact hornSimp_aMap23_mem' t Q T i hi
  rw [Work.SSSR.KunnethEZ.rawX_gen, map_sum]
  simp only [map_zsmul]
  rw [map_sum]
  simp only [map_zsmul]
  refine Finset.sum_eq_zero (fun T _ => ?_)
  rw [sCCMap_genP]
  rw [genC_subcomplex_ι _ _ (hmem T)]
  rw [Work.SSSR.sCCMap_pieceHorn_ι_eq]
  rw [cokernel_π_comp_apply_zero (Work.SSSR.bdryIncl (Work.SSSR.sSingP p) σ ≫
    Work.SSSR.TIncl (Work.SSSR.sSingP p) σ) _]
  exact zsmul_zero _

end Work.SSSR
