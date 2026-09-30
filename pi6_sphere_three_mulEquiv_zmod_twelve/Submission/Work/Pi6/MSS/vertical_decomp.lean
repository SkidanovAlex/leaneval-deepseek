import Mathlib
import Submission.Work.Pi6.MSS.E2cfkDefs
import Submission.Work.SSS.sSing_fibre_factor
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The vertical decomposition of a cycle over the first Serre stage

Let `p : E ⟶ B` be a continuous map and `𝕜` a field.  A `q`-chain `γ` of the singular complex of
`E` which is a cycle and which lies in the first Serre stage (`sser p 1`, the subcomplex of
simplices whose image in `B` is degenerate from a vertex, i.e. lies over a single point of `B`)
decomposes as a finite sum of cycles in the fibres of `p`:

`γ = ∑_{b ∈ s} (fibreIncl p b)_* (w b)`,  with `d (w b) = 0`.

This is the chain level statement behind the injectivity of the fibre edge map of the Serre
spectral sequence (`Work.Pi6.MSS.e2Col_fibre_kernel`).

The proof proceeds as follows.

* `vt_exists_map_of_mem_skeleton_one`: a simplex of the `1`-skeleton of a simplicial set is a
  degeneracy of a vertex.
* `vt_exists_fibre_lift_const` / `vt_exists_fibre_lift_of_mem_sser`: a simplex of `Sing E` whose
  image in `Sing B` is a degeneracy of a vertex is a simplex of a single fibre.
* `vt_sSingP_fibreIncl_injective` / `vt_fibre_lift_base_unique`: a simplex has at most one
  liftable fibre ("disjoint supports").
* `vt_exists_fibre_retraction`: consequently the fibre inclusions `C_n(fibre p b) ⟶ C_n(E)`
  possess simultaneous retractions, i.e. the sum of their images is direct.

The main theorem then writes `γ ∈ ⨆ b, range (fibreIncl p b)_*` (the generator case is the lift
lemma), extracts a finitely supported family `c` with `∑ b, c b = γ`
(`Submodule.mem_iSup_iff_exists_finsupp`), lifts it through the fibre inclusions, and uses the
retractions to split the cycle condition `d γ = 0` into the fibrewise conditions `d (w b) = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.Pi6.MSS
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial Topology

noncomputable section

/-! ## A simplex of the `1`-skeleton is a degeneracy of a vertex -/

private lemma vt_exists_map_of_mem_skeleton_one {X : SSet} {n : ℕ} (y : X.obj (op ⦋n⦌))
    (h : y ∈ (X.skeleton 1).obj (op ⦋n⦌)) :
    ∃ (v : X.obj (op ⦋0⦌)) (f : ⦋n⦌ ⟶ ⦋0⦌), X.map f.op v = y := by
  change y ∈ (⨆ (i : Fin 1) (x : X.nonDegenerate (i : ℕ)),
    SSet.Subcomplex.ofSimplex x.1).obj (op ⦋n⦌) at h
  rw [Subfunctor.iSup_obj] at h
  rw [Set.mem_iUnion] at h
  obtain ⟨i, hi⟩ := h
  rw [Subfunctor.iSup_obj] at hi
  rw [Set.mem_iUnion] at hi
  obtain ⟨x, hx⟩ := hi
  rw [SSet.Subcomplex.mem_ofSimplex_obj_iff] at hx
  obtain ⟨f, hf⟩ := hx
  fin_cases i
  exact ⟨x.1, f, hf⟩

/-! ## The fibre lift of a simplex over a constant vertex -/

/-- A simplex `σ` of `Sing E` whose image under `Sing p` is the constant simplex at `b` lifts to
the fibre over `b`. -/
private lemma vt_exists_fibre_lift_const {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) {n : ℕ} (σ : (Work.SSS.sSing E).obj (op ⦋n⦌)) (b : B)
    (hb : (Work.SSS.sSingP p).app (op ⦋n⦌) σ =
      (SSet.const (TopCat.toSSetObj₀Equiv.symm b)).app (op ⦋n⦌) σ) :
    ∃ σ' : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (op ⦋n⦌),
      (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) σ' = σ := by
  have hconst : p.comp (TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌) σ) =
      ContinuousMap.const (stdSimplex ℝ (Fin (n+1))) b := by
    have h := congrArg (TopCat.toSSetObjEquivT (TopCat.of B) (op ⦋n⦌)) hb
    rw [show TopCat.toSSetObjEquivT (TopCat.of B) (op ⦋n⦌)
          ((Work.SSS.sSingP p).app (op ⦋n⦌) σ) =
        p.comp (TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌) σ) from rfl] at h
    rw [Work.SSS.toSSetObjEquiv_const_app] at h
    simpa using h
  have hpt : ∀ z, p (TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌) σ z) = b := by
    intro z
    have h := congrArg (fun f => f z) hconst
    simpa only [ContinuousMap.comp_apply, ContinuousMap.const_apply] using h
  let fy : C(stdSimplex ℝ (Fin (n+1)), Work.StemsB.fibre p b) :=
    { toFun := fun z => ⟨(TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌) σ) z, hpt z⟩
      continuous_toFun :=
        (TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌) σ).continuous.subtype_mk hpt }
  refine ⟨(TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌)).symm fy, ?_⟩
  apply (TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌)).injective
  rw [show TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌)
        ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌)
          ((TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌)).symm fy)) =
      (Work.StemsB.fibreIncl p b).comp
        (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌)
          ((TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌)).symm fy)) from rfl]
  rw [Equiv.apply_symm_apply]
  ext z
  rfl

/-- A simplex of `Sing E` lying in the first Serre stage of `p` is a simplex of a single fibre. -/
private lemma vt_exists_fibre_lift_of_mem_sser {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (n : ℕ) (σ : (Work.SSS.sSing E).obj (op ⦋n⦌))
    (hσ : σ ∈ (Work.StemsB.serreSubcomplex (Work.SSS.sSingP p) 1).obj (op ⦋n⦌)) :
    ∃ (b : B) (σ' : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (op ⦋n⦌)),
      (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) σ' = σ := by
  obtain ⟨v, f, hf⟩ := vt_exists_map_of_mem_skeleton_one ((Work.SSS.sSingP p).app (op ⦋n⦌) σ) hσ
  refine ⟨TopCat.toSSetObj₀Equiv v, ?_⟩
  refine vt_exists_fibre_lift_const p σ (TopCat.toSSetObj₀Equiv v) ?_
  rw [← hf, Equiv.symm_apply_apply, SimplexCategory.eq_const_to_zero f, SSet.const_app]
  rfl

/-! ## Disjointness of the fibres -/

/-- The map on `n`-simplices induced by the inclusion of the fibre over `b` is injective. -/
private lemma vt_sSingP_fibreIncl_injective {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (b : B) (n : ℕ) :
    Function.Injective ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌)) := by
  intro x y hxy
  have h3 : (Work.StemsB.fibreIncl p b).comp
        (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌) x) =
      (Work.StemsB.fibreIncl p b).comp
        (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌) y) := by
    have h := congrArg (TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌)) hxy
    rw [show TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌)
          ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) x) =
        (Work.StemsB.fibreIncl p b).comp
          (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌) x) from rfl,
      show TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌)
          ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) y) =
        (Work.StemsB.fibreIncl p b).comp
          (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌) y) from rfl] at h
    exact h
  apply (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌)).injective
  ext z
  exact Subtype.ext (by
    have hz := congrArg (fun f => f z) h3
    simpa only [ContinuousMap.comp_apply, Work.StemsB.fibreIncl_apply] using hz)

/-- A simplex of `E` which lifts to two fibres lifts to the same point of the base. -/
private lemma vt_fibre_lift_base_unique {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) {n : ℕ} (x : (Work.SSS.sSing E).obj (op ⦋n⦌)) (b b' : B)
    (hb : ∃ y : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (op ⦋n⦌),
      (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) y = x)
    (hb' : ∃ y : (Work.SSS.sSing (Work.StemsB.fibre p b')).obj (op ⦋n⦌),
      (Work.SSS.sSingP (Work.StemsB.fibreIncl p b')).app (op ⦋n⦌) y = x) : b = b' := by
  obtain ⟨y, hy⟩ := hb
  obtain ⟨y', hy'⟩ := hb'
  have hval : ∀ (b : B) (y : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (op ⦋n⦌)),
      (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) y = x →
      p ((TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌) x)
        ⟨Pi.single (0 : Fin (n+1)) 1, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩) = b := by
    intro b y hy
    have hcont : TopCat.toSSetObjEquivT (TopCat.of E) (op ⦋n⦌) x =
        (Work.StemsB.fibreIncl p b).comp
          (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌) y) := by
      rw [← hy]
      rfl
    rw [hcont]
    exact (TopCat.toSSetObjEquivT (TopCat.of (Work.StemsB.fibre p b)) (op ⦋n⦌) y
      ⟨Pi.single (0 : Fin (n+1)) 1, single_mem_stdSimplex ℝ (0 : Fin (n+1))⟩).2
  exact (hval b y hy).symm.trans (hval b' y' hy')

/-! ## The retractions onto the fibres -/

/-- The images of the fibre chain complexes in `C_n(E)` form a direct sum: there are simultaneous
retractions. -/
private lemma vt_exists_fibre_retraction (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (n : ℕ) :
    ∃ r : (b : B) → (E2cfk.ECC 𝕜 E).X n →ₗ[𝕜] (E2cfk.fibCC 𝕜 p b).X n,
      (∀ b : B, (r b).comp (((E2cfk.fIncl 𝕜 p b).f n).hom) = LinearMap.id) ∧
      (∀ b b' : B, b ≠ b' → (r b).comp (((E2cfk.fIncl 𝕜 p b').f n).hom) = 0) := by
  classical
  -- the coproduct cocone describing the `n`-chains of `E`
  have hcE : IsColimit (Cofan.mk ((E2cfk.ECC 𝕜 E).X n)
      (fun τ : (Work.SSS.sSing E).obj (op ⦋n⦌) =>
        SSet.ιChainComplex (Work.SSS.sSing E) (R := ModuleCat.of 𝕜 𝕜) τ)) :=
    SSet.isColimitChainComplexXCofan (Work.SSS.sSing E) (ModuleCat.of 𝕜 𝕜) n
  -- the coproduct cocone describing the `n`-chains of the fibre over `b`
  have hcF : ∀ b : B, IsColimit (Cofan.mk ((E2cfk.fibCC 𝕜 p b).X n)
      (fun τ : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (op ⦋n⦌) =>
        SSet.ιChainComplex (Work.SSS.sSing (Work.StemsB.fibre p b)) (R := ModuleCat.of 𝕜 𝕜) τ)) :=
    fun b => SSet.isColimitChainComplexXCofan (Work.SSS.sSing (Work.StemsB.fibre p b))
      (ModuleCat.of 𝕜 𝕜) n
  -- the components of the retraction onto the fibre over `b`
  let comp : (b : B) → (τ : (Work.SSS.sSing E).obj (op ⦋n⦌)) →
      ModuleCat.of 𝕜 𝕜 ⟶ (E2cfk.fibCC 𝕜 p b).X n := fun b τ =>
    if h : ∃ τ' : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (op ⦋n⦌),
        (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) τ' = τ then
      SSet.ιChainComplex (Work.SSS.sSing (Work.StemsB.fibre p b)) (R := ModuleCat.of 𝕜 𝕜)
        (Classical.choose h)
    else 0
  have hcomp : ∀ (b : B) (τ' : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (op ⦋n⦌)),
      comp b ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) τ') =
        SSet.ιChainComplex (Work.SSS.sSing (Work.StemsB.fibre p b)) (R := ModuleCat.of 𝕜 𝕜) τ' := by
    intro b τ'
    have hex : ∃ τ'' : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (op ⦋n⦌),
        (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) τ'' =
          (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) τ' := ⟨τ', rfl⟩
    dsimp only [comp]
    rw [dif_pos hex, vt_sSingP_fibreIncl_injective p b n (Classical.choose_spec hex)]
  have hcomp0 : ∀ (b b' : B), b ≠ b' →
      ∀ τ' : (Work.SSS.sSing (Work.StemsB.fibre p b')).obj (op ⦋n⦌),
      comp b ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b')).app (op ⦋n⦌) τ') = 0 := by
    intro b b' hne τ'
    have hnex : ¬ ∃ τ'' : (Work.SSS.sSing (Work.StemsB.fibre p b)).obj (op ⦋n⦌),
        (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) τ'' =
          (Work.SSS.sSingP (Work.StemsB.fibreIncl p b')).app (op ⦋n⦌) τ' := by
      rintro ⟨τ'', hτ''⟩
      exact hne (vt_fibre_lift_base_unique p _ b b' ⟨τ'', hτ''⟩ ⟨τ', rfl⟩)
    dsimp only [comp]
    rw [dif_neg hnex]
  refine ⟨fun b => (Cofan.IsColimit.desc (hcE) (comp b)).hom, ?_, ?_⟩
  · intro b
    have key : (E2cfk.fIncl 𝕜 p b).f n ≫ (Cofan.IsColimit.desc (hcE) (comp b)) =
        𝟙 ((E2cfk.fibCC 𝕜 p b).X n) := by
      apply SSet.chainComplex_hom_ext (X := Work.SSS.sSing (Work.StemsB.fibre p b))
        (R := ModuleCat.of 𝕜 𝕜) (n := n)
      intro τ'
      rw [← Category.assoc]
      rw [show (E2cfk.fIncl 𝕜 p b).f n = (SSet.chainComplexMap
        (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)) (ModuleCat.of 𝕜 𝕜)).f n from rfl]
      rw [SSet.ι_chainComplexMap_f]
      rw [show (Work.SSS.sSing E).ιChainComplex
            ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) τ') ≫
              Cofan.IsColimit.desc (hcE) (comp b) =
            comp b ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b)).app (op ⦋n⦌) τ')
          from Cofan.IsColimit.fac hcE (comp b) _]
      rw [hcomp b τ', Category.comp_id]
    have h2 := congrArg ModuleCat.Hom.hom key
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
    exact h2
  · intro b b' hne
    have key : (E2cfk.fIncl 𝕜 p b').f n ≫ (Cofan.IsColimit.desc (hcE) (comp b)) = 0 := by
      apply SSet.chainComplex_hom_ext (X := Work.SSS.sSing (Work.StemsB.fibre p b'))
        (R := ModuleCat.of 𝕜 𝕜) (n := n)
      intro τ'
      rw [← Category.assoc]
      rw [show (E2cfk.fIncl 𝕜 p b').f n = (SSet.chainComplexMap
        (Work.SSS.sSingP (Work.StemsB.fibreIncl p b')) (ModuleCat.of 𝕜 𝕜)).f n from rfl]
      rw [SSet.ι_chainComplexMap_f]
      rw [show (Work.SSS.sSing E).ιChainComplex
            ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b')).app (op ⦋n⦌) τ') ≫
              Cofan.IsColimit.desc (hcE) (comp b) =
            comp b ((Work.SSS.sSingP (Work.StemsB.fibreIncl p b')).app (op ⦋n⦌) τ')
          from Cofan.IsColimit.fac hcE (comp b) _]
      rw [hcomp0 b b' hne τ', comp_zero]
    have h2 := congrArg ModuleCat.Hom.hom key
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    exact h2

/-! ## The main theorem -/

theorem vertical_decomp (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (q : ℕ)
    (γ : (Work.Pi6.MSS.E2cfk.ECC 𝕜 E).X q)
    (hγ : γ ∈ LinearMap.range ((Work.Pi6.MSS.E2cfk.sserInc 𝕜 p 1).f q).hom)
    (hcyc : (Work.Pi6.MSS.E2cfk.ECC 𝕜 E).d q (q - 1) γ = 0) :
    ∃ (s : Finset B) (w : (b : B) → (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p b).X q),
      (∀ b : B, (Work.Pi6.MSS.E2cfk.fibCC 𝕜 p b).d q (q - 1) (w b) = 0) ∧
      (∀ b : B, b ∉ s → w b = 0) ∧
      γ = ∑ b ∈ s, (Work.Pi6.MSS.E2cfk.fIncl 𝕜 p b).f q (w b) := by
  classical
  obtain ⟨r, hr_id, hr_zero⟩ := vt_exists_fibre_retraction 𝕜 p (q - 1)
  -- ## Step 1: every generator of the first Serre stage lies over a fibre
  have hgen : ∀ τ : (E2cfk.sser p 1).toSSet.obj (op ⦋q⦌),
      (SSet.ιChainComplex (Work.SSS.sSing E) (R := ModuleCat.of 𝕜 𝕜) τ.1).hom 1 ∈
        ⨆ b : B, LinearMap.range ((E2cfk.fIncl 𝕜 p b).f q).hom := by
    intro τ
    obtain ⟨b, σ', hσ'⟩ := vt_exists_fibre_lift_of_mem_sser p q τ.1 τ.2
    refine Submodule.mem_iSup_of_mem b ⟨
      (SSet.ιChainComplex (Work.SSS.sSing (Work.StemsB.fibre p b))
        (R := ModuleCat.of 𝕜 𝕜) σ').hom 1, ?_⟩
    have hmor : SSet.ιChainComplex (Work.SSS.sSing (Work.StemsB.fibre p b))
          (R := ModuleCat.of 𝕜 𝕜) σ' ≫ (E2cfk.fIncl 𝕜 p b).f q =
        SSet.ιChainComplex (Work.SSS.sSing E) (R := ModuleCat.of 𝕜 𝕜) τ.1 := by
      rw [show (E2cfk.fIncl 𝕜 p b).f q = (SSet.chainComplexMap
        (Work.SSS.sSingP (Work.StemsB.fibreIncl p b)) (ModuleCat.of 𝕜 𝕜)).f q from rfl]
      rw [SSet.ι_chainComplexMap_f, hσ']
    have h2 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hmor) (1 : 𝕜)
    rw [ModuleCat.hom_comp] at h2
    exact h2
  -- ## Step 2: `γ` lies in the supremum of the fibre images
  have hsup : γ ∈ ⨆ b : B, LinearMap.range ((E2cfk.fIncl 𝕜 p b).f q).hom := by
    obtain ⟨η, hη⟩ := LinearMap.mem_range.mp hγ
    rw [← hη]
    set P : Submodule 𝕜 ((E2cfk.ECC 𝕜 E).X q) :=
      ⨆ b : B, LinearMap.range ((E2cfk.fIncl 𝕜 p b).f q).hom with hP
    have hcS : IsColimit (Cofan.mk
        (((E2cfk.sser p 1).toSSet.chainComplex (ModuleCat.of 𝕜 𝕜)).X q)
        (fun τ : (E2cfk.sser p 1).toSSet.obj (op ⦋q⦌) =>
          SSet.ιChainComplex (E2cfk.sser p 1).toSSet (R := ModuleCat.of 𝕜 𝕜) τ)) :=
      SSet.isColimitChainComplexXCofan (E2cfk.sser p 1).toSSet (ModuleCat.of 𝕜 𝕜) q
    have key : ((E2cfk.sserInc 𝕜 p 1).f q) ≫ (ModuleCat.ofHom (Submodule.mkQ P)) = 0 := by
      apply SSet.chainComplex_hom_ext (X := (E2cfk.sser p 1).toSSet)
        (R := ModuleCat.of 𝕜 𝕜) (n := q)
      intro τ
      rw [← Category.assoc]
      rw [show (E2cfk.sserInc 𝕜 p 1).f q = (SSet.chainComplexMap (E2cfk.sser p 1).ι
        (ModuleCat.of 𝕜 𝕜)).f q from rfl]
      rw [SSet.ι_chainComplexMap_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom,
        LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      exact hgen τ
    have h2 := congrArg (fun (g : ((E2cfk.sser p 1).toSSet.chainComplex (ModuleCat.of 𝕜 𝕜)).X q ⟶
        ModuleCat.of 𝕜 (↥((E2cfk.ECC 𝕜 E).X q) ⧸ P)) => ModuleCat.Hom.hom g) key
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    have happ := DFunLike.congr_fun h2 η
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at happ
    rw [ModuleCat.hom_ofHom, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at happ
    exact happ
  -- ## Step 3: a finitely supported decomposition of `γ`
  obtain ⟨c, hc_mem, hc_sum⟩ := (Submodule.mem_iSup_iff_exists_finsupp
    (fun b : B => LinearMap.range ((E2cfk.fIncl 𝕜 p b).f q).hom) γ).mp hsup
  let w : (b : B) → (E2cfk.fibCC 𝕜 p b).X q := fun b =>
    if h : b ∈ c.support then Classical.choose (LinearMap.mem_range.mp (hc_mem b)) else 0
  have hw : ∀ b : B, (E2cfk.fIncl 𝕜 p b).f q (w b) = c b := by
    intro b
    by_cases hb : b ∈ c.support
    · dsimp only [w]
      rw [dif_pos hb]
      exact Classical.choose_spec (LinearMap.mem_range.mp (hc_mem b))
    · dsimp only [w]
      rw [dif_neg hb]
      show (ModuleCat.Hom.hom ((E2cfk.fIncl 𝕜 p b).f q)) 0 = c b
      rw [map_zero, eq_comm]
      by_contra hc0
      exact hb (Finsupp.mem_support_iff.mpr hc0)
  have hsum : γ = ∑ b ∈ c.support, (E2cfk.fIncl 𝕜 p b).f q (w b) := by
    rw [← hc_sum]
    show c.support.sum (fun i => c i) =
      c.support.sum (fun b => (E2cfk.fIncl 𝕜 p b).f q (w b))
    exact Finset.sum_congr rfl (fun b _ => (hw b).symm)
  refine ⟨c.support, w, ?_, ?_, hsum⟩
  · -- ## Step 4: the cycle condition splits
    intro b
    by_cases hb : b ∈ c.support
    · have hdγ : (E2cfk.ECC 𝕜 E).d q (q - 1)
          (∑ b' ∈ c.support, (E2cfk.fIncl 𝕜 p b').f q (w b')) = 0 := by
        rw [← hsum]; exact hcyc
      have hc0 : ∑ b' ∈ c.support, (E2cfk.fIncl 𝕜 p b').f (q - 1)
          ((E2cfk.fibCC 𝕜 p b').d q (q - 1) (w b')) = 0 := by
        rw [← hdγ]
        rw [map_sum]
        refine Finset.sum_congr rfl (fun b' _ => ?_)
        have hcomm := HomologicalComplex.Hom.comm (E2cfk.fIncl 𝕜 p b') q (q - 1)
        have h2 := congrArg (fun (g : (E2cfk.fibCC 𝕜 p b').X q ⟶ (E2cfk.ECC 𝕜 E).X (q - 1)) =>
          ModuleCat.Hom.hom g) hcomm
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
        have h3 := DFunLike.congr_fun h2 (w b')
        simp only [LinearMap.comp_apply] at h3
        exact h3.symm
      have happ : r b (∑ b' ∈ c.support, (E2cfk.fIncl 𝕜 p b').f (q - 1)
          ((E2cfk.fibCC 𝕜 p b').d q (q - 1) (w b'))) = 0 := by
        rw [hc0, map_zero]
      rw [map_sum] at happ
      rw [Finset.sum_eq_single b] at happ
      · rw [← LinearMap.comp_apply, hr_id b, LinearMap.id_apply] at happ
        exact happ
      · intro b' hb' hne
        rw [← LinearMap.comp_apply, hr_zero b b' (Ne.symm hne), LinearMap.zero_apply]
      · intro hbnot
        exact absurd hb hbnot
    · dsimp only [w]
      rw [dif_neg hb]
      show (ModuleCat.Hom.hom ((E2cfk.fibCC 𝕜 p b).d q (q - 1)))
        (0 : (E2cfk.fibCC 𝕜 p b).X q) = 0
      rw [map_zero]
  · intro b hb
    dsimp only [w]
    rw [dif_neg hb]
end

end Work.Pi6.MSS
