import Mathlib
import Submission.Work.Pi6.SQM.SIG.Basic
import Submission.Work.Pi6.SQM.SIG.Apply
import Submission.Work.Pi6.SQM.SIG.classZeroCoboundary
import Submission.Work.Pi6.SQM.SIG.clsPb
import Submission.Work.Cohomology.MVcapSquares
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.cupNatural
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `Z4Defs` — coefficient reduction `ℤ/4 → 𝔽₂` and the generic pullback `pbR`

Vocabulary for the proof of `Work.Pi6.SQM.SIG.sigmaLift` (preservation of `ℤ/4`-liftability under
the cohomology suspension).

* `pbR R f u` is the pullback of cochains along a map of simplicial sets, for an *arbitrary*
  coefficient ring `R` (the existing `pb` is the case `R = 𝔽₂`).
* `red42 Y n α` is the coefficientwise reduction of a `ℤ/4`-cochain to an `𝔽₂`-cochain, induced by
  the ring homomorphism `r42 : ℤ/4 → 𝔽₂`.
* `classZeroCoboundary_R` is the (generic) statement that a cocycle whose class vanishes is a
  coboundary, used to lift primitives over contractible spaces.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cohomologyClassOf cocycleOf
  SSetCochainComplex SSetCochainComplex_d cochainDiffLM_apply)

/-! ## The generic pullback `pbR` -/

/-- **Pullback of cochains along a map of simplicial sets**, over an arbitrary coefficient ring. -/
def pbR (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n : ℕ}
    (u : Cochain R Y n) : Cochain R X n :=
  ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap u

/-- For `R = 𝔽₂` this is the previously defined `pb`. -/
theorem pbR_F2 {X Y : SSet} (f : X ⟶ Y) {n : ℕ} (u : Cochain F2 Y n) :
    pbR F2 f u = pb f u := rfl

/-- `pbR` sends `0` to `0`. -/
theorem pbR_zero (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n : ℕ} :
    pbR R f (0 : Cochain R Y n) = 0 :=
  map_zero _

/-- `pbR` is additive. -/
theorem pbR_add (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n : ℕ}
    (u v : Cochain R Y n) : pbR R f (u + v) = pbR R f u + pbR R f v :=
  map_add _ u v

/-- Evaluation of the pullback on a generator: `pbR` is natural in the simplicial set. -/
theorem genEval_pbR (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n : ℕ}
    (u : Cochain R Y n) (σ : X _⦋n⦌) :
    genEval R X (pbR R f u) σ = genEval R Y u (f.app _ σ) :=
  genEval_dualMap R f u σ

/-- Functoriality of the simplicial chain complex, degreewise, over any coefficient ring. -/
theorem chainComplexMap_comp_fR (R : Type) [CommRing R] {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    (SSet.chainComplexMap (f ≫ g) (ModuleCat.of R R)).f n =
      (SSet.chainComplexMap f (ModuleCat.of R R)).f n ≫
        (SSet.chainComplexMap g (ModuleCat.of R R)).f n := by
  apply SSet.chainComplex_hom_ext
  intro x
  rw [SSet.ι_chainComplexMap_f, ← Category.assoc, SSet.ι_chainComplexMap_f,
    SSet.ι_chainComplexMap_f]
  rfl

/-- `pbR` is contravariantly functorial. -/
theorem pbR_comp (R : Type) [CommRing R] {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (u : Cochain R Z n) : pbR R (f ≫ g) u = pbR R f (pbR R g u) := by
  unfold pbR
  rw [chainComplexMap_comp_fR R f g n]
  simp only [ModuleCat.hom_comp]
  rw [← LinearMap.dualMap_comp_dualMap]
  rfl

/-- `pbR` commutes with the coboundary. -/
theorem pbR_cochainDiff (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) (n : ℕ)
    (u : Cochain R Y n) :
    cochainDiff R X (pbR R f u) = pbR R f (cochainDiff R Y u) := by
  apply LinearMap.ext
  intro x
  have hc := congrArg ModuleCat.Hom.hom
    ((SSet.chainComplexMap f (ModuleCat.of R R)).comm (n + 1) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
  have hc' := LinearMap.congr_fun hc x
  simp only [LinearMap.comp_apply] at hc'
  simp only [cochainDiff, pbR, LinearMap.comp_apply, LinearMap.dualMap_apply]
  rw [hc']

/-- Restriction to a subspace is the pullback along the inclusion. -/
theorem restr_eq_pbR (R : Type) [CommRing R] (X : TopCat) (A : Set X) {n : ℕ}
    (u : Cochain R (SX X) n) :
    ((restr R X A).f n).hom u = pbR R (TopCat.toSSet.map (subtypeIncl X A)) u := by
  rw [restr, Work.Cohomology.dualChainMap_f_hom, Work.Cohomology.chainMap_f_eq]
  rfl

/-- A relative cochain pulled back along the inclusion is `0`. -/
theorem pbR_subtypeIncl_relKern (R : Type) [CommRing R] (X : TopCat) (A : Set X) {n : ℕ}
    (u : relKern R X A n) :
    pbR R (TopCat.toSSet.map (subtypeIncl X A)) u.1 = 0 := by
  rw [← restr_eq_pbR R X A u.1]
  exact u.2

/-- A map into the subspace `A` kills every relative cochain. -/
theorem pbR_eq_zero_of_factors (R : Type) [CommRing R] {X : TopCat} (A : Set X) {Z : SSet}
    (f : Z ⟶ SX X) (c : Z ⟶ SX ↥A) (hf : f = c ≫ TopCat.toSSet.map (subtypeIncl X A))
    {n : ℕ} (u : relKern R X A n) : pbR R f u.1 = 0 := by
  rw [hf, pbR_comp R c (TopCat.toSSet.map (subtypeIncl X A)) n u.1,
    pbR_subtypeIncl_relKern R X A u, pbR_zero]


set_option backward.isDefEq.respectTransparency true in
theorem constSSet_eq_map (K : Type) [TopologicalSpace K] (k₀ : K) {Z : SSet}
    (g : Z ⟶ SX ↥({k₀} : Set K)) :
    constSSet K k₀ g = g ≫ TopCat.toSSet.map (subtypeIncl (TopCat.of K) ({k₀} : Set K)) := rfl

set_option backward.isDefEq.respectTransparency true in
theorem loopSSet_evSSet_factor (K : Type) [TopologicalSpace K] (k₀ : K) :
    loopSSet K k₀ ≫ evSSet K k₀ =
      (TopCat.toSSet.map (TopCat.ofHom
        (⟨fun _ : Path k₀ k₀ => (⟨k₀, rfl⟩ : ↥({k₀} : Set K)),
          continuous_const⟩ : C(Path k₀ k₀, ↥({k₀} : Set K))))) ≫
        TopCat.toSSet.map (subtypeIncl (TopCat.of K) ({k₀} : Set K)) := by
  rw [comp_loop_ev, constSSet_eq_map]

/-- A map factoring through the inclusion of the subspace kills every relative cochain. -/
theorem pbR_comp_subtypeIncl_zero (R : Type) [CommRing R] {X : TopCat} (A : Set X) {Z : SSet}
    (g : Z ⟶ SX ↥A) {n : ℕ} (u : relKern R X A n) :
    pbR R (g ≫ TopCat.toSSet.map (subtypeIncl X A)) u.1 = 0 := by
  rw [pbR_comp R g (TopCat.toSSet.map (subtypeIncl X A)) n u.1,
    pbR_subtypeIncl_relKern R X A u, pbR_zero]

/-- `ΩK ↪ PK → K` is the constant map, so a cochain vanishing on the base point pulls back to
`0` along the composite. -/
theorem pbR_loop_ev_relKern (R : Type) [CommRing R] (K : Type) [TopologicalSpace K] (k₀ : K)
    {n : ℕ} (α : Cochain R (SX (TopCat.of K)) n)
    (hα : pbR R (TopCat.toSSet.map (subtypeIncl (TopCat.of K) ({k₀} : Set K))) α = 0) :
    pbR R (loopSSet K k₀) (pbR R (evSSet K k₀) α) = 0 := by
  rw [← pbR_comp R (loopSSet K k₀) (evSSet K k₀) n α, loopSSet_evSSet_factor,
    pbR_comp R _ (TopCat.toSSet.map (subtypeIncl (TopCat.of K) ({k₀} : Set K))) n α, hα,
    pbR_zero]

/-! ## The coefficient reduction `ℤ/4 → 𝔽₂` -/

/-- **Reduction of a `ℤ/4`-cochain to an `𝔽₂`-cochain**, induced by `r42 : ℤ/4 → 𝔽₂`. -/
def red42 (Y : SSet) (n : ℕ) (α : Cochain (ZMod 4) Y n) : Cochain F2 Y n :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of F2 F2) n).desc
    (Cofan.mk (ModuleCat.of F2 F2)
      (fun σ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
        (r42 (genEval (ZMod 4) Y α σ)))))).hom

/-- The generator formula for `red42`. -/
theorem ιChainComplex_red42 (Y : SSet) (n : ℕ) (α : Cochain (ZMod 4) Y n) (σ : Y _⦋n⦌) :
    Y.ιChainComplex (R := ModuleCat.of F2 F2) σ ≫
        (Y.isColimitChainComplexXCofan (ModuleCat.of F2 F2) n).desc
          (Cofan.mk (ModuleCat.of F2 F2)
            (fun τ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
              (r42 (genEval (ZMod 4) Y α τ))))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2 (r42 (genEval (ZMod 4) Y α σ))) :=
  Cofan.IsColimit.fac _ _ _

/-- The generator formula for `red42`. -/
theorem genEval_red42 (Y : SSet) (n : ℕ) (α : Cochain (ZMod 4) Y n) (σ : Y _⦋n⦌) :
    genEval F2 Y (red42 Y n α) σ = r42 (genEval (ZMod 4) Y α σ) := by
  have h2 := congrArg (fun (g : ModuleCat.of F2 F2 ⟶ ModuleCat.of F2 F2) => g.hom 1)
    (ιChainComplex_red42 Y n α σ)
  simpa only [red42, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

/-- `red42` is additive. -/
theorem red42_add (Y : SSet) (n : ℕ) (α β : Cochain (ZMod 4) Y n) :
    red42 Y n (α + β) = red42 Y n α + red42 Y n β := by
  apply genEval_ext
  intro σ
  simp only [genEval_add, genEval_red42, map_add]


/-- `red42` is compatible with subtraction. -/
theorem red42_sub (Y : SSet) (n : ℕ) (α β : Cochain (ZMod 4) Y n) :
    red42 Y n (α - β) = red42 Y n α - red42 Y n β := by
  apply genEval_ext
  intro σ
  rw [genEval_red42 Y n (α - β) σ]
  rw [show genEval (ZMod 4) Y (α - β) σ
      = genEval (ZMod 4) Y α σ - genEval (ZMod 4) Y β σ from by
    simp only [genEval, LinearMap.sub_apply]]
  rw [map_sub]
  rw [show genEval F2 Y (red42 Y n α - red42 Y n β) σ
      = genEval F2 Y (red42 Y n α) σ - genEval F2 Y (red42 Y n β) σ from by
    simp only [genEval, LinearMap.sub_apply]]
  rw [genEval_red42 Y n α σ, genEval_red42 Y n β σ]

/-- `red42` sends `0` to `0`. -/
theorem red42_zero (Y : SSet) (n : ℕ) :
    red42 Y n (0 : Cochain (ZMod 4) Y n) = 0 := by
  apply genEval_ext
  intro σ
  rw [genEval_red42]
  simp only [genEval, LinearMap.zero_apply, map_zero]

/-- `red42` is compatible with pullback along a map of simplicial sets. -/
theorem pbR_red42 {X Y : SSet} (f : X ⟶ Y) {n : ℕ} (α : Cochain (ZMod 4) Y n) :
    red42 X n (pbR (ZMod 4) f α) = pbR F2 f (red42 Y n α) := by
  apply genEval_ext
  intro σ
  rw [genEval_red42, genEval_pbR, genEval_pbR, genEval_red42]

/-! ## Cocycles with vanishing class are coboundaries (any coefficient ring) -/

/-- A cycle of a cochain complex of modules whose homology class vanishes is a boundary. -/
lemma exists_toCycles_eq_of_homologyπ_eq_zero' {R : Type} [CommRing R]
    (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ) [K.HasHomology (n + 1)]
    (z : K.cycles (n + 1)) (h : ModuleCat.Hom.hom (K.homologyπ (n + 1)) z = 0) :
    ∃ y : K.X n, ModuleCat.Hom.hom (K.toCycles n (n + 1)) y = z := by
  let T := ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
    (K.toCycles_comp_homologyπ n (n + 1))
  have hprev : (ComplexShape.up ℕ).prev (n + 1) = n :=
    ComplexShape.prev_eq' (c := ComplexShape.up ℕ) (ComplexShape.up_mk n (n + 1) rfl)
  have hT : T.Exact :=
    ShortComplex.exact_of_g_is_cokernel T (K.homologyIsCokernel n (n + 1) hprev)
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT z h
  exact ⟨y, hy⟩

/-- **A cocycle whose cohomology class vanishes is a coboundary**, for any coefficient ring. -/
theorem classZeroCoboundary_R (R : Type) [CommRing R] (X : SSet) (n : ℕ)
    (u : Cochain R X (n + 1)) (hu : cochainDiff R X u = 0)
    (h : cohomologyClassOf R X u hu = 0) :
    ∃ v : Cochain R X n, cochainDiff R X v = u := by
  have hz : ModuleCat.Hom.hom
      ((SSetCochainComplex R X).homologyπ (n + 1))
      (cocycleOf R X u hu) = 0 := h
  obtain ⟨y, hy⟩ := exists_toCycles_eq_of_homologyπ_eq_zero'
    (SSetCochainComplex R X) n (cocycleOf R X u hu) hz
  refine ⟨y, ?_⟩
  have hA : ModuleCat.Hom.hom
        ((SSetCochainComplex R X).iCycles (n + 1))
        (ModuleCat.Hom.hom
          ((SSetCochainComplex R X).toCycles n (n + 1)) y) = u := by
    rw [hy]
    exact iCycles_cocycleOf R X u hu
  have hB : ModuleCat.Hom.hom
        ((SSetCochainComplex R X).d n (n + 1)) y
      = ModuleCat.Hom.hom
        ((SSetCochainComplex R X).iCycles (n + 1))
        (ModuleCat.Hom.hom
          ((SSetCochainComplex R X).toCycles n (n + 1)) y) := by
    have hc := congrArg (fun f => ModuleCat.Hom.hom f y)
      (HomologicalComplex.toCycles_i (SSetCochainComplex R X) n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    exact hc.symm
  have hC : ModuleCat.Hom.hom ((SSetCochainComplex R X).d n (n + 1)) y = u := hB.trans hA
  have hd : cochainDiff R X y = ModuleCat.Hom.hom
      ((SSetCochainComplex R X).d n (n + 1)) y := by
    rw [SSetCochainComplex_d]
    exact (cochainDiffLM_apply R X n y).symm
  exact hd.trans hC

/-- A contractible space has vanishing cohomology in positive degrees. -/
theorem subsingleton_coh_of_contractible_R (R : Type) [CommRing R] (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (m : ℕ) : Subsingleton (Coh R X (m + 1)) :=
  ModuleCat.isZero_iff_subsingleton.mp (contractible R (TopCat.of X) m)

/-- On a contractible space every cocycle of positive degree is a coboundary. -/
theorem exists_coboundary_of_contractible_R (R : Type) [CommRing R] (X : Type)
    [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) (u : Cochain R (SX X) (n + 1))
    (hu : cochainDiff R (SX X) u = 0) :
    ∃ v : Cochain R (SX X) n, cochainDiff R (SX X) v = u := by
  have h : IsZero (↑(HomologicalComplex.homology (SSetCochainComplex R (SX X)) (n + 1))) :=
    contractible R (TopCat.of X) n
  haveI := ModuleCat.isZero_iff_subsingleton.mp h
  exact classZeroCoboundary_R R (SX X) n u hu (Subsingleton.elim _ _)

end

end Work.Pi6.SQM.SIG
