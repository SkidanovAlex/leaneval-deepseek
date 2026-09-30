import Mathlib
import Submission.Work.Pi6.SQM.SIG.Apply
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.pairIsoOfTrivial
import Submission.Work.StemsB.contractible_pathSpace
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial
open Work.Cohomology

namespace Work.Pi6.SQ

noncomputable section

/-!
# The coefficient-change layer `ℤ/4 → 𝔽₂` used by `sigmaLift`

* `pbG R f u` — pullback of cochains along a map of simplicial sets, over an arbitrary ring `R`
  (the library's `Work.Pi6.SQM.SIG.pb` is the case `R = 𝔽₂`);
* `red42 Y n α` — the coefficientwise reduction of a `ℤ/4`-cochain to an `𝔽₂`-cochain;
* the standard class-level lemmas for the singular cochain complex (`cohomologyClassOf` of a
  coboundary is zero, of a sum is the sum, and two cocycles with equal classes differ by a
  coboundary);
* `relSection4` — over `ℤ/4`, every class of `H^{n+2}(K)` has a relative cocycle representative on
  `(K, {k₀})` mapping to it under `relIncl`.
-/

/-! ## The generic pullback -/

/-- Pullback of cochains along a map of simplicial sets, over an arbitrary coefficient ring. -/
def pbG (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n : ℕ}
    (u : Cochain R Y n) : Cochain R X n :=
  ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap u

/-- For `R = 𝔽₂` this is the previously defined `pb`. -/
theorem pbG_F2 {X Y : SSet} (f : X ⟶ Y) {n : ℕ} (u : Cochain F2 Y n) :
    pbG F2 f u = Work.Pi6.SQM.SIG.pb f u := rfl

theorem pbG_zero (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n : ℕ} :
    pbG R f (0 : Cochain R Y n) = 0 := map_zero _

theorem pbG_add (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n : ℕ}
    (u v : Cochain R Y n) : pbG R f (u + v) = pbG R f u + pbG R f v := map_add _ _ _

/-- The coboundary is additive. -/
theorem cochainDiff_add {R : Type} [CommRing R] {Y : SSet} {k : ℕ}
    (γ γ' : Cochain R Y k) :
    cochainDiff R Y (γ + γ') = cochainDiff R Y γ + cochainDiff R Y γ' := by
  simp only [cochainDiff, LinearMap.add_comp]

/-- The coboundary is compatible with subtraction. -/
theorem cochainDiff_sub {R : Type} [CommRing R] {Y : SSet} {k : ℕ}
    (γ γ' : Cochain R Y k) :
    cochainDiff R Y (γ - γ') = cochainDiff R Y γ - cochainDiff R Y γ' := by
  simp only [cochainDiff, LinearMap.sub_comp]

/-- Evaluation of the pullback on a generator. -/
theorem genEval_pbG (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n : ℕ}
    (u : Cochain R Y n) (σ : X _⦋n⦌) :
    genEval R X (pbG R f u) σ = genEval R Y u (f.app _ σ) :=
  genEval_dualMap R f u σ

/-- The pullback commutes with the coboundary. -/
theorem pbG_cochainDiff (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) (n : ℕ)
    (u : Cochain R Y n) :
    cochainDiff R X (pbG R f u) = pbG R f (cochainDiff R Y u) := by
  apply LinearMap.ext
  intro x
  have hc := congrArg ModuleCat.Hom.hom
    ((SSet.chainComplexMap f (ModuleCat.of R R)).comm (n + 1) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
  have hc' := LinearMap.congr_fun hc x
  simp only [LinearMap.comp_apply] at hc'
  simp only [cochainDiff, pbG, LinearMap.comp_apply, LinearMap.dualMap_apply]
  rw [hc']

/-- The pullback is contravariantly functorial. -/
theorem pbG_comp (R : Type) [CommRing R] {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (u : Cochain R Z n) : pbG R (f ≫ g) u = pbG R f (pbG R g u) := by
  apply genEval_ext
  intro σ
  rw [genEval_pbG, genEval_pbG, genEval_pbG, NatTrans.comp_app]
  rfl

/-- Restriction to a subspace is the pullback along the inclusion. -/
theorem restr_eq_pbG (R : Type) [CommRing R] (X : TopCat) (A : Set X) {n : ℕ}
    (u : Cochain R (Work.Pi6.SQM.SX X) n) :
    ((restr R X A).f n).hom u = pbG R (TopCat.toSSet.map (subtypeIncl X A)) u := by
  rw [restr, Work.Cohomology.dualChainMap_f_hom, Work.Cohomology.chainMap_f_eq]
  rfl

/-- A relative cochain pulled back along the inclusion of the subspace is `0`. -/
theorem pbG_subtypeIncl_relKern (R : Type) [CommRing R] (X : TopCat) (A : Set X) {n : ℕ}
    (u : relKern R X A n) :
    pbG R (TopCat.toSSet.map (subtypeIncl X A)) u.1 = 0 := by
  rw [← restr_eq_pbG R X A u.1]
  exact u.2

/-- A map into the base point kills every relative cochain. -/
theorem pbG_constSSet_relKern (R : Type) [CommRing R] (K : Type) [TopologicalSpace K] (k₀ : K)
    {Z : SSet} (g : Z ⟶ Work.Pi6.SQM.SX ↥({k₀} : Set K)) {n : ℕ}
    (u : relKern R (TopCat.of K) ({k₀} : Set K) n) :
    pbG R (Work.Pi6.SQM.SIG.constSSet K k₀ g) u.1 = 0 := by
  show pbG R (g ≫ TopCat.toSSet.map (subtypeIncl (TopCat.of K) ({k₀} : Set K))) u.1 = 0
  rw [pbG_comp R g (TopCat.toSSet.map (subtypeIncl (TopCat.of K) ({k₀} : Set K))) n u.1,
    pbG_subtypeIncl_relKern R (TopCat.of K) ({k₀} : Set K) u, pbG_zero]

/-- `ΩK ↪ PK → K` is the constant map at `k₀`, so a cochain vanishing at the base point pulls
back to `0` along the composite. -/
theorem pbG_loop_ev_relKern (R : Type) [CommRing R] (K : Type) [TopologicalSpace K] (k₀ : K)
    {n : ℕ} (u : relKern R (TopCat.of K) ({k₀} : Set K) n) :
    pbG R (Work.Pi6.SQM.SIG.loopSSet K k₀ ≫ Work.Pi6.SQM.SIG.evSSet K k₀) u.1 = 0 := by
  rw [Work.Pi6.SQM.SIG.comp_loop_ev K k₀]
  exact pbG_constSSet_relKern R K k₀ _ u

/-! ## The reduction `ℤ/4 → 𝔽₂` on cochains -/

/-- Reduction of a `ℤ/4`-cochain to an `𝔽₂`-cochain, induced by `r42 : ℤ/4 → 𝔽₂`. -/
def red42 (Y : SSet) (n : ℕ) (α : Cochain (ZMod 4) Y n) : Cochain F2 Y n :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of F2 F2) n).desc
    (Cofan.mk (ModuleCat.of F2 F2)
      (fun σ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
        (Work.Pi6.SQM.r42 (genEval (ZMod 4) Y α σ)))))).hom

/-- The generator formula for `red42`. -/
theorem ιChainComplex_red42 (Y : SSet) (n : ℕ) (α : Cochain (ZMod 4) Y n) (σ : Y _⦋n⦌) :
    Y.ιChainComplex (R := ModuleCat.of F2 F2) σ ≫
        (Y.isColimitChainComplexXCofan (ModuleCat.of F2 F2) n).desc
          (Cofan.mk (ModuleCat.of F2 F2)
            (fun τ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
              (Work.Pi6.SQM.r42 (genEval (ZMod 4) Y α τ))))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
        (Work.Pi6.SQM.r42 (genEval (ZMod 4) Y α σ))) :=
  Cofan.IsColimit.fac _ _ _

/-- The generator formula for `red42`. -/
theorem genEval_red42 (Y : SSet) (n : ℕ) (α : Cochain (ZMod 4) Y n) (σ : Y _⦋n⦌) :
    genEval F2 Y (red42 Y n α) σ = Work.Pi6.SQM.r42 (genEval (ZMod 4) Y α σ) := by
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
theorem pbG_red42 {X Y : SSet} (f : X ⟶ Y) {n : ℕ} (α : Cochain (ZMod 4) Y n) :
    red42 X n (pbG (ZMod 4) f α) = pbG F2 f (red42 Y n α) := by
  apply genEval_ext
  intro σ
  rw [genEval_red42, genEval_pbG, genEval_pbG, genEval_red42]

/-- `red42` commutes with the coboundary. -/
theorem red42_cochainDiff (Y : SSet) (n : ℕ) (α : Cochain (ZMod 4) Y n) :
    red42 Y (n + 1) (cochainDiff (ZMod 4) Y α) = cochainDiff F2 Y (red42 Y n α) := by
  apply genEval_ext
  intro σ
  rw [genEval_red42, genEval_cochainDiff, genEval_cochainDiff]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, map_neg, map_one, genEval_red42]

/-! ## Standard class-level lemmas for a cochain complex of a simplicial set -/

/-- The class of the zero cocycle is zero. -/
theorem cohomologyClassOf_zero (R : Type) [CommRing R] (Y : SSet) (n : ℕ)
    (h : cochainDiff R Y (0 : Cochain R Y n) = 0) :
    cohomologyClassOf R Y (0 : Cochain R Y n) h = 0 := by
  show ((SSetCochainComplex R Y).homologyπ n).hom
    (cocycleOf R Y (0 : Cochain R Y n) h) = 0
  have hz : cocycleOf R Y (0 : Cochain R Y n) h = 0 :=
    iCycles_injective R Y n (by rw [iCycles_cocycleOf, map_zero])
  rw [hz, map_zero]

/-- The class of a sum of cocycles is the sum of the classes. -/
theorem cohomologyClassOf_add (R : Type) [CommRing R] (Y : SSet) {n : ℕ}
    (u v : Cochain R Y n) (hu : cochainDiff R Y u = 0) (hv : cochainDiff R Y v = 0)
    (huv : cochainDiff R Y (u + v) = 0) :
    cohomologyClassOf R Y (u + v) huv = cohomologyClassOf R Y u hu +
      cohomologyClassOf R Y v hv := by
  show ((SSetCochainComplex R Y).homologyπ n).hom (cocycleOf R Y (u + v) huv) =
    ((SSetCochainComplex R Y).homologyπ n).hom (cocycleOf R Y u hu) +
      ((SSetCochainComplex R Y).homologyπ n).hom (cocycleOf R Y v hv)
  have h : cocycleOf R Y (u + v) huv = cocycleOf R Y u hu + cocycleOf R Y v hv :=
    iCycles_injective R Y n (by rw [map_add, iCycles_cocycleOf, iCycles_cocycleOf,
      iCycles_cocycleOf])
  rw [h, map_add]

/-- The class of a coboundary is zero. -/
theorem cohomologyClassOf_coboundary_zero (R : Type) [CommRing R] (Y : SSet) (n : ℕ)
    (t : Cochain R Y n) (h : cochainDiff R Y (cochainDiff R Y t) = 0) :
    cohomologyClassOf R Y (cochainDiff R Y t) h = 0 := by
  show ((SSetCochainComplex R Y).homologyπ (n + 1)).hom
    (cocycleOf R Y (cochainDiff R Y t) h) = 0
  have hto : ModuleCat.Hom.hom ((SSetCochainComplex R Y).d n (n + 1)) t =
      cochainDiff R Y t := by
    rw [SSetCochainComplex_d]
    exact (cochainDiffLM_apply R Y n t).symm
  have hz : cocycleOf R Y (cochainDiff R Y t) h
      = ModuleCat.Hom.hom ((SSetCochainComplex R Y).toCycles n (n + 1)) t := by
    apply iCycles_injective R Y (n + 1)
    rw [iCycles_cocycleOf]
    have h2 := congrArg (fun g => ModuleCat.Hom.hom g t)
      (HomologicalComplex.toCycles_i (SSetCochainComplex R Y) n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [h2, hto]
  rw [hz]
  have h3 := congrArg (fun g => ModuleCat.Hom.hom g t)
    (HomologicalComplex.toCycles_comp_homologyπ (SSetCochainComplex R Y) n (n + 1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h3

/-- Two cocycles with equal classes differ by a coboundary (in positive degree). -/
theorem exists_coboundary_of_class_eq (R : Type) [CommRing R] (Y : SSet) (n : ℕ)
    (α β : Cochain R Y (n + 1)) (hα : cochainDiff R Y α = 0) (hβ : cochainDiff R Y β = 0)
    (h : cohomologyClassOf R Y α hα = cohomologyClassOf R Y β hβ) :
    ∃ t : Cochain R Y n, cochainDiff R Y t = α - β := by
  have hγ : cochainDiff R Y (α - β) = 0 := by
    rw [cochainDiff_sub, hα, hβ, sub_zero]
  have hz : ModuleCat.Hom.hom ((SSetCochainComplex R Y).homologyπ (n + 1))
      (cocycleOf R Y (α - β) hγ) = 0 := by
    have h1 : cocycleOf R Y (α - β) hγ = cocycleOf R Y α hα - cocycleOf R Y β hβ :=
      iCycles_injective R Y (n + 1) (by rw [map_sub, iCycles_cocycleOf, iCycles_cocycleOf,
        iCycles_cocycleOf])
    rw [h1, map_sub, sub_eq_zero]
    simpa only [cohomologyClassOf] using h
  obtain ⟨t, ht⟩ := Work.Pi6.SQM.SIG.exists_toCycles_eq_of_homologyπ_eq_zero
    (SSetCochainComplex R Y) n (cocycleOf R Y (α - β) hγ) hz
  refine ⟨t, ?_⟩
  have hd : ModuleCat.Hom.hom ((SSetCochainComplex R Y).d n (n + 1)) t = α - β := by
    have h2 := congrArg (fun g => ModuleCat.Hom.hom g t)
      (HomologicalComplex.toCycles_i (SSetCochainComplex R Y) n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [ht, iCycles_cocycleOf] at h2
    exact h2.symm
  rw [← hd]
  simp only [SSetCochainComplex_d, ModuleCat.hom_ofHom]
  exact (cochainDiffLM_apply R Y n t).symm

/-- Adding a coboundary to a cocycle does not change its class. -/
theorem classEq_of_diff_coboundary (R : Type) [CommRing R] (Y : SSet) (n : ℕ)
    (α : Cochain R Y (n + 1)) (hα : cochainDiff R Y α = 0) (t : Cochain R Y n)
    (h : cochainDiff R Y (α + cochainDiff R Y t) = 0) :
    cohomologyClassOf R Y (α + cochainDiff R Y t) h = cohomologyClassOf R Y α hα := by
  have ht : cochainDiff R Y (cochainDiff R Y t) = 0 := by
    have h1 : cochainDiff R Y (α + cochainDiff R Y t) =
        cochainDiff R Y α + cochainDiff R Y (cochainDiff R Y t) := by rw [cochainDiff_add]
    rw [h1, hα, zero_add] at h
    exact h
  rw [cohomologyClassOf_add R Y α (cochainDiff R Y t) hα ht h,
    cohomologyClassOf_coboundary_zero R Y n t ht, add_zero]

/-- A cocycle whose cohomology class vanishes is a coboundary. -/
theorem classZeroCoboundaryR (R : Type) [CommRing R] (Y : SSet) (n : ℕ)
    (u : Cochain R Y (n + 1)) (hu : cochainDiff R Y u = 0)
    (h : cohomologyClassOf R Y u hu = 0) :
    ∃ v : Cochain R Y n, cochainDiff R Y v = u := by
  have hz : ModuleCat.Hom.hom ((SSetCochainComplex R Y).homologyπ (n + 1))
      (cocycleOf R Y u hu) = 0 := h
  obtain ⟨v, hv⟩ := Work.Pi6.SQM.SIG.exists_toCycles_eq_of_homologyπ_eq_zero
    (SSetCochainComplex R Y) n (cocycleOf R Y u hu) hz
  refine ⟨v, ?_⟩
  have hd : ModuleCat.Hom.hom ((SSetCochainComplex R Y).d n (n + 1)) v = u := by
    have h2 := congrArg (fun g => ModuleCat.Hom.hom g v)
      (HomologicalComplex.toCycles_i (SSetCochainComplex R Y) n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [hv, iCycles_cocycleOf] at h2
    exact h2.symm
  rw [← hd]
  simp only [SSetCochainComplex_d, ModuleCat.hom_ofHom]
  exact (cochainDiffLM_apply R Y n v).symm

/-- On a contractible space every positive-degree cocycle is a coboundary. -/
theorem exists_coboundary_of_contractible (R : Type) [CommRing R] (X : Type)
    [TopologicalSpace X] [ContractibleSpace X] (n : ℕ)
    (u : Cochain R (Work.Pi6.SQM.SX X) (n + 1))
    (hu : cochainDiff R (Work.Pi6.SQM.SX X) u = 0) :
    ∃ v : Cochain R (Work.Pi6.SQM.SX X) n, cochainDiff R (Work.Pi6.SQM.SX X) v = u := by
  haveI : Subsingleton ((SSetCochainComplex R (Work.Pi6.SQM.SX X)).homology (n + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mp (contractible R (TopCat.of X) n)
  exact classZeroCoboundaryR R (Work.Pi6.SQM.SX X) n u hu (Subsingleton.elim _ _)

theorem liftable4_zero (X : Type) [TopologicalSpace X] (n : ℕ) :
    Work.Pi6.SQM.Liftable4 (0 : Coh F2 X n) := by
  refine ⟨0, ?_, 0, ?_, ?_, ?_⟩
  · simp only [cochainDiff, LinearMap.zero_comp]
  · simp only [cochainDiff, LinearMap.zero_comp]
  · exact cohomologyClassOf_zero F2 (Work.Pi6.SQM.SX X) n _
  · intro σ
    simp only [genEval, LinearMap.zero_apply, map_zero]

/-! ## The relative section over `ℤ/4` -/


/-- Adding a coboundary to a cocycle does not change its class (difference form). -/
theorem classEq_of_diff_coboundary' (R : Type) [CommRing R] (Y : SSet) (n : ℕ)
    (x y : Cochain R Y (n + 1)) (hx : cochainDiff R Y x = 0) (hy : cochainDiff R Y y = 0)
    (v : Cochain R Y n) (hv : cochainDiff R Y v = x - y) :
    cohomologyClassOf R Y x hx = cohomologyClassOf R Y y hy := by
  have h1 : x = y + cochainDiff R Y v := by rw [hv]; abel
  subst h1
  exact classEq_of_diff_coboundary R Y n y hy v hx

/-- A point has no cohomology over `ℤ/4` in positive degrees. -/
theorem subsingleton_coh_singleton4 (K : Type) [TopologicalSpace K] (k₀ : K) (m : ℕ) :
    Subsingleton (Coh (ZMod 4) ↥({k₀} : Set K) (m + 1)) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (contractible (ZMod 4) (TopCat.of ↥({k₀} : Set K)) m)

/-- An isomorphism of `ℤ/4`-modules cancels its inverse on the right. -/
theorem asIso_hom_inv_apply4 {M N : ModuleCat (ZMod 4)} (f : M ⟶ N) (h : IsIso f) (y : N) :
    f.hom ((@asIso _ _ _ _ f h).inv.hom y) = y := by
  have h2 := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (Iso.inv_hom_id (@asIso _ _ _ _ f h))) y
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply,
    asIso_hom] using h2

/-- **The relative section over `ℤ/4`**: every class of `H^{n+2}(K;ℤ/4)` is the image under
`relIncl` of the class of a relative cocycle of `(K,{k₀})`. -/
theorem relSection4 (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ)
    (z : Coh (ZMod 4) K (n + 2)) :
    ∃ (a : relKern (ZMod 4) (TopCat.of K) ({k₀} : Set K) (n + 2))
      (ha : relDiffLM (ZMod 4) (TopCat.of K) ({k₀} : Set K) (n + 2) a = 0),
      (HomologicalComplex.homologyMap
        (relIncl (ZMod 4) (TopCat.of K) ({k₀} : Set K)) (n + 2)).hom
        (relClassOf (ZMod 4) (TopCat.of K) ({k₀} : Set K) a ha) = z := by
  haveI hIso : IsIso (HomologicalComplex.homologyMap
      (relIncl (ZMod 4) (TopCat.of K) ({k₀} : Set K)) (n + 2)) :=
    pairIsoOfTrivial (ZMod 4) (TopCat.of K) ({k₀} : Set K) (n + 1)
      (subsingleton_coh_singleton4 K k₀ n)
      (subsingleton_coh_singleton4 K k₀ (n + 1))
  obtain ⟨a, ha, hcls⟩ := exists_relClassOf (ZMod 4) (TopCat.of K) ({k₀} : Set K) (n + 2)
    ((asIso (HomologicalComplex.homologyMap
      (relIncl (ZMod 4) (TopCat.of K) ({k₀} : Set K)) (n + 2))).inv.hom z)
  refine ⟨a, ha, ?_⟩
  rw [hcls]
  exact asIso_hom_inv_apply4 _ hIso z

end

end Work.Pi6.SQ
