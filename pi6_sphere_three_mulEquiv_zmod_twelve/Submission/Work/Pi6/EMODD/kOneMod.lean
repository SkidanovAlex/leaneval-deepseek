import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.EMFG.kOneComparison
import Submission.Work.EMFG.torusFGandEM
import Submission.Work.SSS.ExpTensLES
import Submission.Work.SSS.singularCoeffFG
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Pi6.EMZ.BocksteinCore
import Submission.Work.Pi6.SQASM.Defs
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Pi6.EMODD.kOneIntegralHomology
import Submission.Work.Pi6.EMODD.coeffChangeZMod
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace Work.Pi6.EMODD

noncomputable section

/-! ## Helpers -/

/-- **`H₀` of a path-connected space is the coefficient ring.** -/
theorem hZeroPathConnected (R : Type) [CommRing R] (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] :
    Nonempty ((Work.Cohomology.singularChains R (TopCat.of X)).homology 0 ≅ ModuleCat.of R R) := by
  have h : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R R)).obj (TopCat.of X)) ≅ ModuleCat.of R R :=
    asIso (TopCat.singularHomology₀ε (C := ModuleCat R) (TopCat.of X) (ModuleCat.of R R))
  exact ⟨h⟩

/-- An additive equivalence between `ZMod p`-modules is `ZMod p`-linear. -/
def linearEquivOfAddEquiv (p : ℕ) {M N : Type} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] (e : M ≃+ N) : M ≃ₗ[ZMod p] N where
  toFun := e
  map_add' := e.map_add
  map_smul' := fun c x => by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    simp only [Int.cast_smul_eq_zsmul (ZMod p) n, RingHom.id_apply]
    exact map_zsmul (e : M →+ N) n x
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- The `ℤ`-linear equivalence underlying an isomorphism in `ModuleCat ℤ`. -/
def linearEquivOfIsoInt {A B : ModuleCat ℤ} (e : A ≅ B) : ↥A ≃ₗ[ℤ] ↥B where
  toFun := e.hom
  map_add' := (e.hom.hom).map_add
  map_smul' := (e.hom.hom).map_smul
  invFun := e.inv
  left_inv := fun x => by
    have h2 := congrArg (fun f : A ⟶ A => (ConcreteCategory.hom f) x) e.hom_inv_id
    simpa using h2
  right_inv := fun y => by
    have h2 := congrArg (fun f : B ⟶ B => (ConcreteCategory.hom f) y) e.inv_hom_id
    simpa using h2

/-- The additive equivalence underlying an isomorphism in `ModuleCat ℤ`. -/
def addEquivOfIsoInt {A B : ModuleCat ℤ} (e : A ≅ B) : ↥A ≃+ ↥B where
  toFun := e.hom
  map_add' := (e.hom.hom).map_add
  invFun := e.inv
  left_inv := (linearEquivOfIsoInt e).left_inv
  right_inv := (linearEquivOfIsoInt e).right_inv

/-- The `ZMod p`-dual of `ZMod p` is `ZMod p` (evaluation at `1`). -/
def dualSelfEquiv (p : ℕ) : (ZMod p →ₗ[ZMod p] ZMod p) ≃ₗ[ZMod p] ZMod p where
  toFun f := f 1
  map_add' f g := rfl
  map_smul' a f := rfl
  invFun a := a • LinearMap.id
  left_inv f := LinearMap.ext_ring (by
    show ((f 1) • LinearMap.id) 1 = f 1
    simp [smul_eq_mul])
  right_inv a := by
    show (a • LinearMap.id) 1 = a
    simp [smul_eq_mul]

/-- The universal coefficient theorem over a field, in the shape needed here. -/
theorem cohUCT (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X] (n : ℕ) :
    Nonempty (Work.Pi6.Coh 𝕜 X n ≅
      ModuleCat.of 𝕜 (↥(Work.Pi6.HR 𝕜 X n) →ₗ[𝕜] 𝕜)) :=
  Work.StemsB.fieldDualUCT 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of X)) n

/-- The dual of a `ZMod p`-module isomorphic to `ZMod p` is `ZMod p`. -/
theorem dualIsoOfIso (p : ℕ) {A : ModuleCat (ZMod p)}
    (e : A ≅ ModuleCat.of (ZMod p) (ZMod p)) :
    Nonempty (ModuleCat.of (ZMod p) (↥A →ₗ[ZMod p] ZMod p) ≅
      ModuleCat.of (ZMod p) (ZMod p)) :=
  ⟨LinearEquiv.toModuleIso (LinearEquiv.arrowCongr (Iso.toLinearEquiv e)
    (LinearEquiv.refl (ZMod p) (ZMod p)) ≪≫ₗ dualSelfEquiv p)⟩

/-- The dual of a zero `ZMod p`-module is zero. -/
theorem isZero_dualOfIsZero (p : ℕ) {A : ModuleCat (ZMod p)} (h : IsZero A) :
    IsZero (ModuleCat.of (ZMod p) (↥A →ₗ[ZMod p] ZMod p)) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  exact ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩

/-- The tensor product of a zero module with any module is zero. -/
theorem isZero_tensor_left {M N : ModuleCat ℤ} (h : IsZero M) :
    IsZero (MonoidalCategoryStruct.tensorObj M N) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  refine ⟨fun a b => ?_⟩
  have hzero : ∀ x : ↥(MonoidalCategoryStruct.tensorObj M N), x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [hzero a, hzero b]

/-- `(ℤ ⊗ ℤ/p) ≅ ℤ/p`. -/
theorem tensorUnitIsoZMod (p : ℕ) :
    Nonempty (MonoidalCategoryStruct.tensorObj (ModuleCat.of ℤ ℤ)
      (ModuleCat.of ℤ (ZMod p)) ≅ ModuleCat.of ℤ (ZMod p)) :=
  ⟨λ_ (ModuleCat.of ℤ (ZMod p))⟩

/-- `(A ⊗ ℤ/p) ≅ ℤ/p` when `A ≅ ℤ`. -/
theorem tensorIsoZMod_of_iso (p : ℕ) {A : ModuleCat ℤ} (e : A ≅ ModuleCat.of ℤ ℤ) :
    Nonempty (MonoidalCategoryStruct.tensorObj A (ModuleCat.of ℤ (ZMod p)) ≅
      ModuleCat.of ℤ (ZMod p)) := by
  refine ⟨asIso (e.hom ▷ (ModuleCat.of ℤ (ZMod p))) ≪≫ ?_⟩
  exact λ_ (ModuleCat.of ℤ (ZMod p))

/-- The mod-`p` coefficient sequence `0 → ℤ →·p ℤ → ℤ/p → 0` is short exact. -/
theorem coeffSES_shortExact (p : ℕ) (hp : p.Prime) :
    (Work.Pi6.EMZ.coeffSES p).ShortExact := by
  have key : ∀ x : ℤ, ((p : ℤ) • 𝟙 (Work.Pi6.EMZ.zZ)).hom x = (p : ℤ) * x := by
    intro x
    rw [ModuleCat.hom_smul]
    simp [zsmul_eq_mul]
  have key2 : ∀ y : ℤ, (Work.Pi6.EMZ.redP p).hom y = ((y : ZMod p)) := fun y =>
    Work.Pi6.EMZ.redP_hom_apply p y
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    show Function.Exact (fun x : ℤ => ((p : ℤ) • 𝟙 (Work.Pi6.EMZ.zZ)).hom x)
      (fun y : ℤ => (Work.Pi6.EMZ.redP p).hom y)
    simp only [key, key2]
    intro y
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := dvd_def.mp h
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, hx⟩
      exact dvd_def.mpr ⟨x, hx.symm⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y h
    have h' : ((p : ℤ) • 𝟙 (Work.Pi6.EMZ.zZ)).hom x = ((p : ℤ) • 𝟙 (Work.Pi6.EMZ.zZ)).hom y := h
    simp only at h'
    exact mul_left_cancel₀ (M₀ := ℤ) (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0) h'
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨x, hx⟩ := ZMod.intCast_surjective (n := p) y
    refine ⟨x, ?_⟩
    show (Work.Pi6.EMZ.redP p).hom x = y
    rw [key2]
    exact hx

/-! ## The main theorem -/

/-- **`K(ℤ,1)` range models are `𝔽_p`-acyclic in the range.** For a range model `W` of `K(ℤ,1)`
through `N` and a prime `p`, the mod-`p` cohomology of `W` is that of the circle through degree `N`.

Route: `Work.EMFG.kOneComparison` gives `H_i(W;ℤ) ≅ H_i(S¹;ℤ)` for `i ≤ N`
(`Work.Pi6.EMODD.kOneIntegralHomology`, see also `Work.EMFG.sphOne_isEMSpaceUpTo`: `S¹` is a range
model of `K(ℤ,1)` through any `N`); the coefficient sequence `0 → ℤ →·p ℤ → ZMod p → 0`
(`Work.Pi6.EMZ.coeffSES` plus `Work.SSS.expTensShort`) computes `H_i(W;ZMod p)` from it
(`Work.Pi6.EMODD.coeffChangeZMod`; the `Tor` term vanishes because `H_{i-1}(W;ℤ)` is free in the
range), and field duality (`Work.StemsB.fieldDualUCT`) converts to cohomology. -/
theorem kOneMod (p : ℕ) [Fact p.Prime] (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W)
    (hW : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N W w₀) :
    (Nonempty (Work.Pi6.Coh (ZMod p) W 0 ≅ ModuleCat.of (ZMod p) (ZMod p))) ∧
      (Nonempty (Work.Pi6.Coh (ZMod p) W 1 ≅ ModuleCat.of (ZMod p) (ZMod p))) ∧
      (∀ q : ℕ, 2 ≤ q → q ≤ N → CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod p) W q)) := by
  classical
  have hp : p.Prime := Fact.out
  -- Step 1: `W` is path connected.
  haveI hpcW : PathConnectedSpace W :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero w₀
      (hW.2 0 (by norm_num) (Or.inl (by norm_num)))
  -- Step 2: work in the range `max N 1`.  For `N ≥ 1` this is `N` itself; for `N = 0` the
  -- hypotheses (`IsEMSpaceUpTo ℤ 1 _ 0`) already give the range-`1` statement, because the only
  -- degree `< 1` is `0`, so that `H₁` is available in the unconditional conjuncts below.
  have hWmax : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) (max N 1) W w₀ := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      refine ⟨hW.1, fun i hi hc => hW.2 i hi (hc.elim Or.inl (fun h => Or.inl (by omega)))⟩
    · rw [max_eq_left (by omega : 1 ≤ N)]
      exact hW
  obtain ⟨hint01, hint2⟩ := kOneIntegralHomology (max N 1) W w₀ hWmax
  have hint0 : Nonempty (Work.Pi6.HR ℤ W 0 ≅ ModuleCat.of ℤ ℤ) :=
    hint01 0 (by norm_num) (by omega)
  have hint1 : Nonempty (Work.Pi6.HR ℤ W 1 ≅ ModuleCat.of ℤ ℤ) :=
    hint01 1 (by norm_num) (by omega)
  -- Step 3: the integral homology groups in the range are free.
  have hfreeI : ∀ i : ℕ, i ≤ max N 1 → Module.Free ℤ ↥(Work.Pi6.HR ℤ W i) := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      exact Module.Free.of_equiv (M' := ↥(Work.Pi6.HR ℤ W 0))
        (linearEquivOfIsoInt hint0.some).symm
    by_cases h1 : i = 1
    · subst h1
      exact Module.Free.of_equiv (M' := ↥(Work.Pi6.HR ℤ W 1))
        (linearEquivOfIsoInt hint1.some).symm
    · haveI : Subsingleton ↥(Work.Pi6.HR ℤ W i) :=
        ModuleCat.isZero_iff_subsingleton.mp (hint2 i (by omega) hi)
      exact Module.Free.of_subsingleton ℤ _
  -- Step 4: the mod-`p` homology in the range.
  have hmod0 : Nonempty (Work.Pi6.HR (ZMod p) W 0 ≅ ModuleCat.of (ZMod p) (ZMod p)) :=
    hZeroPathConnected (ZMod p) W
  have hcc1 : Nonempty ((Work.SSS.expTens (Work.Pi6.EMZ.chZ W) (ModuleCat.of ℤ (ZMod p))).homology 1 ≅
      CategoryTheory.MonoidalCategoryStruct.tensorObj (Work.Pi6.HR ℤ W 1)
        (ModuleCat.of ℤ (ZMod p))) :=
    coeffChangeZMod p (Work.Pi6.EMZ.chZ W) 1 (by norm_num) (coeffSES_shortExact p hp)
      (fun i => Work.Pi6.EMZ.chZ_flat W i) (hfreeI 0 (by omega))
  have hmod1 : Nonempty (Work.Pi6.HR (ZMod p) W 1 ≅ ModuleCat.of (ZMod p) (ZMod p)) := by
    obtain ⟨eB⟩ := hcc1
    obtain ⟨eT⟩ := tensorIsoZMod_of_iso p hint1.some
    refine ⟨LinearEquiv.toModuleIso (linearEquivOfAddEquiv p ?_)⟩
    exact (Work.Pi6.EMZ.expTensCoeffAddEquiv p hp W 1).symm.trans (addEquivOfIsoInt (eB ≪≫ eT))
  have hmodZ : ∀ q : ℕ, 2 ≤ q → q ≤ max N 1 → IsZero (Work.Pi6.HR (ZMod p) W q) := by
    intro q hq2 hqN
    have hq1 : 1 ≤ q := by omega
    obtain ⟨eB⟩ := coeffChangeZMod p (Work.Pi6.EMZ.chZ W) q hq1 (coeffSES_shortExact p hp)
      (fun i => Work.Pi6.EMZ.chZ_flat W i) (hfreeI (q - 1) (by omega))
    have hzK : IsZero (Work.Pi6.HR ℤ W q) := hint2 q hq2 hqN
    have hzT : IsZero (CategoryTheory.MonoidalCategoryStruct.tensorObj (Work.Pi6.HR ℤ W q)
        (ModuleCat.of ℤ (ZMod p))) := isZero_tensor_left hzK
    have hzE : IsZero ((Work.SSS.expTens (Work.Pi6.EMZ.chZ W)
        (ModuleCat.of ℤ (ZMod p))).homology q) := IsZero.of_iso hzT eB
    haveI : Subsingleton ↥((Work.SSS.expTens (Work.Pi6.EMZ.chZ W)
        (ModuleCat.of ℤ (ZMod p))).homology q) :=
      ModuleCat.isZero_iff_subsingleton.mp hzE
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ((Work.Pi6.EMZ.expTensCoeffAddEquiv p hp W q).symm.injective.subsingleton)
  -- Step 5: pass to cohomology via the field universal coefficient theorem.
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨e⟩ := cohUCT (ZMod p) W 0
    obtain ⟨ee⟩ := dualIsoOfIso p hmod0.some
    exact ⟨e ≪≫ ee⟩
  · obtain ⟨e⟩ := cohUCT (ZMod p) W 1
    obtain ⟨ee⟩ := dualIsoOfIso p hmod1.some
    exact ⟨e ≪≫ ee⟩
  · intro q hq2 hqN
    have hzHR : IsZero (Work.Pi6.HR (ZMod p) W q) := hmodZ q hq2 (le_trans hqN (le_max_left N 1))
    have hzD := isZero_dualOfIsZero p hzHR
    obtain ⟨e⟩ := cohUCT (ZMod p) W q
    exact IsZero.of_iso hzD e

end

end Work.Pi6.EMODD
