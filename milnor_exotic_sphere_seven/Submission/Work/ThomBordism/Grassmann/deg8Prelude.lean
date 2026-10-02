import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.Thom.bijective_proj_zeroComplementA
import Submission.Work.ThomBordism.Grassmann.incidenceFibreCohomologyRat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# Preliminaries for the degree-eight Borel chain

This module collects the reusable pieces of the degree-eight computation of the rational
cohomology of the oriented Grassmannian:

* `Deg8.R m j k` / `Deg8.S m j k`: the rational cohomology `H^j(G̃r_k(ℝ^{k+m});ℚ)` of the
  Grassmannian and `H^j(S γ_k;ℚ)` of the sphere bundle of the tautological bundle;
* `Deg8.rank_exact_le`, `Deg8.rank_add_le_of_shortExact`: the two cardinal-rank bookkeeping
  lemmas for an exact sequence over `ℚ` (used in place of the `finrank` versions so that no
  finiteness hypotheses are needed);
* `gysinEulerQ`, `gysinπQ`, `gysinδQ` and the three rationalized Gysin exactness statements;
* `Deg8.gysinπ_tautological_bijective`, `Deg8.injective_gysinπ_of_lt_rank`: the middle map
  `π^*` is bijective in the stable range `j + 2 ≤ k` and injective for `j < k`;
* `Deg8.tmul_one_eq_zero_of_two_zsmul_eq_zero` and `Deg8.gysinEulerQ_eq_zero_of_two_smul`:
  the vanishing of the rationalized `∪e` for a bundle whose Euler class is `2`-torsion;
* `Deg8.win_le`, `Deg8.win_odd_le`: the two dimension relations read off the Gysin window
  `H^{j-k}(B) --∪e--> H^j(B) --π*--> H^j(S E) --> H^{j-k+1}(B)`, in the cases `j ≥ k` (all `k`)
  and `j ≥ k` with odd `k` (where the two `∪e` maps vanish, making the window short exact);
* `Deg8.rank_S_eq_R` (the incidence step) and `Deg8.rank_eq_of_descent` (the stable-range step).
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

open scoped TensorProduct

noncomputable section

namespace Deg8

universe u

/-- `H^j(G̃r_k(ℝ^{k+m});ℚ)`, the rational cohomology of the oriented Grassmannian. -/
abbrev R (m j k : ℕ) : Type :=
  Work.SignatureBordism.ratCohomology j (sset (OG k m))

/-- `H^j(S γ_k;ℚ)`, the rational cohomology of the sphere bundle of the tautological bundle. -/
abbrev S (m j k : ℕ) : Type :=
  Work.SignatureBordism.ratCohomology j (sset (Work.Thom.zeroComplement (tautologicalBundle k m)))

/-! ## Cardinal rank bookkeeping for exact sequences -/

/-- **A three-term exact sequence bounds the middle rank**: for `V₀ --f--> V₁ --g--> V₂` exact,
`rank V₁ ≤ rank V₀ + rank V₂`.  Unlike the `finrank` version this needs no finiteness
hypotheses. -/
theorem rank_exact_le {V₀ V₁ V₂ : Type u} [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup V₂]
    [Module ℚ V₀] [Module ℚ V₁] [Module ℚ V₂]
    (f : V₀ →ₗ[ℚ] V₁) (g : V₁ →ₗ[ℚ] V₂) (h : Function.Exact f g) :
    Module.rank ℚ V₁ ≤ Module.rank ℚ V₀ + Module.rank ℚ V₂ := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp h
  have hg' : Module.rank ℚ (LinearMap.range g) ≤ Module.rank ℚ V₂ :=
    Submodule.rank_le (LinearMap.range g)
  have hf' : Module.rank ℚ (LinearMap.range f) ≤ Module.rank ℚ V₀ := by
    calc Module.rank ℚ (LinearMap.range f)
        = Module.rank ℚ (LinearMap.range f) + 0 := (add_zero _).symm
      _ ≤ Module.rank ℚ (LinearMap.range f) + Module.rank ℚ (LinearMap.ker f) :=
          add_le_add le_rfl (zero_le)
      _ = Module.rank ℚ V₀ := LinearMap.rank_range_add_rank_ker f
  have hmain : Module.rank ℚ V₁
      = Module.rank ℚ (LinearMap.range g) + Module.rank ℚ (LinearMap.range f) := by
    rw [← LinearMap.rank_range_add_rank_ker g, hker]
  rw [hmain]
  exact le_trans (add_le_add hg' hf') (le_of_eq (add_comm _ _))

/-- **A short exact sequence bounds the outer ranks**: for `V₁ --f--> V₂ --g--> V₃` exact with
`f` injective and `g` surjective, `rank V₁ + rank V₃ ≤ rank V₂`. -/
theorem rank_add_le_of_shortExact {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [AddCommGroup V₂]
    [AddCommGroup V₃] [Module ℚ V₁] [Module ℚ V₂] [Module ℚ V₃]
    (f : V₁ →ₗ[ℚ] V₂) (g : V₂ →ₗ[ℚ] V₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) :
    Module.rank ℚ V₁ + Module.rank ℚ V₃ ≤ Module.rank ℚ V₂ := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp h
  have h1 : Module.rank ℚ (LinearMap.range f) = Module.rank ℚ V₁ := rank_range_of_injective f hf
  have h2 : Module.rank ℚ (LinearMap.range g) = Module.rank ℚ V₃ := rank_range_of_surjective g hg
  have hmain : Module.rank ℚ V₁ + Module.rank ℚ V₃ = Module.rank ℚ V₂ := by
    rw [← h1, ← h2, ← hker, add_comm]
    exact LinearMap.rank_range_add_rank_ker g
  exact le_of_eq hmain

/-! ## The rationalized Gysin window

For a real bundle `Z` over `B` of rank `n` with a Thom class `T`, the Gysin sequence

  `H^a(B) --∪e--> H^{a+n}(B) --π*--> H^{a+n}(S Z) --δ--> H^{a+1}(B) --∪e--> H^{(a+1)+n}(B)`

(`Work.Thom.gysin_exact_at_base`/`_at_sphere`/`_at_cobase`) is rationalized here: since `ℚ` is a
flat `ℤ`-module, tensoring with `ℚ` preserves exactness, and the resulting maps are `ℚ`-linear. -/

/-- The rationalized `∪e` map of the Gysin sequence, as a `ℚ`-linear map. -/
noncomputable def gysinEulerQ {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (n : ℕ)
    (T : Work.Thom.ThomClass Z n) (a : ℕ) :
    (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ a B : Type)) →ₗ[ℚ]
      (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ (a+n) B : Type)) :=
  (Work.Thom.gysinEuler T a).baseChange ℚ

/-- The rationalized map `π*` of the Gysin sequence. -/
noncomputable def gysinπQ {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (j : ℕ) :
    (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ j B : Type)) →ₗ[ℚ]
      (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ j (Work.Thom.zeroComplement Z) : Type)) :=
  (Work.Thom.gysinπ Z j).baseChange ℚ

/-- The rationalized transgression `δ` of the Gysin sequence. -/
noncomputable def gysinδQ {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (n : ℕ)
    (T : Work.Thom.ThomClass Z n) (a : ℕ) :
    (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ (a+n) (Work.Thom.zeroComplement Z) : Type)) →ₗ[ℚ]
      (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ (a+1) B : Type)) :=
  (Work.Thom.gysinδ T a).baseChange ℚ

/-- **The rationalized Gysin window is exact at the base term**: `range (∪e) = ker (π*)`. -/
theorem gysin_exact_at_base_rat {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (n : ℕ) (T : Work.Thom.ThomClass Z n) (a : ℕ) :
    Function.Exact (gysinEulerQ Z n T a) (gysinπQ Z (a+n)) := by
  have hex : Function.Exact (Work.Thom.gysinEuler T a) (Work.Thom.gysinπ Z (a+n)) := by
    rw [LinearMap.exact_iff]
    ext y
    rw [LinearMap.mem_ker]
    constructor
    · intro hy
      have hmem : y ∈ Set.range (Work.Thom.gysinEuler T a) := by
        rw [Work.Thom.gysin_exact_at_base T a]; exact hy
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      have hmem : (Work.Thom.gysinEuler T a) x ∈ Set.range (Work.Thom.gysinEuler T a) := ⟨x, rfl⟩
      rw [Work.Thom.gysin_exact_at_base T a] at hmem
      exact hmem
  have h := Module.Flat.lTensor_exact ℚ hex
  rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h

/-- **The rationalized Gysin window is exact at the sphere term**: `range (π*) = ker δ`. -/
theorem gysin_exact_at_sphere_rat {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (n : ℕ) (T : Work.Thom.ThomClass Z n) (a : ℕ) :
    Function.Exact (gysinπQ Z (a+n)) (gysinδQ Z n T a) := by
  have hex : Function.Exact (Work.Thom.gysinπ Z (a+n)) (Work.Thom.gysinδ T a) := by
    rw [LinearMap.exact_iff]
    ext y
    rw [LinearMap.mem_ker]
    constructor
    · intro hy
      rw [Work.Thom.gysinδ_eq_zero_iff T a y] at hy
      have hmem : y ∈ Set.range (Work.Thom.gysinπ Z (a+n)) := by
        rw [Work.Thom.gysin_exact_at_sphere T a]; exact hy
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      have hmem : (Work.Thom.gysinπ Z (a+n)) x ∈ Set.range (Work.Thom.gysinπ Z (a+n)) := ⟨x, rfl⟩
      rw [Work.Thom.gysin_exact_at_sphere T a] at hmem
      rwa [Work.Thom.gysinδ_eq_zero_iff T a ((Work.Thom.gysinπ Z (a+n)) x)]
  have h := Module.Flat.lTensor_exact ℚ hex
  rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h

/-- **The rationalized Gysin window is exact at the cobase term**: `range δ = ker (∪e)`. -/
theorem gysin_exact_at_cobase_rat {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (n : ℕ) (T : Work.Thom.ThomClass Z n) (a : ℕ) :
    Function.Exact (gysinδQ Z n T a) (gysinEulerQ Z n T (a+1)) := by
  have hex : Function.Exact (Work.Thom.gysinδ T a) (Work.Thom.gysinEuler T (a+1)) := by
    rw [LinearMap.exact_iff]
    ext y
    rw [LinearMap.mem_ker]
    constructor
    · intro hy
      have hmem : y ∈ Set.range (Work.Thom.gysinδ T a) := by
        rw [Work.Thom.gysin_exact_at_cobase T a]; exact hy
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      have hmem : (Work.Thom.gysinδ T a) x ∈ Set.range (Work.Thom.gysinδ T a) := ⟨x, rfl⟩
      rw [Work.Thom.gysin_exact_at_cobase T a] at hmem
      exact hmem
  have h := Module.Flat.lTensor_exact ℚ hex
  rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h

/-! ## The middle map `π^*` of the Gysin sequence -/

/-- **The Gysin descent for the tautological bundle**: cupping with the Thom class, i.e. the map
`π_S^* : H^j(G;ℤ) → H^j(S γ;ℤ)`, is bijective whenever `j + 2 ≤ k`. -/
theorem gysinπ_tautological_bijective (k m j : ℕ) (hj : j + 2 ≤ k) :
    Function.Bijective (Work.Thom.gysinπ (tautologicalBundle k m) j) := by
  have hb := Work.Thom.bijective_proj_zeroComplementA (tautologicalBundle k m)
    (show Module.finrank ℝ (Amb k) = k from by simp [Amb]) (tautologicalThomClass k m) hj
  have hcomp : (Work.Thom.CohMap ((Work.Thom.bundleProj (tautologicalBundle k m)).comp
      (Work.Thom.subtypeMap (Work.Thom.zeroComplement (tautologicalBundle k m)))) ℤ j).hom
      = (Work.Thom.gysinπ (tautologicalBundle k m) j) := by
    rw [Work.Thom.CohMap_comp (Work.Thom.subtypeMap (Work.Thom.zeroComplement (tautologicalBundle k m)))
      (Work.Thom.bundleProj (tautologicalBundle k m)) ℤ j]
    rfl
  rwa [hcomp] at hb

/-- **The stable-range step**: for `j + 2 ≤ k` the rational cohomology of the Grassmannian in
degree `j` agrees with that of the sphere bundle of its tautological bundle. -/
theorem rank_eq_of_descent (k m j : ℕ) (hj : j + 2 ≤ k) :
    Module.rank ℚ (R m j k) = Module.rank ℚ (S m j k) := by
  have hbij := gysinπ_tautological_bijective k m j hj
  have e : (Work.Thom.Coh ℤ j (OG k m)) ≃ₗ[ℤ]
      (Work.Thom.Coh ℤ j (Work.Thom.zeroComplement (tautologicalBundle k m))) :=
    LinearEquiv.ofBijective _ hbij
  exact (LinearEquiv.baseChange ℤ ℚ _ _ e).rank_eq

/-- **The Gysin map `π^*` is injective below the rank**: for a real bundle `Z` whose model fibre
has dimension `n`, `gysinπ Z j` is injective whenever `j < n`. -/
theorem injective_gysinπ_of_lt_rank {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (j : ℕ) (hj : j < Module.finrank ℝ F) :
    Function.Injective (Work.Thom.gysinπ Z j) := by
  haveI hsub : Subsingleton (Work.Thom.OpenThom Z j) :=
    Work.Thom.subsingleton_OpenThom_genFibreA Z j hj
  have hrel : (Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) j).hom = 0 := by
    ext x
    have hx : x = 0 := @Subsingleton.elim (Work.Thom.OpenThom Z j) hsub x 0
    rw [hx]
    exact map_zero _
  have hker : (Work.Thom.restrCoh (Work.Thom.zeroComplement Z) ℤ j).hom.ker = ⊥ := by
    rw [← Work.Thom.pairRange_eq_ker₂ (Work.Thom.zeroComplement Z) j, hrel, LinearMap.range_zero]
  have hinj : Function.Injective (Work.Thom.restrCoh (Work.Thom.zeroComplement Z) ℤ j).hom :=
    LinearMap.ker_eq_bot.mp hker
  have hb := Work.Thom.bijective_CohMap_bundleProj Z j
  exact hinj.comp hb.1

/-- The injectivity specialized to the tautological bundle: `gysinπ (tautologicalBundle k m) j` is
injective for `j < k`. -/
theorem injective_gysinπ_tautological (k m j : ℕ) (hj : j < k) :
    Function.Injective (Work.Thom.gysinπ (tautologicalBundle k m) j) :=
  injective_gysinπ_of_lt_rank (tautologicalBundle k m) j (by simpa [Amb] using hj)

/-! ## Vanishing of the rationalized `∪e` for a `2`-torsion Euler class -/

/-- **A pure tensor with a `2`-torsion second factor vanishes in `ℚ ⊗[ℤ] M`** (instance-free form:
the hypothesis `y + y = 0` avoids all scalar-instance friction). -/
theorem tmul_eq_zero_of_add_self_eq_zero {M : Type*} [AddCommGroup M] [Module ℤ M] (q : ℚ) {y : M}
    (h : y + y = 0) : q ⊗ₜ[ℤ] y = 0 := by
  have h2 : (2 : ℚ) • (q ⊗ₜ[ℤ] y) = 0 := by
    rw [two_smul ℚ (q ⊗ₜ[ℤ] y)]
    rw [← TensorProduct.tmul_add, h, TensorProduct.tmul_zero]
  have h3 := congrArg (fun z => (2 : ℚ)⁻¹ • z) h2
  simpa using h3

/-- **The rationalized `∪e` vanishes when the Euler class is `2`-torsion.** -/
theorem gysinEulerQ_eq_zero_of_two_zsmul {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (n a : ℕ)
    (T : Work.Thom.ThomClass Z n) (hT : (2 : ℤ) • T.eulerClass = 0) :
    gysinEulerQ Z n T a = 0 := by
  have he : T.eulerClass + T.eulerClass = 0 := (two_zsmul T.eulerClass).symm.trans hT
  change (Work.Thom.gysinEuler T a).baseChange ℚ = 0
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply]
  refine TensorProduct.induction_on
    (motive := fun x => (Work.Thom.gysinEuler T a).baseChange ℚ x = 0) x ?_ ?_ ?_
  · exact map_zero _
  · intro q y
    rw [LinearMap.baseChange_tmul]
    let y' : ↥((Work.Cohomology.cochainC ℤ (sset B)).homology a) := y
    let e' : ↥((Work.Cohomology.cochainC ℤ (sset B)).homology n) := T.eulerClass
    have he' : e' + e' = 0 := he
    have hzz : Work.Cohomology.cupH' ℤ (sset B) a n y' e'
        + Work.Cohomology.cupH' ℤ (sset B) a n y' e' = 0 := by
      rw [← Work.Cohomology.cupH'_add_right (R := ℤ) (X := sset B) a n y' e' e', he', map_zero]
    have hge : Work.Thom.gysinEuler T a y = Work.Cohomology.cupH' ℤ (sset B) a n y' e' := by
      rw [Work.Thom.gysinEuler_eq_cupEuler]
    have hzz' : Work.Thom.gysinEuler T a y + Work.Thom.gysinEuler T a y = 0 := by
      simpa only [hge] using hzz
    exact tmul_eq_zero_of_add_self_eq_zero q hzz'
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- **A short exact sequence bounds the middle rank from above**: for `V₁ --f--> V₂ --g--> V₃` with
`f` injective and exact at `V₂`, `rank V₂ ≤ rank V₁ + rank V₃`. -/
theorem rank_le_add_of_shortExact {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [AddCommGroup V₂]
    [AddCommGroup V₃] [Module ℚ V₁] [Module ℚ V₂] [Module ℚ V₃]
    (f : V₁ →ₗ[ℚ] V₂) (g : V₂ →ₗ[ℚ] V₃) (hf : Function.Injective f)
    (h : Function.Exact f g) :
    Module.rank ℚ V₂ ≤ Module.rank ℚ V₁ + Module.rank ℚ V₃ := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp h
  have h1 : Module.rank ℚ (LinearMap.range f) = Module.rank ℚ V₁ := rank_range_of_injective f hf
  have h2 : Module.rank ℚ (LinearMap.range g) ≤ Module.rank ℚ V₃ := Submodule.rank_le _
  have hmain : Module.rank ℚ V₂ = Module.rank ℚ (LinearMap.range g) + Module.rank ℚ (LinearMap.range f) := by
    rw [← LinearMap.rank_range_add_rank_ker g, hker]
  rw [hmain, h1]
  exact le_trans (add_le_add h2 le_rfl) (le_of_eq (add_comm _ _))

/-! ## The Gysin window relations -/

/-- **The window bound at a source degree `≥ 0`**: the Gysin window
`H^{j-k}(G_k) --∪e--> H^j(G_k) --π^*--> H^j(S γ_k)` is exact at the middle term, hence
`rank H^j(G_k) ≤ rank H^{j-k}(G_k) + rank H^j(S γ_k)`. -/
theorem win_le (k m j : ℕ) (hj : k ≤ j) :
    Module.rank ℚ (R m j k) ≤ Module.rank ℚ (R m (j - k) k) + Module.rank ℚ (S m j k) := by
  have h := rank_exact_le
    (gysinEulerQ (tautologicalBundle k m) k (tautologicalThomClass k m) (j - k))
    (gysinπQ (tautologicalBundle k m) ((j - k) + k))
    (gysin_exact_at_base_rat (tautologicalBundle k m) k (tautologicalThomClass k m) (j - k))
  rw [Nat.sub_add_cancel hj] at h
  exact h

/-- **The short exact window at a source degree `≥ 0` for odd `k`**: when the Euler class is
`2`-torsion, both `∪e` maps of the window vanish, so
`0 → H^j(B) → H^j(S E) → H^{j-k+1}(B) → 0` is short exact and
`rank H^j(B) + rank H^{j-k+1}(B) ≤ rank H^j(S E)`. -/
theorem win_odd_le {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (n a : ℕ)
    (T : Work.Thom.ThomClass Z n) (hT : (2 : ℤ) • T.eulerClass = 0) :
    Module.rank ℚ (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ (a+n) B : Type))
      + Module.rank ℚ (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ (a+1) B : Type))
      ≤ Module.rank ℚ
          (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ (a+n) (Work.Thom.zeroComplement Z) : Type)) := by
  have hzero1 : gysinEulerQ Z n T a = 0 := gysinEulerQ_eq_zero_of_two_zsmul Z n a T hT
  have hzero2 : gysinEulerQ Z n T (a+1) = 0 := gysinEulerQ_eq_zero_of_two_zsmul Z n (a+1) T hT
  refine rank_add_le_of_shortExact (gysinπQ Z (a+n)) (gysinδQ Z n T a) ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot]
    have h := (LinearMap.exact_iff.mp (gysin_exact_at_base_rat Z n T a))
    rw [h, hzero1, LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top]
    have h := (LinearMap.exact_iff.mp (gysin_exact_at_cobase_rat Z n T a))
    rw [← h, hzero2, LinearMap.ker_zero]
  · exact gysin_exact_at_sphere_rat Z n T a

/-! ## The incidence and stable-range identifications -/

/-- **The incidence step as an equality of ranks**: for `1 ≤ j ≤ k+m-3`,
`H^j(S γ_k;ℚ) ≅ H^j(G̃r_{k-1}(ℝ^{k+m});ℚ)`. -/
theorem rank_S_eq_R (k m j : ℕ) (hk : 1 ≤ k) (hj1 : 1 ≤ j) (hj : j ≤ k + m - 3) :
    Module.rank ℚ (S m j k) = Module.rank ℚ (R m j (k - 1)) := by
  obtain ⟨e⟩ := incidenceFibreCohomologyRat k m j hk hj1 hj
  exact e.rank_eq

end Deg8

end

end Work.ThomBordism.Grassmann
