import Mathlib
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.Tubular.exists_halfOrientationFamily_euclidean
import Submission.Work.ThomBordism.localGeneration

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Euclidean model family of local generators, and its two invariance properties

This file develops the API of the coherent family of local generators of `ℝ^N` supplied by
`Work.Tubular.exists_halfOrientationFamily_euclidean`, and proves the two facts about it that the
target `Work.PTGeometric.exists_halfOrientationFamily_of_det_pos` needs:

* `Work.PTGeometric.HOF.eucFam_translation` — the family is *translation invariant*;
* `Work.PTGeometric.HOF.eucFam_germ` — a `C^1` germ whose derivative is invertible with positive
  determinant preserves the family.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.PTGeometric.HOF

noncomputable section

/-- The Euclidean model space `ℝ^N`. -/
abbrev Euc (N : ℕ) := EuclideanSpace ℝ (Fin N)

variable {N : ℕ}

/-- **The coherent family of local generators of `ℝ^N`**, chosen once and for all. -/
noncomputable def eucFam (N : ℕ) (hN : 1 ≤ N) :
    ∀ y : Euc N, Work.Orient.LocH (TopCat.of (Euc N)) N y :=
  Classical.choose (Work.Tubular.exists_halfOrientationFamily_euclidean N hN)

/-- Each `eucFam y` generates the local homology at `y`. -/
theorem eucFam_gen (N : ℕ) (hN : 1 ≤ N) (y : Euc N) :
    Submodule.span ℤ ({eucFam N hN y} :
      Set (Work.Orient.LocH (TopCat.of (Euc N)) N y)) = ⊤ :=
  (Classical.choose_spec (Work.Tubular.exists_halfOrientationFamily_euclidean N hN)).1 y

/-- The family is coherent over every compact set. -/
theorem eucFam_coh (N : ℕ) (hN : 1 ≤ N) (K : Set (Euc N)) (hK : IsCompact K) :
    ∃ a : Work.Orient.RelH (TopCat.of (Euc N)) N K,
      ∀ (y : Euc N) (hy : y ∈ K),
        Work.Orient.resRelH (TopCat.of (Euc N)) N (Set.singleton_subset_iff.mpr hy) a
          = eucFam N hN y :=
  (Classical.choose_spec (Work.Tubular.exists_halfOrientationFamily_euclidean N hN)).2 K hK

/-- **The canonical class over a compact set**: a class of `H_N(ℝ^N, ℝ^N∖K)` whose localisation at
every point of `K` is `eucFam`. -/
noncomputable def eucCanon (N : ℕ) (hN : 1 ≤ N) (K : Set (Euc N)) (hK : IsCompact K) :
    Work.Orient.RelH (TopCat.of (Euc N)) N K :=
  Classical.choose (eucFam_coh N hN K hK)

/-- The defining property of `eucCanon`. -/
theorem eucCanon_spec (N : ℕ) (hN : 1 ≤ N) (K : Set (Euc N)) (hK : IsCompact K)
    (y : Euc N) (hy : y ∈ K) :
    Work.Orient.resRelH (TopCat.of (Euc N)) N (Set.singleton_subset_iff.mpr hy)
        (eucCanon N hN K hK) = eucFam N hN y :=
  Classical.choose_spec (eucFam_coh N hN K hK) y hy

/-! ## Coefficients with respect to a `ℤ`-basis of the local group -/

/-- The transport of a multiple of `x` along an isomorphism of `ℤ`-modules with `ℤ`. -/
theorem iso_toSpanSingleton {M : Type*} [AddCommGroup M] [Module ℤ M] (e : M ≃ₗ[ℤ] ℤ)
    (x : M) (k : ℤ) : e (LinearMap.toSpanSingleton ℤ M x k) = k * e x := by
  have h : e (LinearMap.toSpanSingleton ℤ M x k) = LinearMap.toSpanSingleton ℤ ℤ (e x) k := by
    have h' := congrArg (fun (φ : ℤ →ₗ[ℤ] ℤ) => φ k)
      (LinearMap.comp_toSpanSingleton e.toLinearMap x)
    simpa [LinearMap.comp_apply] using h'
  rw [h, LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The image of a generator under an isomorphism of `ℤ`-modules with `ℤ` is `±1`. -/
theorem iso_gen_pm_one {M : Type*} [AddCommGroup M] [Module ℤ M] {x : M}
    (hgen : Submodule.span ℤ ({x} : Set M) = ⊤) (e : M ≃ₗ[ℤ] ℤ) :
    e x = 1 ∨ e x = -1 := by
  have hmem : e.symm 1 ∈ LinearMap.range (LinearMap.toSpanSingleton ℤ M x) := by
    rw [LinearMap.range_toSpanSingleton, hgen]
    exact Submodule.mem_top
  obtain ⟨m, hm⟩ := hmem
  have h3 : m * e x = 1 := by
    have h4 : e (LinearMap.toSpanSingleton ℤ M x m) = 1 := by
      rw [hm, LinearEquiv.apply_symm_apply]
    rwa [iso_toSpanSingleton] at h4
  have h5 : ((m * e x).natAbs) = 1 := by rw [h3]; rfl
  rw [Int.natAbs_mul] at h5
  have h6 : (e x).natAbs = 1 := Nat.eq_one_of_mul_eq_one_left h5
  rcases Int.natAbs_eq_iff.mp h6 with h7 | h7
  · exact Or.inl h7
  · exact Or.inr h7

/-- The image of a generator under an isomorphism of `ℤ`-modules with `ℤ` is nonzero. -/
theorem iso_gen_ne_zero {M : Type*} [AddCommGroup M] [Module ℤ M] {x : M}
    (hgen : Submodule.span ℤ ({x} : Set M) = ⊤) (e : M ≃ₗ[ℤ] ℤ) : e x ≠ 0 := by
  rcases iso_gen_pm_one hgen e with h | h <;> rw [h] <;> norm_num

/-- Two `ℤ`-multiples of a generator of a `ℤ`-module isomorphic to `ℤ` have equal coefficients. -/
theorem coeff_eq_of_smul_eq {M : Type*} [AddCommGroup M] [Module ℤ M] {x : M}
    (hgen : Submodule.span ℤ ({x} : Set M) = ⊤) (e : M ≃ₗ[ℤ] ℤ) {k k' : ℤ}
    (h : k • x = k' • x) : k = k' := by
  have h1 : e (k • x) = e (k' • x) := congrArg e h
  rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at h1
  exact mul_right_cancel₀ (iso_gen_ne_zero hgen e) h1

/-- The coefficient of a composed `ℤ`-multiple of a generator: if `a • (b • x) = c • x` then
`c = a * b`. -/
theorem coeff_mul_of_smul {M : Type*} [AddCommGroup M] [Module ℤ M] {x : M}
    (hgen : Submodule.span ℤ ({x} : Set M) = ⊤) (e : M ≃ₗ[ℤ] ℤ) {a b c : ℤ}
    (h : a • (b • x) = c • x) : c = a * b := by
  have h1 : e (a • (b • x)) = e (c • x) := congrArg e h
  rw [map_zsmul, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h1
  have h2 : a * (b * e x) = c * e x := h1
  refine (mul_right_cancel₀ (iso_gen_ne_zero hgen e) ?_).symm
  rw [mul_assoc]
  exact h2

/-- If `k • x` generates and `x` generates then `k = ±1`. -/
theorem eq_pm_one_of_smul_span {M : Type*} [AddCommGroup M] [Module ℤ M] {x : M}
    (hgen : Submodule.span ℤ ({x} : Set M) = ⊤) (e : M ≃ₗ[ℤ] ℤ) {k : ℤ}
    (h : Submodule.span ℤ ({k • x} : Set M) = ⊤) : k = 1 ∨ k = -1 := by
  have hmem : x ∈ LinearMap.range (LinearMap.toSpanSingleton ℤ M (k • x)) := by
    rw [LinearMap.range_toSpanSingleton, h]
    exact Submodule.mem_top
  obtain ⟨m, hm⟩ := hmem
  have h3 : e x = m * (k * e x) := by
    have h4 : e x = e (LinearMap.toSpanSingleton ℤ M (k • x) m) := by rw [hm]
    rw [iso_toSpanSingleton] at h4
    rw [map_zsmul, smul_eq_mul] at h4
    exact h4
  have hmk : m * k = 1 := by
    rcases iso_gen_pm_one hgen e with h5 | h5
    · have h6 : (1 : ℤ) = m * (k * 1) := by rw [h5] at h3; exact h3
      simpa using h6.symm
    · have h6 : (-1 : ℤ) = m * (k * (-1)) := by rw [h5] at h3; exact h3
      have h7 : -(m * k) = -1 := by
        rw [show k * (-1) = -k by ring, show m * (-k) = -(m * k) by ring] at h6
        exact h6.symm
      exact neg_injective h7
  have h8 : ((m * k).natAbs) = 1 := by rw [hmk]; rfl
  rw [Int.natAbs_mul] at h8
  have h9 : (k.natAbs) = 1 := Nat.eq_one_of_mul_eq_one_left h8
  rcases Int.natAbs_eq_iff.mp h9 with h10 | h10
  · exact Or.inl h10
  · exact Or.inr h10

/-! ## The coordinate balls of the Euclidean model, and the localisation out of them -/

/-- The coordinate ball of the Euclidean model: the chart preimage of a closed ball. -/
abbrev cball (N : ℕ) (z : Euc N) (r : ℝ) : Set (Euc N) :=
  (chartAt (Euc N) z) ⁻¹' Metric.closedBall ((chartAt (Euc N) z) z) (r / 2) ∩
    (chartAt (Euc N) z).source

/-- A coordinate ball of `ℝ^N` is the closed ball of the ambient metric. -/
theorem cball_eq (N : ℕ) (z : Euc N) (r : ℝ) : cball N z r = Metric.closedBall z (r / 2) := by
  rw [cball, chartAt_self_eq]
  simp

/-- The centre of a coordinate ball belongs to it. -/
theorem mem_cball_center (N : ℕ) (z : Euc N) (r : ℝ) (hr : 0 < r) : z ∈ cball N z r := by
  rw [cball_eq]
  exact Metric.mem_closedBall_self (by linarith)

/-- Coordinate balls are compact. -/
theorem isCompact_cball (N : ℕ) (z : Euc N) (r : ℝ) : IsCompact (cball N z r) := by
  rw [cball_eq]
  exact isCompact_closedBall z (r / 2)

/-- **The restriction `H_N(ℝ^N, ℝ^N∖B) → H_N(ℝ^N, ℝ^N∖{y})` out of a coordinate ball is an
isomorphism.** -/
theorem isIso_res_cball (N : ℕ) (hN : 1 ≤ N) (z : Euc N) (r : ℝ) (hr : 0 < r)
    (y : Euc N) (hy : y ∈ cball N z r) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap (TopCat.of (Euc N))
      (cball N z r)ᶜ ({y} : Set (Euc N))ᶜ
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy))) N) :=
  Work.Tubular.convexLocalIso_free N hN (TopCat.of (Euc N)) z r hr
    (by rw [chartAt_self_eq]; exact fun x hx => trivial) y hy

/-- The localisation out of a coordinate ball at a point of the ball is injective. -/
theorem injective_res_cball (N : ℕ) (hN : 1 ≤ N) (z : Euc N) (r : ℝ) (hr : 0 < r)
    (y : Euc N) (hy : y ∈ cball N z r) :
    Function.Injective (Work.Orient.resRelH (TopCat.of (Euc N)) N
      (Set.singleton_subset_iff.mpr hy)) := by
  haveI := isIso_res_cball N hN z r hr y hy
  exact (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap (TopCat.of (Euc N))
      (cball N z r)ᶜ ({y} : Set (Euc N))ᶜ
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy))) N)).1

/-! ## Translation invariance of the Euclidean family -/

/-- The translation `x ↦ x + c` of `ℝ^N`, as a continuous map of `TopCat`. -/
def eucSub (c : Euc N) : TopCat.of (Euc N) ⟶ TopCat.of (Euc N) :=
  TopCat.ofHom ⟨fun x => x + c, continuous_id.add continuous_const⟩

@[simp] theorem eucSub_apply (c x : Euc N) : eucSub c x = x + c := rfl

/-- The translation by `c` carries the complement of `{v}` into the complement of `{v + c}`. -/
theorem eucSub_mem (c v x : Euc N) (hx : x ∉ ({v} : Set (Euc N))) :
    eucSub c x ∉ ({v + c} : Set (Euc N)) := by
  simp only [Set.mem_singleton_iff] at hx ⊢
  intro h
  exact hx (add_right_cancel h)

/-- The translation by `c` carries the complement of a coordinate ball into the complement of its
image. -/
theorem eucSub_mem_ball (c z : Euc N) (r : ℝ) {x : Euc N}
    (hx : x ∉ Metric.closedBall z (r / 2)) : x + c ∉ Metric.closedBall (z + c) (r / 2) := by
  intro h
  refine hx ?_
  rw [Metric.mem_closedBall, dist_eq_norm] at h ⊢
  have h' : ‖x + c - (z + c)‖ = ‖x - z‖ := by congr 1; abel
  rwa [h'] at h

/-- The translation by `c` carries the complement of a coordinate ball into the complement of its
image. -/
theorem eucSub_mem_cball (c z : Euc N) (r : ℝ) {x : Euc N} (hx : x ∉ cball N z r) :
    eucSub c x ∉ cball N (z + c) r := by
  show x + c ∉ cball N (z + c) r
  rw [cball_eq] at hx ⊢
  exact eucSub_mem_ball c z r hx

/-- An explicit isomorphism of the local homology of `ℝ^N` at a point with `ℤ`. -/
noncomputable def locIso (N : ℕ) (hN : 1 ≤ N) (y : Euc N) :
    Work.Orient.LocH (TopCat.of (Euc N)) N y ≃ₗ[ℤ] ℤ :=
  (Classical.choice (Work.Cohomology.localHomology N hN (Euc N) y)).toLinearEquiv

/-! ## Translation invariance of the Euclidean family

The translation by `c` is homotopic, *as a map of the pair `(ℝ^N, ℝ^N∖B) → (ℝ^N, ℝ^N∖B')`* for
suitable nested balls `B ⊆ B'`, to the identity: this is the straight-line homotopy
`H_t(x) = x + t·c`, which stays outside `B'` on the complement of `B` by the choice of `B`.  Hence
the translation acts on the relative classes exactly as the identity does, and localising gives the
statement at the level of the local generators. -/

/-- **Translation invariance of the Euclidean family.** -/
theorem eucFam_translation (N : ℕ) (hN : 1 ≤ N) (c v : Euc N) :
    RelHmapOf N (eucSub c) {v} {v + c} (eucSub_mem c v) (eucFam N hN v)
      = eucFam N hN (v + c) := by
  classical
  set Rb : ℝ := ‖c‖ + ‖v‖ + 1 with hRb
  have hRbpos : 0 < Rb := by rw [hRb]; positivity
  have hcR : ‖c‖ ≤ Rb := by rw [hRb]; have := norm_nonneg v; linarith
  have hvR : ‖v‖ ≤ Rb := by rw [hRb]; have := norm_nonneg c; linarith
  -- the balls
  set B : Set (Euc N) := cball N 0 (8 * Rb) with hB
  set B' : Set (Euc N) := cball N 0 (4 * Rb) with hB'
  have hBclose : B = Metric.closedBall (0 : Euc N) (4 * Rb) := by
    rw [hB, cball_eq, show 8 * Rb / 2 = 4 * Rb by ring]
  have hB'close : B' = Metric.closedBall (0 : Euc N) (2 * Rb) := by
    rw [hB', cball_eq, show 4 * Rb / 2 = 2 * Rb by ring]
  have hvB : v ∈ B := by
    rw [hBclose, Metric.mem_closedBall, dist_zero_right]; linarith
  have hvcB' : v + c ∈ B' := by
    rw [hB'close, Metric.mem_closedBall, dist_zero_right]
    calc ‖v + c‖ ≤ ‖v‖ + ‖c‖ := norm_add_le _ _
      _ ≤ Rb + Rb := add_le_add hvR hcR
      _ = 2 * Rb := by ring
  -- the pair condition for `eucSub c` on the complement of `B`
  have hmem : ∀ x, x ∉ B → eucSub c x ∉ B' := by
    intro x hx
    rw [hBclose] at hx
    rw [hB'close]
    simp only [Metric.mem_closedBall, dist_zero_right, eucSub_apply] at hx ⊢
    intro h
    refine hx ?_
    calc ‖x‖ = ‖(x + c) - c‖ := by rw [show (x + c) - c = x from by abel]
      _ ≤ ‖x + c‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ 2 * Rb + Rb := add_le_add h hcR
      _ ≤ 4 * Rb := by linarith
  -- the pair conditions
  have hmem0 : ∀ x, x ∉ B → eucSub 0 x ∉ B' := by
    intro x hx
    rw [hBclose] at hx
    rw [hB'close]
    simp only [Metric.mem_closedBall, dist_zero_right, eucSub_apply] at hx ⊢
    intro h
    refine hx ?_
    calc ‖x‖ = ‖x + 0‖ := by simp
      _ ≤ 2 * Rb := h
      _ ≤ 4 * Rb := by linarith
  -- the homotopy `H_t(x) = x + t·c`
  have hc1 : Continuous fun p : ↥unitInterval × Euc N => ((p.1 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hc2 : Continuous fun p : ↥unitInterval × Euc N => (p.2 : Euc N) := continuous_snd
  have hcont : Continuous fun p : ↥unitInterval × Euc N =>
      (p.2 : Euc N) + ((p.1 : unitInterval) : ℝ) • c :=
    hc2.add (hc1.smul continuous_const)
  let H : TopCat.Homotopy (eucSub 0) (eucSub c) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p => (p.2 : Euc N) + ((p.1 : unitInterval) : ℝ) • c, hcont⟩
      (fun x => by
        show (x : Euc N) + ((0 : unitInterval) : ℝ) • c = x + 0
        simp)
      (fun x => by
        show (x : Euc N) + ((1 : unitInterval) : ℝ) • c = x + c
        simp)
  have hH : ∀ (t : ↥unitInterval) (x : Euc N), x ∉ B → H (t, x) ∉ B' := by
    intro t x hx
    rw [hBclose] at hx
    rw [hB'close]
    simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    show ¬ ‖(x : Euc N) + (t : ℝ) • c‖ ≤ 2 * Rb
    intro h
    refine hx ?_
    have ht : ‖((t : ℝ)) • c‖ ≤ ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast t.2.1)]
      calc (t : ℝ) * ‖c‖ ≤ 1 * ‖c‖ := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast t.2.2) (norm_nonneg c)
        _ = ‖c‖ := one_mul _
    calc ‖x‖ = ‖((x : Euc N) + (t : ℝ) • c) - (t : ℝ) • c‖ := by
          rw [show ((x : Euc N) + (t : ℝ) • c) - (t : ℝ) • c = x from by abel]
      _ ≤ ‖x + (t : ℝ) • c‖ + ‖(t : ℝ) • c‖ := norm_sub_le _ _
      _ ≤ 2 * Rb + Rb := add_le_add h (le_trans ht hcR)
      _ ≤ 4 * Rb := by linarith
  -- the homotopy invariance
  have hhom : RelHmapOf N (eucSub 0) B B' hmem0 = RelHmapOf N (eucSub c) B B' hmem :=
    RelHmapOf_homotopic hmem0 hmem H hH
  -- `eucSub 0` is the identity
  have hmap0 : eucSub 0 = 𝟙 (TopCat.of (Euc N)) := by
    ext x i
    simp [eucSub, eucSub_apply]
  have hB'sub : B' ⊆ B := by
    rw [hBclose, hB'close]
    exact Metric.closedBall_subset_closedBall (by linarith)
  have hmem1 : ∀ x, x ∉ B → (𝟙 (TopCat.of (Euc N))) x ∉ B' := by
    intro x hx h
    exact hx (hB'sub h)
  have hzero : RelHmapOf N (eucSub 0) B B' hmem0
      = RelHmapOf N (𝟙 (TopCat.of (Euc N))) B B' hmem1 :=
    RelHmapOf_congr hmap0 hmem0 hmem1
  -- the identity induces the trivial comparison of the canonical classes
  have hid : RelHmapOf N (𝟙 (TopCat.of (Euc N))) B B' hmem1
      (eucCanon N hN B (isCompact_cball N 0 (8 * Rb))) = eucCanon N hN B' (isCompact_cball N 0 (4 * Rb)) := by
    set f : TopCat.of (Euc N) ⟶ TopCat.of (Euc N) := 𝟙 (TopCat.of (Euc N)) with hf
    have h0B : (0 : Euc N) ∈ B := mem_cball_center N 0 (8 * Rb) (by linarith)
    have h0B' : (0 : Euc N) ∈ B' := mem_cball_center N 0 (4 * Rb) (by linarith)
    have hinj := injective_res_cball N hN 0 (4 * Rb) (by linarith) 0 h0B'
    apply hinj
    have hnat : (Work.Orient.resRelH (TopCat.of (Euc N)) N (Set.singleton_subset_iff.mpr h0B'))
          (RelHmapOf N f B B' hmem1 (eucCanon N hN B (isCompact_cball N 0 (8 * Rb))))
        = RelHmapOf N f {0} {0} (fun x hx => hx)
          ((Work.Orient.resRelH (TopCat.of (Euc N)) N (Set.singleton_subset_iff.mpr h0B))
            (eucCanon N hN B (isCompact_cball N 0 (8 * Rb)))) := by
      have h := LinearMap.congr_fun (RelHmapOf_resRelH (X := TopCat.of (Euc N))
        (Y := TopCat.of (Euc N)) (n := N) f (K₁ := ({0} : Set (Euc N))) (K₂ := B)
        (K'₁ := ({0} : Set (Euc N))) (K'₂ := B')
        (Set.singleton_subset_iff.mpr h0B) (Set.singleton_subset_iff.mpr h0B')
        hmem1 (fun x hx => hx))
        (eucCanon N hN B (isCompact_cball N 0 (8 * Rb)))
      simpa only [LinearMap.comp_apply] using h.symm
    rw [hnat]
    rw [eucCanon_spec N hN B (isCompact_cball N 0 (8 * Rb)) 0 h0B]
    rw [RelHmapOf_id]
    rw [eucCanon_spec N hN B' (isCompact_cball N 0 (4 * Rb)) 0 h0B']
    rfl
  -- the class-level statement
  have hclass : RelHmapOf N (eucSub c) B B' hmem (eucCanon N hN B (isCompact_cball N 0 (8 * Rb)))
      = eucCanon N hN B' (isCompact_cball N 0 (4 * Rb)) := by
    rw [← hhom, hzero, hid]
  -- localise at `v + c`
  have hinj := injective_res_cball N hN 0 (4 * Rb) (by linarith) (v + c) hvcB'
  have hnat : (Work.Orient.resRelH (TopCat.of (Euc N)) N (Set.singleton_subset_iff.mpr hvcB'))
        (RelHmapOf N (eucSub c) B B' hmem (eucCanon N hN B (isCompact_cball N 0 (8 * Rb))))
      = RelHmapOf N (eucSub c) {v} {v + c} (eucSub_mem c v)
        ((Work.Orient.resRelH (TopCat.of (Euc N)) N (Set.singleton_subset_iff.mpr hvB))
          (eucCanon N hN B (isCompact_cball N 0 (8 * Rb)))) := by
    have h := LinearMap.congr_fun (RelHmapOf_resRelH (X := TopCat.of (Euc N))
      (Y := TopCat.of (Euc N)) (n := N) (eucSub c) (K₁ := ({v} : Set (Euc N))) (K₂ := B)
      (K'₁ := ({v + c} : Set (Euc N))) (K'₂ := B')
      (Set.singleton_subset_iff.mpr hvB) (Set.singleton_subset_iff.mpr hvcB')
      hmem (eucSub_mem c v)) (eucCanon N hN B (isCompact_cball N 0 (8 * Rb)))
    simpa only [LinearMap.comp_apply] using h.symm
  rw [← eucCanon_spec N hN B (isCompact_cball N 0 (8 * Rb)) v hvB]
  rw [← hnat, hclass]
  rw [eucCanon_spec N hN B' (isCompact_cball N 0 (4 * Rb)) (v + c) hvcB']

end

end Work.PTGeometric.HOF
