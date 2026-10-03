/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The diagonal embedding `N(H) → N(G)`

For a countable group `G` and a subgroup `H ≤ G`, a choice `C : CosetData G H` of right-coset
representatives splits `ℓ²(G)` as the Hilbert sum of the closed subspaces `C.e q (ℓ²(H))`,
`q : C.Q` (`Work.ORVonNeumann.Rep.e_inner_eq_zero` for the orthogonality,
`Work.ORVonNeumann.Rep.dense_range_e` for totality).  Under this decomposition the group von
Neumann algebra `N(H)` embeds *diagonally* into `N(G)`: an operator `b ∈ N(H)` acts as `b` on
each of the coset copies of `ℓ²(H)`.

This module constructs that embedding explicitly and proves the properties required of it:
it is a `ℂ`-algebra homomorphism (`diagOp_apply_e`, `cosetDiagOp_mul`, `diagOp_one`, ...), it is
`*`-preserving (`diagOp_star`), injective (`diagOp_injective`), it sends the left regular
representation of `H` to that of `G` (`diagOp_leftRegOp`) and it is "block diagonal"
(`diagOp_apply_e`).

## Main result

* `Work.ORVonNeumann.Rep.exists_diagHom` — there is `C : CosetData G H` and an injective
  `*`-preserving `ℂ`-algebra homomorphism `N(H) → N(G)` which is the identity on the left
  regular representations and block diagonal with respect to `C`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.CosetData
import Submission.Work.ORVonNeumann.Rep.exists_leftRegular
import Submission.Work.ORVonNeumann.Rep.exists_rightRegular
import Submission.Work.ORVonNeumann.Rep.HilbertBasis
import Submission.Work.ORVonNeumann.Rep.DenseSpan
import Submission.Work.ORVonNeumann.Rep.Orthonormal
import Submission.Work.ORVonNeumann.Rep.Trace
import Submission.Work.ORVonNeumann.Rep.e_inner_eq_zero
import Submission.Work.ORVonNeumann.Rep.rightRegOp_e_apply
import Submission.Work.ORVonNeumann.Rep.exists_cosetData

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ORVonNeumann.Rep

open MeasureTheory
open scoped ENNReal

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-! ## The left regular representation on the basis vectors -/

/-- The left regular representation acts on the basis vectors by left multiplication. -/
theorem leftRegOp_deltaG (g z : G) : leftRegOp g (deltaG z) = deltaG (g * z) := by
  calc leftRegOp g (deltaG z) = leftRegOp g (leftRegOp z (delta1 G)) := by rw [leftRegOp_delta1]
    _ = leftRegOp (g * z) (delta1 G) := leftRegOp_mul_apply g z (delta1 G)
    _ = deltaG (g * z) := leftRegOp_delta1 (g * z)

variable {H : Subgroup G}

/-! ## The Hilbert sum decomposition of `ℓ²(G)` over the cosets of `H` -/

/-- Every basis vector `δ_g` lies in the range of the coset lift of its own coset. -/
theorem deltaG_mem_range_e (C : CosetData G H) (g : G) :
    deltaG g ∈ LinearMap.range (C.e (C.qpart g)).toLinearMap :=
  ⟨deltaG (C.hpart g), C.E_delta_self g⟩

/-- The closed span of the ranges of the coset lifts is all of `ℓ²(G)`. -/
theorem dense_range_e (C : CosetData G H) :
    ⊤ ≤ (⨆ q : C.Q, LinearMap.range (C.e q).toLinearMap).topologicalClosure := by
  have hle : Submodule.span ℂ (Set.range (deltaG (G := G))) ≤
      ⨆ q : C.Q, LinearMap.range (C.e q).toLinearMap := by
    rw [Submodule.span_le]
    rintro x ⟨g, rfl⟩
    exact Submodule.mem_iSup_of_mem (C.qpart g) (deltaG_mem_range_e C g)
  exact le_trans dense_span_deltaG (Submodule.topologicalClosure_mono hle)

/-- The coset lifts form an orthogonal family. -/
theorem orthogonalFamily_e (C : CosetData G H) :
    OrthogonalFamily ℂ (fun _ : C.Q => l2 ↥H) C.e :=
  fun q q' hqq' y y' => e_inner_eq_zero C hqq' y y'

/-- `ℓ²(G)` is the Hilbert sum of the copies `C.e q (ℓ²(H))` of `ℓ²(H)` over the cosets. -/
theorem hilbSum (C : CosetData G H) :
    IsHilbertSum ℂ (fun _ : C.Q => l2 ↥H) C.e :=
  IsHilbertSum.mk (orthogonalFamily_e C) (dense_range_e C)

/-- The isometric identification `ℓ²(G) ≃ ℓ²(Q, ℓ²(H))` of the coset decomposition. -/
noncomputable def hilbEquiv (C : CosetData G H) :
    l2 G ≃ₗᵢ[ℂ] ↥(lp (fun _ : C.Q => l2 ↥H) 2) :=
  (hilbSum C).linearIsometryEquiv

/-! ## Extensionality -/

/-- **Extensionality on the coset blocks**: two bounded operators on `ℓ²(G)` that agree on
every coset block `C.e q y` are equal. -/
theorem ext_of_eq_on_blocks (C : CosetData G H) {S T : boundedEnd G}
    (h : ∀ (q : C.Q) (y : l2 ↥H), S (C.e q y) = T (C.e q y)) : S = T := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hclosed : IsClosed (((S.toLinearMap.eqLocus T.toLinearMap : Submodule ℂ (l2 G))) :
      Set (l2 G)) :=
    isClosed_eq S.continuous T.continuous
  have hle : (⨆ q : C.Q, LinearMap.range (C.e q).toLinearMap) ≤
      S.toLinearMap.eqLocus T.toLinearMap := by
    refine iSup_le fun q => ?_
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_eqLocus]
    exact h q y
  have htop : (S.toLinearMap.eqLocus T.toLinearMap).topologicalClosure = ⊤ :=
    top_unique (le_trans (dense_range_e C) (Submodule.topologicalClosure_mono hle))
  have hall : (⊤ : Submodule ℂ (l2 G)) ≤ S.toLinearMap.eqLocus T.toLinearMap := by
    rw [← htop]
    exact Submodule.topologicalClosure_minimal (s := S.toLinearMap.eqLocus T.toLinearMap) le_rfl
      hclosed
  exact (LinearMap.mem_eqLocus (f := S.toLinearMap) (g := T.toLinearMap)).mp (hall trivial)

/-- A vector of `ℓ²(G)` orthogonal to every coset block vanishes. -/
theorem eq_zero_of_inner_blocks_eq_zero (C : CosetData G H) (x₀ : l2 G)
    (h : ∀ (q : C.Q) (y : l2 ↥H), inner ℂ x₀ (C.e q y) = 0) : x₀ = 0 := by
  let Z : Submodule ℂ (l2 G) :=
    { carrier := {w | inner ℂ x₀ w = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        show inner ℂ x₀ (a + b) = 0
        rw [inner_add_right, ha, hb, add_zero]
      smul_mem' := by
        intro c a ha
        show inner ℂ x₀ (c • a) = 0
        rw [inner_smul_right, ha, mul_zero] }
  have hclosed : IsClosed (Z : Set (l2 G)) := by
    show IsClosed {w : l2 G | inner ℂ x₀ w = 0}
    exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hle : (⨆ q : C.Q, LinearMap.range (C.e q).toLinearMap) ≤ Z := by
    refine iSup_le fun q => ?_
    rintro w ⟨y, rfl⟩
    exact h q y
  have htop : Z.topologicalClosure = ⊤ :=
    top_unique (le_trans (dense_range_e C) (Submodule.topologicalClosure_mono hle))
  have hall : (⊤ : Submodule ℂ (l2 G)) ≤ Z := by
    rw [← htop]
    exact Submodule.topologicalClosure_minimal (s := Z) le_rfl hclosed
  exact inner_self_eq_zero.mp (show inner ℂ x₀ x₀ = 0 from hall trivial)

/-- **A bounded operator on `ℓ²(G)` whose inner products against the coset blocks all vanish
is zero.** -/
theorem ext_of_inner_blocks (C : CosetData G H) {R : boundedEnd G}
    (h : ∀ (q : C.Q) (y : l2 ↥H) (q' : C.Q) (y' : l2 ↥H),
      inner ℂ (R (C.e q y)) (C.e q' y') = 0) : R = 0 := by
  have hblock : ∀ (q : C.Q) (y : l2 ↥H), R (C.e q y) = 0 := fun q y =>
    eq_zero_of_inner_blocks_eq_zero C (R (C.e q y)) (fun q' y' => h q y q' y')
  have hclosed : IsClosed (((R.toLinearMap.ker : Submodule ℂ (l2 G))) : Set (l2 G)) :=
    R.isClosed_ker
  have hspan : (⨆ q : C.Q, LinearMap.range (C.e q).toLinearMap) ≤ R.toLinearMap.ker := by
    refine iSup_le fun q => ?_
    rintro x ⟨y, rfl⟩
    exact (LinearMap.mem_ker).mpr (hblock q y)
  have htop : R.toLinearMap.ker.topologicalClosure = ⊤ :=
    top_unique (le_trans (dense_range_e C) (Submodule.topologicalClosure_mono hspan))
  have hall : (⊤ : Submodule ℂ (l2 G)) ≤ R.toLinearMap.ker := by
    rw [← htop]
    exact Submodule.topologicalClosure_minimal (s := R.toLinearMap.ker) le_rfl hclosed
  exact ContinuousLinearMap.ext fun x => (LinearMap.mem_ker).mp (hall trivial)

/-! ## The block operator `⊕_q b` on the Hilbert sum `ℓ²(Q, ℓ²(H))` -/

/-- The norm identity `‖g‖ ^ 2 = ∑' i, ‖g i‖ ^ 2` for an element of an `ℓ²`-direct sum. -/
private theorem lp_norm_sq {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (g : ↥(lp E 2)) : ‖g‖ ^ 2 = ∑' i, ‖(g : (i : ι) → E i) i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) g
  simpa using h

/-- Summability of the norms squared of the coordinatewise image of an `ℓ²`-sum. -/
private theorem summable_blockOp {ι : Type*} {K : Type*} [Group K] [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K] [MeasurableMul K] (b : boundedEnd K)
    (f : ↥(lp (fun _ : ι => l2 K) 2)) : Summable fun i => ‖b (f i)‖ ^ 2 := by
  have hf : Summable fun i => ‖f i‖ ^ 2 := by
    simpa using (lp.memℓp f).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hf.mul_left (‖b‖ ^ 2))
  have hle := b.le_opNorm (f i)
  rw [← mul_pow]
  nlinarith [norm_nonneg (b (f i)), norm_nonneg (f i), norm_nonneg b, hle]

private theorem exists_lp_blockOp_aux {ι : Type*} {K : Type*} [Group K] [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K] [MeasurableMul K] (b : boundedEnd K) :
    ∃ L : ↥(lp (fun _ : ι => l2 K) 2) →L[ℂ] ↥(lp (fun _ : ι => l2 K) 2),
      ∀ (f : ↥(lp (fun _ : ι => l2 K) 2)) (i : ι),
        ((L f) : (j : ι) → l2 K) i = b (((f : (j : ι) → l2 K)) i) := by
  have hmem : ∀ f : ↥(lp (fun _ : ι => l2 K) 2), Memℓp (fun i => b (f i)) 2 := fun f =>
    memℓp_gen (by simpa using summable_blockOp b f)
  let F : ↥(lp (fun _ : ι => l2 K) 2) →ₗ[ℂ] ↥(lp (fun _ : ι => l2 K) 2) :=
    { toFun := fun f => ⟨fun i => b (f i), hmem f⟩
      map_add' := fun f g => Subtype.ext (funext fun i =>
        show b ((f + g) i) = b (f i) + b (g i) from
          (congrArg b (show (f + g) i = f i + g i from rfl)).trans (map_add b (f i) (g i)))
      map_smul' := fun c f => Subtype.ext (funext fun i =>
        show b ((c • f) i) = c • b (f i) from
          (congrArg b (show (c • f) i = c • f i from rfl)).trans (map_smul b c (f i))) }
  have hcoord : ∀ (f : ↥(lp (fun _ : ι => l2 K) 2)) (i : ι),
      (F f : (j : ι) → l2 K) i = b (f i) := fun f i => rfl
  have hnorm : ∀ f : ↥(lp (fun _ : ι => l2 K) 2), ‖F f‖ ≤ ‖b‖ * ‖f‖ := by
    intro f
    have h1 : (∑' i, ‖b (f i)‖ ^ 2) = ‖F f‖ ^ 2 := by
      rw [lp_norm_sq (g := F f)]
      refine tsum_congr fun i => ?_
      rw [hcoord f i]
    have h2 : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := lp_norm_sq f
    have hf : Summable fun i => ‖f i‖ ^ 2 := by
      simpa using (lp.memℓp f).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    have hle : ∀ i, ‖b (f i)‖ ^ 2 ≤ ‖b‖ ^ 2 * ‖f i‖ ^ 2 := by
      intro i
      have h := b.le_opNorm (f i)
      rw [← mul_pow]
      nlinarith [norm_nonneg (b (f i)), norm_nonneg (f i), norm_nonneg b, h]
    have hsum : (∑' i, ‖b (f i)‖ ^ 2) ≤ ∑' i, ‖b‖ ^ 2 * ‖f i‖ ^ 2 :=
      Summable.tsum_le_tsum hle (summable_blockOp b f) (hf.mul_left _)
    have hsquare : ‖F f‖ ^ 2 ≤ (‖b‖ * ‖f‖) ^ 2 := by
      rw [← h1, mul_pow, h2]
      exact hsum.trans_eq tsum_mul_left
    have h := sq_le_sq.mp hsquare
    rwa [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at h
  refine ⟨F.mkContinuous ‖b‖ (fun f => hnorm f), fun f i => ?_⟩
  show (F f : (j : ι) → l2 K) i = b (f i)
  exact hcoord f i

/-- The coordinatewise ("block diagonal with all blocks `b`") operator on the Hilbert sum
`ℓ²(Q, ℓ²(H))`. -/
noncomputable def lpBlockOp (C : CosetData G H) (b : boundedEnd ↥H) :
    ↥(lp (fun _ : C.Q => l2 ↥H) 2) →L[ℂ] ↥(lp (fun _ : C.Q => l2 ↥H) 2) :=
  Classical.choose (exists_lp_blockOp_aux (ι := C.Q) (K := ↥H) b)

theorem lpBlockOp_apply (C : CosetData G H) (b : boundedEnd ↥H)
    (f : ↥(lp (fun _ : C.Q => l2 ↥H) 2)) (q : C.Q) :
    ((lpBlockOp C b f) : (j : C.Q) → l2 ↥H) q = b (((f : (j : C.Q) → l2 ↥H)) q) :=
  (Classical.choose_spec (exists_lp_blockOp_aux (ι := C.Q) (K := ↥H) b)) f q

theorem lpBlockOp_single (C : CosetData G H) [DecidableEq C.Q] (b : boundedEnd ↥H) (q : C.Q)
    (y : l2 ↥H) : lpBlockOp C b (lp.single 2 q y) = lp.single 2 q (b y) := by
  refine lp.ext (funext fun q' => ?_)
  rw [lpBlockOp_apply, lp.single_apply, lp.single_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : q' = q
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg h, map_zero]

/-! ## The diagonal operator `cosetDiagOp b` on `ℓ²(G)` -/

/-- The diagonal operator: `b` acts on each coset copy of `ℓ²(H)`. -/
noncomputable def cosetDiagOp (C : CosetData G H) (b : boundedEnd ↥H) : boundedEnd G :=
  ((hilbEquiv C).symm : ↥(lp (fun _ : C.Q => l2 ↥H) 2) →L[ℂ] l2 G).comp
    ((lpBlockOp C b).comp ((hilbEquiv C) : l2 G →L[ℂ] ↥(lp (fun _ : C.Q => l2 ↥H) 2)))

theorem cosetDiagOp_apply (C : CosetData G H) (b : boundedEnd ↥H) (f : l2 G) :
    cosetDiagOp C b f = (hilbEquiv C).symm (lpBlockOp C b ((hilbEquiv C) f)) :=
  rfl

theorem hilbEquiv_e (C : CosetData G H) [DecidableEq C.Q] (q : C.Q) (y : l2 ↥H) :
    (hilbEquiv C) (C.e q y) = lp.single 2 q y := by
  rw [← IsHilbertSum.linearIsometryEquiv_symm_apply_single (hilbSum C) (i := q) (x := y)]
  exact LinearIsometryEquiv.apply_symm_apply _ _

/-- **The defining property of the diagonal operator**: it acts as `b` on every coset block. -/
theorem diagOp_apply_e (C : CosetData G H) [DecidableEq C.Q] (b : boundedEnd ↥H) (q : C.Q)
    (y : l2 ↥H) : cosetDiagOp C b (C.e q y) = C.e q (b y) := by
  rw [cosetDiagOp_apply, hilbEquiv_e C q y, lpBlockOp_single]
  exact IsHilbertSum.linearIsometryEquiv_symm_apply_single (hilbSum C) (i := q) (x := b y)

/-! ## Algebraic properties of `cosetDiagOp` -/

theorem diagOp_add (C : CosetData G H) [DecidableEq C.Q] (b c : boundedEnd ↥H) :
    cosetDiagOp C (b + c) = cosetDiagOp C b + cosetDiagOp C c := by
  refine ext_of_eq_on_blocks C fun q y => ?_
  have h1 : cosetDiagOp C (b + c) (C.e q y) = C.e q (b y + c y) := by
    rw [diagOp_apply_e C (b + c) q y, add_apply]
  have h2 : (cosetDiagOp C b + cosetDiagOp C c) (C.e q y) = C.e q (b y) + C.e q (c y) := by
    rw [add_apply, diagOp_apply_e C b q y, diagOp_apply_e C c q y]
  rw [h1, h2, map_add]

theorem cosetDiagOp_mul (C : CosetData G H) [DecidableEq C.Q] (b c : boundedEnd ↥H) :
    cosetDiagOp C (b * c) = cosetDiagOp C b * cosetDiagOp C c := by
  refine ext_of_eq_on_blocks C fun q y => ?_
  have h1 : cosetDiagOp C (b * c) (C.e q y) = C.e q (b (c y)) := by
    rw [diagOp_apply_e C (b * c) q y, mul_apply_eq_comp]
  have h2 : (cosetDiagOp C b * cosetDiagOp C c) (C.e q y) = C.e q (b (c y)) := by
    rw [mul_apply_eq_comp, diagOp_apply_e C c q y, diagOp_apply_e C b q (c y)]
  rw [h1, h2]

theorem diagOp_one (C : CosetData G H) [DecidableEq C.Q] : cosetDiagOp C 1 = 1 := by
  refine ext_of_eq_on_blocks C fun q y => ?_
  have h1 : cosetDiagOp C 1 (C.e q y) = C.e q y := by
    rw [diagOp_apply_e C 1 q y, one_apply_eq_self]
  have h2 : (1 : boundedEnd G) (C.e q y) = C.e q y := one_apply_eq_self _
  rw [h1, h2]

theorem diagOp_zero (C : CosetData G H) [DecidableEq C.Q] : cosetDiagOp C 0 = 0 := by
  refine ext_of_eq_on_blocks C fun q y => ?_
  have h1 : cosetDiagOp C 0 (C.e q y) = 0 := by
    rw [diagOp_apply_e C 0 q y, zero_apply, map_zero]
  have h2 : (0 : boundedEnd G) (C.e q y) = 0 := zero_apply _
  rw [h1, h2]

theorem diagOp_smul (C : CosetData G H) [DecidableEq C.Q] (r : ℂ) (b : boundedEnd ↥H) :
    cosetDiagOp C (r • b) = r • cosetDiagOp C b := by
  refine ext_of_eq_on_blocks C fun q y => ?_
  have h1 : cosetDiagOp C (r • b) (C.e q y) = C.e q (r • b y) := by
    rw [diagOp_apply_e C (r • b) q y, smul_apply]
  have h2 : (r • cosetDiagOp C b) (C.e q y) = r • C.e q (b y) := by
    rw [smul_apply, diagOp_apply_e C b q y]
  rw [h1, h2, map_smul]

theorem diagOp_sub (C : CosetData G H) [DecidableEq C.Q] (b c : boundedEnd ↥H) :
    cosetDiagOp C (b - c) = cosetDiagOp C b - cosetDiagOp C c := by
  refine ext_of_eq_on_blocks C fun q y => ?_
  have h1 : cosetDiagOp C (b - c) (C.e q y) = C.e q (b y - c y) := by
    rw [diagOp_apply_e C (b - c) q y, sub_apply]
  have h2 : (cosetDiagOp C b - cosetDiagOp C c) (C.e q y) = C.e q (b y) - C.e q (c y) := by
    rw [sub_apply, diagOp_apply_e C b q y, diagOp_apply_e C c q y]
  rw [h1, h2, map_sub]

theorem diagOp_algebraMap (C : CosetData G H) [DecidableEq C.Q] (r : ℂ) :
    cosetDiagOp C (algebraMap ℂ (boundedEnd ↥H) r) = algebraMap ℂ (boundedEnd G) r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, diagOp_smul, diagOp_one]

/-! ## `cosetDiagOp` is `*`-preserving -/

theorem inner_diagOp_apply_e_self (C : CosetData G H) [DecidableEq C.Q] (b : boundedEnd ↥H)
    (q : C.Q) (y y' : l2 ↥H) :
    inner ℂ (cosetDiagOp C b (C.e q y)) (C.e q y') = inner ℂ (b y) y' := by
  rw [diagOp_apply_e, LinearIsometry.inner_map_map]

theorem inner_diagOp_apply_e_ne (C : CosetData G H) [DecidableEq C.Q] (b : boundedEnd ↥H)
    {q q' : C.Q} (hqq' : q ≠ q') (y y' : l2 ↥H) :
    inner ℂ (cosetDiagOp C b (C.e q y)) (C.e q' y') = 0 := by
  rw [diagOp_apply_e, e_inner_eq_zero C hqq' (b y) y']

/-- **`cosetDiagOp` is `*`-preserving** (the involution on `B(ℓ²)` is the adjoint). -/
theorem diagOp_star (C : CosetData G H) [DecidableEq C.Q] (b : boundedEnd ↥H) :
    cosetDiagOp C (star b) = star (cosetDiagOp C b) := by
  have hzero : cosetDiagOp C (star b) - star (cosetDiagOp C b) = 0 := by
    refine ext_of_inner_blocks C fun q y q' y' => ?_
    by_cases hqq : q = q'
    · subst hqq
      rw [sub_apply, inner_sub_left]
      rw [inner_diagOp_apply_e_self]
      rw [ContinuousLinearMap.star_eq_adjoint]
      rw [ContinuousLinearMap.adjoint_inner_left]
      rw [ContinuousLinearMap.star_eq_adjoint]
      rw [ContinuousLinearMap.adjoint_inner_left]
      rw [diagOp_apply_e, LinearIsometry.inner_map_map]
      exact sub_self _
    · rw [sub_apply, inner_sub_left]
      rw [inner_diagOp_apply_e_ne C (star b) hqq y y']
      rw [ContinuousLinearMap.star_eq_adjoint]
      rw [ContinuousLinearMap.adjoint_inner_left]
      rw [diagOp_apply_e, e_inner_eq_zero C hqq y (b y')]
      exact sub_zero 0
  exact sub_eq_zero.mp hzero

/-! ## `cosetDiagOp b` lies in `N(G)` for `b ∈ N(H)` -/

/-- **The diagonal operator of an element of `N(H)` lies in `N(G)`**, i.e. it commutes with
the right regular representation of `G`. -/
theorem diagOp_mem_groupVonNeumann (C : CosetData G H) [DecidableEq C.Q] {b : boundedEnd ↥H}
    (hb : b ∈ groupVonNeumann ↥H) : cosetDiagOp C b ∈ groupVonNeumann G := by
  rw [mem_groupVonNeumann_iff]
  intro k
  change cosetDiagOp C b * rightRegOp k = rightRegOp k * cosetDiagOp C b
  have hb' : ∀ x : ↥H, ∀ y : l2 ↥H, b (rightRegOp x y) = rightRegOp x (b y) := by
    intro x y
    have h := congrArg (fun S : boundedEnd ↥H => S y) ((mem_groupVonNeumann_iff b).mp hb x)
    rwa [mul_apply_eq_comp, mul_apply_eq_comp] at h
  refine ext_of_eq_on_blocks C fun q y => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, rightRegOp_e_apply C q k y, CosetData.E,
    diagOp_apply_e, diagOp_apply_e, rightRegOp_e_apply C q k (b y), CosetData.E, hb']

/-- **`cosetDiagOp` is injective.** -/
theorem diagOp_eq_zero (C : CosetData G H) [DecidableEq C.Q] {b : boundedEnd ↥H}
    (h : cosetDiagOp C b = 0) : b = 0 := by
  refine ContinuousLinearMap.ext fun y => ?_
  have h1 : C.e (C.qpart (1 : G)) (b y) = 0 := by
    have h2 := diagOp_apply_e C b (C.qpart (1 : G)) y
    rw [h, zero_apply] at h2
    exact h2.symm
  have h3 : C.e (C.qpart (1 : G)) (b y) = C.e (C.qpart (1 : G)) 0 := by rw [h1, map_zero]
  simpa using (C.e (C.qpart (1 : G))).injective h3

theorem diagOp_injective (C : CosetData G H) [DecidableEq C.Q] :
    Function.Injective (cosetDiagOp C) := by
  intro b c hbc
  have h0 : cosetDiagOp C (b - c) = 0 := by rw [diagOp_sub, hbc, sub_self]
  exact sub_eq_zero.mp (diagOp_eq_zero C h0)

/-! ## Agreement with the left regular representation of `H` -/

/-- **`cosetDiagOp` sends the left regular representation of `H` to that of `G`.** -/
theorem diagOp_leftRegOp (C : CosetData G H) [DecidableEq C.Q] (h : ↥H) :
    cosetDiagOp C (leftRegOp h) = leftRegOp (h : G) := by
  refine ext_of_eq_on_blocks C fun q y => ?_
  rw [diagOp_apply_e]
  have hDense : Dense (Submodule.span ℂ (Set.range (deltaG (G := ↥H))) : Set (l2 ↥H)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact le_antisymm le_top (dense_span_deltaG (G := ↥H))
  have hcomp : ((leftRegOp (h : G)).comp (C.e q).toContinuousLinearMap) =
      ((C.e q).toContinuousLinearMap.comp (leftRegOp h)) := by
    apply ContinuousLinearMap.ext_on hDense
    rintro x ⟨h', rfl⟩
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [C.e_delta, leftRegOp_deltaG, leftRegOp_deltaG, C.e_delta]
    congr 1
    rw [← mul_assoc, Subgroup.coe_mul]
  exact (congrArg (fun S => S y) hcomp).symm

/-! ## The diagonal embedding `N(H) → N(G)` -/

theorem exists_diagHom {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (H : Subgroup G) : ∃ C : Work.ORVonNeumann.Rep.CosetData G H, ∃ Φ : ↥(Work.ORVonNeumann.groupVonNeumann ↥H) →ₐ[ℂ] ↥(Work.ORVonNeumann.groupVonNeumann G), (∀ (h : ↥H), Φ ⟨Work.ORVonNeumann.Rep.leftRegOp h, Work.ORVonNeumann.Rep.leftRegOp_mem_groupVonNeumann h⟩ = ⟨Work.ORVonNeumann.Rep.leftRegOp (h : G), Work.ORVonNeumann.Rep.leftRegOp_mem_groupVonNeumann (h : G)⟩) ∧ (∀ b : ↥(Work.ORVonNeumann.groupVonNeumann ↥H), Φ (star b) = star (Φ b)) ∧ Function.Injective Φ ∧ (∀ (b : ↥(Work.ORVonNeumann.groupVonNeumann ↥H)) (q : C.Q), ∀ y : Work.ORVonNeumann.l2 ↥H, (Φ b : Work.ORVonNeumann.boundedEnd G) (C.e q y) = C.e q ((b : Work.ORVonNeumann.boundedEnd ↥H) y)) := by
  classical
  obtain ⟨C⟩ := exists_cosetData H
  refine ⟨C, ?_⟩
  let Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G) :=
    { toFun := fun b =>
        ⟨cosetDiagOp C (b : boundedEnd ↥H), diagOp_mem_groupVonNeumann C b.2⟩
      map_one' := by
        refine Subtype.ext ?_
        simpa using diagOp_one C
      map_mul' := fun b c => by
        refine Subtype.ext ?_
        simpa using cosetDiagOp_mul C (b : boundedEnd ↥H) (c : boundedEnd ↥H)
      map_zero' := by
        refine Subtype.ext ?_
        simpa using diagOp_zero C
      map_add' := fun b c => by
        refine Subtype.ext ?_
        simpa using diagOp_add C (b : boundedEnd ↥H) (c : boundedEnd ↥H)
      commutes' := fun r => by
        refine Subtype.ext ?_
        simpa using diagOp_algebraMap C r }
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · intro h
    refine Subtype.ext ?_
    show cosetDiagOp C (leftRegOp h) = leftRegOp (h : G)
    exact diagOp_leftRegOp C h
  · intro b
    refine Subtype.ext ?_
    show cosetDiagOp C (star (b : boundedEnd ↥H)) = star (cosetDiagOp C (b : boundedEnd ↥H))
    exact diagOp_star C (b : boundedEnd ↥H)
  · intro b c hbc
    have hb : (b : boundedEnd ↥H) = (c : boundedEnd ↥H) := by
      refine diagOp_injective C ?_
      show cosetDiagOp C (b : boundedEnd ↥H) = cosetDiagOp C (c : boundedEnd ↥H)
      exact congrArg Subtype.val hbc
    exact Subtype.ext hb
  · intro b q y
    show cosetDiagOp C (b : boundedEnd ↥H) (C.e q y) = C.e q ((b : boundedEnd ↥H) y)
    exact diagOp_apply_e C (b : boundedEnd ↥H) q y

end Work.ORVonNeumann.Rep
