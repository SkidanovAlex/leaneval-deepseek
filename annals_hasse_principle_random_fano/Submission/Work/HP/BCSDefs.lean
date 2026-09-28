import Mathlib
import Submission.Work.HP.Defs

/-!
# Shared definitions for `Work.HP.ball_count_schmidt`

Lattices in Euclidean space, their ball counts, successive minima and rank, and the
orthogonal projection onto the orthogonal complement of a line.  These definitions are used
by `Submission.Work.HP.ball_count_schmidt` and by the auxiliary files
`Submission/Work/HP/BCS/*`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance instIsTorsionFreeEuclid : Module.IsTorsionFree ℤ (EuclideanSpace ℝ ι) := by
  refine ⟨fun n hn x y hxy => ?_⟩
  have hn0 : n ≠ 0 := by
    intro h; subst h; exact hn.ne_zero rfl
  ext i
  have h := congrArg (fun z : EuclideanSpace ℝ ι => z.ofLp i) hxy
  simp only [WithLp.ofLp_smul, Pi.smul_apply, zsmul_eq_mul] at h
  exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hn0) h

/-! ## Counting and successive minima for lattices in `ℝ^ι` -/

/-- Number of points of the lattice `Λ` of norm at most `T`. -/
def sCnt (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) (T : ℝ) : ℕ :=
  {x | x ∈ Λ ∧ ‖x‖ ≤ T}.ncard

/-- The set whose infimum defines the `i`-th successive minimum. -/
def sMinSet (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) (i : ℕ) : Set ℝ :=
  {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → EuclideanSpace ℝ ι,
    (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f ∧ ∀ j, ‖f j‖ ≤ r}

/-- The `i`-th successive minimum of `Λ` for the Euclidean unit ball. -/
def sMin (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) (i : ℕ) : ℝ := sInf (sMinSet Λ i)

/-- The rank of `Λ` over `ℤ`. -/
def sRank (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) : ℕ := Module.finrank ℤ Λ


/-! ## The orthogonal projection onto the orthogonal complement of a line -/

section proj

variable (u : EuclideanSpace ℝ ι)

/-- Orthogonal projection onto `u^⊥`, i.e. `x ↦ x - (‖u‖²)⁻¹ * ⟪x,u⟫ * u`. -/
def projU : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.id - (‖u‖ ^ 2)⁻¹ • LinearMap.smulRight ((innerSL ℝ u).toLinearMap) u

lemma projU_apply (x : EuclideanSpace ℝ ι) :
    projU u x = x - ((‖u‖ ^ 2)⁻¹ * inner ℝ x u) • u := by
  simp [projU, LinearMap.smulRight_apply, smul_smul, real_inner_comm]

lemma inner_projU_left (x : EuclideanSpace ℝ ι) : inner ℝ (projU u x) u = 0 := by
  rw [projU_apply, inner_sub_left]
  have h : inner ℝ (((‖u‖ ^ 2)⁻¹ * inner ℝ x u) • u) u
      = ((‖u‖ ^ 2)⁻¹ * inner ℝ x u) * (‖u‖ ^ 2 : ℝ) := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [h]
  by_cases hu : ‖u‖ = 0
  · rw [norm_eq_zero.mp hu]; simp
  · rw [show (‖u‖ ^ 2)⁻¹ * inner ℝ x u * (‖u‖ ^ 2 : ℝ) = inner ℝ x u by
      rw [mul_comm ((‖u‖ ^ 2)⁻¹) (inner ℝ x u), mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero 2 hu), mul_one]
    , sub_self]

lemma projU_self_eq_zero (hu : u ≠ 0) : projU u u = 0 := by
  rw [projU_apply, real_inner_self_eq_norm_sq]
  rw [show (‖u‖ ^ 2)⁻¹ * ‖u‖ ^ 2 = 1 by
    rw [inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))], one_smul, sub_self]

lemma projU_eq_zero_iff (hu : u ≠ 0) (x : EuclideanSpace ℝ ι) :
    projU u x = 0 ↔ x ∈ Submodule.span ℝ {u} := by
  constructor
  · intro h
    have hx : x = ((‖u‖ ^ 2)⁻¹ * inner ℝ x u) • u := by
      have := congrArg (fun z => z + ((‖u‖ ^ 2)⁻¹ * inner ℝ x u) • u) h
      simpa [projU_apply, sub_eq_zero] using this
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, projU_self_eq_zero u hu, smul_zero]

lemma projU_sub_eq_zero_iff (hu : u ≠ 0) (x y : EuclideanSpace ℝ ι) :
    projU u x = projU u y ↔ x - y ∈ Submodule.span ℝ {u} := by
  rw [← sub_eq_zero, ← map_sub, projU_eq_zero_iff u hu]

lemma projU_add_smul (c : ℝ) (x : EuclideanSpace ℝ ι) :
    projU u (x + c • u) = projU u x := by
  rw [map_add, map_smul]
  have : projU u u = 0 := by
    by_cases hu : u = 0
    · subst hu; simp
    · exact projU_self_eq_zero u hu
  rw [this, smul_zero, add_zero]

/-- Pythagoras: `‖projU u x + c u‖² = ‖projU u x‖² + ‖c u‖²`. -/
lemma norm_sq_add_smul' (c : ℝ) (x : EuclideanSpace ℝ ι) :
    ‖projU u x + c • u‖ ^ 2 = ‖projU u x‖ ^ 2 + (c * ‖u‖) ^ 2 := by
  have horth : inner ℝ (projU u x) (c • u) = 0 := by
    rw [real_inner_smul_right, inner_projU_left, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (projU u x) (c • u) horth
  have h2 : ‖projU u x + c • u‖ ^ 2 = ‖projU u x‖ ^ 2 + ‖c • u‖ ^ 2 := by
    rw [sq, sq, sq, h]
  rw [h2, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow]

lemma norm_projU_le (x : EuclideanSpace ℝ ι) : ‖projU u x‖ ≤ ‖x‖ := by
  have hx : x = projU u x + ((‖u‖ ^ 2)⁻¹ * inner ℝ x u) • u := by
    rw [projU_apply]; abel
  have h := norm_sq_add_smul' u ((‖u‖ ^ 2)⁻¹ * inner ℝ x u) x
  rw [← hx] at h
  have h2 : ‖projU u x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ((‖u‖ ^ 2)⁻¹ * inner ℝ x u * ‖u‖), h]
  simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg (projU u x))]
    using sq_le_sq.mp h2

/-- Pythagoras in the form used for the fibre count:
`‖x + s u‖² = ‖projU u x‖² + (⟪x,u⟫/‖u‖² + s)² ‖u‖²`. -/
lemma norm_sq_add_smul (s : ℝ) (x : EuclideanSpace ℝ ι) :
    ‖x + s • u‖ ^ 2 = ‖projU u x‖ ^ 2 + (inner ℝ x u / ‖u‖ ^ 2 + s) ^ 2 * ‖u‖ ^ 2 := by
  set c := inner ℝ x u / ‖u‖ ^ 2 + s with hc
  have hx : x + s • u = projU u x + c • u := by
    rw [projU_apply, add_smul, div_eq_inv_mul]; abel
  rw [hx, norm_sq_add_smul' u c x, hc]
  ring

/-- `projU u` viewed as a `ℤ`-linear map, so that it can be used on `ℤ`-submodules. -/
def projUZ (u : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι →ₗ[ℤ] EuclideanSpace ℝ ι :=
  (projU u).restrictScalars ℤ

@[simp] lemma projUZ_apply (u x : EuclideanSpace ℝ ι) : projUZ u x = projU u x := rfl

end proj

/-! ## Elementary properties of `sCnt` and `sMin` -/

section basic

variable {Λ : Submodule ℤ (EuclideanSpace ℝ ι)}

lemma sMin_eq_sInf (i : ℕ) : sMin Λ i = sInf (sMinSet Λ i) := rfl

lemma sMin_nonneg (i : ℕ) : 0 ≤ sMin Λ i := by
  by_cases h : (sMinSet Λ i).Nonempty
  · exact le_csInf h fun r hr => hr.1
  · rw [sMin, Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

lemma sMin_le {i : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ∃ f : Fin i → EuclideanSpace ℝ ι, (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f ∧
      ∀ j, ‖f j‖ ≤ r) : sMin Λ i ≤ r :=
  csInf_le ⟨0, fun x hx => hx.1⟩ ⟨hr, hf⟩

lemma sMin_le_sum_norm {i : ℕ} {f : Fin i → EuclideanSpace ℝ ι}
    (hf : ∀ j, f j ∈ Λ) (hi : LinearIndependent ℤ f) : sMin Λ i ≤ ∑ j, ‖f j‖ :=
  sMin_le (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    ⟨f, hf, hi, fun j => Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j)⟩

lemma sMin_mono {i j : ℕ} (hij : i ≤ j)
    (h : ∃ f : Fin j → EuclideanSpace ℝ ι, (∀ k, f k ∈ Λ) ∧ LinearIndependent ℤ f) :
    sMin Λ i ≤ sMin Λ j := by
  obtain ⟨f, hfΛ, hfind⟩ := h
  refine le_csInf ⟨∑ k, ‖f k‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, f, hfΛ, hfind,
    fun k => Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ k)⟩ ?_
  rintro r ⟨hr0, g, hgΛ, hgind, hgnorm⟩
  refine csInf_le ⟨0, fun x hx => hx.1⟩
    ⟨hr0, fun k => g (Fin.castLE hij k), fun k => hgΛ _,
      hgind.comp (Fin.castLE hij) (Fin.castLE_injective hij), fun k => hgnorm _⟩

lemma sMin_le_of_forall_eps {i : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ ε > 0, ∃ f : Fin i → EuclideanSpace ℝ ι, (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f ∧
      ∀ j, ‖f j‖ ≤ a + ε) : sMin Λ i ≤ a :=
  le_of_forall_pos_le_add fun ε hε => sMin_le (by linarith) (h ε hε)

lemma le_sMin_of_forall {i : ℕ} {a : ℝ}
    (hne : ∃ f : Fin i → EuclideanSpace ℝ ι, (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f)
    (h : ∀ r : ℝ, 0 ≤ r → (∃ f : Fin i → EuclideanSpace ℝ ι, (∀ j, f j ∈ Λ) ∧
      LinearIndependent ℤ f ∧ ∀ j, ‖f j‖ ≤ r) → a ≤ r) : a ≤ sMin Λ i := by
  obtain ⟨f, hfΛ, hfind⟩ := hne
  refine le_csInf ⟨∑ j, ‖f j‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, f, hfΛ, hfind,
    fun j => Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j)⟩
    fun r hr => h r hr.1 hr.2

lemma sCnt_mono {T T' : ℝ} (h : T ≤ T') (hfin : {x | x ∈ Λ ∧ ‖x‖ ≤ T'}.Finite) :
    sCnt Λ T ≤ sCnt Λ T' :=
  Set.ncard_le_ncard (fun x hx => ⟨hx.1, le_trans hx.2 h⟩) hfin

lemma sCnt_bot {T : ℝ} (hT : 0 ≤ T) : sCnt (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) T = 1 := by
  have hset : {x : EuclideanSpace ℝ ι | x ∈ (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) ∧
      ‖x‖ ≤ T} = {0} := by
    ext x
    constructor
    · rintro ⟨hx, -⟩
      simpa using hx
    · rintro rfl
      exact ⟨Submodule.zero_mem _, by simpa using hT⟩
  rw [sCnt, hset, Set.ncard_singleton]

end basic

end Work.HP
