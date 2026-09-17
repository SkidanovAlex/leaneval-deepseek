import Mathlib
import Submission.MatSpace
import Submission.GenProc
import Submission.OpNorm

set_option synthInstance.maxHeartbeats 1000000

/-!
# The constraint projection of the exploration process

The constraint space of the process at a matrix `A` is the space of symmetric matrices whose
quadratic form vanishes on every *violated* vector, i.e. every candidate vector `y` with
`quadFormV A y ≤ 1`:

    F(A) = {M ∈ Sym_d : ⟨M, y ⊗ y⟩ = 0  for all violated candidates y}.

The set of violated vectors is a function of `A` alone, and the projection onto `F(A)` is
therefore a Borel function of `A`, which is what `Submission.GenProc` needs.

The candidates are an arbitrary finite family `BoxL : Fin m → Vec d` of nonzero vectors.  In the
application `BoxL` enumerates all nonzero lattice vectors in a large ball, so that (on an event
of overwhelming probability) *every* vector that can be violated is among the candidates; the
construction of that box is in `Submission/LatticeBox.lean`.
-/

namespace Submission.Contact

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.OpNorm

noncomputable section

variable {d m : ℕ}

/-- Vectors of `ℝ^d`. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable (R : ℝ)

/-- The pattern of *violated candidates* of the matrix `A`: the candidates `y` of norm at most
`R` whose quadratic form is at most `1`.  The norm restriction is a bookkeeping device: it makes
`violSet` unconditionally finite, of size at most the number of lattice points in a ball of
radius `R`. -/
def patt (BoxL : Fin m → Vec d) (A : MatV d) : Fin m → Bool :=
  fun i => if ‖BoxL i‖ ≤ R ∧ quadFormV A (BoxL i) ≤ 1 then true else false

lemma measurable_quadFormV_left (y : Vec d) :
    Measurable fun A : MatV d => quadFormV A y := by
  simp only [quadFormV]
  fun_prop

lemma measurable_patt (BoxL : Fin m → Vec d) : Measurable (patt R BoxL) := by
  rw [measurable_pi_iff]
  intro i
  have hc : Measurable fun _ : MatV d => ‖BoxL i‖ := measurable_const
  refine Measurable.ite ?_ measurable_const measurable_const
  exact MeasurableSet.inter (measurableSet_le hc measurable_const)
    (measurableSet_le (measurable_quadFormV_left (BoxL i)) measurable_const)

/-- The constraint projection attached to a violation pattern. -/
def projOf (BoxL : Fin m → Vec d) (χ : Fin m → Bool) : MatV d →L[ℝ] MatV d :=
  (tangentSub ((Finset.univ.filter (fun i : Fin m => χ i = true)).image BoxL)).starProjection

lemma measurable_projOf (BoxL : Fin m → Vec d) : Measurable (projOf BoxL) :=
  measurable_of_finite _

/-- The constraint projection of the process at the matrix `A`. -/
def projL (BoxL : Fin m → Vec d) (A : MatV d) : MatV d →L[ℝ] MatV d :=
  projOf BoxL (patt R BoxL A)

lemma measurable_projL (BoxL : Fin m → Vec d) : Measurable (projL R BoxL) :=
  (measurable_projOf BoxL).comp (measurable_patt R BoxL)

/-- The set of violated candidates of `A`. -/
def violSet (BoxL : Fin m → Vec d) (A : MatV d) : Finset (Vec d) :=
  (Finset.univ.filter (fun i : Fin m => ‖BoxL i‖ ≤ R ∧ quadFormV A (BoxL i) ≤ 1)).image BoxL

lemma projL_apply_eq (BoxL : Fin m → Vec d) (A : MatV d) :
    projL R BoxL A = (tangentSub (violSet R BoxL A)).starProjection := by
  have h : (Finset.univ.filter (fun i : Fin m => patt R BoxL A i = true)).image BoxL
      = violSet R BoxL A := by
    ext y
    simp only [violSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, patt,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases hh : ‖BoxL i‖ ≤ R ∧ quadFormV A (BoxL i) ≤ 1
      · exact ⟨i, hh, rfl⟩
      · simp [hh] at hi
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, by simp [hi], rfl⟩
  unfold projL projOf
  exact congrArg (fun S : Finset (Vec d) => (tangentSub S).starProjection) h

lemma tangentSub_le_symV (S : Finset (Vec d)) : tangentSub S ≤ symV d := inf_le_left

/-- The constraint projection is an admissible (self-adjoint idempotent onto symmetric
matrices) operator. -/
lemma good_tangentSub (S : Finset (Vec d)) : Good ((tangentSub S).starProjection) where
  idem := by
    refine ContinuousLinearMap.ext fun x => ?_
    rw [ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)]
  adj := fun x y => Submodule.inner_starProjection_left_eq_right _ x y
  maps := fun x => tangentSub_le_symV S (Submodule.starProjection_apply_mem _ _)

lemma good_projL (BoxL : Fin m → Vec d) (A : MatV d) : Good (projL R BoxL A) := by
  rw [projL_apply_eq]; exact good_tangentSub _

/-! ## The good event

The operator-norm maximal bound says that, outside an event of probability
`≤ (4C)^d·8e^{-r²/2Kε²}`, the matrix `A_k - a₀·Id` has quadratic form bounded by `2r` on the
unit sphere, for all `k ≤ K`.
-/

/-- The bad event of the maximal operator-norm bound. -/
def badEvent (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ) (r : ℝ) :
    Set (Fin K → MatV d × MatV d) :=
  {ω | ∃ k ≤ K, ∃ x : Vec d, ‖x‖ = 1 ∧
    2 * r < |quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) x|}

variable (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)

theorem badEvent_measureReal_le {r : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) :
    ∃ C : ℝ, 1 ≤ C ∧ (sampleLaw d K).real (badEvent R BoxL a₀ ε K r)
      ≤ (4 * C) ^ d * (8 * Real.exp (-r ^ 2 / (2 * (K : ℝ) * ε ^ 2))) :=
  maximal_tail_quadform_exists (pl := projL R BoxL) (a₀ := a₀) (K := K)
    (measurable_projL R BoxL) (fun A => good_projL R BoxL A) hε hr

lemma quadFormV_zero (M : MatV d) : quadFormV M (0 : Vec d) = 0 := by
  simp [quadFormV]

/-- On the complement of the bad event the quadratic form of `A_k - a₀·Id` is bounded by
`2r‖y‖²` for every `y`. -/
lemma quadFormV_bound_of_not_bad {r : ℝ} {ω : Fin K → MatV d × MatV d}
    (h : ω ∉ badEvent R BoxL a₀ ε K r) (k : ℕ) (hk : k ≤ K) (y : Vec d) :
    |quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) y| ≤ 2 * r * ‖y‖ ^ 2 := by
  set M : MatV d := proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d with hM
  by_cases hy : y = 0
  · subst hy
    rw [quadFormV_zero, norm_zero, abs_zero]; ring_nf; positivity
  · have hnorm : ‖y‖ ^ 2 ≠ 0 := by positivity
    have hunit : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
    have hkey : |quadFormV M ((‖y‖⁻¹ : ℝ) • y)| ≤ 2 * r := by
      by_contra hc
      rw [not_le] at hc
      exact h ⟨k, hk, _, hunit, hc⟩
    have h2 : ‖y‖ ^ 2 * (‖y‖⁻¹ : ℝ) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_pow]
    have hsplit : quadFormV M y = ‖y‖ ^ 2 * quadFormV M ((‖y‖⁻¹ : ℝ) • y) := by
      rw [quadFormV_smul_right, ← mul_assoc, h2, one_mul]
    rw [hsplit, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2)]
    calc ‖y‖ ^ 2 * |quadFormV M ((‖y‖⁻¹ : ℝ) • y)| ≤ ‖y‖ ^ 2 * (2 * r) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 2 * r * ‖y‖ ^ 2 := by ring

/-- On the complement of the bad event, the quadratic form of the state is squeezed between
`(a₀-2r)‖y‖²` and `(a₀+2r)‖y‖²`. -/
lemma quadFormV_state_squeeze {r : ℝ} {ω : Fin K → MatV d × MatV d}
    (h : ω ∉ badEvent R BoxL a₀ ε K r) (k : ℕ) (hk : k ≤ K) (y : Vec d) :
    (a₀ - 2 * r) * ‖y‖ ^ 2 ≤ quadFormV (proc (projL R BoxL) a₀ ε K ω k) y ∧
      quadFormV (proc (projL R BoxL) a₀ ε K ω k) y ≤ (a₀ + 2 * r) * ‖y‖ ^ 2 := by
  have hb := quadFormV_bound_of_not_bad R BoxL a₀ ε K h k hk y
  have hsplit : quadFormV (proc (projL R BoxL) a₀ ε K ω k) y
      = quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) y + a₀ * ‖y‖ ^ 2 := by
    conv_lhs => rw [show proc (projL R BoxL) a₀ ε K ω k
        = (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) + a₀ • oneV d from by abel]
    rw [quadFormV_add, quadFormV_oneV]
  constructor
  · rw [hsplit]
    have h1 := (abs_le.mp hb).1
    nlinarith
  · rw [hsplit]
    have h1 := (abs_le.mp hb).2
    nlinarith

/-! ## Rank bookkeeping -/

theorem finrank_tangentSub_violSet_ge (hne : ∀ i, BoxL i ≠ 0)
    (hnegL : ∀ i, ∃ j, BoxL j = -BoxL i) (hR : 0 ≤ R) (A : MatV d) :
    d * (d + 1) ≤ 2 * Module.finrank ℝ ↥(tangentSub (violSet R BoxL A))
      + (violSet R BoxL A).card := by
  have hneg : ∀ x ∈ violSet R BoxL A, -x ∈ violSet R BoxL A := by
    intro x hx
    rw [violSet, Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_filter] at hi
    obtain ⟨j, hj⟩ := hnegL i
    have hev : quadFormV A (-BoxL i) = quadFormV A (BoxL i) := by
      simpa using quadFormV_smul_right A (-1 : ℝ) (BoxL i)
    refine ⟨j, ?_, hj⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hj, norm_neg]; exact hi.2.1
    · rw [hj, hev]; exact hi.2.2
  have hne' : ∀ x ∈ violSet R BoxL A, x ≠ 0 := by
    intro x hx
    rw [violSet, Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hne i
  exact finrank_tangentSub_ge (violSet R BoxL A) hne' hneg

end

end Submission.Contact
