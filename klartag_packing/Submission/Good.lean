import Mathlib
import Submission.Contact

/-!
# The measurable good event of the exploration process

`Submission/Contact.badEvent` is defined by an existential quantifier over the *whole* unit
sphere, which makes its measurability awkward.  For the drift estimate we only ever use two
properties of the complement: the quadratic form of `A_k - a₀·Id` is bounded by `2r` on the unit
sphere, and the event has small measure.

Both are available for the *net* event

    badNet S r = {ω | ∃ k ≤ K, ∃ x ∈ S, r < |quadFormV (A_k - a₀·Id) x|}

where `S` is a finite `1/4`-net of the unit sphere.  This set is a finite union of measurable
sets, its measure is bounded by the union bound, and its complement gives the quadratic-form
bound through `Commons.Analysis.InnerProductSpace.quadform_le_of_sphere_net`.
-/

namespace Submission.Good

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.OpNorm
open Submission.Contact

noncomputable section

variable {d m : ℕ} (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)

/-- The net-based bad event. -/
def badNet (S : Finset (Vec d)) (r : ℝ) : Set (Fin K → MatV d × MatV d) :=
  {ω | ∃ k ≤ K, ∃ x ∈ S, r < |quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) x|}

lemma measurableSet_badNet (S : Finset (Vec d)) (r : ℝ) : MeasurableSet (badNet R BoxL a₀ ε K S r) := by
  have hset : badNet R BoxL a₀ ε K S r
      = ⋃ k ∈ Finset.range (K + 1), ⋃ x ∈ S,
          {ω : Fin K → MatV d × MatV d | r < |quadFormV (proc (projL R BoxL) a₀ ε K ω k
            - a₀ • oneV d) x|} := by
    ext ω
    simp only [badNet, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨k, hk, hne⟩
      exact ⟨k, Nat.lt_succ_of_le hk, hne⟩
    · rintro ⟨k, hk, hne⟩
      exact ⟨k, Nat.le_of_lt_succ hk, hne⟩
  rw [hset]
  refine MeasurableSet.biUnion (Finset.countable_toSet _) fun k _ => ?_
  refine MeasurableSet.biUnion (Finset.countable_toSet _) fun x _ => ?_
  refine measurableSet_lt measurable_const ?_
  exact ((Contact.measurable_quadFormV_left x).comp
    ((measurable_proc (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
      (measurable_projL R BoxL) k).sub measurable_const)).abs

theorem badNet_measureReal_le (S : Finset (Vec d)) (hSun : ∀ x ∈ S, ‖x‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hε : 0 ≤ ε) :
    (sampleLaw d K).real (badNet R BoxL a₀ ε K S r)
      ≤ (S.card : ℝ) * (8 * Real.exp (-(r ^ 2) / (2 * (K : ℝ) * ε ^ 2))) := by
  classical
  set E : Vec d → Set (Fin K → MatV d × MatV d) := fun x =>
    {ω | ∃ k ≤ K, r < |∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < k),
        ε * inner ℝ (incrAt (projL R BoxL) a₀ ε K ω j) (tensorV x)|} with hE
  have heach : ∀ x ∈ S, (sampleLaw d K).real (E x)
      ≤ 8 * Real.exp (-(r ^ 2) / (2 * (K : ℝ) * ε ^ 2)) := by
    intro x hx
    have hW : ‖tensorV x‖ ≤ 1 := by rw [norm_tensorV, hSun x hx]; norm_num
    have hmain := maximal_tail_incr (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
      (measurable_projL R BoxL) (fun A => good_projL R BoxL A) (tensorV x) hW hε hr
    refine le_trans (MeasureTheory.measureReal_mono ?_ (MeasureTheory.measure_ne_top _ _)) hmain
    intro ω hω
    obtain ⟨k, hk, hlt⟩ := hω
    exact ⟨k, hk, le_of_lt hlt⟩
  have hsub : badNet R BoxL a₀ ε K S r ⊆ ⋃ x ∈ S, E x := by
    rintro ω ⟨k, hk, x, hx, hlt⟩
    refine Set.mem_biUnion hx ?_
    refine ⟨k, hk, ?_⟩
    rw [quadFormV_state_sub (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K) hk ω x] at hlt
    exact hlt
  calc (sampleLaw d K).real (badNet R BoxL a₀ ε K S r)
      ≤ (sampleLaw d K).real (⋃ x ∈ S, E x) :=
        MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top _ _)
    _ ≤ ∑ x ∈ S, (sampleLaw d K).real (E x) := MeasureTheory.measureReal_biUnion_finset_le S E
    _ ≤ ∑ _x ∈ S, (8 * Real.exp (-(r ^ 2) / (2 * (K : ℝ) * ε ^ 2))) :=
        Finset.sum_le_sum fun x hx => heach x hx
    _ = (S.card : ℝ) * (8 * Real.exp (-(r ^ 2) / (2 * (K : ℝ) * ε ^ 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- On the complement of the net-based bad event, the quadratic form of `A_k - a₀·Id` is bounded
by `2r‖y‖²` for every `y`. -/
lemma quadFormV_bound_of_not_badNet (S : Finset (Vec d)) (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : Vec d, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ 1 / 4) {r : ℝ} {ω : Fin K → MatV d × MatV d}
    (h : ω ∉ badNet R BoxL a₀ ε K S r) (hr : 0 ≤ r) (k : ℕ) (hk : k ≤ K) (y : Vec d) :
    |quadFormV (proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d) y| ≤ 2 * r * ‖y‖ ^ 2 := by
  set M : MatV d := proc (projL R BoxL) a₀ ε K ω k - a₀ • oneV d with hM
  have hMsym : (matOf d M).IsSymm := symm_state_sub (pl := projL R BoxL) (a₀ := a₀) (ε := ε)
    (K := K) (fun A => good_projL R BoxL A) k ω
  by_cases hy : y = 0
  · subst hy
    rw [quadFormV_zero, norm_zero, abs_zero]; ring_nf; positivity
  · have hnorm : ‖y‖ ^ 2 ≠ 0 := by positivity
    have hunit : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
    have hnet : ∀ x ∈ S, |quadFormV M x| ≤ r := by
      intro x hx
      by_contra hc
      exact h ⟨k, hk, x, hx, lt_of_not_ge hc⟩
    have hnet' : ∀ x ∈ S, |∑ i, ∑ j, (matOf d M) i j * x i * x j| ≤ r := by
      intro x hx
      simpa [quadFormV] using hnet x hx
    have hall := Commons.Analysis.InnerProductSpace.quadform_le_of_sphere_net
      (matOf d M) hMsym hr S hSun hcover hnet' ((‖y‖⁻¹ : ℝ) • y)
    rw [hunit] at hall
    simp only [one_pow, mul_one] at hall
    have hkey : |quadFormV M ((‖y‖⁻¹ : ℝ) • y)| ≤ 2 * r := by
      rw [show quadFormV M ((‖y‖⁻¹ : ℝ) • y)
          = ∑ i, ∑ j, (matOf d M) i j * ((‖y‖⁻¹ : ℝ) • y) i * ((‖y‖⁻¹ : ℝ) • y) j from rfl]
      linarith
    have h2 : ‖y‖ ^ 2 * (‖y‖⁻¹ : ℝ) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_pow]
    have hsplit : quadFormV M y = ‖y‖ ^ 2 * quadFormV M ((‖y‖⁻¹ : ℝ) • y) := by
      rw [quadFormV_smul_right, ← mul_assoc, h2, one_mul]
    rw [hsplit, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2)]
    calc ‖y‖ ^ 2 * |quadFormV M ((‖y‖⁻¹ : ℝ) • y)| ≤ ‖y‖ ^ 2 * (2 * r) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 2 * r * ‖y‖ ^ 2 := by ring

end

end Submission.Good
