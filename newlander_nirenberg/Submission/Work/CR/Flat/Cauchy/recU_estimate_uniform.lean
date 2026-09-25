/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The *uniform* `C^{0,α}` estimate for the explicit solution `recU`

The explicit solution `recU f` of the unsupported `∂̄`-problem on the unit polydisc
(constructed coordinate by coordinate in `Submission/Work/CR/Flat/Cauchy/openSolRec.lean`)
satisfies, on the polydisc of radius `eqRad = 3/4` and with a constant which is
*independent of the data* `f`,

  `‖recU f z‖ ≤ C * S`,   `‖recU f x - recU f y‖ ≤ C * S * ‖x - y‖ ^ α`,

where `S = ∑ j, (holderNorm 0 α (f j) (polydisc 0 1)).toReal` is the `C^{0,α}`-norm of
the data.  This is the estimate needed by the final assembly
`exists_dbar_solution_polydisc_open`, where a *single* constant has to work for every `f`.

The proof follows the plan recorded in the header of `openSolRec.lean`:

* `recU_data_bound` (Step 0): the `C^{0,α}`-norm of the data controls `f` pointwise and
  in Hölder fashion on `trackSet`;
* `exists_uniform_dbarC_bound` (Step 1): the constant `C₀` of
  `cutFbar_mul_bound_uniform` can be made independent of the coordinate `j` (take the
  maximum of the constants chosen for the finitely many `j`); this is what makes the
  induction uniform;
* `recF_stage_bound` (Step 2): by induction on the stage `m`, the data at stage `m` are
  bounded by `K ^ m * S` (pointwise and in Hölder fashion) with
  `K = max 1 (4 * trRho * C₀) + 1`;
* `recU_bound_explicit` (Step 3): summing the `n` summands of `recU`.

Each of the three ingredients is proved in its own module; the constant produced below is
explicit: `2 * trRho * n * K ^ n * (2 + L) + 1`, where `L` is a Lipschitz constant for the
cutoff `openCut` and `K` is as above.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Cauchy.cutFbar_mul_bound_uniform
import Submission.Work.CR.Flat.Cauchy.dbarTransform_basic
import Submission.Work.CR.Flat.Cauchy.recU_data_bound
import Submission.Work.CR.Flat.Cauchy.recF_stage_bound
import Submission.Work.CR.Flat.Cauchy.recU_bound_explicit

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- **Step 1 of the plan: the constant of `cutFbar_mul_bound_uniform` can be taken
independent of the coordinate `j`.**  For every `j` the lemma `cutFbar_mul_bound_uniform`
produces a constant `C j > 0`; the sum `∑ j, C j + 1` is larger than every `C j`, hence
works simultaneously for all coordinates. -/
theorem exists_uniform_dbarC_bound (n : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (j : Fin n) {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
      (∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A) →
      (∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet → ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
      (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) → ‖z j‖ ≤ cutOut →
        ‖dbarC openCut (z j) * F z‖ ≤ C₀ * A) ∧
      (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
        (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
        ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
          ≤ C₀ * (A + H) * ‖a - a'‖ ^ α) := by
  classical
  obtain ⟨cχ, -, hcχ⟩ := dbarC_openCut_bounded
  obtain ⟨cχ', -, hcχ'⟩ := dbarC_openCut_lipschitz
  have hcχ0 : ∀ ζ : ℂ, cutOut ≤ ‖ζ‖ → dbarC openCut ζ = 0 :=
    fun ζ h => dbarC_openCut_eq_zero_of_le_norm h
  let Cj : Fin n → ℝ := fun j =>
    Classical.choose (cutFbar_mul_bound_uniform (n := n) (α := α) hα hα1 (j := j) hcχ hcχ0 hcχ')
  have hCj : ∀ j : Fin n, 0 < Cj j ∧ ∀ {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
      (∀ z : Fin n → ℂ, z ∈ trackSet → ‖F z‖ ≤ A) →
      (∀ x y : Fin n → ℂ, x ∈ trackSet → y ∈ trackSet → ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
      (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < trTrack) → ‖z j‖ ≤ cutOut →
        ‖dbarC openCut (z j) * F z‖ ≤ Cj j * A) ∧
      (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < trTrack) →
        (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
        ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖
          ≤ Cj j * (A + H) * ‖a - a'‖ ^ α) :=
    fun j => Classical.choose_spec
      (cutFbar_mul_bound_uniform (n := n) (α := α) hα hα1 (j := j) hcχ hcχ0 hcχ')
  refine ⟨(∑ j, Cj j) + 1, ?_, ?_⟩
  · have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hCj j).1.le)
    linarith
  · intro j F A H hA0 hH0 hF hFH
    obtain ⟨b1, b2⟩ := (hCj j).2 hA0 hH0 hF hFH
    have hle : Cj j ≤ (∑ i, Cj i) + 1 := by
      have h1 := Finset.single_le_sum (f := Cj)
        (fun i (_ : i ∈ Finset.univ) => (hCj i).1.le) (Finset.mem_univ j)
      linarith
    refine ⟨?_, ?_⟩
    · intro z hz hzj
      exact le_trans (b1 z hz hzj) (mul_le_mul_of_nonneg_right hle hA0)
    · intro a a' ha ha'
      have ht : 0 ≤ ‖a - a'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
      have hAH : 0 ≤ A + H := by linarith
      exact le_trans (b2 a a' ha ha')
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hAH) ht)

/-- The data of the recursion at stage `m ≤ n` are continuous (this is all the smoothness
that the estimates of `dbarTransform_basic` require). -/
theorem recF_continuous {n : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf1 : ∀ j, ContDiff ℝ 1 (f j)) (hcl : IsClosedForm f) :
    ∀ m, m ≤ n → ∀ k : Fin n, Continuous (recF f m k) :=
  fun m hm k => ((recF_inv (k := 0) hf1 hcl m hm).1 k).continuous

/-- **The uniform `C^{0,α}` estimate for `recU`.**  The constant only depends on `n`, `α`
and the fixed absolute constants of the cutoff `openCut`. -/
theorem recU_estimate_uniform {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (f j)) →
      IsClosedForm f → (∑ j, holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))) ≠ ⊤ →
      (∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < eqRad) →
        ‖recU f z‖ ≤ C * ∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) ∧
      (∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < eqRad) → (∀ l, ‖y l‖ < eqRad) →
        ‖recU f x - recU f y‖ ≤
          C * (∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) * ‖x - y‖ ^ α) := by
  obtain ⟨C₀, hC₀pos, hC₀prop⟩ := exists_uniform_dbarC_bound n α hα hα1
  obtain ⟨L, hL0, hLip⟩ := openCut_lipschitz
  let K : ℝ := max 1 (4 * trRho * C₀) + 1
  have hK1 : 1 ≤ K := by
    have h1 : (1 : ℝ) ≤ max 1 (4 * trRho * C₀) := le_max_left _ _
    simp only [K]
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  refine ⟨2 * trRho * (n : ℝ) * K ^ n * (2 + L) + 1, ?_, ?_⟩
  · have hb : (0 : ℝ) ≤ 2 * trRho * (n : ℝ) * K ^ n * (2 + L) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith [trRho_pos]) (Nat.cast_nonneg n))
        (pow_nonneg (le_of_lt hKpos) n)) (by linarith)
    linarith
  · intro f hf1 hcl hS
    obtain ⟨hS0, hA, hH⟩ := recU_data_bound (n := n) (α := α) (f := f) hα hS
    set S : ℝ := ∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal with hSdef
    have hS0' : 0 ≤ S := by rw [hSdef]; exact hS0
    have hA' : ∀ j z, z ∈ trackSet → ‖f j z‖ ≤ S :=
      fun j z hz => by rw [hSdef]; exact hA j z hz
    have hH' : ∀ j x y, x ∈ trackSet → y ∈ trackSet → ‖f j x - f j y‖ ≤ S * ‖x - y‖ ^ α :=
      fun j x y hx hy => by rw [hSdef]; exact hH j x y hx hy
    have hcont : ∀ m, m ≤ n → ∀ k : Fin n, Continuous (recF f m k) :=
      recF_continuous hf1 hcl
    exact recU_bound_explicit (S := S) (K := K) hα hα1 hK1 hL0 hLip hS0' hcont
      (recF_stage_bound (C₀ := C₀) (S := S) hC₀pos hC₀prop hS0' hA' hH' hcont)

end Work.CR.Flat.Cauchy
