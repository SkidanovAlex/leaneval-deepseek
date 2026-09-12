import Submission.Model
import Submission.ModelCore
import Submission.ModelAlg
import Submission.ModelFlow
import Submission.ModelUniq
import Mathlib

/-!
# Time-rescaling of model geodesics

Task: prove the final theorem `geodesic_rescale` (replace its placeholder proof).

If `(c, vel)` is a geodesic with initial data `(x₀, v₀)` defined on `Ioo (-ε) ε`, then for any
`s : ℝ` with `s ≠ 0` the rescaled curve `t ↦ c (s * t)` (with velocity `t ↦ s • vel (s * t)`)
is a geodesic with initial data `(x₀, s • v₀)` defined on `Ioo (-ε / |s|) (ε / |s|)`.

Sketch:
1. Show `HasDerivAt (fun u => c (s * u)) (s • vel (s * t)) t` from `hc` by the chain rule
   (`HasDerivAt.scomp` / `HasDerivAt.comp` with `(fun u => s * u)` and scalar multiplication),
   valid for `s * t ∈ Ioo (-ε) ε`, i.e. `t ∈ Ioo (-ε/|s|) (ε/|s|)` (prove by cases on the sign of `s`
   or use `abs`: `|s*t| < ε` iff `|t| < ε/|s|`, `div_lt_iff₀` etc.).
2. Show the velocity equation: derivative of `t ↦ s • vel (s*t)` equals
   `s ^ 2 • accel (g (c (s*t))) (fderiv ℝ g (c (s*t))) (vel (s*t))`, which by `accel_smul`
   equals `accel (g (c (s*t))) (fderiv ℝ g (c (s*t))) (s • vel (s*t))`.
   (This is where `Submission.Model.accel_smul` is used; import `Submission.ModelAlg`.)
3. Combine into `(c', vel') := (fun t => c (s*t), fun t => s • vel (s*t))`, then apply
   `uniform_exists_geodesic`-style existence + `unique_geodesic` is NOT needed if the theorem is
   stated as "the rescaled curve is a geodesic", which only needs the two HasDerivAt statements.

Actually the cleanest statement (no uniqueness needed):

    geodesic_rescale (g) (hg) (hinv) {ε : ℝ} (hε : 0 < ε) {c vel : ℝ → E}
      (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
      (hv : ∀ t ∈ Ioo (-ε) ε, HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
      {s : ℝ} (hs : s ≠ 0) :
      (∀ t ∈ Ioo (-ε / |s|) (ε / |s|),
        HasDerivAt (fun u => c (s * u)) (s • vel (s * t)) t) ∧
      (∀ t ∈ Ioo (-ε / |s|) (ε / |s|),
        HasDerivAt (fun u => s • vel (s * u))
          (accel (g (c (s * t))) (fderiv ℝ g (c (s * t))) (s • vel (s * t))) t)

This is a purely analytic statement: no new existence/uniqueness is required.  Prove it by
unfolding, chain rule and `accel_smul`.  You may add helper lemmas.

Do NOT change the statement of `geodesic_rescale`.  The final file must contain no placeholders/axioms.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- If `t` lies in the rescaled interval `Ioo (-ε / |s|) (ε / |s|)` then `s * t` lies in
`Ioo (-ε) ε`.  Follows from `|t| < ε / |s|` ⇒ `|s * t| = |s| * |t| < |s| * (ε / |s|) = ε`. -/
lemma smul_mem_Ioo {ε s t : ℝ} (hs : s ≠ 0)
    (ht : t ∈ Ioo (-ε / |s|) (ε / |s|)) : s * t ∈ Ioo (-ε) ε := by
  have ht' : |t| < ε / |s| := by
    have hpair : -(ε / |s|) < t ∧ t < ε / |s| := by
      constructor
      · have : -ε / |s| < t := ht.1
        simpa [neg_div] using this
      · exact ht.2
    exact abs_lt.mpr hpair
  have hs0 : 0 < |s| := abs_pos.mpr hs
  have h1 : |s| * |t| < |s| * (ε / |s|) := mul_lt_mul_of_pos_left ht' hs0
  have h2 : |s| * (ε / |s|) = ε := mul_div_cancel₀ ε (abs_ne_zero.mpr hs)
  have h3 : |s| * |t| < ε := by
    rw [h2] at h1
    exact h1
  have h4 : |s * t| < ε := by
    rw [abs_mul]
    exact h3
  exact abs_lt.mp h4

/-- Time rescaling of a geodesic by a nonzero factor gives another geodesic. -/
theorem geodesic_rescale (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε) {c vel : ℝ → E}
    (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    {s : ℝ} (hs : s ≠ 0) :
    (∀ t ∈ Ioo (-ε / |s|) (ε / |s|),
      HasDerivAt (fun u => c (s * u)) (s • vel (s * t)) t) ∧
    (∀ t ∈ Ioo (-ε / |s|) (ε / |s|),
      HasDerivAt (fun u => s • vel (s * u))
        (accel (g (c (s * t))) (fderiv ℝ g (c (s * t))) (s • vel (s * t))) t) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    have hmem : s * t ∈ Ioo (-ε) ε := smul_mem_Ioo hs ht
    have hlin : HasDerivAt (fun u : ℝ => s * u) s t := by
      simpa using (hasDerivAt_id t).const_mul s
    exact HasDerivAt.scomp t (hc (s * t) hmem) hlin
  · intro t ht
    have hmem : s * t ∈ Ioo (-ε) ε := smul_mem_Ioo hs ht
    have hlin : HasDerivAt (fun u : ℝ => s * u) s t := by
      simpa using (hasDerivAt_id t).const_mul s
    have hder := HasDerivAt.scomp t (hv (s * t) hmem) hlin
    have hders := HasDerivAt.const_smul s hder
    refine hders.congr_deriv ?_
    simp [accel_smul, smul_smul, pow_two]

end

end Submission.Model
