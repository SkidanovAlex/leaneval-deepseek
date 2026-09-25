import Mathlib
import Submission.Work.CR.Flat.Cauchy.recU_estimate
import Submission.Work.CR.Flat.Cauchy.recU_estimate_uniform

noncomputable section

open scoped NNReal ENNReal ContDiff

namespace Work.NN.Final

open Work.CR.Flat.Cauchy

/-!
# The `C^{0,α}` estimate for `recU` without global closedness of the datum

`Work.CR.Flat.Cauchy.recU_estimate_uniform` proves, for data `f` which are *globally* closed
(`IsClosedForm f`), the uniform `C^{0,α}` bound on the polydisc of radius `eqRad`

  `‖recU f z‖ ≤ C * S`,  `‖recU f x - recU f y‖ ≤ C * S * ‖x - y‖ ^ α`,
  where `S = ∑ j, (holderNorm 0 α (f j) (polydisc 0 1)).toReal`.

The closedness hypothesis enters *only* through the smoothness of the stages of the recursion,
which in that module is supplied by `recF_inv` (`Work.CR.Flat.Cauchy.openSolRec`).  The estimates
themselves (`recU_data_bound`, `recF_stage_bound`, `recU_bound_explicit`) use nothing but the
`C^{0,α}` control of the datum.  Here we remove the closedness hypothesis: the only thing we need
is that each stage `recF f m k` is continuous, and this follows from `C¹`-ness of the datum alone
by the same induction as in `openSolRec.recF_inv`, with the closedness hypothesis left out.

The estimate is the one consumed by the fixed-point argument of the assembly chapter for
Newlander–Nirenberg, where the datum `f = ∂̄_J v` is only closed on a polydisc, not globally.
-/

/-- Any finite smoothness level is below the `C^∞` level `∞`. -/
private lemma le_infty (m : ℕ) : (m : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  exact_mod_cast le_top

/-- **The stages of the recursion are `C¹` when the datum is, with no closedness hypothesis.**
This is the first conjunct of `Work.CR.Flat.Cauchy.recF_inv`, whose proof never uses closedness. -/
private lemma recF_contDiff_one {n : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) : ∀ s ≤ n, ∀ j, ContDiff ℝ 1 (recF f s j) := by
  intro s
  induction s with
  | zero => intro _; simpa using hf
  | succ s ihs =>
      intro hs
      have ih1 : ∀ i, ContDiff ℝ 1 (recF f s i) := ihs (by omega)
      by_cases hlt : s < n
      · set j : Fin n := ⟨s, hlt⟩ with hj
        have hrec : recF f (s + 1) = stepData j (recF f s) := recF_succ_of_lt f hlt
        intro i
        rw [hrec]
        simp only [stepData]
        exact contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) j 1
          (((contDiff_cutFbar j).of_le (le_infty _)).mul (ih1 i))
          (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])
      · have hrec : recF f (s + 1) = recF f s := by
          rw [recF_succ]; simp [hlt]
        intro i
        rw [hrec]
        exact ih1 i

/-- Continuity of the stages, the form in which the estimates of `recU_bound_explicit` /
`recF_stage_bound` consume the regularity of the datum. -/
private lemma recF_continuous_one {n : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) : ∀ m, m ≤ n → ∀ k : Fin n, Continuous (recF f m k) :=
  fun m hm k => (recF_contDiff_one hf m hm k).continuous

/-- **The `C^{0,α}` estimate for `recU` on the polydisc of radius `eqRad`, for data which are only
assumed `C¹` (and with finite `C^{0,α}`-norm), with a constant independent of the datum.** -/
theorem recUEstimateNoClosed {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (f j)) →
        (∑ j, Work.CR.Flat.holderNorm 0 α (f j) (Work.CR.Flat.polydisc 0 (fun _ => 1))) ≠ ⊤ →
        (∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < Work.CR.Flat.Cauchy.eqRad) →
            ‖Work.CR.Flat.Cauchy.recU f z‖ ≤
              C * ∑ j, (Work.CR.Flat.holderNorm 0 α (f j)
                (Work.CR.Flat.polydisc 0 (fun _ => 1))).toReal) ∧
        (∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < Work.CR.Flat.Cauchy.eqRad) →
            (∀ l, ‖y l‖ < Work.CR.Flat.Cauchy.eqRad) →
            ‖Work.CR.Flat.Cauchy.recU f x - Work.CR.Flat.Cauchy.recU f y‖ ≤
              C * (∑ j, (Work.CR.Flat.holderNorm 0 α (f j)
                (Work.CR.Flat.polydisc 0 (fun _ => 1))).toReal) * ‖x - y‖ ^ α) := by
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
  · intro f hf1 hS
    obtain ⟨hS0, hA, hH⟩ := recU_data_bound (n := n) (α := α) (f := f) hα hS
    set S : ℝ := ∑ j, (Work.CR.Flat.holderNorm 0 α (f j)
      (Work.CR.Flat.polydisc 0 (fun _ => 1))).toReal with hSdef
    have hS0' : 0 ≤ S := by rw [hSdef]; exact hS0
    have hA' : ∀ j z, z ∈ trackSet → ‖f j z‖ ≤ S := fun j z hz => by
      rw [hSdef]; exact hA j z hz
    have hH' : ∀ j x y, x ∈ trackSet → y ∈ trackSet → ‖f j x - f j y‖ ≤ S * ‖x - y‖ ^ α :=
      fun j x y hx hy => by rw [hSdef]; exact hH j x y hx hy
    have hcont : ∀ m, m ≤ n → ∀ k : Fin n, Continuous (recF f m k) :=
      recF_continuous_one hf1
    exact recU_bound_explicit (S := S) (K := K) hα hα1 hK1 hL0 hLip hS0' hcont
      (recF_stage_bound (C₀ := C₀) (S := S) hC₀pos hC₀prop hS0' hA' hH' hcont)

end Work.NN.Final
