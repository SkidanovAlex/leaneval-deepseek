/-
# The endpoint estimate of area A8 (`lam_endpoint`)

This module proves the endpoint estimate for the trilinear form

`lam T ψ u v w = ∑'_x ⟨T u v (·) x, ψ x⟩ · w x`

of area A8 (`Submission/Work/KMTAreas/A8Trilinear.lean`), in the precise form in which the
trilinear interpolation of that area consumes it: from

* the hypothesis `hψ` that for every `x` the linear functional `a ↦ ⟨a, ψ x⟩` is dominated by the
  `r`-variational norm, and
* the `ℒ^Q` estimate `‖x ↦ V^r(T f g)(x)‖_Q ≤ M ‖f‖_A ‖g‖_B` for finitely supported `f, g`,

we deduce the bound

`‖lam T ψ u v w‖ ≤ M ‖u‖_A ‖v‖_B ‖w‖_{Q'}`  (`Q' = conjExp Q`, `Q ∈ [1, ∞]`).

The mathematical content is Hölder's inequality for the pairing series, together with the
pointwise domination `‖⟨T u v (·) x, ψ x⟩‖ ≤ V^r(T u v (·) x)`.  The proof is done at the level of
`eLpNorm`, so that the degenerate end cases `Q = 1` (`Q' = ∞`) and `Q = ∞` (`Q' = 1`) are covered:
the general Hölder inequality `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm` accepts the Hölder triple
`Q, Q', 1` for every `1 ≤ Q`, with `ENNReal.HolderTriple` handling `1` and `⊤` transparently.

For `u`, `v`, `w` not all finitely supported `lam` is zero by definition, so the estimate is
vacuous there; the content is the finitely supported case.
-/
import Mathlib
import Submission.Work.KMTAreas.A8Trilinear
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A8

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory (FinSupp)

/-- **Hölder's inequality for the pairing series.**  For `Q ∈ [1, ∞]` and arbitrary
`F w : ℤ → ℂ`,

  `‖∑'_x F x * w x‖ₑ ≤ ‖F‖_{ℒ^Q} · ‖w‖_{ℒ^{Q'}}`,  `Q' = conjExp Q = (1 - Q⁻¹)⁻¹`.

The series on the left is absolutely summable as soon as the right-hand side is finite, but the
estimate is stated for arbitrary `F`, `w` and in `ℝ≥0∞`, so the degenerate cases are absorbed by
the arithmetic of `ℝ≥0∞` (the left-hand side is `0` when the series is not summable). -/
lemma enorm_tsum_mul_le {F w : ℤ → ℂ} {Q : ENNReal} (hQ : 1 ≤ Q) :
    ‖∑' x : ℤ, F x * w x‖ₑ
      ≤ eLpNorm F Q Measure.count * eLpNorm w (conjExp Q) Measure.count := by
  -- `Q` and its conjugate `conjExp Q` form a Hölder triple with `1`.
  have htri : ENNReal.HolderTriple Q (conjExp Q) 1 :=
    ⟨by
      rw [inv_one, conjExp, inv_inv]
      exact add_tsub_cancel_of_le (ENNReal.inv_le_one.mpr hQ)⟩
  -- on `ℤ` with the counting measure every function is measurable
  have hm : AEStronglyMeasurable F Measure.count :=
    Measurable.aestronglyMeasurable fun _ _ => trivial
  have hmw : AEStronglyMeasurable w Measure.count :=
    Measurable.aestronglyMeasurable fun _ _ => trivial
  have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := Q) (q := conjExp Q) (r := 1)
    (fun a b : ℂ => a * b) 1 (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) hm hmw (by
      filter_upwards with x
      show ‖F x * w x‖₊ ≤ 1 * ‖F x‖₊ * ‖w x‖₊
      rw [nnnorm_mul, one_mul]) (hpqr := htri)
  simp only [ENNReal.coe_one, one_mul] at hH
  calc ‖∑' x : ℤ, F x * w x‖ₑ ≤ ∑' x : ℤ, ‖F x * w x‖ₑ := enorm_tsum_le_tsum_enorm
    _ = ∫⁻ x : ℤ, ‖F x * w x‖ₑ ∂Measure.count := (lintegral_count _).symm
    _ = eLpNorm (fun x : ℤ => F x * w x) 1 Measure.count := (eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)).symm
    _ ≤ eLpNorm F Q Measure.count * eLpNorm w (conjExp Q) Measure.count := hH

theorem lam_endpoint {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ}
    (hlin₁ : ∀ f f' g (c : ℂ), Work.Analysis.InverseTheory.FinSupp f →
      Work.Analysis.InverseTheory.FinSupp f' → Work.Analysis.InverseTheory.FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    (hlin₂ : ∀ f g g' (c : ℂ), Work.Analysis.InverseTheory.FinSupp f →
      Work.Analysis.InverseTheory.FinSupp g → Work.Analysis.InverseTheory.FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    {r : NNReal} (hr : 1 ≤ r) (psi : ℤ → (ℕ →₀ ℂ))
    (hpsi : ∀ (x : ℤ) (a : ℕ → ℂ),
      ENNReal.ofReal ‖Work.KMTAreas.pair a (psi x)‖ ≤ PointwiseErgodicTheorems.variationalNorm r a)
    {A B Q : ENNReal} (hQ1 : 1 ≤ Q) {M : NNReal}
    (hT : ∀ f g : ℤ → ℂ, Work.Analysis.InverseTheory.FinSupp f → Work.Analysis.InverseTheory.FinSupp g →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T f g n x)) Q
          MeasureTheory.Measure.count
        ≤ (M : ENNReal) * MeasureTheory.eLpNorm f A MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g B MeasureTheory.Measure.count) :
    ∀ u v w : ℤ → ℂ, ‖Work.KMTAreas.lam T psi u v w‖ₑ
      ≤ (M : ENNReal) * MeasureTheory.eLpNorm u A MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm v B MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm w (Work.KMTAreas.conjExp Q) MeasureTheory.Measure.count := by
  intro u v w
  by_cases h : FinSupp u ∧ FinSupp v ∧ FinSupp w
  · obtain ⟨hu, hv, hw⟩ := h
    rw [lam_of_finSupp hu hv hw]
    -- the pointwise domination of the pairing by the variational norm
    have hpt : ∀ x : ℤ, ‖pair (fun n : ℕ => T u v n x) (psi x)‖ₑ
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T u v n x) := by
      intro x
      simpa only [ofReal_norm] using hpsi x (fun n : ℕ => T u v n x)
    -- hence the `ℒ^Q` comparison of the two image functions
    have hFle : eLpNorm (fun x : ℤ => pair (fun n : ℕ => T u v n x) (psi x)) Q Measure.count
        ≤ eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => T u v n x)) Q Measure.count :=
      eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by simpa using hpt x
    calc ‖∑' x : ℤ, pair (fun n : ℕ => T u v n x) (psi x) * w x‖ₑ
        ≤ eLpNorm (fun x : ℤ => pair (fun n : ℕ => T u v n x) (psi x)) Q Measure.count
            * eLpNorm w (conjExp Q) Measure.count := enorm_tsum_mul_le hQ1
      _ ≤ eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => T u v n x)) Q Measure.count
            * eLpNorm w (conjExp Q) Measure.count := by gcongr
      _ ≤ ((M : ENNReal) * eLpNorm u A Measure.count * eLpNorm v B Measure.count)
            * eLpNorm w (conjExp Q) Measure.count := by
            gcongr
            exact hT u v hu hv
  · rw [lam_of_not_finSupp h]
    simp

end Work.KMTAreas.A8
