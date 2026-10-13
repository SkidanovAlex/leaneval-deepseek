import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Loj.multBound_converging

/-!
  annals_wilkies_conjecture, AREA E3: the multiplicity count in the degree form the polar argument
  needs.

  The Łojasiewicz argument (see `NOTES_hasLoj_of_multiplicity.md`) bounds the growth of the sphere
  minima `μ (ρ) = min {Φ : dist (·, y) = ρ}` by the number of nondegenerate complex zeros,
  converging to `y`, of the *square* polar system `{Φ - ε = 0, minors = 0}`.  That count is provided
  by `Work.WilE3.MultiplicityBound`; this file packages it in the "polynomial in `atomDeg Φ` alone"
  form, with the (generous, but bounded) hypothesis that every row of the system has atom degree at
  most `3 * atomDeg Φ + 3` (true for the rows `Φ` and the `k - 1` minors of `∇Φ` against `x - y`,
  whose atom degrees are `≤ 2 * atomDeg Φ + 1`).
-/

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-- **The polar-system count in degree form.**  From `Work.WilE3.MultiplicityBound`: for a square EA
system `P` all of whose rows have atom degree `≤ 3 * atomDeg Φ + 3`, the number of its nondegenerate
complex zeros in a shrinking ball around a zero `x` of `P` is bounded by a polynomial in `atomDeg Φ`
alone, uniformly in the chain and in the system. -/
theorem radialPolar_count (hMB : Work.WilE3.MultiplicityBound) (F : ℕ) :
    ∃ M : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
      (P : Fin k → EAPoly k r) (x : Fin k → ℂ),
      k + r ≤ F →
      (∀ i, Work.WilE3.eaEvalC c (P i) x = 0) →
      (∀ i, atomDeg (P i) ≤ 3 * atomDeg Φ + 3) →
      ∀ ρ : ℂ → ℝ, (∀ ε, 0 < ρ ε) → Filter.Tendsto ρ (𝓝[≠] (0 : ℂ)) (𝓝 0) →
      ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ∀ s : Finset (Fin k → ℂ),
        (∀ z ∈ s, (∀ i, Work.WilE3.eaEvalC c (P i) z = 0) ∧
          (Matrix.of fun i j => Work.WilE3.eaEvalC c (eaD c j (P i)) z).det ≠ 0) →
        (∀ z ∈ s, ‖z - x‖ < ρ ε) →
        s.card ≤ M.eval (atomDeg Φ) := by
  obtain ⟨M0, hM0⟩ := Work.WilE3.Loj.multBound_converging hMB F
  refine ⟨M0.comp (Polynomial.C (3 * F) * Polynomial.X + Polynomial.C (3 * F)), ?_⟩
  intro k r c Φ P x hkr hPx hdeg ρ hρpos hρtend
  filter_upwards [hM0 k r c P x hkr hPx ρ hρpos hρtend] with ε hε
  intro s hs hball
  refine le_trans (hε s hs hball) ?_
  have hkr' : k ≤ F := by omega
  -- the degree sum is at most `F * (3 * atomDeg Φ + 3)`
  have hsum : (∑ i : Fin k, atomDeg (P i)) ≤ F * (3 * atomDeg Φ + 3) := by
    calc (∑ i : Fin k, atomDeg (P i)) ≤ ∑ _i : Fin k, (3 * atomDeg Φ + 3) :=
          Finset.sum_le_sum fun i _ => hdeg i
      _ = k * (3 * atomDeg Φ + 3) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ F * (3 * atomDeg Φ + 3) :=
          Nat.mul_le_mul_right _ hkr'
  refine le_trans (Work.WilE3.Loj.polynomial_eval_le_eval hsum) (le_of_eq ?_)
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring_nf

end Work.WilE3.Taylor
