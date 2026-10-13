import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.Loj

set_option autoImplicit false
open Classical Topology Filter
open scoped Topology
open WilkiesDesign.E

/-- Monotonicity of `Polynomial.eval : ℕ → ℕ` (all coefficients are natural numbers). -/
theorem polynomial_eval_le_eval {p : Polynomial ℕ} {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- The zero EA polynomial evaluates to zero at every complex point. -/
theorem eaEvalC_zeroL {k r : ℕ} (c : EAChain k r) (z : Fin k → ℂ) :
    Work.WilE3.eaEvalC c (0 : EAPoly k r) z = 0 := by
  simp [Work.WilE3.eaEvalC, MvPolynomial.eval₂_zero]

/-- The symbolic derivative `eaD` kills the zero EA polynomial. -/
theorem eaD_zeroL {k r : ℕ} (c : EAChain k r) (i : Fin k) :
    eaD c i (0 : EAPoly k r) = 0 := by
  simp [eaD]

/-- **`MultiplicityBound` in "zeros converging to a point" form.**  For a square EA system `P` with
`P x = 0` and any radius function `ρ ε → 0`, the number of *nondegenerate* zeros of `P` in the
`ρ ε`-ball around `x` is eventually bounded by a polynomial in the atom degrees.  (Obtained from
`MultiplicityBound` with the deformation `g := 0`, absorbing the `atomDeg 0 = 1` summand of the
bound into the polynomial.) -/
theorem multBound_converging (hMB : Work.WilE3.MultiplicityBound) (F : ℕ) :
    ∃ M : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (P : Fin k → EAPoly k r) (x : Fin k → ℂ),
      k + r ≤ F → (∀ i, Work.WilE3.eaEvalC c (P i) x = 0) →
      ∀ ρ : ℂ → ℝ, (∀ ε, 0 < ρ ε) → Tendsto ρ (𝓝[≠] (0 : ℂ)) (𝓝 0) →
      ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ∀ s : Finset (Fin k → ℂ),
        (∀ z ∈ s, (∀ i, Work.WilE3.eaEvalC c (P i) z = 0) ∧
          (Matrix.of fun i j => Work.WilE3.eaEvalC c (eaD c j (P i)) z).det ≠ 0) →
        (∀ z ∈ s, ‖z - x‖ < ρ ε) →
        s.card ≤ M.eval (∑ i, atomDeg (P i)) := by
  obtain ⟨M0, hcount⟩ := hMB F
  -- Absorb the `k` extra degree units (`∑ᵢ atomDeg 0 = k ≤ F`) into the polynomial
  -- `M0` by substituting `X ↦ X + F`.
  refine ⟨M0.comp (Polynomial.X + Polynomial.C F), ?_⟩
  intro k r c P x hkr hx ρ hρpos hρtend
  -- Apply the multiplicity bound with the trivial deformation `g := 0`.
  filter_upwards [hcount k r c P (fun _ => (0 : EAPoly k r)) x ρ hkr hx hρpos hρtend]
    with ε hε
  intro s hs hball
  refine le_trans (hε s ?hcond hball) ?hbound
  case hcond =>
    -- The `g = 0` hypotheses of the multiplicity bound are the hypotheses at hand.
    intro z hz
    refine ⟨fun i => ?_, ?_⟩
    · simpa [eaEvalC_zeroL] using (hs z hz).1 i
    · have hmat : (Matrix.of fun i j => Work.WilE3.eaEvalC c (eaD c j (P i)) z +
            ε * Work.WilE3.eaEvalC c (eaD c j ((fun _ => (0 : EAPoly k r)) i)) z)
          = Matrix.of (fun i j => Work.WilE3.eaEvalC c (eaD c j (P i)) z) := by
        ext i j
        simp [eaD_zeroL, eaEvalC_zeroL]
      rw [hmat]
      exact (hs z hz).2
  case hbound =>
    -- `M0.eval (D + k) ≤ M0.eval (D + F) = (M0.comp (X + C F)).eval D`.
    have hk : k ≤ F := by omega
    have hsum : (∑ i : Fin k, atomDeg ((fun _ => (0 : EAPoly k r)) i)) = k := by
      simp [atomDeg, MvPolynomial.totalDegree_zero]
    rw [hsum]
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact polynomial_eval_le_eval (by omega)

end Work.WilE3.Loj
