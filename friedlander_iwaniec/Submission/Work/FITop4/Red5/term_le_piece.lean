import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.pieceDefs
import Submission.Work.FITop4.Red5.angular_partition_le

namespace Work.FITop4.Red5

attribute [local instance] Classical.propDecidable

/-- **The indicator inequality behind `term_le_piece`.**

If both mollifier factors are non-zero at `z` (so that, by the support conditions, `z` really lies in
the polar cell `(Pa, φ)`), then the difference of the two indicators `QInd - cGInd` is dominated by
twice the "bad indicator".  Indeed `QInd - cGInd ∈ {0, 1}` (the only non-zero case being
`QPred ∧ ¬cGPred`); in that case `QPred` gives both the `(n, Π) = 1` clause and `τ(n) ≤ Pa.τ`, so
`pcInd Pa φ z = 1`, while `¬cGPred` together with `N < n` (from `p(n) ≠ 0`) gives `¬goodPred`, i.e.
`badInd = 1`. -/
lemma ind_le_piece {m N x Pz : ℕ} {τ : ℝ} {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ}
    (hPz : Pa.Pz = Pz)
    (ha : (N : ℝ) ≤ Pa.N)
    (hpsup : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hq0z : q 0 = 0)
    (hqsup : ∀ α : ℝ, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ)
    (z : GaussianInt) (hzprim : Work.FIPlan.IsPrimary z)
    (hpn : p ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≠ 0)
    (hqn : q (Complex.arg z.toComplex - φ) ≠ 0) :
    QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z)
      ≤ 2 * badInd m x τ (Work.FIPlan.gnorm z) * pcInd Pa φ z := by
  by_cases hQ : QPred Pz Pa (Work.FIPlan.gnorm z)
  · by_cases hc : cGPred m N x Pz τ (Work.FIPlan.gnorm z)
    · rw [QInd, cGInd, if_pos hQ, if_pos hc]
      have hb : 0 ≤ badInd m x τ (Work.FIPlan.gnorm z) := badInd_nonneg m x τ _
      have hp : 0 ≤ pcInd Pa φ z := pcInd_nonneg Pa φ z
      nlinarith [hb, hp]
    · have hps := hpsup _ hpn
      have hqsp := hqsup _ hqn
      have hNlt : N < Work.FIPlan.gnorm z := by
        have h1 : (N : ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := lt_of_le_of_lt ha hps.1
        exact_mod_cast h1
      have hargne : Complex.arg z.toComplex - φ ≠ 0 := by
        intro h0
        exact hqn (by rw [h0]; exact hq0z)
      have hargpos : 0 < Complex.arg z.toComplex - φ :=
        lt_of_le_of_ne hqsp.1 (Ne.symm hargne)
      have hbox : InPolarBox Pa φ z :=
        ⟨hzprim, hps.1, hps.2, by linarith, by linarith⟩
      have hnsp : NoSmallPrimes Pa z := by
        intro r hr hrle
        exact hQ.1 r hr (by simpa [hPz] using hrle)
      have hpc : pcCond Pa φ z := ⟨hbox, hnsp, hQ.2⟩
      have hgp : ¬ goodPred m x τ (Work.FIPlan.gnorm z) := by
        intro hg
        exact hc ⟨hg.1, hNlt, hg.2.1, hQ.1, hg.2.2⟩
      rw [QInd, if_pos hQ, cGInd, if_neg hc, badInd, if_neg hgp, pcInd, if_pos hpc]
      norm_num
  · rw [QInd, if_neg hQ]
    have h1 : (0 : ℝ) ≤ cGInd m N x Pz τ (Work.FIPlan.gnorm z) := cGInd_nonneg m N x Pz τ _
    have hb : 0 ≤ badInd m x τ (Work.FIPlan.gnorm z) := badInd_nonneg m x τ _
    have hp : 0 ≤ pcInd Pa φ z := pcInd_nonneg Pa φ z
    have h2 : (0 : ℝ) ≤ 2 * badInd m x τ (Work.FIPlan.gnorm z) * pcInd Pa φ z :=
      mul_nonneg (mul_nonneg (by norm_num) hb) hp
    linarith

theorem term_le_piece {m N x Pz : ℕ} {τ : ℝ} {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ}
    (hPz : Pa.Pz = Pz)
    (hPatau : ∀ n : ℕ, n ≤ 2 * N → (((n.divisors.card : ℕ) : ℝ) ≤ τ) →
      (((n.divisors.card : ℕ) : ℝ) ≤ Pa.τ))
    (ha : (N : ℝ) ≤ Pa.N)
    (hpsup : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hq0z : q 0 = 0)
    (hqsup : ∀ α : ℝ, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ)
    (hp0 : ∀ u : ℝ, 0 ≤ p u) (hq0 : ∀ α : ℝ, 0 ≤ q α)
    (z : GaussianInt) (hz : z ∈ primAnn (2 * N)) (w : GaussianInt) :
    (QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
        * q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
      ≤ 2 * badInd m x τ (Work.FIPlan.gnorm z)
        * ‖pieceCoeff Pa φ q p z * Work.FITop3.Zc w z‖ := by
  -- `z` lies in the primary annulus, so it is primary.
  have hzmem := hz
  simp only [primAnn, Finset.mem_filter] at hzmem
  obtain ⟨_, hzprim⟩ := hzmem
  -- elementary nonnegativity
  have hqnn : 0 ≤ q (Complex.arg z.toComplex - φ) := hq0 _
  have hpnn : 0 ≤ p ((Work.FIPlan.gnorm z : ℕ) : ℝ) := hp0 _
  have hAnn : 0 ≤ q (Complex.arg z.toComplex - φ) * p ((Work.FIPlan.gnorm z : ℕ) : ℝ)
      * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
      * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| :=
    mul_nonneg (mul_nonneg (mul_nonneg hqnn hpnn) (abs_nonneg _)) (abs_nonneg _)
  have hZnn : 0 ≤ (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := Zint_nonneg _
  -- replace the norm of the cell summand by the explicit real expression
  rw [norm_pieceCoeff_mul_Zc Pa φ q p w z, abs_cfVal Pa φ q p z hqnn hpnn]
  -- the indicator inequality, turned into an inequality of products
  have hQK_b : (QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
        * (q (Complex.arg z.toComplex - φ) * p ((Work.FIPlan.gnorm z : ℕ) : ℝ)
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|)
      ≤ (2 * badInd m x τ (Work.FIPlan.gnorm z) * pcInd Pa φ z)
        * (q (Complex.arg z.toComplex - φ) * p ((Work.FIPlan.gnorm z : ℕ) : ℝ)
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|) := by
    by_cases hA : q (Complex.arg z.toComplex - φ) * p ((Work.FIPlan.gnorm z : ℕ) : ℝ)
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| = 0
    · rw [hA]; simp
    · have hpn : p ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≠ 0 := fun h => hA (by rw [h]; ring)
      have hqn : q (Complex.arg z.toComplex - φ) ≠ 0 := fun h => hA (by rw [h]; ring)
      exact mul_le_mul_of_nonneg_right
        (ind_le_piece hPz ha hpsup hq0z hqsup z hzprim hpn hqn) hAnn
  calc (QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
          * q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
      = ((QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
          * (q (Complex.arg z.toComplex - φ) * p ((Work.FIPlan.gnorm z : ℕ) : ℝ)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|))
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by ring
    _ ≤ ((2 * badInd m x τ (Work.FIPlan.gnorm z) * pcInd Pa φ z)
          * (q (Complex.arg z.toComplex - φ) * p ((Work.FIPlan.gnorm z : ℕ) : ℝ)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|))
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) :=
        mul_le_mul_of_nonneg_right hQK_b hZnn
    _ = 2 * badInd m x τ (Work.FIPlan.gnorm z)
          * (pcInd Pa φ z
            * (q (Complex.arg z.toComplex - φ) * p ((Work.FIPlan.gnorm z : ℕ) : ℝ)
              * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
              * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by ring

end Work.FITop4.Red5
