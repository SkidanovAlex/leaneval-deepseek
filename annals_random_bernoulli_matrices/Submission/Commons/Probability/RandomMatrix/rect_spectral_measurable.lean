import Mathlib
import Submission.Commons.Probability.RandomMatrix.spectral_norm_bounded_entries
import Submission.Commons.Probability.RandomMatrix.measurable_opNorm_clm
import Submission.Commons.Probability.RandomMatrix.rect_spectral_norm_bounded_entries

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory ProbabilityTheory Matrix

namespace Commons.Probability.RandomMatrix

/-- Measurable-event version of `rect_spectral_norm_bounded_entries`:
for a rectangular (n−1)×n random matrix with independent, measurable, bounded,
zero-mean entries there is a MEASURABLE set `G` of probability at least
`1 − exp(−Ln)` on which the rectangular `∀ x` spectral bound holds with a
universal scale `C·K·√n`. -/
theorem rect_spectral_measurable :
    ∀ (L : ℝ), 1 ≤ L → ∀ (K : ℝ), 1 ≤ K →
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (A : Ω → Fin (n - 1) → Fin n → ℝ),
          (∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (fun ω => A ω k j)) →
          (ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => (A · kj.1 kj.2)) P) →
          (∀ (k : Fin (n - 1)) (j : Fin n) (ω : Ω), |A ω k j| ≤ K) →
          (∀ k : Fin (n - 1), ∀ j : Fin n, ∫ ω, A ω k j ∂P = 0) →
          ∃ G : Set Ω,
            MeasurableSet G ∧
            P.real G ≥ 1 - Real.exp (-L * (n : ℝ)) ∧
            G ⊆ {ω : Ω |
              ∀ x : Fin n → ℝ,
                (∑ k : Fin (n - 1), ((∑ j : Fin n, A ω k j * x j))^2) ≤
                  (C * K * Real.sqrt (n : ℝ))^2 * (∑ i : Fin n, (x i)^2)} := by
  classical
  intro L hL1 K hK1
  obtain ⟨Csq, hCsq1, hsquare⟩ := spectral_norm_bounded_entries L hL1 K hK1
  refine ⟨Csq, hCsq1, ?_⟩
  intro n hn Ω _ P _ A hmeasA hindA hbA hmeanA
  let B : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => RectPad.padMat hn (fun k j => A ω k j)
  have hK0 : 0 ≤ K := by linarith
  -- measurability of the padded entries
  have hmeasB : ∀ i j : Fin n, Measurable (fun ω => B ω i j) := by
    intro i j
    by_cases hi : i = RectPad.rectLast hn
    · have hc : (fun ω => B ω i j) = fun ω => (0 : ℝ) := by
        funext ω
        dsimp [B]
        simp [RectPad.padMat, hi]
      rw [hc]
      exact measurable_const
    · have hc : (fun ω => B ω i j) = fun ω => A ω (RectPad.rectBack hn i hi) j := by
        funext ω
        dsimp [B]
        simp [RectPad.padMat, hi]
      rw [hc]
      exact hmeasA (RectPad.rectBack hn i hi) j
  -- boundedness of the padded entries
  have hbB : ∀ (i j : Fin n) (ω : Ω), |B ω i j| ≤ K := by
    intro i j ω
    by_cases hi : i = RectPad.rectLast hn
    · have hc : B ω i j = 0 := by
        dsimp [B]
        simp [RectPad.padMat, hi]
      rw [hc]
      simpa using hK0
    · have hc : B ω i j = A ω (RectPad.rectBack hn i hi) j := by
        dsimp [B]
        simp [RectPad.padMat, hi]
      rw [hc]
      exact hbA (RectPad.rectBack hn i hi) j ω
  -- zero mean of the padded entries
  have hmeanB : ∀ i j : Fin n, ∫ ω, B ω i j ∂P = 0 := by
    intro i j
    by_cases hi : i = RectPad.rectLast hn
    · calc
        ∫ ω, B ω i j ∂P = ∫ ω, (0 : ℝ) ∂P := by
          congr
          funext ω
          dsimp [B]
          simp [RectPad.padMat, hi]
        _ = 0 := by simp
    · calc
        ∫ ω, B ω i j ∂P = ∫ ω, A ω (RectPad.rectBack hn i hi) j ∂P := by
          congr
          funext ω
          dsimp [B]
          simp [RectPad.padMat, hi]
        _ = 0 := hmeanA (RectPad.rectBack hn i hi) j
  -- independence of the padded entries
  have hindB : ProbabilityTheory.iIndepFun
      (fun ij : Fin n × Fin n => (B · ij.1 ij.2)) P := by
    classical
    let φ : (Fin (n - 1) × Fin n) ⊕ (PUnit × Fin n) ≃ Fin n × Fin n :=
      (Equiv.sumProdDistrib (Fin (n - 1)) PUnit (Fin n)).symm.trans
        ((RectPad.rectEquiv hn).symm.prodCongr (Equiv.refl (Fin n)))
    let X : Fin (n - 1) × Fin n → Ω → ℝ := fun p => (A · p.1 p.2)
    let FJ : (Fin (n - 1) × Fin n) ⊕ (PUnit × Fin n) → Ω → ℝ :=
      fun s => Sum.elim X (fun _ : PUnit × Fin n => fun _ : Ω => (0 : ℝ)) s
    let Y : Fin n × Fin n → Ω → ℝ := fun ij => (B · ij.1 ij.2)
    have hFJ : ProbabilityTheory.iIndepFun FJ P := by
      simpa [FJ, X] using (Commons.Probability.Independence.iIndepFun_elim_const P
        (fun p : Fin (n - 1) × Fin n => (A · p.1 p.2)) hindA)
    have hZ : (fun s : (Fin (n - 1) × Fin n) ⊕ (PUnit × Fin n) => Y (φ s)) = FJ := by
      funext s
      cases s with
      | inl p =>
        rcases p with ⟨k, j⟩
        simp [Y, FJ, X, φ]
        funext ω
        dsimp [B]
        rw [RectPad.padMat_rectRow]
      | inr p =>
        rcases p with ⟨q, j⟩
        simp [Y, FJ, X, φ]
        funext ω
        dsimp [B]
        rw [RectPad.padMat_rectLast]
    have hZind : ProbabilityTheory.iIndepFun (fun s : (Fin (n - 1) × Fin n) ⊕ (PUnit × Fin n) =>
        Y (φ s)) P := by
      rw [hZ]
      exact hFJ
    simpa [Y] using (ProbabilityTheory.iIndepFun.of_precomp
      (g := (φ : (Fin (n - 1) × Fin n) ⊕ (PUnit × Fin n) → Fin n × Fin n))
      (by exact φ.bijective.surjective) hZind)
  -- apply the square theorem to the padded matrix
  let θ : ℝ := Csq * K * Real.sqrt (n : ℝ)
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    positivity
  have htailB := hsquare n (Ω := Ω) (P := P) B hmeasB hindB hbB hmeanB
  let bad : Set Ω := {ω | ‖((B ω).toEuclideanLin).toContinuousLinearMap‖ > θ}
  have htail : P.real bad ≤ Real.exp (-L * (n : ℝ)) := by
    simpa [bad, θ] using htailB
  -- measurability of the bad event and of the good set G := badᶜ
  have hbad_meas : MeasurableSet bad := by
    dsimp [bad]
    exact measurable_opNorm_clm B hmeasB (measurableSet_Ioi : MeasurableSet (Set.Ioi θ))
  let G : Set Ω := badᶜ
  have hG_meas : MeasurableSet G := by
    dsimp [G]
    exact hbad_meas.compl
  -- probability comparison
  have hG_ge : 1 - Real.exp (-L * (n : ℝ)) ≤ P.real G := by
    have hsum := MeasureTheory.measureReal_add_measureReal_compl (μ := P) (s := bad) hbad_meas
    have huniv : P.real Set.univ = 1 := by
      simp [Measure.real]
    have hsum' : P.real bad + P.real G = 1 := by
      dsimp [G]
      rw [hsum, huniv]
    dsimp [G]
    nlinarith [htail, hsum']
  -- on the good event the rectangular inequality holds for every x
  have hG_sub : G ⊆
      {ω : Ω | ∀ x : Fin n → ℝ,
        (∑ k : Fin (n - 1), ((∑ j : Fin n, A ω k j * x j))^2) ≤
          (Csq * K * Real.sqrt (n : ℝ))^2 * (∑ i : Fin n, (x i)^2)} := by
    intro ω hω x
    have hop : ‖((B ω).toEuclideanLin).toContinuousLinearMap‖ ≤ θ := by
      exact le_of_not_gt (by simpa [G, bad] using hω)
    let u : E n := WithLp.toLp 2 x
    have hsqnorm : ‖((B ω).toEuclideanLin).toContinuousLinearMap u‖ ^ 2
        = (∑ k : Fin (n - 1), (∑ j : Fin n, A ω k j * x j)^2) := by
      calc
        ‖((B ω).toEuclideanLin).toContinuousLinearMap u‖ ^ 2
            = ∑ i : Fin n, (∑ j : Fin n, (B ω) i j * x j)^2 := by
              rw [sq_norm_ofLp]
              apply Finset.sum_congr rfl
              intro i hi
              congr 1
        _ = (∑ k : Fin (n - 1), (∑ j : Fin n, A ω k j * x j)^2) := by
              have hBpad : (B ω) = RectPad.padMat hn (fun k j => A ω k j) := by
                simp [B]
              rw [hBpad]
              exact RectPad.padMat_row_sq_sum hn (fun k j => A ω k j) x
    have hop_le : ‖((B ω).toEuclideanLin).toContinuousLinearMap u‖ ≤ θ * ‖u‖ := by
      calc
        ‖((B ω).toEuclideanLin).toContinuousLinearMap u‖
            ≤ ‖((B ω).toEuclideanLin).toContinuousLinearMap‖ * ‖u‖ :=
              ContinuousLinearMap.le_opNorm (((B ω).toEuclideanLin).toContinuousLinearMap) u
        _ ≤ θ * ‖u‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg u)
    have hfac : 0 ≤ (θ * ‖u‖ - ‖((B ω).toEuclideanLin).toContinuousLinearMap u‖) *
        (θ * ‖u‖ + ‖((B ω).toEuclideanLin).toContinuousLinearMap u‖) := by
      exact mul_nonneg (sub_nonneg.mpr hop_le)
        (add_nonneg (mul_nonneg hθ0 (norm_nonneg u)) (norm_nonneg _))
    have hsq : ‖((B ω).toEuclideanLin).toContinuousLinearMap u‖ ^ 2 ≤ (θ * ‖u‖) ^ 2 := by
      nlinarith [hfac]
    have hu_norm : ‖u‖ ^ 2 = ∑ i : Fin n, (x i)^2 := by
      rw [sq_norm_ofLp]
    calc
      (∑ k : Fin (n - 1), (∑ j : Fin n, A ω k j * x j)^2)
          = ‖((B ω).toEuclideanLin).toContinuousLinearMap u‖ ^ 2 := hsqnorm.symm
      _ ≤ (θ * ‖u‖) ^ 2 := hsq
      _ = θ ^ 2 * ‖u‖ ^ 2 := by ring
      _ = (Csq * K * Real.sqrt (n : ℝ))^2 * (∑ i : Fin n, (x i)^2) := by
        dsimp [θ]
        rw [hu_norm]
  -- finish
  refine ⟨G, hG_meas, hG_ge, ?_⟩
  intro ω hω
  exact hG_sub hω

end Commons.Probability.RandomMatrix
