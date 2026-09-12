import Mathlib
import Submission.Commons.Probability.RandomMatrix.spectral_norm_bounded_entries
import Submission.Commons.Probability.RandomMatrix.measurable_opNorm_clm
import Submission.Commons.Probability.Independence.iIndepFun_elim_const

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory ProbabilityTheory Matrix

namespace Commons.Probability.RandomMatrix

/-! ### Finite-index glue: rows `Fin (n - 1)` embedded into `Fin n` (last row left out) -/

namespace RectPad

noncomputable section

def rectRow {n : ℕ} (hn : 1 ≤ n) (k : Fin (n - 1)) : Fin n :=
  ⟨k.1, by omega⟩

def rectLast {n : ℕ} (hn : 1 ≤ n) : Fin n :=
  ⟨n - 1, by omega⟩

def rectBack {n : ℕ} (hn : 1 ≤ n) (i : Fin n) (hi : i ≠ rectLast hn) : Fin (n - 1) :=
  ⟨i.1, by
    have hne : i.1 ≠ n - 1 := by
      intro hh
      apply hi
      apply Fin.ext
      simpa [rectLast] using hh
    omega⟩

lemma rectRow_ne_rectLast {n : ℕ} (hn : 1 ≤ n) (k : Fin (n - 1)) : rectRow hn k ≠ rectLast hn := by
  intro h
  have hv := congrArg Fin.val h
  simp [rectRow, rectLast] at hv
  omega

/-- Equivalence between `Fin n` and `Fin (n - 1) ⊕ PUnit`, sending the last row to `PUnit`
and the embedded rows to the left component. -/
def rectEquiv {n : ℕ} (hn : 1 ≤ n) : Fin n ≃ Fin (n - 1) ⊕ PUnit where
  toFun := fun i => if h : i = rectLast hn then Sum.inr () else Sum.inl ⟨i.1, by
      have hne : i.1 ≠ n - 1 := by
        intro hh
        apply h
        apply Fin.ext
        simpa [rectLast] using hh
      omega⟩
  invFun := fun s => Sum.elim (rectRow hn) (fun _ => rectLast hn) s
  left_inv := by
    intro i
    by_cases hi : i = rectLast hn
    · simp [hi]
    · simp [hi]
      apply Fin.ext
      simp [rectRow]
  right_inv := by
    intro s
    cases s with
    | inl k =>
      have hne : ¬ ⟨k.1, (by omega : k.1 < n)⟩ = rectLast hn := by
        intro hh
        have hv := congrArg Fin.val hh
        simp [rectLast] at hv
        omega
      simp [rectRow, hne]
    | inr u =>
      simp

@[simp] lemma rectEquiv_symm_inl {n : ℕ} (hn : 1 ≤ n) (k : Fin (n - 1)) :
    (rectEquiv hn).symm (Sum.inl k) = rectRow hn k := by
  simp [rectEquiv]

@[simp] lemma rectEquiv_symm_inr {n : ℕ} (hn : 1 ≤ n) (u : PUnit) :
    (rectEquiv hn).symm (Sum.inr u) = rectLast hn := by
  simp [rectEquiv]

/-- `padMat hn A` is the `n × n` matrix obtained by appending a zero row at the bottom
to the `(n - 1) × n` matrix `A`.  Rows are embedded through `rectRow`, the extra row is
`rectLast`. -/
def padMat {n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : i = rectLast hn then 0 else A (rectBack hn i h) j

lemma padMat_of_ne {n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → Fin n → ℝ)
    {i : Fin n} (hi : i ≠ rectLast hn) (j : Fin n) :
    padMat hn A i j = A (rectBack hn i hi) j := by
  simp [padMat, hi]

lemma padMat_rectLast {n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → Fin n → ℝ) (j : Fin n) :
    padMat hn A (rectLast hn) j = 0 := by
  simp [padMat]

lemma rectBack_rectRow {n : ℕ} (hn : 1 ≤ n) (k : Fin (n - 1)) :
    rectBack hn (rectRow hn k) (rectRow_ne_rectLast hn k) = k := by
  apply Fin.ext
  simp [rectBack, rectRow]

lemma padMat_rectRow {n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → Fin n → ℝ) (k : Fin (n - 1)) (j : Fin n) :
    padMat hn A (rectRow hn k) j = A k j := by
  rw [padMat_of_ne hn A (rectRow_ne_rectLast hn k) j]
  congr 1

/-- Splitting a sum over `Fin n` into the embedded rows plus the last row. -/
lemma sum_split_rect {n : ℕ} (hn : 1 ≤ n) (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) =
      (∑ k : Fin (n - 1), f (rectRow hn k)) + f (rectLast hn) := by
  classical
  let e : Fin n ≃ Fin (n - 1) ⊕ PUnit := {
    toFun := fun i => if h : i = rectLast hn then Sum.inr () else Sum.inl ⟨i.1, by
        have hne : i.1 ≠ n - 1 := by
          intro hh
          apply h
          apply Fin.ext
          simpa [rectLast] using hh
        omega⟩
    invFun := fun s => Sum.elim (rectRow hn) (fun _ => rectLast hn) s
    left_inv := by
      intro i
      by_cases hi : i = rectLast hn
      · simp [hi]
      · simp [hi]
        apply Fin.ext
        simp [rectRow]
    right_inv := by
      intro s
      cases s with
      | inl k =>
        have hne : ¬ ⟨k.1, (by omega : k.1 < n)⟩ = rectLast hn := by
          intro hh
          have hv := congrArg Fin.val hh
          simp [rectLast] at hv
          omega
        simp [rectRow, hne]
      | inr u =>
        simp }
  calc
    (∑ i : Fin n, f i) = ∑ s : Fin (n - 1) ⊕ PUnit, f (e.symm s) := by
      rw [← Equiv.sum_comp e.symm f]
    _ = (∑ k : Fin (n - 1), f (e.symm (Sum.inl k))) +
        ∑ q : PUnit, f (e.symm (Sum.inr q)) := by
      simp [Fintype.sum_sum_type]
    _ = (∑ k : Fin (n - 1), f (rectRow hn k)) + f (rectLast hn) := by
      simp [e]

/-- Sum of squares of the rows of `padMat A` (an `n`-row matrix with a zero last row)
equals the sum of squares of the rows of `A`. -/
lemma padMat_row_sq_sum {n : ℕ} (hn : 1 ≤ n) (A : Fin (n - 1) → Fin n → ℝ) (u : Fin n → ℝ) :
    (∑ i : Fin n, (∑ j : Fin n, padMat hn A i j * u j)^2)
      = (∑ k : Fin (n - 1), (∑ j : Fin n, A k j * u j)^2) := by
  classical
  rw [sum_split_rect hn (fun i => (∑ j : Fin n, padMat hn A i j * u j)^2)]
  have hlast : (∑ j : Fin n, padMat hn A (rectLast hn) j * u j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [padMat_rectLast]
    ring
  rw [hlast]
  norm_num
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [padMat_rectRow]

end
end RectPad

open RectPad

/-! ### Main theorem -/

theorem rect_spectral_norm_bounded_entries :
    ∀ (L : ℝ), 1 ≤ L → ∀ (K : ℝ), 1 ≤ K →
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (A : Ω → Fin (n - 1) → Fin n → ℝ),
          (∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (fun ω => A ω k j)) →
          (ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => (A · kj.1 kj.2)) P) →
          (∀ (k : Fin (n - 1)) (j : Fin n) (ω : Ω), |A ω k j| ≤ K) →
          (∀ k : Fin (n - 1), ∀ j : Fin n, ∫ ω, A ω k j ∂P = 0) →
          P.real {ω : Ω |
            ∀ x : Fin n → ℝ,
              (∑ k : Fin (n - 1), ((∑ j : Fin n, A ω k j * x j))^2) ≤
                (C * K * Real.sqrt (n : ℝ))^2 * (∑ i : Fin n, (x i)^2)} ≥
            1 - Real.exp (-L * (n : ℝ)) := by
  classical
  intro L hL1 K hK1
  obtain ⟨Csq, hCsq1, hsquare⟩ := spectral_norm_bounded_entries L hL1 K hK1
  refine ⟨Csq, hCsq1, ?_⟩
  intro n hn Ω _ P _ A hmeasA hindA hbA hmeanA
  let B : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => padMat hn (fun k j => A ω k j)
  have hK0 : 0 ≤ K := by linarith
  -- measurability of the padded entries
  have hmeasB : ∀ i j : Fin n, Measurable (fun ω => B ω i j) := by
    intro i j
    by_cases hi : i = rectLast hn
    · have hc : (fun ω => B ω i j) = fun ω => (0 : ℝ) := by
        funext ω
        dsimp [B]
        simp [padMat, hi]
      rw [hc]
      exact measurable_const
    · have hc : (fun ω => B ω i j) = fun ω => A ω (rectBack hn i hi) j := by
        funext ω
        dsimp [B]
        simp [padMat, hi]
      rw [hc]
      exact hmeasA (rectBack hn i hi) j
  -- boundedness of the padded entries
  have hbB : ∀ (i j : Fin n) (ω : Ω), |B ω i j| ≤ K := by
    intro i j ω
    by_cases hi : i = rectLast hn
    · have hc : B ω i j = 0 := by
        dsimp [B]
        simp [padMat, hi]
      rw [hc]
      simpa using hK0
    · have hc : B ω i j = A ω (rectBack hn i hi) j := by
        dsimp [B]
        simp [padMat, hi]
      rw [hc]
      exact hbA (rectBack hn i hi) j ω
  -- zero mean of the padded entries
  have hmeanB : ∀ i j : Fin n, ∫ ω, B ω i j ∂P = 0 := by
    intro i j
    by_cases hi : i = rectLast hn
    · calc
        ∫ ω, B ω i j ∂P = ∫ ω, (0 : ℝ) ∂P := by
          congr
          funext ω
          dsimp [B]
          simp [padMat, hi]
        _ = 0 := by simp
    · calc
        ∫ ω, B ω i j ∂P = ∫ ω, A ω (rectBack hn i hi) j ∂P := by
          congr
          funext ω
          dsimp [B]
          simp [padMat, hi]
        _ = 0 := hmeanA (rectBack hn i hi) j
  -- independence of the padded entries
  have hindB : ProbabilityTheory.iIndepFun
      (fun ij : Fin n × Fin n => (B · ij.1 ij.2)) P := by
    classical
    let φ : (Fin (n - 1) × Fin n) ⊕ (PUnit × Fin n) ≃ Fin n × Fin n :=
      (Equiv.sumProdDistrib (Fin (n - 1)) PUnit (Fin n)).symm.trans
        ((rectEquiv hn).symm.prodCongr (Equiv.refl (Fin n)))
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
        rw [padMat_rectRow]
      | inr p =>
        rcases p with ⟨q, j⟩
        simp [Y, FJ, X, φ]
        funext ω
        dsimp [B]
        rw [padMat_rectLast]
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
  -- measurability of the bad event and the good event
  have hbad_meas : MeasurableSet bad := by
    dsimp [bad]
    exact measurable_opNorm_clm B hmeasB (measurableSet_Ioi : MeasurableSet (Set.Ioi θ))
  have hgood_meas : MeasurableSet (badᶜ) := hbad_meas.compl
  -- probability comparison
  have hgood_ge : 1 - Real.exp (-L * (n : ℝ)) ≤ P.real (badᶜ) := by
    have hsum := MeasureTheory.measureReal_add_measureReal_compl (μ := P) (s := bad) hbad_meas
    have huniv : P.real Set.univ = 1 := by
      simp [Measure.real]
    have hsum' : P.real bad + P.real (badᶜ) = 1 := by
      rw [hsum, huniv]
    nlinarith [htail, hsum']
  -- on the good event the rectangular inequality holds for every x
  have hcont : badᶜ ⊆
      {ω : Ω | ∀ x : Fin n → ℝ,
        (∑ k : Fin (n - 1), ((∑ j : Fin n, A ω k j * x j))^2) ≤
          (Csq * K * Real.sqrt (n : ℝ))^2 * (∑ i : Fin n, (x i)^2)} := by
    intro ω hω x
    have hop : ‖((B ω).toEuclideanLin).toContinuousLinearMap‖ ≤ θ := by
      exact le_of_not_gt hω
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
              have hBpad : (B ω) = padMat hn (fun k j => A ω k j) := by
                simp [B]
              rw [hBpad]
              exact padMat_row_sq_sum hn (fun k j => A ω k j) x
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
  calc
    P.real {ω : Ω |
        ∀ x : Fin n → ℝ,
          (∑ k : Fin (n - 1), ((∑ j : Fin n, A ω k j * x j))^2) ≤
            (Csq * K * Real.sqrt (n : ℝ))^2 * (∑ i : Fin n, (x i)^2)}
        ≥ P.real (badᶜ) := by
          exact MeasureTheory.measureReal_mono (s₁ := badᶜ)
            (s₂ := {ω : Ω | ∀ x : Fin n → ℝ,
              (∑ k : Fin (n - 1), ((∑ j : Fin n, A ω k j * x j))^2) ≤
                (Csq * K * Real.sqrt (n : ℝ))^2 * (∑ i : Fin n, (x i)^2)}) hcont
    _ ≥ 1 - Real.exp (-L * (n : ℝ)) := hgood_ge

end Commons.Probability.RandomMatrix
