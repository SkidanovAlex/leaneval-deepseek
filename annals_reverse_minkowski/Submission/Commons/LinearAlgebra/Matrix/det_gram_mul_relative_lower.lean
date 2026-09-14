import Mathlib
import Submission.Commons.Analysis.Fourier.sum_sq_le_const_sum_sq_mulVec
import Submission.Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub

open scoped Matrix BigOperators
open Matrix
set_option autoImplicit false

namespace Commons.LinearAlgebra.Matrix

lemma quad_perturb_lower {m : ℕ} (B₀ A : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (x : Fin m → ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεA : (∑ i : Fin m, (((A - B₀).mulVec x) i) ^ 2) ≤
        ε ^ 2 * (∑ i : Fin m, ((B₀.mulVec x) i) ^ 2)) :
    (1 - ε) ^ 2 * (∑ i : Fin m, ((B₀.mulVec x) i) ^ 2) ≤
      ∑ i : Fin m, ((A.mulVec x) i) ^ 2 := by
  classical
  let p : Fin m → ℝ := B₀.mulVec x
  let q : Fin m → ℝ := (A - B₀).mulVec x
  let U : ℝ := ∑ i : Fin m, (p i) ^ 2
  let S : ℝ := ∑ i : Fin m, (q i) ^ 2
  let u : ℝ := Real.sqrt U
  let z : ℝ := Real.sqrt S
  have hU0 : 0 ≤ U := by
    dsimp [U]
    exact Finset.sum_nonneg (fun i hi => sq_nonneg (p i))
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i hi => sq_nonneg (q i))
  have hu0 : 0 ≤ u := by dsimp [u]; exact Real.sqrt_nonneg U
  have hz0 : 0 ≤ z := by dsimp [z]; exact Real.sqrt_nonneg S
  have hU : U = u ^ 2 := by dsimp [u]; exact (Real.sq_sqrt hU0).symm
  have hS : S = z ^ 2 := by dsimp [z]; exact (Real.sq_sqrt hS0).symm
  have hAeq : A = B₀ + (A - B₀) := by
    ext i j
    simp
  have hpadd : A.mulVec x = p + q := by
    dsimp [p, q]
    calc
      A.mulVec x = (B₀ + (A - B₀)).mulVec x := by
        exact congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M.mulVec x) hAeq
      _ = B₀.mulVec x + (A - B₀).mulVec x := by rw [Matrix.add_mulVec]
  have hS_le : S ≤ ε ^ 2 * U := by
    dsimp [S, U, q]
    exact hεA
  have hcs : (∑ i : Fin m, p i * q i) ^ 2 ≤ U * S := by
    dsimp [U, S]
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m)) p q)
  have huz0 : 0 ≤ u * z := mul_nonneg hu0 hz0
  have hcs2 : |∑ i : Fin m, p i * q i| ≤ u * z := by
    have hsq : (∑ i : Fin m, p i * q i) ^ 2 ≤ (u * z) ^ 2 := by
      calc
        (∑ i : Fin m, p i * q i) ^ 2 ≤ U * S := hcs
        _ = (u * z) ^ 2 := by rw [hU, hS]; ring
    simpa [abs_of_nonneg huz0] using (sq_le_sq.mp hsq)
  have hcsl : -(u * z) ≤ ∑ i : Fin m, p i * q i := (abs_le.mp hcs2).1
  have hz2 : z ^ 2 ≤ (ε * u) ^ 2 := by
    calc
      z ^ 2 = S := by dsimp [z]; rw [Real.sq_sqrt hS0]
      _ ≤ ε ^ 2 * U := hS_le
      _ = (ε * u) ^ 2 := by rw [hU]; ring
  have hεu0 : 0 ≤ ε * u := mul_nonneg hε0 hu0
  have hz_le : z ≤ ε * u := by
    have habs : |z| ≤ |ε * u| := sq_le_sq.mp hz2
    rwa [abs_of_nonneg hz0, abs_of_nonneg hεu0] at habs
  have hsum : (∑ i : Fin m, ((A.mulVec x) i) ^ 2) =
      U + S + 2 * (∑ i : Fin m, p i * q i) := by
    rw [hpadd]
    calc
      (∑ i : Fin m, ((p + q) i) ^ 2) = ∑ i : Fin m, ((p i) ^ 2 + 2 * (p i * q i) + (q i) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          change (p i + q i) ^ 2 = (p i) ^ 2 + 2 * (p i * q i) + (q i) ^ 2
          ring
      _ = (∑ i : Fin m, (p i) ^ 2) + (∑ i : Fin m, (q i) ^ 2)
            + 2 * (∑ i : Fin m, p i * q i) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
              ring
      _ = U + S + 2 * (∑ i : Fin m, p i * q i) := by
              dsimp [U, S]
  have hmain2 : (u - z) ^ 2 ≤ (∑ i : Fin m, ((A.mulVec x) i) ^ 2) := by
    rw [hsum]
    have h1eq : (u - z) ^ 2 = U + S - 2 * (u * z) := by
      calc
        (u - z) ^ 2 = u ^ 2 + z ^ 2 - 2 * u * z := by ring
        _ = U + S - 2 * (u * z) := by rw [hU.symm, hS.symm]; ring
    have h1 : (u - z) ^ 2 ≤ U + S - 2 * (u * z) := le_of_eq h1eq
    have h2 : U + S - 2 * (u * z) ≤ U + S + 2 * (∑ i : Fin m, p i * q i) := by
      nlinarith [hcsl]
    exact le_trans h1 h2
  have hge : (1 - ε) ^ 2 * U ≤ (u - z) ^ 2 := by
    have hnonneg : 0 ≤ (1 - ε) * u := by
      exact mul_nonneg (sub_nonneg.mpr (by linarith)) hu0
    have hle2 : (1 - ε) * u ≤ u - z := by
      nlinarith [hz_le]
    have hpow := pow_le_pow_left₀ hnonneg hle2 2
    calc
      (1 - ε) ^ 2 * U = ((1 - ε) * u) ^ 2 := by rw [hU]; ring
      _ ≤ (u - z) ^ 2 := hpow
  calc
    (1 - ε) ^ 2 * (∑ i : Fin m, ((B₀.mulVec x) i) ^ 2) = (1 - ε) ^ 2 * U := by
      dsimp [U, p]
    _ ≤ (u - z) ^ 2 := hge
    _ ≤ ∑ i : Fin m, ((A.mulVec x) i) ^ 2 := hmain2

/-- `x ⬝ᵥ (Mᵀ M x) = Σᵢ (M x)ᵢ²`. -/
lemma dot_gram_sq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ ((M.transpose * M) *ᵥ x) = ∑ i, ((M.mulVec x) i) ^ 2 := by
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  simp [Matrix.vecMul_transpose, dotProduct, Matrix.mulVec, pow_two]

/-- Entrywise closeness: `|A j i - B₀ j i| ≤ δ` with `0 ≤ δ` forces the quadratic
difference estimate `Σ (((A-B₀)x)ᵢ)² ≤ (m δ)² Σ xᵢ²`. -/
lemma sum_sq_mulVec_entrywise_le {m : ℕ} (E : Matrix (Fin m) (Fin m) ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hE : ∀ j i : Fin m, |E j i| ≤ δ) (x : Fin m → ℝ) :
    (∑ j : Fin m, ((E.mulVec x) j) ^ 2) ≤ (m : ℝ) ^ 2 * δ ^ 2 * (∑ i : Fin m, (x i) ^ 2) := by
  have hsumsq : (∑ j : Fin m, ∑ i : Fin m, (E j i) ^ 2) ≤ (m : ℝ) ^ 2 * δ ^ 2 := by
    have hterm : ∀ j i : Fin m, (E j i) ^ 2 ≤ δ ^ 2 := by
      intro j i
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hδ] using hE j i)
    calc
      (∑ j : Fin m, ∑ i : Fin m, (E j i) ^ 2)
          ≤ (∑ j : Fin m, ∑ i : Fin m, δ ^ 2) := by
            exact Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun i hi => hterm j i))
      _ = (m : ℝ) ^ 2 * δ ^ 2 := by
            simp [pow_two]
            ring
  calc
    (∑ j : Fin m, ((E.mulVec x) j) ^ 2)
        ≤ (∑ j : Fin m, ∑ i : Fin m, (E j i) ^ 2) * (∑ k : Fin m, (x k) ^ 2) := by
          exact Commons.Analysis.Fourier.sum_sq_mulVec_le E x
    _ ≤ (m : ℝ) ^ 2 * δ ^ 2 * (∑ i : Fin m, (x i) ^ 2) := by
          exact mul_le_mul_of_nonneg_right hsumsq
            (Finset.sum_nonneg (fun i hi => sq_nonneg (x i)))


/-- Bound on the perturbation quadratic form in terms of `(C δ)² ‖B₀ x‖²`, where the
quadratic lower bound `Σx² ≤ c·Σ(B₀x)²` is available from invertibility of `B₀`. -/
lemma entrywise_diff_sq_le {m : ℕ} (B₀ A : Matrix (Fin m) (Fin m) ℝ) {δ c : ℝ}
    (x : Fin m → ℝ) (hc0 : 0 < c)
    (hc : (∑ i : Fin m, (x i) ^ 2) ≤ c * (∑ i : Fin m, ((B₀.mulVec x) i) ^ 2))
    (hδ0 : 0 ≤ δ) (hE : ∀ j i : Fin m, |A j i - B₀ j i| ≤ δ) :
    (∑ i : Fin m, (((A - B₀).mulVec x) i) ^ 2) ≤
      (((m : ℝ) * (c + 1) + 1) * δ) ^ 2 * (∑ i : Fin m, ((B₀.mulVec x) i) ^ 2) := by
  classical
  let M : ℝ := (m : ℝ)
  let C : ℝ := M * (c + 1) + 1
  let U : ℝ := ∑ i : Fin m, ((B₀.mulVec x) i) ^ 2
  let S : ℝ := ∑ i : Fin m, (((A - B₀).mulVec x) i) ^ 2
  have hU0 : 0 ≤ U := by
    dsimp [U]
    exact Finset.sum_nonneg (fun i hi => sq_nonneg ((B₀.mulVec x) i))
  have hMδ0 : 0 ≤ M ^ 2 * δ ^ 2 := by
    dsimp [M]
    positivity
  have hSW : S ≤ M ^ 2 * δ ^ 2 * (∑ i : Fin m, (x i) ^ 2) := by
    dsimp [S, M]
    exact sum_sq_mulVec_entrywise_le (A - B₀) hδ0 hE x
  have hWU : (∑ i : Fin m, (x i) ^ 2) ≤ c * U := by
    dsimp [U]
    exact hc
  have hSU : S ≤ M ^ 2 * c * (δ ^ 2 * U) := by
    calc
      S ≤ M ^ 2 * δ ^ 2 * (∑ i : Fin m, (x i) ^ 2) := hSW
      _ ≤ M ^ 2 * δ ^ 2 * (c * U) := by
        exact mul_le_mul_of_nonneg_left hWU hMδ0
      _ = M ^ 2 * c * (δ ^ 2 * U) := by ring
  have hc1 : c ≤ (c + 1) ^ 2 := by nlinarith [sq_nonneg (c + 1 / 2)]
  have hM2 : 0 ≤ M ^ 2 := by exact sq_nonneg M
  have hSU1 : S ≤ M ^ 2 * (c + 1) ^ 2 * (δ ^ 2 * U) := by
    calc
      S ≤ M ^ 2 * c * (δ ^ 2 * U) := hSU
      _ ≤ M ^ 2 * (c + 1) ^ 2 * (δ ^ 2 * U) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1 hM2)
          (mul_nonneg (sq_nonneg δ) hU0)
  have hCM : M ^ 2 * (c + 1) ^ 2 ≤ C ^ 2 := by
    dsimp [C, M]
    have ha : 0 ≤ (m : ℝ) * (c + 1) := by
      exact mul_nonneg (Nat.cast_nonneg m) (by linarith)
    nlinarith
  have hSU2 : S ≤ C ^ 2 * (δ ^ 2 * U) := by
    calc
      S ≤ M ^ 2 * (c + 1) ^ 2 * (δ ^ 2 * U) := hSU1
      _ ≤ C ^ 2 * (δ ^ 2 * U) := by
        exact mul_le_mul_of_nonneg_right hCM (mul_nonneg (sq_nonneg δ) hU0)
  calc
    S ≤ C ^ 2 * (δ ^ 2 * U) := hSU2
    _ = (C * δ) ^ 2 * U := by ring
    _ = (((m : ℝ) * (c + 1) + 1) * δ) ^ 2 * (∑ i : Fin m, ((B₀.mulVec x) i) ^ 2) := by
      dsimp [C, M, U]


/-- Dot-product form of `quad_perturb_lower`. -/
lemma quad_perturb_dot {m : ℕ} (B₀ A : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hεA : ∀ x : Fin m → ℝ,
      (∑ i : Fin m, (((A - B₀).mulVec x) i) ^ 2) ≤
        ε ^ 2 * (∑ i : Fin m, ((B₀.mulVec x) i) ^ 2)) :
    ∀ x : Fin m → ℝ,
      (1 - ε) ^ 2 * (x ⬝ᵥ ((B₀.transpose * B₀) *ᵥ x)) ≤
        x ⬝ᵥ ((A.transpose * A) *ᵥ x) := by
  intro x
  rw [dot_gram_sq B₀ x, dot_gram_sq A x]
  exact quad_perturb_lower B₀ A ε x hε0 hε1 (hεA x)

/-- A quadratic-form comparison `t²·xᵀB₀ᵀB₀x ≤ xᵀAᵀAx` for every `x` is equivalent to
positive semidefiniteness of `AᵀA - t²·B₀ᵀB₀`. -/
lemma gram_sub_psd {m : ℕ} (B₀ A : Matrix (Fin m) (Fin m) ℝ) (t : ℝ)
    (hquad : ∀ x : Fin m → ℝ,
      t ^ 2 * (x ⬝ᵥ ((B₀.transpose * B₀) *ᵥ x)) ≤
        x ⬝ᵥ ((A.transpose * A) *ᵥ x)) :
    ((A.transpose * A) - t ^ 2 • (B₀.transpose * B₀)).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?h1 ?h2
  · rw [Matrix.isHermitian_iff_isSymm]
    exact ((Matrix.isSymm_transpose_mul_self A).sub
      ((Matrix.isSymm_transpose_mul_self B₀).smul (t ^ 2)))
  · intro x
    have hexp : x ⬝ᵥ (((A.transpose * A) - t ^ 2 • (B₀.transpose * B₀)) *ᵥ x)
        = x ⬝ᵥ ((A.transpose * A) *ᵥ x)
          - t ^ 2 * (x ⬝ᵥ ((B₀.transpose * B₀) *ᵥ x)) := by
      calc
        x ⬝ᵥ (((A.transpose * A) - (t ^ 2 • (B₀.transpose * B₀))) *ᵥ x)
            = x ⬝ᵥ ((A.transpose * A) *ᵥ x
                - (t ^ 2 • (B₀.transpose * B₀)) *ᵥ x) := by
                rw [sub_mulVec]
        _ = x ⬝ᵥ ((A.transpose * A) *ᵥ x
                - t ^ 2 • ((B₀.transpose * B₀) *ᵥ x)) := by
                rw [smul_mulVec]
        _ = x ⬝ᵥ ((A.transpose * A) *ᵥ x)
            - t ^ 2 * (x ⬝ᵥ ((B₀.transpose * B₀) *ᵥ x)) := by
                simp [dotProduct_sub, dotProduct_smul]
    simpa [hexp] using (sub_nonneg.mpr (hquad x))

/-- Congruence + determinant-monotonicity step: a positive semidefinite comparison between
`AᵀA` and `t²·B₀ᵀB₀` yields the relative determinant inequality for every matrix `V`. -/
lemma det_gram_psd_relative {m r : ℕ} (B₀ A : Matrix (Fin m) (Fin m) ℝ) (t : ℝ)
    (V : Matrix (Fin m) (Fin r) ℝ)
    (hpsd : ((A.transpose * A) - t ^ 2 • (B₀.transpose * B₀)).PosSemidef) :
    t ^ (2 * r) * ((V.transpose * B₀.transpose * B₀ * V).det) ≤
      ((V.transpose * A.transpose * A * V).det) := by
  classical
  let P : Matrix (Fin r) (Fin r) ℝ := t ^ 2 • (V.transpose * B₀.transpose * B₀ * V)
  let Q : Matrix (Fin r) (Fin r) ℝ := V.transpose * A.transpose * A * V
  have hBpsd : (B₀.transpose * B₀).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) B₀
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hGram : (V.transpose * (B₀.transpose * B₀) * V).PosSemidef := by
    have := hBpsd.conjTranspose_mul_mul_same V
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hGram' : (V.transpose * B₀.transpose * B₀ * V).PosSemidef := by
    simpa [Matrix.mul_assoc] using hGram
  have hP : P.PosSemidef := by
    dsimp [P]
    exact hGram'.smul (sq_nonneg t)
  have hcong : (V.transpose * ((A.transpose * A) - t ^ 2 • (B₀.transpose * B₀)) * V).PosSemidef := by
    have := hpsd.conjTranspose_mul_mul_same V
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hdiff : V.transpose * (((A.transpose * A) - t ^ 2 • (B₀.transpose * B₀))) * V
      = V.transpose * A.transpose * A * V - t ^ 2 • (V.transpose * B₀.transpose * B₀ * V) := by
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hQP : (Q - P).PosSemidef := by
    dsimp [Q, P]
    rw [← hdiff]
    exact hcong
  have hdet := det_mono_posSemidef_sub (A := P) (B := Q) hP hQP
  dsimp [P, Q] at hdet
  have hdet' : (t ^ 2) ^ r * (V.transpose * B₀.transpose * B₀ * V).det ≤
      (V.transpose * A.transpose * A * V).det := by
    rw [Matrix.det_smul] at hdet
    simpa [Fintype.card_fin] using hdet
  have hpow : t ^ (2 * r) = (t ^ 2) ^ r := by
    rw [pow_mul]
  rwa [hpow]

/-- Relative lower bound for Gram determinants under an entrywise perturbation of the
ambient matrix: with `A` entrywise `δ`-close to an invertible `B₀`,
`det(UᵀAᵀAU) ≥ (1 - Cδ)^(2r) · det(UᵀB₀ᵀB₀U)` uniformly in `U`. -/
theorem det_gram_mul_relative_lower {m r : ℕ} (B₀ : Matrix (Fin m) (Fin m) ℝ)
    (hB : B₀.det ≠ 0) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (δ : ℝ), 0 ≤ δ → C * δ ≤ (1 : ℝ) / 2 →
    ∀ (A : Matrix (Fin m) (Fin m) ℝ),
      (∀ j i : Fin m, |A j i - B₀ j i| ≤ δ) →
      ∀ U : Matrix (Fin m) (Fin r) ℤ,
        let Uc : Matrix (Fin m) (Fin r) ℝ := U.map (fun z : ℤ => (z : ℝ))
        (1 - C * δ) ^ (2 * r) * ((Uc.transpose * B₀.transpose * B₀ * Uc).det) ≤
          ((Uc.transpose * A.transpose * A * Uc).det) := by
  classical
  obtain ⟨c, hc0, hc⟩ := Commons.Analysis.Fourier.sum_sq_le_const_sum_sq_mulVec B₀ hB
  let C : ℝ := (m : ℝ) * (c + 1) + 1
  have hCpos : 0 < C := by
    dsimp [C]
    have h : 0 ≤ (m : ℝ) * (c + 1) := by
      exact mul_nonneg (Nat.cast_nonneg m) (by linarith)
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro δ hδ0 hCδ A hA U
  have hC0 : 0 ≤ C := le_of_lt hCpos
  have hε0 : 0 ≤ C * δ := mul_nonneg hC0 hδ0
  have hε1 : C * δ ≤ 1 := by linarith
  have hdiff : ∀ x : Fin m → ℝ,
      (∑ i : Fin m, (((A - B₀).mulVec x) i) ^ 2) ≤
        (C * δ) ^ 2 * (∑ i : Fin m, ((B₀.mulVec x) i) ^ 2) := by
    intro x
    dsimp [C]
    exact entrywise_diff_sq_le B₀ A x hc0 (hc x) hδ0 hA
  let ε : ℝ := C * δ
  have hquad : ∀ x : Fin m → ℝ,
      (1 - ε) ^ 2 * (x ⬝ᵥ ((B₀.transpose * B₀) *ᵥ x)) ≤
        x ⬝ᵥ ((A.transpose * A) *ᵥ x) := by
    exact quad_perturb_dot B₀ A ε hε0 hε1 (by
      intro x
      simpa [ε] using hdiff x)
  have hpsd : ((A.transpose * A) - (1 - ε) ^ 2 • (B₀.transpose * B₀)).PosSemidef :=
    gram_sub_psd B₀ A (1 - ε) hquad
  have hrel := det_gram_psd_relative B₀ A (1 - ε) (U.map (fun z : ℤ => (z : ℝ))) hpsd
  dsimp [ε] at hrel ⊢
  simpa using hrel
end Commons.LinearAlgebra.Matrix
