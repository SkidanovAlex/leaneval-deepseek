import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.isUnit_one_sub_of_matNorm_lt_one
import Submission.Work.KT.idem_close_conj_of_isUnit
import Submission.Work.KT.idem_close_conj
import Submission.Work.KT.chain_prod_intertwine
import Submission.Work.KT.chain_grid_cover
import Submission.Work.KT.chain_sup_rowsum_mul_le
import Submission.Work.KT.chain_isUnit_one_add_of_rowsum_lt_one
import Submission.Work.KT.chain_idem_isUnit_and_conj
import Submission.Work.KT.chain_exists_norm_bound
import Submission.Work.KT.chain_uniform_continuous_norm_sub

open Matrix

namespace Work.KT

noncomputable section

/-! ### my definitions -/

/-- Grid point `1 - 2j/m` of `[-1,1]`. -/
def yj (m j : ℕ) : ℝ := 1 - 2 * (j : ℝ) / (m : ℝ)

/-- Clamp of `y` to `[yj m (j+1), yj m j]`. -/
def cval (m j : ℕ) (y : ℝ) : ℝ := min (yj m j) (max (yj m (j + 1)) y)

/-- Row-sum norm of a complex matrix, as an `NNReal`. -/
def matNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : NNReal :=
  Finset.univ.sup fun i => ∑ j, ‖A i j‖₊

/-- Entrywise-sup norm of a complex matrix. -/
def eNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ‖(fun i j => A i j)‖

/-- The same as `eNorm`, as an `NNReal`. -/
def eNormNN {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : NNReal := ‖(fun i j => A i j)‖₊

/-- Prefix products of a sequence in a monoid. -/
def prodUpTo {A : Type*} [Monoid A] (W : ℕ → A) : ℕ → A
  | 0 => 1
  | (k + 1) => prodUpTo W k * W k

@[simp] lemma prodUpTo_zero {A : Type*} [Monoid A] (W : ℕ → A) : prodUpTo W 0 = 1 := rfl
@[simp] lemma prodUpTo_succ {A : Type*} [Monoid A] (W : ℕ → A) (k : ℕ) :
    prodUpTo W (k + 1) = prodUpTo W k * W k := rfl

lemma continuous_prodUpTo {X : Type*} [TopologicalSpace X] {A : Type*} [TopologicalSpace A]
    [Monoid A] [ContinuousMul A] (W : ℕ → X → A) (hW : ∀ i, Continuous (W i)) (m : ℕ) :
    Continuous fun x => prodUpTo (fun i => W i x) m := by
  induction m with
  | zero => simpa using continuous_const
  | succ k ih =>
    have h : (fun x => prodUpTo (fun i => W i x) (k + 1))
        = fun x => prodUpTo (fun i => W i x) k * W k x := by
      funext x; rw [prodUpTo_succ]
    rw [h]
    exact ih.mul (hW k)

lemma isUnit_prodUpTo {A : Type*} [Monoid A] {W : ℕ → A} (h : ∀ i, IsUnit (W i)) (m : ℕ) :
    IsUnit (prodUpTo W m) := by
  induction m with
  | zero => simpa using isUnit_one
  | succ k ih => rw [prodUpTo_succ]; exact ih.mul (h k)

lemma prodUpTo_eq_one {A : Type*} [Monoid A] {W : ℕ → A} {m : ℕ} (h : ∀ i, i < m → W i = 1) :
    prodUpTo W m = 1 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [prodUpTo_succ, ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self k))),
      h k (Nat.lt_succ_self k), mul_one]

/-! ### the grid and the clamp -/

lemma yj_zero (m : ℕ) : yj m 0 = 1 := by simp [yj]

lemma yj_mono (m : ℕ) {i j : ℕ} (hij : i ≤ j) : yj m j ≤ yj m i := by
  simp only [yj]
  rw [sub_le_sub_iff_left]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  exact_mod_cast Nat.mul_le_mul_left 2 hij

lemma yj_le_one (m j : ℕ) : yj m j ≤ 1 := by
  have h : 0 ≤ 2 * (j : ℝ) / (m : ℝ) := div_nonneg (by positivity) (Nat.cast_nonneg m)
  simp only [yj]
  linarith

lemma yj_ge_neg_one (m j : ℕ) (h : j ≤ m) : -1 ≤ yj m j := by
  have h2 : 2 * (j : ℝ) / (m : ℝ) ≤ 2 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      rw [div_le_iff₀ hm']
      have : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
      linarith
  simp only [yj]
  linarith

lemma cval_le (m j : ℕ) (y : ℝ) : cval m j y ≤ yj m j := min_le_left _ _

lemma le_cval (m j : ℕ) (hm : 0 < m) (y : ℝ) : yj m (j + 1) ≤ cval m j y :=
  le_min (yj_mono m (Nat.le_succ j)) (le_max_left _ _)

lemma cval_eq_of_mem (m j : ℕ) (y : ℝ) (h1 : yj m (j + 1) ≤ y) (h2 : y ≤ yj m j) :
    cval m j y = y := by
  simp only [cval]
  rw [max_eq_right h1, min_eq_right h2]

lemma cval_eq_left (m j : ℕ) (y : ℝ) (h2 : yj m j ≤ y) : cval m j y = yj m j := by
  simp only [cval]
  rw [max_eq_right (le_trans (yj_mono m (Nat.le_succ j)) h2)]
  exact min_eq_left h2

lemma cval_eq_right (m j : ℕ) (y : ℝ) (h1 : y ≤ yj m (j + 1)) : cval m j y = yj m (j + 1) := by
  simp only [cval]
  rw [max_eq_left h1]
  exact min_eq_right (yj_mono m (Nat.le_succ j))

lemma cval_mem_Icc (m j : ℕ) (hj : j < m) (y : ℝ) : -1 ≤ cval m j y ∧ cval m j y ≤ 1 :=
  ⟨le_trans (yj_ge_neg_one m (j + 1) hj)
      (le_cval m j (Nat.lt_of_le_of_lt (Nat.zero_le j) hj) y),
    le_trans (cval_le m j y) (yj_le_one m j)⟩

lemma yj_sub (m j : ℕ) (hm : 0 < m) : yj m j - yj m (j + 1) = 2 / (m : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  simp only [yj, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The closed unit ball of `ℝ`, from an explicit element. -/
def mkBall (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : Ball ℝ :=
  ⟨x, by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact abs_le.mpr ⟨h1, h2⟩⟩

/-- The grid point `y_j` as a point of the ball. -/
def ptj (m j : ℕ) (hj : j ≤ m) : Ball ℝ :=
  mkBall (yj m j) (yj_ge_neg_one m j hj) (yj_le_one m j)

/-- The clamp of `y` to `[y_{j+1}, y_j]` as a point of the ball. -/
def cball (m j : ℕ) (hj : j < m) (y : Ball ℝ) : Ball ℝ :=
  mkBall (cval m j (y : ℝ)) (cval_mem_Icc m j hj (y : ℝ)).1 (cval_mem_Icc m j hj (y : ℝ)).2

def ptjAll (m : ℕ) (k : ℕ) : Ball ℝ :=
  if h : k ≤ m then ptj m k h else ptj m 0 (Nat.zero_le m)

lemma ptjAll_of_le {m k : ℕ} (h : k ≤ m) : ptjAll m k = ptj m k h := by
  simp only [ptjAll, dif_pos h]

lemma continuous_cval (m j : ℕ) : Continuous fun y : Ball ℝ => cval m j (y : ℝ) := by
  change Continuous fun y : Ball ℝ => min (yj m j) (max (yj m (j + 1)) (y : ℝ))
  exact Continuous.min continuous_const (Continuous.max continuous_const continuous_subtype_val)

lemma continuous_cball (m j : ℕ) (hj : j < m) : Continuous (cball m j hj) :=
  Continuous.subtype_mk (continuous_cval m j) (fun y => by
    show cval m j (y : ℝ) ∈ Metric.closedBall (0 : ℝ) 1
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact abs_le.mpr (cval_mem_Icc m j hj (y : ℝ)))

lemma dist_rel (m j : ℕ) (hj : j < m) (y : Ball ℝ) :
    dist (cball m j hj y) (ptj m j (le_of_lt hj)) = |cval m j (y : ℝ) - yj m j| := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simp only [cball, ptj, mkBall]

lemma dist_cball_le (m j : ℕ) (hm : 0 < m) (hj : j < m) (y : Ball ℝ) :
    dist (cball m j hj y) (ptj m j (le_of_lt hj)) ≤ 2 / (m : ℝ) := by
  rw [dist_rel]
  have h1 : cval m j (y : ℝ) ≤ yj m j := cval_le m j _
  have h2 : yj m (j + 1) ≤ cval m j (y : ℝ) := le_cval m j hm _
  have h3 : cval m j (y : ℝ) - yj m j ≤ 0 := by linarith
  rw [abs_of_nonpos h3]
  have h4 : yj m j - yj m (j + 1) = 2 / (m : ℝ) := yj_sub m j hm
  linarith

lemma dist_ptj (m i k : ℕ) (hi : i ≤ m) (hk : k ≤ m) :
    dist (ptj m i hi) (ptj m k hk) = |yj m i - yj m k| := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simp only [ptj, mkBall]

/-- Relating the row-sum norm to the entrywise-sup norm. -/
lemma matNorm_le_eNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (matNorm A : ℝ) ≤ ((n : ℝ) + 1) * eNorm A := by
  have h1 : matNorm A ≤ ((n : NNReal) + 1) * eNormNN A := by
    refine Finset.sup_le fun i _ => ?_
    calc ∑ j, ‖A i j‖₊ ≤ ∑ _j : Fin n, eNormNN A :=
          Finset.sum_le_sum fun j _ =>
            (nnnorm_le_pi_nnnorm (fun j => A i j) j).trans
              (nnnorm_le_pi_nnnorm (fun i j => A i j) i)
      _ = (n : NNReal) * eNormNN A := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((n : NNReal) + 1) * eNormNN A := by
          rw [add_mul, one_mul]; exact le_add_of_nonneg_right zero_le
  have h2 : ((((n : NNReal) + 1) * eNormNN A : NNReal) : ℝ) = ((n : ℝ) + 1) * eNorm A := by
    simp [eNorm, eNormNN]
  calc (matNorm A : ℝ) ≤ (((n : NNReal) + 1) * eNormNN A : NNReal) := by exact_mod_cast h1
    _ = ((n : ℝ) + 1) * eNorm A := h2

lemma matNorm_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (matNorm (A * B) : ℝ) ≤ (matNorm A : ℝ) * (matNorm B : ℝ) := by
  exact_mod_cast chain_sup_rowsum_mul_le A B

lemma matNorm_lt_one_of_coe {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : (matNorm A : ℝ) < 1) :
    matNorm A < 1 :=
  NNReal.coe_lt_coe.mp (by simpa using h)

/-- The per-grid-point family of conjugating matrices. -/
def Wfun {n : ℕ} (m : ℕ) (γ : Ball ℝ → Matrix (Fin n) (Fin n) ℂ) (i : ℕ) (y : Ball ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  if hi : i < m then
    1 + (2 * γ (ptj m i (le_of_lt hi)) - 1) * (γ (cball m i hi y) - γ (ptj m i (le_of_lt hi)))
  else 1

lemma Wfun_of_lt {n : ℕ} {m : ℕ} {γ : Ball ℝ → Matrix (Fin n) (Fin n) ℂ} {i : ℕ} (hi : i < m)
    (y : Ball ℝ) :
    Wfun m γ i y = 1 + (2 * γ (ptj m i (le_of_lt hi)) - 1) *
      (γ (cball m i hi y) - γ (ptj m i (le_of_lt hi))) := by
  rw [Wfun, dif_pos hi]

lemma Wfun_of_ge {n : ℕ} {m : ℕ} {γ : Ball ℝ → Matrix (Fin n) (Fin n) ℂ} {i : ℕ}
    (hi : ¬ i < m) (y : Ball ℝ) : Wfun m γ i y = 1 := by
  rw [Wfun, dif_neg hi]

lemma continuous_Wfun {n : ℕ} (m : ℕ) (γ : Ball ℝ → Matrix (Fin n) (Fin n) ℂ) (hγ : Continuous γ)
    (i : ℕ) : Continuous (Wfun m γ i) := by
  change Continuous fun y : Ball ℝ => Wfun m γ i y
  simp only [Wfun]
  split_ifs with hi
  · exact continuous_const.add (continuous_const.mul
      ((hγ.comp (continuous_cball m i hi)).sub continuous_const))
  · exact continuous_const

lemma dist_ptj_val (m j : ℕ) (hj : j ≤ m) (y : Ball ℝ) :
    dist (ptj m j hj) y = |yj m j - (y : ℝ)| := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simp only [ptj, mkBall]

/-- **Chaining lemma.**  For a continuous family of idempotent matrices over the closed unit ball
`D¹ = [-1,1]` of `ℝ`, there is a continuous family of invertible matrices conjugating the family to
its value at the point `1`.

Proof route: if `p`, `q` are idempotent complex matrices with the row-sum norm of
`(2p-1)(q-p)` less than `1`, then `z = p*q + (1-p)*(1-q) = 1 + (2p-1)(q-p)` is a unit with
`z * q = p * z`; this is `Work.KT.isUnit_one_sub_of_matNorm_lt_one` +
`Work.KT.idem_close_conj_of_isUnit`.  Uniform continuity of `γ` on the compact interval gives
`δ > 0`; pick `m` with `2/m ≤ δ` and points `y_j = 1 - 2j/m`.  Set
`W_j(y) = γ(y_j)*γ(c_j(y)) + (1-γ(y_j))*(1-γ(c_j(y)))` where `c_j(y)` is the clamp of `y` to
`[y_{j+1}, y_j]`.  Then `W_j(y)` is a unit for every `y`, `W_j(y) * γ(c_j(y)) = γ(y_j) * W_j(y)`,
and `X := W_0 * W_1 * ⋯ * W_{m-1}` satisfies `X 1 = 1` and `X(y) * γ(y) = γ(1) * X(y)` for all `y`.
(The recurrence is `A_0⋯A_{j-1} γ(y_j) = γ(1) A_0⋯A_{j-1}` on each step; `X(1) = 1` since `W_0(1)=1`.) -/
theorem chain_conjugation (n : ℕ) (γ : Ball ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hγ : Continuous γ) (hidem : ∀ y, γ y * γ y = γ y) :
    ∃ X : Ball ℝ → Matrix (Fin n) (Fin n) ℂ, Continuous X ∧
      X ⟨1, by simp [Metric.mem_closedBall]⟩ = 1 ∧ (∀ y, IsUnit (X y)) ∧
      ∀ y, X y * γ y = γ ⟨1, by simp [Metric.mem_closedBall]⟩ * X y := by
  haveI : CompactSpace (Ball ℝ) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℝ) 1)
  obtain ⟨A₀, hA₀nn, hA₀⟩ := chain_exists_norm_bound γ hγ
  set BR : ℝ := ((n : ℝ) + 1) * A₀ with hBRdef
  have hBRnn : 0 ≤ BR := by rw [hBRdef]; positivity
  set ηR : ℝ := 1 / (BR + 1) with hηRdef
  have hηRpos : 0 < ηR := by rw [hηRdef]; positivity
  have hBη : BR * ηR < 1 := by
    rw [hηRdef, mul_one_div]
    rw [div_lt_iff₀ (show (0 : ℝ) < BR + 1 by linarith)]
    linarith
  set εR : ℝ := ηR / ((n : ℝ) + 1) with hεRdef
  have hεRpos : 0 < εR := by rw [hεRdef]; positivity
  have hεRη : ((n : ℝ) + 1) * εR = ηR := by
    rw [hεRdef]; field_simp
  obtain ⟨δ, hδpos, hδ⟩ := chain_uniform_continuous_norm_sub γ hγ εR hεRpos
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  set m : ℕ := N + 1 with hmdef
  have hmpos : 0 < m := Nat.succ_pos N
  have hmδ : 2 / (m : ℝ) < δ := by
    have h1 : (2 : ℝ) / δ < (N : ℝ) := hN
    rw [div_lt_iff₀ hδpos] at h1
    rw [hmdef, Nat.cast_add, Nat.cast_one,
      div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    nlinarith [h1, hδpos, (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  have hclose : ∀ a b : Ball ℝ, dist a b < δ →
      matNorm ((2 * γ a - 1) * (γ b - γ a)) < 1 := by
    intro a b hab
    have h1 : (matNorm (2 * γ a - 1) : ℝ) ≤ BR := by
      calc (matNorm (2 * γ a - 1) : ℝ) ≤ ((n : ℝ) + 1) * eNorm (2 * γ a - 1) :=
            matNorm_le_eNorm _
        _ ≤ ((n : ℝ) + 1) * A₀ :=
            mul_le_mul_of_nonneg_left (hA₀ a) (by positivity)
        _ = BR := rfl
    have h2 : (matNorm (γ b - γ a) : ℝ) < ηR := by
      calc (matNorm (γ b - γ a) : ℝ) ≤ ((n : ℝ) + 1) * eNorm (γ b - γ a) :=
            matNorm_le_eNorm _
        _ < ((n : ℝ) + 1) * εR :=
            mul_lt_mul_of_pos_left (hδ b a (by simpa [dist_comm] using hab)) (by positivity)
        _ = ηR := hεRη
    have h3 : (matNorm ((2 * γ a - 1) * (γ b - γ a)) : ℝ) < 1 := by
      calc (matNorm ((2 * γ a - 1) * (γ b - γ a)) : ℝ)
          ≤ (matNorm (2 * γ a - 1) : ℝ) * (matNorm (γ b - γ a) : ℝ) := matNorm_mul_le _ _
        _ ≤ BR * ηR := mul_le_mul h1 (le_of_lt h2) (NNReal.coe_nonneg _) hBRnn
        _ < 1 := hBη
    exact matNorm_lt_one_of_coe h3
  let pt1 : Ball ℝ := ⟨1, by simp [Metric.mem_closedBall]⟩
  have hpt1val : (pt1 : ℝ) = 1 := rfl
  let X : Ball ℝ → Matrix (Fin n) (Fin n) ℂ := fun y => prodUpTo (fun i => Wfun m γ i y) m
  have hXcont : Continuous X := continuous_prodUpTo (Wfun m γ) (fun i => continuous_Wfun m γ hγ i) m
  refine ⟨X, hXcont, ?_, ?_, ?_⟩
  · change prodUpTo (fun i => Wfun m γ i pt1) m = 1
    apply prodUpTo_eq_one
    intro i hi
    rw [Wfun_of_lt hi]
    have hc : cball m i hi pt1 = ptj m i (le_of_lt hi) := by
      apply Subtype.ext
      show cval m i (pt1 : ℝ) = yj m i
      rw [hpt1val]
      exact cval_eq_left m i 1 (yj_le_one m i)
    rw [hc, sub_self, mul_zero, add_zero]
  · intro y
    change IsUnit (prodUpTo (fun i => Wfun m γ i y) m)
    apply isUnit_prodUpTo
    intro i
    by_cases hi : i < m
    · rw [Wfun_of_lt hi]
      refine (chain_idem_isUnit_and_conj (γ (ptj m i (le_of_lt hi))) (γ (cball m i hi y))
        (hidem _) (hidem _) ?_).1
      have hd : dist (ptj m i (le_of_lt hi)) (cball m i hi y) < δ := by
        rw [dist_comm]
        exact lt_of_le_of_lt (dist_cball_le m i hmpos hi y) hmδ
      exact hclose _ _ hd
    · rw [Wfun_of_ge hi]
      exact isUnit_one
  · intro y
    change prodUpTo (fun i => Wfun m γ i y) m * γ y = γ pt1 * prodUpTo (fun i => Wfun m γ i y) m
    have hyabs : |(y : ℝ)| ≤ 1 := by
      have hy : (y : ℝ) ∈ Metric.closedBall (0 : ℝ) 1 := y.2
      rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hy
    obtain ⟨hyl, hyu⟩ := abs_le.mp hyabs
    obtain ⟨j, hjm, hjl, hjr⟩ := chain_grid_cover m hmpos (y : ℝ) hyl hyu
    have hjl' : yj m (j + 1) ≤ (y : ℝ) := by simpa [yj, Nat.cast_add, Nat.cast_one] using hjl
    have hjr' : (y : ℝ) ≤ yj m j := by simpa [yj] using hjr
    have hp0 : ptjAll m 0 = pt1 := by
      rw [ptjAll_of_le (Nat.zero_le m)]
      apply Subtype.ext
      show yj m 0 = (pt1 : ℝ)
      rw [hpt1val, yj_zero]
    have hchain : prodUpTo (fun i => Wfun m γ i y) m * γ y
        = γ (ptjAll m 0) * prodUpTo (fun i => Wfun m γ i y) m := by
      refine chain_prod_intertwine (fun k => γ (ptjAll m k)) (γ y)
        (fun i => Wfun m γ i y) (fun k => prodUpTo (fun i => Wfun m γ i y) k) j m rfl
        (fun k => prodUpTo_succ (fun i => Wfun m γ i y) k) hjm ?_ ?_ ?_
      · intro i hi
        have him : i < m := Nat.lt_trans hi hjm
        have hi1m : i + 1 ≤ m := le_trans (Nat.succ_le_of_lt hi) (le_of_lt hjm)
        rw [ptjAll_of_le (le_of_lt him), ptjAll_of_le hi1m, Wfun_of_lt him]
        have hc : cball m i him y = ptj m (i + 1) hi1m := by
          apply Subtype.ext
          show cval m i (y : ℝ) = yj m (i + 1)
          exact cval_eq_right m i _ (le_trans hjr' (yj_mono m (Nat.succ_le_of_lt hi)))
        rw [hc]
        have hd : dist (ptj m i (le_of_lt him)) (ptj m (i + 1) hi1m) < δ := by
          rw [dist_ptj]
          have hsub : yj m i - yj m (i + 1) = 2 / (m : ℝ) := yj_sub m i hmpos
          have hle : yj m (i + 1) ≤ yj m i := yj_mono m (Nat.le_succ i)
          rw [abs_of_nonneg (by linarith), hsub]
          exact hmδ
        exact (chain_idem_isUnit_and_conj (γ (ptj m i (le_of_lt him)))
          (γ (ptj m (i + 1) hi1m)) (hidem _) (hidem _) (hclose _ _ hd)).2
      · have hc : cball m j hjm y = y := by
          apply Subtype.ext
          show cval m j (y : ℝ) = (y : ℝ)
          exact cval_eq_of_mem m j _ hjl' hjr'
        rw [ptjAll_of_le (le_of_lt hjm), Wfun_of_lt hjm, hc]
        have hd : dist (ptj m j (le_of_lt hjm)) y < δ := by
          rw [dist_ptj_val]
          have hsub : yj m j - yj m (j + 1) = 2 / (m : ℝ) := yj_sub m j hmpos
          have hle : yj m (j + 1) ≤ yj m j := yj_mono m (Nat.le_succ j)
          rw [abs_of_nonneg (by linarith)]
          exact lt_of_le_of_lt (by linarith) hmδ
        exact (chain_idem_isUnit_and_conj (γ (ptj m j (le_of_lt hjm))) (γ y)
          (hidem _) (hidem _) (hclose _ _ hd)).2
      · intro i hji him
        rw [Wfun_of_lt him]
        have hc : cball m i him y = ptj m i (le_of_lt him) := by
          apply Subtype.ext
          show cval m i (y : ℝ) = yj m i
          exact cval_eq_left m i _ (le_trans (yj_mono m (Nat.succ_le_of_lt hji)) hjl')
        rw [hc, sub_self, mul_zero, add_zero]
    rw [hp0] at hchain
    exact hchain

end

end Work.KT
