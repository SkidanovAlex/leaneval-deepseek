/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# A loop in `GL_n(ℂ)` whose determinant has a logarithm is nullhomotopic

`Work.KT.Dim2.loop_GL_nullhomotopic_of_det_log`: if `f : S¹ → GL_n(ℂ)` is a loop of invertible
complex matrices and `det ∘ f` has a continuous logarithm, then `f` is null-homotopic through
invertible matrices.  Equivalently, `det : π₁(GL_n(ℂ)) → π₁(ℂ*)` is injective.

The proof is an induction on `n`; the inductive step deforms the loop so that its *last column*
becomes a positive multiple of the last basis vector, which exhibits the loop (up to homotopy) as
block upper triangular `[[A, ·], [0, λ]]` with `A` a loop of `(n-1) × (n-1)` matrices; the
determinant hypothesis descends to `A`, and the induction hypothesis applies.
-/
import Mathlib
import Submission.Work.KT.Dim2.Defs
import Submission.Work.Degree.nullhomotopic_of_dim_lt_sph

namespace Work.KT.Dim2

open Matrix ContinuousMap

noncomputable section

variable {n : ℕ}

/-! ## 1. Elementary matrix computations -/

lemma star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma cip_self' (u : Fin n → ℂ) : cip u u = (cnrm2 u : ℂ) := by
  rw [cip, cnrm2, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => star_mul_self (u j)

lemma outer_mulVec (w u : Fin n → ℂ) : (outer w u) *ᵥ u = fun i => w i * cip u u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, outer, Matrix.of_apply, cip]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma step_mulVec' {u w : Fin n → ℂ} (hu : u ≠ 0) :
    (1 + (cip u u)⁻¹ • outer w u) *ᵥ u = u + w := by
  have h0 : cip u u ≠ 0 := by
    rw [cip_self']
    exact_mod_cast ne_of_gt (cnrm2_pos hu)
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, outer_mulVec]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm, inv_mul_cancel₀ h0, mul_one]

/-- `M *ᵥ e0 m = 0` is impossible for an invertible `M`. -/
lemma mulVec_e0_ne_zero {m : ℕ} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hM : IsUnit M) :
    M *ᵥ e0 (m + 1) ≠ 0 := by
  obtain ⟨u, rfl⟩ := hM
  intro h
  have h1 : (↑u⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) *ᵥ
      ((↑u : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) *ᵥ e0 (m + 1)) = e0 (m + 1) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_zero] at h1
  exact e0_ne_zero m h1.symm

/-- `cnrm2` is bounded by `n` times the squared norm. -/
lemma cnrm2_le_card_mul (u : Fin n → ℂ) : cnrm2 u ≤ (n : ℝ) * ‖u‖ ^ 2 := by
  calc cnrm2 u = ∑ j, ‖u j‖ ^ 2 := rfl
    _ ≤ ∑ _j : Fin n, ‖u‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := norm_le_pi_norm u j
        nlinarith [norm_nonneg (u j), norm_nonneg u]
    _ = (n : ℝ) * ‖u‖ ^ 2 := by simp

lemma cnrm2_sub_le {u v : Fin n → ℂ} {ε : ℝ} (hε0 : 0 ≤ ε) (h : ‖u - v‖ ≤ ε) :
    cnrm2 (u - v) ≤ (n : ℝ) * ε ^ 2 := by
  refine (cnrm2_le_card_mul (u - v)).trans ?_
  have h2 : ‖u - v‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg (u - v)]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Positivity of the interpolation `(1-s) c + s`, `0 ≤ s ≤ 1`, `c > 0`. -/
lemma one_sub_mul_add_pos {t c : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hc : 0 < c) :
    0 < (1 - t) * c + t := by
  rcases lt_or_eq_of_le ht1 with h | h
  · have h1 : 0 < 1 - t := by linarith
    nlinarith [mul_pos h1 hc]
  · rw [h]; norm_num

/-! ## 2. Homotopies of non-vanishing scalar loops -/

lemma LoopHom.refl (f : C(C1, ℂ)) (hf : ∀ z, f z ≠ 0) : LoopHom f f :=
  ⟨ContinuousMap.Homotopy.refl f, fun p => hf p.2⟩

lemma LoopHom.mul {f g f' g' : C(C1, ℂ)} (h : LoopHom f g) (h' : LoopHom f' g') :
    LoopHom (f * f') (g * g') := by
  obtain ⟨H, hH⟩ := h
  obtain ⟨H', hH'⟩ := h'
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨fun p => H p * H' p, H.toContinuousMap.continuous.mul H'.toContinuousMap.continuous⟩
    ?_ ?_, ?_⟩
  · intro x
    have h1 : H (0, x) = f x := H.map_zero_left x
    have h2 : H' (0, x) = f' x := H'.map_zero_left x
    change H (0, x) * H' (0, x) = (f * f') x
    rw [h1, h2, ContinuousMap.mul_apply]
  · intro x
    have h1 : H (1, x) = g x := H.map_one_left x
    have h2 : H' (1, x) = g' x := H'.map_one_left x
    change H (1, x) * H' (1, x) = (g * g') x
    rw [h1, h2, ContinuousMap.mul_apply]
  · intro p
    exact mul_ne_zero (hH p) (hH' p)

/-- Existence of a continuous logarithm gives null-homotopy through non-vanishing loops. -/
lemma NullLoop.of_log {f : C(C1, ℂ)} (h : ∃ F : C(C1, ℂ), ∀ z, Complex.exp (F z) = f z) :
    NullLoop f := by
  obtain ⟨F, hF⟩ := h
  have hcont : Continuous fun p : unitInterval × C1 => Complex.exp ((1 - (p.1 : ℝ)) * F p.2) := by
    fun_prop
  refine ⟨ContinuousMap.Homotopy.mk ⟨_, hcont⟩ ?_ ?_, ?_⟩
  · intro z
    have h1 : (((0 : unitInterval) : ℝ) : ℂ) = 0 := by norm_num
    simp only [h1, sub_zero, one_mul]
    exact hF z
  · intro z
    have h1 : (((1 : unitInterval) : ℝ) : ℂ) = 1 := by norm_num
    simp only [h1, sub_self, zero_mul, Complex.exp_zero]
    rfl
  · intro p
    exact Complex.exp_ne_zero _

/-- The inverse of a positive-real loop is null-homotopic. -/
lemma nullLoop_inv_pos (r : C(C1, ℝ)) (hr : ∀ z, 0 < r z) (f : C(C1, ℂ))
    (hf : ∀ z, f z = ((r z : ℂ))⁻¹) : NullLoop f := by
  have hlog : Continuous fun z : C1 => Real.log (r z) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (Real.continuousAt_log (ne_of_gt (hr z))).comp r.continuous.continuousAt
  refine NullLoop.of_log ⟨⟨fun z => ((-(Real.log (r z)) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (continuous_neg.comp hlog)⟩, ?_⟩
  intro z
  rw [hf z]
  change Complex.exp (((-(Real.log (r z)) : ℝ) : ℂ)) = ((r z : ℂ))⁻¹
  rw [Complex.ofReal_neg, Complex.ofReal_log (le_of_lt (hr z)), Complex.exp_neg,
    Complex.exp_log (Complex.ofReal_ne_zero.mpr (ne_of_gt (hr z)))]

/-- Combining two null loops: if `c` agrees pointwise with a product of null loops, it is null. -/
lemma NullLoop.of_mul {a b c : C(C1, ℂ)} (ha : NullLoop a) (hb : NullLoop b)
    (h : ∀ z, c z = a z * b z) : NullLoop c := by
  have hc : c = a * b := ContinuousMap.ext fun z => h z
  rw [hc]
  have := ha.mul hb
  simpa using this

/-! ## 3. Block matrices (special block = last coordinate) -/

/-- The identification `Fin 1 ⊕ Fin m ≃ Fin (m+1)`: `Fin 1` is the first coordinate and `Fin m`
the last `m` coordinates. -/
def eSum (m : ℕ) : Fin 1 ⊕ Fin m ≃ Fin (m + 1) where
  toFun s := match s with
    | Sum.inl _ => 0
    | Sum.inr j => j.succ
  invFun i := Fin.cases (Sum.inl 0) (fun j => Sum.inr j) i
  left_inv := by
    rintro (i | j)
    · have hi : i = 0 := Subsingleton.elim i (0 : Fin 1)
      subst hi; rfl
    · simp [Fin.cases_succ]
  right_inv := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · subst h; simp [Fin.cases_zero]
    · subst h; simp [Fin.cases_succ]

/-- Reindexing `Fin (m+1) ≅ Fin 1 ⊕ Fin m`, splitting off the first coordinate. -/
def blkE (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ ≃ Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℂ :=
  Matrix.reindex (eSum m).symm (eSum m).symm

/-- The block matrix `[[μ, b], [0, A]]` on `Fin (m+1)`. -/
def blk (m : ℕ) (μ : Matrix (Fin 1) (Fin 1) ℂ) (b : Matrix (Fin 1) (Fin m) ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  (blkE m).symm (Matrix.fromBlocks μ b 0 A)

/-- The `1 × 1` matrix with entry `c`. -/
def oneByOne (c : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => c

@[simp] lemma oneByOne_apply (c : ℂ) (i j : Fin 1) : oneByOne c i j = c := rfl
lemma oneByOne_det (c : ℂ) : (oneByOne c).det = c := by simp [oneByOne]
lemma oneByOne_one : oneByOne (1 : ℂ) = 1 := by
  ext i j
  rw [oneByOne_apply, Matrix.one_apply, if_pos (Subsingleton.elim i j)]

lemma mulVec_e0_apply {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (i : Fin (m + 1)) :
    Matrix.mulVec M (e0 (m + 1)) i = M i 0 := by
  simp only [Matrix.mulVec, dotProduct, e0]
  rw [Finset.sum_eq_single (0 : Fin (m + 1))]
  · simp
  · intro j _ hj
    have hne : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext (by simpa using h))
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[simp] lemma eSum_inl_zero (m : ℕ) : eSum m (Sum.inl (0 : Fin 1)) = 0 := rfl

@[simp] lemma eSum_inr_succ (m : ℕ) (j : Fin m) : eSum m (Sum.inr j) = j.succ := rfl

lemma blkE_apply (m : ℕ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (i j : Fin 1 ⊕ Fin m) :
    blkE m X i j = X (eSum m i) (eSum m j) := by
  simp only [blkE, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]

lemma blkE_mul (m : ℕ) (X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    blkE m X * blkE m Y = blkE m (X * Y) := by
  simp only [blkE, Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv X Y (eSum m) (eSum m) (eSum m)]

lemma blkE_symm_det (m : ℕ) (Y : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℂ) :
    ((blkE m).symm Y).det = Y.det := by
  simp only [blkE, Matrix.reindex_symm, Equiv.symm_symm]
  exact Matrix.det_reindex_self (eSum m) Y

lemma blkE_one (m : ℕ) : blkE m 1 = 1 := by
  ext i j
  rw [blkE_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : eSum m i ≠ eSum m j := fun hh => h ((eSum m).injective hh)
    simp [h, h']

lemma blk_det (m : ℕ) (μ : Matrix (Fin 1) (Fin 1) ℂ) (b : Matrix (Fin 1) (Fin m) ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) : (blk m μ b A).det = μ.det * A.det := by
  show ((blkE m).symm (Matrix.fromBlocks μ b 0 A)).det = _
  rw [blkE_symm_det, Matrix.det_fromBlocks_zero₂₁]

lemma blk_one (m : ℕ) : blk m 1 0 1 = 1 := by
  show (blkE m).symm (Matrix.fromBlocks 1 0 0 1) = 1
  rw [Matrix.fromBlocks_one, ← blkE_one]
  exact Equiv.symm_apply_apply _ _

lemma blk_mul (m : ℕ) (μ : Matrix (Fin 1) (Fin 1) ℂ) (b : Matrix (Fin 1) (Fin m) ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) (μ' : Matrix (Fin 1) (Fin 1) ℂ)
    (b' : Matrix (Fin 1) (Fin m) ℂ) (A' : Matrix (Fin m) (Fin m) ℂ) :
    blk m μ b A * blk m μ' b' A' = blk m (μ * μ') (μ * b' + b * A') (A * A') := by
  rw [show blk m μ b A = (blkE m).symm (Matrix.fromBlocks μ b 0 A) from rfl,
    show blk m μ' b' A' = (blkE m).symm (Matrix.fromBlocks μ' b' 0 A') from rfl,
    show blk m (μ * μ') (μ * b' + b * A') (A * A') =
      (blkE m).symm (Matrix.fromBlocks (μ * μ') (μ * b' + b * A') 0 (A * A')) from rfl]
  apply (blkE m).injective
  rw [← blkE_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Matrix.fromBlocks_multiply]
  simp

lemma blk_isUnit_iff {m : ℕ} (c : ℂ) (b : Matrix (Fin 1) (Fin m) ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) :
    IsUnit (blk m (oneByOne c) b A) ↔ c ≠ 0 ∧ A.det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, blk_det, oneByOne_det, isUnit_iff_ne_zero]
  constructor
  · intro h; exact ⟨fun h0 => h (by rw [h0, zero_mul]), fun h0 => h (by rw [h0, mul_zero])⟩
  · rintro ⟨h1, h2⟩ h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact h1 h
    · exact h2 h

/-- Extracting the block decomposition of a matrix whose first column is a multiple of `e0`. -/
lemma blkE_eq_of_firstCol {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c : ℂ)
    (hcol : M *ᵥ e0 (m + 1) = c • e0 (m + 1)) :
    blkE m M = Matrix.fromBlocks (oneByOne c) (Matrix.of fun _ j => M 0 j.succ)
      (0 : Matrix (Fin m) (Fin 1) ℂ) (Matrix.of fun i j => M i.succ j.succ) := by
  have hentry : ∀ i : Fin (m + 1), M i 0 = c * (e0 (m + 1) i) := by
    intro i
    have h := congrFun hcol i
    rw [mulVec_e0_apply] at h
    rw [h, Pi.smul_apply, smul_eq_mul]
  have h0 : M 0 0 = c := by have := hentry 0; simpa [e0] using this
  have hlow : ∀ i : Fin m, M i.succ 0 = 0 := by
    intro i
    have h := hentry i.succ
    have hne : ((i.succ : Fin (m + 1)) : ℕ) ≠ 0 := by simp [Fin.val_succ]
    simpa [e0, hne] using h
  ext i j
  rcases i with i | i
  · have hi : i = 0 := Subsingleton.elim i (0 : Fin 1)
    subst hi
    rcases j with j | j
    · have hj : j = 0 := Subsingleton.elim j (0 : Fin 1)
      subst hj
      rw [blkE_apply]
      simp only [eSum_inl_zero, Matrix.fromBlocks_apply₁₁, oneByOne_apply]
      exact h0
    · rw [blkE_apply]
      simp only [eSum_inl_zero, eSum_inr_succ, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
  · rcases j with j | j
    · rw [blkE_apply]
      simp only [eSum_inr_succ, eSum_inl_zero, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      exact hlow i
    · rw [blkE_apply]
      simp only [eSum_inr_succ, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]

/-- Block decomposition as an equality of matrices on `Fin (m+1)`. -/
lemma eq_blk_of_firstCol {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c : ℂ)
    (hcol : M *ᵥ e0 (m + 1) = c • e0 (m + 1)) :
    M = blk m (oneByOne c) (Matrix.of fun _ j => M 0 j.succ)
      (Matrix.of fun i j => M i.succ j.succ) := by
  have key : (blkE m).symm (blkE m M) = blk m (oneByOne c) (Matrix.of fun _ j => M 0 j.succ)
      (Matrix.of fun i j => M i.succ j.succ) := by
    rw [blkE_eq_of_firstCol M c hcol]
    rfl
  rw [← key, Equiv.symm_apply_apply]

/-! ## 4. Homotopies of matrix loops -/

lemma HomU.refl {f : C(C1, Matrix (Fin n) (Fin n) ℂ)} (hf : ∀ z, IsUnit (f z)) : HomU f f :=
  ⟨ContinuousMap.Homotopy.refl f, fun p => hf p.2⟩

lemma HomU.trans {f g h : C(C1, Matrix (Fin n) (Fin n) ℂ)} (H1 : HomU f g) (H2 : HomU g h) :
    HomU f h := by
  obtain ⟨H1, h1⟩ := H1
  obtain ⟨H2, h2⟩ := H2
  refine ⟨H1.trans H2, fun p => ?_⟩
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with hp
  · exact h1 _
  · exact h2 _

/-- Pointwise product of matrix loops. -/
def cmul {n : ℕ} (f g : C(C1, Matrix (Fin n) (Fin n) ℂ)) : C(C1, Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun z => f z * g z, f.continuous.matrix_mul g.continuous⟩

lemma HomU.mul {f g f' g' : C(C1, Matrix (Fin n) (Fin n) ℂ)} (h : HomU f g) (h' : HomU f' g') :
    HomU (cmul f f') (cmul g g') := by
  obtain ⟨H, hH⟩ := h
  obtain ⟨H', hH'⟩ := h'
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨fun p => H p * H' p, H.toContinuousMap.continuous.matrix_mul H'.toContinuousMap.continuous⟩
    ?_ ?_, ?_⟩
  · intro x
    have h1 : H (0, x) = f x := H.map_zero_left x
    have h2 : H' (0, x) = f' x := H'.map_zero_left x
    change H (0, x) * H' (0, x) = (cmul f f') x
    rw [h1, h2]; rfl
  · intro x
    have h1 : H (1, x) = g x := H.map_one_left x
    have h2 : H' (1, x) = g' x := H'.map_one_left x
    change H (1, x) * H' (1, x) = (cmul g g') x
    rw [h1, h2]; rfl
  · intro p
    exact IsUnit.mul (hH p) (hH' p)


/-! ## 5. Uniform smallness and the discrete family of vectors -/

lemma continuous_cnrm2_V (V : C(C1 × unitInterval, Fin n → ℂ)) :
    Continuous fun p : C1 × unitInterval => cnrm2 (V p) := by
  simp only [cnrm2]
  exact continuous_finsetSum _ fun j _ => ((continuous_apply j).comp V.continuous).norm.pow 2

lemma uniform_small (V : C(C1 × unitInterval, Fin n → ℂ)) (hV : ∀ p, V p ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p q : C1 × unitInterval, dist p q < δ →
      4 * cnrm2 (V p - V q) < cnrm2 (V q) := by
  obtain ⟨p₀, -, hp₀⟩ :=
    IsCompact.exists_isMinOn (s := Set.univ) isCompact_univ Set.univ_nonempty
      (continuous_cnrm2_V V).continuousOn
  set m : ℝ := cnrm2 (V p₀) with hm
  have hmpos : 0 < m := cnrm2_pos (hV p₀)
  set ε : ℝ := Real.sqrt (m / (4 * ((n : ℝ) + 1))) with hε
  have hεpos : 0 < ε := by
    rw [hε]; exact Real.sqrt_pos.mpr (by positivity)
  have hεsq : ε ^ 2 = m / (4 * ((n : ℝ) + 1)) := by
    rw [hε]; exact Real.sq_sqrt (by positivity)
  have hkey : 4 * (n : ℝ) * ε ^ 2 < m := by
    rw [hεsq]
    have hden : 0 < 4 * ((n : ℝ) + 1) := by positivity
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith [hmpos]
  have huc : UniformContinuous V := CompactSpace.uniformContinuous_of_continuous V.continuous
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuous_iff.mp huc) ε hεpos
  refine ⟨δ, hδpos, fun p q hpq => ?_⟩
  have hdist : dist (V p) (V q) < ε := hδ hpq
  have h1 : ‖V p - V q‖ ≤ ε := by rw [dist_eq_norm] at hdist; exact hdist.le
  have h2 : cnrm2 (V p - V q) ≤ (n : ℝ) * ε ^ 2 := cnrm2_sub_le hεpos.le h1
  have h3 : m ≤ cnrm2 (V q) := by
    rw [hm]
    exact (Filter.eventually_principal.mp hp₀) q (Set.mem_univ q)
  linarith

/-- The `k`-th division point of `[0,1]` in `N` steps. -/
def tOf (N : ℕ) (k : Fin (N + 1)) : unitInterval :=
  ⟨(k : ℝ) / N, by
    rw [Set.mem_Icc]
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · rw [div_le_one (by exact_mod_cast h)]
      exact_mod_cast Nat.le_of_lt_succ k.2⟩

lemma tOf_val (N : ℕ) (k : Fin (N + 1)) : (tOf N k : ℝ) = (k : ℝ) / N := rfl

lemma tOf_zero (N : ℕ) : tOf N 0 = 0 := by ext; simp [tOf]

lemma tOf_last (N : ℕ) (hN : 0 < N) : tOf N (Fin.last N) = 1 := by
  ext
  simp [tOf, Fin.val_last, div_self (by positivity : (N : ℝ) ≠ 0)]

lemma tOf_castSucc (N : ℕ) (k : Fin N) : (tOf N k.castSucc : ℝ) = (k : ℝ) / N := rfl

lemma tOf_succ (N : ℕ) (k : Fin N) : (tOf N k.succ : ℝ) = ((k : ℝ) + 1) / N := by
  rw [tOf_val, Fin.val_succ]; push_cast; ring

/-- A sufficiently fine discrete sampling of a non-vanishing homotopy of vectors which satisfies
the uniform smallness needed to build the frame homotopy. -/
lemma exists_frame_input (V : C(C1 × unitInterval, Fin n → ℂ)) (hV : ∀ p, V p ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : Fin (N + 1) → C(C1, Fin n → ℂ),
      (∀ (k : Fin (N + 1)) (x : C1), u k x ≠ 0) ∧
      (∀ z, u 0 z = V (z, 0)) ∧
      (∀ z, u (Fin.last N) z = V (z, 1)) ∧
      ∀ (k : Fin N) (x : C1),
        4 * cnrm2 (u k.succ x - u k.castSucc x) < cnrm2 (u k.castSucc x) := by
  obtain ⟨δ, hδ, hsmall⟩ := uniform_small V hV
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : 0 < N := by
    have h1 : (0:ℝ) < 1 / δ := by positivity
    exact_mod_cast lt_trans h1 hN
  have hNd : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ (by exact_mod_cast hNpos : (0:ℝ) < N), mul_comm δ (N : ℝ)]
    rw [div_lt_iff₀ hδ] at hN
    exact hN
  refine ⟨N, hNpos, fun k => ⟨fun z => V (z, tOf N k), ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact V.continuous.comp (continuous_id.prodMk continuous_const)
  · intro k x
    exact hV (x, tOf N k)
  · intro z
    show V (z, tOf N 0) = V (z, 0)
    rw [tOf_zero]
  · intro z
    show V (z, tOf N (Fin.last N)) = V (z, 1)
    rw [tOf_last N hNpos]
  · intro k x
    have hd : dist (tOf N k.succ) (tOf N k.castSucc) = 1 / (N : ℝ) := by
      rw [Subtype.dist_eq, Real.dist_eq, tOf_succ, tOf_castSucc]
      rw [show ((k:ℝ) + 1) / N - (k:ℝ) / N = 1 / N by ring]
      rw [abs_of_pos (by positivity)]
    have hpq : dist (x, tOf N k.succ) (x, tOf N k.castSucc) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, hd]
      exact hNd
    show 4 * cnrm2 (V (x, tOf N k.succ) - V (x, tOf N k.castSucc)) <
      cnrm2 (V (x, tOf N k.castSucc))
    exact hsmall _ _ hpq

/-! ## 6. The three auxiliary statements -/

lemma cip_cauchy (u w : Fin n → ℂ) : ‖cip u w‖ ^ 2 ≤ cnrm2 u * cnrm2 w := by
  have h1 : ‖cip u w‖ ≤ ∑ j, ‖u j‖ * ‖w j‖ := by
    rw [cip]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_star]
  have h2 : (∑ j, ‖u j‖ * ‖w j‖) ^ 2 ≤ cnrm2 u * cnrm2 w := by
    rw [cnrm2, cnrm2]
    exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun j : Fin n => ‖u j‖) (fun j : Fin n => ‖w j‖)
  have h3 : ‖cip u w‖ ^ 2 ≤ (∑ j, ‖u j‖ * ‖w j‖) ^ 2 := by
    have hs : 0 ≤ ∑ j : Fin n, ‖u j‖ * ‖w j‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [norm_nonneg (cip u w), hs]
  linarith

/-- The square of the rank-one matrix `outer w u`. -/
lemma outer_sq (w u : Fin n → ℂ) :
    outer w u * outer w u = (cip u w) • outer w u := by
  ext i k
  simp only [outer, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, cip, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- If `X * X = τ • X` with `1 + τ ≠ 0` then `1 + X` is invertible. -/
lemma isUnit_one_add_of_sq_smul {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} {τ : ℂ}
    (hX : X * X = τ • X) (hc : 1 + τ ≠ 0) : IsUnit (1 + X) := by
  have hcoef : (1 : ℂ) - (1 + τ)⁻¹ - (1 + τ)⁻¹ * τ = 0 := by
    have hlam : (1 + τ)⁻¹ * (1 + τ) = 1 := inv_mul_cancel₀ hc
    linear_combination -hlam
  refine ⟨⟨1 + X, 1 - ((1 + τ)⁻¹) • X, ?_, ?_⟩, rfl⟩
  · calc (1 + X) * (1 - ((1 + τ)⁻¹) • X)
        = 1 + (X - (1 + τ)⁻¹ • X - ((1 + τ)⁻¹ * τ) • X) := by
          rw [mul_sub, mul_one, add_mul, one_mul, Matrix.mul_smul, hX, smul_smul]
          abel
      _ = 1 + ((1 : ℂ) • X - (1 + τ)⁻¹ • X - ((1 + τ)⁻¹ * τ) • X) := by rw [one_smul]
      _ = 1 + ((1 - (1 + τ)⁻¹ - (1 + τ)⁻¹ * τ) • X) := by rw [← sub_smul, ← sub_smul]
      _ = 1 := by rw [hcoef, zero_smul, add_zero]
  · calc (1 - ((1 + τ)⁻¹) • X) * (1 + X)
        = 1 + (X - (1 + τ)⁻¹ • X - ((1 + τ)⁻¹ * τ) • X) := by
          rw [sub_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, hX, smul_smul]
          abel
      _ = 1 + ((1 : ℂ) • X - (1 + τ)⁻¹ • X - ((1 + τ)⁻¹ * τ) • X) := by rw [one_smul]
      _ = 1 + ((1 - (1 + τ)⁻¹ - (1 + τ)⁻¹ * τ) • X) := by rw [← sub_smul, ← sub_smul]
      _ = 1 := by rw [hcoef, zero_smul, add_zero]

lemma norm_ofReal_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  have h : x * x = |x| ^ 2 := by rw [sq_abs, sq]
  rw [← Real.sqrt_sq (norm_nonneg (x : ℂ)), ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, h,
    Real.sqrt_sq (abs_nonneg x)]

/-- `(a • X) * (a • X) = (a * a) • (X * X)`. -/
lemma smul_mul_smul_sq {n : ℕ} (a : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    (a • X) * (a • X) = (a * a) • (X * X) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The rank-one "step" matrix is invertible under the smallness hypothesis. -/
theorem step_isUnit_smul {n : ℕ} {u w : Fin n → ℂ} (hu : u ≠ 0) (h : 4 * cnrm2 w < cnrm2 u)
    (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1) :
    IsUnit (1 + ((s : ℂ) * (cip u u)⁻¹) • outer w u) := by
  have hcu : 0 < cnrm2 u := cnrm2_pos hu
  have hcu0 : cnrm2 u ≠ 0 := ne_of_gt hcu
  have hcu' : ‖cip u u‖ = cnrm2 u := by
    rw [cip_self', norm_ofReal_eq_abs, abs_of_nonneg (cnrm2_nonneg u)]
  have hspos : ‖(s : ℂ)‖ = s := by rw [norm_ofReal_eq_abs, abs_of_nonneg hs]
  have hcw : Real.sqrt (cnrm2 u * cnrm2 w) < cnrm2 u / 2 := by
    have h4 : cnrm2 w < cnrm2 u / 4 := by linarith
    have hlt : cnrm2 u * cnrm2 w < (cnrm2 u / 2) ^ 2 := by nlinarith
    calc Real.sqrt (cnrm2 u * cnrm2 w) < Real.sqrt ((cnrm2 u / 2) ^ 2) :=
          Real.sqrt_lt_sqrt (mul_nonneg (cnrm2_nonneg u) (cnrm2_nonneg w)) hlt
      _ = cnrm2 u / 2 := Real.sqrt_sq (by linarith)
  have hcipw : ‖cip u w‖ ≤ Real.sqrt (cnrm2 u * cnrm2 w) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (cip_cauchy u w)
  have hA : (cnrm2 u)⁻¹ * ‖cip u w‖ < 1 / 2 := by
    calc (cnrm2 u)⁻¹ * ‖cip u w‖ ≤ (cnrm2 u)⁻¹ * Real.sqrt (cnrm2 u * cnrm2 w) :=
          mul_le_mul_of_nonneg_left hcipw (inv_nonneg.mpr (cnrm2_nonneg u))
      _ < (cnrm2 u)⁻¹ * (cnrm2 u / 2) := mul_lt_mul_of_pos_left hcw (inv_pos.mpr hcu)
      _ = 1 / 2 := by rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hcu0, one_mul]; norm_num
  have hbound : ‖((s : ℂ) * (cip u u)⁻¹) * cip u w‖ < 1 := by
    rw [mul_assoc, norm_mul, norm_mul, hspos, norm_inv, hcu']
    calc s * ((cnrm2 u)⁻¹ * ‖cip u w‖) ≤ 1 * ((cnrm2 u)⁻¹ * ‖cip u w‖) :=
          mul_le_mul_of_nonneg_right hs'
            (mul_nonneg (inv_nonneg.mpr (cnrm2_nonneg u)) (norm_nonneg _))
      _ < 1 := by linarith
  have hne : (1 : ℂ) + (s : ℂ) * (cip u u)⁻¹ * cip u w ≠ 0 := by
    intro h0
    have h1 : ((s : ℂ) * (cip u u)⁻¹) * cip u w = -1 := by linear_combination h0
    rw [h1, norm_neg, norm_one] at hbound
    exact lt_irrefl 1 hbound
  have hX : (((s : ℂ) * (cip u u)⁻¹) • outer w u) * (((s : ℂ) * (cip u u)⁻¹) • outer w u)
      = ((s : ℂ) * (cip u u)⁻¹ * cip u w) • (((s : ℂ) * (cip u u)⁻¹) • outer w u) := by
    have h1 : ((s : ℂ) * (cip u u)⁻¹) * ((s : ℂ) * (cip u u)⁻¹) * cip u w
        = ((s : ℂ) * (cip u u)⁻¹ * cip u w) * ((s : ℂ) * (cip u u)⁻¹) := by ring
    rw [smul_mul_smul_sq, outer_sq, smul_smul, smul_smul, h1]
  exact isUnit_one_add_of_sq_smul hX hne

/-! ### The Euclidean structure of `ℂⁿ` and the sphere models -/

/-- `ℂⁿ` with the Euclidean norm is linearly isometric to `ℝ^{2n}`. -/
noncomputable def euclideanIso (N : ℕ) :
    EuclideanSpace ℝ (Fin (2 * N)) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin N => ℂ) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      ((finProdFinEquiv.trans (finCongr (Nat.mul_comm N 2))).symm)).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (Equiv.sigmaEquivProd (Fin N) (Fin 2)).symm).trans
      ((LinearIsometryEquiv.piLpCurry ℝ 2 (fun _ : Fin N => fun _ : Fin 2 => ℝ)).trans
        (LinearIsometryEquiv.piLpCongrRight 2
          (fun _ : Fin N => (Complex.orthonormalBasisOneI.repr).symm))))

lemma toLp_ne_zero {N : ℕ} {u : Fin N → ℂ} (hu : u ≠ 0) : WithLp.toLp 2 u ≠ 0 := fun h =>
  hu (by
    have hh := congrArg WithLp.ofLp h
    simpa using hh)

lemma continuous_norm_toLp {X : Type} [TopologicalSpace X] {N : ℕ} {f : X → Fin N → ℂ}
    (hf : Continuous f) : Continuous fun x => ‖WithLp.toLp 2 (f x)‖ :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℂ)).symm.continuous.comp hf).norm

/-- The unit vector in the direction of a nonzero complex vector, seen as a point of `S^{2n-1}`. -/
noncomputable def normSph {m : ℕ} (u : Fin (m + 1) → ℂ) (hu : u ≠ 0) :
    Submission.Sphere.Sph (2 * m + 1) :=
  ⟨(‖WithLp.toLp 2 u‖)⁻¹ • (euclideanIso (m + 1)).symm (WithLp.toLp 2 u), by
    have hne : ‖WithLp.toLp 2 u‖ ≠ 0 := norm_ne_zero_iff.mpr (toLp_ne_zero hu)
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul,
      (euclideanIso (m + 1)).symm.norm_map, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hne]⟩

/-- The complex vector underlying a point of `S^{2n-1}`. -/
noncomputable def sphVec {m : ℕ} (p : Submission.Sphere.Sph (2 * m + 1)) : Fin (m + 1) → ℂ :=
  WithLp.ofLp (euclideanIso (m + 1) (p : EuclideanSpace ℝ (Fin (2 * m + 1 + 1))))

lemma continuous_sphVec {m : ℕ} :
    Continuous fun p : Submission.Sphere.Sph (2 * m + 1) => sphVec p :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℂ)).continuous.comp
    ((euclideanIso (m + 1)).continuous.comp continuous_subtype_val)

lemma sphVec_norm {m : ℕ} (p : Submission.Sphere.Sph (2 * m + 1)) :
    ‖WithLp.toLp 2 (sphVec p)‖ = 1 := by
  rw [sphVec, WithLp.toLp_ofLp, (euclideanIso (m + 1)).norm_map]
  have hp := p.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hp

lemma sphVec_ne_zero {m : ℕ} (p : Submission.Sphere.Sph (2 * m + 1)) : sphVec p ≠ 0 := by
  intro h
  have h1 := sphVec_norm p
  rw [h] at h1
  simpa using h1

lemma sphVec_normSph {m : ℕ} (u : Fin (m + 1) → ℂ) (hu : u ≠ 0) :
    sphVec (normSph u hu) = (‖WithLp.toLp 2 u‖)⁻¹ • u := by
  show WithLp.ofLp (euclideanIso (m + 1) ((‖WithLp.toLp 2 u‖)⁻¹ •
    (euclideanIso (m + 1)).symm (WithLp.toLp 2 u))) = (‖WithLp.toLp 2 u‖)⁻¹ • u
  rw [LinearIsometryEquiv.map_smul, LinearIsometryEquiv.apply_symm_apply, WithLp.ofLp_smul,
    WithLp.ofLp_toLp]

lemma continuous_normSph_coe {m : ℕ} :
    Continuous fun u : {u : Fin (m + 1) → ℂ // u ≠ 0} =>
      (normSph u.1 u.2 : EuclideanSpace ℝ (Fin (2 * m + 1 + 1))) := by
  show Continuous fun u : {u : Fin (m + 1) → ℂ // u ≠ 0} =>
      (‖WithLp.toLp 2 u.1‖)⁻¹ • (euclideanIso (m + 1)).symm (WithLp.toLp 2 u.1)
  refine (((continuous_norm_toLp continuous_subtype_val).inv₀
    (fun u => norm_ne_zero_iff.mpr (toLp_ne_zero u.2)))).smul ?_
  exact (euclideanIso (m + 1)).symm.continuous.comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℂ)).symm.continuous.comp
      continuous_subtype_val)

lemma continuous_normSph {m : ℕ} :
    Continuous fun u : {u : Fin (m + 1) → ℂ // u ≠ 0} => normSph u.1 u.2 :=
  Continuous.subtype_mk continuous_normSph_coe fun u => (normSph u.1 u.2).2

/-- The isometry `ℂ ≃ ℝ²` used to identify the two models of the circle. -/
noncomputable def isoC2 : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (1 + 1)) :=
  Complex.orthonormalBasisOneI.repr

/-- The unit circle `S¹` of `ℂ`, mapped to the unit circle of `ℝ²`. -/
noncomputable def sphC : C1 → Submission.Sphere.Sph 1 := fun z => ⟨isoC2 (z : ℂ), by
  have hz : ‖(z : ℂ)‖ = 1 := by
    have h := z.2
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, isoC2.norm_map]
  exact hz⟩

/-- The inverse of `sphC`. -/
noncomputable def cOfSph : Submission.Sphere.Sph 1 → C1 := fun p =>
  ⟨isoC2.symm (p : EuclideanSpace ℝ (Fin (1 + 1))), by
    have hp : ‖(p : EuclideanSpace ℝ (Fin (1 + 1)))‖ = 1 := by
      have h := p.2
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, isoC2.symm.norm_map]
    exact hp⟩

lemma continuous_sphC : Continuous sphC :=
  Continuous.subtype_mk (isoC2.continuous.comp continuous_subtype_val) _

lemma continuous_cOfSph : Continuous cOfSph :=
  Continuous.subtype_mk (isoC2.symm.continuous.comp continuous_subtype_val) _

lemma cOfSph_sphC (z : C1) : cOfSph (sphC z) = z := by
  apply Subtype.ext
  show isoC2.symm (isoC2 (z : ℂ)) = (z : ℂ)
  rw [isoC2.symm_apply_apply]

lemma sphC_cOfSph (p : Submission.Sphere.Sph 1) : sphC (cOfSph p) = p := by
  apply Subtype.ext
  show isoC2 (isoC2.symm (p : EuclideanSpace ℝ (Fin (1 + 1)))) =
    (p : EuclideanSpace ℝ (Fin (1 + 1)))
  rw [isoC2.apply_symm_apply]

/-- Multiplication of complex vectors by a real scalar is multiplication by the corresponding
complex number. -/
lemma real_smul_complex_smul {N : ℕ} (r : ℝ) (u : Fin N → ℂ) : r • u = (r : ℂ) • u := by
  ext i
  simp [Complex.real_smul]

/-- Any two nonzero vectors of `ℂ^N`, `N ≥ 2`, are joined by a path avoiding `0`. -/
lemma exists_path_ne_zero {N : ℕ} (a c : Fin N → ℂ) (ha : a ≠ 0) (hc : c ≠ 0) :
    ∃ γ : C(unitInterval, Fin N → ℂ), (∀ t, γ t ≠ 0) ∧ γ 0 = a ∧ γ 1 = c := by
  by_cases hdep : ∃ μ : ℂ, a = μ • c
  · obtain ⟨μ, hμ⟩ := hdep
    have hμ0 : μ ≠ 0 := fun h0 => ha (by rw [hμ, h0, zero_smul])
    let γ : unitInterval → Fin N → ℂ :=
      fun t => Complex.exp ((1 - (t : ℝ)) • Complex.log μ) • c
    have hγc : Continuous γ := by
      show Continuous fun t : unitInterval =>
        Complex.exp ((1 - (t : ℝ)) • Complex.log μ) • c
      exact (Complex.continuous_exp.comp
        ((continuous_const.sub continuous_subtype_val).smul continuous_const)).smul
        continuous_const
    refine ⟨⟨γ, hγc⟩, ?_, ?_, ?_⟩
    · intro t
      show γ t ≠ 0
      exact smul_ne_zero (Complex.exp_ne_zero _) hc
    · show γ 0 = a
      show Complex.exp ((1 - ((0 : unitInterval) : ℝ)) • Complex.log μ) • c = a
      rw [show (1 : ℝ) - ((0 : unitInterval) : ℝ) = 1 by norm_num, one_smul,
        Complex.exp_log hμ0, hμ]
    · show γ 1 = c
      show Complex.exp ((1 - ((1 : unitInterval) : ℝ)) • Complex.log μ) • c = c
      rw [show (1 : ℝ) - ((1 : unitInterval) : ℝ) = 0 by norm_num, zero_smul,
        Complex.exp_zero, one_smul]
  · let γ : unitInterval → Fin N → ℂ := fun t => (1 - (t : ℝ)) • a + (t : ℝ) • c
    have hγc : Continuous γ := by
      show Continuous fun t : unitInterval => (1 - (t : ℝ)) • a + (t : ℝ) • c
      exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
        (continuous_subtype_val.smul continuous_const)
    refine ⟨⟨γ, hγc⟩, ?_, ?_, ?_⟩
    · intro t h0
      have h0' : (1 - (t : ℝ)) • a + (t : ℝ) • c = 0 := h0
      have hne1 : (t : ℝ) ≠ 1 := by
        intro h
        exact hc (by
          have hh := h0'
          rw [h] at hh
          simpa using hh)
      have hne0 : (t : ℝ) ≠ 0 := by
        intro h
        exact ha (by
          have hh := h0'
          rw [h] at hh
          simpa using hh)
      have h1t : (1 : ℝ) - (t : ℝ) ≠ 0 := by
        intro h; exact hne1 (by linarith)
      have h2 : (1 - (t : ℝ)) • a = -((t : ℝ) • c) := add_eq_zero_iff_eq_neg.mp h0'
      have h3 : a = (((1 - (t : ℝ))⁻¹ * (-(t : ℝ))) : ℝ) • c := by
        calc a = ((1 - (t : ℝ))⁻¹ * (1 - (t : ℝ))) • a := by
              rw [inv_mul_cancel₀ h1t, one_smul]
          _ = (1 - (t : ℝ))⁻¹ • ((1 - (t : ℝ)) • a) := by rw [smul_smul]
          _ = (1 - (t : ℝ))⁻¹ • (-((t : ℝ) • c)) := by rw [h2]
          _ = (1 - (t : ℝ))⁻¹ • ((-(t : ℝ)) • c) := by rw [neg_smul]
          _ = (((1 - (t : ℝ))⁻¹ * (-(t : ℝ))) : ℝ) • c := by rw [smul_smul]
      exact hdep ⟨((((1 - (t : ℝ))⁻¹ * (-(t : ℝ))) : ℝ) : ℂ),
        by rw [h3, real_smul_complex_smul]⟩
    · show γ 0 = a
      show (1 - ((0 : unitInterval) : ℝ)) • a + ((0 : unitInterval) : ℝ) • c = a
      rw [show (1 : ℝ) - ((0 : unitInterval) : ℝ) = 1 by norm_num,
        show ((0 : unitInterval) : ℝ) = 0 by norm_num, zero_smul, add_zero, one_smul]
    · show γ 1 = c
      show (1 - ((1 : unitInterval) : ℝ)) • a + ((1 : unitInterval) : ℝ) • c = c
      rw [show (1 : ℝ) - ((1 : unitInterval) : ℝ) = 0 by norm_num,
        show ((1 : unitInterval) : ℝ) = 1 by norm_num, zero_smul, zero_add, one_smul]

/-- Any loop in `ℂ^n \ {0}` with `n ≥ 2` is null-homotopic through non-zero vectors, ending at any
prescribed non-zero direction. -/
theorem nullhomotopic_nonzero_loop {m : ℕ} (hm : 1 ≤ m) (v : C(C1, Fin (m + 1) → ℂ))
    (hv : ∀ z, v z ≠ 0) (c : Fin (m + 1) → ℂ) (hc : c ≠ 0) :
    ∃ V : C(C1 × unitInterval, Fin (m + 1) → ℂ), (∀ p, V p ≠ 0) ∧ (∀ z, V (z, 0) = v z) ∧
      ∃ r : C(C1, ℝ), (∀ z, 0 < r z) ∧ ∀ z, V (z, 1) = (r z : ℂ) • c := by
  let P : C(C1, Fin (m + 1) → ℂ) → Prop := fun f => ∀ z, f z ≠ 0
  let g0 : C(Submission.Sphere.Sph 1, Submission.Sphere.Sph (2 * m + 1)) :=
    ⟨fun p => normSph (v (cOfSph p)) (hv _),
      Continuous.subtype_mk (continuous_normSph_coe.comp
        (Continuous.subtype_mk (v.continuous.comp continuous_cOfSph) (fun p => hv _))) _⟩
  obtain ⟨y, hy⟩ := Work.Degree.nullhomotopic_of_dim_lt_sph 1 (2 * m + 1) (by omega) g0
  obtain ⟨K⟩ := hy
  have hg0 : ∀ z : C1, g0 (sphC z) = normSph (v z) (hv z) := by
    intro z
    apply Subtype.ext
    show (normSph (v (cOfSph (sphC z))) (hv _) : EuclideanSpace ℝ (Fin (2 * m + 1 + 1))) =
      (normSph (v z) (hv z) : EuclideanSpace ℝ (Fin (2 * m + 1 + 1)))
    rw [cOfSph_sphC z]
  let s : C(C1, ℝ) := ⟨fun z => ‖WithLp.toLp 2 (v z)‖,
    continuous_norm_toLp v.continuous⟩
  have hs_pos : ∀ z : C1, 0 < s z := by
    intro z
    show 0 < ‖WithLp.toLp 2 (v z)‖
    exact norm_pos_iff.mpr (toLp_ne_zero (hv z))
  let a : Fin (m + 1) → ℂ := sphVec y
  let vA : C(C1, Fin (m + 1) → ℂ) :=
    ⟨fun z => (s z) • a, s.continuous.smul continuous_const⟩
  let vC : C(C1, Fin (m + 1) → ℂ) :=
    ⟨fun z => (s z) • c, s.continuous.smul continuous_const⟩
  -- first stage: deform `v` to the constant direction `a`, following the nullhomotopy `K`
  have hH1c : Continuous fun p : unitInterval × C1 => (s p.2) • sphVec (K (p.1, sphC p.2)) :=
    (s.continuous.comp continuous_snd).smul (continuous_sphVec.comp
      (K.continuous.comp (continuous_fst.prodMk (continuous_sphC.comp continuous_snd))))
  let H1b : ContinuousMap.Homotopy v vA := ContinuousMap.Homotopy.mk
    ⟨fun p => (s p.2) • sphVec (K (p.1, sphC p.2)), hH1c⟩
    (by
      intro z
      have h1 : K (0, sphC z) = g0 (sphC z) := K.map_zero_left (sphC z)
      have hne : ‖WithLp.toLp 2 (v z)‖ ≠ 0 := norm_ne_zero_iff.mpr (toLp_ne_zero (hv z))
      show (‖WithLp.toLp 2 (v z)‖) • sphVec (K (0, sphC z)) = v z
      rw [h1, hg0 z, sphVec_normSph, smul_smul, mul_inv_cancel₀ hne, one_smul])
    (by
      intro z
      have h1 : K (1, sphC z) = ContinuousMap.const _ y (sphC z) := K.map_one_left (sphC z)
      show (s z) • sphVec (K (1, sphC z)) = vA z
      rw [h1, ContinuousMap.const_apply]
      rfl)
  let H1 : ContinuousMap.HomotopyWith v vA P :=
    { toHomotopy := H1b
      prop' := fun t => by
        intro z
        exact smul_ne_zero (ne_of_gt (hs_pos z)) (sphVec_ne_zero _) }
  -- second stage: move the constant direction `a` to `c`
  obtain ⟨γ, hγne, hγ0, hγ1⟩ := exists_path_ne_zero a c (sphVec_ne_zero y) hc
  have hH2c : Continuous fun p : unitInterval × C1 => (s p.2) • γ p.1 :=
    (s.continuous.comp continuous_snd).smul (γ.continuous.comp continuous_fst)
  let H2b : ContinuousMap.Homotopy vA vC := ContinuousMap.Homotopy.mk
    ⟨fun p => (s p.2) • γ p.1, hH2c⟩
    (by
      intro z
      show (s z) • γ 0 = vA z
      rw [hγ0]
      rfl)
    (by
      intro z
      show (s z) • γ 1 = vC z
      rw [hγ1]
      rfl)
  let H2 : ContinuousMap.HomotopyWith vA vC P :=
    { toHomotopy := H2b
      prop' := fun t => by
        intro z
        exact smul_ne_zero (ne_of_gt (hs_pos z)) (hγne t) }
  let Htot : ContinuousMap.HomotopyWith v vC P := H1.trans H2
  refine ⟨⟨fun p => Htot (prodSwap p), Htot.continuous.comp prodSwap.continuous⟩,
    ?_, ?_, s, hs_pos, ?_⟩
  · intro p
    show Htot (prodSwap p) ≠ 0
    rw [prodSwap_apply]
    have h := Htot.prop p.2 p.1
    rwa [Homotopy.curry_apply] at h
  · intro z
    show Htot (prodSwap (z, 0)) = v z
    rw [prodSwap_apply]
    exact Htot.apply_zero z
  · intro z
    show Htot (prodSwap (z, 1)) = (s z : ℂ) • c
    rw [prodSwap_apply, Htot.apply_one z]
    show (s z : ℝ) • c = (s z : ℂ) • c
    exact real_smul_complex_smul (s z) c

/-! ### Unit homotopies of matrix loops over an arbitrary space -/

/-- Two matrix loops over `X` are homotopic through invertible matrices. -/
def HomUx {X : Type} [TopologicalSpace X] {n : ℕ} (f g : C(X, Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∃ H : ContinuousMap.Homotopy f g, ∀ p : unitInterval × X, IsUnit (H p)

lemma HomUx.trans {X : Type} [TopologicalSpace X] {n : ℕ}
    {f g h : C(X, Matrix (Fin n) (Fin n) ℂ)} (H1 : HomUx f g) (H2 : HomUx g h) : HomUx f h := by
  obtain ⟨H1, h1⟩ := H1
  obtain ⟨H2, h2⟩ := H2
  refine ⟨H1.trans H2, fun p => ?_⟩
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with hp
  · exact h1 _
  · exact h2 _

/-- Left-multiplying by an interpolated loop: a unit homotopy `1 ≃ S` gives `P ≃ S * P`. -/
lemma HomUx.mul_left {X : Type} [TopologicalSpace X] {n : ℕ}
    (P : C(X, Matrix (Fin n) (Fin n) ℂ)) (hP : ∀ x, IsUnit (P x))
    {S : C(X, Matrix (Fin n) (Fin n) ℂ)}
    (H : HomUx (1 : C(X, Matrix (Fin n) (Fin n) ℂ)) S) :
    HomUx P ⟨fun x => S x * P x, S.continuous.matrix_mul P.continuous⟩ := by
  obtain ⟨H, hH⟩ := H
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨fun p => H p * P p.2, H.toContinuousMap.continuous.matrix_mul (P.continuous.comp continuous_snd)⟩
    ?_ ?_, ?_⟩
  · intro x
    have h0 : H (0, x) = (1 : C(X, Matrix (Fin n) (Fin n) ℂ)) x := H.map_zero_left x
    show H (0, x) * P x = P x
    rw [h0, ContinuousMap.one_apply, Matrix.one_mul]
  · intro x
    have h1 : H (1, x) = S x := H.map_one_left x
    show H (1, x) * P x = S x * P x
    rw [h1]
  · intro p
    exact IsUnit.mul (hH p) (hP p.2)

/-! ### The step matrix and its interpolation -/

/-- The rank-one step matrix `1 + (cip u u)⁻¹ • outer w u`. -/
def frameStepMat {n : ℕ} (u w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (cip u u)⁻¹ • outer w u

lemma frameStepMat_apply {n : ℕ} (u w : Fin n → ℂ) (i j : Fin n) :
    frameStepMat u w i j = (if i = j then 1 else 0) + (cip u u)⁻¹ * (w i * star (u j)) := by
  simp [frameStepMat, outer, cip, Matrix.one_apply]

lemma frameStepMat_mulVec {n : ℕ} {u w : Fin n → ℂ} (hu : u ≠ 0) :
    Matrix.mulVec (frameStepMat u w) u = u + w := by
  rw [frameStepMat]
  exact step_mulVec' hu

lemma frameStepMat_isUnit {n : ℕ} {u w : Fin n → ℂ} (hu : u ≠ 0)
    (h : 4 * cnrm2 w < cnrm2 u) : IsUnit (frameStepMat u w) := by
  rw [frameStepMat]
  simpa using step_isUnit_smul (u := u) (w := w) hu h 1 zero_le_one le_rfl

/-- The step matrix as a continuous family over `X`. -/
def frameStepMap {X : Type} [TopologicalSpace X] {n : ℕ} (u w : C(X, Fin n → ℂ))
    (hu : ∀ x, u x ≠ 0) :
    C(X, Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun x => frameStepMat (u x) (w x), by
    refine continuous_matrix fun i j => ?_
    rw [funext fun x => frameStepMat_apply (u x) (w x) i j]
    have hcip : Continuous fun x : X => ∑ k, star (u x k) * u x k := by
      refine continuous_finsetSum Finset.univ fun k _ => ?_
      exact (Complex.continuous_conj.comp ((continuous_apply k).comp u.continuous)).mul
        ((continuous_apply k).comp u.continuous)
    have hne : ∀ x : X, (∑ k, star (u x k) * u x k) ≠ 0 := by
      intro x
      have h : (∑ k, star (u x k) * u x k) = cip (u x) (u x) := rfl
      rw [h, cip_self']
      exact_mod_cast ne_of_gt (cnrm2_pos (hu x))
    have hw : Continuous fun x : X => w x i := (continuous_apply i).comp w.continuous
    have hu' : Continuous fun x : X => star (u x j) :=
      Complex.continuous_conj.comp ((continuous_apply j).comp u.continuous)
    exact Continuous.add continuous_const ((hcip.inv₀ hne).mul (hw.mul hu'))⟩

/-- The interpolated step family `1 + (s * (cip u u)⁻¹) • outer w u`. -/
def frameStepHomMap {X : Type} [TopologicalSpace X] {n : ℕ} (u w : C(X, Fin n → ℂ))
    (hu : ∀ x, u x ≠ 0) :
    C(unitInterval × X, Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun p => 1 + (((p.1 : ℝ) : ℂ) * (cip (u p.2) (u p.2))⁻¹) •
      outer (w p.2) (u p.2), by
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, outer, Matrix.of_apply,
      smul_eq_mul]
    have hcip : Continuous fun p : unitInterval × X => ∑ k, star (u p.2 k) * u p.2 k := by
      refine continuous_finsetSum Finset.univ fun k _ => ?_
      exact (Complex.continuous_conj.comp
        ((continuous_apply k).comp (u.continuous.comp continuous_snd))).mul
        ((continuous_apply k).comp (u.continuous.comp continuous_snd))
    have hne : ∀ p : unitInterval × X, (∑ k, star (u p.2 k) * u p.2 k) ≠ 0 := by
      intro p
      have h : (∑ k, star (u p.2 k) * u p.2 k) = cip (u p.2) (u p.2) := rfl
      rw [h, cip_self']
      exact_mod_cast ne_of_gt (cnrm2_pos (hu p.2))
    have hs : Continuous fun p : unitInterval × X => ((p.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    have hw : Continuous fun p : unitInterval × X => w p.2 i :=
      (continuous_apply i).comp (w.continuous.comp continuous_snd)
    have hu' : Continuous fun p : unitInterval × X => star (u p.2 j) :=
      Complex.continuous_conj.comp ((continuous_apply j).comp (u.continuous.comp continuous_snd))
    exact Continuous.add continuous_const ((hs.mul (hcip.inv₀ hne)).mul (hw.mul hu'))⟩

lemma frameStepHomMap_apply {X : Type} [TopologicalSpace X] {n : ℕ} (u w : C(X, Fin n → ℂ))
    (hu : ∀ x, u x ≠ 0) (p : unitInterval × X) :
    frameStepHomMap u w hu p = 1 + (((p.1 : ℝ) : ℂ) * (cip (u p.2) (u p.2))⁻¹) •
      outer (w p.2) (u p.2) := rfl

lemma frameStepHomMap_zero {X : Type} [TopologicalSpace X] {n : ℕ} (u w : C(X, Fin n → ℂ))
    (hu : ∀ x, u x ≠ 0) (x : X) : frameStepHomMap u w hu (0, x) = 1 := by
  rw [frameStepHomMap_apply]
  have h0 : (((0 : unitInterval) : ℝ) : ℂ) = 0 := by norm_num
  rw [h0, zero_mul, zero_smul, add_zero]

lemma frameStepHomMap_one {X : Type} [TopologicalSpace X] {n : ℕ} (u w : C(X, Fin n → ℂ))
    (hu : ∀ x, u x ≠ 0) (x : X) :
    frameStepHomMap u w hu (1, x) = frameStepMat (u x) (w x) := by
  rw [frameStepHomMap_apply, frameStepMat]
  have h1 : (((1 : unitInterval) : ℝ) : ℂ) = 1 := by norm_num
  rw [h1, one_mul]

/-- **Lifting a slow homotopy of non-zero vectors to a homotopy of invertible matrices.**
Let `u 0, u 1, …, u N` be continuous families of nonzero vectors over a space `X`, such that
consecutive terms are close: `4 * cnrm2 (u (k+1) - u k) < cnrm2 (u k)` for every `k < N` and every
`x : X`.  Then there is a continuous family `F` of invertible matrices with `F (·, 0) = 1` and
`Matrix.mulVec (F (·, 1)) (u 0) = u N`. -/
theorem exists_frame_homotopy {X : Type} [TopologicalSpace X] {n N : ℕ} (hN : 0 < N)
    (u : Fin (N + 1) → C(X, Fin n → ℂ)) (hu : ∀ (k : Fin (N + 1)) (x : X), u k x ≠ 0)
    (hsmall : ∀ (k : Fin N) (x : X),
      4 * cnrm2 (u k.succ x - u k.castSucc x) < cnrm2 (u k.castSucc x)) :
    ∃ F : C(X × unitInterval, Matrix (Fin n) (Fin n) ℂ), (∀ p, IsUnit (F p)) ∧
      (∀ x, F (x, 0) = 1) ∧
      (∀ x, Matrix.mulVec (F (x, 1)) (u 0 x) = u (Fin.last N) x) := by
  have hstep : ∀ k : Fin N, HomUx (1 : C(X, Matrix (Fin n) (Fin n) ℂ))
      (frameStepMap (u k.castSucc) (u k.succ - u k.castSucc) (fun x => hu k.castSucc x)) := by
    intro k
    refine ⟨ContinuousMap.Homotopy.mk
      (frameStepHomMap (u k.castSucc) (u k.succ - u k.castSucc) (fun x => hu k.castSucc x))
      ?_ ?_, ?_⟩
    · intro x
      show (frameStepHomMap (u k.castSucc) (u k.succ - u k.castSucc)
        (fun x => hu k.castSucc x)) (0, x) = (1 : C(X, Matrix (Fin n) (Fin n) ℂ)) x
      rw [frameStepHomMap_zero, ContinuousMap.one_apply]
    · intro x
      show (frameStepHomMap (u k.castSucc) (u k.succ - u k.castSucc)
        (fun x => hu k.castSucc x)) (1, x) =
        (frameStepMap (u k.castSucc) (u k.succ - u k.castSucc) (fun x => hu k.castSucc x)) x
      rw [frameStepHomMap_one]
      rfl
    · intro p
      have ht0 : (0:ℝ) ≤ (p.1 : ℝ) := p.1.2.1
      have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
      have hs := hsmall k p.2
      exact step_isUnit_smul (hu k.castSucc p.2) hs (p.1 : ℝ) ht0 ht1
  have key : ∀ k : Fin (N + 1), ∃ P : C(X, Matrix (Fin n) (Fin n) ℂ),
      (∀ x, IsUnit (P x)) ∧ (∀ x, Matrix.mulVec (P x) (u 0 x) = u k x) ∧
      HomUx (1 : C(X, Matrix (Fin n) (Fin n) ℂ)) P := by
    intro k
    refine Fin.induction ?base ?step k
    · refine ⟨1, fun x => isUnit_one, ?_, ?_⟩
      · intro x
        rw [ContinuousMap.one_apply, Matrix.one_mulVec]
      · exact ⟨ContinuousMap.Homotopy.refl 1, fun p => isUnit_one⟩
    · intro k ih
      obtain ⟨P, hPunit, hPact, hPhom⟩ := ih
      refine ⟨⟨fun x => frameStepMat (u k.castSucc x) (u k.succ x - u k.castSucc x) * P x,
        (frameStepMap (u k.castSucc) (u k.succ - u k.castSucc)
          (fun x => hu k.castSucc x)).continuous.matrix_mul P.continuous⟩, ?_, ?_, ?_⟩
      · intro x
        exact IsUnit.mul (frameStepMat_isUnit (hu k.castSucc x) (hsmall k x)) (hPunit x)
      · intro x
        change Matrix.mulVec (frameStepMat (u k.castSucc x) (u k.succ x - u k.castSucc x) * P x)
          (u 0 x) = u k.succ x
        rw [← Matrix.mulVec_mulVec, hPact x, frameStepMat_mulVec (hu k.castSucc x),
          add_sub_cancel]
      · exact HomUx.trans hPhom (HomUx.mul_left P hPunit (hstep k))
  obtain ⟨P, hPunit, hPact, HF, hHF⟩ := key (Fin.last N)
  refine ⟨⟨fun p => HF (p.2, p.1),
    HF.toContinuousMap.continuous.comp (continuous_snd.prodMk continuous_fst)⟩, ?_, ?_, ?_⟩
  · intro p
    exact hHF (p.2, p.1)
  · intro x
    have h0 := HF.map_zero_left x
    simp only [ContinuousMap.one_apply] at h0
    exact h0
  · intro x
    have h1 : HF (1, x) = P x := HF.map_one_left x
    show Matrix.mulVec (HF (1, x)) (u 0 x) = u (Fin.last N) x
    rw [h1]
    exact hPact x

/-! ## 7. The induction -/

/-! ## 8. The inductive step of the block decomposition -/

/-- Entry formula for the inverse block reindexing. -/
lemma blkE_symm_apply (m : ℕ) (Y : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℂ)
    (i j : Fin (m + 1)) :
    (blkE m).symm Y i j = Y ((eSum m).symm i) ((eSum m).symm j) := by
  have h := blkE_apply m ((blkE m).symm Y) ((eSum m).symm i) ((eSum m).symm j)
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm

/-- `blk` is continuous in its three matrix arguments. -/
lemma continuous_blk {m : ℕ} {X : Type} [TopologicalSpace X] (μ : X → Matrix (Fin 1) (Fin 1) ℂ)
    (b : X → Matrix (Fin 1) (Fin m) ℂ) (A : X → Matrix (Fin m) (Fin m) ℂ)
    (hμ : Continuous μ) (hb : Continuous b) (hA : Continuous A) :
    Continuous fun x => blk m (μ x) (b x) (A x) := by
  have h1 : Continuous fun x => Matrix.fromBlocks (μ x) (b x) 0 (A x) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simpa only [Matrix.fromBlocks_apply₁₁] using hμ.matrix_elem i j
    · simpa only [Matrix.fromBlocks_apply₁₂] using hb.matrix_elem i j
    · simpa only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using continuous_const
    · simpa only [Matrix.fromBlocks_apply₂₂] using hA.matrix_elem i j
  have h2 : Continuous fun x => (blkE m).symm (Matrix.fromBlocks (μ x) (b x) 0 (A x)) := by
    refine continuous_matrix fun i j => ?_
    simp only [blkE_symm_apply]
    exact h1.matrix_elem ((eSum m).symm i) ((eSum m).symm j)
  exact h2

/-- A unit homotopy of matrix loops gives a non-vanishing homotopy of determinant loops. -/
lemma HomU.detLoop {n : ℕ} {f g : C(C1, Matrix (Fin n) (Fin n) ℂ)} (h : HomU f g) :
    LoopHom (detLoop f) (detLoop g) := by
  obtain ⟨H, hH⟩ := h
  refine ⟨ContinuousMap.Homotopy.mk ⟨fun p => (H p).det, H.toContinuousMap.continuous.matrix_det⟩
    ?_ ?_, fun p => ?_⟩
  · intro z
    exact congrArg Matrix.det (H.map_zero_left z)
  · intro z
    exact congrArg Matrix.det (H.map_one_left z)
  · have h1 : IsUnit (H p).det := by
      have h2 : IsUnit (H p) := hH p
      rwa [Matrix.isUnit_iff_isUnit_det] at h2
    exact isUnit_iff_ne_zero.mp h1

lemma LoopHom.symm {f g : C(C1, ℂ)} (h : LoopHom f g) : LoopHom g f := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H.symm, fun p => ?_⟩
  rw [ContinuousMap.Homotopy.symm_apply]
  exact hH _

lemma nullH_detLoop {n : ℕ} {f : C(C1, Matrix (Fin n) (Fin n) ℂ)} (h : NullH f) :
    NullLoop (detLoop f) := by
  have h3 : detLoop (1 : C(C1, Matrix (Fin n) (Fin n) ℂ)) = 1 := by
    ext z
    exact Matrix.det_one
  have h4 := HomU.detLoop h
  rw [h3] at h4
  exact h4

lemma cmul_one_right {n : ℕ} (f : C(C1, Matrix (Fin n) (Fin n) ℂ)) : cmul f 1 = f := by
  ext z
  simp [cmul]

lemma cmul_one_left {n : ℕ} (f : C(C1, Matrix (Fin n) (Fin n) ℂ)) : cmul 1 f = f := by
  ext z
  simp [cmul]

lemma HomU.congr {n : ℕ} {f g f' g' : C(C1, Matrix (Fin n) (Fin n) ℂ)} (h1 : f = f')
    (h2 : g = g') (h : HomU f g) : HomU f' g' := by
  rw [← h1, ← h2]
  exact h

/-- Continuity of the `1 × 1` block. -/
lemma continuous_oneByOne {X : Type} [TopologicalSpace X] {c : X → ℝ} (hc : Continuous c) :
    Continuous fun x => oneByOne ((c x : ℝ) : ℂ) := by
  refine continuous_matrix fun i j => ?_
  exact Complex.continuous_ofReal.comp hc

/-- The inductive statement. -/
def P (n : ℕ) : Prop :=
  ∀ g : C(C1, Matrix (Fin n) (Fin n) ℂ), (∀ z, IsUnit (g z)) → NullLoop (detLoop g) → NullH g

lemma P_zero : P 0 := by
  intro g hg hnl
  have hg1 : g = 1 := ContinuousMap.ext fun z => Subsingleton.elim _ _
  subst hg1
  exact ⟨ContinuousMap.Homotopy.refl 1, fun p => isUnit_one⟩

lemma P_one : P 1 := by
  intro g hg hnl
  obtain ⟨Hd, hHd⟩ := hnl
  let F : unitInterval × C1 → Matrix (Fin 1) (Fin 1) ℂ := fun p => Matrix.of fun _ _ => Hd p
  have hFc : Continuous F := by
    refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun p : unitInterval × C1 => Hd p := Hd.toContinuousMap.continuous
    simpa [F, Matrix.of_apply] using h1
  refine ⟨ContinuousMap.Homotopy.mk ⟨F, hFc⟩ ?_ ?_, ?_⟩
  · intro z
    have h := Hd.map_zero_left z
    simp only [detLoop, ContinuousMap.coe_mk] at h
    rw [Matrix.det_fin_one] at h
    ext i j
    have hi : i = 0 := Subsingleton.elim i (0 : Fin 1)
    have hj : j = 0 := Subsingleton.elim j (0 : Fin 1)
    subst hi; subst hj
    simpa [F, Matrix.of_apply] using h
  · intro z
    have h := Hd.map_one_left z
    simp only [ContinuousMap.one_apply] at h
    ext i j
    have hi : i = 0 := Subsingleton.elim i (0 : Fin 1)
    have hj : j = 0 := Subsingleton.elim j (0 : Fin 1)
    subst hi; subst hj
    simpa [F, Matrix.of_apply, Matrix.one_apply] using h
  · intro p
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
    exact isUnit_iff_ne_zero.mpr (hHd p)

lemma P_step (m : ℕ) (hm : 1 ≤ m) (ih : P m)
    (g : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) (hg : ∀ z, IsUnit (g z))
    (hnl : NullLoop (detLoop g)) : NullH g := by
  -- the first column of `g` is a loop in `ℂ^{m+1} \ {0}`
  let v : C(C1, Fin (m + 1) → ℂ) :=
    ⟨fun z => Matrix.mulVec (g z) (e0 (m + 1)), g.continuous.matrix_mulVec continuous_const⟩
  have hv : ∀ z, v z ≠ 0 := fun z => mulVec_e0_ne_zero (hg z)
  obtain ⟨V, hVne, hV0, r, hrpos, hV1⟩ :=
    nullhomotopic_nonzero_loop hm v hv (e0 (m + 1)) (e0_ne_zero m)
  obtain ⟨N, hN, u, hu, hu0, huN, hsmall⟩ := exists_frame_input V hVne
  obtain ⟨F, hFunit, hF0, hF1⟩ := exists_frame_homotopy hN u hu hsmall
  -- the deformed loop `G = F(·,1) * g`
  let G : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
    ⟨fun z => F (z, 1) * g z,
      (F.continuous.comp (continuous_id.prodMk continuous_const)).matrix_mul g.continuous⟩
  let F1 : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
    ⟨fun z => F (z, 1), F.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hGg : HomU g G := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × C1 => F (p.2, p.1) * g p.2, ?_⟩ ?_ ?_, ?_⟩
    · exact (F.continuous.comp prodSwap.continuous).matrix_mul (g.continuous.comp continuous_snd)
    · intro z
      show F (z, 0) * g z = g z
      rw [hF0 z, Matrix.one_mul]
    · intro z
      show F (z, 1) * g z = G z
      rfl
    · intro p
      exact IsUnit.mul (hFunit (p.2, p.1)) (hg p.2)
  have hcol : ∀ z, Matrix.mulVec (G z) (e0 (m + 1)) = (r z : ℂ) • e0 (m + 1) := by
    intro z
    calc Matrix.mulVec (G z) (e0 (m + 1))
        = Matrix.mulVec (F (z, 1)) (Matrix.mulVec (g z) (e0 (m + 1))) := by
          show Matrix.mulVec (F (z, 1) * g z) (e0 (m + 1)) = _
          rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (F (z, 1)) (v z) := rfl
      _ = Matrix.mulVec (F (z, 1)) (u 0 z) := by
          rw [show v z = u 0 z from (hV0 z).symm.trans (hu0 z).symm]
      _ = u (Fin.last N) z := hF1 z
      _ = V (z, 1) := huN z
      _ = (r z : ℂ) • e0 (m + 1) := hV1 z
  -- the determinant of `G` is null-homotopic
  have h1F1 : HomU (1 : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) F1 := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × C1 => F (p.2, p.1), F.continuous.comp prodSwap.continuous⟩
      ?_ ?_, ?_⟩
    · intro z
      show F (z, 0) = (1 : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) z
      rw [hF0 z, ContinuousMap.one_apply]
    · intro z
      show F (z, 1) = F1 z
      rfl
    · intro p
      exact hFunit (p.2, p.1)
  have hF1nl : NullLoop (detLoop F1) := by
    have h := h1F1.detLoop
    have h3 : detLoop (1 : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) = 1 := by
      ext z
      exact Matrix.det_one
    rw [h3] at h
    exact h.symm
  have hnlG : NullLoop (detLoop G) :=
    NullLoop.of_mul hF1nl hnl (fun z => by
      show (F (z, 1) * g z).det = (F (z, 1)).det * (g z).det
      rw [Matrix.det_mul])
  -- the block decomposition of `G`
  let A : C(C1, Matrix (Fin m) (Fin m) ℂ) :=
    ⟨fun z => Matrix.of fun i j => G z i.succ j.succ, by
      refine continuous_matrix fun i j => ?_
      exact G.continuous.matrix_elem i.succ j.succ⟩
  let bmat : C(C1, Matrix (Fin 1) (Fin m) ℂ) :=
    ⟨fun z => Matrix.of fun _ j => G z 0 j.succ, by
      refine continuous_matrix fun i j => ?_
      exact G.continuous.matrix_elem 0 j.succ⟩
  have hGblk : ∀ z, G z = blk m (oneByOne (r z)) (bmat z) (A z) :=
    fun z => eq_blk_of_firstCol (G z) (r z) (hcol z)
  have hGdet : ∀ z, (G z).det = (r z) * (A z).det := by
    intro z
    rw [hGblk z, blk_det, oneByOne_det]
  have hAunit : ∀ z, IsUnit (A z) := by
    intro z
    have h1 : IsUnit (blk m (oneByOne (r z)) (bmat z) (A z)) := by
      rw [← hGblk z]
      exact IsUnit.mul (hFunit (z, 1)) (hg z)
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr ((blk_isUnit_iff (r z) (bmat z) (A z)).mp h1).2
  have hAdet : NullLoop (detLoop A) := by
    have hAexp : ∀ z, (A z).det = ((r z : ℂ))⁻¹ * (G z).det := by
      intro z
      rw [hGdet z, ← mul_assoc,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hrpos z))), one_mul]
    let finv : C(C1, ℂ) := ⟨fun z => ((r z : ℂ))⁻¹,
      (Complex.continuous_ofReal.comp r.continuous).inv₀
        (fun z => Complex.ofReal_ne_zero.mpr (ne_of_gt (hrpos z)))⟩
    have hfinv : NullLoop finv := nullLoop_inv_pos r hrpos finv (fun z => rfl)
    exact NullLoop.of_mul hfinv hnlG (fun z => by
      show (A z).det = ((r z : ℂ))⁻¹ * (G z).det
      rw [hAexp z])
  obtain ⟨HA, hHA⟩ := ih A hAunit hAdet
  -- the block decomposition as a product of two block matrices
  let S : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
    ⟨fun z => blk m (oneByOne (r z)) 0 1,
      continuous_blk (fun z => oneByOne ((r z : ℝ) : ℂ))
        (fun _ : C1 => (0 : Matrix (Fin 1) (Fin m) ℂ))
        (fun _ : C1 => (1 : Matrix (Fin m) (Fin m) ℂ))
        (continuous_oneByOne r.continuous) continuous_const continuous_const⟩
  let Blk1 : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
    ⟨fun z => blk m 1 (bmat z) (A z),
      continuous_blk (fun _ : C1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (fun z => bmat z)
        (fun z => A z) continuous_const bmat.continuous A.continuous⟩
  let Apr : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
    ⟨fun z => blk m 1 0 (A z),
      continuous_blk (fun _ : C1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (fun _ : C1 => (0 : Matrix (Fin 1) (Fin m) ℂ)) (fun z => A z)
        continuous_const continuous_const A.continuous⟩
  have hG1eq : ∀ z, G z = Blk1 z * S z := by
    intro z
    rw [hGblk z]
    change blk m (oneByOne (r z)) (bmat z) (A z) =
      blk m (1 : Matrix (Fin 1) (Fin 1) ℂ) (bmat z) (A z) * blk m (oneByOne (r z)) 0 1
    rw [blk_mul]
    simp [Matrix.one_mul, Matrix.mul_one]
  have hG_Blk1S : G = cmul Blk1 S := ContinuousMap.ext fun z => hG1eq z
  -- killing the off-diagonal block `bmat`
  have hBlk1 : HomU Blk1 Apr := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × C1 => blk m (1 : Matrix (Fin 1) (Fin 1) ℂ)
        (((1 - (p.1 : ℝ)) : ℝ) • bmat p.2) (A p.2), ?_⟩ ?_ ?_, ?_⟩
    · exact continuous_blk (fun _ : unitInterval × C1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (fun p : unitInterval × C1 => ((1 - (p.1 : ℝ)) : ℝ) • bmat p.2)
        (fun p : unitInterval × C1 => A p.2) continuous_const
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (bmat.continuous.comp continuous_snd)) (A.continuous.comp continuous_snd)
    · intro z
      show blk m 1 (((1 - ((0 : unitInterval) : ℝ)) : ℝ) • bmat z) (A z) = Blk1 z
      rw [show (1 : ℝ) - ((0 : unitInterval) : ℝ) = 1 by norm_num, one_smul]
      rfl
    · intro z
      show blk m 1 (((1 - ((1 : unitInterval) : ℝ)) : ℝ) • bmat z) (A z) = Apr z
      rw [show (1 : ℝ) - ((1 : unitInterval) : ℝ) = 0 by norm_num, zero_smul]
      rfl
    · intro p
      show IsUnit (blk m (1 : Matrix (Fin 1) (Fin 1) ℂ)
        (((1 - (p.1 : ℝ)) : ℝ) • bmat p.2) (A p.2))
      rw [← oneByOne_one]
      have hA' : IsUnit (A p.2).det := by
        have h2 : IsUnit (A p.2) := hAunit p.2
        rwa [Matrix.isUnit_iff_isUnit_det] at h2
      exact (blk_isUnit_iff (1 : ℂ) (((1 - (p.1 : ℝ)) : ℝ) • bmat p.2) (A p.2)).mpr
        ⟨one_ne_zero, isUnit_iff_ne_zero.mp hA'⟩
  -- the scalar block is homotopic to `1`
  have hS : HomU S 1 := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × C1 =>
        blk m (oneByOne (((1 - (p.1 : ℝ)) * r p.2 + (p.1 : ℝ) : ℝ))) 0 1, ?_⟩ ?_ ?_, ?_⟩
    · refine continuous_blk
        (fun p : unitInterval × C1 => oneByOne (((1 - (p.1 : ℝ)) * r p.2 + (p.1 : ℝ) : ℝ)))
        (fun _ : unitInterval × C1 => (0 : Matrix (Fin 1) (Fin m) ℂ))
        (fun _ : unitInterval × C1 => (1 : Matrix (Fin m) (Fin m) ℂ)) ?_ continuous_const
        continuous_const
      exact continuous_oneByOne
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (r.continuous.comp continuous_snd)).add
          (continuous_subtype_val.comp continuous_fst))
    · intro z
      show blk m (oneByOne (((1 - ((0 : unitInterval) : ℝ)) * r z +
        ((0 : unitInterval) : ℝ) : ℝ))) 0 1 = S z
      rw [show (1 : ℝ) - ((0 : unitInterval) : ℝ) = 1 by norm_num,
        show ((0 : unitInterval) : ℝ) = 0 by norm_num, one_mul, add_zero]
      rfl
    · intro z
      show blk m (oneByOne (((1 - ((1 : unitInterval) : ℝ)) * r z +
        ((1 : unitInterval) : ℝ) : ℝ))) 0 1 =
        (1 : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) z
      rw [show (1 : ℝ) - ((1 : unitInterval) : ℝ) = 0 by norm_num,
        show ((1 : unitInterval) : ℝ) = 1 by norm_num, zero_mul, zero_add]
      rw [show ((1 : ℝ) : ℂ) = 1 by norm_num, oneByOne_one, blk_one,
        ContinuousMap.one_apply]
    · intro p
      show IsUnit (blk m (oneByOne (((1 - (p.1 : ℝ)) * r p.2 + (p.1 : ℝ) : ℝ))) 0 1)
      rw [blk_isUnit_iff]
      exact ⟨Complex.ofReal_ne_zero.mpr
        (ne_of_gt (one_sub_mul_add_pos p.1.2.1 p.1.2.2 (hrpos p.2))), by simp⟩
  -- the `A` block is homotopic to `1` by the induction hypothesis
  have hApr : HomU Apr 1 := by
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p : unitInterval × C1 => blk m (1 : Matrix (Fin 1) (Fin 1) ℂ)
        (0 : Matrix (Fin 1) (Fin m) ℂ) (HA (p.1, p.2)), ?_⟩ ?_ ?_, ?_⟩
    · exact continuous_blk (fun _ : unitInterval × C1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (fun _ : unitInterval × C1 => (0 : Matrix (Fin 1) (Fin m) ℂ))
        (fun p : unitInterval × C1 => HA (p.1, p.2)) continuous_const continuous_const HA.continuous
    · intro z
      show blk m 1 0 (HA (0, z)) = Apr z
      rw [show HA (0, z) = A z from HA.map_zero_left z]
      rfl
    · intro z
      show blk m 1 0 (HA (1, z)) = (1 : C(C1, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) z
      rw [show HA (1, z) = (1 : C(C1, Matrix (Fin m) (Fin m) ℂ)) z from HA.map_one_left z,
        ContinuousMap.one_apply, blk_one, ContinuousMap.one_apply]
    · intro p
      show IsUnit (blk m (1 : Matrix (Fin 1) (Fin 1) ℂ)
        (0 : Matrix (Fin 1) (Fin m) ℂ) (HA (p.1, p.2)))
      rw [← oneByOne_one]
      have hA' : IsUnit (HA (p.1, p.2)).det := by
        have h2 : IsUnit (HA (p.1, p.2)) := hHA (p.1, p.2)
        rwa [Matrix.isUnit_iff_isUnit_det] at h2
      exact (blk_isUnit_iff (1 : ℂ) (0 : Matrix (Fin 1) (Fin m) ℂ) (HA (p.1, p.2))).mpr
        ⟨one_ne_zero, isUnit_iff_ne_zero.mp hA'⟩
  have hAlast : HomU (cmul Blk1 S) Apr :=
    HomU.congr rfl (cmul_one_right Apr) (HomU.mul hBlk1 hS)
  have hgG1 : HomU g (cmul Blk1 S) := by
    rw [← hG_Blk1S]
    exact hGg
  exact HomU.trans hgG1 (HomU.trans hAlast hApr)


lemma P_all (n : ℕ) : P n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n'
    · exact P_zero
    · rcases n' with _ | n''
      · exact P_one
      · exact P_step (n'' + 1) (by omega) (ih (n'' + 1) (by omega))

/-- A loop `f : S¹ → GL_n(ℂ)` whose determinant has a continuous logarithm is nullhomotopic
through invertible matrices.  Equivalently, `det : π₁(GL_n(ℂ)) → π₁(ℂ*) = ℤ` is injective. -/
theorem loop_GL_nullhomotopic_of_det_log (n : ℕ)
    (f : C(Metric.sphere (0 : ℂ) 1, Matrix (Fin n) (Fin n) ℂ))
    (hf : ∀ z, IsUnit (f z))
    (h : ∃ F : C(Metric.sphere (0 : ℂ) 1, ℂ), ∀ z, Complex.exp (F z) = Matrix.det (f z)) :
    ∃ H : C(Metric.sphere (0 : ℂ) 1 × unitInterval, Matrix (Fin n) (Fin n) ℂ),
      (∀ p, IsUnit (H p)) ∧ (∀ z, H (z, 0) = f z) ∧ (∀ z, H (z, 1) = 1) := by
  have hnl : NullLoop (detLoop f) := NullLoop.of_log h
  obtain ⟨H, hH⟩ := P_all n f hf hnl
  refine ⟨H.toContinuousMap.comp prodSwap, ?_, ?_, ?_⟩
  · intro p; exact hH (p.2, p.1)
  · intro z
    show H.toContinuousMap (prodSwap (z, 0)) = f z
    rw [prodSwap_apply]
    exact H.map_zero_left z
  · intro z
    show H.toContinuousMap (prodSwap (z, 1)) = 1
    rw [prodSwap_apply]
    exact H.map_one_left z

end

end Work.KT.Dim2
