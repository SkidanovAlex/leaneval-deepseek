/-
  Area E7, auxiliary: the kernel of the fibre Jacobian at a fibre-critical point.

  Context.  On a `Good` stratum `S` with `S.j = j` the fibre derivatives `∂_y h` (rows indexed by
  `Fin j`, columns by the `q` fibre coordinates) have rank `j` at every point of the stratum; the
  fibre-critical set of the coordinate `y_l` is the locus where all `(j+1)×(j+1)` minors of the
  matrix `[∂_y h ; e_l]` vanish (`Work.WilE7.critMinor`, see `FiberCutDefs`).

  This file proves the linear-algebra content of that step, transported to exp-affine polynomials:

    if all `(j+1)×(j+1)` minors of `[∂_y h(z) ; e_l(z)]` vanish at `z`, and `∂_y h(z)` has full row
    rank `j`, then `y_l` is a linear combination of the `h_a` in the fibre directions: every `v` in
    the kernel of the row matrix `(∂_{y_{l'}} h_a(z))` satisfies `v l = 0`.

  Mathematically: the vanishing of all maximal minors of `R := [A ; e_l]` forces `rank R ≤ j`, so
  `rank R = rank A = j`; the first `j` rows then span the whole row space, hence `e_l` lies in their
  span, and orthogonality to the rows of `A` propagates to `e_l`.

  The purely linear-algebraic ingredient — "a matrix of full row rank has a nonvanishing maximal
  minor" — is proved here as `existsMinorNeZero_of_fullRowRank`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic
import Submission.Work.WilE7.FiberCutDefs

set_option autoImplicit false
noncomputable section
open Classical WilkiesDesign WilkiesDesign.E
namespace Work.WilE7.Aux

/-! ### The linear-algebraic ingredient -/

/-- **A matrix of full row rank has a nonvanishing maximal minor.**  If `R : Matrix (Fin n) (Fin q) ℝ`
has `rank = n` then its columns span a space of dimension `n`, hence contain `n` linearly
independent vectors: the corresponding `n × n` submatrix is nonsingular. -/
private theorem existsMinorNeZero_of_fullRowRank {n q : ℕ} (R : Matrix (Fin n) (Fin q) ℝ)
    (hrank : R.rank = n) : ∃ σ : Fin n → Fin q, (R.submatrix id σ).det ≠ 0 := by
  have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range R.col)) = n := by
    rw [← Matrix.rank_eq_finrank_span_cols (A := R)]
    exact hrank
  obtain ⟨f, hf_mem, -, hf_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range R.col)
  let e := finCongr hfr
  let g : Fin n → (Fin n → ℝ) := fun i => f (e.symm i)
  have hg_mem : ∀ i, g i ∈ Set.range R.col := fun i => hf_mem (e.symm i)
  have hg_li : LinearIndependent ℝ g := by
    have h := hf_li.comp e.symm e.symm.injective
    simpa [g, Function.comp_def] using h
  choose σ hσ using hg_mem
  refine ⟨σ, ?_⟩
  have hcol : (R.submatrix id σ).col = g := by
    funext i a
    simpa [Matrix.col] using congrFun (hσ i) a
  have hli : LinearIndependent ℝ (R.submatrix id σ).col := hcol.symm ▸ hg_li
  have hns : (R.submatrix id σ).Nonsingular := Matrix.Nonsingular.of_linearIndependent_col hli
  exact (Matrix.nonsingular_iff_det_ne_zero (A := R.submatrix id σ)).mp hns

/-- If every `(j+1)×(j+1)` minor of `R` vanishes and the first `j` rows of `R` have rank `j`, then
the last row of `R` lies in the span of the first `j` rows; equivalently, any vector orthogonal to
the first `j` rows is orthogonal to the last row. -/
private theorem kerOfVanishCritMinors {j q : ℕ} (R : Matrix (Fin (j+1)) (Fin q) ℝ)
    (hmin : ∀ σ : Fin (j+1) → Fin q, (R.submatrix id σ).det = 0)
    (hrank : (R.submatrix Fin.castSucc id).rank = j) :
    ∀ v : Fin q → ℝ,
      (∀ a : Fin j, ∑ l', R (Fin.castSucc a) l' * v l' = 0) →
      ∑ l', R (Fin.last j) l' * v l' = 0 := by
  intro v hv
  -- A nonvanishing maximal minor would contradict `hmin`, so `rank R ≤ j`.
  have hle : R.rank ≤ j := by
    by_contra hcon
    push_neg at hcon
    have hcard : R.rank = j + 1 := le_antisymm R.rank_le_height (by omega)
    obtain ⟨σ, hσ⟩ := existsMinorNeZero_of_fullRowRank R hcard
    exact hσ (hmin σ)
  have hA : (R.submatrix Fin.castSucc id).rank ≤ R.rank :=
    Matrix.rank_submatrix_le R Fin.castSucc id
  have hReq : R.rank = j := by
    have hj : j ≤ R.rank := by simpa [hrank] using hA
    exact le_antisymm hle hj
  -- Hence the row spaces of `R` and of its first `j` rows coincide.
  have hsub : Submodule.span ℝ (Set.range (R.submatrix Fin.castSucc id).row) ≤
      Submodule.span ℝ (Set.range R.row) := by
    apply Submodule.span_mono
    rintro x ⟨a, rfl⟩
    exact ⟨Fin.castSucc a, rfl⟩
  have heq : Submodule.span ℝ (Set.range (R.submatrix Fin.castSucc id).row) =
      Submodule.span ℝ (Set.range R.row) := by
    refine Submodule.eq_of_le_of_finrank_eq hsub ?_
    rw [← Matrix.rank_eq_finrank_span_row (A := R.submatrix Fin.castSucc id),
        ← Matrix.rank_eq_finrank_span_row (A := R), hrank, hReq]
  have hmem : R.row (Fin.last j) ∈
      Submodule.span ℝ (Set.range (R.submatrix Fin.castSucc id).row) := by
    rw [heq]
    exact Submodule.subset_span ⟨Fin.last j, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hdot : ∀ l', R (Fin.last j) l' = ∑ a : Fin j, c a * R (Fin.castSucc a) l' := by
    intro l'
    have h1 := congrFun hc l'
    simp only [Matrix.row, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    exact h1.symm
  calc ∑ l' : Fin q, R (Fin.last j) l' * v l'
      = ∑ l' : Fin q, (∑ a : Fin j, c a * R (Fin.castSucc a) l') * v l' := by
        refine Finset.sum_congr rfl (fun l' _ => by rw [hdot l'])
    _ = ∑ a : Fin j, c a * ∑ l' : Fin q, R (Fin.castSucc a) l' * v l' := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l' _ => by ring)
    _ = 0 := by
        refine Finset.sum_eq_zero (fun a _ => ?_)
        rw [hv a, mul_zero]

/-! ### Elementary evaluations of the operators -/

/-- The derivative of a coordinate function at a fibre direction: `∂_{y_{l'}} y_l = δ_{l l'}`. -/
private theorem eaEval_eaD_X_inl {k r : ℕ} (c : EAChain k r) (i j : Fin k) (z : Fin k → ℝ) :
    eaEval c (eaD c i (MvPolynomial.X (Sum.inl j))) z = if i = j then 1 else 0 := by
  rw [eaD]
  have hsum : (∑ k' : Fin r, MvPolynomial.C (c.a k' i) * MvPolynomial.X (Sum.inr k') *
      MvPolynomial.pderiv (Sum.inr k') (MvPolynomial.X (Sum.inl j))) = 0 := by
    apply Finset.sum_eq_zero
    intro k' _
    rw [MvPolynomial.pderiv_X_of_ne (i := Sum.inr k') (j := Sum.inl j) (by simp)]
    simp
  rw [hsum, add_zero, MvPolynomial.pderiv_X]
  simp [eaEval, Pi.single_apply, Sum.inl.injEq, eq_comm]

/-- `Fin.lastCases` is determined by its value on the last index and on the castSucc indices. -/
private theorem lastCases_apply_eq {n : ℕ} {α : Sort*} (x : α) (f : Fin n → α) (d : Fin (n+1) → α)
    (hx : d (Fin.last n) = x) (hf : ∀ i, d (Fin.castSucc i) = f i) (i : Fin (n+1)) :
    Fin.lastCases x f i = d i := by
  have : (fun i => Fin.lastCases x f i) = d := by
    funext i
    induction i using Fin.lastCases with
    | last => rw [Fin.lastCases_last, hx]
    | cast i => rw [Fin.lastCases_castSucc, hf i]
  exact congrFun this i

/-- `detOp` evaluated at a point is the determinant of the matrix of evaluated mixed derivatives,
indexed by a single map `d` of directions. -/
private theorem eaEval_detOp' {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (d : Fin (j+1) → Fin k) (f : EAPoly k r) (z : Fin k → ℝ) :
    eaEval c (detOp c h (fun b : Fin j => d (Fin.castSucc b)) (d (Fin.last j)) f) z =
      (Matrix.of fun (a b : Fin (j+1)) => eaEval c (eaD c (d b) (Fin.lastCases f h a)) z).det := by
  rw [Work.WilE5.eaEval_detOp]
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [lastCases_apply_eq (d (Fin.last j)) (fun b : Fin j => d (Fin.castSucc b)) d rfl (fun i => rfl) b]

/-! ### The evaluation matrix of the critical minors -/

/-- The `a`-th row of the matrix `[∂_y h ; y_l]` evaluated at `z`, as a function of the fibre
direction `l'`: the mixed derivatives `∂_{y_{l'}} h_a(z)` for `a : Fin j`, and `∂_{y_{l'}} y_l`
for the last row. -/
private def rowVec {p q j r : ℕ} (c : EAChain (p+q) r) (h : Fin j → EAPoly (p+q) r) (l : Fin q)
    (z : Fin (p+q) → ℝ) (a : Fin (j+1)) : Fin q → ℝ :=
  fun l' => eaEval c (eaD c (Work.WilE5.yDir p l')
    (Fin.lastCases (MvPolynomial.X (Sum.inl (Work.WilE5.yDir p l))) h a)) z

/-- The matrix `[∂_y h(z) ; y_l(z)]` of evaluated mixed derivatives. -/
private def critMat {p q j r : ℕ} (c : EAChain (p+q) r) (h : Fin j → EAPoly (p+q) r) (l : Fin q)
    (z : Fin (p+q) → ℝ) : Matrix (Fin (j+1)) (Fin q) ℝ :=
  Matrix.of (rowVec c h l z)

/-- The `a`-th row of `critMat` for `a : Fin j` is the row `∂_y h_a(z)`. -/
private theorem rowVec_castSucc {p q j r : ℕ} (c : EAChain (p+q) r) (h : Fin j → EAPoly (p+q) r)
    (l : Fin q) (z : Fin (p+q) → ℝ) (a : Fin j) (l' : Fin q) :
    rowVec c h l z (Fin.castSucc a) l' = eaEval c (eaD c (Work.WilE5.yDir p l') (h a)) z := by
  simp only [rowVec, Fin.lastCases_castSucc]

/-- The last row of `critMat` is the coordinate function `y_l`: `∂_{y_{l'}} y_l = δ_{l l'}`. -/
private theorem rowVec_last {p q j r : ℕ} (c : EAChain (p+q) r) (h : Fin j → EAPoly (p+q) r)
    (l : Fin q) (z : Fin (p+q) → ℝ) (l' : Fin q) :
    rowVec c h l z (Fin.last j) l' = if l' = l then 1 else 0 := by
  simp only [rowVec, Fin.lastCases_last]
  rw [eaEval_eaD_X_inl]
  rw [if_congr (show (Work.WilE5.yDir p l' = Work.WilE5.yDir p l) ↔ (l' = l)
      from (Work.WilE5.yDir_injective p).eq_iff) rfl rfl]

/-- The critical minor `critMinor c h l σ` evaluated at `z` is the `σ`-column minor of `critMat`. -/
private theorem eaEval_critMinor {p q r j : ℕ} (c : EAChain (p+q) r) (h : Fin j → EAPoly (p+q) r)
    (l : Fin q) (σ : Fin (j+1) → Fin q) (z : Fin (p+q) → ℝ) :
    eaEval c (Work.WilE7.critMinor c h l σ) z =
      (Matrix.of fun (a b : Fin (j+1)) =>
        eaEval c (eaD c (Work.WilE5.yDir p (σ b))
          (Fin.lastCases (MvPolynomial.X (Sum.inl (Work.WilE5.yDir p l))) h a)) z).det := by
  rw [Work.WilE7.critMinor]
  exact eaEval_detOp' c h (fun b => Work.WilE5.yDir p (σ b))
    (MvPolynomial.X (Sum.inl (Work.WilE5.yDir p l))) z

/-- `critMinor c h l σ` evaluated at `z` is the determinant of the `σ`-submatrix of `critMat`. -/
private theorem submatrix_det_critMat {p q r j : ℕ} (c : EAChain (p+q) r) (h : Fin j → EAPoly (p+q) r)
    (l : Fin q) (z : Fin (p+q) → ℝ) (σ : Fin (j+1) → Fin q) :
    ((critMat c h l z).submatrix id σ).det = eaEval c (Work.WilE7.critMinor c h l σ) z := by
  have h1 : (critMat c h l z).submatrix id σ
      = Matrix.of (fun (a b : Fin (j+1)) => eaEval c (eaD c (Work.WilE5.yDir p (σ b))
          (Fin.lastCases (MvPolynomial.X (Sum.inl (Work.WilE5.yDir p l))) h a)) z) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq, critMat, rowVec]
  rw [h1, ← eaEval_critMinor c h l σ z]

/-- The first `j` rows of `critMat` form the fibre Jacobian `(∂_{y_{l'}} h_a(z))`. -/
private theorem top_eq_critMat {p q r j : ℕ} (c : EAChain (p+q) r) (h : Fin j → EAPoly (p+q) r)
    (l : Fin q) (z : Fin (p+q) → ℝ) :
    (critMat c h l z).submatrix Fin.castSucc id
      = Matrix.of (fun (a : Fin j) (l' : Fin q) => eaEval c (eaD c (Work.WilE5.yDir p l') (h a)) z) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq, critMat, rowVec, Fin.lastCases_castSucc]

/-! ### The main lemma -/

theorem critMinorsVanishKer {p q : ℕ} {j r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r) (l : Fin q) (z : Fin (p + q) → ℝ)
    (hrank : (Matrix.of fun (a : Fin j) (l' : Fin q) =>
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l') (h a)) z).rank = j)
    (hmin : ∀ σ : Fin (j + 1) → Fin q, WilkiesDesign.E.eaEval c (Work.WilE7.critMinor c h l σ) z = 0) :
    ∀ v : Fin q → ℝ,
      (∀ a, ∑ l', WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l') (h a)) z * v l' = 0) →
      v l = 0 := by
  intro v hv
  have hminR : ∀ σ : Fin (j+1) → Fin q, ((critMat c h l z).submatrix id σ).det = 0 := by
    intro σ
    rw [submatrix_det_critMat]
    exact hmin σ
  have hrankR : ((critMat c h l z).submatrix Fin.castSucc id).rank = j := by
    rw [top_eq_critMat]
    exact hrank
  have hv' : ∀ a : Fin j, ∑ l', (critMat c h l z) (Fin.castSucc a) l' * v l' = 0 := by
    intro a
    have h1 : (∑ l' : Fin q, (critMat c h l z) (Fin.castSucc a) l' * v l')
        = ∑ l' : Fin q, eaEval c (eaD c (Work.WilE5.yDir p l') (h a)) z * v l' := by
      refine Finset.sum_congr rfl (fun l' _ => ?_)
      rw [critMat, Matrix.of_apply, rowVec_castSucc]
    rw [h1]
    exact hv a
  have hkey := kerOfVanishCritMinors (critMat c h l z) hminR hrankR v hv'
  have h2 : (∑ l' : Fin q, (critMat c h l z) (Fin.last j) l' * v l')
      = ∑ l' : Fin q, (if l' = l then (1:ℝ) else 0) * v l' := by
    refine Finset.sum_congr rfl (fun l' _ => ?_)
    rw [critMat, Matrix.of_apply, rowVec_last]
  rw [h2] at hkey
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hkey

end Work.WilE7.Aux
