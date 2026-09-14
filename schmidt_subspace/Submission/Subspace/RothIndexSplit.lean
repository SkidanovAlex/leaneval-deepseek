import Mathlib
import Submission.Subspace.WronskianMV
import Submission.Subspace.SuccEmbed
import Submission.Subspace.IndexRename
import Submission.Commons.Algebra.MvPolynomial.pderivIter_rename
import Submission.Commons.Analysis.Real.sum_max_sub_div_ge

/-!
# The index of the Wronskian determinant splits

For a decomposition `P = ∑_j Φ_j Ψ_j` with `Φ_j = rename Fin.succ (φ_j)` (variables
`x_1,…,x_n`) and `Ψ_j = rename e₂ (ψ_j)` (the variable `x_0`), the Wronskian determinant
`V = det (∂^{μ_i + j e_0} P)` factors as a product of two renames of the two smaller Wronskians.
Consequently the index is additive:
`Ind V = Ind U₂' + Ind U₁'`, where `U₂'` lives in `n` variables and `U₁'` in one variable.
-/

open scoped BigOperators

namespace Submission.Subspace

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The index of the Wronskian determinant is the sum of the indices of the two smaller
Wronskians. -/
theorem index_wronskian_det_split {n k : ℕ} (β : Fin (n + 1) → K) (r : Fin (n + 1) → ℕ)
    (P : MvPolynomial (Fin (n + 1)) K) (φ : Fin k → MvPolynomial (Fin n) K)
    (ψ : Fin k → MvPolynomial (Fin 1) K) (μ : Fin k → Fin n →₀ ℕ)
    (hdec : P = ∑ j, MvPolynomial.rename Fin.succ (φ j) *
      MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) (ψ j))
    (hdet₂ : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).det ≠ 0)
    (hdet₁ : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
        (ψ j)).det ≠ 0) :
    index β r (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P).det =
      index (β ∘ Fin.succ) (r ∘ Fin.succ) (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).det +
      index (β ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))))
        (r ∘ (fun _ : Fin 1 => (0 : Fin (n + 1)))) (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
          (ψ j)).det := by
  classical
  set e₂ : Fin 1 → Fin (n + 1) := fun _ => 0 with he₂
  set Φ : Fin k → MvPolynomial (Fin (n + 1)) K := fun j => MvPolynomial.rename Fin.succ (φ j)
    with hΦdef
  set Ψ : Fin k → MvPolynomial (Fin (n + 1)) K := fun j => MvPolynomial.rename e₂ (ψ j) with hΨdef
  have hΦ : ∀ j, MvPolynomial.pderiv (0 : Fin (n + 1)) (Φ j) = 0 := by
    intro j
    exact pderiv_rename_eq_zero Fin.succ 0 (by simp [Set.range]) (φ j)
  have hΨ : ∀ j (t : Fin n), MvPolynomial.pderiv (Fin.succ t) (Ψ j) = 0 := by
    intro j t
    refine pderiv_rename_eq_zero e₂ (Fin.succ t) ?_ (ψ j)
    rintro ⟨i, hi⟩
    fin_cases i
    exact Fin.succ_ne_zero t hi.symm
  have hfact := det_wronskian_factorization_mv P Φ Ψ hdec hΦ hΨ μ
  -- the two factors, rewritten as renames of the smaller Wronskians
  have hBmat : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((μ i).mapDomain Fin.succ) (Φ j)) =
      (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).map
          (MvPolynomial.rename Fin.succ) := by
    apply Matrix.ext
    intro i j
    show Commons.Algebra.MvPolynomial.pderivIter ((μ i).mapDomain Fin.succ)
        (MvPolynomial.rename Fin.succ (φ j)) =
      MvPolynomial.rename Fin.succ (Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j))
    exact Commons.Algebra.MvPolynomial.pderivIter_rename Fin.succ (Fin.succ_injective n) (μ i)
      (φ j)
  have hB : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((μ i).mapDomain Fin.succ) (Φ j)).det =
      MvPolynomial.rename Fin.succ (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).det := by
    rw [hBmat, AlgHom.map_det]
    rfl
  have hsum_e₂ : ∀ j : ℕ, (j • Finsupp.single (0 : Fin 1) 1).mapDomain e₂ =
      j • Finsupp.single (0 : Fin (n + 1)) 1 := by
    intro j
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
  have hAmat : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter
        ((j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) (Ψ i)) =
      (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((j : ℕ) • Finsupp.single (0 : Fin 1) 1)
          (ψ i)).map (MvPolynomial.rename e₂) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.of_apply, hΨdef]
    rw [← hsum_e₂ j]
    exact Commons.Algebra.MvPolynomial.pderivIter_rename e₂ (fun a b _ => Subsingleton.elim a b)
      _ (ψ i)
  have hA : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter
        ((j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) (Ψ i)).det =
      MvPolynomial.rename e₂ (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((j : ℕ) • Finsupp.single (0 : Fin 1) 1)
          (ψ i)).det := by
    rw [hAmat, AlgHom.map_det]
    rfl
  have hBne : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((μ i).mapDomain Fin.succ) (Φ j)).det ≠ 0 := by
    rw [hB]
    intro hc
    refine hdet₂ (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective n) ?_)
    rw [hc, map_zero]
  have htrans : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((j : ℕ) • Finsupp.single (0 : Fin 1) 1)
        (ψ i)).det = (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
        (ψ j)).det := by
    rw [← Matrix.det_transpose (M := Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
        (ψ j))]
    congr 1
  have hAne : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter
        ((j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) (Ψ i)).det ≠ 0 := by
    rw [hA]
    intro hc
    have h1 : (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((j : ℕ) • Finsupp.single (0 : Fin 1) 1)
          (ψ i)).det = 0 := by
      refine MvPolynomial.rename_injective e₂ (fun a b _ => Subsingleton.elim a b) ?_
      rw [hc, map_zero]
    rw [htrans] at h1
    exact hdet₁ h1
  rw [hfact, index_mul β r _ _ hBne hAne, hB, hA,
    index_rename Fin.succ (Fin.succ_injective n) β r _,
    index_rename e₂ (fun a b _ => Subsingleton.elim a b) β r _,
    htrans]


/-- **Quantitative lower bound for the index of the Wronskian determinant.**

If the Wronskian matrix `(∂^{μ_i + j e_0} P)` has nonzero determinant, `B` bounds the weighted
degree of the multi-indices `μ_i`, `deg_{x_0} P ≤ r 0` and `Ind P ≤ n+1`, then

`k · (Ind P)²/(2(n+1)) - k · B ≤ Ind (det)`.

This combines the column-minimum form of the determinant bound (`index_det_ge_min`) with the
inequality under differentiation and the elementary estimate
`Commons.Analysis.Real.sum_max_sub_div_ge`. -/
theorem index_wronskian_det_ge {n k : ℕ} {K : Type*} [Field K] [CharZero K]
    (β : Fin (n + 1) → K) (r : Fin (n + 1) → ℕ) (P : MvPolynomial (Fin (n + 1)) K)
    (μ : Fin k → Fin n →₀ ℕ) (B : ℝ)
    (hB : ∀ i, Commons.Algebra.MvPolynomial.indexWt r ((μ i).mapDomain Fin.succ) ≤ B)
    (hB0 : 0 ≤ B)
    (hdet : (Matrix.of fun i j : Fin k => Commons.Algebra.MvPolynomial.pderivIter
      ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P).det ≠ 0)
    (hr : 1 ≤ r 0) (hk : (k : ℝ) ≤ (r 0 : ℝ) + 1) (hm : 2 ≤ n + 1)
    (hIm : index β r P ≤ ((n : ℝ) + 1)) :
    (k : ℝ) * (index β r P) ^ 2 / (2 * ((n : ℝ) + 1)) - (k : ℝ) * B ≤
      index β r (Matrix.of fun i j : Fin k => Commons.Algebra.MvPolynomial.pderivIter
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P).det := by
  classical
  set I : ℝ := index β r P with hIdef
  set V : Matrix (Fin k) (Fin k) (MvPolynomial (Fin (n + 1)) K) := Matrix.of fun i j : Fin k =>
    Commons.Algebra.MvPolynomial.pderivIter
      ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P with hVdef
  have hDpos : 0 < (r 0 : ℝ) := by exact_mod_cast hr
  -- each nonzero entry of column `j` has index at least `max (I - B - j/r 0) 0`
  have hcol : ∀ i j : Fin k, V i j ≠ 0 →
      max (I - B - (j : ℝ) / (r 0 : ℝ)) 0 ≤ index β r (V i j) := by
    intro i j hij
    have hij' : Commons.Algebra.MvPolynomial.pderivIter
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P ≠ 0 := by
      simpa [hVdef] using hij
    have hdiff := index_sub_indexWt_le_index_pderivIter β r
      ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P hij'
    have hwt : Commons.Algebra.MvPolynomial.indexWt r
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) =
        Commons.Algebra.MvPolynomial.indexWt r ((μ i).mapDomain Fin.succ) +
          (j : ℝ) / (r 0 : ℝ) := by
      rw [indexWt_add, indexWt_smul_single]
    refine max_le ?_ (index_nonneg β r _)
    rw [hIdef]
    have hw := hB i
    rw [hwt] at hdiff
    have hVij : index β r (V i j) = index β r (Commons.Algebra.MvPolynomial.pderivIter
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P) := by
      rw [hVdef]; rfl
    linarith [hdiff, hw, hVij]
  have hmin := index_det_ge_min V hdet (fun j : Fin k => max (I - B - (j : ℝ) / (r 0 : ℝ)) 0)
    hcol
  -- comparison of the two sums
  have hkey : ∀ j : Fin k, max (I - (j : ℝ) / (r 0 : ℝ)) 0 - B ≤
      max (I - B - (j : ℝ) / (r 0 : ℝ)) 0 := by
    intro j
    rcases le_or_gt ((j : ℝ) / (r 0 : ℝ)) I with h | h
    · rw [max_eq_left (sub_nonneg.mpr h)]
      have : max (I - B - (j : ℝ) / (r 0 : ℝ)) 0 ≥ I - B - (j : ℝ) / (r 0 : ℝ) :=
        le_max_left _ _
      linarith
    · rw [max_eq_right (le_of_lt (sub_neg.mpr h))]
      exact le_trans (sub_nonpos.mpr hB0) (le_max_right (I - B - (j : ℝ) / (r 0 : ℝ)) 0)
  have hsum1 : (∑ j : Fin k, max (I - (j : ℝ) / (r 0 : ℝ)) 0) - (k : ℝ) * B ≤
      ∑ j : Fin k, max (I - B - (j : ℝ) / (r 0 : ℝ)) 0 := by
    have hc : (k : ℝ) * B = ∑ _j : Fin k, B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hc, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun j _ => hkey j
  have hrewrite : (∑ j : Fin k, max (I - (j : ℝ) / (r 0 : ℝ)) 0) =
      ∑ j ∈ Finset.range k, max (I - (j : ℝ) / (r 0 : ℝ)) 0 :=
    Fin.sum_univ_eq_sum_range (fun j => max (I - (j : ℝ) / (r 0 : ℝ)) 0) k
  have hI0 : 0 ≤ I := by rw [hIdef]; exact index_nonneg β r P
  have hIm' : I ≤ ((n : ℝ) + 1) := by rw [hIdef]; exact hIm
  have hsum2 := Commons.Analysis.Real.sum_max_sub_div_ge hI0 hIm'
    (by exact_mod_cast hm) (by exact_mod_cast hr) hk
  rw [hrewrite] at hsum1
  linarith [hsum1, hsum2, hmin]

/-- **Factorisation of the Wronskian determinant of a decomposition** in the variable
presentation: `det (∂^{μ_i + j e_0} P)` equals the product of the renamed smaller Wronskians. -/
theorem det_wronskian_factorization_rename {K : Type*} [Field K] [CharZero K] {n k : ℕ}
    (P : MvPolynomial (Fin (n + 1)) K) (φ : Fin k → MvPolynomial (Fin n) K)
    (ψ : Fin k → MvPolynomial (Fin 1) K) (μ : Fin k → Fin n →₀ ℕ)
    (hdec : P = ∑ j, MvPolynomial.rename Fin.succ (φ j) *
      MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) (ψ j)) :
    (Matrix.of fun i j : Fin k => Commons.Algebra.MvPolynomial.pderivIter
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P).det =
      MvPolynomial.rename Fin.succ (Matrix.of fun i j : Fin k =>
          Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).det *
        MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) (Matrix.of fun i j : Fin k =>
          Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
            (ψ j)).det := by
  classical
  set e₂ : Fin 1 → Fin (n + 1) := fun _ => 0 with he₂
  set Φ : Fin k → MvPolynomial (Fin (n + 1)) K := fun j => MvPolynomial.rename Fin.succ (φ j)
    with hΦdef
  set Ψ : Fin k → MvPolynomial (Fin (n + 1)) K := fun j => MvPolynomial.rename e₂ (ψ j) with hΨdef
  have hΦ : ∀ j, MvPolynomial.pderiv (0 : Fin (n + 1)) (Φ j) = 0 := by
    intro j
    exact pderiv_rename_eq_zero Fin.succ 0 (by simp [Set.range]) (φ j)
  have hΨ : ∀ j (t : Fin n), MvPolynomial.pderiv (Fin.succ t) (Ψ j) = 0 := by
    intro j t
    refine pderiv_rename_eq_zero e₂ (Fin.succ t) ?_ (ψ j)
    rintro ⟨i, hi⟩
    fin_cases i
    exact Fin.succ_ne_zero t hi.symm
  have hfact := det_wronskian_factorization_mv P Φ Ψ hdec hΦ hΨ μ
  -- the two factors, rewritten as renames of the smaller Wronskians
  have hBmat : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((μ i).mapDomain Fin.succ) (Φ j)) =
      (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).map
          (MvPolynomial.rename Fin.succ) := by
    apply Matrix.ext
    intro i j
    show Commons.Algebra.MvPolynomial.pderivIter ((μ i).mapDomain Fin.succ)
        (MvPolynomial.rename Fin.succ (φ j)) =
      MvPolynomial.rename Fin.succ (Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j))
    exact Commons.Algebra.MvPolynomial.pderivIter_rename Fin.succ (Fin.succ_injective n) (μ i)
      (φ j)
  have hB : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((μ i).mapDomain Fin.succ) (Φ j)).det =
      MvPolynomial.rename Fin.succ (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).det := by
    rw [hBmat, AlgHom.map_det]
    rfl
  have hsum_e₂ : ∀ j : ℕ, (j • Finsupp.single (0 : Fin 1) 1).mapDomain e₂ =
      j • Finsupp.single (0 : Fin (n + 1)) 1 := by
    intro j
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
  have hAmat : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter
        ((j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) (Ψ i)) =
      (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((j : ℕ) • Finsupp.single (0 : Fin 1) 1)
          (ψ i)).map (MvPolynomial.rename e₂) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.of_apply, hΨdef]
    rw [← hsum_e₂ j]
    exact Commons.Algebra.MvPolynomial.pderivIter_rename e₂ (fun a b _ => Subsingleton.elim a b)
      _ (ψ i)
  have hA : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter
        ((j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) (Ψ i)).det =
      MvPolynomial.rename e₂ (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((j : ℕ) • Finsupp.single (0 : Fin 1) 1)
          (ψ i)).det := by
    rw [hAmat, AlgHom.map_det]
    rfl
  have htrans : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((j : ℕ) • Finsupp.single (0 : Fin 1) 1)
        (ψ i)).det = (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
        (ψ j)).det := by
    rw [← Matrix.det_transpose (M := Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
        (ψ j))]
    congr 1
  rw [hfact, hB, hA, htrans]


/-- **Nonvanishing of the Wronskian determinant of a decomposition.**  If both the
`n`-variable and the one-variable Wronskians of a decomposition
`P = ∑_j Φ_j Ψ_j` are nonzero, then the Wronskian determinant
`det (∂^{μ_i + j e_0} P)` is nonzero. -/
theorem det_wronskian_mv_ne_zero {n k : ℕ} (P : MvPolynomial (Fin (n + 1)) K)
    (φ : Fin k → MvPolynomial (Fin n) K) (ψ : Fin k → MvPolynomial (Fin 1) K)
    (μ : Fin k → Fin n →₀ ℕ)
    (hdec : P = ∑ j, MvPolynomial.rename Fin.succ (φ j) *
      MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin (n + 1))) (ψ j))
    (hdet₂ : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).det ≠ 0)
    (hdet₁ : (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
        (ψ j)).det ≠ 0) :
    (Matrix.of fun i j : Fin k =>
      Commons.Algebra.MvPolynomial.pderivIter
        ((μ i).mapDomain Fin.succ + (j : ℕ) • Finsupp.single (0 : Fin (n + 1)) 1) P).det ≠ 0 := by
  rw [det_wronskian_factorization_rename P φ ψ μ hdec, mul_ne_zero_iff]
  constructor
  · intro hc
    refine hdet₂ (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective n) ?_)
    rw [hc, map_zero]
  · intro hc
    have h1 : (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter ((i : ℕ) • Finsupp.single (0 : Fin 1) 1)
          (ψ j)).det = 0 := by
      refine MvPolynomial.rename_injective (fun _ : Fin 1 => (0 : Fin (n + 1)))
        (fun a b _ => Subsingleton.elim a b) ?_
      rw [hc, map_zero]
    exact hdet₁ h1

end Submission.Subspace
