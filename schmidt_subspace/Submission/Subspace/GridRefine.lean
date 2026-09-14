import Mathlib
import Submission.Subspace.NonVanishMain
import Submission.Commons.Algebra.MvPolynomial.exists_pderivIter_eval_ne_zero_of_aeval_linear
import Submission.Commons.Algebra.MvPolynomial.exists_pderivIter_eval_ne_zero_fintype
import Submission.Commons.Algebra.MvPolynomial.blockDiag_aeval_degree_le

/-!
# The grid refinement (Evertse's Lemma 26)

Given hyperplanes `V_h = Z(b h)` (`b h 0 ≠ 0`) together with *integral* vectors
`g h l ∈ V_h` spanning `V_h` over `ℚ`, and a polynomial `H` which does not vanish on
`V = ∏_h V_h`, one can find a *grid point*
`x_h = ∑_l z h l • g h l` (`|z h l| ≤ B`, so `x ∈ ℤ^{mN} ∩ V`) and a multi-index `J` with

`(J/d) ≤ m · N · (N-1) / B`   and   `(∂_J H)(x) ≠ 0`.

The grid property is what makes the `A`-bounds work: `x` is integral, so a derivative of an
integral polynomial evaluated at `x` is an integer.
-/

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

variable {m N : ℕ}

/-- A nonzero polynomial over an infinite field does not vanish at every point. -/
lemma exists_eval_ne_zero_of_ne_zero {σ K : Type*} [Field K] [Infinite K]
    {P : MvPolynomial σ K} (hP : P ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x P ≠ 0 := by
  by_contra h
  push_neg at h
  exact hP (MvPolynomial.funext fun x => by rw [h x, map_zero])

/-- The pivot substitution is the identity on the evaluation at a point of `Z(b)`. -/
theorem aeval_pivotSubst_of_mem_V {K : Type*} [Field K] (b : Fin m → Fin N → K)
    [NeZero N] (hb : ∀ h, b h 0 ≠ 0)
    (y : Fin m × Fin N → K) (hy : ∀ h, ∑ j, b h j * y (h, j) = 0) :
    (MvPolynomial.aeval y).comp (pivotSubst b) = MvPolynomial.aeval y := by
  refine MvPolynomial.algHom_ext fun z => ?_
  rw [AlgHom.comp_apply]
  obtain ⟨h, j⟩ := z
  by_cases hj : j = 0
  · subst hj
    have hsep : (∑ j ∈ Finset.univ.erase (0 : Fin N), b h j * y (h, j))
        = -(b h 0 * y (h, 0)) := by
      have h1 : (∑ j ∈ Finset.univ.erase (0 : Fin N), b h j * y (h, j)) +
          b h 0 * y (h, 0) = 0 := by
        rw [Finset.sum_erase_add (Finset.univ) (fun j : Fin N => b h j * y (h, j))
          (Finset.mem_univ 0), hy h]
      exact eq_neg_of_add_eq_zero_left h1
    rw [pivotSubst_X_zero, map_mul, map_sum]
    simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self_apply]
    rw [hsep, neg_mul_neg, inv_mul_cancel_left₀ (hb h)]
  · rw [pivotSubst_X_of_ne b h hj, MvPolynomial.aeval_X]

/-- If the pivot substitution does not kill `P`, then `P` does not vanish identically on the
variety `Z(b)`: there is a rational point of `Z(b)` where `P` is nonzero. -/
theorem nonvanish_point {K : Type*} [Field K] [Infinite K] {m N : ℕ} [NeZero N]
    (b : Fin m → Fin N → K) (hb : ∀ h, b h 0 ≠ 0)
    (P : MvPolynomial (Fin m × Fin N) K) (hP : pivotSubst b P ≠ 0) :
    ∃ y : Fin m × Fin N → K, (∀ h, ∑ j, b h j * y (h, j) = 0) ∧
      MvPolynomial.aeval y P ≠ 0 := by
  classical
  obtain ⟨y', hy'⟩ := exists_eval_ne_zero_of_ne_zero hP
  set y : Fin m × Fin N → K := fun z =>
    if z.2 = 0 then -(b z.1 0)⁻¹ * (∑ j ∈ Finset.univ.erase 0, b z.1 j * y' (z.1, j))
    else y' z with hydef
  have hyne : ∀ (h : Fin m) (j : Fin N), j ≠ 0 → y (h, j) = y' (h, j) := by
    intro h j hj
    rw [hydef]
    simp [hj]
  have hy0 : ∀ h, y (h, 0) = -(b h 0)⁻¹ *
      (∑ j ∈ Finset.univ.erase (0 : Fin N), b h j * y' (h, j)) := by
    intro h
    rw [hydef]
    simp
  have hyV : ∀ h, ∑ j, b h j * y (h, j) = 0 := by
    intro h
    have hsum_eq : (∑ j ∈ Finset.univ.erase (0 : Fin N), b h j * y (h, j))
        = ∑ j ∈ Finset.univ.erase (0 : Fin N), b h j * y' (h, j) :=
      Finset.sum_congr rfl fun j hj => by rw [hyne h j (Finset.mem_erase.mp hj).1]
    have hsplit : (∑ j ∈ Finset.univ.erase (0 : Fin N), b h j * y (h, j)) + b h 0 * y (h, 0)
        = ∑ j, b h j * y (h, j) :=
      Finset.sum_erase_add (Finset.univ) (fun j : Fin N => b h j * y (h, j)) (Finset.mem_univ 0)
    rw [← hsplit, hsum_eq, hy0]
    rw [← mul_assoc, mul_neg, mul_inv_cancel₀ (hb h), neg_one_mul, add_neg_cancel]
  refine ⟨y, hyV, ?_⟩
  have hψ : (fun z : Fin m × Fin N =>
      MvPolynomial.aeval y (pivotSubst b (MvPolynomial.X z))) =
      (fun z : Fin m × Fin N =>
        MvPolynomial.aeval y' (pivotSubst b (MvPolynomial.X z))) := by
    funext z
    obtain ⟨h, j⟩ := z
    by_cases hj : j = 0
    · subst hj
      have h1 : MvPolynomial.aeval y (pivotSubst b (MvPolynomial.X (h, 0)))
          = -(b h 0)⁻¹ * (∑ j ∈ Finset.univ.erase (0 : Fin N), b h j * y (h, j)) := by
        rw [pivotSubst_X_zero, map_mul, map_sum]
        simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
          Algebra.algebraMap_self_apply]
      have h2 : MvPolynomial.aeval y' (pivotSubst b (MvPolynomial.X (h, 0)))
          = -(b h 0)⁻¹ * (∑ j ∈ Finset.univ.erase (0 : Fin N), b h j * y' (h, j)) := by
        rw [pivotSubst_X_zero, map_mul, map_sum]
        simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
          Algebra.algebraMap_self_apply]
      rw [h1, h2]
      congr 1
      exact Finset.sum_congr rfl fun j hj => by rw [hyne h j (Finset.mem_erase.mp hj).1]
    · rw [pivotSubst_X_of_ne b h hj]
      simp only [MvPolynomial.aeval_X]
      exact hyne h j hj
  have key : MvPolynomial.aeval y (pivotSubst b P)
      = MvPolynomial.aeval y' (pivotSubst b P) := by
    have h : ∀ (w : Fin m × Fin N → K),
        MvPolynomial.aeval w (pivotSubst b P)
          = MvPolynomial.aeval (fun z => MvPolynomial.aeval w (pivotSubst b (MvPolynomial.X z))) P := by
      intro w
      rw [pivotSubst, MvPolynomial.comp_aeval_apply]
      simp only [MvPolynomial.aeval_X]
    rw [h y, h y', hψ]
  have h1 : MvPolynomial.aeval y P = MvPolynomial.aeval y (pivotSubst b P) := by
    have h := aeval_pivotSubst_of_mem_V b hb y hyV
    simpa only [AlgHom.comp_apply] using (congrArg (fun f => f P) h).symm
  rw [h1, key]
  exact hy'

/-! ## The block-diagonal linear substitution -/

/-- The matrix of the block-diagonal substitution attached to `g` (over `ℚ`). -/
noncomputable def blockMatrixRat {m N N' : ℕ} (g : Fin m → Fin N' → Fin N → ℤ) :
    Fin m × Fin N → Fin m × Fin N' → ℚ :=
  fun x y => if x.1 = y.1 then ((g x.1 y.2 x.2 : ℤ) : ℚ) else 0

/-- The corresponding linear forms `X (h,j) ↦ ∑_l g h l j · X (h,l)`. -/
noncomputable def blockLinFormRat {m N N' : ℕ} (g : Fin m → Fin N' → Fin N → ℤ)
    (x : Fin m × Fin N) : MvPolynomial (Fin m × Fin N') ℚ :=
  ∑ y : Fin m × Fin N', MvPolynomial.C (blockMatrixRat g x y) * MvPolynomial.X y

lemma blockLinFormRat_eq {m N N' : ℕ} (g : Fin m → Fin N' → Fin N → ℤ) :
    blockLinFormRat g = (fun x : Fin m × Fin N =>
      ∑ y : Fin m × Fin N', MvPolynomial.C (blockMatrixRat g x y) * MvPolynomial.X y) := rfl

open Commons.Algebra.MvPolynomial

/-- **The grid refinement.** -/
theorem grid_refinement {m N : ℕ} [NeZero m] [NeZero N] (hN : 2 ≤ N)
    (b : Fin m → Fin N → ℚ)
    (g : Fin m → Fin (N - 1) → Fin N → ℤ)
    (hg : ∀ h l, ∑ j, b h j * (g h l j : ℚ) = 0)
    (hspan : ∀ h (y : Fin N → ℚ), (∑ j, b h j * y j = 0) →
      y ∈ Submodule.span ℚ (Set.range (fun l : Fin (N - 1) => (fun j => (g h l j : ℚ)))))
    (H : MvPolynomial (Fin m × Fin N) ℚ)
    (hHpt : ∃ y : Fin m × Fin N → ℚ, (∀ h, ∑ j, b h j * y (h, j) = 0) ∧
      MvPolynomial.aeval y H ≠ 0)
    (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h)
    (hdeg : ∀ u ∈ H.support, ∀ h, ∑ j, u (h, j) ≤ d h)
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ (z : Fin m × Fin (N - 1) → ℤ) (J : (Fin m × Fin N) →₀ ℕ),
      (∀ q, |z q| ≤ (B : ℤ)) ∧
      Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin N => d hi.1) J ≤
        (m : ℝ) * (N : ℝ) * ((N - 1 : ℕ) : ℝ) / (B : ℝ) ∧
      MvPolynomial.aeval (fun hi : Fin m × Fin N =>
        ((∑ l, z (hi.1, l) * g hi.1 l hi.2 : ℤ) : ℚ))
        (Commons.Algebra.MvPolynomial.pderivIter J H) ≠ 0 := by
  classical
  obtain ⟨y, hyV, hyH⟩ := hHpt
  have hA0 : ∀ (h : Fin m) (j : Fin N) (h' : Fin m) (j' : Fin (N - 1)),
      blockMatrixRat g (h, j) (h', j') ≠ 0 → h' = h := by
    intro h j h' j' hne
    by_contra hh
    rw [blockMatrixRat, if_neg (fun hc => hh hc.symm)] at hne
    exact hne rfl
  -- ### Step 1: the parametrisation is nonzero
  have hΦ : MvPolynomial.aeval (blockLinFormRat g) H ≠ 0 := by
    intro h0
    have hmem : ∀ h, (fun j : Fin N => y (h, j)) ∈
        Submodule.span ℚ (Set.range (fun l : Fin (N - 1) => (fun j => (g h l j : ℚ)))) :=
      fun h => hspan h (fun j => y (h, j)) (hyV h)
    choose cc hcc using fun h => (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hmem h)
    have hcc' : ∀ (h : Fin m) (j : Fin N), y (h, j) = ∑ l : Fin (N - 1),
        cc h l * ((g h l j : ℤ) : ℚ) := by
      intro h j
      have hh := congrFun (hcc h) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
      exact hh.symm
    have hkey : ∀ x : Fin m × Fin N,
        MvPolynomial.aeval (fun q : Fin m × Fin (N - 1) => cc q.1 q.2)
          (blockLinFormRat g x) = y x := by
      intro x
      obtain ⟨h, j⟩ := x
      rw [hcc' h j, blockLinFormRat, map_sum, Fintype.sum_prod_type]
      simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Algebra.algebraMap_self_apply, blockMatrixRat]
      rw [Finset.sum_eq_single h]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [if_pos rfl]; ring
      · intro h' _ hne
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [if_neg (fun hc => hne hc.symm), zero_mul]
      · intro hnot; exact absurd (Finset.mem_univ h) hnot
    have hy_eq : (fun x : Fin m × Fin N =>
        MvPolynomial.aeval (fun q : Fin m × Fin (N - 1) => cc q.1 q.2)
          (blockLinFormRat g x)) = y := funext hkey
    have hzero : MvPolynomial.aeval y H = 0 := by
      rw [← hy_eq, ← MvPolynomial.comp_aeval_apply (f := blockLinFormRat g)
        (φ := MvPolynomial.aeval (fun q : Fin m × Fin (N - 1) => cc q.1 q.2)) H, h0, map_zero]
    exact hyH hzero
  -- ### Step 2: the box-vanishing lemma in the parametrising coordinates
  obtain ⟨z, i, hz, hi, hne⟩ := Commons.Algebra.MvPolynomial.exists_pderivIter_eval_ne_zero_fintype
    (fun q : Fin m × Fin (N - 1) => d q.1)
    (MvPolynomial.aeval (blockLinFormRat g) H) hΦ
    (fun u hu q => le_trans
      (Finset.single_le_sum (f := fun l : Fin (N - 1) => u (q.1, l)) (fun l _ => Nat.zero_le _)
        (Finset.mem_univ q.2))
      (by
        have hu' := hu
        rw [blockLinFormRat_eq] at hu'
        exact blockDiag_aeval_degree_le H d hdeg (blockMatrixRat g)
          (fun h j h' j' hne => hA0 h j h' j' hne) u hu' q.1))
    B hB
  -- ### Step 3: push the derivative back to `H`
  obtain ⟨J, hJ, hJne⟩ := Commons.Algebra.MvPolynomial.exists_pderivIter_eval_ne_zero_of_aeval_linear
    (blockMatrixRat g) H i (fun q : Fin m × Fin (N - 1) => ((z q : ℤ) : ℚ))
    (by
      have h := hne
      rw [blockLinFormRat_eq] at h
      exact h)
  refine ⟨z, J, hz, ?_, ?_⟩
  · -- (a) the index bound
    have hIle : ∀ x : Fin m × Fin N, J x ≤ ∑ l : Fin (N - 1), i (x.1, l) := by
      intro x
      refine le_trans (hJ x) ?_
      have h1 : ∀ y : Fin m × Fin (N - 1),
          (if blockMatrixRat g x y = 0 then 0 else i y) ≤ if y.1 = x.1 then i y else 0 := by
        intro y
        by_cases hy : y.1 = x.1
        · rw [if_pos hy]
          by_cases hAxy : blockMatrixRat g x y = 0
          · rw [if_pos hAxy]; exact Nat.zero_le _
          · rw [if_neg hAxy]
        · have hAxy : blockMatrixRat g x y = 0 := by
            rw [blockMatrixRat]; exact if_neg (fun hc => hy hc.symm)
          rw [hAxy, if_pos rfl, if_neg hy]
      calc ∑ y ∈ i.support, (if blockMatrixRat g x y = 0 then 0 else i y)
          ≤ ∑ y ∈ i.support, (if y.1 = x.1 then i y else 0) :=
            Finset.sum_le_sum fun y _ => h1 y
        _ ≤ ∑ y : Fin m × Fin (N - 1), (if y.1 = x.1 then i y else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun y _ _ => Nat.zero_le _)
        _ = ∑ l : Fin (N - 1), i (x.1, l) := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single x.1]
            · refine Finset.sum_congr rfl fun l _ => ?_
              rw [if_pos rfl]
            · intro h' _ hne'
              refine Finset.sum_eq_zero fun l _ => ?_
              rw [if_neg (fun hc => hne' (by simpa using hc))]
            · intro hnot; exact absurd (Finset.mem_univ x.1) hnot
    have h2 : ∀ x : Fin m × Fin N, (J x : ℝ) ≤ (((N - 1) * (d x.1 / B) : ℕ) : ℝ) := by
      intro x
      have h3 : (∑ l : Fin (N - 1), i (x.1, l)) ≤ (N - 1) * (d x.1 / B) := by
        have hle : ∀ l : Fin (N - 1), i (x.1, l) ≤ d x.1 / B := fun l => hi (x.1, l)
        have hsum : (∑ l : Fin (N - 1), d x.1 / B) = (N - 1) * (d x.1 / B) := by
          simp [Finset.sum_const, Finset.card_univ, Finset.card_fin]
        rw [← hsum]
        exact Finset.sum_le_sum fun l _ => hle l
      exact_mod_cast le_trans (hIle x) h3
    have h4 : ∀ x : Fin m × Fin N, ((J x : ℝ) / (d x.1 : ℝ)) ≤
        ((N - 1 : ℕ) : ℝ) / (B : ℝ) := by
      intro x
      have hd0 : (0 : ℝ) < (d x.1 : ℝ) := by exact_mod_cast hd x.1
      have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
      have h5 : (((N - 1) * (d x.1 / B) : ℕ) : ℝ) ≤
          ((N - 1 : ℕ) : ℝ) * ((d x.1 : ℝ) / (B : ℝ)) := by
        have h6 : ((d x.1 / B : ℕ) : ℝ) ≤ (d x.1 : ℝ) / (B : ℝ) := Nat.cast_div_le
        calc (((N - 1) * (d x.1 / B) : ℕ) : ℝ)
            = ((N - 1 : ℕ) : ℝ) * ((d x.1 / B : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((N - 1 : ℕ) : ℝ) * ((d x.1 : ℝ) / (B : ℝ)) :=
              mul_le_mul_of_nonneg_left h6 (by positivity)
      have h6 : (J x : ℝ) ≤ ((N - 1 : ℕ) : ℝ) * ((d x.1 : ℝ) / (B : ℝ)) := le_trans (h2 x) h5
      rw [div_le_iff₀ hd0]
      calc (J x : ℝ) ≤ ((N - 1 : ℕ) : ℝ) * ((d x.1 : ℝ) / (B : ℝ)) := h6
        _ = ((N - 1 : ℕ) : ℝ) / (B : ℝ) * (d x.1 : ℝ) := by ring
    have h6 : Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin N => d hi.1) J
        ≤ ∑ x : Fin m × Fin N, ((N - 1 : ℕ) : ℝ) / (B : ℝ) := by
      rw [Commons.Algebra.MvPolynomial.indexWt]
      exact Finset.sum_le_sum fun x _ => h4 x
    have h7 : (∑ x : Fin m × Fin N, ((N - 1 : ℕ) : ℝ) / (B : ℝ))
        = (m : ℝ) * (N : ℝ) * ((N - 1 : ℕ) : ℝ) / (B : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    exact le_trans h6 (le_of_eq h7)
  · -- (b) the evaluation at the grid point
    have hpt : (fun x : Fin m × Fin N =>
        ∑ y : Fin m × Fin (N - 1), blockMatrixRat g x y * ((z y : ℤ) : ℚ)) =
        (fun hi : Fin m × Fin N => ((∑ l, z (hi.1, l) * g hi.1 l hi.2 : ℤ) : ℚ)) := by
      funext x
      obtain ⟨h, j⟩ := x
      rw [Fintype.sum_prod_type, Finset.sum_eq_single h]
      · rw [show (∑ l : Fin (N - 1),
            blockMatrixRat g (h, j) (h, l) * ((z (h, l) : ℤ) : ℚ))
            = ∑ l : Fin (N - 1), ((z (h, l) * g h l j : ℤ) : ℚ) from
          Finset.sum_congr rfl fun l _ => by
            rw [blockMatrixRat, if_pos rfl]; push_cast; ring]
        rw [← Int.cast_sum]
      · intro h' _ hne'
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [blockMatrixRat, if_neg (fun hc => hne' hc.symm), zero_mul]
      · intro hnot; exact absurd (Finset.mem_univ h) hnot
    rw [MvPolynomial.aeval_eq_eval, ← hpt]
    exact hJne


/-- **The non-vanishing lemma with grid points** (Evertse's Lemmas 24 and 26 combined). -/
theorem nonvanish_grid {m N : ℕ} [NeZero m] [NeZero N] (hN : 2 ≤ N)
    (F : MvPolynomial (Fin m × Fin N) ℤ) (hF : F ≠ 0)
    (e : Fin m → ℕ) (hhom : IsBlockHom e (F.map (Int.castRingHom ℚ)))
    (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h) (hle : ∀ h, e h ≤ d h)
    (b : Fin m → Fin N → ℚ) (hb : ∀ h, b h 0 ≠ 0)
    (q : Fin N) (hq : (q : ℕ) = 1)
    (g : Fin m → Fin (N - 1) → Fin N → ℤ)
    (hg : ∀ h l, ∑ j, b h j * (g h l j : ℚ) = 0)
    (hspan : ∀ h (y : Fin N → ℚ), (∑ j, b h j * y j = 0) →
      y ∈ Submodule.span ℚ (Set.range (fun l : Fin (N - 1) => (fun j => (g h l j : ℚ)))))
    (Θ η : ℝ) (hΘ : 0 < Θ) (hη0 : 0 < η) (hη : η ≤ 1 / 2) (hηΘ : 4 * η < Θ)
    (hratio : ∀ i j : Fin m, i ≤ j →
      (d i : ℝ) ≤ η ^ (2 ^ (m - 1) * ((j : ℕ) - (i : ℕ))) * (d j : ℝ))
    (hcond : η ^ (2 ^ (m - 1)) *
        (⨅ h : Fin m, (d h : ℝ) * Height.logHeight₁ (-(b h q) / (b h 0))) ≥
        hZ F + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ)))
    (B : ℕ) (hB : 1 ≤ B) :
    ∃ (z : Fin m × Fin (N - 1) → ℤ) (J : (Fin m × Fin N) →₀ ℕ),
      (∀ q', |z q'| ≤ (B : ℤ)) ∧
      Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin N => d hi.1) J ≤
        (m : ℝ) * Θ + (m : ℝ) * (N : ℝ) * ((N - 1 : ℕ) : ℝ) / (B : ℝ) ∧
      MvPolynomial.aeval (fun hi : Fin m × Fin N =>
        ((∑ l, z (hi.1, l) * g hi.1 l hi.2 : ℤ) : ℚ))
        (Commons.Algebra.MvPolynomial.pderivIter J (F.map (Int.castRingHom ℚ))) ≠ 0 := by
  classical
  have hq0 : q ≠ 0 := by intro hh; rw [hh] at hq; simp at hq
  obtain ⟨α, hα, hαne⟩ :=
    nonvanish_core hN F hF e hhom d hd hle b hb q hq Θ η hΘ hη0 hη hηΘ hratio hcond
  set H : MvPolynomial (Fin m × Fin N) ℚ :=
    Commons.Algebra.MvPolynomial.pderivIter (α.mapDomain (keepMap q))
      (F.map (Int.castRingHom ℚ)) with hHdef
  have hHne : H ≠ 0 := fun h0 => hαne (by rw [h0, map_zero])
  obtain ⟨y, hyV, hHy⟩ := nonvanish_point b hb H hαne
  have hdeg : ∀ u ∈ H.support, ∀ h : Fin m, ∑ j, u (h, j) ≤ d h := by
    intro u hu h
    have hu' : u ∈ (Commons.Algebra.MvPolynomial.pderivIter (α.mapDomain (keepMap q))
        (F.map (Int.castRingHom ℚ))).support := by rw [hHdef] at hu; exact hu
    have h1 : u + α.mapDomain (keepMap q) ∈ (F.map (Int.castRingHom ℚ)).support := by
      rw [MvPolynomial.mem_support_iff] at hu' ⊢
      intro h0
      exact hu' (by rw [Commons.Algebra.MvPolynomial.coeff_pderivIter, h0, zero_mul])
    have h2 := hhom _ h1 h
    calc ∑ j, u (h, j) ≤ ∑ j, (u + α.mapDomain (keepMap q)) (h, j) :=
          Finset.sum_le_sum fun j _ => by
            rw [Finsupp.add_apply]; exact Nat.le_add_right _ _
      _ = e h := h2
      _ ≤ d h := hle h
  obtain ⟨z, J, hz, hJ, hJne⟩ :=
    grid_refinement hN b g hg hspan H ⟨y, hyV, hHy⟩ d hd hdeg B hB
  refine ⟨z, J + α.mapDomain (keepMap q), hz, ?_, ?_⟩
  · rw [indexWt_add, show Commons.Algebra.MvPolynomial.indexWt
        (fun hi : Fin m × Fin N => d hi.1) (α.mapDomain (keepMap q)) =
        Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin 2 => d hi.1) α from by
      rw [← indexWt_mapDomain (fun hi : Fin m × Fin N => d hi.1) (keepMap q)
        (keepMap_injective hq0) α]
      rfl]
    linarith
  · have hpd : Commons.Algebra.MvPolynomial.pderivIter (J + α.mapDomain (keepMap q))
        (F.map (Int.castRingHom ℚ)) = Commons.Algebra.MvPolynomial.pderivIter J H := by
      rw [add_comm, Commons.Algebra.MvPolynomial.pderivIter_add, hHdef]
    rw [hpd]
    exact hJne

end Submission.Subspace
