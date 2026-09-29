import Mathlib
import Submission.Work.Resample.axis
import Submission.Work.Resample.tensorNorm

/-!
# The iterated axis recursion computes the tensor product

`Work.Resample.tensorMapRec ss ts F` applies the family of one-dimensional maps `F i`
successively along the axes of a flat lexicographic array of shape `ss` (this is the exact
computation performed by `HvdH.LayoutLib.applyAlong` iterated over the axes).  The present
file proves that, when each `F i` is the matrix-vector map of the entry function `f i`
(`F = Work.Resample.matFam ss ts f`), the recursion computes the tensor (Kronecker) product
`Work.Resample.tensorFun ss ts f` of the family of matrices.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Elementary helpers -/

/-- `vget` at a valid index is the bundled value. -/
lemma vget_of_lt {n : ℕ} (u : Fin n → ℂ) {i : ℕ} (h : i < n) : vget u i = u ⟨i, h⟩ := by
  simp [vget, h]

/-- `vget` of the zero vector. -/
@[simp] lemma vget_zero {n : ℕ} (i : ℕ) : vget (0 : Fin n → ℂ) i = 0 := by
  simp [vget]

/-- A sum over `Fin n` with `n = 0` vanishes. -/
lemma sum_fin_zero {n : ℕ} (h : n = 0) (φ : Fin n → ℂ) : ∑ i : Fin n, φ i = 0 := by
  subst h; simp

/-- The tensor product vanishes as soon as the product of the input shape is `0`. -/
lemma tensorFun_eq_zero_of_prod_zero {ss ts : List ℕ} (h : ss.prod = 0)
    (f : ℕ → ℕ → ℕ → ℂ) (u : Fin ss.prod → ℂ) : tensorFun ss ts f u = 0 := by
  funext J
  refine Finset.sum_eq_zero fun K _ => ?_
  have hK : (K : ℕ) < ss.prod := K.isLt
  omega

/-- The tensor product of a family of matrices kills the zero vector. -/
@[simp] lemma tensorFun_zero_apply {ss ts : List ℕ} (f : ℕ → ℕ → ℕ → ℂ) :
    tensorFun ss ts f (0 : Fin ss.prod → ℂ) = 0 := by
  funext J
  simp [tensorFun]

/-- The matrix-vector map of `matOf`. -/
lemma mulVec_matOf_apply (t s : ℕ) (f : ℕ → ℕ → ℕ → ℂ) (x : Fin s → ℂ) (j : Fin t) :
    ((matOf t s (f 0)).mulVec x) j = ∑ k : Fin s, f 0 j k * x k := by
  simp [matOf, Matrix.mulVec, dotProduct]

/-- The matrix-vector map of `matOf` is the zero map when the matrix has no columns. -/
lemma mulVec_matOf_eq_zero (t s : ℕ) (hs : s = 0) (f : ℕ → ℕ → ℕ → ℂ) (x : Fin s → ℂ) :
    (matOf t s (f 0)).mulVec x = 0 := by
  funext j
  rw [mulVec_matOf_apply]
  exact sum_fin_zero hs (fun k => f 0 j k * x k)

/-! ## Unfolding lemmas -/

@[simp] lemma matFam_zero (s : ℕ) (ss' : List ℕ) (t : ℕ) (ts' : List ℕ)
    (f : ℕ → ℕ → ℕ → ℂ) :
    matFam (s :: ss') (t :: ts') f 0 = (matOf t s (f 0)).mulVec := rfl

@[simp] lemma matFam_succ (s : ℕ) (ss' : List ℕ) (t : ℕ) (ts' : List ℕ)
    (f : ℕ → ℕ → ℕ → ℂ) (i : ℕ) :
    matFam (s :: ss') (t :: ts') f (i + 1) = matFam ss' ts' (fun i => f (i + 1)) i := rfl

@[simp] lemma blockwise_apply (t N N' : ℕ) (Φ : (Fin N → ℂ) → (Fin N' → ℂ))
    (u : Fin (t * N) → ℂ) (idx : Fin (t * N')) :
    blockwise t N N' Φ u idx
      = vget (Φ (fun K' => vget u ((idx : ℕ) / N' * N + (K' : ℕ)))) ((idx : ℕ) % N') := rfl

@[simp] lemma axisApply1Gen_apply (s t B : ℕ) (Φ : (Fin s → ℂ) → (Fin t → ℂ))
    (u : Fin (s * B) → ℂ) (idx : Fin (t * B)) :
    axisApply1Gen s t B Φ u idx
      = vget (Φ (fun j => vget u ((j : ℕ) * B + (idx : ℕ) % B))) ((idx : ℕ) / B) := rfl

@[simp] lemma tensorMapRec_nil (F : (i : ℕ) → (Fin (([].getD i 0)) → ℂ) →
    (Fin (([].getD i 0)) → ℂ)) : tensorMapRec [] [] F = id := rfl

lemma tensorMapRec_cons (s : ℕ) (ss' : List ℕ) (t : ℕ) (ts' : List ℕ)
    (F : (i : ℕ) → (Fin ((s :: ss').getD i 0) → ℂ) → (Fin ((t :: ts').getD i 0) → ℂ))
    (u : Fin ((s :: ss').prod) → ℂ) :
    tensorMapRec (s :: ss') (t :: ts') F u
      = blockwise t ss'.prod ts'.prod (tensorMapRec ss' ts' (fun i => F (i + 1)))
          (axisApply1Gen s t ss'.prod (F 0) u) := rfl

/-! ## Index arithmetic -/

/-- `vget` of a block of a `Fin (s * B)` vector. -/
lemma vget_finProdFinEquiv {s B : ℕ} (u : Fin (s * B) → ℂ) (j : Fin s) (K' : Fin B) :
    vget u (j * B + K') = u (finProdFinEquiv (j, K')) := by
  have hlt : (j : ℕ) * B + (K' : ℕ) < s * B := by
    have h1 : (j : ℕ) + 1 ≤ s := Nat.succ_le_of_lt j.isLt
    have h2 : ((j : ℕ) + 1) * B ≤ s * B := Nat.mul_le_mul_right B h1
    have h3 : (j : ℕ) * B + (K' : ℕ) < ((j : ℕ) + 1) * B := by
      rw [Nat.add_mul]; omega
    omega
  rw [vget_of_lt u hlt]
  have hv : ((finProdFinEquiv (j, K') : Fin (s * B)) : ℕ) = (j : ℕ) * B + (K' : ℕ) := by
    rw [finProdFinEquiv_apply_val]; ring
  exact congrArg u (Fin.ext hv.symm)

/-- Evaluation of one axis application at the index `(J, K')`. -/
lemma axisApply1Gen_eval {s t B J : ℕ} (hB : 0 < B) (hJ : J < t)
    (Φ : (Fin s → ℂ) → (Fin t → ℂ)) (u : Fin (s * B) → ℂ) (K' : Fin B)
    (hlt : J * B + (K' : ℕ) < t * B) :
    axisApply1Gen s t B Φ u ⟨J * B + (K' : ℕ), hlt⟩
      = Φ (fun k => u (finProdFinEquiv (k, K'))) ⟨J, hJ⟩ := by
  have hdiv : (J * B + (K' : ℕ)) / B = J := by
    rw [show J * B + (K' : ℕ) = (K' : ℕ) + J * B by ring, Nat.add_mul_div_right _ _ hB,
        Nat.div_eq_of_lt K'.isLt, Nat.zero_add]
  have hmod : (J * B + (K' : ℕ)) % B = (K' : ℕ) := by
    rw [show J * B + (K' : ℕ) = (K' : ℕ) + J * B by ring, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt K'.isLt]
  rw [axisApply1Gen_apply, hdiv, hmod, vget_of_lt _ hJ]
  congr 1
  funext j
  exact vget_finProdFinEquiv u j K'

/-! ## The block vector -/

/-- The vector of the `idx`-th block of `u` transformed by the first axis map: this is precisely
the vector to which the recursion applies the tensor of the remaining factors. -/
noncomputable def blkVec (s t : ℕ) (ss' ts' : List ℕ) (f : ℕ → ℕ → ℕ → ℂ)
    (u : Fin (s * ss'.prod) → ℂ) (idx : Fin (t * ts'.prod)) : Fin ss'.prod → ℂ :=
  fun K' => vget (axisApply1Gen s t ss'.prod ((matOf t s (f 0)).mulVec) u)
    ((idx : ℕ) / ts'.prod * ss'.prod + (K' : ℕ))

/-- Linearity of the tensor in its vector argument, at a single coordinate. -/
lemma tensorLin_sum_apply {ss ts : List ℕ} (f : ℕ → ℕ → ℕ → ℂ) {n : ℕ}
    (c : Fin n → ℂ) (x : Fin n → (Fin ss.prod → ℂ)) (j : Fin ts.prod) :
    tensorLin ss ts f (∑ k : Fin n, c k • x k) j
      = ∑ k : Fin n, c k * tensorLin ss ts f (x k) j := by
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-! ## The recursion step -/

/-- The recursion step, pointwise: applying the tensor product over `s :: ss'` to `u` is the
same as applying the tensor over `ss'` to the blockwise first-axis transform of `u`. -/
lemma tensorFun_blockwise_apply (s t : ℕ) (ss' ts' : List ℕ) (f : ℕ → ℕ → ℕ → ℂ)
    (u : Fin (s * ss'.prod) → ℂ) (idx : Fin (t * ts'.prod)) :
    tensorFun (s :: ss') (t :: ts') f u idx
      = (blockwise t ss'.prod ts'.prod (tensorFun ss' ts' (fun i => f (i + 1)))
          (axisApply1Gen s t ss'.prod ((matOf t s (f 0)).mulVec) u)) idx := by
  by_cases hT : ts'.prod = 0
  · have hlt : (idx : ℕ) < t * ts'.prod := idx.isLt
    have h0 : t * ts'.prod = 0 := by rw [hT, Nat.mul_zero]
    omega
  by_cases ht : t = 0
  · have hlt : (idx : ℕ) < t * ts'.prod := idx.isLt
    have h0 : t * ts'.prod = 0 := by rw [ht, Nat.zero_mul]
    omega
  have hTpos : 0 < ts'.prod := Nat.pos_of_ne_zero hT
  by_cases hB : ss'.prod = 0
  · have h0 : (s :: ss').prod = 0 := by rw [List.prod_cons, hB, Nat.mul_zero]
    have hX : tensorFun (s :: ss') (t :: ts') f u idx = 0 :=
      congrFun (tensorFun_eq_zero_of_prod_zero (ts := t :: ts') h0 f u) idx
    rw [hX, blockwise_apply, tensorFun_eq_zero_of_prod_zero hB, vget_zero]
  by_cases hs : s = 0
  · have h0 : (s :: ss').prod = 0 := by rw [List.prod_cons, hs, Nat.zero_mul]
    have hX : tensorFun (s :: ss') (t :: ts') f u idx = 0 :=
      congrFun (tensorFun_eq_zero_of_prod_zero (ts := t :: ts') h0 f u) idx
    have hv : axisApply1Gen s t ss'.prod ((matOf t s (f 0)).mulVec) u = 0 := by
      funext l
      rw [axisApply1Gen_apply, mulVec_matOf_eq_zero t s hs]
      exact vget_zero _
    rw [hX, blockwise_apply, hv,
      show (fun K' : Fin ss'.prod => vget (0 : Fin (t * ss'.prod) → ℂ)
          ((idx : ℕ) / ts'.prod * ss'.prod + (K' : ℕ))) = 0 from by
        funext K'; exact vget_zero _,
      tensorFun_zero_apply, vget_zero]
  -- main case: `0 < s` and `0 < ss'.prod`
  have hBpos : 0 < ss'.prod := Nat.pos_of_ne_zero hB
  have hJlt : (idx : ℕ) / ts'.prod < t := by
    rw [Nat.div_lt_iff_lt_mul hTpos]
    exact idx.isLt
  have hRlt : (idx : ℕ) % ts'.prod < ts'.prod := Nat.mod_lt _ hTpos
  have hidx : idx = finProdFinEquiv
      (⟨(idx : ℕ) / ts'.prod, hJlt⟩, ⟨(idx : ℕ) % ts'.prod, hRlt⟩) := by
    apply Fin.ext
    rw [finProdFinEquiv_apply_val]
    change (idx : ℕ) = (idx : ℕ) % ts'.prod + ts'.prod * ((idx : ℕ) / ts'.prod)
    rw [add_comm]
    exact (Nat.div_add_mod (idx : ℕ) ts'.prod).symm
  have hL := tensorFun_cons s ss' t ts' hBpos hTpos f u
      ⟨(idx : ℕ) / ts'.prod, hJlt⟩ ⟨(idx : ℕ) % ts'.prod, hRlt⟩
  have hRHS : (blockwise t ss'.prod ts'.prod (tensorFun ss' ts' (fun i => f (i + 1)))
        (axisApply1Gen s t ss'.prod ((matOf t s (f 0)).mulVec) u)) idx
      = (tensorLin ss' ts' (fun i => f (i + 1)) (blkVec s t ss' ts' f u idx))
          ⟨(idx : ℕ) % ts'.prod, hRlt⟩ := by
    rw [blockwise_apply, vget_of_lt _ hRlt]
    rfl
  have hW : blkVec s t ss' ts' f u idx
      = ∑ k : Fin s, f 0 (↑(⟨(idx : ℕ) / ts'.prod, hJlt⟩ : Fin t)) k •
          (fun K'' : Fin ss'.prod => u (finProdFinEquiv (k, K''))) := by
    funext K'
    show vget (axisApply1Gen s t ss'.prod ((matOf t s (f 0)).mulVec) u)
        ((idx : ℕ) / ts'.prod * ss'.prod + (K' : ℕ))
      = (∑ k : Fin s, f 0 (↑(⟨(idx : ℕ) / ts'.prod, hJlt⟩ : Fin t)) k •
          (fun K'' : Fin ss'.prod => u (finProdFinEquiv (k, K'')))) K'
    have hlt : (idx : ℕ) / ts'.prod * ss'.prod + (K' : ℕ) < t * ss'.prod := by
      have h1 : (idx : ℕ) / ts'.prod + 1 ≤ t := Nat.succ_le_of_lt hJlt
      have h2 : ((idx : ℕ) / ts'.prod + 1) * ss'.prod ≤ t * ss'.prod :=
        Nat.mul_le_mul_right _ h1
      have h3 : (idx : ℕ) / ts'.prod * ss'.prod + (K' : ℕ)
          < ((idx : ℕ) / ts'.prod + 1) * ss'.prod := by rw [Nat.add_mul]; omega
      omega
    rw [vget_of_lt _ hlt,
      axisApply1Gen_eval hBpos hJlt ((matOf t s (f 0)).mulVec) u K' hlt,
      mulVec_matOf_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  trans ∑ k : Fin s, f 0 (↑(⟨(idx : ℕ) / ts'.prod, hJlt⟩ : Fin t)) k *
      tensorFun ss' ts' (fun i => f (i + 1)) (fun K'' => u (finProdFinEquiv (k, K'')))
        ⟨(idx : ℕ) % ts'.prod, hRlt⟩
  · conv_lhs => rw [hidx]
    exact hL
  · rw [hRHS, hW, tensorLin_sum_apply]
    rfl

/-- The recursion step for the tensor product. -/
lemma tensorFun_blockwise (s t : ℕ) (ss' ts' : List ℕ) (f : ℕ → ℕ → ℕ → ℂ)
    (u : Fin (s * ss'.prod) → ℂ) :
    tensorFun (s :: ss') (t :: ts') f u
      = blockwise t ss'.prod ts'.prod (tensorFun ss' ts' (fun i => f (i + 1)))
          (axisApply1Gen s t ss'.prod ((matOf t s (f 0)).mulVec) u) :=
  funext fun idx => tensorFun_blockwise_apply s t ss' ts' f u idx

/-! ## The main theorem -/

lemma tensorMapLin_aux (ss : List ℕ) : ∀ (ts : List ℕ), ts.length = ss.length →
    ∀ (f : ℕ → ℕ → ℕ → ℂ),
      tensorMapRec ss ts (matFam ss ts f) = tensorFun ss ts f := by
  induction ss with
  | nil =>
    intro ts hl f
    have hts : ts = [] := List.length_eq_zero_iff.mp hl
    subst hts
    rw [tensorMapRec_nil]
    funext u J
    show u J = ∑ K : Fin 1, (1 : ℂ) * u K
    rw [Fin.sum_univ_one, one_mul]
    exact congrArg u (Fin.eq_zero J)
  | cons s ss' ih =>
    intro ts hl f
    cases ts with
    | nil => simp at hl
    | cons t ts' =>
      have hTS : ts'.length = ss'.length := by
        simp only [List.length_cons] at hl
        omega
      funext u
      rw [tensorMapRec_cons]
      rw [show (fun i => matFam (s :: ss') (t :: ts') f (i + 1))
            = matFam ss' ts' (fun i => f (i + 1)) from by
        funext i; exact matFam_succ s ss' t ts' f i]
      rw [ih ts' hTS (fun i => f (i + 1))]
      rw [matFam_zero]
      exact (tensorFun_blockwise s t ss' ts' f u).symm

theorem tensorMapLin (ss ts : List ℕ) (hl : ts.length = ss.length)
    (f : ℕ → ℕ → ℕ → ℂ) (u : Fin ss.prod → ℂ) :
    Work.Resample.tensorMapRec ss ts (Work.Resample.matFam ss ts f) u =
      Work.Resample.tensorFun ss ts f u :=
  congrFun (tensorMapLin_aux ss ts hl f) u

end Work.Resample
