import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.weightDominationDefs

/-!
# `Work.Mostow.weightDomination`

If `c` acts on each block `span {e (i,0), e (i,1)}` of an orthonormal basis of `E (2 * r)`
as the rotation of angle `φ i`, and if the projections of `Wz` onto the blocks are
(coordinatewise, in norm) dominated by those of `W`, then `c` moves `Wz` by at most as
much as it moves `W`.

The proof decomposes `c v - v` into the orthogonal block contributions
`F i v = c (blkProj e i v) - blkProj e i v`, whose norm is `4 sin²(φ i / 2) ‖blkProj e i v‖²`,
and then compares the two sums blockwise.
-/

open scoped BigOperators

namespace Work.Mostow

variable {r : ℕ}

/-! ## Elementary helpers -/

/-- `Real.cos` only depends on the class of its argument in `AddCircle (2 * π)`. -/
private lemma cos_congr_addCircle {t t' : ℝ}
    (h : (t : AddCircle (2 * Real.pi)) = (t' : AddCircle (2 * Real.pi))) :
    Real.cos t = Real.cos t' := by
  rw [← Real.Angle.cos_coe t, ← Real.Angle.cos_coe t']
  exact congrArg Real.Angle.cos h

/-- `Real.sin` only depends on the class of its argument in `AddCircle (2 * π)`. -/
private lemma sin_congr_addCircle {t t' : ℝ}
    (h : (t : AddCircle (2 * Real.pi)) = (t' : AddCircle (2 * Real.pi))) :
    Real.sin t = Real.sin t' := by
  rw [← Real.Angle.sin_coe t, ← Real.Angle.sin_coe t']
  exact congrArg Real.Angle.sin h

/-- A linear isometry equivalence distributes over finite sums. -/
private lemma lIE_map_sum_univ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : E ≃ₗᵢ[ℝ] E) {ι : Type*} [Fintype ι] (f : ι → E) :
    c (∑ i, f i) = ∑ i, c (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add, ih]

/-- In a real inner product space, the squared norm of a sum of pairwise orthogonal
vectors is the sum of the squared norms. -/
private lemma norm_sq_sum_of_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (f : ι → E) (h : ∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0) :
    ‖∑ i, f i‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  have hmain : inner ℝ (∑ i, f i) (∑ i, f i) = ∑ i, inner ℝ (f i) (f i) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_sum]
    exact Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun j _ hj => h i j hj.symm)
  calc ‖∑ i, f i‖ ^ 2 = inner ℝ (∑ i, f i) (∑ i, f i) :=
        (real_inner_self_eq_norm_sq _).symm
    _ = ∑ i, inner ℝ (f i) (f i) := hmain
    _ = ∑ i, ‖f i‖ ^ 2 :=
        Finset.sum_congr rfl (fun i _ => real_inner_self_eq_norm_sq (f i))

/-! ## Basis and block lemmas -/

/-- Elements of distinct blocks of the orthonormal basis are orthogonal. -/
private lemma inner_ne_block
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ (EuclideanSpace ℝ (Fin (2 * r))))
    {i j : Fin r} (hij : i ≠ j) {b b' : Fin 2} :
    inner ℝ (e (i, b)) (e (j, b')) = 0 :=
  e.inner_eq_zero (by intro h; exact hij (congrArg Prod.fst h))

/-- `Fin.castSucc 0` and `1` are different elements of `Fin 2`. -/
private lemma fin_castSucc_zero_ne_one : (Fin.castSucc (0 : Fin 1) : Fin 2) ≠ 1 := by decide

/-- The two basis vectors of a single block are orthogonal. -/
private lemma inner_e_block01
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ (EuclideanSpace ℝ (Fin (2 * r))))
    (i : Fin r) : inner ℝ (e (i, Fin.castSucc 0)) (e (i, 1)) = 0 :=
  e.inner_eq_zero (by
    intro h
    exact fin_castSucc_zero_ne_one (congrArg Prod.snd h))

/-- The two basis vectors of a single block are orthogonal (other orientation). -/
private lemma inner_e_block10
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ (EuclideanSpace ℝ (Fin (2 * r))))
    (i : Fin r) : inner ℝ (e (i, 1)) (e (i, Fin.castSucc 0)) = 0 :=
  e.inner_eq_zero (by
    intro h
    exact fin_castSucc_zero_ne_one (congrArg Prod.snd h).symm)

/-- Norm of a two-term combination inside a single block. -/
private lemma norm_sq_smul_pair
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ (EuclideanSpace ℝ (Fin (2 * r))))
    (i : Fin r) (A B : ℝ) :
    ‖A • e (i, Fin.castSucc 0) + B • e (i, 1)‖ ^ 2 = A ^ 2 + B ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    OrthonormalBasis.inner_eq_one, inner_e_block01 e i, inner_e_block10 e i, mul_one]
  ring

/-- The squared norm of the block projection. -/
private lemma norm_sq_blkProj
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ (EuclideanSpace ℝ (Fin (2 * r))))
    (i : Fin r) (v : EuclideanSpace ℝ (Fin (2 * r))) :
    ‖blkProj e i v‖ ^ 2 =
      (inner ℝ (e (i, Fin.castSucc 0)) v) ^ 2 + (inner ℝ (e (i, 1)) v) ^ 2 := by
  unfold blkProj
  exact norm_sq_smul_pair e i _ _

/-- `(cos x - 1)² + sin²x = 4 sin²(x/2)`. -/
private lemma cos_sub_one_sq_add_sin_sq (x : ℝ) :
    (Real.cos x - 1) ^ 2 + Real.sin x ^ 2 = 4 * Real.sin (x / 2) ^ 2 := by
  have h := Real.sin_sq_eq_half_sub (x / 2)
  rw [show (2 : ℝ) * (x / 2) = x by ring] at h
  have hc := Real.sin_sq_add_cos_sq x
  nlinarith [h, hc]

/-! ## The block norm identity -/

/-- If `c` acts as the rotation of angle `τ i` on the `i`-th block of `e`, then
`‖c v - v‖² = ∑ i, 4 sin²(τ i / 2) ‖blkProj e i v‖²`. -/
private lemma weightNorm_aux
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ (EuclideanSpace ℝ (Fin (2 * r))))
    (c : EuclideanSpace ℝ (Fin (2 * r)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * r)))
    (τ : Fin r → ℝ)
    (h0 : ∀ i, c (e (i, Fin.castSucc 0)) =
          Real.cos (τ i) • e (i, Fin.castSucc 0) + Real.sin (τ i) • e (i, 1))
    (h1 : ∀ i, c (e (i, 1)) =
          - Real.sin (τ i) • e (i, Fin.castSucc 0) + Real.cos (τ i) • e (i, 1)) :
    ∀ v : EuclideanSpace ℝ (Fin (2 * r)),
      ‖c v - v‖ ^ 2 = ∑ i : Fin r, 4 * Real.sin (τ i / 2) ^ 2 * ‖blkProj e i v‖ ^ 2 := by
  classical
  intro v
  -- expansion of `v` and of `c v` in the basis
  have hv : v = ∑ i : Fin r, blkProj e i v := by
    conv_lhs => rw [← e.sum_repr' v]
    rw [Fintype.sum_prod_type]
    unfold blkProj
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.sum_univ_two]
    rfl
  have hcv : c v = ∑ i : Fin r, c (blkProj e i v) := by
    conv_lhs => rw [hv]
    exact lIE_map_sum_univ c _
  have hsubsum : c v - v = ∑ i : Fin r, (c (blkProj e i v) - blkProj e i v) := by
    rw [Finset.sum_sub_distrib, ← hcv, ← hv]
  -- the explicit block displacement
  have hF : ∀ i : Fin r, c (blkProj e i v) - blkProj e i v =
      (((Real.cos (τ i) - 1) * inner ℝ (e (i, Fin.castSucc 0)) v
          - Real.sin (τ i) * inner ℝ (e (i, 1)) v) • e (i, Fin.castSucc 0)
        + (Real.sin (τ i) * inner ℝ (e (i, Fin.castSucc 0)) v
          + (Real.cos (τ i) - 1) * inner ℝ (e (i, 1)) v) • e (i, 1)) := by
    intro i
    have hci : c (blkProj e i v) =
        (Real.cos (τ i) * inner ℝ (e (i, Fin.castSucc 0)) v
            - Real.sin (τ i) * inner ℝ (e (i, 1)) v) • e (i, Fin.castSucc 0)
          + (Real.sin (τ i) * inner ℝ (e (i, Fin.castSucc 0)) v
            + Real.cos (τ i) * inner ℝ (e (i, 1)) v) • e (i, 1) := by
      unfold blkProj
      rw [map_add, map_smul, map_smul, h0 i, h1 i]
      module
    rw [hci]
    unfold blkProj
    module
  -- distinct blocks are orthogonal
  have horth : ∀ i j : Fin r, i ≠ j →
      inner ℝ (c (blkProj e i v) - blkProj e i v)
        (c (blkProj e j v) - blkProj e j v) = 0 := by
    intro i j hij
    rw [hF i, hF j]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      inner_ne_block e hij, mul_zero, add_zero]
  -- norm of a single block displacement
  have hnorm_i : ∀ i : Fin r, ‖c (blkProj e i v) - blkProj e i v‖ ^ 2 =
      4 * Real.sin (τ i / 2) ^ 2 * ‖blkProj e i v‖ ^ 2 := by
    intro i
    rw [hF i, norm_sq_smul_pair e i, norm_sq_blkProj e i v]
    have hkey : ((Real.cos (τ i) - 1) * inner ℝ (e (i, Fin.castSucc 0)) v
            - Real.sin (τ i) * inner ℝ (e (i, 1)) v) ^ 2
          + (Real.sin (τ i) * inner ℝ (e (i, Fin.castSucc 0)) v
            + (Real.cos (τ i) - 1) * inner ℝ (e (i, 1)) v) ^ 2
        = ((Real.cos (τ i) - 1) ^ 2 + Real.sin (τ i) ^ 2)
          * ((inner ℝ (e (i, Fin.castSucc 0)) v) ^ 2 + (inner ℝ (e (i, 1)) v) ^ 2) := by
      ring
    rw [hkey, cos_sub_one_sq_add_sin_sq]
  rw [hsubsum, norm_sq_sum_of_orthogonal (fun i => c (blkProj e i v) - blkProj e i v) horth]
  exact Finset.sum_congr rfl (fun i _ => hnorm_i i)

/-! ## The target lemma -/

theorem weightDomination (r : ℕ) (hr : 0 < r)
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ (Submission.Mostow.E (2 * r)))
    (φ : Fin r → AddCircle (2 * Real.pi))
    (c : Submission.Mostow.E (2 * r) ≃ₗᵢ[ℝ] Submission.Mostow.E (2 * r))
    (hblock : ∀ (i : Fin r) (x y : ℝ), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧
      c (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
        (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
          (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (Wz W : Submission.Mostow.E (2 * r))
    (hdom : ∀ i : Fin r,
      ‖(inner ℝ (e (i, Fin.castSucc 0)) Wz) • e (i, Fin.castSucc 0) +
          (inner ℝ (e (i, 1)) Wz) • e (i, 1)‖ ≤
        ‖(inner ℝ (e (i, Fin.castSucc 0)) W) • e (i, Fin.castSucc 0) +
          (inner ℝ (e (i, 1)) W) • e (i, 1)‖) :
    ‖c Wz - Wz‖ ≤ ‖c W - W‖ := by
  classical
  -- extract the rotation angles from `hblock`
  choose t htφ ht using fun i => hblock i 1 0
  choose s hsφ hs using fun i => hblock i 0 1
  have hcos : ∀ i, Real.cos (s i) = Real.cos (t i) :=
    fun i => cos_congr_addCircle (by rw [hsφ i, htφ i])
  have hsin : ∀ i, Real.sin (s i) = Real.sin (t i) :=
    fun i => sin_congr_addCircle (by rw [hsφ i, htφ i])
  have h0 : ∀ i, c (e (i, Fin.castSucc 0)) =
      Real.cos (t i) • e (i, Fin.castSucc 0) + Real.sin (t i) • e (i, 1) := by
    intro i
    simpa using ht i
  have h1 : ∀ i, c (e (i, 1)) =
      - Real.sin (t i) • e (i, Fin.castSucc 0) + Real.cos (t i) • e (i, 1) := by
    intro i
    have h := hs i
    simp only [zero_smul, one_smul, zero_add, mul_zero, mul_one, zero_sub] at h
    rw [hcos i, hsin i] at h
    simpa using h
  have hWz := weightNorm_aux e c t h0 h1 Wz
  have hW := weightNorm_aux e c t h0 h1 W
  have hle : ∑ i : Fin r, 4 * Real.sin (t i / 2) ^ 2 * ‖blkProj e i Wz‖ ^ 2 ≤
      ∑ i : Fin r, 4 * Real.sin (t i / 2) ^ 2 * ‖blkProj e i W‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hnn : (0 : ℝ) ≤ 4 * Real.sin (t i / 2) ^ 2 := by positivity
    have hz : ‖blkProj e i Wz‖ ≤ ‖blkProj e i W‖ := by
      unfold blkProj
      exact hdom i
    have hsq : ‖blkProj e i Wz‖ ^ 2 ≤ ‖blkProj e i W‖ ^ 2 :=
      by nlinarith [hz, norm_nonneg (blkProj e i Wz), norm_nonneg (blkProj e i W)]
    exact mul_le_mul_of_nonneg_left hsq hnn
  have hfin : ‖c Wz - Wz‖ ^ 2 ≤ ‖c W - W‖ ^ 2 := by
    rw [hWz, hW]
    exact hle
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hfin

end Work.Mostow
