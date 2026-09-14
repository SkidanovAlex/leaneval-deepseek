import Mathlib
import Submission.Subspace.RothMain
import Submission.Commons.Algebra.MvPolynomial.coeff_indexTay_mul_factorial
import Submission.Commons.Algebra.MvPolynomial.coeff_aeval_dehomog_two_vars
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_mul_le

/-!
# The projective Roth lemma (two variables per block)

`roth_lemma` is the *affine* multivariate Roth lemma.  For the non-vanishing step of the
subspace theorem we need its *projective* form: a multihomogeneous
`G ∈ ℤ[X (h,0), X (h,1)]` of block-degrees `d h` and a point `x h = (x h 0, x h 1) ≠ 0`
of large projective height.

This file proves that form from `roth_lemma` by dehomogenising at a chart
(`X (h, c h) ↦ 1`, `X (h, 1 - c h) ↦ Y h`), using the chain rule
`pderiv h (projSubst c G) = projSubst c (pderiv (h, 1 - c h) G)` and the multivariate Taylor
coefficient formula `coeff_indexTay_mul_factorial`.
-/

open MvPolynomial
open scoped BigOperators

namespace Submission.Subspace

variable {m : ℕ}


lemma fin2_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

lemma fin2_sub_one_ne_self (x : Fin 2) : (1 : Fin 2) - x ≠ x := by
  fin_cases x <;> decide

/-- The "other" chart coordinate. -/
def otherChart (c : Fin m → Fin 2) (h : Fin m) : Fin m × Fin 2 := (h, 1 - c h)

lemma otherChart_injective (c : Fin m → Fin 2) : Function.Injective (otherChart c) := by
  intro a b hab
  simpa [otherChart] using congrArg Prod.fst hab


/-- The dehomogenisation substitution attached to a choice of chart `c h` in each block:
`X (h, c h) ↦ 1` and `X (h, 1 - c h) ↦ X h`. -/
noncomputable def projSubst (c : Fin m → Fin 2) :
    MvPolynomial (Fin m × Fin 2) ℤ →ₐ[ℤ] MvPolynomial (Fin m) ℤ :=
  MvPolynomial.aeval (fun hi : Fin m × Fin 2 =>
    if hi.2 = c hi.1 then 1 else MvPolynomial.X hi.1)

@[simp]
lemma projSubst_X_chart (c : Fin m → Fin 2) (h : Fin m) :
    projSubst c (MvPolynomial.X (h, c h)) = 1 := by
  rw [projSubst, MvPolynomial.aeval_X]; simp

lemma projSubst_X_other (c : Fin m → Fin 2) (h : Fin m) {i : Fin 2} (hi : i ≠ c h) :
    projSubst c (MvPolynomial.X (h, i)) = MvPolynomial.X h := by
  rw [projSubst, MvPolynomial.aeval_X]; simp [hi]

lemma pderiv_projSubst_X (c : Fin m → Fin 2) (h : Fin m) (i : Fin 2) (hi : i ≠ c h)
    (j : Fin m × Fin 2) :
    MvPolynomial.pderiv h (projSubst c (MvPolynomial.X j)) =
      projSubst c (MvPolynomial.pderiv (h, i) (MvPolynomial.X j)) := by
  rcases j with ⟨h', j'⟩
  by_cases hh : h' = h
  · subst hh
    simp only [projSubst, MvPolynomial.aeval_X, MvPolynomial.pderiv_X]
    rcases fin2_eq_zero_or_one j' with h1 | h1 <;> rw [h1] <;>
      rcases fin2_eq_zero_or_one i with h2 | h2 <;> rw [h2] <;>
      rcases fin2_eq_zero_or_one (c h') with h3 | h3 <;>
      simp_all
  · simp only [projSubst, MvPolynomial.aeval_X, MvPolynomial.pderiv_X]
    rcases fin2_eq_zero_or_one j' with h1 | h1 <;> rw [h1] <;>
      rcases fin2_eq_zero_or_one (c h') with h3 | h3 <;>
      simp_all

/-- The chain rule for the dehomogenisation substitution. -/
lemma pderiv_projSubst (c : Fin m → Fin 2) (h : Fin m) (i : Fin 2) (hi : i ≠ c h)
    (G : MvPolynomial (Fin m × Fin 2) ℤ) :
    MvPolynomial.pderiv h (projSubst c G) =
      projSubst c (MvPolynomial.pderiv (h, i) G) := by
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
        hp, pderiv_projSubst_X c h i hi j]

/-- The dehomogenisation substitution over `ℚ`. -/
noncomputable def projSubstQ (c : Fin m → Fin 2) :
    MvPolynomial (Fin m × Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin m) ℚ :=
  MvPolynomial.aeval (fun hi : Fin m × Fin 2 =>
    if hi.2 = c hi.1 then 1 else MvPolynomial.X hi.1)

@[simp]
lemma projSubstQ_X_chart (c : Fin m → Fin 2) (h : Fin m) :
    projSubstQ c (MvPolynomial.X (h, c h)) = 1 := by
  rw [projSubstQ, MvPolynomial.aeval_X]; simp

lemma projSubstQ_X_other (c : Fin m → Fin 2) (h : Fin m) {i : Fin 2} (hi : i ≠ c h) :
    projSubstQ c (MvPolynomial.X (h, i)) = MvPolynomial.X h := by
  rw [projSubstQ, MvPolynomial.aeval_X]; simp [hi]

lemma pderiv_projSubstQ_X (c : Fin m → Fin 2) (h : Fin m) (i : Fin 2) (hi : i ≠ c h)
    (j : Fin m × Fin 2) :
    MvPolynomial.pderiv h (projSubstQ c (MvPolynomial.X j)) =
      projSubstQ c (MvPolynomial.pderiv (h, i) (MvPolynomial.X j)) := by
  rcases j with ⟨h', j'⟩
  by_cases hh : h' = h
  · subst hh
    simp only [projSubstQ, MvPolynomial.aeval_X, MvPolynomial.pderiv_X]
    rcases fin2_eq_zero_or_one j' with h1 | h1 <;> rw [h1] <;>
      rcases fin2_eq_zero_or_one i with h2 | h2 <;> rw [h2] <;>
      rcases fin2_eq_zero_or_one (c h') with h3 | h3 <;>
      simp_all
  · simp only [projSubstQ, MvPolynomial.aeval_X, MvPolynomial.pderiv_X]
    rcases fin2_eq_zero_or_one j' with h1 | h1 <;> rw [h1] <;>
      rcases fin2_eq_zero_or_one (c h') with h3 | h3 <;>
      simp_all

lemma pderiv_projSubstQ (c : Fin m → Fin 2) (h : Fin m) (i : Fin 2) (hi : i ≠ c h)
    (G : MvPolynomial (Fin m × Fin 2) ℚ) :
    MvPolynomial.pderiv h (projSubstQ c G) =
      projSubstQ c (MvPolynomial.pderiv (h, i) G) := by
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
        hp, pderiv_projSubstQ_X c h i hi j]

lemma pderivIter_projSubstQ (c : Fin m → Fin 2) (J : Fin m →₀ ℕ)
    (G : MvPolynomial (Fin m × Fin 2) ℚ) :
    Commons.Algebra.MvPolynomial.pderivIter J (projSubstQ c G) =
      projSubstQ c (Commons.Algebra.MvPolynomial.pderivIter
        (J.mapDomain (otherChart c)) G) := by
  have hstep : ∀ (h : Fin m) (m' : Fin m →₀ ℕ),
      Commons.Algebra.MvPolynomial.pderivIter m' (projSubstQ c G) =
        projSubstQ c (Commons.Algebra.MvPolynomial.pderivIter
          (m'.mapDomain (otherChart c)) G) →
      Commons.Algebra.MvPolynomial.pderivIter (m' + Finsupp.single h 1) (projSubstQ c G) =
        projSubstQ c (Commons.Algebra.MvPolynomial.pderivIter
          ((m' + Finsupp.single h 1).mapDomain (otherChart c)) G) := by
    intro h m' hh
    have hmap : m'.mapDomain (otherChart c) + Finsupp.single (h, (1 : Fin 2) - c h) 1 =
        (m' + Finsupp.single h 1).mapDomain (otherChart c) := by
      rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
      rfl
    rw [← Commons.Algebra.MvPolynomial.pderivIter_properties.2.2.1 h m' (projSubstQ c G), hh,
      pderiv_projSubstQ c h (1 - c h) (fin2_sub_one_ne_self (c h))
        (Commons.Algebra.MvPolynomial.pderivIter (m'.mapDomain (otherChart c)) G),
      Commons.Algebra.MvPolynomial.pderivIter_properties.2.2.1 (h, (1 : Fin 2) - c h) _
        G, hmap]
  have hgen : ∀ (f : Fin m →₀ ℕ) (a : Fin m) (b : ℕ),
      (Commons.Algebra.MvPolynomial.pderivIter f (projSubstQ c G) =
        projSubstQ c (Commons.Algebra.MvPolynomial.pderivIter
          (f.mapDomain (otherChart c)) G)) →
      Commons.Algebra.MvPolynomial.pderivIter (f + Finsupp.single a b) (projSubstQ c G) =
        projSubstQ c (Commons.Algebra.MvPolynomial.pderivIter
          ((f + Finsupp.single a b).mapDomain (otherChart c)) G) := by
    intro f a b
    induction b with
    | zero => intro hf; simpa using hf
    | succ b ih =>
        intro hf
        rw [Finsupp.single_add, ← add_assoc]
        exact hstep a (f + Finsupp.single a b) (ih hf)
  refine Finsupp.induction₂ (motive := fun J =>
    Commons.Algebra.MvPolynomial.pderivIter J (projSubstQ c G) =
      projSubstQ c (Commons.Algebra.MvPolynomial.pderivIter
        (J.mapDomain (otherChart c)) G)) J ?_ ?_
  · rw [Finsupp.mapDomain_zero, Commons.Algebra.MvPolynomial.pderivIter_properties.1,
      Commons.Algebra.MvPolynomial.pderivIter_properties.1]
  · intro a b f _ _ hf
    exact hgen f a b hf

lemma eval_projSubstQ (c : Fin m → Fin 2) (β : Fin m → ℚ)
    (H : MvPolynomial (Fin m × Fin 2) ℚ) :
    MvPolynomial.aeval β (projSubstQ c H) =
      MvPolynomial.aeval
        (fun hi : Fin m × Fin 2 => if hi.2 = c hi.1 then (1 : ℚ) else β hi.1) H := by
  rw [projSubstQ, MvPolynomial.comp_aeval_apply]
  refine congrArg (fun g : Fin m × Fin 2 → ℚ => MvPolynomial.aeval g H) ?_
  funext hi
  by_cases h : hi.2 = c hi.1
  · simp [h]
  · simp [h, MvPolynomial.aeval_X]


lemma pderivIter_projSubst (c : Fin m → Fin 2) (J : Fin m →₀ ℕ)
    (G : MvPolynomial (Fin m × Fin 2) ℤ) :
    Commons.Algebra.MvPolynomial.pderivIter J (projSubst c G) =
      projSubst c (Commons.Algebra.MvPolynomial.pderivIter
        (J.mapDomain (otherChart c)) G) := by
  have hstep : ∀ (h : Fin m) (m' : Fin m →₀ ℕ),
      Commons.Algebra.MvPolynomial.pderivIter m' (projSubst c G) =
        projSubst c (Commons.Algebra.MvPolynomial.pderivIter (m'.mapDomain (otherChart c)) G) →
      Commons.Algebra.MvPolynomial.pderivIter (m' + Finsupp.single h 1) (projSubst c G) =
        projSubst c (Commons.Algebra.MvPolynomial.pderivIter
          ((m' + Finsupp.single h 1).mapDomain (otherChart c)) G) := by
    intro h m' hh
    have hmap : m'.mapDomain (otherChart c) + Finsupp.single (h, (1 : Fin 2) - c h) 1 =
        (m' + Finsupp.single h 1).mapDomain (otherChart c) := by
      rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
      rfl
    rw [← Commons.Algebra.MvPolynomial.pderivIter_properties.2.2.1 h m' (projSubst c G), hh,
      pderiv_projSubst c h (1 - c h) (fin2_sub_one_ne_self (c h))
        (Commons.Algebra.MvPolynomial.pderivIter (m'.mapDomain (otherChart c)) G),
      Commons.Algebra.MvPolynomial.pderivIter_properties.2.2.1 (h, (1 : Fin 2) - c h) _
        G, hmap]
  have hgen : ∀ (f : Fin m →₀ ℕ) (a : Fin m) (b : ℕ),
      (Commons.Algebra.MvPolynomial.pderivIter f (projSubst c G) =
        projSubst c (Commons.Algebra.MvPolynomial.pderivIter (f.mapDomain (otherChart c)) G)) →
      Commons.Algebra.MvPolynomial.pderivIter (f + Finsupp.single a b) (projSubst c G) =
        projSubst c (Commons.Algebra.MvPolynomial.pderivIter
          ((f + Finsupp.single a b).mapDomain (otherChart c)) G) := by
    intro f a b
    induction b with
    | zero => intro hf; simpa using hf
    | succ b ih =>
        intro hf
        rw [Finsupp.single_add, ← add_assoc]
        exact hstep a (f + Finsupp.single a b) (ih hf)
  refine Finsupp.induction₂ (motive := fun J =>
    Commons.Algebra.MvPolynomial.pderivIter J (projSubst c G) =
      projSubst c (Commons.Algebra.MvPolynomial.pderivIter (J.mapDomain (otherChart c)) G)) J ?_ ?_
  · rw [Finsupp.mapDomain_zero, Commons.Algebra.MvPolynomial.pderivIter_properties.1,
      Commons.Algebra.MvPolynomial.pderivIter_properties.1]
  · intro a b f _ _ hf
    exact hgen f a b hf


lemma fin2_eq_other {i j : Fin 2} (h : i ≠ j) : i = 1 - j := by
  revert h; fin_cases i <;> fin_cases j <;> decide

/-- The point encoded by the chart `c` and the affine parameter `β`. -/
noncomputable def chartPoint (c : Fin m → Fin 2) (β : Fin m → ℚ) : Fin m × Fin 2 → ℚ :=
  fun hi => if hi.2 = c hi.1 then 1 else β hi.1

lemma chartPoint_other (c : Fin m → Fin 2) (β : Fin m → ℚ) (h : Fin m) :
    chartPoint c β (h, 1 - c h) = β h := by
  simp [chartPoint, fin2_sub_one_ne_self]

lemma chartPoint_chart (c : Fin m → Fin 2) (β : Fin m → ℚ) (h : Fin m) :
    chartPoint c β (h, c h) = 1 := by
  simp [chartPoint]

/-- **Index comparison under dehomogenisation.**  The projective index of `G` at the chart
point is bounded by the affine index of the dehomogenisation at `β`. -/
lemma eval_eq_aeval' {σ : Type*} (α : σ → ℚ) (p : MvPolynomial σ ℚ) :
    MvPolynomial.eval α p = MvPolynomial.aeval α p := by
  simp [MvPolynomial.aeval_def]

lemma eval_projSubstQ' (c : Fin m → Fin 2) (β : Fin m → ℚ)
    (H : MvPolynomial (Fin m × Fin 2) ℚ) :
    MvPolynomial.eval β (projSubstQ c H) = MvPolynomial.eval (chartPoint c β) H := by
  rw [eval_eq_aeval', eval_eq_aeval' (chartPoint c β) H]
  exact eval_projSubstQ c β H

lemma indexWt_eq_sum {σ : Type*} [Fintype σ] (r : σ → ℕ) (m : σ →₀ ℕ) :
    Commons.Algebra.MvPolynomial.indexWt r m = m.sum (fun i k => (k : ℝ) / (r i : ℝ)) := by
  have h : ∀ x : σ, x ∉ Finsupp.support m →
      (m x : ℝ) / (r x : ℝ) = 0 := by
    intro x hx; rw [Finsupp.notMem_support_iff.mp hx]; simp
  rw [Commons.Algebra.MvPolynomial.indexWt, Finsupp.sum]
  exact (Finset.sum_subset (Finset.subset_univ (Finsupp.support m))
    (fun x _ hx => h x hx)).symm

lemma indexWt_mapDomain_otherChart (c : Fin m → Fin 2) (d : Fin m → ℕ) (J : Fin m →₀ ℕ) :
    Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin 2 => d hi.1)
        (J.mapDomain (otherChart c)) = Commons.Algebra.MvPolynomial.indexWt d J := by
  rw [indexWt_eq_sum, indexWt_eq_sum,
    Finsupp.sum_mapDomain_index (fun a => by simp) (fun a b1 b2 => by push_cast; ring)]
  exact Finsupp.sum_congr fun a _ => by rw [otherChart]

/-- **Index comparison under dehomogenisation.**  The projective index of `G` at the chart
point is bounded by the affine index of the dehomogenisation at `β`. -/
theorem index_chartPoint_le [NeZero m] (c : Fin m → Fin 2) (d : Fin m → ℕ) (β : Fin m → ℚ)
    (G : MvPolynomial (Fin m × Fin 2) ℚ) (hQ : projSubstQ c G ≠ 0) :
    index (chartPoint c β) (fun hi : Fin m × Fin 2 => d hi.1) G ≤
      index β d (projSubstQ c G) := by
  classical
  refine le_csInf ?_ ?_
  · rw [Commons.Algebra.MvPolynomial.indexSet_eq_image]
    exact Finset.image_nonempty.mpr (MvPolynomial.support_nonempty.mpr
      ((Commons.Algebra.MvPolynomial.indexTay_injective β).ne hQ))
  · intro t ht
    rw [Commons.Algebra.MvPolynomial.indexSet_eq_image, Finset.mem_coe, Finset.mem_image] at ht
    rcases ht with ⟨J, hJ, rfl⟩
    have hcoeff : (Commons.Algebra.MvPolynomial.indexTay β (projSubstQ c G)).coeff J ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hJ
    have hfact := Commons.Algebra.MvPolynomial.coeff_indexTay_mul_factorial β J (projSubstQ c G)
    have hfac : (∏ i : Fin m, ((J i).factorial : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have heval : MvPolynomial.eval β
        (Commons.Algebra.MvPolynomial.pderivIter J (projSubstQ c G)) ≠ 0 := by
      intro h0
      have h1 : (∏ i : Fin m, ((J i).factorial : ℚ)) *
          (Commons.Algebra.MvPolynomial.indexTay β (projSubstQ c G)).coeff J = 0 :=
        hfact.trans h0
      exact (mul_ne_zero hfac hcoeff) h1
    rw [pderivIter_projSubstQ c J G, eval_projSubstQ' c β] at heval
    have hJ' : J.mapDomain (otherChart c) ∈
        (Commons.Algebra.MvPolynomial.indexTay (chartPoint c β) G).support := by
      rw [MvPolynomial.mem_support_iff]
      intro h0
      refine heval ?_
      have h2 := Commons.Algebra.MvPolynomial.coeff_indexTay_mul_factorial (chartPoint c β)
        (J.mapDomain (otherChart c)) G
      rw [h0] at h2
      rw [mul_zero] at h2
      exact h2.symm
    have hmain : index (chartPoint c β) (fun hi : Fin m × Fin 2 => d hi.1) G ≤
        Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin 2 => d hi.1)
          (J.mapDomain (otherChart c)) := by
      refine csInf_le ?_ ?_
      · exact ⟨0, fun x hx => by
          rw [Commons.Algebra.MvPolynomial.indexSet_eq_image, Finset.mem_coe,
            Finset.mem_image] at hx
          rcases hx with ⟨m', -, rfl⟩
          exact Commons.Algebra.MvPolynomial.indexWt_nonneg _⟩
      · rw [Commons.Algebra.MvPolynomial.indexSet_eq_image, Finset.mem_coe, Finset.mem_image]
        exact ⟨_, hJ', rfl⟩
    rw [indexWt_mapDomain_otherChart] at hmain
    exact hmain

/-! ## The exponent vector of the dehomogenisation -/

open Commons.NumberTheory.Height.MvPolynomial (gP tP mulHeight_gP_eq gP_notMem
  mem_tP_iff mem_tP_none mem_tP_some)

/-- The exponent vector of `projSubst c G` corresponding to the monomial `Y ^ t`:
`(h, 1 - c h) ↦ t h` and `(h, c h) ↦ d h - t h`. -/
noncomputable def projExp (c : Fin m → Fin 2) (d : Fin m → ℕ) (t : Fin m →₀ ℕ) :
    Fin m × Fin 2 →₀ ℕ :=
  ∑ h : Fin m, (Finsupp.single (h, 1 - c h) (t h) + Finsupp.single (h, c h) (d h - t h))

lemma projExp_apply (c : Fin m → Fin 2) (d : Fin m → ℕ) (t : Fin m →₀ ℕ)
    (h : Fin m) (j : Fin 2) :
    projExp c d t (h, j) =
      (if (1 : Fin 2) - c h = j then t h else 0) +
      (if c h = j then d h - t h else 0) := by
  classical
  rw [projExp, Finsupp.finsetSum_apply, Finset.sum_eq_single h]
  · simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq, true_and]
  · intro h' _ hne
    simp [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq, hne]
  · intro hnot
    simp at hnot

lemma projExp_apply_other (c : Fin m → Fin 2) (d : Fin m → ℕ) (t : Fin m →₀ ℕ)
    (h : Fin m) : projExp c d t (h, 1 - c h) = t h := by
  rw [projExp_apply, if_pos rfl, if_neg (Ne.symm (fin2_sub_one_ne_self (c h))), add_zero]

lemma projExp_apply_chart (c : Fin m → Fin 2) (d : Fin m → ℕ) (t : Fin m →₀ ℕ)
    (h : Fin m) : projExp c d t (h, c h) = d h - t h := by
  rw [projExp_apply, if_neg (fin2_sub_one_ne_self (c h)), zero_add, if_pos rfl]

lemma projExp_sum_coords (c : Fin m → Fin 2) (d : Fin m → ℕ) (t : Fin m →₀ ℕ)
    (h : Fin m) :
    projExp c d t (h, 0) + projExp c d t (h, 1) = t h + (d h - t h) := by
  rcases fin2_eq_zero_or_one (c h) with hc | hc
  · have h2 := projExp_apply_chart c d t h
    rw [hc] at h2
    have h1 := projExp_apply_other c d t h
    rw [hc, (by decide : (1 : Fin 2) - 0 = 1)] at h1
    rw [h2, h1]
    omega
  · have h1 := projExp_apply_other c d t h
    rw [hc, (by decide : (1 : Fin 2) - 1 = 0)] at h1
    have h2 := projExp_apply_chart c d t h
    rw [hc] at h2
    rw [h2, h1]

/-- The exponent vector formed by the "other" chart coordinates of a block exponent vector. -/
noncomputable def otherExp (c : Fin m → Fin 2) (u : (Fin m × Fin 2) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.indicator Finset.univ (fun h _ => u (h, 1 - c h))

lemma otherExp_apply (c : Fin m → Fin 2) (u : (Fin m × Fin 2) →₀ ℕ) (h : Fin m) :
    otherExp c u h = u (h, 1 - c h) := by
  simp [otherExp]

/-- **Coefficients of the blockwise dehomogenisation** (`K = ℚ` version). -/
theorem coeff_projSubstQ_eq (c : Fin m → Fin 2) (d : Fin m → ℕ)
    (G : MvPolynomial (Fin m × Fin 2) ℚ)
    (hhom : ∀ u ∈ G.support, ∀ h, u (h, 0) + u (h, 1) = d h) (t : Fin m →₀ ℕ) :
    (projSubstQ c G).coeff t = G.coeff (projExp c d t) := by
  unfold projSubstQ projExp
  exact Commons.Algebra.MvPolynomial.coeff_aeval_dehomog_two_vars c d G hhom t

/-- The dehomogenisation `projSubstQ c` is the `ℚ`-base change of `projSubst c`. -/
lemma projSubst_map (c : Fin m → Fin 2) (G : MvPolynomial (Fin m × Fin 2) ℤ) :
    projSubstQ c (G.map (Int.castRingHom ℚ)) =
      (projSubst c G).map (Int.castRingHom ℚ) := by
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      have hX : projSubstQ c (MvPolynomial.X j) =
          (projSubst c (MvPolynomial.X j)).map (Int.castRingHom ℚ) := by
        rw [projSubst, projSubstQ, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        by_cases h : j.2 = c j.1
        · simp [h]
        · simp [h]
      simp only [map_mul, MvPolynomial.map_X, hp, hX]

/-- **Coefficients of the blockwise dehomogenisation** (`ℤ` version). -/
lemma coeff_projSubst_eq (c : Fin m → Fin 2) (d : Fin m → ℕ)
    (G : MvPolynomial (Fin m × Fin 2) ℤ)
    (hhom : ∀ u ∈ G.support, ∀ h, u (h, 0) + u (h, 1) = d h) (t : Fin m →₀ ℕ) :
    (projSubst c G).coeff t = G.coeff (projExp c d t) := by
  have hhomQ : ∀ u ∈ (G.map (Int.castRingHom ℚ)).support, ∀ h, u (h, 0) + u (h, 1) = d h :=
    fun u hu h => hhom u (MvPolynomial.support_map_subset (Int.castRingHom ℚ) G hu) h
  have h := coeff_projSubstQ_eq c d (G.map (Int.castRingHom ℚ)) hhomQ t
  rw [projSubst_map, MvPolynomial.coeff_map, MvPolynomial.coeff_map] at h
  exact Int.cast_injective h

/-- An exponent vector `u` of a multihomogeneous polynomial with `u (h,0) + u (h,1) = d h`
equals `projExp c d` applied to its "other chart" exponents. -/
lemma projExp_eq_self_of_hom (c : Fin m → Fin 2) (d : Fin m → ℕ)
    (u : (Fin m × Fin 2) →₀ ℕ) (hhom : ∀ h, u (h, 0) + u (h, 1) = d h) :
    projExp c d (otherExp c u) = u := by
  ext a
  rcases a with ⟨h, j⟩
  rcases Commons.Algebra.MvPolynomial.fin2_eq_or_sub (c h) j with hj | hj
  · subst hj
    rw [projExp_apply_chart, otherExp_apply]
    have hperm := Commons.Algebra.MvPolynomial.block_perm u c h
    have hh := hhom h
    omega
  · subst hj
    rw [projExp_apply_other, otherExp_apply]

/-- (A) The dehomogenisation of a nonzero multihomogeneous polynomial is nonzero. -/
theorem projSubstQ_ne_zero (c : Fin m → Fin 2) (d : Fin m → ℕ)
    (G : MvPolynomial (Fin m × Fin 2) ℚ) (hG : G ≠ 0)
    (hhom : ∀ u ∈ G.support, ∀ h, u (h, 0) + u (h, 1) = d h) :
    projSubstQ c G ≠ 0 := by
  classical
  intro hQ
  obtain ⟨u, hu⟩ := MvPolynomial.support_nonempty.mpr hG
  have hcoeff : G.coeff u ≠ 0 := MvPolynomial.mem_support_iff.mp hu
  refine hcoeff ?_
  have h := coeff_projSubstQ_eq c d G hhom (otherExp c u)
  rw [hQ, MvPolynomial.coeff_zero] at h
  have hproj : projExp c d (otherExp c u) = u :=
    projExp_eq_self_of_hom c d u (fun h => hhom u hu h)
  rw [hproj] at h
  exact h.symm

/-- Membership of `some t` in `tP P`. -/
lemma some_mem_tP_iff {τ : Type*} [Fintype τ] {P : MvPolynomial τ ℚ} {t : τ →₀ ℕ} :
    some t ∈ Commons.NumberTheory.Height.MvPolynomial.tP P ↔ t ∈ P.support := by
  rw [Commons.NumberTheory.Height.MvPolynomial.mem_tP_iff]
  constructor
  · rintro (h | ⟨m, hm, hsm⟩)
    · exact absurd h (by simp)
    · rw [Option.some.inj hsm] at hm
      exact hm
  · intro h; exact Or.inr ⟨t, h, rfl⟩

/-- Height comparison: if the coefficients of `Q'` are coefficients of `Q` (via `Φ`), then the
height of `gP Q'` does not exceed that of `gP Q`. -/
theorem mulHeight_gP_le_of_coeff_map {σ τ : Type*} [Fintype σ] [Fintype τ]
    (Q : MvPolynomial σ ℚ) (Q' : MvPolynomial τ ℚ) (Φ : (τ →₀ ℕ) → (σ →₀ ℕ))
    (hΦ : ∀ t ∈ Q'.support, Q'.coeff t = Q.coeff (Φ t)) :
    Height.mulHeight (gP Q') ≤ Height.mulHeight (gP Q) := by
  classical
  have hmem : ∀ o ∈ tP Q', Option.map Φ o ∈ tP Q := by
    intro o ho
    rw [mem_tP_iff Q'] at ho
    rw [mem_tP_iff Q]
    rcases ho with rfl | ⟨t, ht, rfl⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨Φ t, ?_, rfl⟩
      have ht' : t ∈ Q'.support := ht
      rw [MvPolynomial.mem_support_iff] at ht ⊢
      rw [← hΦ t ht']
      exact ht
  let Ξ : ↥(tP Q') → ↥(tP Q) := fun i => ⟨Option.map Φ i.val, hmem i.val i.property⟩
  have hcomp : (fun i : ↥(tP Q') => gP Q' i) = (fun j : ↥(tP Q) => gP Q j) ∘ Ξ := by
    funext i
    obtain ⟨o, ho⟩ := i
    cases o with
    | none => rfl
    | some t => exact hΦ t (some_mem_tP_iff.mp ho)
  calc Height.mulHeight (gP Q')
      = Height.mulHeight (fun i : ↥(tP Q') => gP Q' i) := mulHeight_gP_eq Q'
    _ = Height.mulHeight ((fun j : ↥(tP Q) => gP Q j) ∘ Ξ) := by rw [hcomp]
    _ ≤ Height.mulHeight (fun j : ↥(tP Q) => gP Q j) := Height.mulHeight_comp_le Ξ _
    _ = Height.mulHeight (gP Q) := (mulHeight_gP_eq Q).symm

/-- (B) The dehomogenisation does not increase the height. -/
theorem hZ_projSubst_le (c : Fin m → Fin 2) (d : Fin m → ℕ)
    (G : MvPolynomial (Fin m × Fin 2) ℤ)
    (hhom : ∀ u ∈ G.support, ∀ h, u (h, 0) + u (h, 1) = d h) :
    hZ (projSubst c G) ≤ hZ G := by
  simp only [hZ, Height.logHeight_eq_log_mulHeight]
  refine Real.log_le_log ?_ ?_
  · rw [mulHeight_gP_eq]
    exact Height.mulHeight_pos _
  · apply mulHeight_gP_le_of_coeff_map _ _ (projExp c d)
    intro t _
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, coeff_projSubst_eq c d G hhom t]

/-- (C) The projective Roth lemma (two variables per block), in the form needed later: `G` is
only *weighted* homogeneous, with block degrees `e h ≥ 1` that may be smaller than the weights
`d h ≥ e h` used in the index. -/
theorem roth_proj [NeZero m] (G : MvPolynomial (Fin m × Fin 2) ℤ) (d e : Fin m → ℕ)
    (hd : ∀ h, 1 ≤ d h) (hle : ∀ h, e h ≤ d h)
    (hG : G ≠ 0)
    (hhom : ∀ u ∈ G.support, ∀ h, u (h, 0) + u (h, 1) = e h)
    (c : Fin m → Fin 2) (β : Fin m → ℚ) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hratio : ∀ i j : Fin m, i ≤ j →
      (d i : ℝ) ≤ η ^ (2 ^ (m - 1) * ((j : ℕ) - (i : ℕ))) * (d j : ℝ))
    (hcond : η ^ (2 ^ (m - 1)) * (⨅ h : Fin m, (d h : ℝ) * Height.logHeight₁ (β h)) ≥
      hZ G + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ))) :
    index (chartPoint c β) (fun hi : Fin m × Fin 2 => d hi.1) (G.map (Int.castRingHom ℚ)) ≤
      4 * (m : ℝ) * η := by
  classical
  have hcast : Function.Injective (Int.castRingHom ℚ) := fun a b hab => Int.cast_injective hab
  have hGq : G.map (Int.castRingHom ℚ) ≠ 0 := fun h => hG (MvPolynomial.map_injective (Int.castRingHom ℚ) hcast h)
  have hhomQ : ∀ u ∈ (G.map (Int.castRingHom ℚ)).support, ∀ h, u (h, 0) + u (h, 1) = e h :=
    fun u hu h => hhom u (MvPolynomial.support_map_subset (Int.castRingHom ℚ) G hu) h
  have hQq : projSubstQ c (G.map (Int.castRingHom ℚ)) ≠ 0 :=
    projSubstQ_ne_zero c e _ hGq hhomQ
  have hQ : projSubst c G ≠ 0 := by
    intro h
    exact hQq (by rw [projSubst_map, h, map_zero])
  have hdeg : ∀ t ∈ (projSubst c G).support, ∀ h : Fin m, t h ≤ d h := by
    intro t ht h
    have hc : G.coeff (projExp c e t) ≠ 0 := by
      rw [← coeff_projSubst_eq c e G hhom t]
      exact MvPolynomial.mem_support_iff.mp ht
    have hmem : projExp c e t ∈ G.support := MvPolynomial.mem_support_iff.mpr hc
    have hh := hhom _ hmem h
    rw [projExp_sum_coords] at hh
    have h1 : t h ≤ e h := by omega
    exact le_trans h1 (hle h)
  have hcond' : η ^ (2 ^ (m - 1)) * (⨅ h : Fin m, (d h : ℝ) * Height.logHeight₁ (β h)) ≥
      hZ (projSubst c G) + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ)) := by
    have := hZ_projSubst_le c e G hhom
    linarith
  have hmain := roth_lemma (P := projSubst c G) hQ d hd hdeg β η hη0 hη hratio hcond'
  calc index (chartPoint c β) (fun hi : Fin m × Fin 2 => d hi.1) (G.map (Int.castRingHom ℚ))
      ≤ index β d (projSubstQ c (G.map (Int.castRingHom ℚ))) :=
        index_chartPoint_le c d β (G.map (Int.castRingHom ℚ)) hQq
    _ = index β d ((projSubst c G).map (Int.castRingHom ℚ)) := by rw [projSubst_map]
    _ ≤ 4 * (m : ℝ) * η := hmain

end Submission.Subspace
