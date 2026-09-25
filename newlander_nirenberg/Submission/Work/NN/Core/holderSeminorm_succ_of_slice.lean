/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Hölder seminorm of order `k+1` from the seminorms of the slices

This file proves `Work.NN.Core.holderSeminorm_succ_of_slice`: if `v` is of class `C^{k+1}` on a
uniqueness domain `Ω ⊆ ℂⁿ` and each *slice* `z ↦ D^k v(z)[u]` of the `k`-th derivative has finite
Hölder seminorm of order `α` at order `1`, then the `(k+1)`-th derivative of `v` itself has finite
Hölder seminorm of order `α` on `Ω`.

The point is that `D^{k+1}v(z)` is a `(k+1)`-multilinear map whose "value on the slice `u`"
is the derivative of the slice at `u`, so the seminorm of `D^{k+1}v` is a supremum over the
continuum of slices `u`; to bound it one expands an arbitrary argument tuple in the standard
*real* basis `1, I` of `ℂⁿ`.  Since `∥D^{k+1}v(x)·w - D^{k+1}v(y)·w∥` is bounded by
`(∏ i, ∥w i∥) • Σ_r ∥D^{k+1}v(x)·δ_r - D^{k+1}v(y)·δ_r∥` for the finitely many basis tuples `δ_r`
(lemma `norm_apply_le_sum_bvec`), only finitely many slices are needed, and each of them is
controlled by the hypothesis.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Core

open scoped NNReal ENNReal
open Set

noncomputable section

/-! ### The standard real coordinates of `ℂⁿ` -/

/-- The `2n` vectors of the standard *real* basis of `ℂⁿ = (Fin n → ℂ)`: the `j`-th standard basis
vector, multiplied by `1` or by `I`. -/
private def nnBvec (n : ℕ) (j : Fin n) (b : Bool) : (Fin n → ℂ) :=
  if b then Pi.single j Complex.I else Pi.single j 1

private lemma nnBvec_norm_le (n : ℕ) (j : Fin n) (b : Bool) : ‖nnBvec n j b‖ ≤ 1 := by
  rw [nnBvec]; split <;> rw [Pi.norm_single] <;> simp

/-- The real coordinate of a complex number in the basis `(1, I)`. -/
private def nnCoef (z : ℂ) (b : Bool) : ℝ := if b then z.im else z.re

@[simp] private lemma nnCoef_true (z : ℂ) : nnCoef z true = z.im := by rw [nnCoef]; simp
@[simp] private lemma nnCoef_false (z : ℂ) : nnCoef z false = z.re := by rw [nnCoef]; simp

private lemma abs_nnCoef_le (z : ℂ) (b : Bool) : |nnCoef z b| ≤ ‖z‖ := by
  rw [nnCoef]; split
  · exact Complex.abs_im_le_norm z
  · exact Complex.abs_re_le_norm z

private lemma nnCoef_smul_nnBvec (n : ℕ) (z : Fin n → ℂ) (j : Fin n) :
    nnCoef (z j) true • nnBvec n j true + nnCoef (z j) false • nnBvec n j false
      = Pi.single j (z j) := by
  rw [nnCoef_true, nnCoef_false]
  ext j'
  by_cases h : j' = j
  · rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    rw [show nnBvec n j true j = Complex.I from by rw [nnBvec]; simp,
      show nnBvec n j false j = (1:ℂ) from by rw [nnBvec]; simp]
    simp only [Complex.real_smul, mul_one]
    conv_rhs => rw [← Complex.re_add_im (z j)]
    ring
  · simp [h, nnBvec]

/-- Decomposition of a vector of `ℂⁿ` in the standard real basis. -/
private lemma sum_nnCoef_smul_nnBvec (n : ℕ) (z : Fin n → ℂ) :
    ∑ p : Fin n × Bool, nnCoef (z p.1) p.2 • nnBvec n p.1 p.2 = z := by
  calc ∑ p : Fin n × Bool, nnCoef (z p.1) p.2 • nnBvec n p.1 p.2
      = ∑ j : Fin n, ∑ b : Bool, nnCoef (z j) b • nnBvec n j b := Fintype.sum_prod_type _
    _ = ∑ j : Fin n, (nnCoef (z j) true • nnBvec n j true
          + nnCoef (z j) false • nnBvec n j false) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Fintype.sum_bool]
    _ = ∑ j : Fin n, Pi.single j (z j) := Finset.sum_congr rfl fun j _ => nnCoef_smul_nnBvec n z j
    _ = z := Finset.univ_sum_single z

/-- The tuple of basis vectors indexed by `r : Fin m → (Fin n × Bool)`. -/
private def bvecTuple {m n : ℕ} (r : Fin m → (Fin n × Bool)) : Fin m → (Fin n → ℂ) :=
  fun i => nnBvec n (r i).1 (r i).2

private lemma bvecTuple_norm_le {m n : ℕ} (r : Fin m → (Fin n × Bool)) (i : Fin m) :
    ‖bvecTuple r i‖ ≤ 1 := nnBvec_norm_le n (r i).1 (r i).2

/-- The product of the real coordinates of the tuple `w` along the multi-index `r`. -/
private def bcoefProd {m n : ℕ} (w : Fin m → (Fin n → ℂ)) (r : Fin m → (Fin n × Bool)) : ℝ :=
  ∏ i, nnCoef (w i (r i).1) (r i).2

private lemma abs_bcoefProd_le {m n : ℕ} (w : Fin m → (Fin n → ℂ))
    (r : Fin m → (Fin n × Bool)) : |bcoefProd w r| ≤ ∏ i, ‖w i‖ := by
  rw [bcoefProd, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  exact le_trans (abs_nnCoef_le _ _) (norm_le_pi_norm _ _)

/-! ### Expansion of a multilinear map in the standard basis -/

/-- Expansion of a continuous multilinear map `T` at a tuple `w` in the standard real basis of
`ℂⁿ`: `T w = Σ_r (∏ i, cᵢ(rᵢ)) • T δ_r`. -/
private lemma multilinear_expansion {m n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin n → ℂ)) ℂ)
    (w : Fin m → (Fin n → ℂ)) :
    T w = ∑ r : Fin m → (Fin n × Bool), bcoefProd w r • T (bvecTuple r) := by
  have hw : (fun i : Fin m => ∑ p : Fin n × Bool, nnCoef (w i p.1) p.2 • nnBvec n p.1 p.2) = w :=
    funext fun i => sum_nnCoef_smul_nnBvec n (w i)
  have key : T (fun i : Fin m => ∑ p : Fin n × Bool, nnCoef (w i p.1) p.2 • nnBvec n p.1 p.2)
      = ∑ r : Fin m → (Fin n × Bool), bcoefProd w r • T (bvecTuple r) := by
    rw [ContinuousMultilinearMap.map_sum (g := fun (i : Fin m) (p : Fin n × Bool) =>
      nnCoef (w i p.1) p.2 • nnBvec n p.1 p.2)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
    rfl
  simpa [hw] using key

/-- The operator norm of a multilinear map at an arbitrary tuple is bounded by `∏ i, ‖w i‖` times
the sum of its values on the finitely many standard basis tuples. -/
private lemma norm_apply_le_sum_bvec {m n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin n → ℂ)) ℂ)
    (w : Fin m → (Fin n → ℂ)) :
    ‖T w‖ ≤ (∑ r : Fin m → (Fin n × Bool), ‖T (bvecTuple r)‖) * ∏ i, ‖w i‖ := by
  have step1 : ‖T w‖ ≤ ∑ r : Fin m → (Fin n × Bool), ‖bcoefProd w r • T (bvecTuple r)‖ := by
    rw [multilinear_expansion T w]
    exact norm_sum_le _ _
  have step2 : ∀ r : Fin m → (Fin n × Bool),
      ‖bcoefProd w r • T (bvecTuple r)‖ = |bcoefProd w r| * ‖T (bvecTuple r)‖ := by
    intro r
    rw [norm_smul, Real.norm_eq_abs]
  calc ‖T w‖
      ≤ ∑ r : Fin m → (Fin n × Bool), ‖bcoefProd w r • T (bvecTuple r)‖ := step1
    _ = ∑ r, |bcoefProd w r| * ‖T (bvecTuple r)‖ :=
        Finset.sum_congr rfl fun r _ => step2 r
    _ ≤ ∑ r, (∏ i, ‖w i‖) * ‖T (bvecTuple r)‖ :=
        Finset.sum_le_sum fun r _ =>
          mul_le_mul_of_nonneg_right (abs_bcoefProd_le w r) (norm_nonneg _)
    _ = (∏ i, ‖w i‖) * ∑ r, ‖T (bvecTuple r)‖ := by
        rw [Finset.mul_sum]
    _ = (∑ r, ‖T (bvecTuple r)‖) * ∏ i, ‖w i‖ := mul_comm _ _

/-! ### The derivative of a slice -/

/-- The derivative of a slice `z ↦ D^k v(z)[u]` is the partial application of `D^{k+1}v`: the
`(k+1)`-th derivative at `Fin.cons a u` is the derivative at `a` of the slice in the direction `u`.

The identity follows from the (definitional) recursion for `iteratedFDerivWithin` together with the
chain rule for the continuous linear evaluation map `W ↦ W u`. -/
private lemma iteratedFDerivWithin_succ_apply_cons {n k : ℕ} {Ω : Set (Fin n → ℂ)}
    {v : (Fin n → ℂ) → ℂ}
    (hdiff : DifferentiableOn ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z) Ω)
    (hΩ : UniqueDiffOn ℝ Ω) {x : Fin n → ℂ} (hx : x ∈ Ω)
    (a : Fin n → ℂ) (u : Fin k → (Fin n → ℂ)) :
    iteratedFDerivWithin ℝ (k+1) v Ω x (Fin.cons a u)
      = fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z u) Ω x a := by
  have hΨ : HasFDerivWithinAt (fun z => iteratedFDerivWithin ℝ k v Ω z)
      (fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z) Ω x) Ω x :=
    (hdiff x hx).hasFDerivWithinAt
  have hcomp : HasFDerivWithinAt (fun z => iteratedFDerivWithin ℝ k v Ω z u)
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ u) ∘SL
        (fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z) Ω x)) Ω x := by
    exact HasFDerivWithinAt.comp (x) (s := Ω) (t := Set.univ)
      (g := fun W : ContinuousMultilinearMap ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ => W u)
      (g' := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ u)
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ u).hasFDerivWithinAt hΨ
      (fun y _ => Set.mem_univ _)
  rw [iteratedFDerivWithin_succ_apply_left (Fin.cons a u), hcomp.fderivWithin (hΩ x hx)]
  simp [Fin.cons_zero, Fin.tail_cons, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.apply_apply]

/-! ### The main theorem -/

theorem holderSeminorm_succ_of_slice {n k : ℕ} {α : ℝ} {Ω : Set (Fin n → ℂ)} {v : (Fin n → ℂ) → ℂ} (hΩ : UniqueDiffOn ℝ Ω) (hv : ContDiffOn ℝ ((k+1 : ℕ) : WithTop ENat) v Ω) (h : ∀ u : Fin k → (Fin n → ℂ), Work.CR.Flat.holderSeminorm 1 α (fun z => iteratedFDerivWithin ℝ k v Ω z u) Ω < ⊤) : Work.CR.Flat.holderSeminorm (k+1) α v Ω < ⊤ := by
  -- the `k`-th iterated derivative is differentiable on `Ω`
  have hdiff : DifferentiableOn ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z) Ω :=
    hv.differentiableOn_iteratedFDerivWithin (by exact_mod_cast Nat.lt_succ_self k) hΩ
  -- the slice identity
  have hslice : ∀ x ∈ Ω, ∀ (a : Fin n → ℂ) (u : Fin k → (Fin n → ℂ)),
      iteratedFDerivWithin ℝ (k+1) v Ω x (Fin.cons a u)
        = fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z u) Ω x a :=
    fun x hx a u => iteratedFDerivWithin_succ_apply_cons hdiff hΩ hx a u
  -- the finite family of slices which controls the `(k+1)`-st derivative
  set P : (Fin (k+1) → (Fin n × Bool)) → ℝ≥0∞ := fun r =>
    Work.CR.Flat.holderSeminorm 1 α
      (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω with hP
  have hP_lt : ∀ r, P r < ⊤ := by
    intro r
    rw [hP]
    exact h (Fin.tail (bvecTuple r))
  have hsum_lt : (∑ r, P r) < ⊤ := ENNReal.sum_lt_top.mpr (fun r _ => hP_lt r)
  -- the pointwise Hölder estimate
  have hmain : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y →
      ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ (k+1) v Ω x - iteratedFDerivWithin ℝ (k+1) v Ω y‖
          / ‖x - y‖ ^ α) ≤ ∑ r, P r := by
    intro x hx y hy hxy
    have hpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    -- for each basis tuple, the difference of the `(k+1)`-st derivatives is a slice difference
    have hnorm : ∀ r : Fin (k+1) → (Fin n × Bool),
        ‖(iteratedFDerivWithin ℝ (k+1) v Ω x - iteratedFDerivWithin ℝ (k+1) v Ω y)
            (bvecTuple r)‖ ≤ (P r).toReal * ‖x - y‖ ^ α := by
      intro r
      rw [sub_apply]
      have hAx : iteratedFDerivWithin ℝ (k+1) v Ω x (bvecTuple r)
          = fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r)))
              Ω x ((bvecTuple r) 0) := by
        conv_lhs => rw [← Fin.cons_self_tail (bvecTuple r)]
        exact hslice x hx ((bvecTuple r) 0) (Fin.tail (bvecTuple r))
      have hAy : iteratedFDerivWithin ℝ (k+1) v Ω y (bvecTuple r)
          = fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r)))
              Ω y ((bvecTuple r) 0) := by
        conv_lhs => rw [← Fin.cons_self_tail (bvecTuple r)]
        exact hslice y hy ((bvecTuple r) 0) (Fin.tail (bvecTuple r))
      rw [hAx, hAy]
      have hAB : ‖fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω x
            - fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω y‖
          ≤ (P r).toReal * ‖x - y‖ ^ α := by
        have hsn : ENNReal.ofReal
            (‖iteratedFDerivWithin ℝ 1
                (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω x
              - iteratedFDerivWithin ℝ 1
                (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω y‖
              / ‖x - y‖ ^ α) ≤ P r := by
          rw [hP]
          exact Work.CR.Flat.le_holderSeminorm 1 α
            (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω hx hy hxy
        rw [← dist_eq_norm, dist_iteratedFDerivWithin_one _ _ (hΩ x hx) (hΩ y hy),
          dist_eq_norm] at hsn
        have hreal := (ENNReal.ofReal_le_iff_le_toReal (hP_lt r).ne).mp hsn
        exact (div_le_iff₀ hpos).mp hreal
      calc ‖(fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω x)
              ((bvecTuple r) 0)
            - (fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω y)
              ((bvecTuple r) 0)‖
          = ‖(fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω x
              - fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω y)
              ((bvecTuple r) 0)‖ := by rw [sub_apply]
        _ ≤ ‖fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω x
              - fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω y‖
              * ‖(bvecTuple r) 0‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω x
              - fderivWithin ℝ (fun z => iteratedFDerivWithin ℝ k v Ω z (Fin.tail (bvecTuple r))) Ω y‖
              * 1 := by gcongr; exact bvecTuple_norm_le r 0
        _ ≤ (P r).toReal * ‖x - y‖ ^ α := by rw [mul_one]; exact hAB
    -- sum over the finitely many basis tuples
    have hsum_bound : (∑ r : Fin (k+1) → (Fin n × Bool),
        ‖(iteratedFDerivWithin ℝ (k+1) v Ω x - iteratedFDerivWithin ℝ (k+1) v Ω y)
            (bvecTuple r)‖) ≤ (∑ r, P r).toReal * ‖x - y‖ ^ α := by
      rw [ENNReal.toReal_sum (fun r _ => (hP_lt r).ne), Finset.sum_mul]
      exact Finset.sum_le_sum fun r _ => hnorm r
    -- and use the multilinear expansion to bound the operator norm
    have hop : ‖iteratedFDerivWithin ℝ (k+1) v Ω x - iteratedFDerivWithin ℝ (k+1) v Ω y‖
        ≤ (∑ r, P r).toReal * ‖x - y‖ ^ α := by
      rw [ContinuousMultilinearMap.opNorm_le_iff
        (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg _) α))]
      intro w
      exact le_trans (norm_apply_le_sum_bvec _ w)
        (mul_le_mul_of_nonneg_right hsum_bound (Finset.prod_nonneg fun i _ => norm_nonneg _))
    have hfinal : ‖iteratedFDerivWithin ℝ (k+1) v Ω x - iteratedFDerivWithin ℝ (k+1) v Ω y‖
        / ‖x - y‖ ^ α ≤ (∑ r, P r).toReal := (div_le_iff₀ hpos).mpr hop
    calc ENNReal.ofReal
          (‖iteratedFDerivWithin ℝ (k+1) v Ω x - iteratedFDerivWithin ℝ (k+1) v Ω y‖
            / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal (∑ r, P r).toReal := ENNReal.ofReal_le_ofReal hfinal
      _ = ∑ r, P r := ENNReal.ofReal_toReal hsum_lt.ne
  refine lt_of_le_of_lt ?_ hsum_lt
  unfold Work.CR.Flat.holderSeminorm
  exact iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => hmain x hx y hy hxy

end

end Work.NN.Core
