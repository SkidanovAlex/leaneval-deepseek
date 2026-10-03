import Mathlib

open scoped BigOperators

namespace Work.Peluse.Ulower

/-- `z * star z` is the (nonnegative) real number `‖z‖ ^ 2`, coerced to `ℂ`. -/
private lemma mul_star_self_eq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma star_coe (c : ℝ) : star ((c : ℝ) : ℂ) = ((c : ℝ) : ℂ) := by
  rw [Complex.star_def]
  exact Complex.conj_ofReal c

/-- The complex identity: the squared norm of a weighted sum expands. -/
private lemma norm_sq_eq_sum {κ : Type*} [Fintype κ] (u v : κ → ℂ) (W : κ → ℝ) :
    (((‖∑ k, ((W k : ℝ) : ℂ) * (u k * star (v k))‖ ^ 2 : ℝ)) : ℂ)
      = ∑ k, ∑ l, ((W k * W l : ℝ) : ℂ) * ((u k * star (u l)) * (star (v k) * v l)) := by
  rw [← mul_star_self_eq]
  congr 1
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [star_mul, star_mul, star_star, star_coe, Complex.ofReal_mul]
  ring

/-- The unweighted case of `norm_sq_eq_sum`. -/
private lemma norm_sq_eq_sum_one {κ : Type*} [Fintype κ] (u v : κ → ℂ) :
    (((‖∑ k, u k * star (v k)‖ ^ 2 : ℝ)) : ℂ)
      = ∑ k, ∑ l, (u k * star (u l)) * (star (v k) * v l) := by
  have h := norm_sq_eq_sum u v (fun _ => (1 : ℝ))
  simpa using h

/-- Rearrangement of a quadruple sum (the two middle blocks are exchanged). -/
private lemma four_sum_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
      = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact Finset.sum_comm (s := Finset.univ) (f := fun b c => ∑ d, f a b c d)
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d :=
        Finset.sum_comm (s := Finset.univ) (f := fun a c => ∑ b, ∑ d, f a b c d)
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        refine Finset.sum_congr rfl (fun a _ => ?_)
        exact Finset.sum_comm (s := Finset.univ) (f := fun b d => f a b c d)
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        exact Finset.sum_comm (s := Finset.univ) (f := fun a d => ∑ b, f a b c d)

/-- The weighted Frobenius/transpose identity for the row Gram matrix. -/
theorem weightedFrobSwap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℂ) (W : κ → ℝ) :
    (∑ i, ∑ j, ‖∑ k, ((W k : ℝ) : ℂ) * (A i k * star (A j k))‖ ^ 2)
      = ∑ k, ∑ l, W k * W l * ‖∑ i, A i k * star (A i l)‖ ^ 2 := by
  set cc : ι → ι → κ → κ → ℂ := fun i j k l =>
    ((W k * W l : ℝ) : ℂ) * ((A i k * star (A i l)) * (star (A j k) * A j l)) with hc
  have hL : (((∑ i, ∑ j, ‖∑ k, ((W k : ℝ) : ℂ) * (A i k * star (A j k))‖ ^ 2 : ℝ)) : ℂ)
      = ∑ i, ∑ j, ∑ k, ∑ l, cc i j k l := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [norm_sq_eq_sum (fun k => A i k) (fun k => A j k) W]
  have hR : (((∑ k, ∑ l, W k * W l * ‖∑ i, A i k * star (A i l)‖ ^ 2 : ℝ)) : ℂ)
      = ∑ k, ∑ l, ∑ i, ∑ j, cc i j k l := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Complex.ofReal_mul]
    rw [norm_sq_eq_sum_one (fun i => A i k) (fun i => A i l)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hc]
    ring
  apply Complex.ofReal_inj.mp
  rw [hL, hR]
  exact four_sum_comm cc

/-- The domination corollary: for weights in `[0,1]` the weighted quantity is at most the
unweighted one. -/
theorem weightedFrobSwap_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℂ) (W : κ → ℝ) (h0 : ∀ k, 0 ≤ W k) (h1 : ∀ k, W k ≤ 1) :
    (∑ i, ∑ j, ‖∑ k, ((W k : ℝ) : ℂ) * (A i k * star (A j k))‖ ^ 2)
      ≤ ∑ i, ∑ j, ‖∑ k, A i k * star (A j k)‖ ^ 2 := by
  have h1' := weightedFrobSwap A (fun _ => (1 : ℝ))
  simp only [Complex.ofReal_one, one_mul] at h1'
  rw [weightedFrobSwap A W, h1']
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  have hkl : W k * W l ≤ 1 := by nlinarith [h0 k, h0 l, h1 k, h1 l]
  exact mul_le_of_le_one_left (by positivity) hkl

end Work.Peluse.Ulower
