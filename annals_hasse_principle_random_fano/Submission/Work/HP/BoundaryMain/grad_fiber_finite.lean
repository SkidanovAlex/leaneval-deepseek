import Mathlib
import Submission.Work.HP.BoundaryMain.bm_defs
import Submission.Work.HP.GradDecomp.gradF_decomp
import Submission.Work.HP.GradCount.ncard_spec_le
import Submission.Work.HP.BoundaryMain.grad_bound_def
import Submission.Work.HP.BoundaryMain.gradF_toR_decomp
import Submission.Work.HP.BoundaryMain.coeff_bound_of_grad

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.HP.BoundaryMain

open Work.HP

/-- Coordinate bound for the Euclidean norm of a real vector. -/
private lemma abs_apply_le_rNorm' {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) :
    |v i| ≤ rNorm v := by
  have h : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  calc |v i| = Real.sqrt ((v i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (v j) ^ 2) := Real.sqrt_le_sqrt h
    _ = rNorm v := rfl

/-- **Finiteness of the fibre of `a ↦ (a ∘ smon j, zeroSInt j a)`.**
Given a point `y` with `y j ≠ 0`, a bound `C` and a fixed "free part" `f`, only finitely many
`(n+1)`-tuples `c i = a (smon d n hd1 j i)` of coefficients of the special monomials
`x_j^{d-1}x_i` can occur as `a` ranges over the integer coefficient vectors with
`zeroSInt d n hd1 j a = f` and `‖∇f_a(y)‖ ≤ C`.

Indeed, `gradF_decomp` expresses `∂_k f_a(y)` (`k ≠ j`) as `∂_k f_f(y) + c_k y_j^{d-1}` and
`∂_j f_a(y)` as `∂_j f_f(y) + y_j^{d-2}(d c_j y_j + (d-1) ∑_{i≠j} c_i y_i)`, so each `c_i` is
confined to an interval of length `O(1)` (the coefficient of `c_j` in the second relation is
`d y_j^{d-1} ≠ 0`).  With `K = ⌊gradBound d n C y j (∇f_f(y))⌋` this gives
`c ∈ ∏ i, Icc (-K) K`, a finite product of finite sets. -/
theorem grad_fiber_finite (d n : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 ≤ d) (C : ℝ)
    (y : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (hyj : y j ≠ 0) (f : Work.HP.Mon d n → ℤ) :
    ({c : Fin (n + 1) → ℤ | ∃ a : Work.HP.Mon d n → ℤ,
        Work.HP.rNorm (Work.HP.gradVec d n (Work.HP.toR a) y) ≤ C ∧
        (fun i => a (Work.HP.smon d n hd1 j i)) = c ∧
        Work.HP.BoundaryMain.zeroSInt d n hd1 j a = f} : Set (Fin (n + 1) → ℤ)).Finite := by
  classical
  -- each coordinate of the gradient is bounded by `C`
  have hineq : ∀ a : Mon d n → ℤ, rNorm (gradVec d n (toR a) y) ≤ C →
      ∀ k : Fin (n + 1), |gradF d n (toR a) y k| ≤ C := by
    intro a hgrad k
    have h1 : |gradVec d n (toR a) y k| ≤ rNorm (gradVec d n (toR a) y) :=
      abs_apply_le_rNorm' _ k
    have h2 : |gradF d n (toR a) y k| ≤ rNorm (gradVec d n (toR a) y) := by
      simpa only [gradVec] using h1
    exact le_trans h2 hgrad
  -- the coefficients of the special monomials of any witness are bounded by `gradBound`
  have hbw : ∀ a : Mon d n → ℤ, rNorm (gradVec d n (toR a) y) ≤ C →
      zeroSInt d n hd1 j a = f →
      ∀ i : Fin (n + 1),
        |(a (smon d n hd1 j i) : ℝ)| ≤ gradBound d n C y j (fun k => gradF d n (toR f) y k) := by
    intro a hgrad hf
    refine coeff_bound_of_grad d n hd2 C y j hyj (fun k => gradF d n (toR f) y k)
      (fun i => a (smon d n hd1 j i)) ?_ ?_
    · intro k hkj
      show |gradF d n (toR f) y k + (a (smon d n hd1 j k) : ℝ) * y j ^ (d - 1)| ≤ C
      have hA : gradF d n (toR a) y k
          = gradF d n (toR f) y k + (a (smon d n hd1 j k) : ℝ) * y j ^ (d - 1) := by
        have h := gradF_toR_decomp d n hd1 hd2 a y j k f hf
        rwa [if_neg hkj] at h
      rw [← hA]
      exact hineq a hgrad k
    · show |gradF d n (toR f) y j + y j ^ (d - 2) * ((d : ℝ) * (a (smon d n hd1 j j) : ℝ) * y j
        + ((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, (a (smon d n hd1 j i) : ℝ) * y i)| ≤ C
      have hA : gradF d n (toR a) y j = gradF d n (toR f) y j
          + y j ^ (d - 2) * ((d : ℝ) * (a (smon d n hd1 j j) : ℝ) * y j
            + ((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, (a (smon d n hd1 j i) : ℝ) * y i) := by
        have h := gradF_toR_decomp d n hd1 hd2 a y j j f hf
        rwa [if_pos rfl] at h
      rw [← hA]
      exact hineq a hgrad j
  -- the fibre is contained in the box `∏ i, Icc (-K) K`
  set K : ℤ := ⌊gradBound d n C y j (fun k => gradF d n (toR f) y k)⌋ with hK
  have hbox : (Set.pi Set.univ (fun _ : Fin (n + 1) => Set.Icc (-K) K)).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  refine hbox.subset ?_
  rintro c ⟨a, hgrad, ha, hf⟩
  have hb := hbw a hgrad hf
  rw [Set.mem_pi]
  intro i _
  rw [Set.mem_Icc]
  have hci : c i = a (smon d n hd1 j i) := (congrFun ha i).symm
  rw [hci]
  have h := hb i
  have h4 : a (smon d n hd1 j i) ≤ K := by
    rw [hK]
    exact Int.le_floor.mpr (abs_le.mp h).2
  have h3 : -(a (smon d n hd1 j i)) ≤ K := by
    rw [hK]
    apply Int.le_floor.mpr
    simpa using neg_le_neg ((abs_le.mp h).1)
  exact ⟨by omega, h4⟩

end Work.HP.BoundaryMain
