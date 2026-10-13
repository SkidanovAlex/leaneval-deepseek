import Mathlib
import Submission.Work.WilE8.Hyp.Basic

namespace Work.WilE8.Hyp

open WilkiesDesign WilkiesDesign.E

theorem hyperPF_supset {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) :
    WilkiesDesign.E.psiV '' {x : Fin n → ℝ | MvPolynomial.eval x Q = 0} ⊆
      WilkiesDesign.E.projFirst n n '' (Work.WilE8.Hyp.hyperPF Q).set := by
  rintro u ⟨x, hx, rfl⟩
  -- `y` is `psiV x` and `w i = sqrt (1 - (psiV x i)^2)`, so that `(y, w)` lies on the
  -- sphere `u^2 + w^2 = 1` and `y / w = x` recovers the original point.
  set y : Fin n → ℝ := fun i => E.psi (x i) with hy
  set w : Fin n → ℝ := fun i => Real.sqrt (1 - E.psi (x i) ^ 2) with hw
  have hwpos : ∀ i, 0 < w i := by
    intro i
    rw [hw]
    show 0 < Real.sqrt (1 - E.psi (x i) ^ 2)
    rw [show (1 : ℝ) - E.psi (x i) ^ 2 = 1 / (1 + (x i) ^ 2) from
      Work.WilE10.one_sub_psi_sq (x i)]
    positivity
  have hwsq : ∀ i, w i ^ 2 = 1 - E.psi (x i) ^ 2 := by
    intro i
    rw [hw]
    show Real.sqrt (1 - E.psi (x i) ^ 2) ^ 2 = 1 - E.psi (x i) ^ 2
    exact Real.sq_sqrt (by rw [Work.WilE10.one_sub_psi_sq (x i)]; positivity)
  refine ⟨Fin.append y w, ?_, ?_⟩
  · -- Membership in the semi-Pfaffian set describing the hyperplane.
    rw [mem_hyperPF_set]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- the `2n`-tuple lies in the closed cube
      intro k
      rcases hk : finSumFinEquiv.symm k with i | i
      · have hk' : k = Fin.castAdd n i := by
          rw [← finSumFinEquiv.apply_symm_apply k, hk, finSumFinEquiv_apply_left]
        rw [hk', Fin.append_left, hy]
        exact Work.WilE10.psi_abs_le_one (x i)
      · have hk' : k = Fin.natAdd n i := by
          rw [← finSumFinEquiv.apply_symm_apply k, hk, finSumFinEquiv_apply_right]
        rw [hk', Fin.append_right]
        have hle : w i ≤ 1 := by
          nlinarith [hwsq i, hwpos i, sq_nonneg (E.psi (x i))]
        rw [abs_of_nonneg (le_of_lt (hwpos i))]
        exact hle
    · -- the sphere equations `u_i^2 + w_i^2 = 1`
      intro i
      rw [Fin.append_left, Fin.append_right, hy, hwsq i]
      ring
    · -- the cleared-denominator equation
      have hfun : (fun v : Fin n ⊕ Fin n => Fin.append y w (finSumFinEquiv v))
          = Sum.elim y w := by
        funext v; rcases v with i | i
        · rw [finSumFinEquiv_apply_left, Fin.append_left]; rfl
        · rw [finSumFinEquiv_apply_right, Fin.append_right]; rfl
      have hfun2 : (fun i => y i / w i) = x := by
        funext i; rw [hy, hw]; exact Work.WilE10.psiR_psi (x i)
      have hcd := Work.WilE8.Clear.clearDenom_eval Q y w (fun i => ne_of_gt (hwpos i))
      rw [hfun]
      rw [← hcd, hfun2, hx, mul_zero]
    · -- the sign conditions `w_i > 0`
      intro i
      rw [Fin.append_right]
      exact hwpos i
  · -- the first `n` coordinates are `psiV x`
    funext i
    show Fin.append y w (Fin.castAdd n i) = E.psi (x i)
    rw [Fin.append_left, hy]

end Work.WilE8.Hyp
