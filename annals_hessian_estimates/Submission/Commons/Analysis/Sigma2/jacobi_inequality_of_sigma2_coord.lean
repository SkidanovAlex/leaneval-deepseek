import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.first_deriv_sigma2_coord
import Submission.Commons.Analysis.Calculus.FDeriv.second_deriv_sigma2_coord
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_three_swap
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_comp_perm_of_contDiffOn
import Submission.Commons.Analysis.Sigma2.diagonal_first_deriv_sigma2
import Submission.Commons.Analysis.Sigma2.diagonal_second_deriv_sigma2
import Submission.Commons.Analysis.Sigma2.jacobi_inequality_pointwise

open Commons.Analysis.Calculus.FDeriv

namespace Commons.Analysis.Sigma2

/- Almost-Jacobi inequality (Prop. 2.1, n = 4) at a point where the Hessian is diagonal, in
coordinate form: `S * (Delta_F b - eps |grad_F b|^2) >= 0` written out as
`sum_i f_i d_i - (delta/S) sum_i f_i (Delta u_i)^2 >= 0`, with `d_i := sum_k u_iikk` and
`Delta u_i := sum_j u_jji`.  The hypotheses `hmono`, `hσ2`, `hσ1` are the ordering, `sigma_2 = 1`
and positivity for the eigenvalue tuple `lam` (the diagonal entries of `D^2u(x)`).
Proof: instantiate `diagonal_first_deriv_sigma2` with the raw first-order identity
`first_deriv_sigma2_coord` to get `sum_j f_j b_jji = 0` (using the index symmetry
`iteratedFDeriv_three_swap`), instantiate `diagonal_second_deriv_sigma2` with the raw second-order
identity `second_deriv_sigma2_coord` (slice `k`) and sum over `k` to get the `d_i` identity
(using `iteratedFDeriv_comp_perm_of_contDiffOn` to identify `u_kkii` with `u_iikk`), then apply
`jacobi_inequality_pointwise`. -/
open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem jacobi_inequality_of_sigma2_coord {v : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4))}
    {u : EuclideanSpace ℝ (Fin 4) → ℝ} {s : Set (EuclideanSpace ℝ (Fin 4))}
    {x : EuclideanSpace ℝ (Fin 4)}
    (hs : IsOpen s) (hu : ContDiffOn ℝ 4 u s) (hx : x ∈ s)
    (hconst : ∀ y ∈ s, (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j] -
          ((iteratedFDeriv ℝ 2 u y) ![v i, v j]) ^ 2 else 0) = 1)
    (lam : Fin 4 → ℝ)
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) :
    let S : ℝ := ∑ t : Fin 4, lam t
    let eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S)
    let δ : ℝ := 1 + eps
    0 ≤ (∑ i : Fin 4, (S - lam i) * (∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]))
        - (δ / S) * (∑ i : Fin 4, (S - lam i) *
            (∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) ^ 2) := by
  dsimp only
  have hu3 : ContDiffOn ℝ 3 u s := hu.of_le (by norm_num)
  -- First-order symmetries of the third derivatives (`b_{abc} = b_{bac} = b_{acb}`).
  have h3a : ∀ a b c : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v a, v b, v c]
      = (iteratedFDeriv ℝ 3 u x) ![v b, v a, v c] := fun a b c =>
    (iteratedFDeriv_three_swap hs hx hu3 (v a) (v b) (v c)).1
  have h3b : ∀ a b c : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v a, v b, v c]
      = (iteratedFDeriv ℝ 3 u x) ![v a, v c, v b] := fun a b c =>
    (iteratedFDeriv_three_swap hs hx hu3 (v a) (v b) (v c)).2
  -- First-order identity: `sum_i f_i b_{kii} = 0` for every `k`.
  have hD1 : ∀ k : Fin 4, (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
      * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) = 0 := fun k =>
    diagonal_first_deriv_sigma2 lam
      (fun i j => (iteratedFDeriv ℝ 2 u x) ![v i, v j])
      (fun k i j => (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j])
      k hdiag (first_deriv_sigma2_coord (u := u) (v := v) hs hu3 hx hconst k)
  -- The first differentiated equation in the form needed by `jacobi_inequality_pointwise`:
  -- `sum_j f_j b_{jji} = 0` for every `i`.
  have h1 : ∀ i : Fin 4, (∑ j : Fin 4, ((∑ t : Fin 4, lam t) - lam j)
      * (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) = 0 := by
    intro i
    rw [show (∑ j : Fin 4, ((∑ t : Fin 4, lam t) - lam j)
          * (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i])
        = (∑ j : Fin 4, ((∑ t : Fin 4, lam t) - lam j)
          * (iteratedFDeriv ℝ 3 u x) ![v i, v j, v j]) from
      Finset.sum_congr rfl (fun j _ => by rw [h3b j j i, h3a j i j])]
    exact hD1 i
  -- Second-order identity, slice by slice: `sum_i f_i c_{kkii} = sum_{ij} b_{kij}^2 - (sum_i b_{kii})^2`.
  have hD2k : ∀ k : Fin 4,
      (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * (iteratedFDeriv ℝ 4 u x) ![v k, v k, v i, v i])
        = (∑ i : Fin 4, ∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j] ^ 2)
          - (∑ i : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) ^ 2 := fun k =>
    diagonal_second_deriv_sigma2 lam
      (fun i j => (iteratedFDeriv ℝ 2 u x) ![v i, v j])
      (fun i j => (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j])
      (fun i j => (iteratedFDeriv ℝ 4 u x) ![v k, v k, v i, v j])
      hdiag (fun i j => h3b k i j)
      (second_deriv_sigma2_coord (u := u) (v := v) hs hu hx hconst k k)
  -- Fourth-order symmetry: `c_{aabb} = c_{bbaa}` (permutation `(0 2)(1 3)` of the arguments).
  have h4perm : ∀ a b : Fin 4,
      (iteratedFDeriv ℝ 4 u x) ![v a, v a, v b, v b]
        = (iteratedFDeriv ℝ 4 u x) ![v b, v b, v a, v a] := by
    intro a b
    have h := iteratedFDeriv_comp_perm_of_contDiffOn (f := u) hs hx (n := 4) hu
      (m := ![v b, v b, v a, v a]) (σ := Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
    have hm : (![v b, v b, v a, v a] : Fin 4 → EuclideanSpace ℝ (Fin 4))
        ∘ (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) = ![v a, v a, v b, v b] := by
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    rw [hm] at h
    exact h
  -- Second differentiated equation in the form needed by `jacobi_inequality_pointwise`.
  have h2 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
        * (∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]))
      = (∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j] ^ 2)
        - (∑ k : Fin 4, (∑ i : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) ^ 2) := by
    have hsum : (∑ k : Fin 4, ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * (iteratedFDeriv ℝ 4 u x) ![v k, v k, v i, v i])
        = (∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
              (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j] ^ 2)
          - (∑ k : Fin 4, (∑ i : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) ^ 2) := by
      have hstep : (∑ k : Fin 4, ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
            * (iteratedFDeriv ℝ 4 u x) ![v k, v k, v i, v i])
          = ∑ k : Fin 4, ((∑ i : Fin 4, ∑ j : Fin 4,
                (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j] ^ 2)
              - (∑ i : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) ^ 2) :=
        Finset.sum_congr rfl (fun k _ => hD2k k)
      rw [Finset.sum_sub_distrib] at hstep
      exact hstep
    have hL : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * (∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]))
        = (∑ k : Fin 4, ∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i)
          * (iteratedFDeriv ℝ 4 u x) ![v k, v k, v i, v i]) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [h4perm k i]
    rw [hL]
    exact hsum
  have hmain := jacobi_inequality_pointwise lam hmono hσ2 hσ1
    (fun k i j => (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j])
    (fun i => ∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k])
    (fun k i j => h3b k i j) (fun k i j => h3a k i j) h1 h2
  dsimp only at hmain
  exact hmain

end Commons.Analysis.Sigma2
