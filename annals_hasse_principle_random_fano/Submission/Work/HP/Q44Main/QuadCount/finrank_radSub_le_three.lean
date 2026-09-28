import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs
import Submission.Work.HP.MDEstimates.polarQuadFacts
import Submission.Work.HP.MDEstimates.hyperplaneFactor
import Submission.Work.HP.MDEstimates.linFormEvalEq
import Submission.Work.HP.Q44Main.QuadCount.radSub_mem_iff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

open MvPolynomial

namespace Work.HP.Q44Main.QuadCount

open Work.HP.MDEstimates

/-!
# The radical of a quadratic form in five variables with no linear factor is at most 3-dimensional

Let `Q` be a homogeneous quadratic form in five variables over `ℚ` which has no linear factor, and
`Q ≠ 0`.  Then its polar radical `radSub Q = ker (polarLM Q)` has dimension at most `3`.

The proof follows the paper.  The key ingredient is that `radSub Q` is contained in the cone
`{Q = 0}`: the polar form is represented by `polarLM`, so `v ∈ ker (polarLM Q)` implies
`polQ Q v v = ⟨polarLM Q v, v⟩ = 0`, i.e. `Q v = 0`.  If the radical had dimension `4` it would be
a hyperplane on which `Q` vanishes identically, hence `Q` would be divisible by a linear form
(`hyperplaneFactor`), contradicting the hypothesis; and dimension `5` forces `Q = 0`.

The bridge between `polarLM` and `polQ` is the observation that the directional derivative
`∑ j, v j • ∂_j Q` has `i`-th coordinate `2 * (polarLM Q v) i` at the exponent `single i 1`.
Since this derivative is homogeneous of degree `1` (when `Q` is), its evaluation at `v` is the
sum of its coordinate coefficients times `v` (`linFormEvalEq`), and Euler's identity turns that
into `2 * Q v`. -/

/-! ## The key computation: `polarLM` versus the directional derivative -/

/-- For any `Q`, the `i`-th coordinate of `polarLM Q v` is half the coefficient, at the exponent
`single i 1`, of the directional derivative `∑ j, v j • ∂_j Q`. -/
theorem two_polarLM_eq_coeff_pderiv (Q : MvPolynomial (Fin 5) ℚ) (v : Fin 5 → ℚ) (i : Fin 5) :
    2 * (polarLM Q v) i
      = (∑ j : Fin 5, v j • MvPolynomial.pderiv j Q).coeff (Finsupp.single i 1) := by
  have hL : 2 * (polarLM Q v) i
      = (∑ j : Fin 5, Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) * v j)
        + Q.coeff (Finsupp.single i 1 + Finsupp.single i 1) * v i := by
    rw [show (polarLM Q v) i
        = ((∑ j : Fin 5, Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) * v j)
          + Q.coeff (Finsupp.single i 1 + Finsupp.single i 1) * v i) / 2 from rfl]
    ring
  have hterm : ∀ j : Fin 5, (v j • MvPolynomial.pderiv j Q).coeff (Finsupp.single i 1)
      = v j * Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)
          * ((((Finsupp.single i 1) j : ℕ)) : ℚ)
        + v j * Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) := by
    intro j
    rw [coeff_smul, coeff_pderiv, smul_eq_mul]
    ring
  have hif : ∀ j : Fin 5,
      v j * Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) * ((((Finsupp.single i 1) j : ℕ)) : ℚ)
        = (if i = j then v j * Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) else 0) := by
    intro j
    by_cases h : i = j
    · subst h; simp [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
      simp [h]
  have hCsum : ∑ j : Fin 5,
        v j * Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)
          * ((((Finsupp.single i 1) j : ℕ)) : ℚ)
      = v i * Q.coeff (Finsupp.single i 1 + Finsupp.single i 1) := by
    have h1 : ∑ j : Fin 5,
          v j * Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)
            * ((((Finsupp.single i 1) j : ℕ)) : ℚ)
        = ∑ j : Fin 5,
          (if i = j then v j * Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) else 0) :=
      Finset.sum_congr rfl (fun j _ => hif j)
    rw [h1, Finset.sum_ite_eq]
    simp
  have hDsum : ∑ j : Fin 5, v j * Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)
      = ∑ j : Fin 5, Q.coeff (Finsupp.single i 1 + Finsupp.single j 1) * v j :=
    Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [hL, coeff_sum]
  simp only [hterm]
  rw [Finset.sum_add_distrib, hCsum, hDsum]
  ring

/-! ## The evaluation identity -/

/-- For a homogeneous quadratic form `Q`, the evaluation `Q v` is the pairing of `polarLM Q v`
with `v`. -/
theorem eval_eq_sum_polarLM (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (v : Fin 5 → ℚ) :
    MvPolynomial.eval v Q = ∑ i : Fin 5, (polarLM Q v) i * v i := by
  have hhom : (∑ j : Fin 5, v j • MvPolynomial.pderiv j Q).IsHomogeneous 1 := by
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [MvPolynomial.mem_homogeneousSubmodule]
    simpa using hQ.pderiv (i := j)
  have hlin := linFormEvalEq hhom v
  have hC : MvPolynomial.eval v (∑ j : Fin 5, v j • MvPolynomial.pderiv j Q)
      = ∑ j : Fin 5, v j * MvPolynomial.eval v (MvPolynomial.pderiv j Q) := by
    rw [MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hEuler : ∑ j : Fin 5, v j * MvPolynomial.eval v (MvPolynomial.pderiv j Q)
      = 2 * MvPolynomial.eval v Q := by
    have h2 : MvPolynomial.eval v ((2 : ℕ) • Q) = 2 * MvPolynomial.eval v Q := by
      rw [two_nsmul, map_add]
      ring
    have h := congrArg (MvPolynomial.eval v) (hQ.sum_X_mul_pderiv (φ := Q))
    rw [MvPolynomial.eval_sum] at h
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X] at h
    rw [h2] at h
    exact h
  have hB : 2 * (∑ i : Fin 5, (polarLM Q v) i * v i)
      = ∑ i : Fin 5,
          (∑ j : Fin 5, v j • MvPolynomial.pderiv j Q).coeff (Finsupp.single i 1) * v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show 2 * ((polarLM Q v) i * v i) = (2 * (polarLM Q v) i) * v i from by ring,
      two_polarLM_eq_coeff_pderiv Q v i]
  have hchain : 2 * (∑ i : Fin 5, (polarLM Q v) i * v i) = 2 * MvPolynomial.eval v Q := by
    rw [hB, ← hlin, hC, hEuler]
  exact (mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) hchain).symm

/-! ## The radical lies in the cone -/

/-- Every rational point of the radical of `Q` is a rational point of the cone `V(Q)`. -/
theorem eval_zero_of_mem_radSub (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    {v : Fin 5 → ℚ} (hv : v ∈ radSub Q) : MvPolynomial.eval v Q = 0 := by
  have hv' : polarLM Q v = 0 := LinearMap.mem_ker.mp hv
  rw [eval_eq_sum_polarLM Q hQ v, hv']
  simp

/-! ## The main theorem -/

theorem finrank_radSub_le_three (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hnolf : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ Q → False) :
    Module.finrank ℚ (Work.HP.MDEstimates.radSub Q) ≤ 3 := by
  by_contra hcon
  rw [not_le] at hcon
  have h5 : Module.finrank ℚ (Work.HP.MDEstimates.radSub Q) ≤ 5 := by
    have h := Submodule.finrank_le (Work.HP.MDEstimates.radSub Q)
    rwa [Module.finrank_fin_fun ℚ] at h
  rcases (by omega : Module.finrank ℚ (Work.HP.MDEstimates.radSub Q) = 4 ∨
      Module.finrank ℚ (Work.HP.MDEstimates.radSub Q) = 5) with h4 | h5'
  · obtain ⟨ℓ, hhom, hdvd⟩ :=
      hyperplaneFactor Q hQ (Work.HP.MDEstimates.radSub Q) h4
        (fun v hv => eval_zero_of_mem_radSub Q hQ hv)
    exact hnolf ℓ hhom hdvd
  · have htop : Work.HP.MDEstimates.radSub Q = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h5']; simp)
    refine hQ0 (MvPolynomial.funext fun v => ?_)
    have hv : v ∈ Work.HP.MDEstimates.radSub Q := by rw [htop]; trivial
    rw [eval_zero_of_mem_radSub Q hQ hv]
    simp

end Work.HP.Q44Main.QuadCount
