/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.CensusFibre.SecPolarDefs
import Submission.Work.MotK.KleinI5
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The second polar of the secant quintic lies in the ideal of the Klein curve

`kleinSecP2 a b c u` (defined in `SecPolarDefs`) is the coefficient of `t ^ 2` in
`s (c + t • u)`, where `s = kleinSec` is the secant quintic of the Klein–Fisher curve
`C = V(p_0, …, p_4) ⊂ ℙ⁴`.

The main result here is `sec_p2_mem`: evaluated at the *coordinates* `c = X` of `ℙ⁴`
and any `u`, the second polar `kleinSecP2` lies in the ideal
`(p_0, …, p_4) ⊂ K[X_0, …, X_4]` of the Klein curve.  This is identity **I5** of
`KleinI5`/`SecPolar` in its polar form: the secant hypersurface `Sec C` has multiplicity
`≥ 3` along `C`, so all its second partials — and hence its second polar in any direction —
vanish on `C`.

The proof has two steps, both pure polynomial algebra with integer coefficients (so they
hold over every commutative ring, in particular over `K` of any characteristic):

* `kleinSecP2_eq` — the second polar is the divided-second-derivative quadratic form
  `kleinSecP2 a b c u = ∑_i kleinSecD_i · u_i² + ∑_{i<j} kleinSecDD_{ij} · u_i u_j`
  (`kleinSecD_i = ∂_i ∂_i s / 2` and `kleinSecDD_{ij} = ∂_i ∂_j s` for `i ≠ j`);
* each of the fifteen coefficients lies in the ideal, by the explicit certificates
  `kleinSecD_i_eq` (`SecPolarDefs`) and `kleinSecDD_{ij}_eq` (`KleinI5`) which exhibit them
  as `∑_k g_k · p_k`.  The ideal is closed under multiplication, so every summand of the
  quadratic form does too.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK.CensusFibre

open Work.MotK

/-! ## The ideal of the Klein curve -/

/-- The ideal of the Klein curve `C = V(p_0, …, p_4)` in `ℙ⁴` (coordinates `X 0, …, X 4`). -/
noncomputable def kleinIdeal (K : Type*) [Field K] (a b : K) : Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.span (Set.range (fun k => kleinP (MvPolynomial.C a) (MvPolynomial.C b)
    (fun i => MvPolynomial.X i) k))

section Helpers

variable (K : Type*) [Field K]

/-- A multiple of the `k`-th Pfaffian lies in the ideal of the Klein curve. -/
theorem mul_kleinP_mem (a b : K) (k : Fin 5) (g : MvPolynomial (Fin 5) K) :
    g * kleinP (MvPolynomial.C a) (MvPolynomial.C b) (fun i => MvPolynomial.X i) k
      ∈ kleinIdeal K a b :=
  Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

/-! ## The second polar as a divided-derivative quadratic form -/

/-- The second polar `kleinSecP2` is the quadratic form of the divided second derivatives
`kleinSecD_i = ∂_i ∂_i s / 2` (diagonal) and `kleinSecDD_{ij} = ∂_i ∂_j s` (`i ≠ j`). -/
theorem kleinSecP2_eq {R : Type*} [CommRing R] (a b : R) (c u : Fin 5 → R) :
    kleinSecP2 a b c u
      = kleinSecD0 a b c * (u 0) ^ 2
        + kleinSecD1 a b c * (u 1) ^ 2
        + kleinSecD2 a b c * (u 2) ^ 2
        + kleinSecD3 a b c * (u 3) ^ 2
        + kleinSecD4 a b c * (u 4) ^ 2
        + kleinSecDD_01 a b c * u 0 * u 1
        + kleinSecDD_02 a b c * u 0 * u 2
        + kleinSecDD_03 a b c * u 0 * u 3
        + kleinSecDD_04 a b c * u 0 * u 4
        + kleinSecDD_12 a b c * u 1 * u 2
        + kleinSecDD_13 a b c * u 1 * u 3
        + kleinSecDD_14 a b c * u 1 * u 4
        + kleinSecDD_23 a b c * u 2 * u 3
        + kleinSecDD_24 a b c * u 2 * u 4
        + kleinSecDD_34 a b c * u 3 * u 4 := by
  simp only [kleinSecP2, kleinSecD0, kleinSecD1, kleinSecD2, kleinSecD3, kleinSecD4,
    kleinSecDD_01, kleinSecDD_02, kleinSecDD_03, kleinSecDD_04,
    kleinSecDD_12, kleinSecDD_13, kleinSecDD_14,
    kleinSecDD_23, kleinSecDD_24, kleinSecDD_34]
  refl_ring1

/-! ## The divided second partials of `s` lie in the ideal

Each certificate `kleinSecD_i_eq` / `kleinSecDD_{ij}_eq` is a five-term sum
`∑_k c_k · kleinP_k` with coefficients in `K[X]`; rewriting and splitting the sum leaves
only multiples of the Pfaffians, which are in the ideal by `mul_kleinP_mem`. -/

/-- `∂_0 ∂_0 s / 2` lies in the ideal of the Klein curve. -/
theorem kleinSecD0_mem (a b : K) :
    kleinSecD0 (MvPolynomial.C a) (MvPolynomial.C b) (fun j => MvPolynomial.X j)
      ∈ kleinIdeal K a b := by
  rw [kleinSecD0_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_1 ∂_1 s / 2` lies in the ideal of the Klein curve. -/
theorem kleinSecD1_mem (a b : K) :
    kleinSecD1 (MvPolynomial.C a) (MvPolynomial.C b) (fun j => MvPolynomial.X j)
      ∈ kleinIdeal K a b := by
  rw [kleinSecD1_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_2 ∂_2 s / 2` lies in the ideal of the Klein curve. -/
theorem kleinSecD2_mem (a b : K) :
    kleinSecD2 (MvPolynomial.C a) (MvPolynomial.C b) (fun j => MvPolynomial.X j)
      ∈ kleinIdeal K a b := by
  rw [kleinSecD2_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_3 ∂_3 s / 2` lies in the ideal of the Klein curve. -/
theorem kleinSecD3_mem (a b : K) :
    kleinSecD3 (MvPolynomial.C a) (MvPolynomial.C b) (fun j => MvPolynomial.X j)
      ∈ kleinIdeal K a b := by
  rw [kleinSecD3_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_4 ∂_4 s / 2` lies in the ideal of the Klein curve. -/
theorem kleinSecD4_mem (a b : K) :
    kleinSecD4 (MvPolynomial.C a) (MvPolynomial.C b) (fun j => MvPolynomial.X j)
      ∈ kleinIdeal K a b := by
  rw [kleinSecD4_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_0 ∂_1 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_01_mem (a b : K) :
    kleinSecDD_01 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_01_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_0 ∂_2 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_02_mem (a b : K) :
    kleinSecDD_02 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_02_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_0 ∂_3 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_03_mem (a b : K) :
    kleinSecDD_03 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_03_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_0 ∂_4 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_04_mem (a b : K) :
    kleinSecDD_04 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_04_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_1 ∂_2 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_12_mem (a b : K) :
    kleinSecDD_12 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_12_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_1 ∂_3 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_13_mem (a b : K) :
    kleinSecDD_13 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_13_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_1 ∂_4 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_14_mem (a b : K) :
    kleinSecDD_14 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_14_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_2 ∂_3 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_23_mem (a b : K) :
    kleinSecDD_23 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_23_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_2 ∂_4 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_24_mem (a b : K) :
    kleinSecDD_24 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_24_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

/-- `∂_3 ∂_4 s` lies in the ideal of the Klein curve. -/
theorem kleinSecDD_34_mem (a b : K) :
    kleinSecDD_34 (MvPolynomial.C a) (MvPolynomial.C b) (fun k => MvPolynomial.X k)
      ∈ kleinIdeal K a b := by
  rw [kleinSecDD_34_eq]
  simp only [← kleinP_zero, ← kleinP_one, ← kleinP_two, ← kleinP_three, ← kleinP_four]
  repeat' apply Ideal.add_mem
  all_goals exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

end Helpers

/-! ## The target: the second polar lies in the ideal of the Klein curve -/

/-- **The second polar of the secant quintic lies in the ideal of the Klein curve.**
This is identity I5 in polar form: the secant hypersurface has multiplicity `≥ 3` along `C`,
so its second polar in any direction `u` vanishes on `C`. -/
theorem sec_p2_mem (K : Type*) [Field K] (a b : K) (u : Fin 5 → MvPolynomial (Fin 5) K) :
    Work.MotK.kleinSecP2 (MvPolynomial.C a) (MvPolynomial.C b) (fun i => MvPolynomial.X i) u
      ∈ Ideal.span (Set.range (fun k => Work.MotK.kleinP (MvPolynomial.C a) (MvPolynomial.C b)
          (fun i => MvPolynomial.X i) k)) := by
  show Work.MotK.kleinSecP2 (MvPolynomial.C a) (MvPolynomial.C b) (fun i => MvPolynomial.X i) u
      ∈ kleinIdeal K a b
  rw [kleinSecP2_eq]
  repeat' apply Ideal.add_mem
  · exact Ideal.mul_mem_right _ _ (kleinSecD0_mem K a b)
  · exact Ideal.mul_mem_right _ _ (kleinSecD1_mem K a b)
  · exact Ideal.mul_mem_right _ _ (kleinSecD2_mem K a b)
  · exact Ideal.mul_mem_right _ _ (kleinSecD3_mem K a b)
  · exact Ideal.mul_mem_right _ _ (kleinSecD4_mem K a b)
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_01_mem K a b))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_02_mem K a b))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_03_mem K a b))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_04_mem K a b))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_12_mem K a b))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_13_mem K a b))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_14_mem K a b))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_23_mem K a b))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_24_mem K a b))
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (kleinSecDD_34_mem K a b))

end Work.MotK.CensusFibre
