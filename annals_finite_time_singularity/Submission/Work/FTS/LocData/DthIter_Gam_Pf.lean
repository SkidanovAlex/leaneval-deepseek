/-
# `D_θ^i Γ(θ) = Γ(θ)·Pf i (cos 2θ) α` on `Iθ`, for `i ≤ 4`

`Γ(θ) = (sin θ·cos²θ)^{α/3}` (`Work.Spaces.Gam`) and `D_θ = sin(2θ)∂_θ`.  This module proves the
exact angular jet formula

  `DthIter i (fun _ θ' => Gam α θ') z θ = Gam α θ * Pf i (cos (2θ)) α`   (`i ≤ 4`, `θ ∈ [0,π/2]`),

for **every real `α`** (no positivity hypothesis), where `Pf` is the explicit angular polynomial of
`Submission/Work/FTS/LocData/HkFstarDefs.lean`.

The proof is the natural one.  Because the function is `z`-independent, `DthIter` acts through the
one-variable operator `dthU φ = sin(2·)·φ'` (`DthIter_rad_eq`).  On the *open* interval, where
`sin θ·cos²θ > 0`,

  `sin(2θ)·Γ' = α·(cos 2θ - 1/3)·Γ`   (`Gam_sin_deriv`, for arbitrary `α`),

and `d/dθ [Pf i (cos 2θ) α] = -(2 sin 2θ)·(α·dQf i (cos 2θ) α)` (`Pf_cos_deriv'`, from the formal
derivative `dQf` of the angular polynomial `Qf`).  Multiplying by `sin(2θ)` and using the recursion
`Qf (i+1) = -2(1-u²)·dQf i + α·Qf 1·Qf i` (with `sin²(2θ) = 1 - cos²(2θ)`) gives the induction
step.  At the two endpoints `θ = 0, π/2` one has `sin(2θ) = 0`, so the left-hand side vanishes for
`i ≥ 1`, while the right-hand side vanishes because `Γ(0) = Γ(π/2) = 0` for `α ≠ 0` and because
`Pf i u 0 = 0` for `i ≠ 0` when `α = 0`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData.HkFstarDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-! ## Derivative of the angular polynomials `Qf i` -/

private lemma hd_one_sub_sq (u : ℝ) : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * u) u := by
  have h := (hasDerivAt_const (x := u) (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_one_sub_three_sq (u : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - 3 * y ^ 2) (-6 * u) u := by
  have h := (hasDerivAt_const (x := u) (1 : ℝ)).sub (((hasDerivAt_id u).pow 2).const_mul 3)
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_id_sub_third (u : ℝ) : HasDerivAt (fun y : ℝ => y - 1 / 3) 1 u := by
  have h := (hasDerivAt_id u).sub_const (1 / 3)
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_three_mul_sub_one (u : ℝ) : HasDerivAt (fun y : ℝ => 3 * y - 1) 3 u := by
  have h := ((hasDerivAt_id u).const_mul 3).sub_const 1
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_Qf_zero (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 0 v α) (dQf 0 u α) u := by
  simp only [Qf_zero, dQf_zero]
  exact hasDerivAt_const (x := u) (1 : ℝ)

private lemma hd_Qf_one (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 1 v α) (dQf 1 u α) u := by
  simp only [Qf_one, dQf_one]
  have h := (hd_three_mul_sub_one u).div_const 3
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_Qf_two (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 2 v α) (dQf 2 u α) u := by
  simp only [Qf_two, dQf_two]
  have hfun : (fun u : ℝ => -2 * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9)
      = (fun u : ℝ => -2 * (1 - u ^ 2)) + (fun u : ℝ => (α / 9) * (3 * u - 1) ^ 2) := by
    funext y; simp only [Pi.add_apply]; ring
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => -2 * (1 - u ^ 2)) (4 * u) u := by
    have h := ((hasDerivAt_const (x := u) (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).const_mul (-2)
    convert h using 1 <;> (try (funext y)) <;> simp <;> ring
  have h2 : HasDerivAt (fun u : ℝ => (α / 9) * (3 * u - 1) ^ 2) (2 * α * (u - 1 / 3)) u := by
    have h := ((((hasDerivAt_id u).const_mul 3).sub_const 1).pow 2).const_mul (α / 9)
    convert h using 1 <;> (try (funext y)) <;> simp <;> ring
  exact (h1.add h2).congr_deriv (by ring)

set_option maxHeartbeats 2000000 in
private lemma hd_Qf_three (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 3 v α) (dQf 3 u α) u := by
  simp only [Qf_three, dQf_three]
  have hfun : (fun u : ℝ => -8 * u * (1 - u ^ 2) - 6 * α * (u - 1 / 3) * (1 - u ^ 2)
        + α ^ 2 * (u - 1 / 3) ^ 3)
      = (fun u : ℝ => -8 * (u * (1 - u ^ 2)))
        + (fun u : ℝ => (-6 * α) * ((u - 1 / 3) * (1 - u ^ 2)))
        + (fun u : ℝ => α ^ 2 * (u - 1 / 3) ^ 3) := by
    funext y; simp only [Pi.add_apply]; ring
  rw [hfun]
  have hA : HasDerivAt (fun u : ℝ => -8 * (u * (1 - u ^ 2)))
      (-8 * (1 * (1 - u ^ 2) + u * (-2 * u))) u :=
    ((hasDerivAt_id u).mul (hd_one_sub_sq u)).const_mul (-8)
  have hB : HasDerivAt (fun u : ℝ => (-6 * α) * ((u - 1 / 3) * (1 - u ^ 2)))
      ((-6 * α) * (1 * (1 - u ^ 2) + (u - 1 / 3) * (-2 * u))) u :=
    ((hd_id_sub_third u).mul (hd_one_sub_sq u)).const_mul (-6 * α)
  have hC : HasDerivAt (fun u : ℝ => α ^ 2 * (u - 1 / 3) ^ 3)
      (α ^ 2 * (3 * (u - 1 / 3) ^ (3 - 1) * 1)) u :=
    ((hd_id_sub_third u).pow 3).const_mul (α ^ 2)
  exact ((hA.add hB).add hC).congr_deriv (by simp; ring)

set_option maxHeartbeats 4000000 in
private lemma hd_Qf_four (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 4 v α) (dQf 4 u α) u := by
  simp only [Qf_four, dQf_four]
  have hfun : (fun u : ℝ =>
        16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * α * (1 - u ^ 2) ^ 2
          - 32 * α * u * (u - 1 / 3) * (1 - u ^ 2)
          - 12 * α ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2) + α ^ 3 * (u - 1 / 3) ^ 4)
      = (fun u : ℝ => 16 * ((1 - u ^ 2) * (1 - 3 * u ^ 2)))
        + (fun u : ℝ => (12 * α) * ((1 - u ^ 2) * (1 - u ^ 2)))
        + (fun u : ℝ => (-(32 * α)) * ((u * (u - 1 / 3)) * (1 - u ^ 2)))
        + (fun u : ℝ => (-(12 * α ^ 2)) * (((u - 1 / 3) * (u - 1 / 3)) * (1 - u ^ 2)))
        + (fun u : ℝ => α ^ 3 * (u - 1 / 3) ^ 4) := by
    funext y; simp only [Pi.add_apply]; ring
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => 16 * ((1 - u ^ 2) * (1 - 3 * u ^ 2)))
      (16 * ((-2 * u) * (1 - 3 * u ^ 2) + (1 - u ^ 2) * (-6 * u))) u :=
    ((hd_one_sub_sq u).mul (hd_one_sub_three_sq u)).const_mul 16
  have h2 : HasDerivAt (fun u : ℝ => (12 * α) * ((1 - u ^ 2) * (1 - u ^ 2)))
      ((12 * α) * ((-2 * u) * (1 - u ^ 2) + (1 - u ^ 2) * (-2 * u))) u :=
    ((hd_one_sub_sq u).mul (hd_one_sub_sq u)).const_mul (12 * α)
  have h3 : HasDerivAt (fun u : ℝ => (-(32 * α)) * ((u * (u - 1 / 3)) * (1 - u ^ 2)))
      ((-(32 * α)) * ((1 * (u - 1 / 3) + u * 1) * (1 - u ^ 2) + (u * (u - 1 / 3)) * (-2 * u))) u :=
    (((hasDerivAt_id u).mul (hd_id_sub_third u)).mul (hd_one_sub_sq u)).const_mul (-(32 * α))
  have h4 : HasDerivAt (fun u : ℝ => (-(12 * α ^ 2)) * (((u - 1 / 3) * (u - 1 / 3)) * (1 - u ^ 2)))
      ((-(12 * α ^ 2)) * ((1 * (u - 1 / 3) + (u - 1 / 3) * 1) * (1 - u ^ 2)
        + ((u - 1 / 3) * (u - 1 / 3)) * (-2 * u))) u :=
    (((hd_id_sub_third u).mul (hd_id_sub_third u)).mul (hd_one_sub_sq u)).const_mul (-(12 * α ^ 2))
  have h5 : HasDerivAt (fun u : ℝ => α ^ 3 * (u - 1 / 3) ^ 4)
      (α ^ 3 * (4 * (u - 1 / 3) ^ (4 - 1) * 1)) u :=
    ((hd_id_sub_third u).pow 4).const_mul (α ^ 3)
  exact ((((h1.add h2).add h3).add h4).add h5).congr_deriv (by simp; ring)

private lemma hd_Qf (i : ℕ) (hi : i ≤ 4) (α u : ℝ) :
    HasDerivAt (fun v : ℝ => Qf i v α) (dQf i u α) u := by
  interval_cases i
  · exact hd_Qf_zero α u
  · exact hd_Qf_one α u
  · exact hd_Qf_two α u
  · exact hd_Qf_three α u
  · exact hd_Qf_four α u

/-! ## The derivative of `θ ↦ Pf i (cos 2θ) α` -/

private lemma deriv_cos_two_mul (θ : ℝ) :
    deriv (fun t : ℝ => Real.cos (2 * t)) θ = -2 * Real.sin (2 * θ) := by
  have h : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * (2 * 1)) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  rw [h.deriv]; ring

private lemma differentiableAt_cos_two_mul (θ : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => Real.cos (2 * t)) θ := by
  have h : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * (2 * 1)) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  exact h.differentiableAt

private lemma Pf_cos_deriv' (i : ℕ) (hi : i ≤ 4) (α θ : ℝ) :
    deriv (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ
      = -(2 * Real.sin (2 * θ)) * (α * dQf i (Real.cos (2 * θ)) α) := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simp only [Pf_zero, dQf_zero, mul_zero]
    simp
  · have hi0 : i ≠ 0 := by omega
    have hfun : (fun t : ℝ => Pf i (Real.cos (2 * t)) α)
        = (fun t : ℝ => α * Qf i (Real.cos (2 * t)) α) := by
      funext t
      simp only [Pf, hi0, ↓reduceIte]
    rw [hfun]
    have hd1 : DifferentiableAt ℝ (fun t : ℝ => Real.cos (2 * t)) θ :=
      differentiableAt_cos_two_mul θ
    have hQ := hd_Qf i hi α (Real.cos (2 * θ))
    have hd2 : DifferentiableAt ℝ (fun u : ℝ => Qf i u α) (Real.cos (2 * θ)) :=
      hQ.differentiableAt
    rw [deriv_const_mul α (by
      have hc : (fun t : ℝ => Qf i (Real.cos (2 * t)) α)
          = ((fun u : ℝ => Qf i u α) ∘ fun t : ℝ => Real.cos (2 * t)) := rfl
      rw [hc]; exact hd2.comp θ hd1)]
    rw [show (fun t : ℝ => Qf i (Real.cos (2 * t)) α)
          = ((fun u : ℝ => Qf i u α) ∘ fun t : ℝ => Real.cos (2 * t)) from rfl]
    rw [deriv_comp θ hd2 hd1, hQ.deriv, deriv_cos_two_mul]
    ring

private lemma Pf_cos_diff (i : ℕ) (hi : i ≤ 4) (α θ : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    have hconst : (fun t : ℝ => Pf 0 (Real.cos (2 * t)) α) = fun _ => (1 : ℝ) := by
      funext t; simp
    rw [hconst]
    exact differentiableAt_const (1 : ℝ)
  · have hfun : (fun t : ℝ => Pf i (Real.cos (2 * t)) α)
        = (fun t : ℝ => α * Qf i (Real.cos (2 * t)) α) := by
      funext t
      have hi0 : ¬ i = 0 := by omega
      simp only [Pf, hi0, ↓reduceIte]
    rw [hfun]
    have hQ : DifferentiableAt ℝ (fun u : ℝ => Qf i u α) (Real.cos (2 * θ)) :=
      (hd_Qf i hi α (Real.cos (2 * θ))).differentiableAt
    exact ((hQ.comp θ (differentiableAt_cos_two_mul θ)).const_mul α)

/-! ## `sin(2θ)·Γ' = α(cos 2θ - 1/3)Γ`, for every real `α` -/

private lemma Gam_sin_deriv (α θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
      = α * (Real.cos (2 * θ) - 1 / 3) * Work.Spaces.Gam α θ := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hG : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
  have hprod : HasDerivAt (fun t => Real.sin t * Real.cos t ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
  have hrpow := hprod.rpow_const (p := α / 3) (Or.inl (ne_of_gt hG))
  have hderiv : deriv (fun t => Work.Spaces.Gam α t) θ
      = (Real.cos θ * Real.cos θ ^ 2
          + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := hrpow.deriv
  have hcos2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq θ]
  have hq2 : (2 / 3 : ℝ) * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
      = Real.cos θ ^ 2 - Real.sin θ ^ 2 - 1 / 3 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hdG : Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))
      = Real.cos θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
    norm_num
    ring
  have hcoef : Real.sin (2 * θ) *
        ((Real.cos θ * Real.cos θ ^ 2
          + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3))
      = α * (Real.cos (2 * θ) - 1 / 3) * (Real.sin θ * Real.cos θ ^ 2) := by
    rw [Real.sin_two_mul, hcos2, hdG]
    linear_combination (Real.sin θ * Real.cos θ ^ 2 * α) * hq2
  have hrpowg : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
      = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * (Real.sin θ * Real.cos θ ^ 2) := by
    conv_lhs => rw [show α / 3 = (α / 3 - 1) + 1 from by ring]
    rw [Real.rpow_add hG (α / 3 - 1) 1, Real.rpow_one]
  rw [hderiv]
  show Real.sin (2 * θ) *
        ((Real.cos θ * Real.cos θ ^ 2
            + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1))
      = α * (Real.cos (2 * θ) - 1 / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
  rw [hrpowg]
  have e1 : Real.sin (2 * θ) *
        ((Real.cos θ * Real.cos θ ^ 2
            + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1))
      = (Real.sin (2 * θ) * ((Real.cos θ * Real.cos θ ^ 2
            + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)))
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
  have e2 : α * (Real.cos (2 * θ) - 1 / 3) *
        ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * (Real.sin θ * Real.cos θ ^ 2))
      = (α * (Real.cos (2 * θ) - 1 / 3) * (Real.sin θ * Real.cos θ ^ 2))
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
  rw [e1, e2, hcoef]

/-! ## The recursion of the angular polynomials -/

private lemma Pf_rec_algebra (i : ℕ) (hi : i ≤ 3) (α θ : ℝ) :
    (α * (Real.cos (2 * θ) - 1 / 3) * Work.Spaces.Gam α θ) * Pf i (Real.cos (2 * θ)) α
      + Work.Spaces.Gam α θ
          * (-(2 * Real.sin (2 * θ) ^ 2) * (α * dQf i (Real.cos (2 * θ)) α))
      = Work.Spaces.Gam α θ * Pf (i + 1) (Real.cos (2 * θ)) α := by
  have hs : Real.sin (2 * θ) ^ 2 = 1 - Real.cos (2 * θ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * θ)
    linarith
  interval_cases i
  · simp only [Nat.reduceAdd, Pf_zero, Pf_one, dQf_zero, mul_zero, mul_one]
    ring
  · simp only [Nat.reduceAdd, Pf_one, Pf_two, dQf_one, Qf_two]
    rw [hs]; ring
  · simp only [Nat.reduceAdd, Pf_two, Pf_three, dQf_two, Qf_three]
    rw [hs]; ring
  · simp only [Nat.reduceAdd, Pf_three, Pf_four, dQf_three, Qf_four]
    rw [hs]; ring

/-! ## `DthIter` on functions of `θ` alone -/

private lemma DthIter_rad_eq (i : ℕ) (g : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun _ θ' => g θ') = fun z θ => Work.Spaces.dthU^[i] g θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.dthU_apply,
        Function.iterate_succ_apply']

/-! ## The jet formula on the open interval -/

private lemma dthU_iter_Gam_eq : ∀ (i : ℕ), i ≤ 4 → ∀ (α θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
    Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ
      = Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α := by
  intro i
  induction i with
  | zero => intro _ α θ _; simp
  | succ i ih =>
      intro hi α θ hθ
      have hi3 : i ≤ 3 := by omega
      have hi4 : i ≤ 4 := by omega
      rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply]
      have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := IsOpen.mem_nhds isOpen_Ioo hθ
      have hev : (Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t))
          =ᶠ[𝓝 θ] ((fun t : ℝ => Work.Spaces.Gam α t)
            * (fun t : ℝ => Pf i (Real.cos (2 * t)) α)) := by
        filter_upwards [hmem] with t ht
        rw [Pi.mul_apply]
        exact ih (by omega) α t ht
      rw [hev.deriv_eq]
      have hG : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.Gam α t) θ :=
        Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
      have hP : DifferentiableAt ℝ (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ :=
        Pf_cos_diff i hi4 α θ
      rw [deriv_mul hG hP]
      rw [show Real.sin (2 * θ)
            * (deriv (fun t : ℝ => Work.Spaces.Gam α t) θ * Pf i (Real.cos (2 * θ)) α
              + Work.Spaces.Gam α θ * deriv (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ)
          = (Real.sin (2 * θ) * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ)
              * Pf i (Real.cos (2 * θ)) α
            + Work.Spaces.Gam α θ
              * (Real.sin (2 * θ) * deriv (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ)
          from by ring]
      rw [Gam_sin_deriv α θ hθ, Pf_cos_deriv' i hi4 α θ, ← Pf_rec_algebra i hi3 α θ]
      ring

/-! ## The endpoints -/

private lemma Gam_eq_zero_of_endpoint {α θ : ℝ} (hα : α ≠ 0)
    (hθ : θ = 0 ∨ θ = Real.pi / 2) : Work.Spaces.Gam α θ = 0 := by
  have h : α / 3 ≠ 0 := div_ne_zero hα (by norm_num)
  rcases hθ with rfl | rfl
  · simp only [Work.Spaces.Gam, Real.sin_zero, Real.cos_zero, one_pow, mul_one]
    exact Real.zero_rpow h
  · have hc : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    simp only [Work.Spaces.Gam, Real.sin_pi_div_two, hc, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      one_mul, mul_zero]
    exact Real.zero_rpow h

/-- The angular jet formula at the two endpoints of `Iθ`. -/
private lemma dthU_iter_Gam_eq_endpoint (i : ℕ) (hi : i ≠ 0) (α θ : ℝ)
    (hθ : θ = 0 ∨ θ = Real.pi / 2) :
    Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ
      = Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α := by
  have hsin : Real.sin (2 * θ) = 0 := by
    rcases hθ with rfl | rfl
    · simp
    · rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  have hzero : Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply, hsin, zero_mul]
  rw [hzero]
  rcases eq_or_ne α 0 with hα | hα
  · subst hα
    have hG : Work.Spaces.Gam 0 θ = 1 := by
      simp only [Work.Spaces.Gam, zero_div, Real.rpow_zero]
    rw [hG, one_mul]
    simp only [Pf, hi, ↓reduceIte, zero_mul]
  · rw [Gam_eq_zero_of_endpoint hα hθ, zero_mul]

/-! ## The main statement -/

theorem DthIter_Gam_Pf (α : ℝ) (i : ℕ) (hi : i ≤ 4) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z θ
      = Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α := by
  rw [DthIter_rad_eq i (fun t : ℝ => Work.Spaces.Gam α t)]
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simp only [Function.iterate_zero_apply, Pf_zero, mul_one]
  · rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · exact dthU_iter_Gam_eq i hi α θ ⟨h0, h1⟩
      · exact dthU_iter_Gam_eq_endpoint i (by omega) α θ (Or.inr h1)
    · exact dthU_iter_Gam_eq_endpoint i (by omega) α θ (Or.inl h0.symm)

end Work.FTS.LocData
