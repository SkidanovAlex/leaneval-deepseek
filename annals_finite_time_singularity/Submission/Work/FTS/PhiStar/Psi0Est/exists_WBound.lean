import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Psi0Classes
import Submission.Work.FTS.PhiStar.Psi0Ode
import Submission.Work.FTS.PhiStar.Psi0Ident
import Submission.Work.Spaces.Gam_mul_weight_le
import Submission.Work.FTS.PhiStar.Psi0Est.sin_sq_cos_rpow_mul_rpow_le
import Submission.Work.FTS.PhiStar.Psi0Est.sin_two_rpow_div_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option maxHeartbeats 1600000

namespace WB

/-! ## `dthU` on an open set: smoothness, differentiability, germ-locality and linearity -/

/-- `dthU φ = sin(2·) · φ'` as a function equality. -/
lemma dthU_eq_fun (φ : ℝ → ℝ) :
    Work.Spaces.dthU φ = fun θ : ℝ => Real.sin (2 * θ) * deriv φ θ := by
  funext θ
  rw [Work.Spaces.dthU_apply]

/-- `dthU` preserves `C^∞`-smoothness on an open set. -/
lemma dthU_contDiffOn {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU f) U := by
  have hone : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by simp
  have hd : ContDiffOn ℝ (∞ : ℕ∞ω) (deriv f) U :=
    hf.deriv_of_isOpen hU (m := (∞ : ℕ∞ω)) hone
  have hsin : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ)) U := by fun_prop
  rw [dthU_eq_fun]
  exact hsin.mul hd

/-- Every iterate of `dthU` preserves `C^∞`-smoothness on an open set. -/
lemma dthU_iter_contDiffOn {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) (m : ℕ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU^[m] f) U := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact dthU_contDiffOn hU ih

/-- Interior differentiability of the `dthU`-iterates of a `C^∞`-function. -/
lemma dthU_iter_differentiableAt {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) (m : ℕ) {θ : ℝ} (hθ : θ ∈ U) :
    DifferentiableAt ℝ (Work.Spaces.dthU^[m] f) θ :=
  ((dthU_iter_contDiffOn hU hf m).contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)

/-- Germ-locality of the `dthU`-iterates. -/
lemma dthU_iter_congr {f g : ℝ → ℝ} {θ : ℝ}
    (h : Filter.EventuallyEq (nhds θ) f g) (m : ℕ) :
    Work.Spaces.dthU^[m] f θ = Work.Spaces.dthU^[m] g θ := by
  have hmain : ∀ m : ℕ, Filter.EventuallyEq (nhds θ) (Work.Spaces.dthU^[m] f)
      (Work.Spaces.dthU^[m] g) := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih =>
        have hd : Filter.EventuallyEq (nhds θ) (deriv (Work.Spaces.dthU^[m] f))
            (deriv (Work.Spaces.dthU^[m] g)) := ih.deriv
        have hm :=
          (Filter.EventuallyEq.refl (nhds θ) (fun θ' : ℝ => Real.sin (2 * θ'))).mul hd
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dthU_eq_fun, dthU_eq_fun]
        exact hm
  exact (hmain m).eq_of_nhds

/-- The derivative of the three-term combination. -/
lemma deriv_three {Uf Ug Uh : ℝ → ℝ} {θ : ℝ}
    (hdf : DifferentiableAt ℝ Uf θ) (hdg : DifferentiableAt ℝ Ug θ)
    (hdh : DifferentiableAt ℝ Uh θ) :
    deriv (fun x => 2 * Uf x - 4 * Ug x - Uh x) θ
      = 2 * deriv Uf θ - 4 * deriv Ug θ - deriv Uh θ := by
  have h := ((hdf.hasDerivAt.const_mul 2).sub (hdg.hasDerivAt.const_mul 4)).sub hdh.hasDerivAt
  exact h.deriv

/-- Linearity of the `dthU`-iterates on an open set (the three-term form used below). -/
lemma dthU_iter_three_eqOn {U : Set ℝ} (hU : IsOpen U) {f g h : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) (hg : ContDiffOn ℝ (∞ : ℕ∞ω) g U)
    (hh : ContDiffOn ℝ (∞ : ℕ∞ω) h U) (m : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[m] (fun θ => 2 * f θ - 4 * g θ - h θ))
      (fun θ => 2 * Work.Spaces.dthU^[m] f θ - 4 * Work.Spaces.dthU^[m] g θ
        - Work.Spaces.dthU^[m] h θ) U := by
  induction m with
  | zero => intro θ hθ; simp
  | succ m ih =>
      intro θ hθ
      have hev : Filter.EventuallyEq (nhds θ)
          (Work.Spaces.dthU^[m] (fun θ => 2 * f θ - 4 * g θ - h θ))
          (fun θ => 2 * Work.Spaces.dthU^[m] f θ - 4 * Work.Spaces.dthU^[m] g θ
            - Work.Spaces.dthU^[m] h θ) :=
        ih.eventuallyEq_of_mem (hU.mem_nhds hθ)
      have hder : deriv (Work.Spaces.dthU^[m] (fun θ => 2 * f θ - 4 * g θ - h θ)) θ
          = deriv (fun x => 2 * Work.Spaces.dthU^[m] f x - 4 * Work.Spaces.dthU^[m] g x
              - Work.Spaces.dthU^[m] h x) θ := hev.deriv_eq
      have hdf : DifferentiableAt ℝ (Work.Spaces.dthU^[m] f) θ :=
        dthU_iter_differentiableAt hU hf m hθ
      have hdg : DifferentiableAt ℝ (Work.Spaces.dthU^[m] g) θ :=
        dthU_iter_differentiableAt hU hg m hθ
      have hdh : DifferentiableAt ℝ (Work.Spaces.dthU^[m] h) θ :=
        dthU_iter_differentiableAt hU hh m hθ
      have hstep : Work.Spaces.dthU (Work.Spaces.dthU^[m]
            (fun θ => 2 * f θ - 4 * g θ - h θ)) θ
          = 2 * Work.Spaces.dthU (Work.Spaces.dthU^[m] f) θ
            - 4 * Work.Spaces.dthU (Work.Spaces.dthU^[m] g) θ
            - Work.Spaces.dthU (Work.Spaces.dthU^[m] h) θ := by
        rw [Work.Spaces.dthU_apply, hder, Work.Spaces.dthU_apply, Work.Spaces.dthU_apply,
          Work.Spaces.dthU_apply, deriv_three hdf hdg hdh]
        ring
      rw [Function.iterate_succ_apply' (Work.Spaces.dthU) m
            (fun θ => 2 * f θ - 4 * g θ - h θ),
        Function.iterate_succ_apply' (Work.Spaces.dthU) m f,
        Function.iterate_succ_apply' (Work.Spaces.dthU) m g,
        Function.iterate_succ_apply' (Work.Spaces.dthU) m h]
      exact hstep

/-! ## The value of `D_θ^j ψ''` via the two-term identity -/

/-- On `(0,π/2)` the `dthU`-iterates of `ψ''` split as `2 D_θ^j P − 4 D_θ^j ψ − D_θ^j Γ̄`. -/
lemma sndDeriv_dthU_iter
    (hident : ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 2 (psiSol α) θ
        = 2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.dthU^[j] (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ') θ
      = 2 * Work.Spaces.dthU^[j] (Pfun α) θ - 4 * Work.Spaces.dthU^[j] (psiSol α) θ
        - Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ := by
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have heq : Set.EqOn (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ')
      (fun θ' : ℝ => 2 * Pfun α θ' - 4 * psiSol α θ' - Work.FTS.VocabO.GamBar α θ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := fun θ' hθ' => hident α hα hα1 θ' hθ'
  have hev : Filter.EventuallyEq (nhds θ) (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ')
      (fun θ' : ℝ => 2 * Pfun α θ' - 4 * psiSol α θ' - Work.FTS.VocabO.GamBar α θ') :=
    heq.eventuallyEq_of_mem (hU.mem_nhds hθ)
  rw [dthU_iter_congr hev j]
  have hGam : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ' : ℝ => Work.FTS.VocabO.GamBar α θ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [show (fun θ' : ℝ => Work.FTS.VocabO.GamBar α θ')
        = fun θ' => Work.Spaces.Gam α θ' * (1 / Work.Spaces.c α) - (5 / 4) * Real.sin (2 * θ')
      from by funext t; rw [Work.FTS.VocabO.GamBar]; ring]
    exact ((contDiffOn_Gam α).mul contDiffOn_const).sub (contDiffOn_const.mul (by fun_prop))
  exact dthU_iter_three_eqOn hU (contDiffOn_Pfun α (le_of_lt hα))
    (contDiffOn_psiSol α hα hα1) hGam j hθ

/-! ## The weighted bounds -/

/-- The angular weight `w = sin(2θ)^{-α/5}/(α + sin 2θ)` is nonnegative on the open quadrant. -/
lemma weight_nonneg (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) := by
  have h2θ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  exact div_nonneg (Real.rpow_nonneg (le_of_lt h2θ) _) (le_of_lt hden)

/-- `α · sin²θ · cos^{2α/3}θ · w ≤ 1`. -/
lemma weight_P_mul_le (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
  have h2θ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], le_of_lt hθ.2⟩
  have hF := sin_sq_cos_rpow_mul_rpow_le α θ hα hα1 hθ
  have hFnn : 0 ≤ Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(α / 5)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hcos _))
      (Real.rpow_nonneg (le_of_lt h2θ) _)
  have hfrac : α / (α + Real.sin (2 * θ)) ≤ 1 := by
    rw [div_le_one hden]; linarith [h2θ]
  calc α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = (α / (α + Real.sin (2 * θ)))
          * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)
            * (Real.sin (2 * θ)) ^ (-(α / 5))) := by ring
    _ ≤ 1 * 1 := mul_le_mul hfrac hF hFnn (by norm_num)
    _ = 1 := by norm_num

/-- `sin(2θ) · w ≤ 2`. -/
lemma weight_sin_mul_le (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.sin (2 * θ) * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 2 := by
  have h2θ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hkey : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(α / 5))
      = (Real.sin (2 * θ)) ^ (1 - α / 5) := by
    have h := Real.rpow_add h2θ 1 (-(α / 5))
    rw [Real.rpow_one] at h
    exact h.symm
  have h2 := sin_two_rpow_div_le α (Real.sin (2 * θ)) hα hα1 h2θ (Real.sin_le_one _)
  have hsplit : Real.sin (2 * θ)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = (Real.sin (2 * θ)) ^ (1 - α / 5) / (α + Real.sin (2 * θ)) := by
    rw [← mul_div_assoc, hkey]
  rw [hsplit]
  exact h2

/-- `α · Γ(θ) · w ≤ 1`. -/
lemma weight_Gam_mul_le (α θ : ℝ) (hα : 0 < α)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    α * Work.Spaces.Gam α θ
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
  have h := Work.Spaces.Gam_mul_weight_le α θ hα (Set.Ioo_subset_Icc_self hθ)
  rwa [show α * Work.Spaces.Gam α θ
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)) from by rw [mul_div_assoc]]

/-- The weighted bound for a combination of the three class bounds. -/
lemma weighted_comb_le (κ ℓ ν cc dd : ℕ → ℝ)
    (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j) (hν0 : ∀ j, 0 ≤ ν j)
    (hcc0 : ∀ j, 0 ≤ cc j) (hdd0 : ∀ j, 0 ≤ dd j)
    {j : ℕ} {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {A B C : ℝ}
    (hA : A ≤ κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
      + ℓ j * Real.sin (2 * θ))
    (hB : B ≤ ν j * Real.sin (2 * θ))
    (hC : C ≤ cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ)) :
    (2 * A + 4 * B + C)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 2 * κ j + 4 * ℓ j + 8 * ν j + cc j + 2 * dd j := by
  have hwnn := weight_nonneg α θ hα hθ
  have hPw := weight_P_mul_le α θ hα hα1 hθ
  have hSw := weight_sin_mul_le α θ hα hα1 hθ
  have hGw := weight_Gam_mul_le α θ hα hθ
  have hAw : A * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ κ j + 2 * ℓ j := by
    have h1 : A * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
            + ℓ j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_right hA hwnn
    have h2 : (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
            + ℓ j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ κ j * 1 + ℓ j * 2 := by
      have he : (κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
            + ℓ j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          = κ j * (α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
            + ℓ j * (Real.sin (2 * θ)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      rw [he]
      exact add_le_add (mul_le_mul_of_nonneg_left hPw (hκ0 j))
        (mul_le_mul_of_nonneg_left hSw (hℓ0 j))
    linarith
  have hBw : B * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ ν j * 2 := by
    have h1 : B * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ ν j * Real.sin (2 * θ)
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_right hB hwnn
    have h2 : ν j * Real.sin (2 * θ)
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ ν j * 2 := by
      have he : ν j * Real.sin (2 * θ)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          = ν j * (Real.sin (2 * θ)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hSw (hν0 j)
    linarith
  have hCw : C * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ cc j + 2 * dd j := by
    have h1 : C * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ (cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_right hC hwnn
    have h2 : (cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ cc j * 1 + dd j * 2 := by
      have he : (cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          = cc j * (α * Work.Spaces.Gam α θ
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
            + dd j * (Real.sin (2 * θ)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      rw [he]
      exact add_le_add (mul_le_mul_of_nonneg_left hGw (hcc0 j))
        (mul_le_mul_of_nonneg_left hSw (hdd0 j))
    linarith
  have he : (2 * A + 4 * B + C)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = 2 * (A * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        + 4 * (B * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        + C * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by ring
  rw [he]
  linarith [hAw, hBw, hCw]

end WB

theorem exists_WBound
    (hident : ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      iteratedDeriv 2 (psiSol α) θ = 2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ)
    (hZ : ∃ κ ell : ℕ → ℝ, ZClass κ ell) (hA : ∃ ν : ℕ → ℝ, AClass ν)
    (hH : ∃ cc dd : ℕ → ℝ, HClass cc dd) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |iteratedDeriv 2 (psiSol α) θ| ≤ C ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 5 →
        |Work.Spaces.dthU^[j] (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ') θ|
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ C) := by
  obtain ⟨κ, ℓ, hκ0, hℓ0, hZb⟩ := hZ
  obtain ⟨ν, hν0, hAb⟩ := hA
  obtain ⟨cc, dd, hcc0, hdd0, hHb⟩ := hH
  set S : ℝ := ∑ j ∈ Finset.range 6, (κ j + ℓ j + ν j + cc j + dd j) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun j _ => by
      have h1 := hκ0 j; have h2 := hℓ0 j; have h3 := hν0 j
      have h4 := hcc0 j; have h5 := hdd0 j
      linarith)
  refine ⟨1000 + 4 * ν 0 + 1000 * S, by have := hν0 0; linarith, ?_⟩
  intro α hα hα1 θ hθ
  have h2θpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have h2θle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  constructor
  · -- the pointwise bound on `ψ''`
    have hid := hident α hα hα1 θ hθ
    have hP := Pfun_abs_le α hα hα1 (Set.Ioo_subset_Icc_self hθ)
    have hψ : |psiSol α θ| ≤ ν 0 * Real.sin (2 * θ) := by
      have := hAb α hα hα1 0 (by norm_num) θ hθ
      simpa using this
    have hΓ := abs_GamBar_le α θ hα (by linarith) (Set.Ioo_subset_Icc_self hθ)
    have hcinv : 1 / Work.Spaces.c α ≤ 10 := by
      have hc := (Work.Spaces.c_bounds α hα (by linarith : α ≤ 1)).1
      calc 1 / Work.Spaces.c α ≤ 1 / (1 / 10 : ℝ) := one_div_le_one_div_of_le (by norm_num) hc
        _ = 10 := by norm_num
    have habs : |2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ|
        ≤ 2 * |Pfun α θ| + 4 * |psiSol α θ| + |Work.FTS.VocabO.GamBar α θ| := by
      have h1 : |2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ|
          ≤ |2 * Pfun α θ - 4 * psiSol α θ| + |Work.FTS.VocabO.GamBar α θ| := abs_sub _ _
      have h2 : |2 * Pfun α θ - 4 * psiSol α θ| ≤ |2 * Pfun α θ| + |4 * psiSol α θ| :=
        abs_sub _ _
      have h3 : |(2 : ℝ) * Pfun α θ| = 2 * |Pfun α θ| := by rw [abs_mul]; norm_num
      have h4 : |(4 : ℝ) * psiSol α θ| = 4 * |psiSol α θ| := by rw [abs_mul]; norm_num
      linarith
    rw [hid]
    calc |2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ|
        ≤ 2 * |Pfun α θ| + 4 * |psiSol α θ| + |Work.FTS.VocabO.GamBar α θ| := habs
      _ ≤ 2 * 20 + 4 * (ν 0 * Real.sin (2 * θ)) + (1 / Work.Spaces.c α + 5 / 4) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hP (by norm_num))
            (mul_le_mul_of_nonneg_left hψ (by norm_num))) hΓ
      _ ≤ 1000 + 4 * ν 0 + 1000 * S := by
          have h1 : 4 * (ν 0 * Real.sin (2 * θ)) ≤ 4 * (ν 0 * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2θle (hν0 0)) (by norm_num)
          linarith [h1, hcinv, hSnn]
  · -- the weighted bounds for `1 ≤ j ≤ 5`
    intro j hj1 hj5
    have hjmem : j ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
    have hSterm : κ j + ℓ j + ν j + cc j + dd j ≤ S := by
      rw [hSdef]
      exact Finset.single_le_sum (s := Finset.range 6)
        (f := fun i => κ i + ℓ i + ν i + cc i + dd i) (a := j) (fun i _ => by
          have h1 := hκ0 i; have h2 := hℓ0 i; have h3 := hν0 i
          have h4 := hcc0 i; have h5 := hdd0 i
          linarith) hjmem
    have hP := hZb α hα hα1 j hj1 hj5 θ hθ
    have hψ : |Work.Spaces.dthU^[j] (psiSol α) θ| ≤ ν j * Real.sin (2 * θ) :=
      hAb α hα hα1 j (by omega) θ hθ
    have hΓ := hHb α hα hα1 j hj1 hj5 θ hθ
    rw [mul_div_assoc]
    have hid := WB.sndDeriv_dthU_iter hident α hα hα1 j hθ
    rw [hid]
    have habs : |2 * Work.Spaces.dthU^[j] (Pfun α) θ
          - 4 * Work.Spaces.dthU^[j] (psiSol α) θ
          - Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ|
        ≤ 2 * |Work.Spaces.dthU^[j] (Pfun α) θ|
          + 4 * |Work.Spaces.dthU^[j] (psiSol α) θ|
          + |Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ| := by
      have h1 : |2 * Work.Spaces.dthU^[j] (Pfun α) θ
            - 4 * Work.Spaces.dthU^[j] (psiSol α) θ
            - Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ|
          ≤ |2 * Work.Spaces.dthU^[j] (Pfun α) θ
              - 4 * Work.Spaces.dthU^[j] (psiSol α) θ|
            + |Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ| := abs_sub _ _
      have h2 : |2 * Work.Spaces.dthU^[j] (Pfun α) θ
            - 4 * Work.Spaces.dthU^[j] (psiSol α) θ|
          ≤ |2 * Work.Spaces.dthU^[j] (Pfun α) θ|
            + |4 * Work.Spaces.dthU^[j] (psiSol α) θ| := abs_sub _ _
      have h3 : |(2 : ℝ) * Work.Spaces.dthU^[j] (Pfun α) θ|
          = 2 * |Work.Spaces.dthU^[j] (Pfun α) θ| := by rw [abs_mul]; norm_num
      have h4 : |(4 : ℝ) * Work.Spaces.dthU^[j] (psiSol α) θ|
          = 4 * |Work.Spaces.dthU^[j] (psiSol α) θ| := by rw [abs_mul]; norm_num
      linarith
    have hw := WB.weight_nonneg α θ hα hθ
    refine le_trans (mul_le_mul_of_nonneg_right habs hw) ?_
    have hcomb := WB.weighted_comb_le κ ℓ ν cc dd hκ0 hℓ0 hν0 hcc0 hdd0 hα hα1 hθ
      (j := j) hP hψ hΓ
    refine le_trans hcomb ?_
    have h1 := hκ0 j; have h2 := hℓ0 j; have h3 := hν0 j
    have h4 := hcc0 j; have h5 := hdd0 j
    have h00 : (0 : ℝ) ≤ ν 0 := hν0 0
    have h6 : 2 * κ j + 4 * ℓ j + 8 * ν j + cc j + 2 * dd j
        ≤ 8 * (κ j + ℓ j + ν j + cc j + dd j) := by linarith
    have h7 : 8 * (κ j + ℓ j + ν j + cc j + dd j)
        ≤ 1000 * (κ j + ℓ j + ν j + cc j + dd j) := by linarith
    have h8 : 1000 * (κ j + ℓ j + ν j + cc j + dd j) ≤ 1000 * S := by linarith
    linarith

end Work.FTS.PhiStar.Psi0Est
