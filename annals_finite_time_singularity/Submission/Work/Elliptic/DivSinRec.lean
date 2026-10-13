/-
Copyright: work module for the Elgindi finite-time singularity project.

# The recursion for the angular quotient `h / sin(2θ)`

`DivSinIter` (the higher-order angular estimate behind `DivisionBySin`) is proved by
differentiating `SinQ h = h / sin(2θ)` under the iterated operator
`Dth1 = sin(2θ) ∂_θ` and expanding the resulting product by the binomial rule.

This file supplies the recursive identity on which that induction rests:

  `D_θ^i (h / sin 2θ) = D_θ^{i-1}(h') - ∑_{l<i} C(i-1,l)
        · D_θ^{i-1-l}(2 cos 2θ) · D_θ^l (h / sin 2θ)`

on `(0, π/2)`, for a smooth angular slice `h` vanishing at the two endpoints.

The operator `Work.Elliptic.Dth1` is definitionally `Work.Spaces.Lop`, and the abstract
Leibniz machinery of `Work.Spaces.DerivLike` (instantiated here for `Lop` on an open set)
supplies the binomial expansion.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Elliptic.Algebra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## `Lop = Dth1` as a derivation-like operator -/

/-- The class of functions that are `C^∞` on `U` is closed under the algebraic
operations of `Work.Spaces.FunClass`. -/
private lemma lop_funClass (U : Set ℝ) :
    Work.Spaces.FunClass (fun u : ℝ → ℝ => ContDiffOn ℝ ⊤ u U) where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    simpa only [Pi.smul_apply, smul_eq_mul] using hA.const_smul c

/-- `Work.Spaces.Lop = Dth1` is a derivation-like operator on the open set `U`. -/
private lemma lop_derivLike (U : Set ℝ) (hU : IsOpen U) :
    Work.Spaces.DerivLike U (fun u : ℝ → ℝ => ContDiffOn ℝ ⊤ u U) Work.Spaces.Lop where
  add := by
    intro A B hA hB θ hθ
    have dA : DifferentiableAt ℝ A θ :=
      (hA.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
    have dB : DifferentiableAt ℝ B θ :=
      (hB.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
    show Real.sin (2 * θ) * deriv (A + B) θ
        = Real.sin (2 * θ) * deriv A θ + Real.sin (2 * θ) * deriv B θ
    rw [show deriv (A + B) θ = deriv A θ + deriv B θ from by
      simpa only [Pi.add_apply] using deriv_add dA dB]
    ring
  mul := by
    intro A B hA hB θ hθ
    exact Work.Spaces.Lop_mul A B θ
      ((hA.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp))
      ((hB.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp))
  congr := by
    intro A B hAB θ hθ
    have hev : A =ᶠ[nhds θ] B := by
      filter_upwards [hU.mem_nhds hθ] with x hx
      exact hAB hx
    show Real.sin (2 * θ) * deriv A θ = Real.sin (2 * θ) * deriv B θ
    rw [hev.deriv_eq]
  preserve := by
    intro A hA
    have hderiv : ContDiffOn ℝ ⊤ (deriv A) U := hA.deriv_of_isOpen hU le_top
    have hsin : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) U := by fun_prop
    exact hsin.mul hderiv
  smul := by
    intro c A hA θ hθ
    show Real.sin (2 * θ) * deriv (fun p => c * A p) θ
        = c * (Real.sin (2 * θ) * deriv A θ)
    rw [deriv_const_mul_field c]
    ring

/-- The iterates of `Lop` are linear on `C^∞`-functions of an open set. -/
private lemma lop_iter_sub {U : Set ℝ} (hU : IsOpen U) {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ ⊤ u U) (hv : ContDiffOn ℝ ⊤ v U) (n : ℕ) :
    Set.EqOn (Work.Spaces.Lop^[n] (u - v))
      (fun θ => Work.Spaces.Lop^[n] u θ - Work.Spaces.Lop^[n] v θ) U := by
  have hD := lop_derivLike U hU
  have hP := lop_funClass U
  have hw : ContDiffOn ℝ ⊤ (fun p => (-1 : ℝ) * v p) U := hP.smul (-1) v hv
  have h1 := Work.Spaces.DerivLike.iterate_add hD n hu hw
  have h2 := Work.Spaces.DerivLike.iterate_smul hD n (-1) hv
  have hfun : (u - v) = (u + fun p => (-1 : ℝ) * v p) := by
    funext p; simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, neg_one_mul]
  rw [hfun]
  refine h1.trans ?_
  intro θ hθ
  have h2θ := h2 hθ
  simp only [Pi.add_apply]
  rw [h2θ]
  ring

/-- `Dth1Iter n f` is the `n`-th iterate of `Work.Spaces.Lop` applied to `f`. -/
lemma Dth1Iter_eq_iterate_Lop (n : ℕ) (f : ℝ → ℝ) :
    Dth1Iter n f = Work.Spaces.Lop^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Dth1Iter_succ, ih, Function.iterate_succ_apply']
      rfl

/-! ## Differentiating the angular quotient -/

/-- `D_θ(h / sin 2θ) = h' - (2 cos 2θ)·(h / sin 2θ)` on `(0, π/2)`. -/
private lemma Lop_SinQ_eqOn {h : ℝ → ℝ} (hsm : SmoothSlice h) :
    Set.EqOn (Work.Spaces.Lop (SinQ h))
      (fun θ => deriv h θ - 2 * Real.cos (2 * θ) * SinQ h θ) (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hsmU : ContDiffOn ℝ ⊤ h (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)
  have hsinU : ContDiffOn ℝ ⊤ (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))
  have hgU : ContDiffOn ℝ ⊤ (SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ ⊤ (fun x => h x / Real.sin (2 * x)) _
    exact hsmU.div hsinU hne
  have hneθ : ∀ᶠ x in nhds θ, Real.sin (2 * x) ≠ 0 := by
    have hc : ContinuousAt (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
    exact hc.eventually_ne (hne θ hθ)
  have heq : (fun x : ℝ => Real.sin (2 * x) * SinQ h x) =ᶠ[nhds θ] h := by
    filter_upwards [hneθ] with x hx
    simp only [SinQ]
    rw [mul_comm, div_mul_cancel₀ _ hx]
  have hdeq : deriv (fun x : ℝ => Real.sin (2 * x) * SinQ h x) θ = deriv h θ := heq.deriv_eq
  have dsin : DifferentiableAt ℝ (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
  have dg : DifferentiableAt ℝ (SinQ h) θ :=
    (hgU.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
  have hprod : deriv (fun x : ℝ => Real.sin (2 * x) * SinQ h x) θ
      = deriv (fun x : ℝ => Real.sin (2 * x)) θ * SinQ h θ
        + Real.sin (2 * θ) * deriv (SinQ h) θ :=
    deriv_mul dsin dg
  rw [deriv_sin_two θ] at hprod
  show Real.sin (2 * θ) * deriv (SinQ h) θ = deriv h θ - 2 * Real.cos (2 * θ) * SinQ h θ
  rw [← hdeq, hprod]
  ring

/-! ## The recursion -/

theorem DivSinRec (i : ℕ) (h : ℝ → ℝ) (hi : 1 ≤ i) (hsm : Work.Elliptic.SmoothSlice h)
    (h0 : h 0 = 0) (hp : h (Real.pi / 2) = 0) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ =
        Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ -
          ∑ l ∈ Finset.range i, (Nat.choose (i - 1) l : ℝ) *
            (Work.Elliptic.Dth1Iter (i - 1 - l) (fun θ => 2 * Real.cos (2 * θ)) θ) *
            (Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h) θ) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  intro θ hθ
  simp only [Nat.add_sub_cancel]
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hsmU : ContDiffOn ℝ ⊤ h (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)
  have hsinU : ContDiffOn ℝ ⊤ (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))
  have hgU : ContDiffOn ℝ ⊤ (SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ ⊤ (fun x => h x / Real.sin (2 * x)) _
    exact hsmU.div hsinU hne
  have hφU : ContDiffOn ℝ ⊤ (fun x : ℝ => 2 * Real.cos (2 * x)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hderU : ContDiffOn ℝ ⊤ (deriv h) (Set.Ioo 0 (Real.pi / 2)) := hsmU.deriv_of_isOpen hU le_top
  have hφgU : ContDiffOn ℝ ⊤ ((fun x : ℝ => 2 * Real.cos (2 * x)) * SinQ h)
      (Set.Ioo 0 (Real.pi / 2)) := hφU.mul hgU
  have hD := lop_derivLike (Set.Ioo (0 : ℝ) (Real.pi / 2)) hU
  have hEq : Set.EqOn (Work.Spaces.Lop (SinQ h))
      (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * SinQ h θ)
      (Set.Ioo 0 (Real.pi / 2)) := Lop_SinQ_eqOn hsm
  have h1 : Work.Spaces.Lop^[j + 1] (SinQ h) θ
      = Work.Spaces.Lop^[j]
          (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * SinQ h θ) θ := by
    rw [Function.iterate_succ_apply]
    exact (Work.Spaces.DerivLike.iterate_congr hD j hEq) hθ
  have h2 : Work.Spaces.Lop^[j]
        (fun θ => deriv h θ - (fun x : ℝ => 2 * Real.cos (2 * x)) θ * SinQ h θ) θ
      = Work.Spaces.Lop^[j] (deriv h) θ
        - Work.Spaces.Lop^[j] ((fun x : ℝ => 2 * Real.cos (2 * x)) * SinQ h) θ :=
    (lop_iter_sub hU hderU hφgU j) hθ
  have h3 : Work.Spaces.Lop^[j] ((fun x : ℝ => 2 * Real.cos (2 * x)) * SinQ h) θ
      = ∑ l ∈ Finset.range (j + 1), (Nat.choose j l : ℝ)
          * (Work.Spaces.Lop^[j - l] (fun x : ℝ => 2 * Real.cos (2 * x)) θ)
          * (Work.Spaces.Lop^[l] (SinQ h) θ) := by
    have hL := Work.Spaces.Lop_iter_mul_eqOn (SinQ h) (fun x : ℝ => 2 * Real.cos (2 * x))
      (Set.Ioo 0 (Real.pi / 2)) hU hgU hφU j
    have hcomm : (SinQ h) * (fun x : ℝ => 2 * Real.cos (2 * x))
        = (fun x : ℝ => 2 * Real.cos (2 * x)) * (SinQ h) := by
      funext x; exact mul_comm _ _
    rw [hcomm] at hL
    rw [hL hθ]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hstep : Work.Spaces.Lop^[j + 1] (SinQ h) θ
      = Work.Spaces.Lop^[j] (deriv h) θ
        - ∑ l ∈ Finset.range (j + 1), (Nat.choose j l : ℝ)
            * (Work.Spaces.Lop^[j - l] (fun x : ℝ => 2 * Real.cos (2 * x)) θ)
            * (Work.Spaces.Lop^[l] (SinQ h) θ) := by
    rw [h1, h2, h3]
  simp only [Dth1Iter_eq_iterate_Lop]
  exact hstep

end Work.Elliptic
