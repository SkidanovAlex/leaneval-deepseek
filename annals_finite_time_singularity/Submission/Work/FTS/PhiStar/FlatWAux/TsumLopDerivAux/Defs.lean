/-
Auxiliary material for `Work.FTS.PhiStar.FlatWAux.TsumLopDeriv`.

The angular operator `Work.Spaces.Lop u θ = sin(2θ) · u'(θ)` acts on functions of `θ` alone.
This file collects

* the coefficient functions `Asf a = Lop^[a] (sin 2·)` and their elementary properties
  (smoothness, uniform bounds on a compact interval),
* order bookkeeping for `ContDiffOn` under `iteratedDeriv` and under iteration of `Lop`,
* the *recursion* of `Lop`-iterates: for `g` of class `C^{i+1}` on an open set `U`,

  `Lop^[i+1] g = ∑_{a ≤ i} C(i,a) · Asf a · Lop^[i-a] (deriv g)`   on `U`,

  which is the Leibniz rule for the derivation `Lop` applied to `Lop g = Asf 0 · deriv g`.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopLeibnizPoint

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar.FlatWAux

/-- The angular coefficients `Asf a θ = D_θ^a (sin 2·) θ`, i.e. the `a`-fold iterate of `Lop`
applied to `θ ↦ sin(2θ)`. -/
def Asf (a : ℕ) : ℝ → ℝ := (Work.Spaces.Lop^[a]) (fun θ : ℝ => Real.sin (2 * θ))

theorem Asf_zero : Asf 0 = fun θ : ℝ => Real.sin (2 * θ) := rfl

theorem Asf_succ (a : ℕ) : Asf (a + 1) = Work.Spaces.Lop (Asf a) :=
  Function.iterate_succ_apply' Work.Spaces.Lop a (fun θ : ℝ => Real.sin (2 * θ))

theorem Asf_contDiff : ∀ a : ℕ, ∀ n : ℕ, ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (Asf a) := by
  intro a
  induction a with
  | zero =>
      intro n
      show ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
      fun_prop
  | succ a ih =>
      intro n
      have h1 : ContDiff ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Asf a) := ih (n + 1)
      have hcast : (((n : ℕ)) : WithTop ℕ∞) + 1 = (((n + 1 : ℕ)) : WithTop ℕ∞) := by
        push_cast; ring
      rw [← hcast] at h1
      have hs : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) := by
        fun_prop
      rw [Asf_succ]
      show ContDiff ℝ ((n : ℕ) : WithTop ℕ∞)
        (fun θ : ℝ => Real.sin (2 * θ) * deriv (Asf a) θ)
      exact hs.mul h1.deriv'

theorem Asf_deriv_continuous (k : ℕ) : Continuous (deriv (Asf k)) := by
  have h2 : ContDiff ℝ (((2 : ℕ)) : WithTop ℕ∞) (Asf k) := Asf_contDiff k 2
  have hc : (((1 : ℕ)) : WithTop ℕ∞) + 1 = (((2 : ℕ)) : WithTop ℕ∞) := by push_cast; norm_num
  rw [← hc] at h2
  exact h2.deriv'.continuous

/-- Uniform bound for the coefficient functions `Asf k` and their derivatives, `k ≤ n`, on a
compact interval. -/
theorem Asf_bound_le (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ k ≤ n, ∀ y ∈ Set.Icc a b, |Asf k y| ≤ C) ∧
      (∀ k ≤ n, ∀ y ∈ Set.Icc a b, |deriv (Asf k) y| ≤ D) := by
  have hex : ∀ k : ℕ, ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ y ∈ Set.Icc a b, |Asf k y| ≤ C) ∧ (∀ y ∈ Set.Icc a b, |deriv (Asf k) y| ≤ D) := by
    intro k
    have h1 : ContinuousOn (Asf k) (Set.Icc a b) := (Asf_contDiff k 0).continuous.continuousOn
    have h2 : ContinuousOn (deriv (Asf k)) (Set.Icc a b) :=
      (Asf_deriv_continuous k).continuousOn
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h1
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn h2
    refine ⟨max C 0, max D 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
    · intro y hy
      exact le_trans (by simpa [Real.norm_eq_abs] using hC y hy) (le_max_left _ _)
    · intro y hy
      exact le_trans (by simpa [Real.norm_eq_abs] using hD y hy) (le_max_left _ _)
  choose C D hC0 hD0 hCb hDb using hex
  refine ⟨∑ k ∈ Finset.range (n + 1), C k, ∑ k ∈ Finset.range (n + 1), D k,
    Finset.sum_nonneg (fun k _ => hC0 k), Finset.sum_nonneg (fun k _ => hD0 k), ?_, ?_⟩
  · intro k hk y hy
    exact le_trans (hCb k y hy)
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  · intro k hk y hy
    exact le_trans (hDb k y hy)
      (Finset.single_le_sum (fun j _ => hD0 j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))

/-- `Lop` costs exactly one order of `ContDiffOn` on an open set. -/
theorem contDiffOn_Lop {u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {n : ℕ}
    (hu : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) u U) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Work.Spaces.Lop u) U := by
  have hcast : (((n : ℕ)) : WithTop ℕ∞) + 1 = (((n + 1 : ℕ)) : WithTop ℕ∞) := by
    push_cast; ring
  have hs : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) U := by
    fun_prop
  have hd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (deriv u) U := by
    refine hu.deriv_of_isOpen hU ?_
    rw [hcast]
  have : Work.Spaces.Lop u = (fun θ : ℝ => Real.sin (2 * θ)) * deriv u := rfl
  rw [this]
  exact hs.mul hd

/-- Iterating `Lop` costs one order per application. -/
theorem contDiffOn_Lop_iter (k : ℕ) {u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) :
    ∀ n : ℕ, ContDiffOn ℝ (((n + k : ℕ)) : WithTop ℕ∞) u U →
      ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) ((Work.Spaces.Lop^[k]) u) U := by
  induction k with
  | zero => intro n hu; simpa using hu
  | succ k ih =>
      intro n hu
      rw [Function.iterate_succ_apply']
      refine contDiffOn_Lop hU ?_
      refine ih (n + 1) ?_
      have hnat : n + 1 + k = n + (k + 1) := by omega
      rw [hnat]
      exact hu

/-- `iteratedDeriv` costs orders of `ContDiffOn` on an open set. -/
theorem contDiffOn_iteratedDeriv {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) :
    ∀ r : ℕ, ∀ n : ℕ, ContDiffOn ℝ (((n + r : ℕ)) : WithTop ℕ∞) g U →
      ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (iteratedDeriv r g) U := by
  intro r
  induction r with
  | zero =>
      intro n hg
      simpa using hg
  | succ r ih =>
      intro n hg
      rw [iteratedDeriv_succ]
      have hnat : (n + 1) + r = n + (r + 1) := by omega
      have hprev : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (iteratedDeriv r g) U :=
        ih (n + 1) (by rw [hnat]; exact hg)
      have hcast : (((n : ℕ)) : WithTop ℕ∞) + 1 = (((n + 1 : ℕ)) : WithTop ℕ∞) := by
        push_cast; ring
      refine hprev.deriv_of_isOpen hU ?_
      rw [hcast]

/-- **Recursion of the `Lop`-iterates.**  On an open set `U` on which `g` is of class
`C^{i+1}`,

`Lop^[i+1] g = ∑_{a ≤ i} C(i,a) · Asf a · Lop^[i-a] (deriv g)`. -/
theorem Lop_iter_succ_eq_sum (i : ℕ) {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) g U) :
    ∀ θ ∈ U, (Work.Spaces.Lop^[i + 1]) g θ
      = ∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (Asf a θ * (Work.Spaces.Lop^[i - a]) (deriv g) θ) := by
  intro θ hθ
  rw [Function.iterate_succ_apply]
  have hlop : Work.Spaces.Lop g = (fun θ' : ℝ => Real.sin (2 * θ')) * deriv g := rfl
  rw [hlop]
  have hs : ContDiffOn ℝ ((i : ℕ) : WithTop ℕ∞) (fun θ' : ℝ => Real.sin (2 * θ')) U := by
    fun_prop
  have hcast : (((i : ℕ)) : WithTop ℕ∞) + 1 = (((i + 1 : ℕ)) : WithTop ℕ∞) := by
    push_cast; ring
  have hdg : ContDiffOn ℝ ((i : ℕ) : WithTop ℕ∞) (deriv g) U := by
    refine hg.deriv_of_isOpen hU ?_
    rw [hcast]
  have h := Work.FTS.EllipticEst.RPFresh.DivSinOpen.Lop_iter_mul_eqOn_fin i i
    (fun θ' : ℝ => Real.sin (2 * θ')) (deriv g) U hU hs hdg le_rfl hθ
  rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show (Work.Spaces.Lop^[a]) (fun θ' : ℝ => Real.sin (2 * θ')) = Asf a from rfl]

end Work.FTS.PhiStar.FlatWAux
