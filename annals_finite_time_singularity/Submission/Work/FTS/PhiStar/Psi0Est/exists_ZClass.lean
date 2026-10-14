import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option maxHeartbeats 1600000

/-! ## 0. Iterates of `dthU`: smoothness, germ-locality and the Leibniz rule -/

/-- `dthU` as a function. -/
lemma dthU_eq_fun (φ : ℝ → ℝ) :
    Work.Spaces.dthU φ = fun θ : ℝ => Real.sin (2 * θ) * deriv φ θ := by
  funext θ
  rw [Work.Spaces.dthU_apply]

/-- The `dthU`-iterates only depend on the germ of the function. -/
lemma dthU_iter_eventuallyEq {f g : ℝ → ℝ} {θ : ℝ} (h : f =ᶠ[𝓝 θ] g) (m : ℕ) :
    Work.Spaces.dthU^[m] f θ = Work.Spaces.dthU^[m] g θ := by
  have hmain : ∀ m : ℕ, Work.Spaces.dthU^[m] f =ᶠ[𝓝 θ] Work.Spaces.dthU^[m] g := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ihm =>
        have hd : deriv (Work.Spaces.dthU^[m] f) =ᶠ[𝓝 θ] deriv (Work.Spaces.dthU^[m] g) :=
          ihm.deriv
        have hm := (Filter.EventuallyEq.refl (𝓝 θ) (fun x : ℝ => Real.sin (2 * x))).mul hd
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          dthU_eq_fun, dthU_eq_fun]
        exact hm
  exact (hmain m).eq_of_nhds

/-- Every `dthU`-iterate of a `C^∞`-function on an open set is `C^∞` there. -/
lemma dthU_iter_contDiffOn {u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ (∞ : ℕ∞ω) u U) (k : ℕ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU^[k] u) U := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hder : ContDiffOn ℝ (∞ : ℕ∞ω) (deriv (Work.Spaces.dthU^[k] u)) U :=
        ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp ih).2
      have hsin : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ)) U := by fun_prop
      exact hsin.mul hder

/-- Linearity of the `dthU`-iterates over a difference. -/
lemma dthU_iter_sub_eqOn {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) (hg : ContDiffOn ℝ (∞ : ℕ∞ω) g U) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[j] (fun x => f x - g x))
      (fun x => Work.Spaces.dthU^[j] f x - Work.Spaces.dthU^[j] g x) U := by
  induction j with
  | zero => intro x _; simp
  | succ j ih =>
      intro x hx
      have hev : (Work.Spaces.dthU^[j] (fun x => f x - g x))
          =ᶠ[𝓝 x] (fun x => Work.Spaces.dthU^[j] f x - Work.Spaces.dthU^[j] g x) :=
        ih.eventuallyEq_of_mem (hU.mem_nhds hx)
      have hder : deriv (Work.Spaces.dthU^[j] (fun x => f x - g x)) x
          = deriv (Work.Spaces.dthU^[j] f - Work.Spaces.dthU^[j] g) x := by
        have h1 := hev.deriv_eq
        have h2 : (fun x : ℝ => Work.Spaces.dthU^[j] f x - Work.Spaces.dthU^[j] g x)
            = (Work.Spaces.dthU^[j] f - Work.Spaces.dthU^[j] g) := rfl
        rw [h2] at h1
        exact h1
      have hdf : DifferentiableAt ℝ (Work.Spaces.dthU^[j] f) x :=
        ((dthU_iter_contDiffOn hU hf j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      have hdg : DifferentiableAt ℝ (Work.Spaces.dthU^[j] g) x :=
        ((dthU_iter_contDiffOn hU hg j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      have hfinal : Work.Spaces.dthU (Work.Spaces.dthU^[j] (fun x => f x - g x)) x
          = Work.Spaces.dthU (Work.Spaces.dthU^[j] f) x
            - Work.Spaces.dthU (Work.Spaces.dthU^[j] g) x := by
        have e1 : Work.Spaces.dthU (Work.Spaces.dthU^[j] (fun x => f x - g x)) x
            = Real.sin (2 * x) * deriv (Work.Spaces.dthU^[j] (fun x => f x - g x)) x := rfl
        have e2 : Work.Spaces.dthU (Work.Spaces.dthU^[j] f) x
            = Real.sin (2 * x) * deriv (Work.Spaces.dthU^[j] f) x := rfl
        have e3 : Work.Spaces.dthU (Work.Spaces.dthU^[j] g) x
            = Real.sin (2 * x) * deriv (Work.Spaces.dthU^[j] g) x := rfl
        rw [e1, e2, e3, hder, deriv_sub hdf hdg]
        ring
      have hL : Work.Spaces.dthU^[j + 1] (fun x => f x - g x)
          = Work.Spaces.dthU (Work.Spaces.dthU^[j] (fun x => f x - g x)) :=
        Function.iterate_succ_apply' Work.Spaces.dthU j (fun x => f x - g x)
      have hR1 : Work.Spaces.dthU^[j + 1] f = Work.Spaces.dthU (Work.Spaces.dthU^[j] f) :=
        Function.iterate_succ_apply' Work.Spaces.dthU j f
      have hR2 : Work.Spaces.dthU^[j + 1] g = Work.Spaces.dthU (Work.Spaces.dthU^[j] g) :=
        Function.iterate_succ_apply' Work.Spaces.dthU j g
      rw [hL, hR1, hR2]
      exact hfinal

/-- Linearity of the `dthU`-iterates over a constant multiple. -/
lemma dthU_iter_const_mul_eqOn {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (c : ℝ)
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f U) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[j] (fun x => c * f x))
      (fun x => c * Work.Spaces.dthU^[j] f x) U := by
  induction j with
  | zero => intro x _; simp
  | succ j ih =>
      intro x hx
      have hev : (Work.Spaces.dthU^[j] (fun x => c * f x))
          =ᶠ[𝓝 x] (fun x => c * Work.Spaces.dthU^[j] f x) :=
        ih.eventuallyEq_of_mem (hU.mem_nhds hx)
      have hder : deriv (Work.Spaces.dthU^[j] (fun x => c * f x)) x
          = deriv (fun x => c * Work.Spaces.dthU^[j] f x) x := hev.deriv_eq
      have hdf : DifferentiableAt ℝ (Work.Spaces.dthU^[j] f) x :=
        ((dthU_iter_contDiffOn hU hf j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      have hfinal : Work.Spaces.dthU (Work.Spaces.dthU^[j] (fun x => c * f x)) x
          = c * Work.Spaces.dthU (Work.Spaces.dthU^[j] f) x := by
        have e1 : Work.Spaces.dthU (Work.Spaces.dthU^[j] (fun x => c * f x)) x
            = Real.sin (2 * x) * deriv (Work.Spaces.dthU^[j] (fun x => c * f x)) x := rfl
        have e2 : Work.Spaces.dthU (Work.Spaces.dthU^[j] f) x
            = Real.sin (2 * x) * deriv (Work.Spaces.dthU^[j] f) x := rfl
        rw [e1, e2, hder, deriv_const_mul c hdf]
        ring
      have hL : Work.Spaces.dthU^[j + 1] (fun x => c * f x)
          = Work.Spaces.dthU (Work.Spaces.dthU^[j] (fun x => c * f x)) :=
        Function.iterate_succ_apply' Work.Spaces.dthU j (fun x => c * f x)
      have hR : Work.Spaces.dthU^[j + 1] f = Work.Spaces.dthU (Work.Spaces.dthU^[j] f) :=
        Function.iterate_succ_apply' Work.Spaces.dthU j f
      rw [hL, hR]
      exact hfinal

/-- The termwise product rule for `dthU`-iterates (the `dthU` form of
`Work.Spaces.sin_deriv_term`). -/
lemma dthU_sin_deriv_term (u v : ℝ → ℝ) (θ : ℝ) (j a : ℕ)
    (ha : DifferentiableAt ℝ (Work.Spaces.dthU^[a] u) θ)
    (hb : DifferentiableAt ℝ (Work.Spaces.dthU^[j - a] v) θ) :
    Real.sin (2 * θ) * deriv (fun θ' => (j.choose a : ℝ)
        * (Work.Spaces.dthU^[a] u θ' * Work.Spaces.dthU^[j - a] v θ')) θ =
      (j.choose a : ℝ) * (Work.Spaces.dthU^[a + 1] u θ * Work.Spaces.dthU^[j - a] v θ
        + Work.Spaces.dthU^[a] u θ * Work.Spaces.dthU^[j - a + 1] v θ) := by
  have hfun2 : (fun θ' => (j.choose a : ℝ)
        * (Work.Spaces.dthU^[a] u θ' * Work.Spaces.dthU^[j - a] v θ'))
      = (fun y => (j.choose a : ℝ)
        * ((Work.Spaces.dthU^[a] u * Work.Spaces.dthU^[j - a] v) y)) := rfl
  rw [hfun2, deriv_const_mul (j.choose a : ℝ) (ha.mul hb), deriv_mul ha hb,
      Function.iterate_succ_apply' Work.Spaces.dthU a u,
      Function.iterate_succ_apply' Work.Spaces.dthU (j - a) v,
      show Work.Spaces.dthU (Work.Spaces.dthU^[a] u) θ
        = Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[a] u) θ from rfl,
      show Work.Spaces.dthU (Work.Spaces.dthU^[j - a] v) θ
        = Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[j - a] v) θ from rfl]
  ring

/-- The iterated Leibniz rule for `dthU` on an open set, with `C^∞` hypotheses. -/
lemma dthU_iter_mul_eqOn {u v : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ (∞ : ℕ∞ω) u U) (hv : ContDiffOn ℝ (∞ : ℕ∞ω) v U) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[j] (u * v))
      (fun θ => ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℕ) : ℝ) *
        (Work.Spaces.dthU^[a] u θ * Work.Spaces.dthU^[j - a] v θ)) U := by
  induction j with
  | zero =>
      intro θ _
      simp
  | succ j ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      have hFa : ∀ a, ContDiffAt ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU^[a] u) θ :=
        fun a => (dthU_iter_contDiffOn hU hu a).contDiffAt (hU.mem_nhds hθ)
      have hGb : ∀ b, ContDiffAt ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU^[b] v) θ :=
        fun b => (dthU_iter_contDiffOn hU hv b).contDiffAt (hU.mem_nhds hθ)
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => ((j.choose a : ℕ) : ℝ)
            * (Work.Spaces.dthU^[a] u θ' * Work.Spaces.dthU^[j - a] v θ')) θ := by
        intro a _
        exact (((hFa a).differentiableAt (by simp)).mul
          ((hGb (j - a)).differentiableAt (by simp))).const_mul _
      have hfun : (fun θ' => ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℕ) : ℝ)
            * (Work.Spaces.dthU^[a] u θ' * Work.Spaces.dthU^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => ((j.choose a : ℕ) : ℝ)
              * (Work.Spaces.dthU^[a] u θ' * Work.Spaces.dthU^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hderiv : deriv (Work.Spaces.dthU^[j] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℕ) : ℝ)
              * (Work.Spaces.dthU^[a] u θ' * Work.Spaces.dthU^[j - a] v θ')) θ :=
        (ih.deriv hU) hθ
      have hkey : Work.Spaces.dthU (Work.Spaces.dthU^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => ((j.choose a : ℕ) : ℝ)
                * (Work.Spaces.dthU^[a] u θ' * Work.Spaces.dthU^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => ((j.choose a : ℕ) : ℝ)
                * (Work.Spaces.dthU^[a] u θ' * Work.Spaces.dthU^[j - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      rw [Finset.sum_congr rfl
        (fun a _ => dthU_sin_deriv_term u v θ j a
          ((hFa a).differentiableAt (by simp)) ((hGb (j - a)).differentiableAt (by simp)))]
      exact Work.Spaces.leibniz_step j (fun b => Work.Spaces.dthU^[b] u θ)
        (fun b => Work.Spaces.dthU^[b] v θ)

/-! ## 1. The identity `D_θ P = 6 sin²θ P − sin²θ Γ̄` and the recursion -/

/-- **The key identity**: on `(0,π/2)`, `D_θ P = 6 sin²θ · P − sin²θ · Γ̄`.
It is the exact cancellation that produces the factor `α` in the class bounds. -/
theorem dthU_Pfun_eq (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.dthU (Pfun α) θ
      = 6 * Real.sin θ ^ 2 * Pfun α θ
        - Real.sin θ ^ 2 * Work.FTS.VocabO.GamBar α θ := by
  have hCpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hd := hasDerivAt_Pfun α (le_of_lt hα) hθ
  rw [Work.Spaces.dthU_apply, hd.deriv, Real.sin_two_mul]
  field_simp
  ring

/-- Smoothness of `Γ̄` on the open angular interval. -/
lemma contDiffOn_GamBar (α : ℝ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Work.FTS.VocabO.GamBar α) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [show Work.FTS.VocabO.GamBar α
      = fun θ : ℝ => Work.Spaces.Gam α θ / Work.Spaces.c α - (5 / 4) * Real.sin (2 * θ)
      from by funext t; rw [Work.FTS.VocabO.GamBar]]
  exact ((contDiffOn_Gam α).div_const _).sub (by fun_prop)

/-- **The recursion identity.**  The iterated `D_θ` of `6 sin²θ · P − sin²θ · Γ̄` expands by
the binomial rule, with the multiplier `sin²θ` and the source `Γ̄`. -/
theorem dthU_iter_Z1_eqOn (α : ℝ) (hα : 0 < α) (j : ℕ) :
    Set.EqOn
      (Work.Spaces.dthU^[j] (fun θ : ℝ => 6 * Real.sin θ ^ 2 * Pfun α θ
        - Real.sin θ ^ 2 * Work.FTS.VocabO.GamBar α θ))
      (fun θ : ℝ => ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) *
        (6 * (Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ)
            * (Work.Spaces.dthU^[j - i] (Pfun α) θ)
          - (Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ)
            * (Work.Spaces.dthU^[j - i] (Work.FTS.VocabO.GamBar α) θ)))
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hf : ContDiffOn ℝ (∞ : ℕ∞ω) (fun t : ℝ => Real.sin t ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
  have h6 : ContDiffOn ℝ (∞ : ℕ∞ω) (fun t : ℝ => 6 * Real.sin t ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
  have hP : ContDiffOn ℝ (∞ : ℕ∞ω) (Pfun α) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    contDiffOn_Pfun α (le_of_lt hα)
  have hG : ContDiffOn ℝ (∞ : ℕ∞ω) (Work.FTS.VocabO.GamBar α)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := contDiffOn_GamBar α
  intro θ hθ
  have hf1 : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => 6 * Real.sin θ ^ 2 * Pfun α θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h6.mul hP
  have hg1 : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun θ : ℝ => Real.sin θ ^ 2 * Work.FTS.VocabO.GamBar α θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hf.mul hG
  rw [dthU_iter_sub_eqOn hU hf1 hg1 j hθ]
  beta_reduce
  have hA : Work.Spaces.dthU^[j] (fun θ : ℝ => 6 * Real.sin θ ^ 2 * Pfun α θ) θ
      = ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℕ) : ℝ) *
        (Work.Spaces.dthU^[a] (fun t : ℝ => 6 * Real.sin t ^ 2) θ
          * Work.Spaces.dthU^[j - a] (Pfun α) θ) :=
    dthU_iter_mul_eqOn hU h6 hP j hθ
  have hB : Work.Spaces.dthU^[j]
        (fun θ : ℝ => Real.sin θ ^ 2 * Work.FTS.VocabO.GamBar α θ) θ
      = ∑ a ∈ Finset.range (j + 1), ((j.choose a : ℕ) : ℝ) *
        (Work.Spaces.dthU^[a] (fun t : ℝ => Real.sin t ^ 2) θ
          * Work.Spaces.dthU^[j - a] (Work.FTS.VocabO.GamBar α) θ) :=
    dthU_iter_mul_eqOn hU hf hG j hθ
  rw [hA, hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dthU_iter_const_mul_eqOn hU 6 hf i hθ]
  ring

/-! ## 2. The base estimate for `Z₁ = D_θ P` -/

/-- Crude bound on `(0, π/4]`: only the `sin 2θ` term is used. -/
lemma dthU_Pfun_le_crude (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi / 4) :
    |Work.Spaces.dthU (Pfun α) θ| ≤ 200 * Real.sin (2 * θ) := by
  have hpi : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, by linarith [hθ1, hpi]⟩
  have hθI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ0, le_of_lt hθ.2⟩
  rw [dthU_Pfun_eq α hα hθ]
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθI.1, by linarith [Real.pi_pos]⟩
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθI.2⟩
  have hP : |Pfun α θ| ≤ 20 := Pfun_abs_le α hα hα1 hθI
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα (by linarith)).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hG : |Work.FTS.VocabO.GamBar α θ| ≤ 45 / 4 := by
    have h2 := abs_GamBar_le α θ hα (by linarith) hθI
    have h3 : 1 / Work.Spaces.c α ≤ 10 := by rw [div_le_iff₀ hcpos]; linarith
    linarith
  have hkey : |6 * Pfun α θ - Work.FTS.VocabO.GamBar α θ| ≤ 132 := by
    have h1 : |6 * Pfun α θ - Work.FTS.VocabO.GamBar α θ|
        ≤ |6 * Pfun α θ| + |Work.FTS.VocabO.GamBar α θ| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (6 * Pfun α θ) (-(Work.FTS.VocabO.GamBar α θ))
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] at h1
    linarith
  have habs : |6 * Real.sin θ ^ 2 * Pfun α θ
      - Real.sin θ ^ 2 * Work.FTS.VocabO.GamBar α θ| ≤ 132 * Real.sin θ ^ 2 := by
    rw [show 6 * Real.sin θ ^ 2 * Pfun α θ
        - Real.sin θ ^ 2 * Work.FTS.VocabO.GamBar α θ
        = Real.sin θ ^ 2 * (6 * Pfun α θ - Work.FTS.VocabO.GamBar α θ) from by ring,
      abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
    calc Real.sin θ ^ 2 * |6 * Pfun α θ - Work.FTS.VocabO.GamBar α θ|
        ≤ Real.sin θ ^ 2 * 132 := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
      _ = 132 * Real.sin θ ^ 2 := by ring
  refine le_trans habs ?_
  have hsinlecos : Real.sin θ ≤ Real.cos θ := by
    have h1 : Real.sin θ ≤ Real.sin (Real.pi / 4) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ) (y := Real.pi / 4)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hθ1
    have h2 : Real.cos (Real.pi / 4) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 4)
        (le_of_lt hθ0) (by linarith [Real.pi_pos]) hθ1
    rw [Real.sin_pi_div_four] at h1
    rw [Real.cos_pi_div_four] at h2
    linarith
  rw [Real.sin_two_mul]
  nlinarith [hsinlecos, hsin0, hcos0, sq_nonneg (Real.sin θ)]

/-- Sharp bound on `(π/4, π/2)`: here the `α`-term is essential. -/
lemma dthU_Pfun_le_sharp (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    |Work.Spaces.dthU (Pfun α) θ| ≤ 40 * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
      + 200 * Real.sin (2 * θ) := by
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hCpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩
  have hc10 : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα (by linarith)).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcinv : 1 / Work.Spaces.c α ≤ 10 := by rw [div_le_iff₀ hcpos]; linarith
  have hH1 := H1_bound (α := α) (θ := θ) hα hα1 hθ
  have hH2 := H2_bound (θ := θ) hθ
  rw [← PsiS_eq_integral θ (le_of_lt hθ.2)] at hH2
  have hdec : 6 * Pfun α θ - Work.FTS.VocabO.GamBar α θ
      = (1 / Work.Spaces.c α) * (3 * (∫ t in θ..(Real.pi / 2),
            Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) / Real.cos θ ^ 3
          - Work.Spaces.Gam α θ)
        + ((5 / 4) * Real.sin (2 * θ)
          - 15 * PsiS θ / (2 * Real.cos θ ^ 3)) := by
    rw [Pfun, Work.FTS.VocabO.GamBar,
      Gzero_eq α θ (le_of_lt hα) (le_of_lt hθ'.1) (le_of_lt hθ'.2), PsiG]
    field_simp
    ring
  have hb : |6 * Pfun α θ - Work.FTS.VocabO.GamBar α θ|
      ≤ 30 * α * Real.cos θ ^ (2 * α / 3) + 10 * Real.sin (2 * θ) := by
    rw [hdec]
    have hA : |(1 / Work.Spaces.c α) * (3 * (∫ t in θ..(Real.pi / 2),
          Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) / Real.cos θ ^ 3
        - Work.Spaces.Gam α θ)|
        ≤ (1 / Work.Spaces.c α) * (3 * α * Real.cos θ ^ (2 * α / 3)) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Work.Spaces.c α)]
      exact mul_le_mul_of_nonneg_left hH1 (by positivity)
    have hB : |(5 / 4) * Real.sin (2 * θ) - 15 * PsiS θ / (2 * Real.cos θ ^ 3)|
        ≤ 10 * Real.sin (2 * θ) := hH2
    calc |(1 / Work.Spaces.c α) * (3 * (∫ t in θ..(Real.pi / 2),
            Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) / Real.cos θ ^ 3
          - Work.Spaces.Gam α θ)
        + ((5 / 4) * Real.sin (2 * θ) - 15 * PsiS θ / (2 * Real.cos θ ^ 3))|
        ≤ |(1 / Work.Spaces.c α) * (3 * (∫ t in θ..(Real.pi / 2),
            Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) / Real.cos θ ^ 3
          - Work.Spaces.Gam α θ)|
          + |(5 / 4) * Real.sin (2 * θ) - 15 * PsiS θ / (2 * Real.cos θ ^ 3)| :=
          abs_add_le _ _
      _ ≤ (1 / Work.Spaces.c α) * (3 * α * Real.cos θ ^ (2 * α / 3))
          + 10 * Real.sin (2 * θ) := by linarith
      _ ≤ 30 * α * Real.cos θ ^ (2 * α / 3) + 10 * Real.sin (2 * θ) := by
          have h := mul_le_mul_of_nonneg_right hcinv
            (by positivity : (0 : ℝ) ≤ 3 * α * Real.cos θ ^ (2 * α / 3))
          linarith
  rw [dthU_Pfun_eq α hα hθ']
  have hfac : 6 * Real.sin θ ^ 2 * Pfun α θ
      - Real.sin θ ^ 2 * Work.FTS.VocabO.GamBar α θ
      = Real.sin θ ^ 2 * (6 * Pfun α θ - Work.FTS.VocabO.GamBar α θ) := by ring
  rw [hfac, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hS2 : Real.sin θ ^ 2 ≤ 1 := by
    have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    nlinarith [abs_nonneg (Real.sin θ), sq_abs (Real.sin θ), h1]
  have hS2nn : (0 : ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hCosnn : (0 : ℝ) ≤ Real.cos θ ^ (2 * α / 3) :=
    Real.rpow_nonneg (le_of_lt hCpos) _
  have hSin : (0 : ℝ) ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ'.1], by linarith [hθ'.2, Real.pi_pos]⟩
  have hpos : (0 : ℝ) ≤ α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)) :=
    mul_nonneg (le_of_lt hα) (mul_nonneg hS2nn hCosnn)
  refine le_trans (mul_le_mul_of_nonneg_left hb hS2nn) ?_
  nlinarith [hS2, hSin, hCosnn, hS2nn, hpos, sq_nonneg (Real.sin θ)]

/-- **Base estimate.** `|D_θ P| ≤ 40 α sin²θ cos^{2α/3}θ + 200 sin 2θ`. -/
theorem Z1_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.Spaces.dthU (Pfun α) θ| ≤ 40 * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
      + 200 * Real.sin (2 * θ) := by
  rcases le_or_gt θ (Real.pi / 4) with hle | hgt
  · refine le_trans (dthU_Pfun_le_crude α hα hα1 hθ.1 hle) ?_
    have hcos0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩
    have hnn : 0 ≤ 40 * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hα))
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hcos0 _))
    linarith
  · exact dthU_Pfun_le_sharp α hα hα1 ⟨hgt, hθ.2⟩

/-! ## 3. The triangular recursion defining the coefficients -/

/-- `recseq b q x1 n` is the sequence `x_1, …, x_{n+1}` of coefficients obtained from the
recursion `x_m = Σ_{i<m-1} C(m-1,i)(6 b_i x_{m-1-i} + b_i q_{m-1-i}) + b_{m-1} x_1`. -/
noncomputable def recseq (b q : ℕ → ℝ) (x1 : ℝ) : ℕ → (ℕ → ℝ)
  | 0 => fun m => if m = 1 then x1 else 0
  | (n + 1) => fun m =>
      if m = n + 2 then
        (∑ i ∈ Finset.range (n + 1), (((n + 1).choose i : ℕ) : ℝ) *
            (6 * b i * (recseq b q x1 n) (n + 1 - i) + b i * q (n + 1 - i))) + b (n + 1) * x1
      else (recseq b q x1 n) m

/-- The value `x_m` of the recursion above. -/
noncomputable def recval (b q : ℕ → ℝ) (x1 : ℝ) (m : ℕ) : ℝ := recseq b q x1 (m - 1) m

lemma recseq_stable (b q : ℕ → ℝ) (x1 : ℝ) {n j : ℕ} (hj : j ≤ n + 1) :
    recseq b q x1 (n + 1) j = recseq b q x1 n j := by
  rw [recseq]
  beta_reduce
  rw [if_neg (by omega : ¬ j = n + 2)]

lemma recseq_eq_recval (b q : ℕ → ℝ) (x1 : ℝ) {n j : ℕ} (hj : j ≤ n + 1) :
    recseq b q x1 n j = recval b q x1 j := by
  have h : ∀ n : ℕ, j - 1 ≤ n → recseq b q x1 n j = recseq b q x1 (j - 1) j := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
        rw [recseq_stable b q x1 (by omega : j ≤ n + 1)]
        exact ih
  exact h n (by omega)

lemma recval_one (b q : ℕ → ℝ) (x1 : ℝ) : recval b q x1 1 = x1 := by
  rw [recval]
  norm_num
  rw [recseq]
  beta_reduce
  rw [if_pos rfl]

lemma recval_rec (b q : ℕ → ℝ) (x1 : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    recval b q x1 m = (∑ i ∈ Finset.range (m - 1), (((m - 1).choose i : ℕ) : ℝ) *
        (6 * b i * recval b q x1 (m - 1 - i) + b i * q (m - 1 - i))) + b (m - 1) * x1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have h1 : n + 2 - 1 = n + 1 := by omega
  show recseq b q x1 (n + 2 - 1) (n + 2) = _
  rw [h1]
  rw [recseq]
  beta_reduce
  rw [if_pos rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [recseq_eq_recval b q x1 (n := n) (j := n + 1 - i)
    (by have := Finset.mem_range.mp hi; omega)]

lemma recval_nonneg (b q : ℕ → ℝ) (x1 : ℝ) (hb : ∀ i, 0 ≤ b i) (hq : ∀ i, 0 ≤ q i)
    (hx1 : 0 ≤ x1) : ∀ m, 0 ≤ recval b q x1 m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 2 with hm | hm
    · interval_cases m
      · rw [recval]
        norm_num
        rw [recseq]
        beta_reduce
        rw [if_neg (by norm_num : ¬ (0 : ℕ) = 1)]
      · rw [recval_one]; exact hx1
    · rw [recval_rec b q x1 hm]
      refine add_nonneg ?_ (mul_nonneg (hb _) hx1)
      apply Finset.sum_nonneg
      intro i hi
      refine mul_nonneg (Nat.cast_nonneg _) (add_nonneg ?_ ?_)
      · exact mul_nonneg (mul_nonneg (by norm_num) (hb i)) (ih (m - 1 - i) (by omega))
      · exact mul_nonneg (hb i) (hq _)

/-! ## 4. The pointwise combination bound for one summand -/

/-- One summand of the recursion, bounded in terms of the class coefficients. -/
lemma six_mul_sub_le {α θ a z h B K L CC DD : ℝ}
    (hα : 0 ≤ α) (hS : Real.sin θ ^ 2 ≤ 1)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L) (hCC : 0 ≤ CC) (hDD : 0 ≤ DD)
    (hSin : 0 ≤ Real.sin (2 * θ)) (hCos : 0 ≤ Real.cos θ ^ (2 * α / 3))
    (hGam0 : 0 ≤ Work.Spaces.Gam α θ)
    (hGam : Work.Spaces.Gam α θ ≤ Real.cos θ ^ (2 * α / 3))
    (ha : |a| ≤ B * Real.sin θ ^ 2)
    (hz : |z| ≤ K * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)) + L * Real.sin (2 * θ))
    (hh : |h| ≤ CC * α * Work.Spaces.Gam α θ + DD * Real.sin (2 * θ)) :
    |6 * a * z - a * h|
      ≤ (6 * B * K + B * CC) * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
        + (6 * B * L + B * DD) * Real.sin (2 * θ) := by
  set S2 := Real.sin θ ^ 2 with hS2def
  set Cos := Real.cos θ ^ (2 * α / 3) with hCosdef
  set Sin := Real.sin (2 * θ) with hSindef
  set G := Work.Spaces.Gam α θ with hGdef
  have hS0 : 0 ≤ S2 := by rw [hS2def]; exact sq_nonneg _
  have hS1 : S2 ≤ 1 := by rw [hS2def]; exact hS
  have ha' : |a| ≤ B * S2 := by rw [hS2def]; exact ha
  have hz' : |z| ≤ K * α * (S2 * Cos) + L * Sin := by
    rw [hS2def, hCosdef, hSindef]; exact hz
  have hh' : |h| ≤ CC * α * G + DD * Sin := by rw [hGdef, hSindef]; exact hh
  have hGam' : G ≤ Cos := by rw [hGdef, hCosdef]; exact hGam
  have hG0 : 0 ≤ G := by rw [hGdef]; exact hGam0
  have hstep1 : |6 * a * z - a * h| = |a| * |6 * z - h| := by
    rw [show 6 * a * z - a * h = a * (6 * z - h) from by ring, abs_mul]
  rw [hstep1]
  have h2 : |6 * z - h| ≤ 6 * |z| + |h| := by
    have h := abs_add_le (6 * z) (-h)
    rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] at h
    simpa only [sub_eq_add_neg, abs_neg] using h
  have h3 : |a| * (6 * |z| + |h|)
      ≤ (B * S2) * (6 * (K * α * (S2 * Cos) + L * Sin) + (CC * α * G + DD * Sin)) := by
    refine mul_le_mul ha' ?_ (by positivity) (by positivity)
    linarith
  have h4 : |a| * |6 * z - h| ≤ |a| * (6 * |z| + |h|) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
  refine le_trans h4 (le_trans h3 ?_)
  have hbm : (0 : ℝ) ≤ 6 * B * K * α :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) hK) hα
  have hbl : (0 : ℝ) ≤ 6 * B * L := mul_nonneg (mul_nonneg (by norm_num) hB) hL
  have hbc : (0 : ℝ) ≤ B * CC * α := mul_nonneg (mul_nonneg hB hCC) hα
  have hbd : (0 : ℝ) ≤ B * DD := mul_nonneg hB hDD
  have hA : S2 * (S2 * Cos) ≤ S2 * Cos := by
    have h := mul_le_mul_of_nonneg_right hS1 (mul_nonneg hS0 hCos)
    linarith
  have hB2 : S2 * Sin ≤ Sin := by
    have h := mul_le_mul_of_nonneg_right hS1 hSin
    linarith
  have hC2 : S2 * G ≤ S2 * Cos := by
    have h := mul_le_mul_of_nonneg_left hGam' hS0
    linarith
  have e1 := mul_le_mul_of_nonneg_left hA hbm
  have e2 := mul_le_mul_of_nonneg_left hB2 hbl
  have e3 := mul_le_mul_of_nonneg_left hC2 hbc
  have e4 := mul_le_mul_of_nonneg_left hB2 hbd
  nlinarith [e1, e2, e3, e4]

/-! ## 5. The recursion and the induction -/

/-- **The induction.**  Given the base estimate, the class bound on the multipliers
(`ElemClass`) and on the source (`HClass`), the recursively defined `κ`, `ℓ` satisfy the
class bounds for `1 ≤ m ≤ 5`. -/
theorem Z_bound_induct (b cc dd : ℕ → ℝ) (hb0 : ∀ i, 0 ≤ b i) (hcc0 : ∀ i, 0 ≤ cc i)
    (hdd0 : ∀ i, 0 ≤ dd i)
    (hbSin : ∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ| ≤ b i * Real.sin θ ^ 2)
    (hGamBar : ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j : ℕ, 1 ≤ j → j ≤ 5 →
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ|
          ≤ cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ)) :
    ∀ m : ℕ, 1 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 / 4 →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.dthU^[m] (Pfun α) θ|
        ≤ recval b cc 40 m * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
          + recval b dd 200 m * Real.sin (2 * θ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm1 hm5 α hα hα1 θ hθ
    rcases eq_or_lt_of_le hm1 with h1 | hm2
    · subst h1
      simpa only [recval_one, Function.iterate_one] using Z1_bound α hα hα1 hθ
    · -- the recursion step
      have hS2 : Real.sin θ ^ 2 ≤ 1 := by
        have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
        nlinarith [abs_nonneg (Real.sin θ), sq_abs (Real.sin θ), h1]
      have hS2pos : 0 < Real.sin θ ^ 2 := by
        have h := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
        positivity
      have hcos0 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
          by linarith [hθ.2, Real.pi_pos]⟩
      have hCos0 : 0 ≤ Real.cos θ ^ (2 * α / 3) := Real.rpow_nonneg hcos0 _
      have hSin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      have hGam0 : 0 ≤ Work.Spaces.Gam α θ :=
        Real.rpow_nonneg (mul_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩) (sq_nonneg _)) _
      have hGamle : Work.Spaces.Gam α θ ≤ Real.cos θ ^ (2 * α / 3) := Gam_le_cos_rpow hα hθ
      -- identify `dthU^[m] (Pfun α)` with the iterate applied to `Z₁`
      have hcongr : Work.Spaces.dthU^[m] (Pfun α) θ
          = Work.Spaces.dthU^[m - 1] (fun θ' : ℝ => 6 * Real.sin θ' ^ 2 * Pfun α θ'
              - Real.sin θ' ^ 2 * Work.FTS.VocabO.GamBar α θ') θ := by
        have hmm : m = (m - 1) + 1 := by omega
        rw [hmm, Function.iterate_succ_apply]
        exact dthU_iter_eventuallyEq
          (Set.EqOn.eventuallyEq_of_mem (fun x hx => dthU_Pfun_eq α hα hx)
            (isOpen_Ioo.mem_nhds hθ)) (m - 1)
      -- the recursion identity
      have hmain : Work.Spaces.dthU^[m] (Pfun α) θ
          = ∑ i ∈ Finset.range m, (((m - 1).choose i : ℕ) : ℝ) *
              (6 * (Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ)
                  * (Work.Spaces.dthU^[m - 1 - i] (Pfun α) θ)
                - (Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ)
                  * (Work.Spaces.dthU^[m - 1 - i] (Work.FTS.VocabO.GamBar α) θ)) := by
        have hmr : (Finset.range m : Finset ℕ) = Finset.range (m - 1 + 1) := by
          congr 1
          omega
        rw [hcongr, hmr]
        exact dthU_iter_Z1_eqOn α hα (m - 1) hθ
      rw [hmain]
      -- bound the sum term by term
      have hterm : ∀ i ∈ Finset.range (m - 1),
          |(((m - 1).choose i : ℕ) : ℝ) *
              (6 * (Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ)
                  * (Work.Spaces.dthU^[m - 1 - i] (Pfun α) θ)
                - (Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ)
                  * (Work.Spaces.dthU^[m - 1 - i] (Work.FTS.VocabO.GamBar α) θ))|
          ≤ (((m - 1).choose i : ℕ) : ℝ) *
              ((6 * b i * recval b cc 40 (m - 1 - i) + b i * cc (m - 1 - i)) * α
                  * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
                + (6 * b i * recval b dd 200 (m - 1 - i) + b i * dd (m - 1 - i))
                  * Real.sin (2 * θ)) := by
        intro i hi
        have hj1 : 1 ≤ m - 1 - i := by have := Finset.mem_range.mp hi; omega
        have hj5 : m - 1 - i ≤ 5 := by have := Finset.mem_range.mp hi; omega
        have hj7 : i ≤ 7 := by have := Finset.mem_range.mp hi; omega
        have hIH := ih (m - 1 - i) (by have := Finset.mem_range.mp hi; omega) hj1 hj5
          α hα hα1 θ hθ
        have hmult := hbSin i hj7 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        have hsrc := hGamBar α hα hα1 (m - 1 - i) hj1 hj5 θ hθ
        have hK0 : 0 ≤ recval b cc 40 (m - 1 - i) :=
          recval_nonneg b cc 40 hb0 hcc0 (by norm_num) _
        have hL0 : 0 ≤ recval b dd 200 (m - 1 - i) :=
          recval_nonneg b dd 200 hb0 hdd0 (by norm_num) _
        have hcase := six_mul_sub_le (α := α) (θ := θ)
          (a := Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ)
          (z := Work.Spaces.dthU^[m - 1 - i] (Pfun α) θ)
          (h := Work.Spaces.dthU^[m - 1 - i] (Work.FTS.VocabO.GamBar α) θ)
          (B := b i) (K := recval b cc 40 (m - 1 - i)) (L := recval b dd 200 (m - 1 - i))
          (CC := cc (m - 1 - i)) (DD := dd (m - 1 - i))
          (le_of_lt hα) hS2 (hb0 i) hK0 hL0 (hcc0 _) (hdd0 _) hSin hCos0
          hGam0 hGamle hmult hIH hsrc
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg ((m - 1).choose i))]
        exact mul_le_mul_of_nonneg_left hcase (Nat.cast_nonneg _)
      -- the last summand
      have hlast : |(((m - 1).choose (m - 1) : ℕ) : ℝ) *
              (6 * (Work.Spaces.dthU^[m - 1] (fun t : ℝ => Real.sin t ^ 2) θ)
                  * (Work.Spaces.dthU^[m - 1 - (m - 1)] (Pfun α) θ)
                - (Work.Spaces.dthU^[m - 1] (fun t : ℝ => Real.sin t ^ 2) θ)
                  * (Work.Spaces.dthU^[m - 1 - (m - 1)] (Work.FTS.VocabO.GamBar α) θ))|
          ≤ b (m - 1) * (40 * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
              + 200 * Real.sin (2 * θ)) := by
        have h0 : m - 1 - (m - 1) = 0 := by omega
        rw [h0]
        simp only [Function.iterate_zero_apply, id_eq, Nat.choose_self, Nat.cast_one, one_mul]
        have hmult := hbSin (m - 1) (by omega) θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        have hZ1 := Z1_bound α hα hα1 hθ
        have hid : 6 * Pfun α θ - Work.FTS.VocabO.GamBar α θ
            = Work.Spaces.dthU (Pfun α) θ / Real.sin θ ^ 2 := by
          rw [dthU_Pfun_eq α hα hθ, eq_div_iff (ne_of_gt hS2pos)]
          ring
        rw [show 6 * (Work.Spaces.dthU^[m - 1] (fun t : ℝ => Real.sin t ^ 2) θ)
              * Pfun α θ
              - (Work.Spaces.dthU^[m - 1] (fun t : ℝ => Real.sin t ^ 2) θ)
                * Work.FTS.VocabO.GamBar α θ
              = (Work.Spaces.dthU^[m - 1] (fun t : ℝ => Real.sin t ^ 2) θ)
                * (6 * Pfun α θ - Work.FTS.VocabO.GamBar α θ) from by ring, hid, abs_mul]
        rw [abs_div, abs_of_pos hS2pos, ← mul_div_assoc]
        have h1 : |Work.Spaces.dthU^[m - 1] (fun t : ℝ => Real.sin t ^ 2) θ|
            ≤ b (m - 1) * Real.sin θ ^ 2 := hmult
        calc |Work.Spaces.dthU^[m - 1] (fun t : ℝ => Real.sin t ^ 2) θ|
              * |Work.Spaces.dthU (Pfun α) θ| / Real.sin θ ^ 2
            ≤ (b (m - 1) * Real.sin θ ^ 2)
              * (40 * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
                  + 200 * Real.sin (2 * θ)) / Real.sin θ ^ 2 := by
              exact div_le_div_of_nonneg_right (mul_le_mul h1 hZ1 (abs_nonneg _)
                (mul_nonneg (hb0 _) (sq_nonneg _))) (le_of_lt hS2pos)
          _ = b (m - 1) * (40 * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3))
                  + 200 * Real.sin (2 * θ)) := by
              rw [div_eq_iff (ne_of_gt hS2pos)]
              ring_nf
      -- assemble
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hr : (Finset.range m : Finset ℕ) = Finset.range ((m - 1) + 1) := by
        congr 1
        omega
      rw [hr, Finset.sum_range_succ]
      refine le_trans (add_le_add (Finset.sum_le_sum hterm) hlast) ?_
      rw [recval_rec b cc 40 hm2, recval_rec b dd 200 hm2]
      set Xf : ℝ := Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3) with hXf
      set Yf : ℝ := Real.sin (2 * θ) with hYf
      have hsum : (∑ i ∈ Finset.range (m - 1), (((m - 1).choose i : ℕ) : ℝ) *
              ((6 * b i * recval b cc 40 (m - 1 - i) + b i * cc (m - 1 - i)) * α * Xf
                + (6 * b i * recval b dd 200 (m - 1 - i) + b i * dd (m - 1 - i)) * Yf))
          = (∑ i ∈ Finset.range (m - 1), (((m - 1).choose i : ℕ) : ℝ) *
              (6 * b i * recval b cc 40 (m - 1 - i) + b i * cc (m - 1 - i))) * α * Xf
            + (∑ i ∈ Finset.range (m - 1), (((m - 1).choose i : ℕ) : ℝ) *
              (6 * b i * recval b dd 200 (m - 1 - i) + b i * dd (m - 1 - i))) * Yf := by
        have hstep : ∀ i ∈ Finset.range (m - 1),
            (((m - 1).choose i : ℕ) : ℝ)
                * ((6 * b i * recval b cc 40 (m - 1 - i) + b i * cc (m - 1 - i)) * α * Xf
                  + (6 * b i * recval b dd 200 (m - 1 - i) + b i * dd (m - 1 - i)) * Yf)
              = (((m - 1).choose i : ℕ) : ℝ)
                  * (6 * b i * recval b cc 40 (m - 1 - i) + b i * cc (m - 1 - i)) * α * Xf
                + (((m - 1).choose i : ℕ) : ℝ)
                  * (6 * b i * recval b dd 200 (m - 1 - i) + b i * dd (m - 1 - i)) * Yf :=
          fun i _ => by ring
        rw [Finset.sum_congr rfl hstep]
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      rw [hsum]
      set A : ℝ := ∑ i ∈ Finset.range (m - 1), (((m - 1).choose i : ℕ) : ℝ) *
        (6 * b i * recval b cc 40 (m - 1 - i) + b i * cc (m - 1 - i)) with hA
      set B : ℝ := ∑ i ∈ Finset.range (m - 1), (((m - 1).choose i : ℕ) : ℝ) *
        (6 * b i * recval b dd 200 (m - 1 - i) + b i * dd (m - 1 - i)) with hB
      have hfin : A * α * Xf + B * Yf + b (m - 1) * (40 * α * Xf + 200 * Yf)
          = (A + b (m - 1) * 40) * α * Xf + (B + b (m - 1) * 200) * Yf := by ring
      exact le_of_eq hfin

/-! ## 6. The `Z`-class -/

/-- **The `Z`-class exists.**  From the three class hypotheses (the tail bound `IClass`, the
elementary bounds `ElemClass` and the source bounds `HClass`) the coefficients
`κ_j = recval b cc 40 j`, `ℓ_j = recval b dd 200 j` satisfy `ZClass κ ℓ`. -/
theorem exists_ZClass (hI : ∃ K : ℝ, IClass K) (hb : ∃ b : ℕ → ℝ, ElemClass b)
    (hH : ∃ cc dd : ℕ → ℝ, HClass cc dd) : ∃ κ ell : ℕ → ℝ, ZClass κ ell := by
  obtain ⟨b, hb0, hbSin, _hbCos, _hbCos2⟩ := hb
  obtain ⟨cc, dd, hcc0, hdd0, hGamBar⟩ := hH
  refine ⟨recval b cc 40, recval b dd 200, ?_, ?_, ?_⟩
  · exact recval_nonneg b cc 40 hb0 hcc0 (by norm_num)
  · exact recval_nonneg b dd 200 hb0 hdd0 (by norm_num)
  · intro α hα hα1 j hj1 hj5 θ hθ
    exact Z_bound_induct b cc dd hb0 hcc0 hdd0 hbSin hGamBar j hj1 hj5 α hα hα1 θ hθ

end Work.FTS.PhiStar.Psi0Est
