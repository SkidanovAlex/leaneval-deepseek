import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.Cutoff
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.EllipticEst.Core.mixedSliceLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The open quadrant `(0,∞) × (0,π/2)` and the angular function `sin(2θ)`

The hypothesis of the statement uses `Work.Stability.smoothOrder`, the genuine smooth order
`∞ = ((⊤ : ℕ∞) : ℕ∞ω)` (which is *weaker* than the analytic order `⊤ = ω`).  All the auxiliary
lemmas below are therefore stated at order `∞`, which is what `smoothOrder` unfolds to. -/

/-- The open quadrant `(0,∞) × (0,π/2)` on which the hypothesis `hV` of the statement holds. -/
def sliceU : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

lemma isOpen_sliceU : IsOpen sliceU := isOpen_Ioi.prod isOpen_Ioo

/-- The function `θ ↦ sin(2θ)`. -/
def s1 (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- The function `(z,θ) ↦ sin(2θ)`. -/
def s2 : ℝ → ℝ → ℝ := fun _ θ => s1 θ

lemma inf_add_one_le : (∞ : ℕ∞ω) + 1 ≤ ∞ := le_of_eq (by simp)

lemma one_le_inf : (1 : ℕ∞ω) ≤ ∞ := by simp

lemma one_ne_inf : (1 : ℕ∞ω) ≠ ∞ := by simp

/-! ## Auxiliary lemmas -/

/-- `D_z^n` is local: two functions agreeing on the open quadrant have the same `D_z`-iterates. -/
lemma DzIter_congr_sliceU {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → f z θ = g z θ) :
    ∀ n z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.DzIter n f z θ = Work.Spaces.DzIter n g z θ := by
  intro n
  induction n with
  | zero => intro z θ hz hθ; exact h z θ hz hθ
  | succ n ih =>
      intro z θ hz hθ
      show Work.Spaces.Dz (Work.Spaces.DzIter n f) z θ
        = Work.Spaces.Dz (Work.Spaces.DzIter n g) z θ
      have hEv : (fun z' : ℝ => Work.Spaces.DzIter n f z' θ)
          =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds (show z ∈ Set.Ioi (0 : ℝ) from hz)] with z' hz'
        exact ih z' θ hz' hθ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [Filter.EventuallyEq.deriv_eq hEv]

/-! ### Smoothness of the plain `θ`-derivative -/

/-- The joint `C^∞`-regularity of the `θ`-derivative `(z,θ) ↦ ∂_θ f(z,θ)`. -/
lemma contDiffAt_uncurry_pth {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ ∞ (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ ∞ (Function.uncurry (Work.Spaces.pth f)) (z, θ) := by
  have h1 : ContDiffAt ℝ ∞ (fderiv ℝ (Function.uncurry f)) (z, θ) :=
    h.fderiv_right inf_add_one_le
  have h2 : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) p) (0, 1)) (z, θ) :=
    h1.clm_apply contDiffAt_const
  refine h2.congr_of_eventuallyEq ?_
  have hfin : ContDiffAt ℝ (1 : ℕ∞ω) (Function.uncurry f) (z, θ) := h.of_le one_le_inf
  have hev : ∀ᶠ q in 𝓝 (z, θ), DifferentiableAt ℝ (Function.uncurry f) q := by
    filter_upwards [hfin.eventually one_ne_inf] with q hq
    exact hq.differentiableAt (by norm_num)
  filter_upwards [hev] with q hq
  exact Work.Spaces.deriv_slice_snd (Function.uncurry f) q.1 q.2 hq

/-- The joint `C^∞`-regularity of `D_θ f`. -/
lemma contDiffAt_uncurry_Dth {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ ∞ (Function.uncurry g) (z, θ)) :
    ContDiffAt ℝ ∞ (Function.uncurry (Work.Spaces.Dth g)) (z, θ) := by
  have hsin : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) := by fun_prop
  have hp := contDiffAt_uncurry_pth h
  exact hsin.mul hp

/-- The joint `C^∞`-regularity of the iterated plain `θ`-derivatives. -/
lemma contDiffOn_uncurry_pthIter {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ContDiffOn ℝ ∞ (Function.uncurry G) U) (k : ℕ) :
    ContDiffOn ℝ ∞ (Function.uncurry (Work.Spaces.pthIter k G)) U := by
  rw [hU.contDiffOn_iff] at h ⊢
  intro p hp
  induction k with
  | zero => simpa using h hp
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ]
      exact contDiffAt_uncurry_pth ih

/-- The joint `C^∞`-regularity of the iterates of `D_θ`. -/
lemma contDiffOn_uncurry_DthIter {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : ContDiffOn ℝ ∞ (Function.uncurry G) U) (n : ℕ) :
    ContDiffOn ℝ ∞ (Function.uncurry (Work.Spaces.DthIter n G)) U := by
  rw [hU.contDiffOn_iff] at h ⊢
  intro p hp
  induction n with
  | zero => simpa using h hp
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ]
      exact contDiffAt_uncurry_Dth ih

/-- The `θ`-slice of a function `C^∞` on the open quadrant is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_theta_slice {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) sliceU) :
    ContDiffOn ℝ ∞ (fun θ : ℝ => F z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hp : (z, θ) ∈ sliceU := by
    show (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
    exact ⟨hz, hθ⟩
  have h1 : ContDiffAt ℝ ∞ (Function.uncurry F) (z, θ) :=
    hF.contDiffAt (isOpen_sliceU.mem_nhds hp)
  have hlin : ContDiffAt ℝ ∞ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  exact (h1.comp θ hlin).contDiffWithinAt

/-- The `z`-slice of a function `C^∞` on the open quadrant is `C^∞` on `(0,∞)`. -/
lemma contDiffOn_z_slice {F : ℝ → ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) sliceU) :
    ContDiffOn ℝ ∞ (fun z : ℝ => F z θ) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun z : ℝ => (z, θ)) (Set.Ioi 0) := by fun_prop
  have h2 : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0) sliceU := by
    intro z hz
    show (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
    exact ⟨hz, hθ⟩
  exact hF.comp h1 h2

/-! ### The one-dimensional Leibniz rule at order `∞` -/

/-- Iterated `Lop` preserves `C^∞`-regularity at a point. -/
lemma Lop_iter_contDiffAt_inf (u : ℝ → ℝ) (θ : ℝ) (hu : ContDiffAt ℝ ∞ u θ) (j : ℕ) :
    ContDiffAt ℝ ∞ (Work.Spaces.Lop^[j] u) θ := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hsin : ContDiffAt ℝ ∞ (fun θ : ℝ => Real.sin (2 * θ)) θ := by fun_prop
      have hd : ContDiffAt ℝ ∞ (deriv (Work.Spaces.Lop^[j] u)) θ :=
        ContDiffAt.derivWithin (m := ∞) ih inf_add_one_le
      have heq : Work.Spaces.Lop (Work.Spaces.Lop^[j] u)
          = (fun θ : ℝ => Real.sin (2 * θ)) * deriv (Work.Spaces.Lop^[j] u) := rfl
      rw [heq]
      exact hsin.mul hd

/-- The one-dimensional iterated Leibniz rule at order `∞`. -/
lemma Lop_iter_mul_eqOn_inf (u v : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (j : ℕ) :
    Set.EqOn (Work.Spaces.Lop^[j] (u * v))
      (fun θ => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[j - a] v θ)) U := by
  induction j with
  | zero =>
      intro θ hθ
      simp [Function.iterate_zero_apply]
  | succ j ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      have hFa : ∀ a, ContDiffAt ℝ ∞ (Work.Spaces.Lop^[a] u) θ :=
        fun a => Lop_iter_contDiffAt_inf u θ (hu.contDiffAt (hU.mem_nhds hθ)) a
      have hGb : ∀ b, ContDiffAt ℝ ∞ (Work.Spaces.Lop^[b] v) θ :=
        fun b => Lop_iter_contDiffAt_inf v θ (hv.contDiffAt (hU.mem_nhds hθ)) b
      have hmem : ∀ a ∈ Finset.range (j + 1), DifferentiableAt ℝ
          (fun θ' => (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        intro a ha
        exact (((hFa a).differentiableAt (by norm_num)).mul
          ((hGb (j - a)).differentiableAt (by norm_num))).const_mul _
      have hfun : (fun θ' => ∑ a ∈ Finset.range (j + 1),
            (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ'))
          = ∑ a ∈ Finset.range (j + 1),
            (fun θ' => (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hderiv : deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (j + 1),
              (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ :=
        (ih.deriv hU) hθ
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[j] (u * v)) θ
          = ∑ a ∈ Finset.range (j + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (j.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[j - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      rw [Finset.sum_congr rfl
        (fun a _ => Work.Spaces.sin_deriv_term u v θ j a
          ((hFa a).differentiableAt (by norm_num)) ((hGb (j - a)).differentiableAt (by norm_num)))]
      exact Work.Spaces.leibniz_step j (fun b => Work.Spaces.Lop^[b] u θ)
        (fun b => Work.Spaces.Lop^[b] v θ)

/-- The curried Leibniz rule for `D_θ^j` at order `∞`. -/
lemma DthIter_mul_inf (j : ℕ) (f g : ℝ → ℝ → ℝ) (z : ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ (fun θ => f z θ) U) (hg : ContDiffOn ℝ ∞ (fun θ => g z θ) U) :
    ∀ θ ∈ U, Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (j - a) g z θ) := by
  intro θ hθ
  have hmain := Lop_iter_mul_eqOn_inf (fun θ' => f z θ') (fun θ' => g z θ') U hU hf hg j hθ
  have hstep : Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z θ
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * (Work.Spaces.Lop^[a] (fun θ' => f z θ') θ
            * Work.Spaces.Lop^[j - a] (fun θ' => g z θ') θ) := by
    rw [show (fun θ' => f z θ') * (fun θ' => g z θ') = (fun θ' => f z θ' * g z θ') from rfl] at hmain
    exact (congrFun (Work.Spaces.DthIter_eq_iterate_Lop j (fun z θ => f z θ * g z θ) z) θ).trans hmain
  rw [hstep]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Work.Spaces.DthIter_eq_iterate_Lop a f z,
    Work.Spaces.DthIter_eq_iterate_Lop (j - a) g z]

/-! ### The derivation-like structure of `Zop` at order `∞` -/

/-- The function class `C^∞` on `(0,∞)`. -/
abbrev SmoothZ0 (u : ℝ → ℝ) : Prop := ContDiffOn ℝ ∞ u (Set.Ioi 0)

theorem SmoothZ0_FunClass : Work.Spaces.FunClass (X := ℝ) SmoothZ0 where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ ∞ (fun p => c * A p) (Set.Ioi 0)
    exact ContDiffOn.const_smul c hA

/-- The one-dimensional operator `Zop : u ↦ (z ↦ z u'(z))` is derivation-like on `(0,∞)`. -/
theorem Zop_DerivLike0 :
    Work.Spaces.DerivLike (Set.Ioi (0 : ℝ)) SmoothZ0 Work.Spaces.Zop where
  add := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show Work.Spaces.Zop (A + B) z = Work.Spaces.Zop A z + Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show Work.Spaces.Zop (A * B) z = Work.Spaces.Zop A z * B z + A z * Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    intro z hz
    show Work.Spaces.Zop A z = Work.Spaces.Zop B z
    simp only [Work.Spaces.Zop]
    rw [h.deriv isOpen_Ioi hz]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ∞ (fderiv ℝ A) (Set.Ioi 0) :=
      hA.fderiv_of_isOpen isOpen_Ioi inf_add_one_le
    have hev : ContDiffOn ℝ ∞ (fun z : ℝ => (fderiv ℝ A z) 1) (Set.Ioi 0) :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ ∞ (fun z : ℝ => z * (fderiv ℝ A z) 1) (Set.Ioi 0) :=
      contDiff_id.contDiffOn.mul hev
    refine hfun.congr (fun z hz => ?_)
    show Work.Spaces.Zop A z = z * (fderiv ℝ A z) 1
    simp only [Work.Spaces.Zop]
    rw [fderiv_apply_one_eq_deriv]
  smul := fun c A hA => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show Work.Spaces.Zop (fun p => c * A p) z = c * Work.Spaces.Zop A z
    simp only [Work.Spaces.Zop]
    rw [deriv_const_mul c hA']
    ring

/-- `Zop^[n]` is additive over `Finset.range` sums with constant coefficients, near a point
where all the summands are `C^∞` on `(0,∞)`. -/
lemma Zop_iter_sum_range (n N : ℕ) (c : ℕ → ℝ) (K : ℕ → ℝ → ℝ) :
    ∀ z : ℝ, 0 < z → (∀ a ≤ N, ContDiffOn ℝ ∞ (K a) (Set.Ioi 0)) →
      Work.Spaces.Zop^[n] (fun z' : ℝ => ∑ a ∈ Finset.range (N + 1), c a * K a z') z
        = ∑ a ∈ Finset.range (N + 1), c a * Work.Spaces.Zop^[n] (K a) z := by
  intro z hz hK
  have hA : ∀ a ≤ N, SmoothZ0 (fun z' : ℝ => c a * K a z') := fun a ha =>
    ContDiffOn.const_smul (c a) (hK a ha)
  have hsum := Work.Spaces.DerivLike.iterate_sum_range Zop_DerivLike0 SmoothZ0_FunClass n N hA
  have h1 : Work.Spaces.Zop^[n]
      (fun z' : ℝ => ∑ a ∈ Finset.range (N + 1), c a * K a z') z
      = ∑ a ∈ Finset.range (N + 1), Work.Spaces.Zop^[n] (fun z' : ℝ => c a * K a z') z := by
    change Work.Spaces.Zop^[n]
      (fun p : ℝ => ∑ i ∈ Finset.range (N + 1), (fun z' : ℝ => c i * K i z') p) z = _
    exact hsum (by simpa using hz)
  rw [h1]
  apply Finset.sum_congr rfl
  intro a ha
  have haN : a ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hsm := Work.Spaces.DerivLike.iterate_smul Zop_DerivLike0 n (c a) (hK a haN)
  exact hsm (by simpa using hz)

/-! ### Weight comparisons -/

/-- `sin(2θ)² · thGam α θ ≤ thEta θ` on `Iθ` for `0 < α ≤ 1`. -/
lemma sinSq_mul_thGam_le_thEta {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thGam α θ
      ≤ Work.FTS.EllipticEst.thEta θ := by
  have hγ : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · simp only [← hs, Work.FTS.EllipticEst.thGam, Work.FTS.EllipticEst.thEta]
    rw [Real.zero_rpow (by intro hc; linarith),
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    norm_num
  · have hs' : 0 < Real.sin (2 * θ) := hs
    have hle : -(Work.Spaces.eta) ≤ 2 - Work.Spaces.gam α := by
      rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
    have hpos : 0 < 2 - Work.Spaces.gam α := by
      rw [Work.Spaces.gam]; linarith
    simp only [Work.FTS.EllipticEst.thGam, Work.FTS.EllipticEst.thEta]
    rw [← Real.rpow_two, ← Real.rpow_add hs']
    rw [show (2 : ℝ) + -(Work.Spaces.gam α) = 2 - Work.Spaces.gam α from by ring]
    exact Work.FTS.EllipticEst.sin_two_rpow_le_rpow hpos hle hθ

/-- `sin(2θ)² · thGam α θ ≤ thGam α θ` on `Iθ`. -/
lemma sinSq_mul_thGam_le_thGam {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thGam α θ
      ≤ Work.FTS.EllipticEst.thGam α θ := by
  have h1 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    have h0 := Work.FTS.EllipticEst.sin_two_nonneg hθ
    have h2 := Work.FTS.EllipticEst.sin_two_le_one θ
    nlinarith
  have h2 : 0 ≤ Work.FTS.EllipticEst.thGam α θ :=
    Work.FTS.EllipticEst.thGam_nonneg hθ
  calc (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thGam α θ
      ≤ 1 * Work.FTS.EllipticEst.thGam α θ := mul_le_mul_of_nonneg_right h1 h2
    _ = Work.FTS.EllipticEst.thGam α θ := one_mul _


/-! ### The Leibniz expansion of `D_z^{j+1} D_θ^i (∂_θ V)` -/

/-- `D_θ (∂_θ V) = sin(2θ) · ∂_θ²V` as functions. -/
lemma Dth_pth_eq (V : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (Work.Spaces.pth V)
      = fun z θ => s2 z θ * Work.Spaces.pthIter 2 V z θ := by
  funext z θ
  rfl

/-- Leibniz expansion of `D_θ^i (∂_θ V)` in powers of `D_θ`, at an interior point. -/
lemma DthIter_pth_leibniz {V : ℝ → ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU)
    {i : ℕ} (hi : 1 ≤ i) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DthIter i (Work.Spaces.pth V) z θ
      = ∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.LopIter a s1 θ) *
          (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) := by
  have hG : ContDiffOn ℝ ∞ (Function.uncurry (Work.Spaces.pthIter 2 V)) sliceU :=
    contDiffOn_uncurry_pthIter isOpen_sliceU hV 2
  have hs1 : ContDiffOn ℝ ∞ (fun θ' : ℝ => s2 z θ') (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ ∞ (fun θ' : ℝ => s1 θ') (Set.Ioo 0 (Real.pi / 2))
    exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have hslice2 : ContDiffOn ℝ ∞
      (fun θ' : ℝ => Work.Spaces.pthIter 2 V z θ') (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_theta_slice hz hG
  have hiter : Work.Spaces.DthIter i (Work.Spaces.pth V)
      = Work.Spaces.DthIter (i - 1) (Work.Spaces.Dth (Work.Spaces.pth V)) := by
    have h := Work.Spaces.DthIter_add_right (i - 1) 1 (Work.Spaces.pth V)
    rw [show i - 1 + 1 = i from by omega] at h
    exact h.symm
  rw [hiter, Dth_pth_eq V]
  have hkey := DthIter_mul_inf (i - 1) s2 (Work.Spaces.pthIter 2 V) z
    (Set.Ioo 0 (Real.pi / 2)) isOpen_Ioo hs1 hslice2 θ hθ
  rw [hkey]
  rw [show i - 1 + 1 = i from by omega]
  apply Finset.sum_congr rfl
  intro a ha
  rw [show Work.Spaces.DthIter a s2 z θ
      = Work.FTS.EllipticEst.LopIter a s1 θ from by
    rw [Work.Spaces.DthIter_eq_iterate_Lop]
    rfl]
  ring

/-- The Leibniz expansion of `D_z^{j+1} D_θ^i (∂_θ V)`: the `D_z^{j+1}` is moved onto each
term of the expansion of `D_θ^i (∂_θ V) = D_θ^{i-1}(sin(2θ)·∂_θ²V)` in powers of `D_θ`. -/
lemma mixedPth_eq_sum {V : ℝ → ℝ → ℝ} (hV : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU)
    {i : ℕ} (hi : 1 ≤ i) (j : ℕ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ
      = ∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.LopIter a s1 θ) *
          (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) := by
  have hG : ContDiffOn ℝ ∞ (Function.uncurry (Work.Spaces.pthIter 2 V)) sliceU :=
    contDiffOn_uncurry_pthIter isOpen_sliceU hV 2
  have hcongr : ∀ z' θ', 0 < z' → θ' ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.DthIter i (Work.Spaces.pth V) z' θ'
        = (fun z θ => ∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
            (Work.FTS.EllipticEst.LopIter a s1 θ) *
            (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ))) z' θ' :=
    fun z' θ' hz' hθ' => DthIter_pth_leibniz hV hi hz' hθ'
  have hDz := DzIter_congr_sliceU hcongr (j + 1) z θ hz hθ
  have hslice2 : ∀ a ≤ i - 1, ContDiffOn ℝ ∞
      (fun z' : ℝ => Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z' θ)
      (Set.Ioi 0) := fun a _ =>
    contDiffOn_z_slice hθ (contDiffOn_uncurry_DthIter isOpen_sliceU hG (i - 1 - a))
  have hzsum : Work.Spaces.Zop^[j + 1]
      (fun z' : ℝ => ∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
        (Work.FTS.EllipticEst.LopIter a s1 θ) *
        (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z' θ))) z
      = ∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
        (Work.FTS.EllipticEst.LopIter a s1 θ) *
        (Work.Spaces.Zop^[j + 1]
          (fun z' : ℝ => Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z' θ) z)) := by
    have h := Zop_iter_sum_range (j + 1) (i - 1)
      (fun a => ((i - 1).choose a : ℝ) * (Work.FTS.EllipticEst.LopIter a s1 θ))
      (fun a z' => Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z' θ)
      z hz hslice2
    rw [show i - 1 + 1 = i from by omega] at h
    exact h
  calc Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i (Work.Spaces.pth V)) z θ := rfl
    _ = Work.Spaces.DzIter (j + 1) (fun z' θ' => ∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.LopIter a s1 θ') *
          (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z' θ'))) z θ := hDz
    _ = Work.Spaces.Zop^[j + 1]
        (fun z' : ℝ => ∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.LopIter a s1 θ) *
          (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z' θ))) z :=
        congrFun (Work.Spaces.Zop_slice (j + 1)
          (fun z' θ' => ∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
            (Work.FTS.EllipticEst.LopIter a s1 θ') *
            (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z' θ'))) θ) z
    _ = ∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
        (Work.FTS.EllipticEst.LopIter a s1 θ) *
        (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) := by
        rw [hzsum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [show Work.Spaces.Zop^[j + 1]
              (fun z' : ℝ => Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V) z' θ) z
            = Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ from
          (congrFun (Work.Spaces.Zop_slice (j + 1)
            (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 V)) θ) z).symm]

/-- Reindexing `∑_{b ∈ Icc 1 n}` as `∑_{b ∈ range n}` of the shifted summand. -/
lemma sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ b ∈ Finset.Icc 1 n, f b = ∑ b ∈ Finset.range n, f (b + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega) f, ih,
        Finset.sum_range_succ (fun b => f (b + 1)) n]

/-- The pointwise bound. -/
lemma mixedSliceLe_pointwise {k : ℕ} {K : ℝ} (hKpos : 0 ≤ K)
    (hK : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.EllipticEst.LopIter i s1 θ| ≤ K * s1 θ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {V : ℝ → ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU)
    {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ
        ≤ ((i : ℝ) * (4 : ℝ) ^ (i - 1) * K ^ 2)
          * ((∑ b ∈ Finset.Icc 1 (i - 1),
                (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ)
            + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) := by
  intro θ hθ
  have hth : 0 ≤ Work.FTS.EllipticEst.thGam α θ :=
    Work.FTS.EllipticEst.thGam_nonneg hθ
  by_cases hθi : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · -- interior point
    have hmix := mixedPth_eq_sum hV hi j hz hθi
    have hsummand_sq : ∀ a ∈ Finset.range i,
        ((((i - 1).choose a : ℝ) * (Work.FTS.EllipticEst.LopIter a s1 θ) *
            (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) ^ 2
          * Work.FTS.EllipticEst.thGam α θ)
        ≤ ((4 : ℝ) ^ (i - 1) * K ^ 2) *
            ((Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)) := by
      intro a ha
      have ha' : a ≤ i - 1 := by
        have := Finset.mem_range.mp ha
        omega
      have hchoose : (((i - 1).choose a : ℝ)) ^ 2 ≤ (4 : ℝ) ^ (i - 1) := by
        have hbase : ((i - 1).choose a : ℝ) ≤ (2 : ℝ) ^ (i - 1) := by
          have := Nat.choose_le_two_pow (i - 1) a
          exact_mod_cast this
        calc (((i - 1).choose a : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ (i - 1)) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hbase 2
          _ = (4 : ℝ) ^ (i - 1) := by rw [sq, ← mul_pow]; norm_num
      have hs1nn : 0 ≤ s1 θ := by
        simpa only [s1] using Work.FTS.EllipticEst.sin_two_nonneg hθ
      have hL : (Work.FTS.EllipticEst.LopIter a s1 θ) ^ 2 ≤ K ^ 2 * s1 θ ^ 2 := by
        have hb := hK a (by omega) θ hθ
        have h4 : |Work.FTS.EllipticEst.LopIter a s1 θ| ≤ |K * s1 θ| := by
          rw [abs_of_nonneg (mul_nonneg hKpos hs1nn)]
          exact hb
        calc (Work.FTS.EllipticEst.LopIter a s1 θ) ^ 2
            = |Work.FTS.EllipticEst.LopIter a s1 θ| ^ 2 := by rw [sq_abs]
          _ ≤ |K * s1 θ| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h4 2
          _ = K ^ 2 * s1 θ ^ 2 := by
              rw [abs_mul, abs_of_nonneg hKpos, abs_of_nonneg hs1nn]; ring
      have hprod : (((i - 1).choose a : ℝ)) ^ 2 * (Work.FTS.EllipticEst.LopIter a s1 θ) ^ 2
          ≤ ((4 : ℝ) ^ (i - 1) * K ^ 2) * s1 θ ^ 2 := by
        have h1 := mul_le_mul hchoose hL (sq_nonneg _) (by positivity)
        calc (((i - 1).choose a : ℝ)) ^ 2 * (Work.FTS.EllipticEst.LopIter a s1 θ) ^ 2
            ≤ (4 : ℝ) ^ (i - 1) * (K ^ 2 * s1 θ ^ 2) := h1
          _ = ((4 : ℝ) ^ (i - 1) * K ^ 2) * s1 θ ^ 2 := by ring
      have hnn : 0 ≤ (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ := mul_nonneg (sq_nonneg _) hth
      have h3 := mul_le_mul_of_nonneg_right hprod hnn
      calc ((((i - 1).choose a : ℝ) * (Work.FTS.EllipticEst.LopIter a s1 θ) *
              (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) ^ 2
            * Work.FTS.EllipticEst.thGam α θ)
          = ((((i - 1).choose a : ℝ)) ^ 2 * (Work.FTS.EllipticEst.LopIter a s1 θ) ^ 2)
              * ((Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) := by ring
        _ ≤ (((4 : ℝ) ^ (i - 1) * K ^ 2) * s1 θ ^ 2)
              * ((Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) := h3
        _ = ((4 : ℝ) ^ (i - 1) * K ^ 2) *
              ((Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)) := by ring
    have hcs : ((∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.LopIter a s1 θ) *
          (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ))) ^ 2)
        ≤ (i : ℝ) * ∑ a ∈ Finset.range i, ((((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.LopIter a s1 θ) *
          (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) ^ 2) := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range i)
        (f := fun a => (((i - 1).choose a : ℝ) * (Work.FTS.EllipticEst.LopIter a s1 θ) *
          (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)))
      simpa [Finset.card_range] using h
    have hstep1 : (∑ a ∈ Finset.range i, ((((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.LopIter a s1 θ) *
          (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) ^ 2
            * Work.FTS.EllipticEst.thGam α θ))
        ≤ ∑ a ∈ Finset.range i, ((4 : ℝ) ^ (i - 1) * K ^ 2) *
            ((Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)) :=
      Finset.sum_le_sum hsummand_sq
    have hreindex : (∑ a ∈ Finset.range i, ((4 : ℝ) ^ (i - 1) * K ^ 2) *
          ((Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ) ^ 2
            * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)))
        = ((4 : ℝ) ^ (i - 1) * K ^ 2) *
            (∑ b ∈ Finset.range i, (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)) := by
      rw [Finset.mul_sum]
      rw [Finset.sum_range_reflect (fun b => ((4 : ℝ) ^ (i - 1) * K ^ 2) *
        ((Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
          * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ))) i]
    have hsplit : (∑ b ∈ Finset.range i, (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
            * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ))
        = (∑ b ∈ Finset.range (i - 1),
            (Work.Spaces.mixed (j + 1) (b + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ))
          + (Work.Spaces.mixed (j + 1) 0 (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ) := by
      have h := Finset.sum_range_succ'
        (fun b => (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
          * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)) (i - 1)
      rw [show i - 1 + 1 = i from by omega] at h
      exact h
    have hbnd : (∑ b ∈ Finset.range (i - 1),
            (Work.Spaces.mixed (j + 1) (b + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ))
          + (Work.Spaces.mixed (j + 1) 0 (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)
        ≤ (∑ b ∈ Finset.Icc 1 (i - 1),
              (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ)
          + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ := by
      have h1 : (∑ b ∈ Finset.range (i - 1),
            (Work.Spaces.mixed (j + 1) (b + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ))
          ≤ ∑ b ∈ Finset.range (i - 1),
              (Work.Spaces.mixed (j + 1) (b + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ :=
        Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (sinSq_mul_thGam_le_thGam hθ) (sq_nonneg _)
      have h2 : (Work.Spaces.mixed (j + 1) 0 (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)
          ≤ (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ := by
        rw [show Work.Spaces.mixed (j + 1) 0 (Work.Spaces.pthIter 2 V) z θ
            = Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ from rfl]
        exact mul_le_mul_of_nonneg_left (sinSq_mul_thGam_le_thEta hα hα1 hθ) (sq_nonneg _)
      have h3 : (∑ b ∈ Finset.range (i - 1),
              (Work.Spaces.mixed (j + 1) (b + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ)
          = ∑ b ∈ Finset.Icc 1 (i - 1),
              (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ :=
        (sum_Icc_one_eq_sum_range
          (fun b => (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) (i - 1)).symm
      exact add_le_add (h3 ▸ h1) h2
    calc (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ
        = ((∑ a ∈ Finset.range i, (((i - 1).choose a : ℝ) *
            (Work.FTS.EllipticEst.LopIter a s1 θ) *
            (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ))) ^ 2)
            * Work.FTS.EllipticEst.thGam α θ := by rw [hmix]
      _ ≤ ((i : ℝ) * ∑ a ∈ Finset.range i, ((((i - 1).choose a : ℝ) *
            (Work.FTS.EllipticEst.LopIter a s1 θ) *
            (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) ^ 2))
            * Work.FTS.EllipticEst.thGam α θ := mul_le_mul_of_nonneg_right hcs hth
      _ = (i : ℝ) * (∑ a ∈ Finset.range i, ((((i - 1).choose a : ℝ) *
            (Work.FTS.EllipticEst.LopIter a s1 θ) *
            (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) ^ 2
              * Work.FTS.EllipticEst.thGam α θ)) := by
          rw [mul_assoc, Finset.sum_mul]
      _ ≤ (i : ℝ) * (((4 : ℝ) ^ (i - 1) * K ^ 2) *
            ((∑ b ∈ Finset.Icc 1 (i - 1),
                (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ)
              + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (∑ a ∈ Finset.range i, ((((i - 1).choose a : ℝ) *
                (Work.FTS.EllipticEst.LopIter a s1 θ) *
                (Work.Spaces.mixed (j + 1) (i - 1 - a) (Work.Spaces.pthIter 2 V) z θ)) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ))
              ≤ ((4 : ℝ) ^ (i - 1) * K ^ 2) *
                  (∑ b ∈ Finset.range i, (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                    * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)) :=
                hstep1.trans hreindex.le
            _ = ((4 : ℝ) ^ (i - 1) * K ^ 2) *
                  ((∑ b ∈ Finset.range (i - 1),
                      (Work.Spaces.mixed (j + 1) (b + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                        * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ))
                    + (Work.Spaces.mixed (j + 1) 0 (Work.Spaces.pthIter 2 V) z θ) ^ 2
                        * (s1 θ ^ 2 * Work.FTS.EllipticEst.thGam α θ)) := by rw [hsplit]
            _ ≤ ((4 : ℝ) ^ (i - 1) * K ^ 2) *
                  ((∑ b ∈ Finset.Icc 1 (i - 1),
                      (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                        * Work.FTS.EllipticEst.thGam α θ)
                    + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                        * Work.FTS.EllipticEst.thEta θ) :=
                mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ = ((i : ℝ) * (4 : ℝ) ^ (i - 1) * K ^ 2) *
            ((∑ b ∈ Finset.Icc 1 (i - 1),
                (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ)
              + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) := by ring
  · -- angular boundary
    have hsin : Real.sin (2 * θ) = 0 := Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
    have hL : Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ = 0 := by
      show Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i (Work.Spaces.pth V)) z θ = 0
      exact Work.Spaces.DzIter_eq_zero_of_slice_zero
        (fun z' => Work.Spaces.DthIter_eq_zero_of_sin hsin i hi z') (j + 1) z
    have hGam0 : Work.FTS.EllipticEst.thGam α θ = 0 := by
      simp only [Work.FTS.EllipticEst.thGam, hsin]
      exact Real.zero_rpow (by intro hc; linarith [Work.Spaces.one_lt_gam hα])
    have hEta0 : Work.FTS.EllipticEst.thEta θ = 0 := by
      simp only [Work.FTS.EllipticEst.thEta, hsin]
      exact Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)
    have hR : (∑ b ∈ Finset.Icc 1 (i - 1),
            (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * Work.FTS.EllipticEst.thGam α θ)
          + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ = 0 := by
      simp [hGam0, hEta0]
    rw [hR, hL, hGam0]
    simp


end

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.CoercivityFix.PsiMul

open Work.FTS.CoercivityFix.E2Bound

set_option autoImplicit false

/-- The polynomial of the chart: `gpoly Ppsi z = 1/(1+z)`, namely `½(1 - X)`. -/
def Ppsi : Polynomial ℝ := Polynomial.C (1 / 2) * (1 - Polynomial.X)

@[simp] lemma Ppsi_eq : Ppsi = Polynomial.C (1 / 2) * (1 - Polynomial.X) := rfl

/-- The chart-side evaluation of `Ppsi` is `ψ(z) = 1/(1+z)`. -/
lemma gpoly_Ppsi {z : ℝ} (hz : z ≠ -1) : gpoly Ppsi z = 1 / (1 + z) := by
  have hz1 : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  have hkey : (1 : ℝ) - (z - 1) / (z + 1) = 2 / (z + 1) := by
    field_simp
    ring
  simp only [gpoly, Ppsi, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  rw [zchart, hkey]
  have h : (1 : ℝ) / 2 * (2 / (z + 1)) = 1 / (z + 1) := by ring
  rw [h, add_comm (1 : ℝ) z]

/-- Every `Zop`-iterate of `ψ` is the chart-side evaluation of the corresponding polynomial
iterate. -/
lemma Zop_iter_gpoly_psi : ∀ (b : ℕ) (z : ℝ), 0 < z →
    Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z = gpoly (Tmul^[b] Ppsi) z := by
  intro b
  induction b with
  | zero =>
      intro z hz
      simpa using (gpoly_Ppsi (z := z) (zchart_ne_neg_one hz)).symm
  | succ b ih =>
      intro z hz
      have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
      have hev : Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) =ᶠ[𝓝 z]
          gpoly (Tmul^[b] Ppsi) := by
        filter_upwards [hmem] with w hw
        exact ih w hw
      have hrec : z * deriv (gpoly (Tmul^[b] Ppsi)) z = gpoly (Tmul (Tmul^[b] Ppsi)) z := by
        simpa only [Work.Spaces.Zop] using Zop_gpoly (Tmul^[b] Ppsi) (zchart_ne_neg_one hz)
      calc Work.Spaces.Zop^[b.succ] (fun z : ℝ => 1 / (1 + z)) z
          = Work.Spaces.Zop (Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z))) z :=
              congrFun (Function.iterate_succ_apply' Work.Spaces.Zop b _) z
        _ = z * deriv (Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z))) z := rfl
        _ = z * deriv (gpoly (Tmul^[b] Ppsi)) z := by rw [hev.deriv_eq]
        _ = gpoly (Tmul (Tmul^[b] Ppsi)) z := hrec
        _ = gpoly (Tmul^[b.succ] Ppsi) z :=
              congrArg (fun P => gpoly P z) (Function.iterate_succ_apply' Tmul b Ppsi).symm

/-- **Every `Zop`-iterate of `ψ(z) = 1/(1+z)` is bounded on `(0,∞)`.**  This is the hypothesis
of the multiplier estimates for the radial factor `1/(1+z)`. -/
theorem zop_psi_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z| ≤ K := by
  have hbd : ∀ b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z →
      |Work.Spaces.Zop^[b] (fun z : ℝ => 1 / (1 + z)) z| ≤ C := by
    intro b
    refine ⟨(Tmul^[b] Ppsi).sum (fun _ a => |a|), ?_, ?_⟩
    · rw [Polynomial.sum_def]
      exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    · intro z hz
      rw [Zop_iter_gpoly_psi b z hz]
      exact poly_eval_abs_le _ (abs_zchart_le_one hz)
  choose C hC using hbd
  refine ⟨∑ b ∈ Finset.range (n + 1), C b, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => (hC i).1)
  · intro b hb z hz
    have hbmem : b ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
    have hle : C b ≤ ∑ i ∈ Finset.range (n + 1), C i :=
      Finset.single_le_sum (fun i _ => (hC i).1) hbmem
    exact le_trans ((hC b).2 z hz) hle


end Work.FTS.CoercivityFix.PsiMul
end
end
