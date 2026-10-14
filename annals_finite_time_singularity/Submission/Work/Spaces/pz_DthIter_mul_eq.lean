import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Have
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.H2.Qd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

theorem Qd_subset_nbhU : Qd ⊆ Work.Spaces.nbhU := by
  intro p hp
  simp only [Qd, Work.Spaces.nbhU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩

theorem Qd_subset_quadU : Qd ⊆ Work.Spaces.quadU := by
  intro p hp
  simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], hp.2⟩


theorem sin_two_pos_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  simp only [Work.Spaces.w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt hp.1)

theorem continuousOn_sin_rpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Qd hp.2)))

/-- `continuousOn_sin_rpow_Qd` under the name used by the `T2`-family of this directory. -/
theorem continuousOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  continuousOn_sin_rpow_Qd c

theorem continuousOn_Whz_Qd : ContinuousOn (fun p : ℝ × ℝ => Whz p.1 p.2) Qd := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    continuousOn_sin_rpow_Qd (Work.Spaces.eta / 2)
  refine continuousOn_w_Qd.div hsin (fun p hp => ?_)
  exact ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Qd hp.2) _)

theorem continuousOn_Wm_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Wm α p.1 p.2) Qd := by
  simp only [Wm, Work.Spaces.Wt, Work.Spaces.wTheta]
  exact continuousOn_w_Qd.mul (continuousOn_sin_rpow_Qd (-(Work.Spaces.gam α / 2)))

theorem continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) Qd :=
    continuousOn_w_Qd.mul (continuousOn_sin_rpow_Qd (-(Work.Spaces.gam α / 2)))
  simpa only [Work.Spaces.Wt, Work.Spaces.wTheta] using h1

/-- `sin(2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
  linarith [hθ.2, Real.pi_pos]

theorem Whz_nonneg {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Whz z θ := by
  simp only [Whz, Work.Spaces.w]
  exact div_nonneg (by positivity) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

theorem Wm_nonneg (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wm α z θ := by
  simp only [Wm, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

end

end Work.FTS.H2
end
-- ===== merged: Submission.Work.Spaces.Gamma_WlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Γ(θ)·z/(1+z)²` belongs to `𝒲^{l,∞}` uniformly in `α ∈ (0,1]`

This proves the paper's Proposition "ΓRegularity": the basic example
`f(z,θ) = Γ(θ)·z/(1+z)²` of a `𝒲^{l,∞}` function has `𝒲^{l,∞}`-norm bounded by a
constant depending only on `l`, uniformly for `α ∈ (0,1]`.

The proof is quantitative.  Writing `f = Γ ⊗ h` with `h(z) = z/(1+z)²`:

* the `z`-derivatives factor through `h`, whose `k`-th derivative is
  `(-1)^{k-1} k! (k-z)/(1+z)^{k+2}` (so `|(1+z)^k h^{(k)}(z)| ≤ k!(k+1)` for `z ≥ 0`);
* the angular derivatives are handled through the coefficient sequence `Tfun` with
  `D_θ^{j+1}Γ = α · Tfun j α · Γ` on `(0,π/2)`, and the key pointwise estimate
  `α Γ(θ) sin(2θ)^{-α/5}/(α+sin(2θ)) ≤ 1`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

local notation "C∞" => (⊤ : ℕ∞)

/-! ## Unconditional derivative-of-a-constant-multiple lemmas -/

lemma deriv_mul_const' (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => f y * c) x = deriv f x * c := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_mul_const hf c
    · have h2 : ¬ DifferentiableAt ℝ (fun y => f y * c) x := by
        intro hh
        apply hf
        have he : f = fun y => (f y * c) * c⁻¹ := by
          funext y; rw [mul_assoc, mul_inv_cancel₀ h, mul_one]
        rw [he]
        exact hh.mul_const c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, zero_mul]

lemma deriv_const_mul' (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-! ## `dthU` is a derivation on smooth functions -/

lemma dthU_add (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    dthU (f + g) = dthU f + dthU g := by
  funext θ
  simp only [dthU_apply, Pi.add_apply]
  rw [deriv_add (hf θ) (hg θ)]
  ring

lemma dthU_mul (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    dthU (f * g) = dthU f * g + f * dthU g := by
  funext θ
  simp only [dthU_apply, Pi.mul_apply, Pi.add_apply]
  rw [deriv_mul (hf θ) (hg θ)]
  ring

lemma dthU_const_mul (c : ℝ) (f : ℝ → ℝ) :
    dthU (fun θ => c * f θ) = fun θ => c * dthU f θ := by
  funext θ
  simp only [dthU_apply]
  rw [deriv_const_mul']
  ring

lemma dthU_mul_apply (f g : ℝ → ℝ) (θ : ℝ) (hf : DifferentiableAt ℝ f θ)
    (hg : DifferentiableAt ℝ g θ) :
    dthU (f * g) θ = dthU f θ * g θ + f θ * dthU g θ := by
  simp only [dthU_apply, Pi.mul_apply]
  rw [deriv_mul hf hg]
  ring

lemma dthU_const_mul_apply (c : ℝ) (f : ℝ → ℝ) (θ : ℝ) :
    dthU (fun θ => c * f θ) θ = c * dthU f θ := by
  simp only [dthU_apply]
  rw [deriv_const_mul']
  ring

lemma dthU_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ C∞ f) : ContDiff ℝ C∞ (dthU f) := by
  show ContDiff ℝ C∞ (fun θ : ℝ => Real.sin (2 * θ) * deriv f θ)
  fun_prop (disch := assumption)

lemma dthU_iter_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ C∞ f) (m : ℕ) :
    ContDiff ℝ C∞ (dthU^[m] f) := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact dthU_smooth ih

lemma dthU_zero : dthU (0 : ℝ → ℝ) = 0 := by
  funext θ; simp [dthU_apply]

lemma dthU_finset_sum {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ s, Differentiable ℝ (φ i)) :
    dthU (∑ i ∈ s, φ i) = ∑ i ∈ s, dthU (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dthU_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have h1 : Differentiable ℝ (φ a) := hφ a (Finset.mem_insert_self a s)
      have h2 : Differentiable ℝ (∑ i ∈ s, φ i) :=
        Differentiable.sum (fun i hi => hφ i (Finset.mem_insert_of_mem hi))
      rw [dthU_add _ _ h1 h2]
      congr 1
      exact ih (fun i hi => hφ i (Finset.mem_insert_of_mem hi))

lemma dthU_iter_add (m : ℕ) (f g : ℝ → ℝ) (hf : ContDiff ℝ C∞ f) (hg : ContDiff ℝ C∞ g) :
    dthU^[m] (f + g) = dthU^[m] f + dthU^[m] g := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih]
      rw [dthU_add]
      · exact (dthU_iter_smooth hf m).differentiable (by simp)
      · exact (dthU_iter_smooth hg m).differentiable (by simp)

lemma dthU_iter_const_mul (m : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    dthU^[m] (fun θ => c * f θ) = fun θ => c * dthU^[m] f θ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, dthU_const_mul]

lemma dthU_iter_succ_apply (i : ℕ) (f : ℝ → ℝ) : dthU (dthU^[i] f) = dthU^[i+1] f :=
  (Function.iterate_succ_apply' dthU i f).symm

/-- Coefficients of the Leibniz expansion of `dthU^[m] (f * g)`. -/
noncomputable def dthCoef (m : ℕ) (f g : ℝ → ℝ) (i : ℕ) : ℝ → ℝ :=
  fun θ => (m.choose i : ℝ) * (dthU^[i] f θ * dthU^[m-i] g θ)

lemma dthCoef_apply (m : ℕ) (f g : ℝ → ℝ) (i : ℕ) (θ : ℝ) :
    dthCoef m f g i θ = (m.choose i : ℝ) * (dthU^[i] f θ * dthU^[m-i] g θ) := rfl

/-- Iterated Leibniz rule for `dthU`. -/
lemma dthU_iter_mul (m : ℕ) (f g : ℝ → ℝ) (hf : ContDiff ℝ C∞ f) (hg : ContDiff ℝ C∞ g) :
    dthU^[m] (f * g) = ∑ i ∈ Finset.range (m+1), dthCoef m f g i := by
  induction m with
  | zero =>
      funext θ
      simp [dthCoef]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      have hdiff : ∀ i ∈ Finset.range (m+1), Differentiable ℝ (dthCoef m f g i) := by
        intro i hi
        exact ((((dthU_iter_smooth hf i).differentiable (by simp)).mul
          ((dthU_iter_smooth hg (m-i)).differentiable (by simp))).const_mul _)
      rw [dthU_finset_sum _ _ hdiff]
      have hterm : ∀ i, dthU (dthCoef m f g i) =
          fun θ => (m.choose i : ℝ) *
            (dthU^[i+1] f θ * dthU^[m-i] g θ + dthU^[i] f θ * dthU^[m-i+1] g θ) := by
        intro i
        have hA : Differentiable ℝ (dthU^[i] f) :=
          (dthU_iter_smooth hf i).differentiable (by simp)
        have hB : Differentiable ℝ (dthU^[m-i] g) :=
          (dthU_iter_smooth hg (m-i)).differentiable (by simp)
        have hdc : dthCoef m f g i =
            fun θ => (m.choose i : ℝ) * ((dthU^[i] f * dthU^[m-i] g) θ) := by
          funext θ; rfl
        rw [hdc, dthU_const_mul, dthU_mul (dthU^[i] f) (dthU^[m-i] g) hA hB,
          dthU_iter_succ_apply, dthU_iter_succ_apply]
        funext θ; simp only [Pi.add_apply, Pi.mul_apply]
      simp only [hterm]
      funext θ
      simp only [Finset.sum_apply, dthCoef_apply]
      rw [Finset.sum_choose_succ_mul (fun a b => dthU^[a] f θ * dthU^[b] g θ) m]
      have hsum : (∑ x ∈ Finset.range (m+1), (m.choose x : ℝ) *
            (dthU^[x] f θ * dthU^[m - x + 1] g θ))
          = ∑ x ∈ Finset.range (m+1), (m.choose x : ℝ) *
            (dthU^[x] f θ * dthU^[m + 1 - x] g θ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' : x ≤ m := by simp at hx; omega
        rw [show m - x + 1 = m + 1 - x from by omega]
      simp only [mul_add, Finset.sum_add_distrib, hsum, add_comm]

/-! ## Smoothness of `Tfun` -/

lemma qfun_smooth : ContDiff ℝ C∞ qfun := by
  rw [show qfun = fun θ : ℝ => Real.cos (2*θ) - 1/3 from rfl]
  fun_prop

lemma Tfun_smooth (j : ℕ) (α : ℝ) : ContDiff ℝ C∞ (Tfun j α) := by
  induction j with
  | zero => exact qfun_smooth
  | succ j ih =>
      have h : Tfun (j+1) α = dthU (Tfun j α) + (fun θ => α * qfun θ) * (Tfun j α) := by
        funext θ
        rw [Tfun_succ]
        simp only [dthU_apply, Pi.add_apply, Pi.mul_apply]
      rw [h]
      exact (dthU_smooth ih).add ((contDiff_const.mul qfun_smooth).mul ih)

/-! ## `D_θ^j Γ = α · Tfun (j-1) α · Γ` -/

lemma Gam_differentiableAt (α θ : ℝ) (h0 : 0 < θ) (h1 : θ < π/2) :
    DifferentiableAt ℝ (fun t => Gam α t) θ := by
  have hb : 0 < Real.sin θ * Real.cos θ ^ 2 := by
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (by
      constructor <;> linarith [Real.pi_pos])
    positivity
  have h1' : DifferentiableAt ℝ (fun t => Real.sin t * Real.cos t ^ 2) θ := by fun_prop
  have h2 := h1'.rpow_const (p := α/3) (Or.inl (ne_of_gt hb))
  simpa only [Gam] using h2

lemma dthU_iter_Gam (j : ℕ) (α : ℝ) (hα : 0 < α) :
    Set.EqOn (dthU^[j+1] (fun t => Gam α t))
      (fun θ => α * Tfun j α θ * Gam α θ) (Set.Ioo 0 (π/2)) := by
  induction j with
  | zero =>
      intro θ hθ
      rw [Function.iterate_one]
      simpa only [Tfun_zero] using dthU_Gam α θ hα hθ
  | succ j ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      have hmem : Set.Ioo (0:ℝ) (π/2) ∈ 𝓝 θ := IsOpen.mem_nhds isOpen_Ioo hθ
      have hev := ih.eventuallyEq_of_mem hmem
      have hderiv := hev.deriv_eq
      have hstep : dthU (dthU^[j+1] (fun t => Gam α t)) θ
          = dthU (fun θ => α * Tfun j α θ * Gam α θ) θ := by
        rw [dthU_apply, dthU_apply, hderiv]
      rw [hstep]
      have hT : DifferentiableAt ℝ (fun θ => α * Tfun j α θ) θ :=
        ((Tfun_smooth j α).differentiable (by simp)).differentiableAt.const_mul α
      have hG : DifferentiableAt ℝ (fun t => Gam α t) θ :=
        Gam_differentiableAt α θ hθ.1 hθ.2
      have hcomp : (fun θ => α * Tfun j α θ * Gam α θ)
          = (fun θ => α * Tfun j α θ) * (fun t => Gam α t) := rfl
      rw [hcomp, dthU_mul_apply (fun θ => α * Tfun j α θ) (fun t => Gam α t) θ hT hG,
        dthU_const_mul_apply α (Tfun j α) θ,
        show dthU (fun t => Gam α t) θ = α * qfun θ * Gam α θ from dthU_Gam α θ hα hθ]
      simp only [Tfun_succ]
      simp only [dthU_apply]
      ring_nf


/-! ## Separation of variables for `DthIter` and `pzIter` -/

lemma DthIter_decomp (j : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    DthIter j (fun z θ => A θ * B z) z θ = dthU^[j] A θ * B z := by
  induction j generalizing θ with
  | zero => rfl
  | succ j ih =>
      rw [DthIter_succ]
      simp only [Dth, pth]
      rw [show (fun θ' => DthIter j (fun z θ => A θ * B z) z θ')
            = (fun θ' => dthU^[j] A θ' * B z) from by
          funext θ'; exact ih θ']
      rw [deriv_mul_const']
      rw [show Real.sin (2 * θ) * (deriv (dthU^[j] A) θ * B z)
            = dthU (dthU^[j] A) θ * B z from by
          simp only [dthU_apply]; ring]
      rw [dthU_iter_succ_apply]

lemma pzIter_decomp (k : ℕ) (C B : ℝ → ℝ) (z θ : ℝ) :
    pzIter k (fun z θ => C θ * B z) z θ = C θ * deriv^[k] B z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [pzIter_succ]
      simp only [pz]
      rw [show (fun z' => pzIter k (fun z θ => C θ * B z) z' θ)
            = (fun z' => C θ * deriv^[k] B z') from by
          funext z'; exact ih z']
      rw [deriv_const_mul']
      rw [show deriv (deriv^[k] B) = deriv^[k+1] B from
        (Function.iterate_succ_apply' deriv k B).symm]

/-! ## Vanishing at the angular boundary -/

lemma dthU_eq_zero_of_sin_eq_zero (φ : ℝ → ℝ) {θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) : dthU φ θ = 0 := by
  rw [dthU_apply, hθ, zero_mul]

lemma dthU_iter_eq_zero_of_sin_eq_zero (φ : ℝ → ℝ) (j : ℕ) {θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) : dthU^[j+1] φ θ = 0 := by
  rw [Function.iterate_succ_apply']
  exact dthU_eq_zero_of_sin_eq_zero (dthU^[j] φ) hθ

lemma Gam_zero_left (α : ℝ) (hα : α ≠ 0) : Gam α 0 = 0 := by
  have h : α / 3 ≠ 0 := div_ne_zero hα (by norm_num)
  simp only [Gam, Real.sin_zero, Real.cos_zero, one_pow, mul_one]
  exact Real.zero_rpow h

lemma Gam_zero_right (α : ℝ) (hα : α ≠ 0) : Gam α (π/2) = 0 := by
  have h : α / 3 ≠ 0 := div_ne_zero hα (by norm_num)
  have hc : Real.cos (π/2) = 0 := Real.cos_pi_div_two
  simp only [Gam, Real.sin_pi_div_two, hc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero]
  exact Real.zero_rpow h

lemma dthU_iter_eq_zero_of_sin_eq_zero' (φ : ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) {θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) : dthU^[j] φ θ = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact dthU_iter_eq_zero_of_sin_eq_zero φ i hθ

lemma dthU_iter_comp (m : ℕ) (f : ℝ → ℝ) : dthU^[m] (dthU f) = dthU^[m+1] f := by
  induction m with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_one]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      exact (Function.iterate_succ_apply' dthU (m+1) f).symm

lemma dthU_iter_Gam_abs_bound (j : ℕ) (hj : 1 ≤ j) (α : ℝ) (hα : 0 < α) (M : ℝ)
    (hM : ∀ θ ∈ Iθ, |Tfun (j-1) α θ| ≤ M) :
    ∀ θ ∈ Iθ, |dthU^[j] (fun t => Gam α t) θ| ≤ α * M * Gam α θ := by
  intro θ hθ
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · have heq := dthU_iter_Gam (j-1) α hα (show θ ∈ Set.Ioo 0 (π/2) from ⟨h0, h1⟩)
      rw [show j - 1 + 1 = j from by omega] at heq
      rw [heq, abs_mul, abs_mul, abs_of_pos hα]
      have hG := (Gam_bounds α θ hα hθ).1
      rw [abs_of_nonneg hG]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hM θ hθ) (le_of_lt hα)) hG
    · subst h1
      rw [dthU_iter_eq_zero_of_sin_eq_zero' _ hj (by
            rw [show 2 * (π/2) = π from by ring, Real.sin_pi]), abs_zero]
      rw [Gam_zero_right α (ne_of_gt hα)]
      simp
  · subst h0
    rw [dthU_iter_eq_zero_of_sin_eq_zero' _ hj (by simp), abs_zero]
    rw [Gam_zero_left α (ne_of_gt hα)]
    simp

/-! ## Bounds for the coefficient sequence `Tfun` -/

lemma dthU_qfun_bounded (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Iθ, |dthU^[m] qfun θ| ≤ B := by
  have hcont : ContinuousOn (dthU^[m] qfun) Iθ :=
    ((dthU_iter_smooth qfun_smooth m).continuous).continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have h := hC θ hθ
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

noncomputable def qBound (m : ℕ) : ℝ := Classical.choose (dthU_qfun_bounded m)

lemma qBound_nonneg (m : ℕ) : 0 ≤ qBound m :=
  (Classical.choose_spec (dthU_qfun_bounded m)).1

lemma dthU_qfun_le_qBound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    |dthU^[m] qfun θ| ≤ qBound m :=
  (Classical.choose_spec (dthU_qfun_bounded m)).2 θ hθ

lemma Tfun_iter_bounded (j : ℕ) : ∃ M : ℕ → ℝ, (∀ m, 0 ≤ M m) ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ : ℝ, θ ∈ Iθ → ∀ m : ℕ,
      |dthU^[m] (Tfun j α) θ| ≤ M m := by
  induction j with
  | zero =>
      refine ⟨qBound, qBound_nonneg, ?_⟩
      intro α hα hα1 θ hθ m
      have hT0 : Tfun 0 α = qfun := by funext t; rfl
      rw [hT0]
      exact dthU_qfun_le_qBound m hθ
  | succ j ih =>
      obtain ⟨M, hM0, hMbound⟩ := ih
      refine ⟨fun m => M (m+1) + ∑ i ∈ Finset.range (m+1),
          (m.choose i : ℝ) * qBound i * M (m-i), ?_, ?_⟩
      · intro m
        exact add_nonneg (hM0 _) (Finset.sum_nonneg fun i _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (qBound_nonneg i)) (hM0 _))
      · intro α hα hα1 θ hθ m
        have hTeq : Tfun (j+1) α = dthU (Tfun j α) + (fun θ => α * qfun θ) * (Tfun j α) := by
          funext t; rw [Tfun_succ]; simp only [dthU_apply, Pi.add_apply, Pi.mul_apply]
        have hsm : (fun θ => α * qfun θ) * (Tfun j α)
            = fun θ => α * ((qfun * (Tfun j α)) θ) := by
          funext t; simp only [Pi.mul_apply]; ring
        have hdiff1 : ContDiff ℝ C∞ (dthU (Tfun j α)) := dthU_smooth (Tfun_smooth j α)
        have hdiff2 : ContDiff ℝ C∞ ((fun θ => α * qfun θ) * (Tfun j α)) :=
          (contDiff_const.mul qfun_smooth).mul (Tfun_smooth j α)
        have hdecomp : dthU^[m] (Tfun (j+1) α)
            = fun θ => dthU^[m+1] (Tfun j α) θ + α * (dthU^[m] (qfun * (Tfun j α))) θ := by
          rw [hTeq, dthU_iter_add m _ _ hdiff1 hdiff2, hsm, dthU_iter_const_mul,
            dthU_iter_comp]
          funext t; simp only [Pi.add_apply]
        have hleib : dthU^[m] (qfun * (Tfun j α))
            = ∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i :=
          dthU_iter_mul m qfun (Tfun j α) qfun_smooth (Tfun_smooth j α)
        have hS : 0 ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M (m-i) :=
          Finset.sum_nonneg fun i _ =>
            mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (qBound_nonneg i)) (hM0 _)
        calc |dthU^[m] (Tfun (j+1) α) θ|
            = |dthU^[m+1] (Tfun j α) θ + α * (dthU^[m] (qfun * (Tfun j α))) θ| := by
                rw [hdecomp]
          _ ≤ |dthU^[m+1] (Tfun j α) θ| + |α * (dthU^[m] (qfun * (Tfun j α))) θ| :=
                abs_add_le _ _
          _ = |dthU^[m+1] (Tfun j α) θ| + α * |(dthU^[m] (qfun * (Tfun j α))) θ| := by
                rw [abs_mul, abs_of_pos hα]
          _ = |dthU^[m+1] (Tfun j α) θ|
                + α * |(∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i) θ| := by
                rw [hleib]
          _ = |dthU^[m+1] (Tfun j α) θ|
                + α * |∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i θ| := by
                rw [Finset.sum_apply]
          _ ≤ M (m+1) + α * ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M (m-i) := by
                apply add_le_add
                · exact hMbound α hα hα1 θ hθ (m+1)
                · apply mul_le_mul_of_nonneg_left _ (le_of_lt hα)
                  calc |∑ i ∈ Finset.range (m+1), dthCoef m qfun (Tfun j α) i θ|
                      ≤ ∑ i ∈ Finset.range (m+1), |dthCoef m qfun (Tfun j α) i θ| :=
                        Finset.abs_sum_le_sum_abs _ _
                    _ ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M (m-i) := by
                        apply Finset.sum_le_sum
                        intro i hi
                        have habs : |dthCoef m qfun (Tfun j α) i θ|
                            = (m.choose i : ℝ) * |dthU^[i] qfun θ|
                              * |dthU^[m-i] (Tfun j α) θ| := by
                          rw [dthCoef_apply, abs_mul, abs_mul,
                            abs_of_nonneg (Nat.cast_nonneg (m.choose i))]
                          ring
                        rw [habs]
                        exact mul_le_mul
                          (mul_le_mul_of_nonneg_left (dthU_qfun_le_qBound i hθ)
                            (Nat.cast_nonneg _))
                          (hMbound α hα hα1 θ hθ (m-i)) (abs_nonneg _)
                          (mul_nonneg (Nat.cast_nonneg _) (qBound_nonneg i))
          _ ≤ M (m+1) + ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M (m-i) := by
                have hstar : α * (∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M (m-i))
                    ≤ ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * qBound i * M (m-i) :=
                  (mul_le_mul_of_nonneg_right hα1 hS).trans_eq (one_mul _)
                linarith [hstar]

noncomputable def tBound (j : ℕ) : ℕ → ℝ := Classical.choose (Tfun_iter_bounded j)

lemma tBound_nonneg (j m : ℕ) : 0 ≤ tBound j m :=
  (Classical.choose_spec (Tfun_iter_bounded j)).1 m

lemma dthU_iter_Tfun_le (j : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) (hθ : θ ∈ Iθ)
    (m : ℕ) : |dthU^[m] (Tfun j α) θ| ≤ tBound j m :=
  (Classical.choose_spec (Tfun_iter_bounded j)).2 α hα hα1 θ hθ m

lemma dthU_Gam_le (j : ℕ) (hj : 1 ≤ j) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ θ ∈ Iθ, |dthU^[j] (fun t => Gam α t) θ| ≤ α * tBound (j-1) 0 * Gam α θ :=
  dthU_iter_Gam_abs_bound j hj α hα (tBound (j-1) 0)
    (fun θ hθ => by simpa using dthU_iter_Tfun_le (j-1) α hα hα1 θ hθ 0)

lemma gamma_weight_nonneg (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) :
    0 ≤ Real.sin (2 * θ) ^ (-(α/5)) / (α + Real.sin (2 * θ)) := by
  apply div_nonneg
  · exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc (by
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])) _
  · have h := Real.sin_nonneg_of_mem_Icc (show 2 * θ ∈ Set.Icc 0 Real.pi from by
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos])
    linarith


end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.Linf_H2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000


/-- At every point of the closed quadrant, a `SmoothNbhd` function is `C^∞`. -/
theorem contDiffAt_uncurry_of_SmoothNbhd {g : ℝ → ℝ → ℝ} (hsm : SmoothNbhd g) {z θ : ℝ}
    (hz : z ∈ Iz) (hθ : θ ∈ Iθ) : ContDiffAt ℝ ⊤ (Function.uncurry g) (z, θ) :=
  hsm.contDiffAt (isOpen_nbhU.mem_nhds (mem_nbhU hz hθ))

/-- The weighted squares of `∂_θ (D_z g)` and of the mixed derivative `D_z D_θ g` agree:
`(w z)² (∂_θ D_z g)² sin(2θ)^{2-γ} = (D_z D_θ g)² W²`.  This is the pointwise weight
bookkeeping that identifies the integrand of the angular Hardy inequality for `D_z g`
with the `(D_z D_θ g · W)²` term of the `H²`-integrand. -/
theorem pth_Dz_sq_rpow_eq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (w z) ^ 2 * (pth (Dz g) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)
      = (mixed 1 1 g z θ) ^ 2 * (Wt α z θ) ^ 2 := by
  intro z hz θ hθ
  have hcd : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) :=
    (contDiffAt_uncurry_of_SmoothNbhd hsm hz hθ).of_le (by norm_num)
  have hcomm : mixed 1 1 g z θ = Real.sin (2 * θ) * pth (Dz g) z θ := by
    show Dz (Dth g) z θ = Real.sin (2 * θ) * pth (Dz g) z θ
    rw [Dz_Dth_comm hcd]; rfl
  have hs : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hgam0 : 0 < gam α := gam_pos hα
  have hgam2 : gam α < 2 := by rw [gam]; linarith
  have hsγ : (Real.sin (2 * θ)) ^ (2 - gam α)
      = Real.sin (2 * θ) * Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(gam α)) := by
    rw [show (2 - gam α) = 2 + (-(gam α)) by ring,
        Real.rpow_add' hs (by linarith : 2 + (-(gam α)) ≠ 0), Real.rpow_two, pow_two]
  have hwt : Wt α z θ * Wt α z θ = w z * w z * (Real.sin (2 * θ)) ^ (-(gam α)) := by
    have h1 : Real.sin (2 * θ) ^ (-(gam α / 2)) * Real.sin (2 * θ) ^ (-(gam α / 2))
        = Real.sin (2 * θ) ^ (-(gam α)) := by
      rw [← Real.rpow_add' hs
            (by intro hh; linarith [hgam0, hh] : (-(gam α / 2)) + (-(gam α / 2)) ≠ 0),
          show (-(gam α / 2)) + (-(gam α / 2)) = -(gam α) by ring]
    rw [Wt, wTheta,
        show w z * Real.sin (2 * θ) ^ (-(gam α / 2)) * (w z * Real.sin (2 * θ) ^ (-(gam α / 2)))
          = w z * w z * (Real.sin (2 * θ) ^ (-(gam α / 2))
              * Real.sin (2 * θ) ^ (-(gam α / 2))) by ring,
        h1]
  simp only [pow_two]
  rw [hcomm, hsγ, hwt]
  ring


/-- Angular Hardy step on `D_z g`, written with the `H²`-integrand on the right.
`HardyTheta` applied to the function `D_z g` (which vanishes at `θ = 0` because of
`VanishTheta`) bounds `(D_z g)²` by an angular integral of `∂_θ (D_z g)` with the
weight `sin(2θ)^{2-γ}`; the pointwise identity `pth_Dz_sq_rpow_eq` rewrites that
integral as `∫_θ (D_z D_θ g · W)²`, which is dominated by `HkIntegrand`. -/
theorem Dz_HardyTheta_HkIntegrand (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd g) (hvt : VanishTheta g) (hmem : HkMem α 2 g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (Dz g z θ) ^ 2 * (w z) ^ 2
        ≤ (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z σ := by
  intro z hz θ hθ
  have hzle : (0 : ℝ) ≤ z := hz
  have hsm' : SmoothNbhd (Dz g) := SmoothNbhd.Dz hsm
  have h0 : Dz g z 0 = 0 := by
    simp only [Dz, pz]
    rw [show (fun z' => g z' 0) = (fun _ => (0 : ℝ)) from funext (fun z' => hvt.1 z')]
    simp
  have hgam2 : gam α < 2 := by rw [gam]; linarith
  have hc : 0 < 2 - gam α := by linarith
  have hHint : IntegrableOn
      (fun σ => (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ := by
    rcases eq_or_lt_of_le hzle with hz0 | hzpos
    · subst hz0
      have hzero : (fun σ => (pth (Dz g) 0 σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
          = (fun _ => (0 : ℝ)) := by
        funext σ
        have hp : pth (Dz g) 0 σ = 0 := by
          show deriv (fun θ' => Dz g 0 θ') σ = 0
          rw [show (fun θ' => Dz g 0 θ') = (fun _ => (0 : ℝ)) from funext (fun θ' => by simp [Dz]),
              deriv_const]
        rw [hp]; ring
      rw [hzero]; exact integrableOn_zero
    · have hw1 : 1 ≤ (w z) ^ 2 := by
        have : 1 ≤ w z := by
          rw [w]
          rw [one_le_div (by positivity : (0:ℝ) < z ^ 2)]
          nlinarith [sq_nonneg z]
        nlinarith [this]
      have hAES : AEStronglyMeasurable
          (fun σ => (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
          (volume.restrict Iθ) := by
        have h1 : AEStronglyMeasurable (fun σ => pth (Dz g) z σ) (volume.restrict Iθ) :=
          (measurable_deriv (fun θ' => Dz g z θ')).aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun σ => (Real.sin (2 * σ)) ^ (2 - gam α))
            (volume.restrict Iθ) :=
          ((by fun_prop : Continuous fun σ : ℝ => Real.sin (2 * σ))).rpow_const
            (fun σ => Or.inr hc.le) |>.aestronglyMeasurable
        exact (h1.pow 2).mul h2
      refine MeasureTheory.Integrable.mono' (hmem.1 z hz) hAES ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun σ hσ => ?_)
      have hsnn : 0 ≤ Real.sin (2 * σ) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · linarith [hσ.1]
        · linarith [hσ.2, Real.pi_pos]
      have hfnn : 0 ≤ (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsnn _)
      have hP := pth_Dz_sq_rpow_eq α hα hα1 g hsm z hz σ hσ
      rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
      calc (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)
          ≤ (w z) ^ 2 * ((pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) :=
            le_mul_of_one_le_left hfnn hw1
        _ = (mixed 1 1 g z σ) ^ 2 * (Wt α z σ) ^ 2 := by rw [← mul_assoc]; exact hP
        _ ≤ HkIntegrand α 2 g z σ := by
            rw [← mul_pow]
            exact sq_le_HkIntegrand_mixed α 2 g z σ 1 1 le_rfl (by norm_num)
  have hHT := HardyTheta α hα hα1 (Dz g) z hsm' hz h0 hHint θ hθ
  have hcoef : 0 ≤ 100 / (gam α - 1) := by
    have : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
    exact div_nonneg (by norm_num) this.le
  have hEq : (w z) ^ 2 * ∫ σ in Iθ,
        (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)
      = ∫ σ in Iθ, (mixed 1 1 g z σ) ^ 2 * (Wt α z σ) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_)
    rw [← mul_assoc]
    exact pth_Dz_sq_rpow_eq α hα hα1 g hsm z hz σ hσ
  have hLe : ∫ σ in Iθ, (mixed 1 1 g z σ) ^ 2 * (Wt α z σ) ^ 2
      ≤ ∫ σ in Iθ, HkIntegrand α 2 g z σ :=
    MeasureTheory.setIntegral_mono_of_nonneg
      (fun σ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun σ _ => by
        rw [← mul_pow]
        exact sq_le_HkIntegrand_mixed α 2 g z σ 1 1 le_rfl (by norm_num))
      (hmem.1 z hz)
  calc (Dz g z θ) ^ 2 * (w z) ^ 2
      ≤ (100 / (gam α - 1)) * ((w z) ^ 2 * ∫ σ in Iθ,
          (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by
        have := mul_le_mul_of_nonneg_right hHT (sq_nonneg (w z))
        calc (Dz g z θ) ^ 2 * (w z) ^ 2
            ≤ ((100 / (gam α - 1)) * ∫ σ in Iθ,
                (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) * (w z) ^ 2 := this
          _ = (100 / (gam α - 1)) * ((w z) ^ 2 * ∫ σ in Iθ,
                (pth (Dz g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by ring
    _ = (100 / (gam α - 1)) * ∫ σ in Iθ, (mixed 1 1 g z σ) ^ 2 * (Wt α z σ) ^ 2 := by
        rw [hEq]
    _ ≤ (100 / (gam α - 1)) * ∫ σ in Iθ, HkIntegrand α 2 g z σ :=
        mul_le_mul_of_nonneg_left hLe hcoef



end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.aesm_of_continuousOn_Qd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.Spaces

/-- If `g` is continuous on the open quadrant `(0,∞) × (0,π/2)`, then it is almost everywhere
strongly measurable with respect to the product of the restrictions of Lebesgue measure to
`Iz = [0,∞)` and `Iθ = [0,π/2]`.  Indeed that product measure is the restriction of the planar
Lebesgue measure to `Iz ×ˢ Iθ`, which equals the open quadrant up to a null set (the difference
being contained in the coordinate hyperplanes and the two boundary lines `θ = 0`, `θ = π/2`). -/
theorem aesm_of_continuousOn_Qd (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable g
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `Iz` agrees a.e. with the open half-line and `Iθ` a.e. with the open interval.
  have hz : Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Iz ×ˢ Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  -- The open quadrant is measurable, so continuity there gives almost everywhere strong
  -- measurability for the restricted planar Lebesgue measure.
  have hUm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hmain : AEStronglyMeasurable g
      ((volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    hg.aestronglyMeasurable hUm
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.Spaces

/-- For `z > 0`, the slice `θ ↦ g (z, θ)` is continuous on the open interval `(0, π/2)`,
hence almost everywhere strongly measurable for the measure `volume.restrict Iθ`
(the two endpoints `0` and `π/2` form a null set). -/
theorem aesm_slice_of_continuousOn_Qd (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g (z, θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- the slice map `θ ↦ (z, θ)` maps `(0, π/2)` into the open quadrant
  have hcont : ContinuousOn (fun θ : ℝ => g (z, θ)) (Set.Ioo 0 (π / 2)) :=
    hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => ⟨hz, hθ⟩)
  -- continuity on the open interval gives a.e. strong measurability there
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => g (z, θ))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  -- `(0, π/2)` and `Iθ = [0, π/2]` differ by the two null endpoints
  have hset : (Set.Ioo (0 : ℝ) (π / 2)) =ᵐ[MeasureTheory.volume]
      (Set.Icc (0 : ℝ) (π / 2)) :=
    MeasureTheory.Ioo_ae_eq_Icc
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Measure.restrict_congr_set hset).symm
  rw [hmeas]
  exact h1

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.bt_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-! ## Pointwise algebra for the bad term -/

/-- `sin (2 θ) ≥ 0` for `θ ∈ Iθ`. -/
theorem bt_sin_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(s ^ (-a/2)) ^ 2 = s ^ (-a)` for `s ≥ 0`, `a ≠ 0`. -/
theorem bt_rpow_sq (a s : ℝ) (hs : 0 ≤ s) (ha : a ≠ 0) :
    (s ^ (-(a / 2))) ^ 2 = s ^ (-a) := by
  have hne : -(a / 2) + -(a / 2) ≠ 0 := by
    have h : -(a / 2) + -(a / 2) = -a := by ring
    rw [h]; exact neg_ne_zero.mpr ha
  rw [pow_two, ← Real.rpow_add' hs hne]
  rw [show -(a / 2) + -(a / 2) = -a by ring]

/-- `(Wt α z θ)^2 = (w z)^2 * sin(2θ)^{-γ}`. -/
theorem bt_Wt_sq (α z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) :
    (Wt α z θ) ^ 2 = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs := bt_sin_nonneg hθ
  have hgam : gam α ≠ 0 := by rw [gam]; linarith
  rw [Wt, wTheta, mul_pow, bt_rpow_sq (gam α) (Real.sin (2 * θ)) hs hgam]

/-- Factorisation of the bad term, in generic variables. -/
theorem bt_factor_gen (α z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) (A B : ℝ) :
    (A * B * Wt α z θ) ^ 2
      = (A ^ 2 * (w z) ^ 2) * (B ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
  rw [mul_pow, mul_pow, bt_Wt_sq α z θ hα hθ]
  ring

/-- The pointwise factorisation of the bad term. -/
theorem bt_factor (α z θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) (f g : ℝ → ℝ → ℝ) :
    (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
      = ((DzIter 3 f z θ) ^ 2 * (w z) ^ 2)
        * ((Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) :=
  bt_factor_gen α z θ hα hθ (DzIter 3 f z θ) (Dth g z θ)




/-- The weight identity behind the `θ`-Hardy estimate, in generic variables. -/
theorem bt_mixed_weight_gen (α z θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Iθ)
    (A C : ℝ) (hAC : C = Real.sin (2 * θ) * A) :
    A ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α) = (C * Wt α z θ) ^ 2 := by
  have hs := bt_sin_nonneg hθ
  have hne1 : (1 : ℝ) + (1 - gam α) ≠ 0 := by
    have h : (1 : ℝ) + (1 - gam α) = 2 - gam α := by ring
    rw [h, gam]; intro hh; linarith
  have hne2 : (1 : ℝ) + (-(gam α)) ≠ 0 := by
    have h : (1 : ℝ) + (-(gam α)) = 1 - gam α := by ring
    rw [h, gam]; intro hh; linarith
  have hkey : (Real.sin (2 * θ)) ^ (2 - gam α)
      = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
    rw [show (2 : ℝ) - gam α = 1 + (1 - gam α) by ring]
    rw [Real.rpow_add' hs hne1]
    rw [show (1 : ℝ) - gam α = 1 + (-(gam α)) by ring]
    rw [Real.rpow_add' hs hne2]
    simp only [Real.rpow_one]
    ring
  rw [hAC, hkey, mul_pow, mul_pow, bt_Wt_sq α z θ hα hθ]
  ring



end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.mixed_mul_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.Spaces

set_option maxHeartbeats 1600000

/-! ## Differentiability of slices -/

lemma SmoothU.differentiableAt {F : ℝ × ℝ → ℝ} (h : SmoothU F) {p : ℝ × ℝ}
    (hp : p ∈ quadU) : DifferentiableAt ℝ F p :=
  (h.contDiffAt (isOpen_quadU.mem_nhds hp)).differentiableAt (by norm_num)

lemma differentiableAt_slice_fst {F : ℝ × ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ F (z, θ)) :
    DifferentiableAt ℝ (fun z' => F (z', θ)) z := by
  change DifferentiableAt ℝ (F ∘ fun z' : ℝ => (z', θ)) z
  exact h.comp z (hasFDerivAt_prodMk_left z θ).differentiableAt

lemma differentiableAt_slice_snd {F : ℝ × ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ F (z, θ)) :
    DifferentiableAt ℝ (fun θ' => F (z, θ')) θ := by
  change DifferentiableAt ℝ (F ∘ fun θ' : ℝ => (z, θ')) θ
  exact h.comp θ (hasFDerivAt_prodMk_right z θ).differentiableAt

/-! ## The derivation-like structure for `Zb` -/

theorem Zb_DerivLike : DerivLike quadU SmoothU Zb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      differentiableAt_slice_fst (hB.differentiableAt hp)
    show Zb (A + B) (z, θ) = Zb A (z, θ) + Zb B (z, θ)
    simp only [Zb]
    rw [show (fun z' => (A + B) (z', θ)) =
          (fun z' => A (z', θ)) + (fun z' => B (z', θ)) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      differentiableAt_slice_fst (hB.differentiableAt hp)
    show Zb (A * B) (z, θ) = Zb A (z, θ) * B (z, θ) + A (z, θ) * Zb B (z, θ)
    simp only [Zb]
    rw [show (fun z' => (A * B) (z', θ)) =
          (fun z' => A (z', θ)) * (fun z' => B (z', θ)) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun z' => A (z', θ)) (fun z' => B (z', θ)) (Set.Ioi (-1)) :=
      fun z' hz' => h ⟨hz', hp.2⟩
    show Zb A (z, θ) = Zb B (z, θ)
    simp only [Zb]
    rw [hs.deriv isOpen_Ioi hp.1]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ A) quadU := hA.fderiv_of_isOpen isOpen_quadU (by simp)
    have hev : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (fderiv ℝ A p) (1, 0)) quadU :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 * (fderiv ℝ A p) (1, 0)) quadU :=
      (contDiff_fst.contDiffOn).mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Zb A (z, θ) = z * (fderiv ℝ A (z, θ)) (1, 0)
    simp only [Zb]
    rw [deriv_slice_fst A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      differentiableAt_slice_fst (hA.differentiableAt hp)
    show Zb (fun p => c * A p) (z, θ) = c * Zb A (z, θ)
    simp only [Zb]
    rw [deriv_const_mul c hA']
    ring

/-! ## The derivation-like structure for `Tb` -/

theorem Tb_DerivLike : DerivLike quadU SmoothU Tb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      differentiableAt_slice_snd (hB.differentiableAt hp)
    show Tb (A + B) (z, θ) = Tb A (z, θ) + Tb B (z, θ)
    simp only [Tb]
    rw [show (fun θ' => (A + B) (z, θ')) =
          (fun θ' => A (z, θ')) + (fun θ' => B (z, θ')) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      differentiableAt_slice_snd (hB.differentiableAt hp)
    show Tb (A * B) (z, θ) = Tb A (z, θ) * B (z, θ) + A (z, θ) * Tb B (z, θ)
    simp only [Tb]
    rw [show (fun θ' => (A * B) (z, θ')) =
          (fun θ' => A (z, θ')) * (fun θ' => B (z, θ')) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun θ' => A (z, θ')) (fun θ' => B (z, θ')) (Set.Ioo 0 (π/2)) :=
      fun θ' hθ' => h ⟨hp.1, hθ'⟩
    show Tb A (z, θ) = Tb B (z, θ)
    simp only [Tb]
    rw [hs.deriv isOpen_Ioo hp.2]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ A) quadU := hA.fderiv_of_isOpen isOpen_quadU (by simp)
    have hev : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (fderiv ℝ A p) (0, 1)) quadU :=
      hfd.clm_apply contDiffOn_const
    have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hfun : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * (fderiv ℝ A p) (0, 1)) quadU :=
      hsin.mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Tb A (z, θ) = Real.sin (2 * θ) * (fderiv ℝ A (z, θ)) (0, 1)
    simp only [Tb]
    rw [deriv_slice_snd A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      differentiableAt_slice_snd (hA.differentiableAt hp)
    show Tb (fun p => c * A p) (z, θ) = c * Tb A (z, θ)
    simp only [Tb]
    rw [deriv_const_mul c hA']
    ring

/-! ## The derivation-like structure for `Zop` -/

theorem Zop_DerivLike : DerivLike (Set.Ioi (-1)) SmoothZ Zop where
  add := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show Zop (A + B) z = Zop A z + Zop B z
    simp only [Zop]
    rw [deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    have hB' : DifferentiableAt ℝ B z :=
      (hB.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show Zop (A * B) z = Zop A z * B z + A z * Zop B z
    simp only [Zop]
    rw [deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    intro z hz
    show Zop A z = Zop B z
    simp only [Zop]
    rw [h.deriv isOpen_Ioi hz]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ A) (Set.Ioi (-1)) :=
      hA.fderiv_of_isOpen isOpen_Ioi (by simp)
    have hev : ContDiffOn ℝ ⊤ (fun z : ℝ => (fderiv ℝ A z) 1) (Set.Ioi (-1)) :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ ⊤ (fun z : ℝ => z * (fderiv ℝ A z) 1) (Set.Ioi (-1)) :=
      (contDiff_id.contDiffOn).mul hev
    refine hfun.congr (fun z hz => ?_)
    show Zop A z = z * (fderiv ℝ A z) 1
    simp only [Zop]
    rw [fderiv_apply_one_eq_deriv]
  smul := fun c A hA => by
    intro z hz
    have hA' : DifferentiableAt ℝ A z :=
      (hA.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)
    show Zop (fun p => c * A p) z = c * Zop A z
    simp only [Zop]
    rw [deriv_const_mul c hA']
    ring

/-! ## Translations between the uncurried operators and `Dz`, `Dth` -/

lemma Zb_uncurry (f : ℝ → ℝ → ℝ) :
    Zb (Function.uncurry f) = Function.uncurry (Dz f) := by
  funext p
  simp only [Zb, Dz, pz, Function.uncurry]

lemma Tb_uncurry (f : ℝ → ℝ → ℝ) :
    Tb (Function.uncurry f) = Function.uncurry (Dth f) := by
  funext p
  simp only [Tb, Dth, pth, Function.uncurry]

lemma Zb_iterate_uncurry (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Zb^[n] (Function.uncurry f) = Function.uncurry (DzIter n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Zb_uncurry]
      rfl

lemma Tb_iterate_uncurry (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Tb^[n] (Function.uncurry f) = Function.uncurry (DthIter n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Tb_uncurry]
      rfl

lemma uncurry_mul (f g : ℝ → ℝ → ℝ) :
    Function.uncurry f * Function.uncurry g = Function.uncurry (fun z θ => f z θ * g z θ) :=
  rfl

lemma Zop_slice (n : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    (fun z => DzIter n f z θ) = Zop^[n] (fun z => f z θ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext z
      rw [Function.iterate_succ_apply']
      show Dz (DzIter n f) z θ = Zop (Zop^[n] (fun z => f z θ)) z
      simp only [Dz, pz, Zop]
      rw [ih]

/-! ## Leibniz for `D_z` alone (used on the angular boundary) -/

theorem DzIter_mul (j : ℕ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : z ∈ Iz)
    (hf : ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1)))
    (hg : ContDiffOn ℝ ⊤ (fun z => g z θ) (Set.Ioi (-1))) :
    DzIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ b ∈ Finset.range (j + 1),
        (j.choose b : ℝ) * (DzIter b f z θ * DzIter (j - b) g z θ) := by
  have hz1 : z ∈ Set.Ioi (-1) := by
    rw [Iz, Set.mem_Ici] at hz
    rw [Set.mem_Ioi]; linarith
  have key := (DerivLike.iterate_mul Zop_DerivLike SmoothZ_FunClass j hf hg) hz1
  rw [show (fun z => f z θ) * (fun z => g z θ) = (fun z => f z θ * g z θ) from rfl] at key
  have htr : Zop^[j] (fun z => (fun z θ => f z θ * g z θ) z θ) z =
      Zop^[j] (fun z => f z θ * g z θ) z := rfl
  rw [congrFun (Zop_slice j (fun z θ => f z θ * g z θ) θ) z, htr, key]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← congrFun (Zop_slice b f θ) z, ← congrFun (Zop_slice (j - b) g θ) z]

/-! ## The general two-operator iterated Leibniz rule -/

theorem DerivLike.twoOp_iterate_mul {X : Type*} {s : Set X} {P : (X → ℝ) → Prop}
    {Z Θb : (X → ℝ) → (X → ℝ)} (hP : FunClass P)
    (hZ : DerivLike s P Z) (hΘ : DerivLike s P Θb) (m n : ℕ) {F G : X → ℝ}
    (hF : P F) (hG : P G) :
    Set.EqOn (Z^[m] (Θb^[n] (F * G)))
      (fun p => ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1),
        ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) s := by
  have hA : ∀ a ≤ n, P (fun p => (n.choose a : ℝ) *
      ((Θb^[a] F) p * (Θb^[n - a] G) p)) := fun a ha =>
    hP.smul _ _ (hP.mul _ _ (hΘ.preserve_iterate a hF) (hΘ.preserve_iterate (n - a) hG))
  have step1 : Set.EqOn (Z^[m] (Θb^[n] (F * G)))
      (Z^[m] (fun p => ∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * ((Θb^[a] F) p * (Θb^[n - a] G) p))) s :=
    hZ.iterate_congr m (hΘ.iterate_mul hP n hF hG)
  have step2 : Set.EqOn
      (Z^[m] (fun p => ∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * ((Θb^[a] F) p * (Θb^[n - a] G) p)))
      (fun p => ∑ a ∈ Finset.range (n + 1),
        (Z^[m] (fun p => (n.choose a : ℝ) *
          ((Θb^[a] F) p * (Θb^[n - a] G) p))) p) s :=
    hZ.iterate_sum_range hP m n hA
  have step3 : ∀ a ≤ n, Set.EqOn
      (Z^[m] (fun p => (n.choose a : ℝ) * ((Θb^[a] F) p * (Θb^[n - a] G) p)))
      (fun p => ∑ b ∈ Finset.range (m + 1), ((n.choose a : ℝ) * (m.choose b : ℝ)) *
        ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) s := by
    intro a ha
    have hFa : P (Θb^[a] F) := hΘ.preserve_iterate a hF
    have hGa : P (Θb^[n - a] G) := hΘ.preserve_iterate (n - a) hG
    have hB : P ((Θb^[a] F) * (Θb^[n - a] G)) := hP.mul _ _ hFa hGa
    have hsm := hZ.iterate_smul m (n.choose a : ℝ) hB
    have hmul := hZ.iterate_mul hP m hFa hGa
    have hmul' := eqOn_const_mul (n.choose a : ℝ) hmul
    have hconv : Set.EqOn
        (fun p => (n.choose a : ℝ) * (∑ b ∈ Finset.range (m + 1),
          (m.choose b : ℝ) * ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)))
        (fun p => ∑ b ∈ Finset.range (m + 1), ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) s := by
      intro p hp
      change (n.choose a : ℝ) * (∑ b ∈ Finset.range (m + 1),
          (m.choose b : ℝ) * ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) =
        ∑ b ∈ Finset.range (m + 1), ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b hb => by ring)
    exact hsm.trans (hmul'.trans hconv)
  have step4 : Set.EqOn
      (fun p => ∑ a ∈ Finset.range (n + 1),
        (Z^[m] (fun p => (n.choose a : ℝ) *
          ((Θb^[a] F) p * (Θb^[n - a] G) p))) p)
      (fun p => ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1),
        ((n.choose a : ℝ) * (m.choose b : ℝ)) *
          ((Z^[b] (Θb^[a] F)) p * (Z^[m - b] (Θb^[n - a] G)) p)) s :=
    eqOn_sum (Finset.range (n + 1))
      (fun a ha => step3 a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
  exact step1.trans (step2.trans step4)

/-! ## The endpoints of the angular interval -/

lemma sin_two_eq_zero_of_not_Ioo {θ : ℝ} (hθ : θ ∈ Iθ) (h : θ ∉ Set.Ioo 0 (π/2)) :
    Real.sin (2 * θ) = 0 := by
  rw [Iθ, Set.mem_Icc] at hθ
  rcases lt_or_ge 0 θ with h0 | h0
  · rcases lt_or_ge θ (π/2) with h1 | h1
    · exact absurd (show θ ∈ Set.Ioo 0 (π/2) from ⟨h0, h1⟩) h
    · have h2 : θ = π / 2 := le_antisymm hθ.2 h1
      rw [h2]
      have h3 : 2 * (π / 2) = π := by ring
      rw [h3, Real.sin_pi]
  · have h2 : θ = 0 := le_antisymm h0 hθ.1
    rw [h2]; simp

lemma DthIter_eq_zero_of_sin {u : ℝ → ℝ → ℝ} {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    ∀ n, 1 ≤ n → ∀ z, DthIter n u z θ = 0 := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n _ =>
      intro _ z
      show Dth (DthIter n u) z θ = 0
      show Real.sin (2 * θ) * pth (DthIter n u) z θ = 0
      rw [h, zero_mul]

lemma DzIter_eq_zero_of_slice_zero {u : ℝ → ℝ → ℝ} {θ : ℝ} (h : ∀ z, u z θ = 0) :
    ∀ j z, DzIter j u z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact h z
  | succ j ih =>
      intro z
      show Dz (DzIter j u) z θ = 0
      show z * deriv (fun z' => DzIter j u z' θ) z = 0
      rw [show (fun z' => DzIter j u z' θ) = fun _ => (0 : ℝ) from funext (fun z' => ih z')]
      simp

theorem mixed_mul_eq (j i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.SmoothInt f) (hg : Work.Spaces.SmoothInt g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) := by
  intro z hz θ hθ
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp only [mixed_zero_right]
    rw [DzIter_mul j f g hz (hf.2 θ hθ) (hg.2 θ hθ)]
    rw [Finset.sum_range_one]
    simp
  · by_cases hcase : θ ∈ Set.Ioo 0 (π/2)
    · -- interior: the two-operator Leibniz rule
      have hz1 : z ∈ Set.Ioi (-1) := by
        rw [Iz, Set.mem_Ici] at hz
        rw [Set.mem_Ioi]; linarith
      have hp : (z, θ) ∈ quadU := ⟨hz1, hcase⟩
      have h2 := (DerivLike.twoOp_iterate_mul (X := ℝ × ℝ) (s := quadU) (P := SmoothU)
          SmoothU_FunClass Zb_DerivLike Tb_DerivLike j i
          (show SmoothU (Function.uncurry f) from hf.1)
          (show SmoothU (Function.uncurry g) from hg.1)) hp
      have h2' : Zb^[j] (Tb^[i] (Function.uncurry f * Function.uncurry g)) (z, θ)
          = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ))
                * ((Zb^[b] (Tb^[a] (Function.uncurry f))) (z, θ)
                   * (Zb^[j - b] (Tb^[i - a] (Function.uncurry g))) (z, θ)) := by
        simpa using h2
      have hL : Zb^[j] (Tb^[i] (Function.uncurry f * Function.uncurry g)) (z, θ)
          = mixed j i (fun z θ => f z θ * g z θ) z θ := by
        rw [uncurry_mul f g, Tb_iterate_uncurry i (fun z θ => f z θ * g z θ),
            Zb_iterate_uncurry j (DthIter i (fun z θ => f z θ * g z θ))]
        rfl
      have e_f : ∀ a b, Zb^[b] (Tb^[a] (Function.uncurry f)) (z, θ) = mixed b a f z θ :=
        fun a b => by
          rw [Tb_iterate_uncurry a f, Zb_iterate_uncurry b (DthIter a f)]
          rfl
      have e_g : ∀ a b, Zb^[b] (Tb^[a] (Function.uncurry g)) (z, θ) = mixed b a g z θ :=
        fun a b => by
          rw [Tb_iterate_uncurry a g, Zb_iterate_uncurry b (DthIter a g)]
          rfl
      rw [← hL, h2']
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro b hb
      rw [e_f a b, e_g (i - a) (j - b)]
    · -- angular boundary: everything vanishes
      have hsin : Real.sin (2 * θ) = 0 := sin_two_eq_zero_of_not_Ioo hθ hcase
      have hL : mixed j i (fun z θ => f z θ * g z θ) z θ = 0 := by
        show DzIter j (DthIter i (fun z θ => f z θ * g z θ)) z θ = 0
        apply DzIter_eq_zero_of_slice_zero
        intro z'
        exact DthIter_eq_zero_of_sin hsin i hi z'
      have hR : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (mixed b a f z θ * mixed (j - b) (i - a) g z θ)) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        apply Finset.sum_eq_zero
        intro b hb
        by_cases ha0 : a = 0
        · have hia : 1 ≤ i - a := by omega
          have hz0 : mixed (j - b) (i - a) g z θ = 0 := by
            show DzIter (j - b) (DthIter (i - a) g) z θ = 0
            apply DzIter_eq_zero_of_slice_zero
            intro z'
            exact DthIter_eq_zero_of_sin hsin (i - a) hia z'
          simp [hz0]
        · have ha1 : 1 ≤ a := by omega
          have hz0 : mixed b a f z θ = 0 := by
            show DzIter b (DthIter a f) z θ = 0
            apply DzIter_eq_zero_of_slice_zero
            intro z'
            exact DthIter_eq_zero_of_sin hsin a ha1 z'
          simp [hz0]
      rw [hL, hR]

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.pz_DthIter_mul_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Smoothness of the `z`-slices of the iterates of `D_θ` -/


/-! ## The `θ`-Leibniz identity on `z`-slices -/


/-! ## The main Leibniz rule -/


end Work.Spaces
end
end
