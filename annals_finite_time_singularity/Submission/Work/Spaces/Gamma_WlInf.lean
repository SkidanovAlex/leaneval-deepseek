import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Have
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.rpow_sup_ineq
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.Gam_mul_weight_le
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.pzIter_hKer_bound

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

theorem Gamma_WlInf (l : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInf α l (fun z θ => Work.Spaces.Gam α θ * z / (1 + z) ^ 2) ≤ C := by
  refine ⟨(∑ k ∈ Finset.range (l+1), (k.factorial : ℝ) * (k+1))
    + (∑ j ∈ Finset.range (l+1), ∑ k ∈ Finset.range (l+1),
        (if 1 ≤ j ∧ k + j ≤ l then (k.factorial : ℝ) * (k+1) * tBound (j-1) 0 else 0)) + 1,
    ?_, ?_⟩
  · have h1 : 0 ≤ ∑ k ∈ Finset.range (l+1), (k.factorial : ℝ) * (k+1) :=
      Finset.sum_nonneg fun k _ => by positivity
    have h2 : 0 ≤ ∑ j ∈ Finset.range (l+1), ∑ k ∈ Finset.range (l+1),
        (if 1 ≤ j ∧ k + j ≤ l then (k.factorial : ℝ) * (k+1) * tBound (j-1) 0 else 0) :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by
        split_ifs with h
        · exact mul_nonneg (by positivity) (tBound_nonneg _ _)
        · norm_num
    linarith
  · intro α hα hα1
    have hf : (fun z θ => Gam α θ * z / (1 + z) ^ 2) = fun z θ => Gam α θ * hKer z := by
      funext z θ; rw [hKer_apply, mul_div_assoc]
    have hterm1 : ∀ k ∈ Finset.range (l+1),
        supAbs (fun z θ => (z + 1) ^ k * pzIter k (fun z θ => Gam α θ * hKer z) z θ)
          ≤ (k.factorial : ℝ) * (k + 1) := by
      intro k hk
      apply supAbs_le
      intro z hz θ hθ
      rw [pzIter_decomp k (fun θ => Gam α θ) hKer z θ]
      rw [show (z + 1) ^ k * (Gam α θ * deriv^[k] hKer z)
            = Gam α θ * ((z + 1) ^ k * deriv^[k] hKer z) by ring]
      rw [abs_mul]
      have hGam := Gam_bounds α θ hα hθ
      calc |Gam α θ| * |(z + 1) ^ k * deriv^[k] hKer z|
          ≤ 1 * ((k.factorial : ℝ) * (k + 1)) := by
            apply mul_le_mul
            · rw [abs_of_nonneg hGam.1]; exact hGam.2
            · exact pzIter_hKer_bound k z hz
            · positivity
            · norm_num
        _ = (k.factorial : ℝ) * (k + 1) := one_mul _
    have hterm2 : ∀ j ∈ Finset.range (l+1), ∀ k ∈ Finset.range (l+1),
        (if 1 ≤ j ∧ k + j ≤ l then
          supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j (fun z θ => Gam α θ * hKer z)) z θ
            * (Real.sin (2*θ)) ^ (-(α/5)) / (α + Real.sin (2*θ)))
         else 0)
        ≤ (if 1 ≤ j ∧ k + j ≤ l then (k.factorial : ℝ) * (k+1) * tBound (j-1) 0 else 0) := by
      intro j hj k hk
      split_ifs with hcond
      · obtain ⟨hj1, hjk⟩ := hcond
        apply supAbs_le
        intro z hz θ hθ
        have hDth : DthIter j (fun z θ => Gam α θ * hKer z)
            = fun z θ => dthU^[j] (fun t => Gam α t) θ * hKer z := by
          funext z θ; exact DthIter_decomp j (fun t => Gam α t) hKer z θ
        rw [hDth, pzIter_decomp k (dthU^[j] (fun t => Gam α t)) hKer z θ]
        have hW := gamma_weight_nonneg α θ hα hθ
        rw [mul_div_assoc]
        rw [show (z + 1) ^ k * (dthU^[j] (fun t => Gam α t) θ * deriv^[k] hKer z)
              * (Real.sin (2*θ) ^ (-(α/5)) / (α + Real.sin (2*θ)))
            = dthU^[j] (fun t => Gam α t) θ * ((z + 1) ^ k * deriv^[k] hKer z)
              * (Real.sin (2*θ) ^ (-(α/5)) / (α + Real.sin (2*θ))) by ring]
        rw [abs_mul, abs_mul, abs_of_nonneg hW]
        calc |dthU^[j] (fun t => Gam α t) θ| * |(z + 1) ^ k * deriv^[k] hKer z|
              * (Real.sin (2*θ) ^ (-(α/5)) / (α + Real.sin (2*θ)))
            ≤ (α * tBound (j-1) 0 * Gam α θ) * ((k.factorial : ℝ) * (k+1))
              * (Real.sin (2*θ) ^ (-(α/5)) / (α + Real.sin (2*θ))) := by
              apply mul_le_mul_of_nonneg_right _ hW
              exact mul_le_mul (dthU_Gam_le j hj1 α hα hα1 θ hθ) (pzIter_hKer_bound k z hz)
                (abs_nonneg _)
                (mul_nonneg (mul_nonneg (le_of_lt hα) (tBound_nonneg _ _))
                  (Gam_bounds α θ hα hθ).1)
          _ = ((k.factorial : ℝ) * (k+1)) * tBound (j-1) 0
              * (α * Gam α θ * (Real.sin (2*θ) ^ (-(α/5)) / (α + Real.sin (2*θ)))) := by ring
          _ ≤ ((k.factorial : ℝ) * (k+1)) * tBound (j-1) 0 * 1 := by
              apply mul_le_mul_of_nonneg_left _
                (mul_nonneg (by positivity) (tBound_nonneg _ _))
              show α * Gam α θ
                * (Real.sin (2*θ) ^ (-(α/5)) / (α + Real.sin (2*θ))) ≤ 1
              rw [← mul_div_assoc]
              exact Gam_mul_weight_le α θ hα hθ
          _ = (k.factorial : ℝ) * (k+1) * tBound (j-1) 0 := by ring
      · exact le_refl 0
    have hmain : WlInf α l (fun z θ => Gam α θ * hKer z)
        ≤ (∑ k ∈ Finset.range (l+1), (k.factorial : ℝ) * (k+1))
          + (∑ j ∈ Finset.range (l+1), ∑ k ∈ Finset.range (l+1),
              (if 1 ≤ j ∧ k + j ≤ l then (k.factorial : ℝ) * (k+1) * tBound (j-1) 0 else 0)) := by
      rw [WlInf]
      apply add_le_add
      · exact Finset.sum_le_sum hterm1
      · exact Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hterm2 j hj k hk
    rw [hf]
    linarith [hmain]

end Work.Spaces
