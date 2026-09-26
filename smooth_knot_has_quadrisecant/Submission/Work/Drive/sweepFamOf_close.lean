import Mathlib
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.sweepBlurFacts

/-!
# The double blur of a Lipschitz loop family is close to it

`Work.Drive.sweepFamOf Γ δ₁ δ₂` is the double bump-blur of an arbitrary continuous loop family `Γ`:

`sweepFamOf Γ δ₁ δ₂ s t = ∫ v in (-1)..1, sweepBump v • ∫ u in (-1)..1, sweepBump u •
    Γ (s - δ₂ v) (t - δ₁ u)`.

Because the bump `sweepBump` has total mass one, this is a *weighted average* of the values of `Γ`
over the box `[s - δ₂, s + δ₂] × [t - δ₁, t + δ₁]`.  Hence if `Γ` is Lipschitz with constants `M`
(in the loop parameter `t`) and `N` (in the sweep parameter `s`), the double blur differs from `Γ`
by at most `M δ₁ + N δ₂` everywhere:

`Work.Drive.sweepFamOf_close`.

The proof is the elementary three-term estimate: the inner blur differs from `Γ (s - δ₂ v) t` by at
most `M δ₁`; the outer blur differs from `Γ s t` by at most `N δ₂`; and the difference between the
double blur and the outer blur of the *unblurred* inner values is again at most `M δ₁` (integrate
the pointwise bound). -/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral
open MeasureTheory

/-! ## 1. Two elementary integral estimates -/

/-- **The bump average of a bounded function is bounded by the same constant.**  Since `sweepBump`
is nonnegative with total mass one, `∫ sweepBump u • g u` is a convex combination of values of `g`. -/
lemma norm_bumpAvg_le {g : ℝ → Space} (hg : Continuous g) {C : ℝ}
    (hC : ∀ u : ℝ, ‖g u‖ ≤ C) :
    ‖∫ u in (-1 : ℝ)..1, sweepBump u • g u‖ ≤ C := by
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
  have h1 : IntervalIntegrable (fun u : ℝ => ‖sweepBump u • g u‖) volume (-1 : ℝ) 1 :=
    ((sweepBump_continuous.smul hg).norm).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun u : ℝ => sweepBump u * C) volume (-1 : ℝ) 1 :=
    ((sweepBump_continuous.mul continuous_const)).intervalIntegrable _ _
  refine (intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) h1 h2 ?_).trans ?_
  · intro u _
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
    exact mul_le_mul_of_nonneg_left (hC u) (sweepBump_nonneg u)
  · rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-- **Blurring is a small perturbation.**  If `f` is continuous and oscillates by at most `ε` over
every window of length `2δ`, then the blur of `f` with the bump `sweepBump` at any scale
`|δ'| ≤ δ` is within `ε` of `f`, pointwise. -/
lemma bump_blur_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) {ε δ δ' : ℝ} (hε : 0 ≤ ε)
    (hbd : ∀ t h : ℝ, |h| ≤ δ → ‖f (t + h) - f t‖ ≤ ε) (hδ : |δ'| ≤ δ) (t : ℝ) :
    ‖(∫ u in (-1 : ℝ)..1, sweepBump u • f (t - δ' * u)) - f t‖ ≤ ε := by
  have hcont : Continuous (fun u : ℝ => sweepBump u • f (t - δ' * u)) :=
    sweepBump_continuous.smul
      (hf.comp (continuous_const.sub (continuous_const.mul continuous_id)))
  have hcont' : Continuous (fun u : ℝ => sweepBump u • (f (t - δ' * u) - f t)) :=
    sweepBump_continuous.smul
      ((hf.comp (continuous_const.sub (continuous_const.mul continuous_id))).sub
        continuous_const)
  have hconstcont : Continuous (fun u : ℝ => sweepBump u • f t) :=
    sweepBump_continuous.smul continuous_const
  have hconst : (∫ u in (-1 : ℝ)..1, sweepBump u • f t) = f t := by
    rw [intervalIntegral.integral_smul_const, integral_sweepBump, one_smul]
  have hdiff : (∫ u in (-1 : ℝ)..1, sweepBump u • f (t - δ' * u)) - f t
      = ∫ u in (-1 : ℝ)..1, sweepBump u • (f (t - δ' * u) - f t) := by
    nth_rewrite 1 [← hconst]
    rw [← intervalIntegral.integral_sub (hcont.intervalIntegrable (-1) 1)
      (hconstcont.intervalIntegrable (-1) 1)]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [smul_sub]
  rw [hdiff]
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
  have hpt : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖sweepBump u • (f (t - δ' * u) - f t)‖ ≤ sweepBump u * ε := by
    intro u hu
    rw [Set.mem_Icc] at hu
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
    have habs : |δ' * u| ≤ δ := by
      rw [abs_mul]
      calc |δ'| * |u| ≤ |δ'| * 1 :=
            mul_le_mul_of_nonneg_left (abs_le.mpr hu) (abs_nonneg _)
        _ = |δ'| := by ring
        _ ≤ δ := hδ
    have habs' : |-(δ' * u)| ≤ δ := by simpa using habs
    have h := hbd t (-(δ' * u)) habs'
    have h' : ‖f (t - δ' * u) - f t‖ ≤ ε := by
      simpa [show t + -(δ' * u) = t - δ' * u by ring] using h
    exact mul_le_mul_of_nonneg_left h' (sweepBump_nonneg u)
  have hmono : (∫ u in (-1 : ℝ)..1, ‖sweepBump u • (f (t - δ' * u) - f t)‖)
      ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * ε :=
    intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
      ((hcont'.norm).intervalIntegrable (-1) 1)
      ((sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1) hpt
  calc (∫ u in (-1 : ℝ)..1, ‖sweepBump u • (f (t - δ' * u) - f t)‖)
      ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * ε := hmono
    _ = ε := by rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-! ## 2. The double blur of a Lipschitz family -/

/-- **The double blur is within `M δ₁ + N δ₂` of the family.** -/
theorem sweepFamOf_close_aux
    (Γ : ℝ → ℝ → Space) (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    {M N : ℝ} (hMnn : 0 ≤ M) (hNnn : 0 ≤ N)
    (hM : ∀ s t₁ t₂ : ℝ, ‖Γ s t₁ - Γ s t₂‖ ≤ M * |t₂ - t₁|)
    (hN : ∀ s₁ s₂ t : ℝ, ‖Γ s₁ t - Γ s₂ t‖ ≤ N * |s₂ - s₁|)
    {δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (s t : ℝ) :
    ‖sweepFamOf Γ δ₁ δ₂ s t - Γ s t‖ ≤ M * δ₁ + N * δ₂ := by
  -- The inner blur is within `M δ₁` of `Γ` at the same outer parameter.
  have hinner : ∀ σ τ : ℝ, ‖(∫ u in (-1 : ℝ)..1, sweepBump u • Γ σ (τ - δ₁ * u)) - Γ σ τ‖
      ≤ M * δ₁ := by
    intro σ τ
    have hf : Continuous (fun τ' : ℝ => Γ σ τ') :=
      hΓ.comp (continuous_const.prodMk continuous_id)
    have hbd : ∀ a h : ℝ, |h| ≤ δ₁ → ‖Γ σ (a + h) - Γ σ a‖ ≤ M * δ₁ := by
      intro a h hh
      have h1 : ‖Γ σ (a + h) - Γ σ a‖ ≤ M * |a - (a + h)| := hM σ (a + h) a
      rw [show a - (a + h) = -h by ring, abs_neg] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hh hMnn)
    exact bump_blur_close (f := fun τ' : ℝ => Γ σ τ') (ε := M * δ₁) (δ := δ₁) (δ' := δ₁)
      hf (mul_nonneg hMnn hδ₁) hbd (by rw [abs_of_nonneg hδ₁]) τ
  -- The outer blur of `s ↦ Γ s t` is within `N δ₂` of `Γ s t`.
  have houter : ‖(∫ v in (-1 : ℝ)..1, sweepBump v • Γ (s - δ₂ * v) t) - Γ s t‖ ≤ N * δ₂ := by
    have hf : Continuous (fun σ : ℝ => Γ σ t) :=
      hΓ.comp (continuous_id.prodMk continuous_const)
    have hbd : ∀ a h : ℝ, |h| ≤ δ₂ → ‖Γ (a + h) t - Γ a t‖ ≤ N * δ₂ := by
      intro a h hh
      have h1 : ‖Γ (a + h) t - Γ a t‖ ≤ N * |a - (a + h)| := hN (a + h) a t
      rw [show a - (a + h) = -h by ring, abs_neg] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hh hNnn)
    exact bump_blur_close (f := fun σ : ℝ => Γ σ t) (ε := N * δ₂) (δ := δ₂) (δ' := δ₂)
      hf (mul_nonneg hNnn hδ₂) hbd (by rw [abs_of_nonneg hδ₂]) s
  -- Continuity of the inner blur in the outer parameter.
  have hinner_cont : Continuous
      (fun v : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u)) := by
    have hf : Continuous (fun p : ℝ × ℝ => sweepBump p.2 • Γ (s - δ₂ * p.1) (t - δ₁ * p.2)) := by
      refine (sweepBump_continuous.comp continuous_snd).smul ?_
      exact hΓ.comp ((continuous_const.sub (continuous_const.mul continuous_fst)).prodMk
        (continuous_const.sub (continuous_const.mul continuous_snd)))
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun v u : ℝ => sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u)) hf (-1) 1
    simpa using h
  have hQcont : Continuous (fun v : ℝ => Γ (s - δ₂ * v) t) :=
    hΓ.comp ((continuous_const.sub (continuous_const.mul continuous_id)).prodMk continuous_const)
  -- The double blur differs from the outer blur of the *unblurred* inner values by `M δ₁`.
  have hmid : ‖sweepFamOf Γ δ₁ δ₂ s t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (s - δ₂ * v) t)‖
      ≤ M * δ₁ := by
    have hInt1 : IntervalIntegrable
        (fun v : ℝ => sweepBump v • (∫ u in (-1 : ℝ)..1, sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u)))
        volume (-1) 1 := (sweepBump_continuous.smul hinner_cont).intervalIntegrable _ _
    have hInt2 : IntervalIntegrable (fun v : ℝ => sweepBump v • Γ (s - δ₂ * v) t) volume (-1) 1 :=
      (sweepBump_continuous.smul hQcont).intervalIntegrable _ _
    have hdiff : sweepFamOf Γ δ₁ δ₂ s t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (s - δ₂ * v) t)
        = ∫ v in (-1 : ℝ)..1, sweepBump v •
            ((∫ u in (-1 : ℝ)..1, sweepBump u • Γ (s - δ₂ * v) (t - δ₁ * u))
              - Γ (s - δ₂ * v) t) := by
      unfold sweepFamOf
      rw [← intervalIntegral.integral_sub hInt1 hInt2]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [smul_sub]
    rw [hdiff]
    exact norm_bumpAvg_le (hinner_cont.sub hQcont) (fun v => hinner (s - δ₂ * v) t)
  have hsplit : sweepFamOf Γ δ₁ δ₂ s t - Γ s t
      = (sweepFamOf Γ δ₁ δ₂ s t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (s - δ₂ * v) t))
        + ((∫ v in (-1 : ℝ)..1, sweepBump v • Γ (s - δ₂ * v) t) - Γ s t) :=
    (sub_add_sub_cancel _ _ _).symm
  rw [hsplit]
  calc ‖(sweepFamOf Γ δ₁ δ₂ s t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (s - δ₂ * v) t))
        + ((∫ v in (-1 : ℝ)..1, sweepBump v • Γ (s - δ₂ * v) t) - Γ s t)‖
      ≤ ‖sweepFamOf Γ δ₁ δ₂ s t - (∫ v in (-1 : ℝ)..1, sweepBump v • Γ (s - δ₂ * v) t)‖
        + ‖(∫ v in (-1 : ℝ)..1, sweepBump v • Γ (s - δ₂ * v) t) - Γ s t‖ := norm_add_le _ _
    _ ≤ M * δ₁ + N * δ₂ := add_le_add hmid houter

open LeanEval.KnotTheory.Quadrisecant in
theorem sweepFamOf_close
    (Γ : ℝ → ℝ → Space) (hΓ : Continuous (fun p : ℝ × ℝ => Γ p.1 p.2))
    {M N : ℝ} (hMnn : 0 ≤ M) (hNnn : 0 ≤ N)
    (hM : ∀ s t₁ t₂ : ℝ, ‖Γ s t₁ - Γ s t₂‖ ≤ M * |t₂ - t₁|)
    (hN : ∀ s₁ s₂ t : ℝ, ‖Γ s₁ t - Γ s₂ t‖ ≤ N * |s₂ - s₁|)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ δ₁ δ₂ : ℝ, 0 ≤ δ₁ → δ₁ ≤ L → 0 ≤ δ₂ → δ₂ ≤ L → ∀ s t : ℝ,
      ‖Work.Drive.sweepFamOf Γ δ₁ δ₂ s t - Γ s t‖ ≤ ε := by
  have hden : (0 : ℝ) < 2 * (M + N + 2) := by linarith
  have hLpos : (0 : ℝ) < ε / (2 * (M + N + 2)) := div_pos hε hden
  refine ⟨ε / (2 * (M + N + 2)), hLpos, ?_⟩
  intro δ₁ δ₂ hδ₁0 hδ₁L hδ₂0 hδ₂L s t
  have hMδ₁ : M * δ₁ ≤ ε / 2 := by
    calc M * δ₁ ≤ M * (ε / (2 * (M + N + 2))) := mul_le_mul_of_nonneg_left hδ₁L hMnn
      _ = (M / (2 * (M + N + 2))) * ε := by ring
      _ ≤ (1 / 2) * ε := by
          refine mul_le_mul_of_nonneg_right ?_ hε.le
          rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
          linarith
      _ = ε / 2 := by ring
  have hNδ₂ : N * δ₂ ≤ ε / 2 := by
    calc N * δ₂ ≤ N * (ε / (2 * (M + N + 2))) := mul_le_mul_of_nonneg_left hδ₂L hNnn
      _ = (N / (2 * (M + N + 2))) * ε := by ring
      _ ≤ (1 / 2) * ε := by
          refine mul_le_mul_of_nonneg_right ?_ hε.le
          rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
          linarith
      _ = ε / 2 := by ring
  calc ‖sweepFamOf Γ δ₁ δ₂ s t - Γ s t‖
      ≤ M * δ₁ + N * δ₂ := sweepFamOf_close_aux Γ hΓ hMnn hNnn hM hN hδ₁0 hδ₂0 s t
    _ ≤ ε / 2 + ε / 2 := add_le_add hMδ₁ hNδ₂
    _ = ε := by ring

end Work.Drive
