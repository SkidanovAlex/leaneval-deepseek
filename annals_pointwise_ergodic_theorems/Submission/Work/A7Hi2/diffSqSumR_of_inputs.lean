import Mathlib
import Submission.Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded_large
import Submission.Work.A7Hi2.sqfn_khintchine_finsupp
import Submission.Work.A7Hi2.sqfn_lp_of_finsupp

/-!
# The `ℓᵖ` square-function bound for the real-scale difference family

This module proves `Work.A7Hi2.diffSqSumR_of_inputs`: from the three analytic inputs for the
*linearised* difference kernels `linDiffKernR K σ ρ U ω`

* the size bound (`hsize`, sup-norm of the kernel),
* the discrete Hörmander condition (`hhorm`),
* the `ℓ²` bound (`hl2`),

one gets, for every `1 < p`, a constant `C > 0` with

`‖ (∑'_n |∑'_j diffKernR K (σ n) (ρ n) j · f (x - j)|²)^{1/2} ‖_{ℓᵖ} ≤ C ‖f‖_{ℓᵖ}`

for all `2`-lacunary comparable real scale families `σ`, `ρ` and all `f : ℤ → ℂ`.

The proof has three steps, the first of which is done here:

1. (`linDiffKernR_lin_lp`) the discrete Calderón–Zygmund theorem
   (`Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded[_large]`) applied to the
   linearised kernel `linDiffKernR K σ ρ F ω` produces the *linearised* `ℓᵖ` bound, uniformly in
   `σ`, `ρ`, `F` and `ω` (the hypotheses `hsize`, `hhorm`, `hl2` are exactly its three inputs);
2. (`Work.A7Hi2.sqfn_khintchine_finsupp`) Khintchine's inequality converts the linearised bound
   (for finitely supported inputs) into the square function bound for finitely supported inputs;
3. (`Work.A7Hi2.sqfn_lp_of_finsupp`) a Fatou/truncation argument removes the finite-support
   restriction.

The last two steps are independent of the analytic inputs and are proved in the sibling modules
`Submission/Work/A7Hi2/sqfn_khintchine_finsupp.lean` and
`Submission/Work/A7Hi2/sqfn_lp_of_finsupp.lean`.
-/

set_option autoImplicit false

namespace Work.A7Hi2

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Two elementary auxiliary lemmas -/

/-- Reindexing a convolution sum: `∑_y k (x - y) g y = ∑_y k y g (x - y)`. -/
lemma tsum_conv_reindex (k : ℤ → ℂ) (g : ℤ → ℂ) (x : ℤ) :
    (∑' y : ℤ, k (x - y) * g y) = ∑' y : ℤ, k y * g (x - y) := by
  have := Equiv.tsum_eq (Equiv.subLeft x) (fun z : ℤ => k z * g (x - z))
  simpa [Equiv.subLeft_apply] using this

/-- A finitely supported function has finite `ℓᵖ`-norm for every positive exponent. -/
lemma summable_norm_rpow_of_finSupp {g : ℤ → ℂ}
    (hg : ∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → g x = 0) {q : ℝ} (hq : 0 < q) :
    Summable (fun n : ℤ => ‖g n‖ ^ q) := by
  obtain ⟨t, ht⟩ := hg
  refine summable_of_ne_finset_zero (s := t) fun n hn => ?_
  rw [ht n hn, norm_zero, Real.zero_rpow (ne_of_gt hq)]

/-! ## Step 1: the linearised `ℓᵖ` bound from the three analytic inputs -/

/-- **The discrete Calderón–Zygmund `ℓᵖ` bound for the linearised difference kernels.**

The three hypotheses are exactly the size, Hörmander and `ℓ²` inputs of the target; the
conclusion is the `ℓᵖ`-boundedness of the linearised operator
`g ↦ (n ↦ ∑'_y (∑_{l ∈ F} ω_l · diffKernR K (σ l) (ρ l) y) · g (n - y))`, uniformly in the
lacunary comparable scale families `σ`, `ρ`, the finite index set `F` and the sign pattern `ω`,
for finitely supported inputs. -/
theorem linDiffKernR_lin_lp (p : ℝ) (hp : 1 < p) (K : SchwartzMap ℝ ℂ)
    (hsize : ∃ B : ℝ, 0 < B ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (ω : ℕ → Bool) (z : ℤ),
      ‖linDiffKernR K σ ρ U ω z‖ ≤ B)
    (hhorm : ∃ A : ℝ, 0 < A ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (ω : ℕ → Bool) (y : ℤ), y ≠ 0 →
      ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
        ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ≤ ENNReal.ofReal A)
    (hl2 : ∃ A : ℝ, 0 < A ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      Summable f →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ U ω (x - y) * f y)
          2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal A * MeasureTheory.eLpNorm f 2
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (F : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
      (∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → g x = 0) →
      MeasureTheory.eLpNorm (fun n : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω y * g (n - y))
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  obtain ⟨B, _hBpos, hsizeB⟩ := hsize
  obtain ⟨A₂, hA₂pos, hl2A⟩ := hl2
  obtain ⟨Ak, hAkpos, hhormA⟩ := hhorm
  -- the target's `ℓ²` hypothesis is stated with `*`; the CZ statements use `•`
  have hl2smul : ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (F : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      Summable f →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω (x - y) • f y)
          2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal A₂ * MeasureTheory.eLpNorm f 2
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    intro σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω f hf
    have h := hl2A σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω f hf
    have hfun2 : (fun x : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω (x - y) • f y)
        = fun x : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω (x - y) * f y :=
      funext fun x => tsum_congr fun y => smul_eq_mul _ _
    rw [hfun2]
    exact h
  rcases lt_trichotomy p 2 with hp2 | hp2eq | hp2
  · -- ## `p < 2`: the `p < 2` case of the discrete Calderón–Zygmund theorem
    obtain ⟨Ccz, hCczpos, hcz⟩ :=
      Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded (H := ℂ) hp hp2
    refine ⟨Ccz * (24 * A₂ ^ 2 + 4 * Ak + 100) ^ (2 / p - 1) * A₂ ^ (2 - 2 / p),
      mul_pos (mul_pos hCczpos (Real.rpow_pos_of_pos (by positivity) _))
        (Real.rpow_pos_of_pos hA₂pos _), ?_⟩
    intro σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω g hg
    have hgoal := hcz (fun y : ℤ => linDiffKernR K σ ρ F ω y) A₂ Ak B hA₂pos (le_of_lt hAkpos)
      (fun z => hsizeB σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω z)
      (fun y hy => hhormA σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω y hy)
      (fun f hf => hl2smul σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω f hf)
      g (summable_norm_rpow_of_finSupp hg (lt_trans zero_lt_one hp))
    have hfun : (fun x : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω (x - y) • g y)
        = fun n : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω y * g (n - y) := by
      funext x
      rw [tsum_congr fun y => smul_eq_mul _ _]
      exact tsum_conv_reindex _ g x
    rw [hfun] at hgoal
    exact hgoal
  · -- ## `p = 2`: the `ℓ²` hypothesis itself
    subst hp2eq
    refine ⟨A₂, hA₂pos, ?_⟩
    intro σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω g hg
    obtain ⟨t, ht⟩ := hg
    have hgoal := hl2A σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω g (summable_of_ne_finset_zero ht)
    have hfun : (fun x : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω (x - y) * g y)
        = fun n : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω y * g (n - y) :=
      funext fun x => tsum_conv_reindex _ g x
    rw [hfun] at hgoal
    simpa only [ENNReal.ofReal_ofNat] using hgoal
  · -- ## `2 < p`: duality, via the `p < 2` case at the dual exponent
    obtain ⟨Ccz, hCczpos, hcz⟩ :=
      Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded_large (H := ℂ) hp2
    refine ⟨Ccz * (24 * A₂ ^ 2 + 4 * Ak + 100) ^ (2 / (p / (p - 1)) - 1)
        * A₂ ^ (2 - 2 / (p / (p - 1))),
      mul_pos (mul_pos hCczpos (Real.rpow_pos_of_pos (by positivity) _))
        (Real.rpow_pos_of_pos hA₂pos _), ?_⟩
    intro σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω g hg
    have hgoal := hcz (fun y : ℤ => linDiffKernR K σ ρ F ω y) A₂ Ak B hA₂pos (le_of_lt hAkpos)
      (fun z => hsizeB σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω z)
      (fun y hy => hhormA σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω y hy)
      (fun f hf => hl2smul σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω f hf)
      g (summable_norm_rpow_of_finSupp hg (lt_trans zero_lt_one hp))
    have hfun : (fun x : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω (x - y) • g y)
        = fun n : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ F ω y * g (n - y) := by
      funext x
      rw [tsum_congr fun y => smul_eq_mul _ _]
      exact tsum_conv_reindex _ g x
    rw [hfun] at hgoal
    exact hgoal

/-! ## The target -/

theorem diffSqSumR_of_inputs (p : ℝ) (hp : 1 < p) (K : SchwartzMap ℝ ℂ)
    (hsize : ∃ B : ℝ, 0 < B ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (ω : ℕ → Bool) (z : ℤ),
      ‖linDiffKernR K σ ρ U ω z‖ ≤ B)
    (hhorm : ∃ A : ℝ, 0 < A ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (ω : ℕ → Bool) (y : ℤ), y ≠ 0 →
      ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
        ‖linDiffKernR K σ ρ U ω (x - y) - linDiffKernR K σ ρ U ω x‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ≤ ENNReal.ofReal A)
    (hl2 : ∃ A : ℝ, 0 < A ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      Summable f →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ U ω (x - y) * f y)
          2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal A * MeasureTheory.eLpNorm f 2
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm
          (fun x : ℤ => (∑' n : ℕ, ‖∑' j : ℤ, diffKernR K (σ n) (ρ n) j * f (x - j)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  obtain ⟨C₁, hC₁pos, hK⟩ := sqfn_khintchine_finsupp p hp
  obtain ⟨C', hC'pos, hCZ⟩ := linDiffKernR_lin_lp p hp K hsize hhorm hl2
  refine ⟨C₁ * C', by positivity, ?_⟩
  intro σ ρ hσ1 hσ2 hρ1 hρ2 hcmp f
  have hlin : ∀ (F : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
      (∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → g x = 0) →
      MeasureTheory.eLpNorm
          (fun n : ℤ => ∑' y : ℤ,
            (∑ l ∈ F, Work.KMTAreas.ADev.bSign ω l * diffKernR K (σ l) (ρ l) y) * g (n - y))
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C' * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    intro F ω g hg
    have h := hCZ σ ρ hσ1 hσ2 hρ1 hρ2 hcmp F ω g hg
    simpa only [linDiffKernR] using h
  have hfin := hK (fun l : ℕ => diffKernR K (σ l) (ρ l)) C' hC'pos hlin
  exact sqfn_lp_of_finsupp p (lt_trans zero_lt_one hp) _ (C₁ * C') (by positivity) hfin f

end

end Work.A7Hi2
