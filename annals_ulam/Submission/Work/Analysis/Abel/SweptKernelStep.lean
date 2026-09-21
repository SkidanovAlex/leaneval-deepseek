import Mathlib
import Submission.Work.Analysis.Abel.SweptKernelDefs
import Submission.Work.Analysis.Abel.SweptKernelExpansion
import Submission.Work.Analysis.Abel.contDiffOn_pder_param
import Submission.Work.Analysis.Abel.hasDerivAt_integral_swept_rpow
import Submission.Work.Analysis.Abel.intervalIntegrable_rpow_sub_mul

/-!
# The induction step for the swept iterated derivative

If `S_j(x) = ∫_x^b ks A p j x σ dσ` (the swept integral of the `j`-th Leibniz expansion of
the kernel `(σ-u)^p A u σ`, `p = n + 1/2`), then for `j ≤ n` the function `S_j` is
differentiable at every `x` in a neighbourhood of `s` with

`S_j'(x) = ∫_x^b ks A p (j+1) x σ dσ = S_{j+1}(x)`,

because the moving-limit boundary term `ks A p j x x = 0` vanishes (all exponents `p - i`
are positive for `i ≤ j ≤ n`) and `∂_x ks A p j x σ = ks A p (j+1) x σ`.
-/

namespace Work.Analysis.Abel

noncomputable section

open scoped ContDiff
open MeasureTheory

/-- **Continuity of the parametrized `u`-derivative slice.** -/
lemma continuousOn_pder_slice {b s δ : ℝ} {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)))
    {y : ℝ} (hy : y ∈ Set.Ioo (s - δ) (s + δ)) (m : ℕ) :
    ContinuousOn (fun σ : ℝ => pder A m y σ) (Set.Ioo (s - δ) (b + δ)) := by
  have hbox : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => pder A m q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)) :=
    contDiffOn_pder_param (isOpen_Ioo.prod isOpen_Ioo) hA m
  have hcomp := ContinuousOn.comp hbox.continuousOn
    ((continuous_const.prodMk continuous_id).continuousOn) (fun σ hσ => ⟨hy, hσ⟩)
  simpa [Function.comp_def] using hcomp

/-- **The swept integral of the `j`-th expansion is the sum of the termwise integrals.** -/
lemma integral_ks_eq_sum {b s δ ρ : ℝ} (hsb : s < b) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρδ : ρ ≤ δ / 4) (hρb : ρ ≤ (b - s) / 4) {n : ℕ} {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)))
    {j : ℕ} (hj : j ≤ n) {y : ℝ} (hy : y ∈ Set.Ioo (s - ρ) (s + ρ)) :
    (∫ σ in y..b, ks A ((n : ℝ) + 1 / 2) j y σ)
      = ∑ i ∈ Finset.range (j + 1), lcoef j i ((n : ℝ) + 1 / 2) *
          ∫ σ in y..b, ((σ - y) ^ (((n : ℝ) + 1 / 2) - i) * pder A (j - i) y σ) := by
  have hyb : y < b := by
    have h1 : y < s + ρ := hy.2
    have h2 : ρ ≤ (b - s) / 4 := hρb
    linarith
  have hyδ : y ∈ Set.Ioo (s - δ) (s + δ) := by
    constructor <;> [linarith [hy.1, hρδ, hρ]; linarith [hy.2, hρδ, hρ]]
  have hint : ∀ i ∈ Finset.range (j + 1),
      IntervalIntegrable (fun σ : ℝ => (σ - y) ^ (((n : ℝ) + 1 / 2) - i) * pder A (j - i) y σ)
        volume y b := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hq : -1 < ((n : ℝ) + 1 / 2) - i := by
      have : (i : ℝ) ≤ n := by exact_mod_cast le_trans hi' hj
      linarith
    have hcont : ContinuousOn (fun σ : ℝ => pder A (j - i) y σ) (Set.Icc y b) :=
      (continuousOn_pder_slice hA hyδ (j - i)).mono (by
        intro σ hσ
        exact ⟨lt_of_lt_of_le hyδ.1 hσ.1, lt_of_le_of_lt hσ.2 (by linarith [hδ])⟩)
    exact intervalIntegrable_rpow_sub_mul hq (le_of_lt hyb) hcont
  have hfun : (fun σ : ℝ => ks A ((n : ℝ) + 1 / 2) j y σ)
      = fun σ : ℝ => ∑ i ∈ Finset.range (j + 1),
          lcoef j i ((n : ℝ) + 1 / 2) * ((σ - y) ^ (((n : ℝ) + 1 / 2) - i) * pder A (j - i) y σ) := by
    funext σ
    simp only [ks]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hint' : ∀ i ∈ Finset.range (j + 1),
      IntervalIntegrable (fun σ : ℝ => lcoef j i ((n : ℝ) + 1 / 2)
        * ((σ - y) ^ (((n : ℝ) + 1 / 2) - i) * pder A (j - i) y σ)) volume y b :=
    fun i hi => (hint i hi).const_mul _
  rw [hfun, intervalIntegral.integral_finsetSum (h := hint')]
  exact Finset.sum_congr rfl (fun i _ => intervalIntegral.integral_const_mul _ _)

end

end Work.Analysis.Abel

namespace Work.Analysis.Abel

noncomputable section

open scoped ContDiff Topology
open MeasureTheory Filter

/-- **The derivative value of the induction step, identified.** -/
lemma sum_integrals_eq_integral_ks {b s δ ρ : ℝ} (hsb : s < b) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρδ : ρ ≤ δ / 4) (hρb : ρ ≤ (b - s) / 4) {n : ℕ} {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)))
    {j : ℕ} (hj : j ≤ n) {y : ℝ} (hy : y ∈ Set.Ioo (s - ρ) (s + ρ)) :
    (∑ i ∈ Finset.range (j + 1), lcoef j i ((n : ℝ) + 1 / 2) *
        ∫ σ in y..b, ((σ - y) ^ (((n : ℝ) + 1 / 2) - i) * pder A (j - i + 1) y σ
          - (((n : ℝ) + 1 / 2) - i) * (σ - y) ^ (((n : ℝ) + 1 / 2) - i - 1)
              * pder A (j - i) y σ))
      = ∫ σ in y..b, ks A ((n : ℝ) + 1 / 2) (j + 1) y σ := by
  set p : ℝ := (n : ℝ) + 1 / 2 with hp
  have hyb : y < b := by
    have h1 : y < s + ρ := hy.2
    linarith [hρb]
  have hyδ : y ∈ Set.Ioo (s - δ) (s + δ) := by
    constructor <;> [linarith [hy.1, hρδ, hρ]; linarith [hy.2, hρδ, hρ]]
  -- integrability of the two families of terms
  have hcont : ∀ m : ℕ, ContinuousOn (fun σ : ℝ => pder A m y σ) (Set.Icc y b) := by
    intro m
    exact (continuousOn_pder_slice hA hyδ m).mono (by
      intro σ hσ
      exact ⟨lt_of_lt_of_le hyδ.1 hσ.1, lt_of_le_of_lt hσ.2 (by linarith [hδ])⟩)
  have hintA : ∀ i ∈ Finset.range (j + 1),
      IntervalIntegrable (fun σ : ℝ => (σ - y) ^ (p - i) * pder A (j - i + 1) y σ) volume y b := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hq : -1 < p - i := by
      have : (i : ℝ) ≤ n := by exact_mod_cast le_trans hi' hj
      simp only [hp]; linarith
    exact intervalIntegrable_rpow_sub_mul hq hyb.le (hcont (j - i + 1))
  have hintB : ∀ i ∈ Finset.range (j + 1),
      IntervalIntegrable (fun σ : ℝ => (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ)
        volume y b := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hq : -1 < p - i - 1 := by
      have : (i : ℝ) ≤ n := by exact_mod_cast le_trans hi' hj
      simp only [hp]; linarith
    have h := (intervalIntegrable_rpow_sub_mul hq hyb.le (hcont (j - i))).const_mul ((p - i))
    simpa [mul_assoc] using h
  have hbr : ∀ i ∈ Finset.range (j + 1),
      IntervalIntegrable (fun σ : ℝ => (σ - y) ^ (p - i) * pder A (j - i + 1) y σ
        - (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ) volume y b :=
    fun i hi => (hintA i hi).sub (hintB i hi)
  -- pull the sum out of and into the integral
  have h1 : (∑ i ∈ Finset.range (j + 1), lcoef j i p *
        ∫ σ in y..b, ((σ - y) ^ (p - i) * pder A (j - i + 1) y σ
          - (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ))
      = ∑ i ∈ Finset.range (j + 1),
          ∫ σ in y..b, lcoef j i p * ((σ - y) ^ (p - i) * pder A (j - i + 1) y σ
            - (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ) :=
    Finset.sum_congr rfl (fun i _ => (intervalIntegral.integral_const_mul _ _).symm)
  rw [h1, ← intervalIntegral.integral_finsetSum (h := fun i hi => (hbr i hi).const_mul _)]
  have hfun : (fun σ : ℝ => ∑ i ∈ Finset.range (j + 1), lcoef j i p *
        ((σ - y) ^ (p - i) * pder A (j - i + 1) y σ
          - (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ))
      = fun σ : ℝ => ks A p (j + 1) y σ := by
    funext σ
    have hsplit : (∑ i ∈ Finset.range (j + 1), lcoef j i p *
        ((σ - y) ^ (p - i) * pder A (j - i + 1) y σ
          - (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ))
        = (∑ i ∈ Finset.range (j + 1), lcoef j i p * (σ - y) ^ (p - i) * pder A (j - i + 1) y σ)
          - (∑ i ∈ Finset.range (j + 1),
              lcoef j i p * (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit, ks_succ_expansion]
  rw [hfun]

/-- **The induction step for the swept iterated derivative.** -/
theorem hasDerivAt_integral_ks_succ {b s δ ρ : ℝ} (hsb : s < b) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρδ : ρ ≤ δ / 4) (hρb : ρ ≤ (b - s) / 4) {n j : ℕ} (hj : j ≤ n) {A : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2)
      (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)))
    {y : ℝ} (hy : y ∈ Set.Ioo (s - ρ) (s + ρ)) :
    HasDerivAt (fun z : ℝ => ∫ σ in z..b, ks A ((n : ℝ) + 1 / 2) j z σ)
      (∫ σ in y..b, ks A ((n : ℝ) + 1 / 2) (j + 1) y σ) y := by
  set p : ℝ := (n : ℝ) + 1 / 2 with hp
  have hyb : y < b := by
    have h1 : y < s + ρ := hy.2
    linarith [hρb]
  have hyρb : y + ρ < b := by
    have h1 : y < s + ρ := hy.2
    linarith [hρb]
  have hbox : Set.Ioo (y - ρ) (y + ρ) ×ˢ Set.Ioo (y - 2 * ρ) (b + ρ)
      ⊆ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ) := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1, hq.1.2, hy.1, hy.2, hρ, hρδ],
            by linarith [hq.1.2, hy.2, hρδ, hρ]⟩,
           ⟨by linarith [hq.2.1, hy.1, hρδ, hρ], by linarith [hq.2.2, hδ, hρ]⟩⟩
  have hterm : ∀ i ∈ Finset.range (j + 1),
      HasDerivAt (fun z : ℝ => lcoef j i p * ∫ σ in z..b, ((σ - z) ^ (p - i) * pder A (j - i) z σ))
        (lcoef j i p * ∫ σ in y..b, ((σ - y) ^ (p - i) * pder A (j - i + 1) y σ
          - (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ)) y := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hq0 : 0 < p - i := by
      have : (i : ℝ) ≤ n := by exact_mod_cast le_trans hi' hj
      simp only [hp]; linarith
    have hB : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => (fun x σ => pder A (j - i) x σ) q.1 q.2)
        (Set.Ioo (y - ρ) (y + ρ) ×ˢ Set.Ioo (y - 2 * ρ) (b + ρ)) := by
      have h0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (fun x σ => pder A (j - i) x σ) q.1 q.2)
          (Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (b + δ)) :=
        contDiffOn_pder_param (isOpen_Ioo.prod isOpen_Ioo) hA (j - i)
      exact (h0.mono hbox).of_le (WithTop.coe_le_coe.mpr le_top)
    have hc := hasDerivAt_integral_swept_rpow (q := p - i) hq0 hρ hyρb hB
    have hc' : HasDerivAt (fun z : ℝ => ∫ σ in z..b, (σ - z) ^ (p - i) * (fun x σ => pder A (j - i) x σ) z σ)
        (∫ σ in y..b, ((σ - y) ^ (p - i) * pder A (j - i + 1) y σ
          - (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ)) y := by
      simpa only [deriv_pder] using hc
    exact hc'.const_mul (lcoef j i p)
  have hbig := HasDerivAt.fun_sum hterm
  have hev : (fun z : ℝ => ∫ σ in z..b, ks A p j z σ) =ᶠ[𝓝 y]
      (fun z : ℝ => ∑ i ∈ Finset.range (j + 1),
        lcoef j i p * ∫ σ in z..b, ((σ - z) ^ (p - i) * pder A (j - i) z σ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    exact integral_ks_eq_sum hsb hδ hρ hρδ hρb hA hj hz
  have h1 := hbig.congr_of_eventuallyEq hev
  have hval := sum_integrals_eq_integral_ks hsb hδ hρ hρδ hρb hA hj hy
  rw [show (∑ i ∈ Finset.range (j + 1), lcoef j i p *
        ∫ σ in y..b, ((σ - y) ^ (p - i) * pder A (j - i + 1) y σ
          - (p - i) * (σ - y) ^ (p - i - 1) * pder A (j - i) y σ))
      = ∫ σ in y..b, ks A p (j + 1) y σ from hval] at h1
  exact h1

end

end Work.Analysis.Abel
