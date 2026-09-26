import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.CuspExp.Models
import Submission.Work.Asymptotics.EtailE.Basic
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Kernels.KMinusSlash
import Submission.Work.Asymptotics.KPlus8FunnelAux
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Compact.gfun_eq
import Submission.Work.Asymptotics.KhatE1.E1combo8_bound
import Submission.Work.Asymptotics.KhatE1.E1combo24_bound
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.EtailE.EtailE_KMinus24
import Submission.Work.Asymptotics.KhatE1.Kdev_funnel_of_leading_core
import Submission.Work.Kernels.LogLambda.ThetaLower.theta_lower_bound
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.KhatE1.B0Defs
import Submission.Work.Asymptotics.KhatE1Core.psi_individual_first_order
import Submission.Work.Asymptotics.KhatE1Core.psi_combo_first_order
import Submission.Work.Asymptotics.funnelTailBasic

set_option maxHeartbeats 4000000

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

/-!
## Funnel coefficient bounds shared with the sharp funnel-tail development

This module collects the parts of the `Kdev` analysis that *other* modules need:
`Sh_ne_zero_of_im_ge`, `R8_p0_eq_e1combo8`, the `z²`-coefficient `z2coef` and the `z¹`-coefficient
`Kdev8Z1` of the `E(z)²`-coefficient of the funnel bracket, together with their funnel bounds.
They are stated here (rather than in `Kdev_cusp0_strip_sharp`) so that downstream modules can
import them without importing the cusp-`0` theorem module.
-/

/-- `Sh τ z ≠ 0` for `Im z ≥ Im τ + 1`. -/
theorem Sh_ne_zero_of_im_ge (τ z : ℍ) (hτ : 2 ≤ τ.im) (hz : τ.im + 1 ≤ z.im) :
    Work.Asymptotics.Compact.Sh τ z ≠ 0 := by
  intro h0
  have hΔ : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hj : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z := by
    have h := Work.Asymptotics.Compact.DeltaFun_mul_sub τ z
    rw [h0, neg_zero] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hΔ)
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hj
  have hzγ : z = γ⁻¹ • τ := by
    rw [← hγ]
    exact (inv_smul_smul γ z).symm
  have h1 : z.im ≤ max τ.im (τ.im)⁻¹ := by
    rw [hzγ]
    exact Work.Kernels.LogLambda.ThetaLower.im_smul_le_max γ⁻¹ τ
  have h2 : max τ.im (τ.im)⁻¹ = τ.im :=
    max_eq_left (le_trans (inv_le_one_of_one_le₀ (by linarith)) (by linarith))
  rw [h2] at h1
  linarith

/-! ## The explicit `E(z)¹`-coefficients of the reference brackets

The reference brackets `Compact.Tref8 = E(z)·R8` and `Compact.Tref24 = E(z)·R24` of the
`K₋`-brackets have `E(z)¹`-coefficients `R8_p0` and `R24_p0`.  The two identifications below
are the first-order part of the sharpness statement: the `E(z)¹`-coefficient of the reference
bracket of `K₋^{(8)}` is exactly `24·E1combo8`, and that of `K₋^{(24)}` is exactly
`E1combo24`; both are `O(‖q(τ)‖ (scale τ)^N)` on the funnel by `E1combo8_bound` /
`E1combo24_bound`.  (The corresponding `E(z)¹`-coefficients of the `K₊`-deviations vanish:
the `K₊`-expansion starts at `E(z)²`.) -/

/-- The `E(z)¹`-coefficient of the reference bracket of `K₋^{(8)}` is `24·E1combo8`. -/
theorem R8_p0_eq_e1combo8 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Compact.R8_p0 ℓ τ = 24 * E1combo8 ℓ τ := by
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hjd : Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ
      = Work.Kernels.E4Fun τ ^ 3 := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  have hj : Work.Kernels.jInvariantFun τ
      = Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := by
    rw [eq_div_iff hΔ, mul_comm]; exact hjd
  by_cases hE4 : Work.Kernels.E4Fun τ = 0
  · simp only [Work.Asymptotics.Compact.R8_p0, E1combo8, Work.Kernels.E14Fun, hj, hE4]
    ring
  · simp only [Work.Asymptotics.Compact.R8_p0, E1combo8, Work.Kernels.E14Fun, hj]
    field_simp
    ring

/-- `B` of the cleared `z²`-identity: `2E₂m₂ + m₁` with `m₂ = E₄²E₆`, `m₁ = 2016E₄Δ − 2E₄⁴`.
It is the stated `B`, and its `q`-expansion vanishes at `q = 0` (`2·1·1·1 + 0 − 2 = 0`). -/
noncomputable def z2B (τ : ℍ) : ℂ :=
  2 * Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ
    + (2016 * Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ - 2 * (Work.Kernels.E4Fun τ) ^ 4)

/-- `A` of the cleared `z²`-identity: `E₂²m₂ + E₂m₁ + m₀` with `m₂ = E₄²E₆`,
`m₁ = 2016E₄Δ − 2E₄⁴`, `m₀ = E₆(E₄³ − 288Δ)`.  It is the stated `A`, and its `q`-expansion
vanishes at `q = 0` because `E₂(0) = E₄(0) = E₆(0) = 1` and `Δ(0) = 0` give `1 + (−2) + 1 = 0`.
(`m₀` is taken in the positive form `E₆(E₄³ − 288Δ)`; with the other sign the constant term
would be `4` instead of `0`.) -/
noncomputable def z2A (τ : ℍ) : ℂ :=
  (Work.Kernels.E2Fun τ) ^ 2 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ
    + Work.Kernels.E2Fun τ
        * (2016 * Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
            - 2 * (Work.Kernels.E4Fun τ) ^ 4)
    + Work.Kernels.E6Fun τ * ((Work.Kernels.E4Fun τ) ^ 3 - 288 * Work.Kernels.DeltaFun τ)

/-- **Step 0 of the `z2AB_bound` bookkeeping:** `z2A` expanded in powers of `u = E₂ − 1`.
The coefficient of `u` is `2E₄²E₆ + 2016E₄Δ − 2E₄⁴`, whose leading term `2 − 2` vanishes, and the
`u²`-term carries `E₄²E₆`; hence, with `‖u‖ ≤ B‖q‖`, `Δ = q + O(q²)`, `E₄ = 1+240q+O(q²)`,
`E₆ = 1−504q+O(q²)`, the whole of `z2A` is `O(q²)`. -/
theorem z2A_expand (τ : ℍ) :
    z2A τ = ((Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ
              + (2016 * Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                  - 2 * (Work.Kernels.E4Fun τ) ^ 4)
              + Work.Kernels.E6Fun τ * ((Work.Kernels.E4Fun τ) ^ 3
                  - 288 * Work.Kernels.DeltaFun τ))
            + (Work.Kernels.E2Fun τ - 1)
                * (2 * (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ
                    + 2016 * Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                    - 2 * (Work.Kernels.E4Fun τ) ^ 4)
            + (Work.Kernels.E2Fun τ - 1) ^ 2
                * ((Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ) := by
  simp only [z2A]
  ring


/-! ## The `q`-order bound for the two `z²`-combinations (`z2A`, `z2B`)

Both combinations vanish at the cusp to order `q`: using the two-term expansions
`E₂² = 1 - 48q + O(q²)`, `E₄ = 1 + 240q + O(q)`, `E₆ = 1 - 504q + O(q)`, `Δ = O(q)`, the
algebraic identities

* `z2A = 2E₄²(E₆ - E₂E₄²) + E₄²E₆(E₂² + E₄ - 2) + Δ(2016E₂E₄ - 288E₆)`,
* `z2B = 2E₄²(E₂E₆ - E₄²) + 2016E₄Δ`

express them as sums of products each carrying one explicit `O(q)` (resp. `O(1)`) factor. -/

/-- `E₄² - 1 = O(q)`. -/
private lemma isBigOq_E4sq_sub_one :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2 - 1) 1 := by
  have h2 : Work.Asymptotics.IsBigOq
      (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1) ^ 2) 2 := by
    have h := (Work.Asymptotics.E4_minus_one).mul (Work.Asymptotics.E4_minus_one)
    simpa only [pow_two] using h
  have h3 : Work.Asymptotics.IsBigOq
      (fun τ : ℍ => 2 * (Work.Kernels.E4Fun τ - 1)) 1 :=
    (Work.Asymptotics.E4_minus_one).const_mul (2 : ℂ)
  refine ((h2.add h3).mono (by norm_num : 1 ≤ min 2 1)).congr (fun τ => ?_)
  ring

/-- `E₆ - E₂E₄² = O(q)`. -/
private lemma isBigOq_E6_sub_E2_E4sq :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E6Fun τ
      - Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ) ^ 2) 1 := by
  have h4 : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2) 0 := by
    have h := (Work.Asymptotics.E4Fun_bdd.mul Work.Asymptotics.E4Fun_bdd).mono (le_refl 0)
    exact h.congr (fun τ => by rw [pow_two])
  have hA := Work.Asymptotics.E6_minus_one
  have hB := ((Work.Asymptotics.E2_minus_one).mul h4).neg
  have hC := (isBigOq_E4sq_sub_one).neg
  refine ((hA.add (hB.add hC)).mono (by norm_num : 1 ≤ min 1 (min 1 1))).congr (fun τ => ?_)
  ring

/-- `E₂² + E₄ - 2 = O(q)`. -/
private lemma isBigOq_E2sq_add_E4_sub_two :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E2Fun τ) ^ 2
      + Work.Kernels.E4Fun τ - 2) 1 := by
  have hA := Work.Asymptotics.E2sq_two_term
  have hB := Work.Asymptotics.E4_minus_one
  have hC : Work.Asymptotics.IsBigOq
      (fun τ : ℍ => (-48 : ℂ) * Work.Kernels.qParamFun τ) 1 :=
    (Work.Asymptotics.qParamFun_isBigOq).const_mul (-48 : ℂ)
  refine ((hA.add (hB.add hC)).mono (by norm_num : 1 ≤ min 2 1)).congr (fun τ => ?_)
  ring

/-- `E₂E₆ - E₄² = O(q)`. -/
private lemma isBigOq_E2E6_sub_E4sq :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ
      - (Work.Kernels.E4Fun τ) ^ 2) 1 := by
  have hAB : Work.Asymptotics.IsBigOq
      (fun τ : ℍ => (Work.Kernels.E2Fun τ - 1) * (Work.Kernels.E6Fun τ - 1)) 1 :=
    ((Work.Asymptotics.E2_minus_one).mul (Work.Asymptotics.E6_minus_one)).mono
      (by norm_num : 1 ≤ 1 + 1)
  have hsum := (hAB.add (Work.Asymptotics.E2_minus_one)).add
    ((Work.Asymptotics.E6_minus_one).add (isBigOq_E4sq_sub_one).neg)
  refine (hsum.mono (by norm_num : 1 ≤ min (min 1 1) (min 1 1))).congr (fun τ => ?_)
  ring

/-- `2016E₂E₄ - 288E₆ = O(1)`. -/
private lemma isBigOq_2016E2E4_sub_288E6 :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => 2016 * Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ
      - 288 * Work.Kernels.E6Fun τ) 0 := by
  have hA : Work.Asymptotics.IsBigOq
      (fun τ : ℍ => 2016 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)) 0 :=
    ((Work.Asymptotics.E2Fun_bdd.mul Work.Asymptotics.E4Fun_bdd)).const_mul (2016 : ℂ)
  have hB : Work.Asymptotics.IsBigOq (fun τ : ℍ => 288 * Work.Kernels.E6Fun τ) 0 :=
    (Work.Asymptotics.E6Fun_bdd).const_mul (288 : ℂ)
  refine (hA.add hB.neg).congr (fun τ => ?_)
  ring



/-- `E₄ + 1 = O(1)`. -/
private lemma isBigOq_E4_add_one :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E4Fun τ + 1) 0 :=
  Work.Asymptotics.E4Fun_bdd.add (Work.Asymptotics.IsBigOq.bounded
    (f := fun _ : ℍ => (1 : ℂ)) 1 (by norm_num) (fun _ _ => by simp))

/-- `E₄² - 1 - 480q = O(q²)`. -/
private lemma isBigOq_E4sq_sub_one_sub :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2 - 1
      - 480 * Work.Kernels.qParamFun τ) 2 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1 - 240
      * Work.Kernels.qParamFun τ) * (Work.Kernels.E4Fun τ + 1)) 2 :=
    (Work.Asymptotics.E4Fun_isBigOq.mul isBigOq_E4_add_one).mono (by norm_num : 2 ≤ 2 + 0)
  have hB : Work.Asymptotics.IsBigOq (fun τ : ℍ => 240 * Work.Kernels.qParamFun τ
      * (Work.Kernels.E4Fun τ - 1)) 2 := by
    have h := ((Work.Asymptotics.qParamFun_isBigOq.mul Work.Asymptotics.E4_minus_one).const_mul
      (240 : ℂ)).mono (by norm_num : 2 ≤ 1 + 1)
    exact h.congr (fun τ => by ring)
  refine ((hA.add hB).mono (by norm_num : 2 ≤ min 2 2)).congr (fun τ => ?_)
  ring

/-- `E₄²E₆ - 1 = O(q)`. -/
private lemma isBigOq_E4sqE6_sub_one :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2
      * Work.Kernels.E6Fun τ - 1) 1 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => ((Work.Kernels.E4Fun τ) ^ 2 - 1)
      * Work.Kernels.E6Fun τ) 1 :=
    (isBigOq_E4sq_sub_one.mul Work.Asymptotics.E6Fun_bdd).mono (by norm_num : 1 ≤ 1 + 0)
  refine ((hA.add Work.Asymptotics.E6_minus_one).mono
    (by norm_num : 1 ≤ min 1 1)).congr (fun τ => ?_)
  ring

/-- `E₆ - E₂E₄² + 960q = O(q²)`. -/
private lemma isBigOq_E6_sub_E2E4sq_add :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E6Fun τ
      - Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ) ^ 2
      + 960 * Work.Kernels.qParamFun τ) 2 := by
  have hD : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E2Fun τ - 1)
      * ((Work.Kernels.E4Fun τ) ^ 2 - 1)) 2 :=
    Work.Asymptotics.E2_minus_one.mul isBigOq_E4sq_sub_one
  refine (((Work.Asymptotics.E6Fun_isBigOq.add
    ((Work.Asymptotics.E2Fun_isBigOq.neg.add isBigOq_E4sq_sub_one_sub.neg).add hD.neg))).mono
      (by norm_num : 2 ≤ min 2 (min 2 2))).congr (fun τ => ?_)
  ring

/-- `E₂² + E₄ - 2 - 192q = O(q²)`. -/
private lemma isBigOq_E2sq_add_E4_sub_two_add :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E2Fun τ) ^ 2 + Work.Kernels.E4Fun τ
      - 2 - 192 * Work.Kernels.qParamFun τ) 2 := by
  refine ((Work.Asymptotics.E2sq_two_term.add Work.Asymptotics.E4Fun_isBigOq).mono
    (by norm_num : 2 ≤ min 2 2)).congr (fun τ => ?_)
  ring

/-- `E₂E₄ - 1 = O(q)`. -/
private lemma isBigOq_E2E4_sub_one :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - 1) 1 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E2Fun τ - 1)
      * (Work.Kernels.E4Fun τ - 1)) 2 :=
    Work.Asymptotics.E2_minus_one.mul Work.Asymptotics.E4_minus_one
  refine ((hA.mono (by norm_num : 1 ≤ 2)).add (Work.Asymptotics.E2_minus_one.add
    Work.Asymptotics.E4_minus_one)).congr (fun τ => ?_)
  ring

/-- `Δ(2016E₂E₄ - 288E₆) - 1728q = O(q²)`. -/
private lemma isBigOq_Delta_2016E2E4_sub_288E6 :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.DeltaFun τ
      * (2016 * Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ
          - 288 * Work.Kernels.E6Fun τ) - 1728 * Work.Kernels.qParamFun τ) 2 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.DeltaFun τ
      - Work.Kernels.qParamFun τ) * (2016 * Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ
          - 288 * Work.Kernels.E6Fun τ)) 2 :=
    (Work.Asymptotics.DeltaFun_isBigOq.mul isBigOq_2016E2E4_sub_288E6).mono
      (by norm_num : 2 ≤ 2 + 0)
  have hB : Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.qParamFun τ
      * (2016 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - 1)
          - 288 * (Work.Kernels.E6Fun τ - 1))) 2 :=
    (Work.Asymptotics.qParamFun_isBigOq.mul
      ((isBigOq_E2E4_sub_one.const_mul (2016 : ℂ)).add
        ((Work.Asymptotics.E6_minus_one.const_mul (288 : ℂ)).neg))).mono
      (by norm_num : 2 ≤ 1 + 1)
  refine ((hA.add hB).mono (by norm_num : 2 ≤ min 2 2)).congr (fun τ => ?_)
  ring

/-- `E₂E₆ - E₄² + 1008q = O(q²)`. -/
private lemma isBigOq_E2E6_sub_E4sq_add :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ
      - (Work.Kernels.E4Fun τ) ^ 2 + 1008 * Work.Kernels.qParamFun τ) 2 := by
  have hAB : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E2Fun τ - 1)
      * (Work.Kernels.E6Fun τ - 1)) 2 :=
    Work.Asymptotics.E2_minus_one.mul Work.Asymptotics.E6_minus_one
  refine ((hAB.add ((Work.Asymptotics.E2Fun_isBigOq.add
    Work.Asymptotics.E6Fun_isBigOq).add isBigOq_E4sq_sub_one_sub.neg)).mono
      (by norm_num : 2 ≤ min 2 (min 2 2))).congr (fun τ => ?_)
  ring

/-- `E₄Δ - q = O(q²)`. -/
private lemma isBigOq_E4Delta_sub_q :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
      - Work.Kernels.qParamFun τ) 2 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1)
      * Work.Kernels.DeltaFun τ) 2 :=
    Work.Asymptotics.E4_minus_one.mul Work.Asymptotics.DeltaFun_isBigOq_one
  refine ((hA.add Work.Asymptotics.DeltaFun_isBigOq).mono
    (by norm_num : 2 ≤ min 2 2)).congr (fun τ => ?_)
  ring

/-- **The `q²`-order bound for `z2A`.** -/
private lemma isBigOq_z2A : Work.Asymptotics.IsBigOq (fun τ : ℍ => z2A τ) 2 := by
  have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ => 2 * ((Work.Kernels.E4Fun τ) ^ 2 - 1)
      * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ
          * (Work.Kernels.E4Fun τ) ^ 2)) 2 := by
    have h := ((isBigOq_E4sq_sub_one.mul isBigOq_E6_sub_E2_E4sq).const_mul (2 : ℂ)).mono
      (by norm_num : 2 ≤ 1 + 1)
    exact h.congr (fun τ => by ring)
  have h2 : Work.Asymptotics.IsBigOq (fun τ : ℍ => 2 * (Work.Kernels.E6Fun τ
      - Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ) ^ 2
      + 960 * Work.Kernels.qParamFun τ)) 2 :=
    (isBigOq_E6_sub_E2E4sq_add).const_mul (2 : ℂ)
  have h3 : Work.Asymptotics.IsBigOq (fun τ : ℍ => ((Work.Kernels.E4Fun τ) ^ 2
      * Work.Kernels.E6Fun τ - 1) * ((Work.Kernels.E2Fun τ) ^ 2
      + Work.Kernels.E4Fun τ - 2)) 2 :=
    (isBigOq_E4sqE6_sub_one.mul isBigOq_E2sq_add_E4_sub_two).mono (by norm_num : 2 ≤ 1 + 1)
  refine (((h1.add h2).add h3).add isBigOq_E2sq_add_E4_sub_two_add).add
    isBigOq_Delta_2016E2E4_sub_288E6 |>.congr (fun τ => ?_)
  simp only [z2A]
  ring

/-- **The `q²`-order bound for `z2B`.** -/
private lemma isBigOq_z2B : Work.Asymptotics.IsBigOq (fun τ : ℍ => z2B τ) 2 := by
  have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ => 2 * ((Work.Kernels.E4Fun τ) ^ 2 - 1)
      * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ
          - (Work.Kernels.E4Fun τ) ^ 2)) 2 := by
    have h := ((isBigOq_E4sq_sub_one.mul isBigOq_E2E6_sub_E4sq).const_mul (2 : ℂ)).mono
      (by norm_num : 2 ≤ 1 + 1)
    exact h.congr (fun τ => by ring)
  have h3 : Work.Asymptotics.IsBigOq (fun τ : ℍ => 2016 * (Work.Kernels.E4Fun τ
      * Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ)) 2 :=
    (isBigOq_E4Delta_sub_q).const_mul (2016 : ℂ)
  refine ((h1.add ((isBigOq_E2E6_sub_E4sq_add).const_mul (2 : ℂ))).add h3).congr (fun τ => ?_)
  simp only [z2B]
  ring

/-- **The `q²`-order bound for `z2A` and `z2B`.** -/
theorem z2AB_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖z2A τ‖ ≤ C * (‖Work.Kernels.qParamFun τ‖ ^ 2) ∧
      ‖z2B τ‖ ≤ C * (‖Work.Kernels.qParamFun τ‖ ^ 2) := by
  obtain ⟨CA, hCA, hA'⟩ := isBigOq_z2A
  obtain ⟨CB, hCB, hB'⟩ := isBigOq_z2B
  refine ⟨max CA CB, by positivity, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  refine ⟨le_trans (hA' τ him) (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
         le_trans (hB' τ him) (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))⟩

/-- **The `q`-order bound for `z2A` and `z2B`.** -/
theorem z2AB_bound_one :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖z2A τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ∧
      ‖z2B τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ := by
  have hE4sq : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2) 0 := by
    have h := (Work.Asymptotics.E4Fun_bdd.mul Work.Asymptotics.E4Fun_bdd).mono (le_refl 0)
    exact h.congr (fun τ => by rw [pow_two])
  have hE4: Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E4Fun τ) 0 :=
    Work.Asymptotics.E4Fun_bdd
  have hE4sqE6 : Work.Asymptotics.IsBigOq
      (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ) 0 :=
    (hE4sq.mul Work.Asymptotics.E6Fun_bdd).mono (by norm_num : 0 ≤ 0 + 0)
  have hD : Work.Asymptotics.IsBigOq Work.Kernels.DeltaFun 1 :=
    Work.Asymptotics.DeltaFun_isBigOq_one
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => z2A τ) 1 := by
    have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ => 2 * ((Work.Kernels.E4Fun τ) ^ 2
        * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * (Work.Kernels.E4Fun τ) ^ 2))) 1 :=
      ((hE4sq.mul isBigOq_E6_sub_E2_E4sq).const_mul (2 : ℂ)).mono (by norm_num : 1 ≤ 0 + 1)
    have h2 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
        (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.E6Fun τ
          * ((Work.Kernels.E2Fun τ) ^ 2 + Work.Kernels.E4Fun τ - 2)) 1 :=
      ((hE4sqE6.mul isBigOq_E2sq_add_E4_sub_two).mono (by norm_num : 1 ≤ 0 + 1))
    have h3 : Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.DeltaFun τ
        * (2016 * Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ
            - 288 * Work.Kernels.E6Fun τ)) 1 :=
      ((hD.mul isBigOq_2016E2E4_sub_288E6).mono (by norm_num : 1 ≤ 1 + 0))
    refine ((h1.add (h2.add h3)).mono (by norm_num : 1 ≤ min 1 1)).congr (fun τ => ?_)
    simp only [z2A]
    ring
  have hB : Work.Asymptotics.IsBigOq (fun τ : ℍ => z2B τ) 1 := by
    have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ => 2 * ((Work.Kernels.E4Fun τ) ^ 2
        * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - (Work.Kernels.E4Fun τ) ^ 2))) 1 :=
      ((hE4sq.mul isBigOq_E2E6_sub_E4sq).const_mul (2 : ℂ)).mono (by norm_num : 1 ≤ 0 + 1)
    have h2 : Work.Asymptotics.IsBigOq (fun τ : ℍ =>
        2016 * Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ) 1 := by
      have h := ((hE4.mul hD).const_mul (2016 : ℂ)).mono (by norm_num : 1 ≤ 0 + 1)
      exact h.congr (fun τ => by ring)
    refine ((h1.add h2).mono (by norm_num : 1 ≤ min 1 1)).congr (fun τ => ?_)
    simp only [z2B]
    ring
  obtain ⟨CA, hCA, hA'⟩ := hA
  obtain ⟨CB, hCB, hB'⟩ := hB
  refine ⟨max CA CB, by positivity, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  have ha := hA' τ him
  have hb := hB' τ him
  simp only [pow_one] at ha hb
  exact ⟨le_trans ha (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)),
         le_trans hb (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩


/-! ## The `z¹`-coefficient of the bracket

The `z¹`-coefficient of `Kdev8BracketE2` is `Kdev8Z1` below; the algebra of `φ₀ = τE₂ - 3i/π`,
`R8_q1 = 3400704E₄ - 3456jE₄`, `Δj = E₄³` reduces it to the `τ`-only combination
`(πτ/3)[j(E₆-E₂E₄)+24(41E₂E₄-11E₆)]`, which vanishes to order `q` at the cusp because
`Δ[j(E₆-E₂E₄)+24(41E₂E₄-11E₆)] = E₄³(E₆-E₂E₄)+24Δ(41E₂E₄-11E₆)` is `O(q²)`. -/

/-- The `z¹`-coefficient of `Kdev8BracketE2` in the `Φᵢ`-form. -/
noncomputable def Kdev8Z1 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Asymptotics.Compact.tailC⁻¹ * (Complex.I / (Real.pi : ℂ)) *
      (-3168 * (τ : ℂ) * Work.Kernels.E6Fun τ
        + 11808 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
        + 12 * Work.Kernels.jInvariantFun τ
            * ((τ : ℂ) * Work.Kernels.E6Fun τ
                - Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ))
    + Complex.I * Work.Asymptotics.Compact.R8_q1 ℓ τ / 3456

/-- **The reduced form of `Kdev8Z1`.** -/
theorem Kdev8Z1_eq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Kdev8Z1 ℓ τ = (Real.pi : ℂ) * (τ : ℂ) / 3 *
      (Work.Kernels.jInvariantFun τ
          * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
        + 24 * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
            - 11 * Work.Kernels.E6Fun τ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, hI2]; ring
  have hI4 : (Complex.I : ℂ) ^ 4 = 1 := by
    calc (Complex.I : ℂ) ^ 4 = ((Complex.I : ℂ) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hI2]; norm_num
  rw [Kdev8Z1, Work.Asymptotics.Compact.tailC, Work.Asymptotics.Compact.R8_q1,
    Work.Kernels.phi0]
  rw [show (-2 : ℤ) = -((2 : ℤ)) by norm_num, zpow_neg, zpow_ofNat]
  field_simp
  ring_nf

/-- `E₄³ - 1 = O(q)`. -/
private lemma isBigOq_E4cube_sub_one :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 3 - 1) 1 := by
  have h24 : Work.Asymptotics.IsBigOq
      (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1) * (Work.Kernels.E4Fun τ - 1)) 2 :=
    (Work.Asymptotics.E4_minus_one).mul (Work.Asymptotics.E4_minus_one)
  have h1 : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ - 1) ^ 3) 3 := by
    have h := (Work.Asymptotics.E4_minus_one).mul h24
    exact h.congr (fun τ => by ring)
  have h2 : Work.Asymptotics.IsBigOq (fun τ : ℍ => 3 * (Work.Kernels.E4Fun τ - 1) ^ 2) 2 := by
    have h := h24.const_mul (3 : ℂ)
    exact h.congr (fun τ => by ring)
  have h3 : Work.Asymptotics.IsBigOq (fun τ : ℍ => 3 * (Work.Kernels.E4Fun τ - 1)) 1 :=
    (Work.Asymptotics.E4_minus_one).const_mul (3 : ℂ)
  refine (((h1.add h2).add h3).mono (by norm_num : 1 ≤ min (min 3 2) 1)).congr (fun τ => ?_)
  ring

/-- `E₆ - E₂E₄ = O(q)`. -/
private lemma isBigOq_E6_sub_E2E4 :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E6Fun τ
      - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ) 1 := by
  have hA := Work.Asymptotics.E6_minus_one
  have hB : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E2Fun τ - 1)
      * Work.Kernels.E4Fun τ) 1 :=
    ((Work.Asymptotics.E2_minus_one).mul Work.Asymptotics.E4Fun_bdd).mono (by norm_num : 1 ≤ 1 + 0)
  have hC := Work.Asymptotics.E4_minus_one
  refine ((hA.add (hB.neg.add hC.neg)).mono (by norm_num : 1 ≤ min 1 (min 1 1))).congr
    (fun τ => ?_)
  ring

/-- `E₆ - E₂E₄ + 720q = O(q²)`. -/
private lemma isBigOq_E6_sub_E2E4_add :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.E6Fun τ
      - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ
      + 720 * Work.Kernels.qParamFun τ) 2 := by
  have hA := Work.Asymptotics.E6Fun_isBigOq
  have hB : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E2Fun τ - 1)
      * (Work.Kernels.E4Fun τ - 1)) 2 :=
    (Work.Asymptotics.E2_minus_one).mul (Work.Asymptotics.E4_minus_one)
  have hC := Work.Asymptotics.E2Fun_isBigOq
  have hD := Work.Asymptotics.E4Fun_isBigOq
  refine ((hA.add ((hB.neg.add hC.neg).add hD.neg)).mono
    (by norm_num : 2 ≤ min 2 (min (min 2 2) 2))).congr (fun τ => ?_)
  ring

/-- `41E₂E₄ - 11E₆ - 30 = O(q)`. -/
private lemma isBigOq_41E2E4_sub_11E6_sub :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => 41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
      - 11 * Work.Kernels.E6Fun τ - 30) 1 := by
  have h2 := Work.Asymptotics.E2_minus_one
  have h4 := Work.Asymptotics.E4_minus_one
  have h6 := Work.Asymptotics.E6_minus_one
  have h24 : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E2Fun τ - 1)
      * (Work.Kernels.E4Fun τ - 1)) 2 := h2.mul h4
  refine ((h2.const_mul (41 : ℂ)).add ((h4.const_mul (41 : ℂ)).add
    (((h24.mono (by norm_num : 1 ≤ 2)).const_mul (41 : ℂ)).add
      ((h6.const_mul (11 : ℂ)).neg)))).congr (fun τ => ?_)
  ring

/-- `41E₂E₄ - 11E₆ = O(1)`. -/
private lemma isBigOq_41E2E4_sub_11E6 :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => 41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
      - 11 * Work.Kernels.E6Fun τ) 0 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => 41 * (Work.Kernels.E2Fun τ
      * Work.Kernels.E4Fun τ)) 0 :=
    ((Work.Asymptotics.E2Fun_bdd.mul Work.Asymptotics.E4Fun_bdd)).const_mul (41 : ℂ)
  have hB : Work.Asymptotics.IsBigOq (fun τ : ℍ => 11 * Work.Kernels.E6Fun τ) 0 :=
    (Work.Asymptotics.E6Fun_bdd).const_mul (11 : ℂ)
  refine (hA.add hB.neg).congr (fun τ => ?_)
  ring

/-- `Δ(41E₂E₄ - 11E₆) - 30q = O(q²)`. -/
private lemma isBigOq_Delta_mul_sub :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.DeltaFun τ
      * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
          - 11 * Work.Kernels.E6Fun τ) - 30 * Work.Kernels.qParamFun τ) 2 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.DeltaFun τ
      - Work.Kernels.qParamFun τ) * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
          - 11 * Work.Kernels.E6Fun τ)) 2 :=
    ((Work.Asymptotics.DeltaFun_isBigOq.mul isBigOq_41E2E4_sub_11E6).mono
      (by norm_num : 2 ≤ 2 + 0))
  have hB : Work.Asymptotics.IsBigOq (fun τ : ℍ => Work.Kernels.qParamFun τ
      * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
          - 11 * Work.Kernels.E6Fun τ - 30)) 2 :=
    ((Work.Asymptotics.qParamFun_isBigOq.mul isBigOq_41E2E4_sub_11E6_sub).mono
      (by norm_num : 2 ≤ 1 + 1))
  refine ((hA.add hB).mono (by norm_num : 2 ≤ min 2 2)).congr (fun τ => ?_)
  ring

/-- `E₄³(E₆ - E₂E₄) + 24Δ(41E₂E₄ - 11E₆) = O(q²)`. -/
private lemma isBigOq_z1combo :
    Work.Asymptotics.IsBigOq (fun τ : ℍ => (Work.Kernels.E4Fun τ) ^ 3
      * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
      + 24 * (Work.Kernels.DeltaFun τ
          * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
              - 11 * Work.Kernels.E6Fun τ))) 2 := by
  have hA : Work.Asymptotics.IsBigOq (fun τ : ℍ => ((Work.Kernels.E4Fun τ) ^ 3 - 1)
      * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)) 2 :=
    ((isBigOq_E4cube_sub_one.mul isBigOq_E6_sub_E2E4).mono (by norm_num : 2 ≤ 1 + 1))
  have hB := isBigOq_E6_sub_E2E4_add
  have hC : Work.Asymptotics.IsBigOq (fun τ : ℍ => 24 * (Work.Kernels.DeltaFun τ
      * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
          - 11 * Work.Kernels.E6Fun τ)
      - 30 * Work.Kernels.qParamFun τ)) 2 :=
    (isBigOq_Delta_mul_sub).const_mul (24 : ℂ)
  refine (((hA.add hB).add hC).mono (by norm_num : 2 ≤ min (min 2 2) 2)).congr (fun τ => ?_)
  ring

/-- **The `q`-order bound for the `z¹`-coefficient of the bracket.** -/
theorem Kdev8Z1_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖Kdev8Z1 ℓ τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C2, hC2, h2⟩ := isBigOq_z1combo
  obtain ⟨cd, hcd, hd⟩ := Work.Asymptotics.exists_Delta_Funnel_lower
  have hCpos : (0 : ℝ) < Real.pi / 3 * (C2 / cd) + 1 := by
    have h1 : (0 : ℝ) < Real.pi / 3 * (C2 / cd) :=
      mul_pos (div_pos Real.pi_pos (by norm_num)) (div_pos hC2 hcd)
    linarith
  refine ⟨Real.pi / 3 * (C2 / cd) + 1, 1, hCpos, by norm_num, fun τ hτ => ?_⟩
  rw [Kdev8Z1_eq]
  have him : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  have hDne : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hdq : cd * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ := hd τ hτ
  have hqpos : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  have hnum : ‖(Work.Kernels.E4Fun τ) ^ 3
      * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
      + 24 * (Work.Kernels.DeltaFun τ
          * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
              - 11 * Work.Kernels.E6Fun τ))‖
      ≤ C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2 := h2 τ him
  have hkey : (Work.Kernels.jInvariantFun τ
        * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
      + 24 * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
          - 11 * Work.Kernels.E6Fun τ))
      = ((Work.Kernels.E4Fun τ) ^ 3
          * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
        + 24 * (Work.Kernels.DeltaFun τ
            * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
                - 11 * Work.Kernels.E6Fun τ))) / Work.Kernels.DeltaFun τ := by
    rw [eq_div_iff hDne, ← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
    ring
  rw [hkey]
  rw [show (Real.pi : ℂ) * (τ : ℂ) / 3 * (((Work.Kernels.E4Fun τ) ^ 3
        * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
        + 24 * (Work.Kernels.DeltaFun τ
            * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
                - 11 * Work.Kernels.E6Fun τ))) / Work.Kernels.DeltaFun τ)
      = ((Real.pi : ℂ) * (τ : ℂ) / 3 * ((Work.Kernels.E4Fun τ) ^ 3
        * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
        + 24 * (Work.Kernels.DeltaFun τ
            * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
                - 11 * Work.Kernels.E6Fun τ)))) / Work.Kernels.DeltaFun τ by ring]
  rw [norm_div, norm_mul]
  have hstep : ‖((Work.Kernels.E4Fun τ) ^ 3
        * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
        + 24 * (Work.Kernels.DeltaFun τ
            * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
                - 11 * Work.Kernels.E6Fun τ)))‖ / ‖Work.Kernels.DeltaFun τ‖
      ≤ (C2 / cd) * ‖Work.Kernels.qParamFun τ‖ := by
    have hbase : ‖((Work.Kernels.E4Fun τ) ^ 3
        * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
        + 24 * (Work.Kernels.DeltaFun τ
            * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
                - 11 * Work.Kernels.E6Fun τ)))‖ / ‖Work.Kernels.DeltaFun τ‖
        ≤ C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2
            / (cd * Real.exp (-(2 * Real.pi * τ.im))) :=
      div_le_div₀ (mul_nonneg hC2.le (by positivity)) hnum (mul_pos hcd hqpos) hdq
    have hq : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
      Work.Asymptotics.norm_qParamFun τ
    have hfac : C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2
          / (cd * Real.exp (-(2 * Real.pi * τ.im)))
        = (C2 / cd) * ‖Work.Kernels.qParamFun τ‖ := by
      rw [hq]; field_simp
    rwa [hfac] at hbase
  have hnorm : ‖(Real.pi : ℂ) * (τ : ℂ) / 3‖ ≤ Real.pi / 3 * Work.Kernels.scale τ := by
    have h1 : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
    have h3 : ‖(Real.pi : ℂ) * (τ : ℂ) / 3‖ = Real.pi / 3 * ‖(τ : ℂ)‖ := by
      rw [show (Real.pi : ℂ) * (τ : ℂ) / 3 = ((Real.pi / 3 : ℝ) : ℂ) * (τ : ℂ) by
        push_cast; ring]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 3)]
    rw [h3]
    exact mul_le_mul_of_nonneg_left h1 (div_nonneg Real.pi_pos.le (by norm_num))
  calc ‖(Real.pi : ℂ) * (τ : ℂ) / 3‖ * ‖((Work.Kernels.E4Fun τ) ^ 3
        * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
        + 24 * (Work.Kernels.DeltaFun τ
            * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
                - 11 * Work.Kernels.E6Fun τ)))‖ / ‖Work.Kernels.DeltaFun τ‖
      = ‖(Real.pi : ℂ) * (τ : ℂ) / 3‖ * (‖((Work.Kernels.E4Fun τ) ^ 3
        * (Work.Kernels.E6Fun τ - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
        + 24 * (Work.Kernels.DeltaFun τ
            * (41 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ)
                - 11 * Work.Kernels.E6Fun τ)))‖ / ‖Work.Kernels.DeltaFun τ‖) := by ring
    _ ≤ (Real.pi / 3 * Work.Kernels.scale τ) * ((C2 / cd) * ‖Work.Kernels.qParamFun τ‖) :=
        mul_le_mul hnorm hstep (div_nonneg (norm_nonneg _) (norm_nonneg _))
          (le_trans (norm_nonneg _) hnorm)
    _ = (Real.pi / 3 * (C2 / cd)) * (Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖) := by ring
    _ ≤ (Real.pi / 3 * (C2 / cd) + 1)
          * (Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖) := by
        refine mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) (norm_nonneg _))
    _ = (Real.pi / 3 * (C2 / cd) + 1) * ‖Work.Kernels.qParamFun τ‖
          * (Work.Kernels.scale τ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]; ring


/-- The `z²`-coefficient `z2coef` of `M2plus`, in the form produced by `ΦMain + ΦDiv + ΦCorr`. -/
noncomputable def z2coef (τ : ℍ) : ℂ :=
  Work.Asymptotics.Compact.tailC⁻¹ *
    (Work.Kernels.jInvariantFun τ
        * (2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
            - (τ : ℂ) * Work.Kernels.E6Fun τ)
      + 288 * (τ : ℂ) * Work.Kernels.E6Fun τ
      - 2016 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
      - Work.Asymptotics.Compact.phi2t τ * (Work.Kernels.E4Fun τ) ^ 2
          * Work.Kernels.E6Fun τ / Work.Kernels.DeltaFun τ)

/-- **The cleared `z²`-identity.**  Multiplying `z2coef` by `Δ` and clearing `jΔ = E₄³`:
`Δ·(tailC·z2coef) = −(τ·A − (3i/π)·B)` with the explicit `A = z2A`, `B = z2B` whose
`q`-expansions start at order `q`.  This is the algebraic half of `M2_z2_bound`; the analytic
half is `‖z2A‖ ≤ C‖q‖`, `‖z2B‖ ≤ C‖q‖`, i.e. the `E2E4E6_combo_decay` mechanism. -/
theorem z2_cleared (τ : ℍ) :
    Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC *
        (Work.Asymptotics.Compact.tailC⁻¹ *
          (Work.Kernels.jInvariantFun τ
              * (2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                  - (τ : ℂ) * Work.Kernels.E6Fun τ)
            + 288 * (τ : ℂ) * Work.Kernels.E6Fun τ
            - 2016 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
            - Work.Asymptotics.Compact.phi2t τ * (Work.Kernels.E4Fun τ) ^ 2
                * Work.Kernels.E6Fun τ / Work.Kernels.DeltaFun τ)))
      = -((τ : ℂ) * z2A τ - (3 * Complex.I / (Real.pi : ℂ)) * z2B τ) := by
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have htC : Work.Asymptotics.Compact.tailC ≠ 0 := Work.Asymptotics.Compact.tailC_ne_zero
  have hjj : Work.Kernels.jInvariantFun τ
      = (Work.Kernels.E4Fun τ) ^ 3 / Work.Kernels.DeltaFun τ := by
    rw [eq_div_iff hΔ]
    rw [mul_comm]
    exact Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  rw [hjj]
  simp only [z2A, z2B, Work.Kernels.phi0, Work.Asymptotics.Compact.phi2t]
  field_simp
  ring


/-- **The `q`-order bound for the `z²`-coefficient of the bracket.** -/
theorem z2coef_bound :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖z2coef τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C2, hC2, h2⟩ := z2AB_bound
  obtain ⟨cd, hcd, hd⟩ := Work.Asymptotics.exists_Delta_Funnel_lower
  have htC0 : (0 : ℝ) < ‖Work.Asymptotics.Compact.tailC‖ :=
    norm_pos_iff.mpr Work.Asymptotics.Compact.tailC_ne_zero
  have htCne : Work.Asymptotics.Compact.tailC ≠ 0 := Work.Asymptotics.Compact.tailC_ne_zero
  refine ⟨(2 * C2) / (cd * ‖Work.Asymptotics.Compact.tailC‖) + 1, 1, by positivity,
    by norm_num, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  have hΔne : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hΔ := hd τ hτ
  obtain ⟨hA2, hB2⟩ := h2 τ hτ
  have hqpos : (0 : ℝ) < ‖Work.Kernels.qParamFun τ‖ :=
    norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ)
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := hqpos.le
  have htC : (0 : ℝ) ≤ ‖Work.Asymptotics.Compact.tailC‖ := htC0.le
  have hΔ' : cd * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    rw [Work.Asymptotics.norm_qParamFun]; exact hΔ
  have hkey : z2coef τ = -((τ : ℂ) * z2A τ - (3 * Complex.I / (Real.pi : ℂ)) * z2B τ)
      / (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC) := by
    rw [eq_div_iff (mul_ne_zero hΔne htCne)]
    calc z2coef τ * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC)
        = Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC * z2coef τ) := by ring
      _ = -((τ : ℂ) * z2A τ - (3 * Complex.I / (Real.pi : ℂ)) * z2B τ) := z2_cleared τ
  have h3 : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    have h3n : ‖(3 : ℂ)‖ = 3 := by norm_num
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [norm_div, norm_mul, hpi, Complex.norm_I, mul_one, h3n]
  have hnum : ‖(τ : ℂ) * z2A τ - (3 * Complex.I / (Real.pi : ℂ)) * z2B τ‖
      ≤ (‖(τ : ℂ)‖ + 3 / Real.pi) * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
    calc ‖(τ : ℂ) * z2A τ - (3 * Complex.I / (Real.pi : ℂ)) * z2B τ‖
        ≤ ‖(τ : ℂ) * z2A τ‖ + ‖(3 * Complex.I / (Real.pi : ℂ)) * z2B τ‖ := norm_sub_le _ _
      _ = ‖(τ : ℂ)‖ * ‖z2A τ‖ + (3 / Real.pi) * ‖z2B τ‖ := by rw [norm_mul, norm_mul, h3]
      _ ≤ ‖(τ : ℂ)‖ * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
            + (3 / Real.pi) * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hA2 (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hB2 (by positivity))
      _ = (‖(τ : ℂ)‖ + 3 / Real.pi) * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by ring
  have h1 : ‖z2coef τ‖
      ≤ (‖(τ : ℂ)‖ + 3 / Real.pi) * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
          / (cd * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Asymptotics.Compact.tailC‖) := by
    rw [hkey, norm_div, norm_neg, norm_mul]
    exact le_trans (div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos (mul_pos hcd hqpos) htC0)
        (mul_le_mul_of_nonneg_right hΔ' htC))
      (div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos (mul_pos hcd hqpos) htC0)))
  have h2' : (‖(τ : ℂ)‖ + 3 / Real.pi) * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
      / (cd * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Asymptotics.Compact.tailC‖)
      ≤ (2 * C2 / (cd * ‖Work.Asymptotics.Compact.tailC‖))
          * (Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖) := by
    rw [div_le_iff₀ (mul_pos (mul_pos hcd hqpos) htC0)]
    have ht : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
    have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hpi3 : (3 : ℝ) / Real.pi ≤ Work.Kernels.scale τ := by
      refine le_trans ?_ hs
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
    have hR : (2 * C2 / (cd * ‖Work.Asymptotics.Compact.tailC‖))
        * (Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖)
        * (cd * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Asymptotics.Compact.tailC‖)
        = 2 * C2 * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
      field_simp
    rw [hR]
    calc (‖(τ : ℂ)‖ + 3 / Real.pi) * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2)
        ≤ (2 * Work.Kernels.scale τ) * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith)
            (mul_nonneg hC2.le (by positivity))
      _ = 2 * C2 * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by ring
  refine le_trans (le_trans h1 h2') ?_
  rw [Real.rpow_one]
  have hC2cd : (0 : ℝ) ≤ 2 * C2 / (cd * ‖Work.Asymptotics.Compact.tailC‖) := by positivity
  have hs : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  calc (2 * C2 / (cd * ‖Work.Asymptotics.Compact.tailC‖))
        * (Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖)
      ≤ (2 * C2 / (cd * ‖Work.Asymptotics.Compact.tailC‖) + 1)
          * (Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hs hq0)
    _ = (2 * C2 / (cd * ‖Work.Asymptotics.Compact.tailC‖) + 1)
          * ‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ := by ring



/-!
## The analytic half of `M2_z2_bound`, matched to the template

Correction to the first orders below (checked by running the linearization rather than trusting
the earlier hand value): with `E₂ = 1+u`, `E₄ = 1+A` where `A = 240q+a`, `E₆ = 1+B` where
`B = −504q+b`, `Δ = q+d`, the expansion of `z2A` is, order by order,
`1 − 2 + 1 = 0` at order zero and `(2u − 24q + 2a + b) + (96q − 2u) + (−72q + b) =
(2u − 2u) + (−24+96−72)q + (2a+2b)` at order one.  The `u`-terms cancel *between the first and
the second summand* and the `q`-coefficient is exactly zero, so the survivor is `2a + 2b`.
Hence `z2A = O(q²)` and `z2B = O(q²)` — stronger than the stated `‖·‖ ≤ C‖q‖`, and consistent
with the 40-digit sweep (`≤ 1.32`, `≤ 1.70`, decaying like `q`).  The four inputs are exactly
`Residues.DeltaExpansion` (`Δ = (Ept τ)² + O(‖Ept τ‖⁴)`, i.e. `q + O(q²)` since
`(Ept τ)² = qParamFun τ`), `Residues.E4FunSecondOrder`, `Residues.E6FunSecondOrder`, and
`Rigidity.E2Fun_sub_one_decay` (only first order is needed: no second-order statement for `E₂`
is required, because its contribution cancels).  What is left is the finite polynomial
bookkeeping of that expansion against those four bounds, ending in
`‖z2A‖, ‖z2B‖ ≤ C‖q‖² ≤ C‖q‖` on the funnel (there `‖q‖ ≤ e^{-4π} ≤ 1`).

`M2_z2_bound` now reads: `z2_cleared` (proved) plus the two `q`-order bounds for the explicit
combinations

  `z2A = E₂²m₂ + E₂m₁ + m₀`, `m₂ = E₄²E₆`, `m₁ = 2016E₄Δ − 2E₄⁴`, `m₀ = E₆(E₄³ − 288Δ)`,
  `z2B = 2E₂m₂ + m₁`.

Their constant terms vanish (`E₂(0)=E₄(0)=E₆(0)=1`, `Δ(0)=0`).  Matching the combo against the
proved template `Work.Asymptotics.E2E4E6_combo_decay` (whose mechanism is
`E2_qExpansion_coeff` / `E4_qExpansion_coeff` / `E6_qExpansion_coeff` plus
`Rigidity.hasSum_qExpansion_cusp_decay`) and using the proved two-term expansions
`E₂ = 1 − 24q + O(q²)`, `E₄ = 1 + 240q + O(q²)` (`E4FunSecondOrder`),
`E₆ = 1 − 504q + O(q²)` (`E6FunSecondOrder`), `Δ = q + O(q²)`, the first orders come out as

  `z2A = −48 q + O(q²)`,   `z2B = O(q²)`,

so `A, B ∈ q·ℂ[[q]]` and `‖bracket‖ = ‖tailC⁻¹(τ A − (3i/π)B)‖ ≤ C(1+|τ|)‖q‖`, which is exactly
`M2_z2_bound` with `N = 1, 2` (and `1 + |τ| ≤ 2·scale`).  The remaining Lean work is the
instance of that template for these two combos — the same shape as `E2E4E6_combo_decay`, one
order higher, with the first-order arithmetic above as the target.

## What the second-order algebra needs (identified)

An independent verification of the intended bound
`‖Bℓτz‖ ≤ C‖q(τ)‖(scale τ)^N(1+t)^M‖E(z)‖²` for the bracket `B` of the matching section below
— carried out at 250 digits with a model that reproduces the proved identities `Tref8_eq`,
`decomp8`, `KMinus_eq`, `KPlus8_sub_Gplus8_decomp` to more than 250 digits — gives
`N = 3`, `M = 0` and ratio `≤ 5·10⁵` on the grid `τ = 0.3 + iy` with `y ∈ {4,…,40}`,
`z = x+it`, `x ∈ {0, 0.25, 0.5, 0.75, 1}` (so the *whole strip*, not only `x = 0`) and
`t ∈ {y+1, y+2, 2y}`.  The same model shows the exact identity
`B ℓ τ z = 2·KhatE1.KdevRem ℓ τ z` (`Submission/Work/Asymptotics/KhatE1Core/Kdev8_matching_bridge.lean`,
proved), so the matching is *equivalent* to `KdevRem_strip_sharp` / `Kdev_strip_sharp8_core`.

The one ingredient the first-order computation (`KhatE1/E1combo8_bound.lean`) uses, and which
the second-order one must use as well, is that `ψ₂` and `ψ₄` have to be **unfolded**,
`ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S`, `ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` (with `ξ₂, ξ₄` the Jacobi quartic
combinations of `θ₀₀⁴, θ₀₁⁴, θ₁₀⁴`), and that the resulting combination of quartic identities
must be applied: as opaque `τ`-atoms, `ψ₂, ψ₄` do *not* satisfy enough algebraic relations for
the `E(z)^k` coefficients (`k = 2, …, 6`) to cancel.  This is the same mechanism as
`E1combo8_bound`, one order higher.

## The `z²`-piece of the `e²`-coefficient, reduced to a known `q`-expansion identity

The `z²`-coefficient of `M2plus + M2minus` is the `z²`-coefficient of `M2plus` (`M2minus` is
affine in `z`), namely the `τ`-only bracket

  `tailC⁻¹·[ j(2φ₀E₄ − τE₆) + 288τE₆ − 2016φ₀E₄ − φ₂t·E₄²E₆/Δ ]`.

Two independent checks identify it: it equals `-f₄` of `Submission/Work/Rigidity/Counterexample.lean`,
i.e. `-(φ₂t·(E₄²E₆/Δ) + φ₀E₄(2016−2j) + τE₆(j−288))`, and with `j = E₄³/Δ`, `Δ = (E₄³−E₆²)/1728`,
`φ₀ = τE₂−3i/π`, `φ₂t = τE₂²−(6i/π)E₂` it expands as `Σ_{n≥1}(τA_n − (3i/π)B_n)qⁿ` with
`A = E₂²m₂+E₂m₁+m₀`, `B = 2E₂m₂+m₁` and `A, B ∈ q·ℂ[[q]]` (`A = −518400q + O(q²)`).  Hence
`‖·‖ ≤ C(1+|τ|)‖q‖` on the funnel, which is the statement
`Work.Asymptotics.KhatE1Core.M2_z2_bound` (independently re-verified at 400 digits: the ratio
`‖·‖/‖q‖` grows like `scale^1.65`, uniformly for `Re τ ∈ [−1,1]`, `Im τ ≥ 2`).

The Lean input needed is exactly the *first* step of the template
`Work.Asymptotics.E2E4E6_combo_decay` (`12(E₂−1) − 3(E₄−1) − 2(E₆−1) = O(q²)`, proved from
`E2_qExpansion_coeff`/`E4_qExpansion_coeff`/`E6_qExpansion_coeff` and
`Rigidity.hasSum_qExpansion_cusp_decay`): one more instance of "a combination of `E₂, E₄, E₆, Δ`
whose `q`-expansion coefficients vanish to order one", with the coefficients read off the proved
two-term expansions.  No `ψ₂, ψ₄` unfolding is needed for this piece.

## The `E(z)²`-coefficients of the two sides (verified template)

With `e := Ept z` the identity of the section below reads
`2·(Kdev - c₁e) = M` where `M = tailC⁻¹(Φ₁+Φ₂+Φ₃) + (3456π)⁻¹(e(R8-R8_p0) + Dev8Sum)`, and the
core is `M = O(‖q τ‖(scale τ)^N(1+t)^M e²)`.  Writing `M = M₂e² + M₃e³ + …` (`M` has no `e⁰`- or
`e¹`-term), the `e²`-coefficient splits as `M₂ = M2plus + M2minus` with

* `M2plus` — the `e²`-coefficient of `tailC⁻¹(Φ₁+Φ₂+Φ₃)`, i.e. of the `K₊`-deviation: the
  `e²`-parts of `ΦMain`, `ΦDiv`, `ΦCorr`, using `E₂(z) = 1+O(e²)`, `E₄(z) = 1+240e²+O(e⁴)`,
  `E₆(z) = 1-504e²+O(e⁴)`, `Δ(z) = e²(1-24e²+O(e⁴))`, `j(z) = e^{-2}+744+O(e²)`,
  `phitVec(z,1) = z²-6iz/π+O(e²)`, `phitVec(z,2) = z²-12iz/π-36/π²+O(e²)`;
* `M2minus` — the `e²`-coefficient of `(3456π)⁻¹(e(R8-R8_p0)+Dev8Sum)`, i.e. of the `K₋`-side:
  `(3456π)⁻¹(Xc·R8_q1 + R8_p1)` (the deviation `Dev8Raw` of the bracket starts at `e³`, so it
  contributes nothing at `e²`).

Both formulas are explicit in the `τ`-atoms `E₂,E₄,E₆,Δ,j,ψ₂,ψ₄`, `φ₀,φ₂` and the `z`-polynomial,
and were checked against the kernel model at high precision: `M2plus` agrees with
`(K₊^{(8)}-𝒢₊^{(8)})/e²` to more than 17 digits (`τ = 4i`, `t = 10,12,14,16,20`), `M2minus`
agrees with `-(K₋^{(8)}-𝒢₋^{(8)}-c₁e)/e²` at `τ = 4i`, `t = 6,8,10`, and `M2plus + M2minus`
satisfies `‖M2plus+M2minus‖ ≤ 10⁴·‖q τ‖·(scale τ)²·(1+t)⁴` on the tested lattice
`τ ∈ {2i,…,6i}`, `t ∈ {Im τ+1, Im τ+3, Im τ+6}` — the `e²`-cancellation that the core requires.
The residual is *not* an algebraic consequence of `E1combo8`/`Λ`/`ψ₄E₈-ψ₂E₁₀` alone: the
`τ`-atoms' analytic relations (the `q`-expansions, `2πiE₂' = (E₂²-E₄)/12`,
`Δ = (E₄³-E₆²)/1728`) enter, which is what makes this coefficient the genuine content of the core.

## The precise remaining computation

Write `e := Ept z` (so `‖e‖ = e^{-πt}`) and `2c₁ := E1combo8/(144π)`.  Combining

* `Compact.Khat8_sub_Ghat8_eq`  (`Kdev = tailC⁻¹(Φ₁+Φ₂+Φ₃)/2 + (3456π)⁻¹ (Sh)⁻¹(br+Sh·br0)/2`),
* `Compact.decomp8`             (`(Sh)⁻¹(br+Sh·br0) = Tref8 + Dev8Sum`, `Sh_ne_zero_of_im_ge`),
* `Compact.Tref8_eq`            (`Tref8 = e·R8`),
* `R8_p0_eq_e1combo8`           (`R8_p0 = 24·E1combo8`, i.e. `(3456π)⁻¹·e·R8_p0 = 2c₁·e`),

one gets the exact identity

  `2·(Kdev ℓ 8 τ z - c₁·e) = tailC⁻¹(Φ₁+Φ₂+Φ₃) + (3456π)⁻¹·(e·(R8 ℓ τ z - R8_p0 ℓ τ) + Dev8Sum ℓ τ z)`

for `τ ∈ 𝔽`, `z` in the strip, `t ≥ Im τ + 1`.  Since `e·(R8 - R8_p0) = e²(Xc·R8_q1+R8_p1) + …`,
the core is therefore *equivalent* to the bound

  `‖tailC⁻¹(Φ₁+Φ₂+Φ₃) + (3456π)⁻¹·(e·(R8-R8_p0) + Dev8Sum)‖ ≤ C‖q τ‖(scale τ)^N(1+t)^M·‖e‖²`,

i.e. to the **matching** of the two exact decompositions at the orders `e⁰, e¹, e², e³, e⁴`:

* the `e⁰`- and `e¹`-coefficients vanish, because the `K₊`-expansion starts at `e²` (the paper's
  `n_{+,z} = 2`) and `Dev8Raw = O(e³)` (its atoms `dW, dL, dD2` are `O(e³)`, `dE6, dE8` are
  `O(e⁴)` and `dSinv = O(e⁴)`);
* the `e²`-, `e³`- and `e⁴`-coefficients cancel between `tailC⁻¹(Φ₁+Φ₂+Φ₃)` and
  `(3456π)⁻¹(Xc·R8_q1+R8_p1)` (resp. `(3456π)⁻¹` times the corresponding coefficients of `R8`)
  down to `O(‖q τ‖(scale τ)^N(1+t)^M)`; equivalently the `τ`-atoms' low-order `e^{πiτ}`-parts
  cancel, which is the same kind of `τ`-atom identity as `E1combo8_bound`
  (`j(ψ₄-ψ₂E₆/E₄) + 576(2E₄-ψ₄) = O(q)`), `Work.FunnelNumerics.Lamb_funnel_bound`
  (`ψ₂E₁₄/Δ - jψ₄ = -Λ`) and `ψ₄E₈ - ψ₂E₁₀ = O(q)`.

For `d = 24` the same identity holds with `R24`, `R24_p0 = E1combo24` (`R24_p0_eq_e1combo24`)
and `Dev24Sum`; the coefficient of `e` is then `E1combo24/(6912π)`, which is likewise
`O(‖q τ‖ (scale τ)^N)` by `E1combo24_bound`.  The cone of `τ`-atoms, the `z`-atom expansions
(`E4FunSecondOrder`, `E6FunSecondOrder`, `cusp_invDelta`, `cusp_W_second`, `cusp_D_second`,
`cusp_L_second`, `E14Fun_sub_one_atom`, …) and the order calculus (`IsBigOq`, `IsBigOe`) needed
for this computation are all available in the workspace; what is missing is the explicit
second-order `τ`-atom algebra. -/
end Work.Asymptotics.KhatE1
