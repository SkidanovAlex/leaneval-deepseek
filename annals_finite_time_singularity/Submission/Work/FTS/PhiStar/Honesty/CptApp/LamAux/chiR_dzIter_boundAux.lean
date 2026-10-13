/-
# `Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux`

**The `D_z`-jets of the radial cut-off `chiR n` are bounded, uniformly in `n`.**

This is a copy of `Work.FTS.PhiStar.Honesty.CptApp.cutRadialBound` (proved in
`Submission/Work/FTS/PhiStar/Honesty/CptApp/cutRadialBound.lean`) placed in its own namespace
and with the import of `CptApp.cutBasic` removed.  The copy exists because
`CptApp.cutBasic` and `CptApp.lamDzDeriv` declare the *same* name
`Work.FTS.PhiStar.Honesty.CptApp.zetaR_eq_zero_of_ge` (with different hypotheses), so no module
may import both; the estimate `lam_Dz_sq_le` needs `lamDzDeriv` (smoothness of the moment
`lam n F`) and therefore must obtain the cut-off bound from a module whose import cone avoids
`cutBasic`.

The proof is described in the header of `cutRadialBound.lean`: the two steps
`psiLo n = 𝕋 (n z − 1)`, `psiHi n = 𝕋 (2 − z/n)` (`𝕋 = Real.smoothTransition`) satisfy
`chiR n = psiLo n · psiHi n`, their weighted plain derivatives `z^k ∂^k` are bounded by the
weighted-derivative constants of `𝕋` (uniformly in `n`), the binomial product rule bounds the
weighted derivatives of the product, and the Stirling expansion `D_z^b = ∑_{k ≤ b} S(b,k) z^k ∂^k`
assembles the result.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.GalBasis.cc.psiCut_cutA_bound
import Submission.Work.FTS.LocData.DzIter_oneSubChi_bound
import Submission.Work.Coercivity.CommutZBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.LamAux

local notation "𝕋" => Real.smoothTransition

/-! ## 1. The two steps whose product is `chiR n`, in affine form -/

/-- The lower step of `chiR n`: `𝕋 (n z − 1)`, in the affine form `𝕋 (λ z + a)` with
`λ = n`, `a = −1`. -/
def psiLo (n : ℕ) (z : ℝ) : ℝ := 𝕋 ((n : ℝ) * z + (-1))

/-- The upper step of `chiR n`: `𝕋 (2 − z/n)`, in the affine form `𝕋 (λ z + a)` with
`λ = −1/n`, `a = 2` (valid also for `n = 0`, where both expressions are the constant `2`). -/
def psiHi (n : ℕ) (z : ℝ) : ℝ := 𝕋 ((-(n : ℝ)⁻¹) * z + 2)

/-- **The factorisation of `chiR n`.** -/
theorem chiR_eq_psiLo_mul_psiHi (n : ℕ) :
    Work.FTS.PhiStar.Honesty.CptApp.chiR n = fun z => psiLo n z * psiHi n z := by
  funext z
  simp only [Work.FTS.PhiStar.Honesty.CptApp.chiR, Work.FTS.PhiStar.Honesty.CptApp.cut01,
    psiLo, psiHi]
  have h1 : (n : ℝ) * z - 1 = (n : ℝ) * z + (-1) := by ring
  have h2 : (2 : ℝ) - z / (n : ℝ) = -(n : ℝ)⁻¹ * z + 2 := by
    rw [div_eq_mul_inv]; ring
  rw [h1, h2]

theorem contDiff_psiLo (n : ℕ) : ContDiff ℝ Work.Stability.smoothOrder (psiLo n) := by
  have hlin : ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ => (n : ℝ) * z + (-1)) :=
    ((contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (n : ℝ))).mul
        contDiff_id).add
      (contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (-1 : ℝ)))
  exact Real.smoothTransition.contDiff.comp hlin

theorem contDiff_psiHi (n : ℕ) : ContDiff ℝ Work.Stability.smoothOrder (psiHi n) := by
  have hlin : ContDiff ℝ Work.Stability.smoothOrder (fun z : ℝ => (-(n : ℝ)⁻¹) * z + 2) :=
    ((contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (-(n : ℝ)⁻¹))).mul
        contDiff_id).add
      (contDiff_const : ContDiff ℝ Work.Stability.smoothOrder (fun _ : ℝ => (2 : ℝ)))
  exact Real.smoothTransition.contDiff.comp hlin

/-! ## 2. The weighted derivatives of a rescaled step -/

theorem weighted_deriv_exp (F : ℝ → ℝ) (hF : ∀ m : ℕ, ContDiff ℝ m F) (lam a₀ : ℝ) :
    ∀ (k : ℕ) (z : ℝ), z ^ k * iteratedDeriv k (fun z => F (lam * z + a₀)) z
      = (lam * z + a₀ - a₀) ^ k * iteratedDeriv k F (lam * z + a₀) := by
  intro k z
  have hchain : iteratedDeriv k (fun z => F (lam * z + a₀)) z
      = lam ^ k * iteratedDeriv k F (lam * z + a₀) :=
    Work.FTS.GalBasis.cc.iteratedDeriv_comp_mul_add F hF lam a₀ k z
  rw [hchain, ← mul_assoc, ← mul_pow,
    show z * lam = lam * z + a₀ - a₀ by ring]

/-- The weighted derivatives of the lower step, uniformly in `n`. -/
theorem weighted_deriv_psiLo {A : ℕ → ℝ}
    (hA : ∀ (a : ℕ) (u : ℝ), |(u - (-1)) ^ a * iteratedDeriv a 𝕋 u| ≤ A a) :
    ∀ (n k : ℕ) (z : ℝ), |z ^ k * iteratedDeriv k (psiLo n) z| ≤ A k := by
  intro n k z
  show |z ^ k * iteratedDeriv k (fun z => 𝕋 ((n : ℝ) * z + (-1))) z| ≤ A k
  rw [weighted_deriv_exp 𝕋 Work.FTS.GalBasis.cc.contDiff_smoothTransition (n : ℝ) (-1) k z]
  exact hA k ((n : ℝ) * z + (-1))

/-- The weighted derivatives of the upper step, uniformly in `n`. -/
theorem weighted_deriv_psiHi {B : ℕ → ℝ}
    (hB : ∀ (b : ℕ) (v : ℝ), |(v - 2) ^ b * iteratedDeriv b 𝕋 v| ≤ B b) :
    ∀ (n k : ℕ) (z : ℝ), |z ^ k * iteratedDeriv k (psiHi n) z| ≤ B k := by
  intro n k z
  show |z ^ k * iteratedDeriv k (fun z => 𝕋 ((-(n : ℝ)⁻¹) * z + 2)) z| ≤ B k
  rw [weighted_deriv_exp 𝕋 Work.FTS.GalBasis.cc.contDiff_smoothTransition (-(n : ℝ)⁻¹) 2 k z]
  exact hB k ((-(n : ℝ)⁻¹) * z + 2)

/-! ## 3. The product rule for the weighted derivatives -/

/-- **Binomial product bound.** -/
theorem weighted_deriv_prod {A B : ℕ → ℝ}
    (hAnn : ∀ a : ℕ, 0 ≤ A a)
    (hA : ∀ (a : ℕ) (u : ℝ), |(u - (-1)) ^ a * iteratedDeriv a 𝕋 u| ≤ A a)
    (hB : ∀ (b : ℕ) (v : ℝ), |(v - 2) ^ b * iteratedDeriv b 𝕋 v| ≤ B b) :
    ∀ (n k : ℕ) (z : ℝ),
      |z ^ k * iteratedDeriv k (fun z => psiLo n z * psiHi n z) z| ≤
        ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * A a * B (k - a) := by
  intro n k z
  have hsm1 : ContDiff ℝ (k : WithTop ℕ∞) (psiLo n) :=
    (contDiff_psiLo n).of_le (by simp)
  have hsm2 : ContDiff ℝ (k : WithTop ℕ∞) (psiHi n) :=
    (contDiff_psiHi n).of_le (by simp)
  have hkey : iteratedDeriv k (fun z => psiLo n z * psiHi n z) z
      = ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ)
          * iteratedDeriv a (psiLo n) z * iteratedDeriv (k - a) (psiHi n) z :=
    iteratedDeriv_mul hsm1.contDiffAt hsm2.contDiffAt
  have hsplit : z ^ k * iteratedDeriv k (fun z => psiLo n z * psiHi n z) z
      = ∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ)
          * ((z ^ a * iteratedDeriv a (psiLo n) z)
             * (z ^ (k - a) * iteratedDeriv (k - a) (psiHi n) z)) := by
    rw [hkey, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hzk : z ^ a * z ^ (k - a) = z ^ k := by rw [← pow_add, Nat.add_sub_cancel' ha']
    rw [← hzk]
    ring
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun a _ => ?_)
  have hX : |z ^ a * iteratedDeriv a (psiLo n) z| ≤ A a := weighted_deriv_psiLo hA n a z
  have hY : |z ^ (k - a) * iteratedDeriv (k - a) (psiHi n) z| ≤ B (k - a) :=
    weighted_deriv_psiHi hB n (k - a) z
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (k.choose a))]
  calc (k.choose a : ℝ) * (|z ^ a * iteratedDeriv a (psiLo n) z|
        * |z ^ (k - a) * iteratedDeriv (k - a) (psiHi n) z|)
      ≤ (k.choose a : ℝ) * (A a * B (k - a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hX hY (abs_nonneg _) (hAnn a))
          (Nat.cast_nonneg _)
    _ = (k.choose a : ℝ) * A a * B (k - a) := by ring

/-! ## 4. The Stirling assembly and the main statement -/

/-- **The reduction to weighted plain derivatives.** -/
theorem exists_cutRadialBound_aux {A B : ℕ → ℝ} (hA1 : ∀ a : ℕ, 1 ≤ A a)
    (hB1 : ∀ b : ℕ, 1 ≤ B b)
    (hA : ∀ (a : ℕ) (u : ℝ), |(u - (-1)) ^ a * iteratedDeriv a 𝕋 u| ≤ A a)
    (hB : ∀ (b : ℕ) (v : ℝ), |(v - 2) ^ b * iteratedDeriv b 𝕋 v| ≤ B b) :
    ∃ K : ℕ → ℝ, (∀ b : ℕ, 0 ≤ K b) ∧
      ∀ (n b : ℕ) (z θ : ℝ),
        |Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z)
          z θ| ≤ K b := by
  have hAnn : ∀ a : ℕ, 0 ≤ A a := fun a => le_trans zero_le_one (hA1 a)
  have hBnn : ∀ b : ℕ, 0 ≤ B b := fun b => le_trans zero_le_one (hB1 b)
  refine ⟨fun b => ∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
      * (∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * A a * B (k - a)), ?_, ?_⟩
  · intro b
    refine Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) ?_
    refine Finset.sum_nonneg fun a _ => ?_
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hAnn a)) (hBnn (k - a))
  · intro n b z θ
    have hm : (fun z (_ : ℝ) => Work.FTS.PhiStar.Honesty.CptApp.chiR n z)
        = Work.Coercivity.CommutZ.mulZ (fun z => psiLo n z * psiHi n z) := by
      funext z' _
      simp only [Work.Coercivity.CommutZ.mulZ_apply]
      exact congrFun (chiR_eq_psiLo_mul_psiHi n) z'
    rw [hm, Work.Coercivity.CommutZ.DzIter_mulZ b (fun z => psiLo n z * psiHi n z)]
    simp only [Work.Coercivity.CommutZ.mulZ_apply]
    have hsm : ContDiff ℝ Work.Stability.smoothOrder (fun z => psiLo n z * psiHi n z) :=
      (contDiff_psiLo n).mul (contDiff_psiHi n)
    have hexp := congrFun
      (Work.FTS.LocData.DzIterZ_eq_sum_scoef (fun z => psiLo n z * psiHi n z) hsm b) z
    rw [hexp]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (Work.Spaces.scoef b k))]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact weighted_deriv_prod hAnn hA hB n k z

/-- **The `D_z`-jets of `chiR n` are uniformly bounded in `n`** (copy of
`CptApp.cutRadialBound` with the `cutBasic` import removed). -/
theorem chiR_dzIter_boundAux : ∃ K : ℕ → ℝ, (∀ b : ℕ, 0 ≤ K b) ∧
    ∀ (n b : ℕ) (z θ : ℝ),
      |Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z)
        z θ| ≤ K b := by
  obtain ⟨A, hA1, hA⟩ := Work.FTS.GalBasis.cc.exists_weighted_smoothTransition_bound (-1)
  obtain ⟨B, hB1, hB⟩ := Work.FTS.GalBasis.cc.exists_weighted_smoothTransition_bound 2
  exact exists_cutRadialBound_aux hA1 hB1 hA hB

end Work.FTS.PhiStar.Honesty.CptApp.LamAux
