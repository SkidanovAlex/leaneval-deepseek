import Mathlib
import Submission.Work.NN.Newton.pushforward_norms
import Submission.Work.NN.Final.holderNorm_one_comp_le

namespace Work.NN.Newton

open scoped ContDiff
open Work.NN.Core

/-- The `C^{1,α}`-bound for one component of the pairing of a continuous-linear-map-valued family
`T` with a *fixed* vector `w` of norm at most `1`, in terms of `mNorm` of `T`. -/
lemma holderNorm_clm_apply_const_le {n : ℕ} {α : ℝ} {Ω : Set (Cn n)}
    {T : Cn n → Cn n →L[ℝ] Cn n} {w : Cn n} {j : Fin n} {K : ℝ}
    (hΩ : IsOpen Ω) (hT : ∀ m : ℕ, ContDiffOn ℝ m T Ω)
    (hM : mNorm 1 α T Ω ≤ ENNReal.ofReal K) (hK0 : 0 ≤ K) (hw : ‖w‖ ≤ 1) :
    Work.CR.Flat.holderNorm 1 α (fun z => (T z w) j) Ω
      ≤ ENNReal.ofReal (8 * K * (n : ℝ)) := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hne_top : ∀ c : ℂ, Work.CR.Flat.holderNorm 1 α (fun _ : Cn n => c) Ω ≠ ⊤ :=
    fun c => ne_of_lt (lt_of_le_of_lt (holderNorm_one_const_le c Ω) ENNReal.ofReal_lt_top)
  have hT1 : ∀ p : Fin n, ContDiffOn ℝ (1 : ℕ∞) (fun z => (linCoef (T z) p) j) Ω :=
    fun p => contDiffOn_linCoef_component (hT 1) p j
  have hT2 : ∀ p : Fin n, ContDiffOn ℝ (1 : ℕ∞) (fun z => (antiCoef (T z) p) j) Ω :=
    fun p => contDiffOn_antiCoef_component (hT 1) p j
  have hF : ∀ p : Fin n,
      ContDiffOn ℝ (1 : ℕ∞) (fun z : Cn n => (fun _ : Cn n => w) z p) Ω :=
    fun p => contDiffOn_const
  have hf1 : ∀ p : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => (linCoef (T z) p) j) Ω ≠ ⊤ :=
    fun p => ne_of_lt (lt_of_le_of_lt
      ((vNorm_apply_le 1 α (fun z => linCoef (T z) p) Ω j).trans (mNorm_coef_le 1 α T Ω p))
      (lt_of_le_of_lt hM ENNReal.ofReal_lt_top))
  have hf2 : ∀ p : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => (antiCoef (T z) p) j) Ω ≠ ⊤ :=
    fun p => ne_of_lt (lt_of_le_of_lt
      ((vNorm_apply_le 1 α (fun z => antiCoef (T z) p) Ω j).trans (mNorm_anti_le 1 α T Ω p))
      (lt_of_le_of_lt hM ENNReal.ofReal_lt_top))
  have hfF : ∀ p : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z : Cn n => (fun _ : Cn n => w) z p) Ω ≠ ⊤ :=
    fun p => hne_top (w p)
  have hsum : (∑ j : Fin n, ‖w j‖) ≤ (n : ℝ) := by
    calc ∑ j : Fin n, ‖w j‖ ≤ ∑ _j : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => le_trans (norm_le_pi_norm w j) hw
      _ = (n : ℝ) := by simp
  have hvN : vNorm 1 α (fun _ : Cn n => w) Ω ≤ ENNReal.ofReal (n : ℝ) :=
    vNorm_const_le.trans (ENNReal.ofReal_le_ofReal hsum)
  calc Work.CR.Flat.holderNorm 1 α (fun z => (T z w) j) Ω
      ≤ ENNReal.ofReal 8
          * (mNorm 1 α T Ω * vNorm 1 α (fun _ : Cn n => w) Ω) :=
        holderNorm_clm_apply_le (F := fun _ : Cn n => w) hΩu j hT1 hT2 hF hf1 hf2 hfF
    _ ≤ ENNReal.ofReal 8 * (ENNReal.ofReal K * ENNReal.ofReal (n : ℝ)) :=
        mul_le_mul' le_rfl (mul_le_mul' hM hvN)
    _ = ENNReal.ofReal (8 * K * (n : ℝ)) := by
        conv_lhs => rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
          ← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hK0)]

/-- The `C^{1,α}` estimate for the pairing of a `C^{1,α}` continuous-linear-map-valued family `T`
with a fixed vector `w`, composed with a `2`-Lipschitz `C^{1,α}` map `Ψ`.  If the `mNorm` of `T` on
`Ω` is at most `K`, and `Ψ` maps `Ω'` into `Ω` with `‖fderiv Ψ‖ ≤ 2`, Lipschitz constant `2` and
`2`-Hölder derivative on `Ω'`, then one component of `T (Ψ ·) w` has `C^{1,α}`-norm on `Ω'` at most
`(5 + 2^{1+α}) · 8 · K · n`. -/
theorem holderNorm_comp_clm_apply_le {n : ℕ} {α : ℝ} (hα0 : 0 < α)
    {Ω Ω' : Set (Work.NN.Core.Cn n)}
    {T : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {Ψ : Work.NN.Core.Cn n → Work.NN.Core.Cn n} {w : Work.NN.Core.Cn n} {j : Fin n} {K : ℝ}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (hT : ∀ m : ℕ, ContDiffOn ℝ m T Ω)
    (hΨ : ∀ m : ℕ, ContDiffOn ℝ m Ψ Ω')
    (hmaps : ∀ x ∈ Ω', Ψ x ∈ Ω)
    (hlip : ∀ x ∈ Ω', ∀ y ∈ Ω', ‖Ψ x - Ψ y‖ ≤ 2 * ‖x - y‖)
    (hdΨ : ∀ x ∈ Ω', ‖fderiv ℝ Ψ x‖ ≤ 2)
    (hdΨα : ∀ x ∈ Ω', ∀ y ∈ Ω', ‖fderiv ℝ Ψ x - fderiv ℝ Ψ y‖ ≤ 2 * ‖x - y‖ ^ α)
    (hM : Work.NN.Newton.mNorm 1 α T Ω ≤ ENNReal.ofReal K) (hK0 : 0 ≤ K)
    (hw : ‖w‖ ≤ 1) :
    Work.CR.Flat.holderNorm 1 α (fun ζ => (T (Ψ ζ) w) j) Ω'
      ≤ ENNReal.ofReal ((5 + 2 ^ (1 + α)) * 8 * K * (n : ℝ)) := by
  have hinner : Work.CR.Flat.holderNorm 1 α (fun z => (T z w) j) Ω
      ≤ ENNReal.ofReal (8 * K * (n : ℝ)) :=
    holderNorm_clm_apply_const_le hΩ hT hM hK0 hw
  have hW : ContDiffOn ℝ (1 : ℕ∞) (fun z => (T z w) j) Ω :=
    contDiffOn_clm_component (hT 1) w j
  have hΨ1 : ContDiffOn ℝ (1 : ℕ∞) Ψ Ω' := hΨ 1
  have hcomp := Work.NN.Final.holderNorm_one_comp_le (X := Cn n) (L := 2) hα0
    (by norm_num : (0 : ℝ) ≤ 2) hΩ hΩ' hW hΨ1 hmaps hlip hdΨ hdΨα
  have hc0 : (0 : ℝ) ≤ 1 + 2 * 2 + 2 ^ (1 + α) := by
    have h2 : (0 : ℝ) ≤ 2 ^ (1 + α) := Real.rpow_nonneg (by norm_num) _
    linarith
  calc Work.CR.Flat.holderNorm 1 α (fun ζ => (T (Ψ ζ) w) j) Ω'
      = Work.CR.Flat.holderNorm 1 α ((fun z => (T z w) j) ∘ Ψ) Ω' := rfl
    _ ≤ ENNReal.ofReal (1 + 2 * 2 + 2 ^ (1 + α))
          * Work.CR.Flat.holderNorm 1 α (fun z => (T z w) j) Ω := hcomp
    _ ≤ ENNReal.ofReal (1 + 2 * 2 + 2 ^ (1 + α)) * ENNReal.ofReal (8 * K * (n : ℝ)) :=
        mul_le_mul' le_rfl hinner
    _ = ENNReal.ofReal ((5 + 2 ^ (1 + α)) * 8 * K * (n : ℝ)) := by
        rw [← ENNReal.ofReal_mul hc0]
        congr 1
        ring

end Work.NN.Newton
