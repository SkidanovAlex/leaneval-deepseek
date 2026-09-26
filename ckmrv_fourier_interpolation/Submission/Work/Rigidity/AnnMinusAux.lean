/-
# Auxiliary objects for the weight-four rigidity lemma at eigenvalue `+1`

This file collects the objects and elementary lemmas used in the proof of
`Work.Rigidity.SingleRigidityP 4 (1 : ℂ) 0` (`AnnMinusWeightFourP`): the `T`-defect
`u = fstDiff f` of `f`, the `S`-slash `H = u ∣[4] S` of `u`, the odd combination
`K = H + u/2`, and the weight-eight invariant `I = u² + uH + H² = K² + (3/4)u²`.

The key elementary facts are

* `sdef_apply`, `sdef_smul`, `sdef_S_smul` : the pointwise form of `H` and the relation
  `H(S•τ) = τ^4 u(τ)` (the involution `S² = 1`);
* `Kcomb_vadd_one` : `K(τ+1) = -K(τ)`;
* `I2_vadd_one`, `I2_S_smul` : `I` is invariant under `T` and `S` at weight `8`.
-/
import Mathlib
import Submission.Work.Rigidity.ModerateGrowth
import Submission.Work.Rigidity.Diff
import Submission.Work.Rigidity.FstDiffTraceFour
import Submission.Work.Kernels.KernelSlash

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

variable {f : ℍ → ℂ}

/-- The `S`-slash `H = u ∣[4] S` of the `T`-defect `u = fstDiff f`, at weight `4`. -/
def sdef (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ => (τ : ℂ) ^ (-4 : ℤ) * fstDiff f (ModularGroup.S • τ)

/-- The odd combination `K = H + u / 2`. -/
def Kcomb (f : ℍ → ℂ) : ℍ → ℂ := fun τ => sdef f τ + (1 / 2) * fstDiff f τ

/-- The weight-`8` invariant `I = u² + u H + H² = K² + (3/4) u²`. -/
def I2 (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ => (fstDiff f τ) ^ 2 + fstDiff f τ * sdef f τ + (sdef f τ) ^ 2

lemma sdef_apply (f : ℍ → ℂ) (τ : ℍ) :
    sdef f τ = fstDiff f (ModularGroup.S • τ) * (τ : ℂ) ^ (-4 : ℤ) := by
  rw [sdef, mul_comm]

/-- The relation `H ∣[4] S = u` in pointwise form: `τ^4 H(S•τ) = τ^4 (τ^{-4} u τ)`. -/
lemma sdef_S_smul (f : ℍ → ℂ) (τ : ℍ) :
    sdef f (ModularGroup.S • τ) = (τ : ℂ) ^ (4 : ℤ) * fstDiff f τ := by
  rw [sdef, S_smul_S_smul, coe_S_smul, zpow_neg_inv (τ : ℂ) (by norm_num : Even (4 : ℤ))]

/-- The `T`-defect of an `S`-invariant, `(T-I)²`-annihilated `f` is `1`-periodic. -/
lemma fstDiff_vadd_one_of_annT2 (hT2 : AnnT2 f) :
    ∀ τ : ℍ, fstDiff f ((1 : ℝ) +ᵥ τ) = fstDiff f τ :=
  (fstDiff_vadd_one_iff f).mp hT2

/-- The trace identity in pointwise form: `u(τ) + H(τ) + H(τ+1) = 0`. -/
lemma trace_pointwise (hT2 : AnnT2 f) (hS : SlashEigen 4 (1 : ℂ) f) (τ : ℍ) :
    fstDiff f τ + sdef f τ + sdef f ((1 : ℝ) +ᵥ τ) = 0 := by
  have h := FstDiffTraceFour hT2 hS τ
  have hc : ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = (τ : ℂ) + 1 := by
    rw [Work.Kernels.coe_vadd_one]; ring
  simp only [sdef]
  rw [hc]
  exact h

/-- The odd combination is anti-invariant under `T`. -/
lemma Kcomb_vadd_one (hT2 : AnnT2 f) (hS : SlashEigen 4 (1 : ℂ) f) (τ : ℍ) :
    Kcomb f ((1 : ℝ) +ᵥ τ) = -Kcomb f τ := by
  have ht := trace_pointwise hT2 hS τ
  have hp := fstDiff_vadd_one_of_annT2 (f := f) hT2 τ
  have hH : sdef f ((1 : ℝ) +ᵥ τ) = -(sdef f τ) - fstDiff f τ := by
    linear_combination ht
  simp only [Kcomb]
  rw [hH, hp]
  ring

/-- The invariant `I` is invariant under `T` at weight `8`. -/
lemma I2_vadd_one (hT2 : AnnT2 f) (hS : SlashEigen 4 (1 : ℂ) f) (τ : ℍ) :
    I2 f ((1 : ℝ) +ᵥ τ) = I2 f τ := by
  have ht := trace_pointwise hT2 hS τ
  have hp := fstDiff_vadd_one_of_annT2 (f := f) hT2 τ
  have hH : sdef f ((1 : ℝ) +ᵥ τ) = -(sdef f τ) - fstDiff f τ := by
    linear_combination ht
  simp only [I2]
  rw [hp, hH]
  ring

/-- The invariant `I` is invariant under `S` at weight `8`. -/
lemma I2_S_smul (f : ℍ → ℂ) (τ : ℍ) :
    I2 f (ModularGroup.S • τ) = (τ : ℂ) ^ (8 : ℤ) * I2 f τ := by
  have h1 := sdef_S_smul f τ
  have h2 : fstDiff f (ModularGroup.S • τ) = (τ : ℂ) ^ (4 : ℤ) * sdef f τ := by
    have hz : (τ : ℂ) ≠ 0 := coe_ne_zero τ
    have h : (τ : ℂ) ^ (-4 : ℤ) * fstDiff f (ModularGroup.S • τ) = sdef f τ := rfl
    have h4 : (τ : ℂ) ^ (4 : ℤ) * (τ : ℂ) ^ (-4 : ℤ) = 1 := by
      rw [← zpow_add₀ hz]; norm_num
    calc fstDiff f (ModularGroup.S • τ)
        = 1 * fstDiff f (ModularGroup.S • τ) := by ring
      _ = (τ : ℂ) ^ (4 : ℤ) * ((τ : ℂ) ^ (-4 : ℤ) * fstDiff f (ModularGroup.S • τ)) := by
          rw [← mul_assoc, h4, one_mul]
      _ = (τ : ℂ) ^ (4 : ℤ) * sdef f τ := by rw [h]
  have hz : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  have h8 : (8 : ℤ) = 4 + 4 := by norm_num
  simp only [I2]
  rw [h1, h2, h8, zpow_add₀ hz]
  ring

/-- `I` is invariant under `S` at weight `8`, in slash form. -/
lemma I2_slash_S (f : ℍ → ℂ) : I2 f ∣[(8 : ℤ)] ModularGroup.S = I2 f := by
  funext τ
  rw [Work.Kernels.slash_S_apply, I2_S_smul]
  have hτ : (τ : ℂ) ≠ 0 := coe_ne_zero τ
  rw [mul_assoc, mul_comm (I2 f τ) ((τ : ℂ) ^ (-8 : ℤ)), ← mul_assoc, ← zpow_add₀ hτ]
  norm_num

/-- `I` is invariant under `T` at weight `8`, in slash form. -/
lemma I2_slash_T (hT2 : AnnT2 f) (hS : SlashEigen 4 (1 : ℂ) f) :
    I2 f ∣[(8 : ℤ)] ModularGroup.T = I2 f := by
  funext τ
  rw [Work.Kernels.slash_T_apply]
  exact I2_vadd_one hT2 hS τ

end Work.Rigidity
