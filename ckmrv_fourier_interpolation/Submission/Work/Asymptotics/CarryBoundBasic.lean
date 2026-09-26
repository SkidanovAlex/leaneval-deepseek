/-
# Norm bookkeeping for the carries: `coeffNorm`, `supportFrobLe` and `Frob`

Elementary estimates used in `Work.Asymptotics.carry_bound`:

* `coeffNorm` is subadditive and homogeneous for `ℂ`-scalars, and does not increase under right
  multiplication by a group element;
* `supportFrobLe` is preserved by addition (with the maximum of the two bounds), by `ℂ`-scalars
  and by finite sums;
* the Frobenius norms of the group elements `T^k`, `S T^k`, `-1` are computed.
-/
import Mathlib
import Submission.Work.Asymptotics.CarryDefs
import Submission.Work.Residues.IdealImRowDiffAll

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## A sum over a union -/

lemma sum_union_le_real {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  classical
  have hdisj : Disjoint s (t \ s) := Finset.disjoint_sdiff
  have hunion : s ∪ t = s ∪ (t \ s) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [hunion, Finset.sum_union hdisj]
  have hle : ∑ x ∈ t \ s, f x ≤ ∑ x ∈ t, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_sdiff.mp hx).1)
      (fun i _ _ => hf i)
  linarith

/-! ## `coeffNorm` -/

lemma coeffNorm_add_le (x y : R) : coeffNorm (x + y) ≤ coeffNorm x + coeffNorm y := by
  classical
  have hsupp : (x + y).coeff.support ⊆ x.coeff.support ∪ y.coeff.support := by
    rw [MonoidAlgebra.coeff_add]; exact Finsupp.support_add
  have h1 : coeffNorm (x + y)
      ≤ ∑ γ ∈ (x + y).coeff.support, (‖x.coeff γ‖ + ‖y.coeff γ‖) := by
    simp only [coeffNorm]
    refine Finset.sum_le_sum fun γ _ => ?_
    simpa using norm_add_le (x.coeff γ) (y.coeff γ)
  have h2 : ∑ γ ∈ (x + y).coeff.support, (‖x.coeff γ‖ + ‖y.coeff γ‖)
      ≤ ∑ γ ∈ x.coeff.support ∪ y.coeff.support, (‖x.coeff γ‖ + ‖y.coeff γ‖) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun i _ _ => by positivity)
  have h3 : ∑ γ ∈ x.coeff.support ∪ y.coeff.support, (‖x.coeff γ‖ + ‖y.coeff γ‖)
      = coeffNorm x + coeffNorm y := by
    rw [Finset.sum_add_distrib, coeffNorm, coeffNorm]
    congr 1
    · exact (Finset.sum_subset Finset.subset_union_left (fun γ _ hγ => by
        rw [Finsupp.notMem_support_iff] at hγ; simp [hγ])).symm
    · exact (Finset.sum_subset Finset.subset_union_right (fun γ _ hγ => by
        rw [Finsupp.notMem_support_iff] at hγ; simp [hγ])).symm
  linarith [h1, h2, h3.le, h3.ge]

lemma coeffNorm_smul_le (c : ℂ) (x : R) : coeffNorm (c • x) ≤ ‖c‖ * coeffNorm x := by
  classical
  have hsupp : (c • x).coeff.support ⊆ x.coeff.support := by
    rw [MonoidAlgebra.coeff_smul]; exact Finsupp.support_smul
  have h1 : coeffNorm (c • x) ≤ ∑ γ ∈ (c • x).coeff.support, (‖c‖ * ‖x.coeff γ‖) := by
    simp only [coeffNorm]
    refine Finset.sum_le_sum fun γ _ => ?_
    rw [MonoidAlgebra.coeff_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul, norm_mul]
    exact le_refl _
  have h2 : ∑ γ ∈ (c • x).coeff.support, (‖c‖ * ‖x.coeff γ‖)
      ≤ ∑ γ ∈ x.coeff.support, (‖c‖ * ‖x.coeff γ‖) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun i _ _ => by positivity)
  have h3 : ∑ γ ∈ x.coeff.support, (‖c‖ * ‖x.coeff γ‖) = ‖c‖ * coeffNorm x := by
    rw [coeffNorm, Finset.mul_sum]
  linarith [h1, h2, h3.le, h3.ge]

lemma coeffNorm_zero : coeffNorm (0 : R) = 0 := by
  simp [coeffNorm]

lemma coeffNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → R) :
    coeffNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffNorm (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeffNorm_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc coeffNorm (f i + ∑ j ∈ s, f j) ≤ coeffNorm (f i) + coeffNorm (∑ j ∈ s, f j) :=
            coeffNorm_add_le _ _
        _ ≤ coeffNorm (f i) + ∑ j ∈ s, coeffNorm (f j) := by linarith

lemma coeffNorm_smul_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → R) :
    coeffNorm (∑ i ∈ s, c i • f i) ≤ ∑ i ∈ s, ‖c i‖ * coeffNorm (f i) := by
  calc coeffNorm (∑ i ∈ s, c i • f i) ≤ ∑ i ∈ s, coeffNorm (c i • f i) :=
        coeffNorm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖c i‖ * coeffNorm (f i) :=
        Finset.sum_le_sum fun i _ => coeffNorm_smul_le _ _

/-- `coeffNorm` does not increase under right multiplication by a group element. -/
lemma coeffNorm_mul_of_le (x : R) (g : SL(2,ℤ)) :
    coeffNorm (x * MonoidAlgebra.of ℂ SL(2,ℤ) g) ≤ coeffNorm x := by
  classical
  have hcoeff : ∀ h : SL(2,ℤ), (x * MonoidAlgebra.of ℂ SL(2,ℤ) g).coeff h = x.coeff (h * g⁻¹) := by
    intro h
    conv_lhs => rw [MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp
  have hsupp : ∀ h ∈ (x * MonoidAlgebra.of ℂ SL(2,ℤ) g).coeff.support, h * g⁻¹ ∈ x.coeff.support := by
    intro h hh
    rw [Finsupp.mem_support_iff] at hh ⊢
    rw [hcoeff h] at hh
    exact hh
  have hinj : Set.InjOn (fun h : SL(2,ℤ) => h * g⁻¹)
      ↑(x * MonoidAlgebra.of ℂ SL(2,ℤ) g).coeff.support :=
    fun a _ b _ hab => mul_right_cancel hab
  have h1 : coeffNorm (x * MonoidAlgebra.of ℂ SL(2,ℤ) g)
      = ∑ h ∈ (x * MonoidAlgebra.of ℂ SL(2,ℤ) g).coeff.support, ‖x.coeff (h * g⁻¹)‖ := by
    simp only [coeffNorm]
    exact Finset.sum_congr rfl fun h _ => by rw [hcoeff h]
  have h2 : ∑ k ∈ ((x * MonoidAlgebra.of ℂ SL(2,ℤ) g).coeff.support).image (fun h => h * g⁻¹),
        ‖x.coeff k‖ ≤ ∑ k ∈ x.coeff.support, ‖x.coeff k‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => by obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hk; exact hsupp h hh)
      (fun _ _ _ => by positivity)
  have h3 : ∑ k ∈ ((x * MonoidAlgebra.of ℂ SL(2,ℤ) g).coeff.support).image (fun h => h * g⁻¹),
        ‖x.coeff k‖ = coeffNorm (x * MonoidAlgebra.of ℂ SL(2,ℤ) g) := by
    rw [h1, Finset.sum_image hinj]
  rw [← h3, coeffNorm]
  exact h2

lemma coeffNorm_of_le (g : SL(2,ℤ)) : coeffNorm (MonoidAlgebra.of ℂ SL(2,ℤ) g) ≤ 1 := by
  classical
  have hcoeff : (MonoidAlgebra.of ℂ SL(2,ℤ) g).coeff = Finsupp.single g (1 : ℂ) := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
  rw [coeffNorm, hcoeff]
  calc ∑ γ ∈ (Finsupp.single g (1 : ℂ)).support, ‖(Finsupp.single g (1 : ℂ)) γ‖
      ≤ ∑ γ ∈ ({g} : Finset SL(2,ℤ)), ‖(Finsupp.single g (1 : ℂ)) γ‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finsupp.support_single_subset
          (fun _ _ _ => by positivity)
    _ = 1 := by
        rw [Finset.sum_singleton, Finsupp.single_eq_same]
        norm_num


/-! ## `supportFrobLe` -/

lemma supportFrobLe_mono {x : R} {K L : ℝ} (h : supportFrobLe x K) (hKL : K ≤ L) :
    supportFrobLe x L := fun γ hγ => le_trans (h γ hγ) hKL

lemma supportFrobLe_zero (K : ℝ) : supportFrobLe (0 : R) K := by
  intro γ hγ
  exact absurd hγ (by simp)

lemma supportFrobLe_add {x y : R} {K L : ℝ} (hx : supportFrobLe x K)
    (hy : supportFrobLe y L) : supportFrobLe (x + y) (max K L) := by
  intro γ hγ
  rw [MonoidAlgebra.coeff_add, Finsupp.mem_support_iff, Finsupp.add_apply] at hγ
  by_cases h0 : x.coeff γ = 0
  · refine le_trans (hy γ ?_) (le_max_right _ _)
    rw [Finsupp.mem_support_iff]
    simpa [h0] using hγ
  · refine le_trans (hx γ ?_) (le_max_left _ _)
    rw [Finsupp.mem_support_iff]
    exact h0

lemma supportFrobLe_smul {x : R} {K : ℝ} (c : ℂ) (hx : supportFrobLe x K) :
    supportFrobLe (c • x) K := by
  intro γ hγ
  rw [MonoidAlgebra.coeff_smul] at hγ
  exact hx γ (Finsupp.support_smul hγ)

lemma supportFrobLe_sum {ι : Type*} (s : Finset ι) (f : ι → R) {K : ℝ}
    (h : ∀ i ∈ s, supportFrobLe (f i) K) : supportFrobLe (∑ i ∈ s, f i) K := by
  classical
  intro γ hγ
  rw [MonoidAlgebra.coeff_sum, Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hγ
  obtain ⟨i, hi, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
  exact h i hi γ (by rw [Finsupp.mem_support_iff]; exact hg)

/-- Right multiplication by a group element shifts the support; the Frobenius norm grows by at
most `Frob g`. -/
lemma supportFrobLe_mul_of {x : R} {K : ℝ} (hx : supportFrobLe x K) (g : SL(2,ℤ)) :
    supportFrobLe (x * MonoidAlgebra.of ℂ SL(2,ℤ) g) (K * Frob g) := by
  classical
  have hcoeff : ∀ h : SL(2,ℤ),
      (x * MonoidAlgebra.of ℂ SL(2,ℤ) g).coeff h = x.coeff (h * g⁻¹) := by
    intro h
    conv_lhs => rw [MonoidAlgebra.of_apply]
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp
  intro h hh
  rw [Finsupp.mem_support_iff, hcoeff] at hh
  have hk : h * g⁻¹ ∈ x.coeff.support := by rwa [Finsupp.mem_support_iff]
  have heq : h = (h * g⁻¹) * g := by rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [heq]
  exact le_trans (Frob_mul_le _ _) (mul_le_mul_of_nonneg_right (hx _ hk) (Frob_nonneg g))

lemma supportFrobLe_smul_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → R) {K : ℝ}
    (h : ∀ i ∈ s, supportFrobLe (f i) K) : supportFrobLe (∑ i ∈ s, c i • f i) K :=
  supportFrobLe_sum s (fun i => c i • f i) (fun i hi => supportFrobLe_smul (c i) (h i hi))

/-! ## Frobenius norms of the generators -/

lemma Frob_neg_eq (γ : SL(2,ℤ)) : Frob (-γ) = Frob γ := by
  rw [Frob_eq_sqrt_frobSq, Frob_eq_sqrt_frobSq, frobSq_neg]

lemma Frob_T_zpow (k : ℤ) : Frob (ModularGroup.T ^ k) = Real.sqrt ((k : ℝ) ^ 2 + 2) := by
  rw [Frob_eq_sqrt_frobSq, coe_frobSq, ModularGroup.coe_T_zpow]
  congr 1
  simp only [sqsum, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  push_cast
  ring

lemma Frob_ST_zpow (k : ℤ) :
    Frob (ModularGroup.S * ModularGroup.T ^ k) = Real.sqrt ((k : ℝ) ^ 2 + 2) := by
  rw [Frob_eq_sqrt_frobSq, coe_frobSq, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
    ModularGroup.coe_T_zpow]
  congr 1
  simp only [sqsum, Fin.sum_univ_two, Matrix.mul_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  push_cast
  ring

lemma Frob_T : Frob (ModularGroup.T : SL(2,ℤ)) = Real.sqrt 3 := by
  rw [show (ModularGroup.T : SL(2,ℤ)) = ModularGroup.T ^ (1 : ℤ) from (zpow_one _).symm,
    Frob_T_zpow]
  congr 1
  push_cast
  norm_num

lemma Frob_S : Frob (ModularGroup.S : SL(2,ℤ)) = Real.sqrt 2 := by
  have h := Frob_ST_zpow 0
  rw [zpow_zero, mul_one] at h
  rw [h]
  congr 1
  push_cast
  norm_num

lemma Frob_neg_one : Frob (-1 : SL(2,ℤ)) = Real.sqrt 2 := by
  have h : frobSq (-1 : SL(2,ℤ)) = 2 := by decide
  rw [Frob_eq_sqrt_frobSq, h, Nat.cast_ofNat]

/-- `Frob (T^k) ≥ |k|`; this is how the exponent of a block is controlled. -/
lemma abs_le_Frob_T_zpow (k : ℤ) : |(k : ℝ)| ≤ Frob (ModularGroup.T ^ k) := by
  rw [Frob_T_zpow]
  have h : |(k : ℝ)| ≤ Real.sqrt ((k : ℝ) ^ 2 + 2) := by
    rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
    nlinarith [sq_abs (k : ℝ)]
  exact h

lemma one_add_abs_le_two_mul_one_add_Frob (k : ℤ) :
    1 + |(k : ℝ)| ≤ 2 * (1 + Frob (ModularGroup.T ^ k)) := by
  have h := abs_le_Frob_T_zpow k
  have h2 := Frob_nonneg (ModularGroup.T ^ k)
  linarith


end Work.Asymptotics
