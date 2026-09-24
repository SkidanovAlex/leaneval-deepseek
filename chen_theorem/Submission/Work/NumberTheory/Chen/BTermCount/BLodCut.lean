import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs
import Submission.Work.NumberTheory.Chen.BTermCount.BLodLargeSieve

open Finset Filter
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The cut coefficient sequences and the large-sieve bound for them

For the defect terms of the Möbius decomposition
`bProdCharSum (r·e) (changeLevel ψ) = Σ_{t ∣ e} μ(t) X_t(ψ)`,
the character sum `X_t(ψ) = Σ_{n ∈ B̄, t ∣ n} ψ(n)` is, by `BLodBilinearCut`, a hyperbola
bilinear form whose coefficient sequences are `aCoeff` cut by `t₁ ∣ q` and `bCoeff` cut by
`t₂ ∣ m` (`t = t₁ t₂`, `t₁` `Y`-smooth, `t₂` `Y`-rough).  These cuts only *decrease* the
coefficient sequences, so the sums of squares stay bounded by `U_j` and `bPairCount`,
uniformly in `t`; consequently the dyadic maximal bilinear character large sieve
(`BLodLargeSieve`) applies with a bound uniform in `t`.
-/

/-- The cut `a`-coefficient of block `j` for the divisibility condition `t₁ ∣ q`. -/
noncomputable def aCut (M Y j t₁ q : ℕ) : ℂ :=
  aCoeff M Y j q * (if t₁ ∣ q then (1 : ℂ) else 0)

/-- The cut `b`-coefficient for the divisibility condition `t₂ ∣ m`. -/
noncomputable def bCut (Y t₂ m : ℕ) : ℂ :=
  bCoeff Y m * (if t₂ ∣ m then (1 : ℂ) else 0)

private theorem norm_ite_one_zero_le_one (P : Prop) [Decidable P] :
    ‖(if P then (1 : ℂ) else 0)‖ ≤ 1 := by
  split_ifs <;> simp

theorem norm_aCut_le_one (M Y j t₁ q : ℕ) : ‖aCut M Y j t₁ q‖ ≤ 1 := by
  rw [aCut, norm_mul]
  calc ‖aCoeff M Y j q‖ * ‖(if t₁ ∣ q then (1 : ℂ) else 0)‖
      ≤ 1 * 1 :=
        mul_le_mul (norm_aCoeff_le_one M Y j q) (norm_ite_one_zero_le_one _)
          (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem norm_bCut_le_bCoeff (Y t₂ m : ℕ) : ‖bCut Y t₂ m‖ ≤ ‖bCoeff Y m‖ := by
  rw [bCut, norm_mul]
  calc ‖bCoeff Y m‖ * ‖(if t₂ ∣ m then (1 : ℂ) else 0)‖ ≤ ‖bCoeff Y m‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_ite_one_zero_le_one _) (norm_nonneg _)
    _ = ‖bCoeff Y m‖ := by ring

theorem sum_sq_aCut_le (M Y j t₁ U : ℕ) :
    ∑ q ∈ Finset.Icc 1 U, ‖aCut M Y j t₁ q‖ ^ 2 ≤ (U : ℝ) := by
  have h1 : ∑ q ∈ Finset.Icc 1 U, ‖aCut M Y j t₁ q‖ ^ 2
      ≤ ∑ _q ∈ Finset.Icc 1 U, (1 : ℝ) := by
    refine Finset.sum_le_sum (fun q _ => ?_)
    have h2 := norm_aCut_le_one M Y j t₁ q
    have h3 : (0:ℝ) ≤ ‖aCut M Y j t₁ q‖ := norm_nonneg _
    rw [sq]
    nlinarith [h2, h3]
  simpa using h1

theorem sum_sq_bCut_le (Y t₂ V : ℕ) :
    ∑ m ∈ Finset.Icc 1 V, ‖bCut Y t₂ m‖ ^ 2 ≤ (bPairCount Y V : ℝ) := by
  have h1 : ∑ m ∈ Finset.Icc 1 V, ‖bCut Y t₂ m‖ ^ 2
      ≤ ∑ m ∈ Finset.Icc 1 V, ‖bCoeff Y m‖ ^ 2 := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    have h2 := norm_bCut_le_bCoeff Y t₂ m
    have h3 : (0:ℝ) ≤ ‖bCut Y t₂ m‖ := norm_nonneg _
    have h4 : (0:ℝ) ≤ ‖bCoeff Y m‖ := norm_nonneg _
    calc ‖bCut Y t₂ m‖ ^ 2 = ‖bCut Y t₂ m‖ * ‖bCut Y t₂ m‖ := by rw [sq]
      _ ≤ ‖bCoeff Y m‖ * ‖bCut Y t₂ m‖ := mul_le_mul_of_nonneg_right h2 h3
      _ ≤ ‖bCoeff Y m‖ * ‖bCoeff Y m‖ := mul_le_mul_of_nonneg_left h2 h4
      _ = ‖bCoeff Y m‖ ^ 2 := by rw [sq]
  exact le_trans h1 (sum_sq_bCoeff_le_bPairCount Y V)

/-- A single element of an image-set of norms is at most the supremum. -/
theorem bilinForm_le_sSup (U V y : ℕ) (h1 : 1 ≤ y) (h2 : y ≤ U * V)
    (a b : ℕ → ℂ) (r : ℕ) (ψ : DirichletCharacter ℂ r) :
    ‖bilinForm U V y a b r ψ‖
      ≤ sSup ((fun y' : ℕ => ‖bilinForm U V y' a b r ψ‖) '' Set.Icc 1 (U * V)) := by
  have hfin : ((fun y' : ℕ => ‖bilinForm U V y' a b r ψ‖) '' Set.Icc 1 (U * V)).Finite :=
    (Set.finite_Icc (1 : ℕ) (U * V)).image (fun y' : ℕ => ‖bilinForm U V y' a b r ψ‖)
  exact le_csSup hfin.bddAbove ⟨y, ⟨h1, h2⟩, rfl⟩

/-- **The large-sieve bound over a dyadic block of conductors, with dominated coefficients.** -/
theorem BLodCutLS :
    ∃ c : ℝ, 0 < c ∧
      ∀ (U V y R : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hR : 1 ≤ R) (hy1 : 1 ≤ y) (hy : y ≤ U * V)
        (a b : ℕ → ℂ) (A₂ B₂ : ℝ)
        (hA₂ : ∑ u ∈ Finset.Icc 1 U, ‖a u‖ ^ 2 ≤ A₂)
        (hB₂ : ∑ v ∈ Finset.Icc 1 V, ‖b v‖ ^ 2 ≤ B₂),
        (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ *
            ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
              ‖bilinForm U V y a b r ψ‖)
          ≤ c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * A₂) *
              Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * B₂) *
              Real.log (2 * (U : ℝ) * (V : ℝ) + 2) := by
  obtain ⟨c, hcpos, hc⟩ := BLodLargeSieve
  refine ⟨c, hcpos, ?_⟩
  intro U V y R hU hV hR hy1 hy a b A₂ B₂ hA₂ hB₂
  have hstep : (∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ *
        ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
          ‖bilinForm U V y a b r ψ‖)
      ≤ ∑ r ∈ Finset.Icc (R + 1) (2 * R), (Nat.totient r : ℝ)⁻¹ *
        ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
          sSup ((fun y' : ℕ => ‖bilinForm U V y' a b r ψ‖) '' Set.Icc 1 (U * V)) := by
    refine Finset.sum_le_sum (fun r _ => ?_)
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ψ _ => ?_))
      (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact bilinForm_le_sSup U V y hy1 hy a b r ψ
  refine le_trans hstep ?_
  have h := hc U V R hU hV hR a b
  refine le_trans h ?_
  set L : ℝ := Real.log (2 * (U : ℝ) * (V : ℝ) + 2) with hLdef
  have h1UV : (1 : ℝ) ≤ 2 * (U : ℝ) * (V : ℝ) + 2 := by
    have hU0 : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
    have hV0 : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg V
    nlinarith
  have hLnn : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg h1UV
  have hRinv : 0 ≤ (R : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcR : 0 ≤ c * (R : ℝ)⁻¹ := mul_nonneg hcpos.le hRinv
  have hsA : Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
        * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2)
      ≤ Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * A₂) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hA₂ (by positivity))
  have hsB : Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
        * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2)
      ≤ Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * B₂) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hB₂ (by positivity))
  have hs : Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
          * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2)
        * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
          * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2)
      ≤ Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * A₂)
        * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * B₂) :=
    mul_le_mul hsA hsB (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h1 : c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
          * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2)
        * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
          * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2)
      ≤ c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * A₂)
        * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * B₂) := by
    have e1 : c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2)
          * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2)
        = (c * (R : ℝ)⁻¹) * (Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2)
          * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
            * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2)) := by ring
    have e2 : (c * (R : ℝ)⁻¹) * (Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * A₂)
          * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * B₂))
        = c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * A₂)
          * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * B₂) := by ring
    rw [e1, ← e2]
    exact mul_le_mul_of_nonneg_left hs hcR
  calc c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
          * ∑ m ∈ Finset.Icc 1 U, ‖a m‖ ^ 2)
        * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2)
          * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ ^ 2) * L
      ≤ c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * A₂)
        * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * B₂) * L :=
        mul_le_mul_of_nonneg_right h1 hLnn
    _ = c * (R : ℝ)⁻¹ * Real.sqrt (((U : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * A₂)
        * Real.sqrt (((V : ℝ) + ((2 * R : ℕ) : ℝ) ^ 2) * B₂)
        * Real.log (2 * (U : ℝ) * (V : ℝ) + 2) := by rw [← hLdef]end Work.NumberTheory.Chen.BTermCount
