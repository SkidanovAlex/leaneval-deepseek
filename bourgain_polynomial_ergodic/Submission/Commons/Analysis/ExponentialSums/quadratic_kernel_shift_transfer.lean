import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.ExponentialSums

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

private def natExtend (g : ℕ → ℝ) : ℤ → ℂ := fun n => if 0 ≤ n then (g n.toNat : ℂ) else 0

private lemma natExtend_of_nonneg (g : ℕ → ℝ) {n : ℤ} (hn : 0 ≤ n) :
    natExtend g n = (g n.toNat : ℂ) := by
  rw [natExtend, if_pos hn]

private lemma natExtend_cast (g : ℕ → ℝ) (m : ℕ) : natExtend g (m : ℤ) = (g m : ℂ) := by
  rw [natExtend_of_nonneg g (Int.natCast_nonneg m), Int.toNat_natCast]

private lemma natExtend_neg (g : ℕ → ℝ) {n : ℤ} (hn : n < 0) : natExtend g n = 0 := by
  rw [natExtend, if_neg (not_le.mpr hn)]

private lemma natExtend_add_sq (g : ℕ → ℝ) (m i : ℕ) :
    natExtend g ((m : ℤ) + (i : ℤ) ^ 2) = (g (m + i ^ 2) : ℂ) := by
  have h0 : (0 : ℤ) ≤ (m : ℤ) + (i : ℤ) ^ 2 := by positivity
  rw [natExtend_of_nonneg g h0]
  have h2 : ((m : ℤ) + (i : ℤ) ^ 2).toNat = m + i ^ 2 := by
    have hcast : ((m : ℤ) + (i : ℤ) ^ 2) = ((m + i ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]
  rw [h2]

private lemma natExtend_sum (g : ℕ → ℝ) (m N : ℕ) :
    (∑ i ∈ Finset.range N, natExtend g ((m : ℤ) + (i : ℤ) ^ 2))
      = ((∑ i ∈ Finset.range N, g (m + i ^ 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => natExtend_add_sq g m i)

private lemma enorm_complex_coe (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

private lemma enorm_real_coe_mul (a S : ℝ) :
    ‖(a : ℂ) * (S : ℂ)‖ₑ = ‖a * S‖ₑ := by
  rw [← Complex.ofReal_mul, enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

private noncomputable def Zmax (G : ℤ → ℂ) (n : ℤ) : ℝ≥0∞ :=
  (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, G (n + (i : ℤ) ^ 2))‖ₑ) ^ (2 : ℝ)

private noncomputable def Zl2 (G : ℤ → ℂ) (n : ℤ) : ℝ≥0∞ := ‖G n‖ₑ ^ (2 : ℝ)

private noncomputable def Nmax (g : ℕ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, g (m + i ^ 2))‖ₑ) ^ (2 : ℝ)

private noncomputable def Nl2 (g : ℕ → ℝ) (m : ℕ) : ℝ≥0∞ := ‖g m‖ₑ ^ (2 : ℝ)

private lemma enorm_step (g : ℕ → ℝ) (m N : ℕ) :
    ‖(N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, g (m + i ^ 2))‖ₑ
      = ‖(N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, natExtend g ((m : ℤ) + (i : ℤ) ^ 2))‖ₑ := by
  rw [natExtend_sum g m N]
  exact (enorm_real_coe_mul (N : ℝ)⁻¹ (∑ i ∈ Finset.range N, g (m + i ^ 2))).symm

private lemma integrand_eq (g : ℕ → ℝ) (m : ℕ) : Nmax g m = Zmax (natExtend g) (m : ℤ) := by
  simp only [Nmax, Zmax]
  rw [iSup_congr (fun N => enorm_step g m N)]

private def natIciEquiv : ℕ ≃ Set.Ici (0 : ℤ) where
  toFun m := ⟨(m : ℤ), Int.natCast_nonneg m⟩
  invFun n := n.1.toNat
  left_inv m := Int.toNat_natCast m
  right_inv n := by
    ext
    exact Int.toNat_of_nonneg n.2

private lemma natIciEquiv_coe (m : ℕ) : ((natIciEquiv m : Set.Ici (0 : ℤ)) : ℤ) = (m : ℤ) := rfl

private lemma natExtend_support (g : ℕ → ℝ) :
    Function.support (fun n : ℤ => ‖natExtend g n‖ₑ ^ (2 : ℝ)) ⊆ Set.Ici (0 : ℤ) := by
  intro n hn
  rw [Set.mem_Ici]
  by_contra h
  rw [Function.mem_support] at hn
  refine hn ?_
  rw [natExtend_neg g (lt_of_not_ge h)]
  simp

private lemma natExtend_tsum (g : ℕ → ℝ) :
    (∑' n : ℤ, Zl2 (natExtend g) n) = (∑' m : ℕ, Nl2 g m) := by
  simp only [Zl2, Nl2]
  rw [← tsum_subtype_eq_of_support_subset (natExtend_support g)]
  rw [← Equiv.tsum_eq natIciEquiv (fun b : Set.Ici (0 : ℤ) => ‖natExtend g (b : ℤ)‖ₑ ^ (2 : ℝ))]
  refine tsum_congr (fun m => ?_)
  rw [natIciEquiv_coe, natExtend_cast, enorm_complex_coe]

theorem quadratic_kernel_shift_transfer
    (h : ∃ C : ℝ, 0 < C ∧
      ∀ g : ℤ → ℂ, (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
        MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ =>
          (iSup fun N : ℕ => enorm ((N : ℝ)⁻¹ *
            Finset.sum (Finset.range N) (fun i => g (m + (i : ℤ) ^ 2)))) ^ (2 : ℝ))
          ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun n : ℤ => (enorm (g n)) ^ (2 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
        MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℕ =>
          (iSup fun N : ℕ => enorm ((N : ℝ)⁻¹ *
            Finset.sum (Finset.range N) (fun i => g (m + i ^ 2)))) ^ (2 : ℝ))
          ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun m : ℕ => (enorm (g m)) ^ (2 : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨C, hCpos, ?_⟩
  intro g hg
  have hGsupp : ∃ s : Finset ℤ, ∀ n, n ∉ s → natExtend g n = 0 := by
    obtain ⟨s, hs⟩ := hg
    refine ⟨s.image (Nat.cast), ?_⟩
    intro n hn
    by_cases hn0 : 0 ≤ n
    · rw [natExtend_of_nonneg g hn0]
      have hmem : n.toNat ∉ s := by
        intro hmem
        apply hn
        rw [Finset.mem_image]
        exact ⟨n.toNat, hmem, Int.toNat_of_nonneg hn0⟩
      rw [hs _ hmem]
      simp
    · rw [natExtend_neg g (lt_of_not_ge hn0)]
  have hbound := hC (natExtend g) hGsupp
  have hbound' : (∑' n : ℤ, Zmax (natExtend g) n)
      ≤ ENNReal.ofReal (C ^ 2) * (∑' n : ℤ, Zl2 (natExtend g) n) := by
    simpa only [Zmax, Zl2, lintegral_count] using hbound
  change MeasureTheory.lintegral MeasureTheory.Measure.count (Nmax g)
      ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count (Nl2 g)
  calc
    MeasureTheory.lintegral MeasureTheory.Measure.count (Nmax g)
        = ∑' m : ℕ, Nmax g m := lintegral_count _
    _ = ∑' m : ℕ, Zmax (natExtend g) (m : ℤ) := tsum_congr (fun m => integrand_eq g m)
    _ ≤ ∑' n : ℤ, Zmax (natExtend g) n :=
          ENNReal.tsum_comp_le_tsum_of_injective Nat.cast_injective _
    _ ≤ ENNReal.ofReal (C ^ 2) * (∑' n : ℤ, Zl2 (natExtend g) n) := hbound'
    _ = ENNReal.ofReal (C ^ 2) * (∑' m : ℕ, Nl2 g m) := by rw [natExtend_tsum g]
    _ = ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count (Nl2 g) := by
          rw [lintegral_count]

end Commons.Analysis.ExponentialSums