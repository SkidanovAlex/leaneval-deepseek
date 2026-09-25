import Mathlib
import Submission.Work.BourgainPlan.Maximal.foundations

/-!
# The `ℤ → ℕ` transfer of the `ℓ²` polynomial maximal inequality

This is the analogue, for a general integer polynomial `P`, of
`Commons.Analysis.ExponentialSums.pow_shift_transfer`.  From the `ℤ`-form of the `ℓ²` maximal
inequality for the averages `N⁻¹ ∑_{i<N} g (m + P i)` we deduce the `ℕ`-form for the density-kernel
average `discAvg P N g n`.

The bridge is the extension `natExtend g : ℤ → ℂ` of `g : ℕ → ℝ` by `0` on the negative integers;
the hypothesis `NonnegOnNat P` makes the two averages agree on `ℕ`.
-/

namespace Work.BourgainPlan.Maximal

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

open Submission.BourgainPlan (discAvg NonnegOnNat)

/-! ## The extension `ℕ → ℝ` to `ℤ → ℂ` -/

private noncomputable def natExtend (g : ℕ → ℝ) : ℤ → ℂ :=
  fun n => if 0 ≤ n then (g n.toNat : ℂ) else 0

private lemma natExtend_of_nonneg (g : ℕ → ℝ) {n : ℤ} (hn : 0 ≤ n) :
    natExtend g n = (g n.toNat : ℂ) := by
  rw [natExtend, if_pos hn]

private lemma natExtend_cast (g : ℕ → ℝ) (m : ℕ) : natExtend g (m : ℤ) = (g m : ℂ) := by
  rw [natExtend_of_nonneg g (Int.natCast_nonneg m), Int.toNat_natCast]

private lemma natExtend_neg (g : ℕ → ℝ) {n : ℤ} (hn : n < 0) : natExtend g n = 0 := by
  rw [natExtend, if_neg (not_le.mpr hn)]

private lemma natExtend_add_eval (P : Polynomial ℤ) (hP : NonnegOnNat P) (g : ℕ → ℝ)
    (m i : ℕ) :
    natExtend g ((m : ℤ) + P.eval (i : ℤ)) = (g (m + (P.eval (i : ℤ)).toNat) : ℂ) := by
  have h0 : (0 : ℤ) ≤ (m : ℤ) + P.eval (i : ℤ) := by
    have := hP i; have := Int.natCast_nonneg m; linarith
  rw [natExtend_of_nonneg g h0]
  congr 1
  rw [Int.toNat_add (Int.natCast_nonneg m) (hP i), Int.toNat_natCast]

private lemma natExtend_sum (P : Polynomial ℤ) (hP : NonnegOnNat P) (g : ℕ → ℝ) (m N : ℕ) :
    (∑ i ∈ Finset.range N, natExtend g ((m : ℤ) + P.eval (i : ℤ)))
      = ((∑ i ∈ Finset.range N, g (m + (P.eval (i : ℤ)).toNat) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => natExtend_add_eval P hP g m i)

/-! ## Norm bookkeeping for `ℝ ⊆ ℂ` -/

private lemma enorm_complex_coe (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

private lemma enorm_real_coe_mul (a S : ℝ) :
    ‖(a : ℂ) * (S : ℂ)‖ₑ = ‖a * S‖ₑ := by
  rw [← Complex.ofReal_mul, enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

/-! ## The `ℤ`- and `ℕ`-integrands -/

private noncomputable def Zmax (P : Polynomial ℤ) (G : ℤ → ℂ) (n : ℤ) : ℝ≥0∞ :=
  (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, G (n + P.eval (i : ℤ))‖ₑ) ^ (2 : ℝ)

private noncomputable def Zl2 (G : ℤ → ℂ) (n : ℤ) : ℝ≥0∞ := ‖G n‖ₑ ^ (2 : ℝ)

private noncomputable def Nmax (P : Polynomial ℤ) (g : ℕ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  (⨆ N : ℕ, ‖discAvg P N g m‖ₑ) ^ (2 : ℝ)

private noncomputable def Nl2 (g : ℕ → ℝ) (m : ℕ) : ℝ≥0∞ := ‖g m‖ₑ ^ (2 : ℝ)

private lemma enorm_step (P : Polynomial ℤ) (hP : NonnegOnNat P) (g : ℕ → ℝ) (m N : ℕ) :
    ‖discAvg P N g m‖ₑ
      = ‖(N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, natExtend g ((m : ℤ) + P.eval (i : ℤ)))‖ₑ := by
  rw [discAvg_eq_sum P N g m, natExtend_sum P hP g m N]
  exact (enorm_real_coe_mul (N : ℝ)⁻¹
    (∑ i ∈ Finset.range N, g (m + (P.eval (i : ℤ)).toNat))).symm

private lemma integrand_eq (P : Polynomial ℤ) (hP : NonnegOnNat P) (g : ℕ → ℝ) (m : ℕ) :
    Nmax P g m = Zmax P (natExtend g) (m : ℤ) := by
  simp only [Nmax, Zmax]
  rw [iSup_congr (fun N => enorm_step P hP g m N)]

/-! ## The `ℤ`-sum of `‖natExtend g‖ₑ²` equals the `ℕ`-sum of `‖g‖ₑ²` -/

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

/-- **The `ℤ → ℕ` transfer of the `ℓ²` polynomial maximal inequality.**  From the `ℤ`-form for the
averages `N⁻¹ ∑_{i<N} g (m + P i)` conclude the `ℕ`-form for `discAvg P N g n`, the density-kernel
average `N⁻¹ ∑_{i<N} g (n + P(i))` of `Submission.PolynomialKernel`.

The hypothesis `hP : NonnegOnNat P` is exactly what makes the two forms agree: for `i ≥ 0` one has
`(P.eval i).toNat = P.eval i` as integers, so `Work.BourgainPlan.Maximal.discAvg_eq_sum`
(`Submission.Work.BourgainPlan.Maximal.foundations`) rewrites `discAvg P N g n` as
`N⁻¹ ∑_{i<N} g (n + (P.eval i).toNat)`, and for `m ≥ 0` also
`(m + P.eval i).toNat = m + (P.eval i).toNat`.

Proof route: copy `Commons.Analysis.ExponentialSums.pow_shift_transfer`
(`Submission/Commons/Analysis/ExponentialSums/pure_power_kernel_maximal_l2.lean`, about 50 lines)
with `natExtend g : ℤ → ℂ` (`n ↦ g n.toNat` for `n ≥ 0`, `0` for `n < 0`), its three glue facts
(`natExtend_of_nonneg`, `natExtend_cast`, `natExtend_neg`), the counting-measure transfer
`ENNReal.tsum_comp_le_tsum_of_injective Nat.cast_injective`, and `natExtend_tsum` for
`∑'_ℕ ‖g‖ₑ² = ∑'_ℤ ‖natExtend g‖ₑ²`.  Those helpers are `private` in
`pure_power_kernel_maximal_l2.lean`, so re-declare them locally. -/
theorem poly_shift_transfer (P : Polynomial ℤ) (hP : Submission.BourgainPlan.NonnegOnNat P)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹
            * ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) *
            ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ → ℝ), (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n : ℕ, (⨆ N : ℕ, ‖Submission.BourgainPlan.discAvg P N g n‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) *
            ∫⁻ n : ℕ, ‖g n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  classical
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
  have hbound' : (∑' n : ℤ, Zmax P (natExtend g) n)
      ≤ ENNReal.ofReal (C ^ 2) * (∑' n : ℤ, Zl2 (natExtend g) n) := by
    simpa only [Zmax, Zl2, lintegral_count] using hbound
  change MeasureTheory.lintegral MeasureTheory.Measure.count (Nmax P g)
      ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count (Nl2 g)
  calc
    MeasureTheory.lintegral MeasureTheory.Measure.count (Nmax P g)
        = ∑' m : ℕ, Nmax P g m := lintegral_count _
    _ = ∑' m : ℕ, Zmax P (natExtend g) (m : ℤ) := tsum_congr (fun m => integrand_eq P hP g m)
    _ ≤ ∑' n : ℤ, Zmax P (natExtend g) n :=
          ENNReal.tsum_comp_le_tsum_of_injective Nat.cast_injective _
    _ ≤ ENNReal.ofReal (C ^ 2) * (∑' n : ℤ, Zl2 (natExtend g) n) := hbound'
    _ = ENNReal.ofReal (C ^ 2) * (∑' m : ℕ, Nl2 g m) := by rw [natExtend_tsum g]
    _ = ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count (Nl2 g) := by
          rw [lintegral_count]

end Work.BourgainPlan.Maximal
