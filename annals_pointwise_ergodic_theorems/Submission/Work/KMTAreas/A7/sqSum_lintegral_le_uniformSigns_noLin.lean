import Mathlib
import Submission.Work.KMTAreas.A7.khintchine_sqSum_pointwise
import Submission.Work.KMTAreas.A7.rpow_iSup_ennreal

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal BigOperators

/-- **The uniform sign bound implies the square-function bound, without the linearity hypothesis.**

This is `Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns` with the (unused) assumption
`hlin : ∀ n, IsLinearMap ℂ (T n)` deleted from the signature: the standard Khintchine
linearisation argument never uses linearity of the operators `T n`, only the hypothesis `hT` on
finitely many signed sums and the measurability of the `T n f`.  The proof below is the proof of
the linear version, verbatim, with `hlin` removed.

Suppose that for every finite set `U` of indices and every choice of signs `ω : ℕ → Bool` the
signed sum `∑_{n ∈ U} ω n · T n f` obeys the `L^p` bound `‖∑_{n ∈ U} ω n T n f‖_p ≤ M ‖f‖_p`.
Then the square function `(∑ₙ ‖T n f‖²)^{1/2}` obeys the same `L^p` bound up to a constant
depending only on `p`. -/
theorem sqSum_lintegral_le_uniformSigns_noLin (p : ℝ) (hp : 1 < p) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ))
      (hmeas : ∀ n (f : ℤ → ℂ), AEMeasurable (T n f) MeasureTheory.Measure.count)
      (M : ℝ) (hM : 0 ≤ M)
      (hT : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
        MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => enorm (∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * T n f x) ^ p)
          ≤ ENNReal.ofReal (M ^ p) * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun x : ℤ => enorm (f x) ^ p))
      (f : ℤ → ℂ),
      MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (∑' n : ℕ, enorm (T n f x) ^ (2 : ℝ)) ^ (p / 2))
        ≤ ENNReal.ofReal (K * M ^ p) * MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => enorm (f x) ^ p) := by
  obtain ⟨c, hc, hkey⟩ := khintchine_sqSum_pointwise p hp.le
  have hpq : 0 < p / 2 := by linarith
  have hcpos : 0 < c ^ p := Real.rpow_pos_of_pos hc p
  refine ⟨(c ^ p)⁻¹, by positivity, ?_⟩
  intro T hmeas M hM hT f
  -- ## Step 1: the bound for the truncated square function, uniformly in the truncation `N`
  set Q : ENNReal := ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count with hQdef
  have step1 : ∀ N : ℕ,
      ∫⁻ x : ℤ, (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂Measure.count
        ≤ ENNReal.ofReal ((c ^ p)⁻¹ * M ^ p) * Q := by
    intro N
    let B : (Fin N → Bool) → ℤ → ENNReal :=
      fun ε x => ‖∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * T (i : ℕ) f x‖ₑ ^ p
    have hBmeas : ∀ ε : Fin N → Bool, AEMeasurable (B ε) Measure.count := by
      intro ε
      have h1 : AEMeasurable (fun x : ℤ =>
          ∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * T (i : ℕ) f x) Measure.count :=
        Finset.aemeasurable_fun_sum Finset.univ fun i _ =>
          AEMeasurable.const_mul (hmeas (i : ℕ) f) (if ε i then (1 : ℂ) else -1)
      have h2 : AEMeasurable (fun x : ℤ =>
          ‖∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * T (i : ℕ) f x‖ₑ) Measure.count :=
        AEMeasurable.enorm h1
      exact AEMeasurable.pow_const h2 p
    have hpoint : ∀ x : ℤ,
        (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
          ≤ (ENNReal.ofReal (c ^ p))⁻¹ *
              ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ∑ ε : Fin N → Bool, B ε x) := by
      intro x
      have h := hkey N (fun i : Fin N => T (i : ℕ) f x)
      rw [show (∑ i : Fin N, ‖T (i : ℕ) f x‖ₑ ^ (2 : ℝ))
            = ∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ) from
          Fin.sum_univ_eq_sum_range (fun n => ‖T n f x‖ₑ ^ (2 : ℝ)) N] at h
      exact h.trans_eq (mul_assoc _ _ _)
    have hbound : ∀ ε : Fin N → Bool, ∫⁻ x : ℤ, B ε x ∂Measure.count
        ≤ ENNReal.ofReal (M ^ p) * Q := by
      intro ε
      have h := hT (Finset.range N) (fun n => if h : n < N then ε ⟨n, h⟩ else false) f
      have hEq : (fun x : ℤ => ‖∑ n ∈ Finset.range N,
            (if (if h : n < N then ε ⟨n, h⟩ else false) then (1 : ℂ) else -1) * T n f x‖ₑ ^ p)
          = B ε := by
        funext x
        have hsum : (∑ n ∈ Finset.range N,
              (if (if h : n < N then ε ⟨n, h⟩ else false) then (1 : ℂ) else -1) * T n f x)
            = ∑ i : Fin N, (if ε i then (1 : ℂ) else -1) * T (i : ℕ) f x := by
          rw [← Fin.sum_univ_eq_sum_range (fun n =>
            (if (if h : n < N then ε ⟨n, h⟩ else false) then (1 : ℂ) else -1) * T n f x) N]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hi : (if h : (i : ℕ) < N then ε ⟨(i : ℕ), h⟩ else false) = ε i := by
            rw [dif_pos i.isLt]
          rw [hi]
        rw [hsum]
      rw [hEq] at h
      rw [hQdef]
      exact h
    have hcard : ((Fintype.card (Fin N → Bool) : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ N) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← ENNReal.ofReal_natCast,
        Nat.cast_pow]
      norm_num
    have hsumconst : (∑ ε : Fin N → Bool, (ENNReal.ofReal (M ^ p) * Q))
        = ENNReal.ofReal ((2 : ℝ) ^ N) * (ENNReal.ofReal (M ^ p) * Q) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    have hpowpos : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) N
    have hb1 : (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hpowpos))
    have hb2 : ENNReal.ofReal (c ^ p) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcpos)
    have hb3 : (ENNReal.ofReal (c ^ p))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hb2
    have hmul : ENNReal.ofReal ((c ^ p)⁻¹ * M ^ p)
        = ENNReal.ofReal ((c ^ p)⁻¹) * ENNReal.ofReal (M ^ p) :=
      ENNReal.ofReal_mul (p := (c ^ p)⁻¹) (q := M ^ p) (by positivity)
    have h1 : (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
          (ENNReal.ofReal ((2 : ℝ) ^ N) * (ENNReal.ofReal (M ^ p) * Q))
        = ENNReal.ofReal (M ^ p) * Q := by
      calc (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
            (ENNReal.ofReal ((2 : ℝ) ^ N) * (ENNReal.ofReal (M ^ p) * Q))
          = ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ENNReal.ofReal ((2 : ℝ) ^ N)) *
              (ENNReal.ofReal (M ^ p) * Q) := (mul_assoc _ _ _).symm
        _ = 1 * (ENNReal.ofReal (M ^ p) * Q) := by
              rw [ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hpowpos))
                ENNReal.ofReal_ne_top]
        _ = ENNReal.ofReal (M ^ p) * Q := one_mul _
    have hY : (ENNReal.ofReal (c ^ p))⁻¹ *
          ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
            (ENNReal.ofReal ((2 : ℝ) ^ N) * (ENNReal.ofReal (M ^ p) * Q)))
        = ENNReal.ofReal ((c ^ p)⁻¹ * M ^ p) * Q := by
      rw [h1]
      calc (ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal (M ^ p) * Q)
          = ((ENNReal.ofReal (c ^ p))⁻¹ * ENNReal.ofReal (M ^ p)) * Q :=
              (mul_assoc _ _ _).symm
        _ = (ENNReal.ofReal ((c ^ p)⁻¹) * ENNReal.ofReal (M ^ p)) * Q := by
              rw [ENNReal.ofReal_inv_of_pos hcpos]
        _ = ENNReal.ofReal ((c ^ p)⁻¹ * M ^ p) * Q := by rw [← hmul]
    calc ∫⁻ x : ℤ, (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂Measure.count
        ≤ ∫⁻ x : ℤ, (ENNReal.ofReal (c ^ p))⁻¹ *
            ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ∑ ε : Fin N → Bool, B ε x)
            ∂Measure.count := lintegral_mono hpoint
      _ = (ENNReal.ofReal (c ^ p))⁻¹ *
            ∫⁻ x : ℤ, (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * (∑ ε : Fin N → Bool, B ε x)
            ∂Measure.count := by
          exact lintegral_const_mul' _ _ hb3
      _ = (ENNReal.ofReal (c ^ p))⁻¹ *
            ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ * ∫⁻ x : ℤ, ∑ ε : Fin N → Bool, B ε x
              ∂Measure.count) := by
          rw [lintegral_const_mul' _ _ hb1]
      _ = (ENNReal.ofReal (c ^ p))⁻¹ *
            ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
              ∑ ε : Fin N → Bool, ∫⁻ x : ℤ, B ε x ∂Measure.count) := by
          rw [lintegral_finsetSum' Finset.univ (fun ε _ => hBmeas ε)]
      _ ≤ (ENNReal.ofReal (c ^ p))⁻¹ *
            ((ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ *
              ∑ ε : Fin N → Bool, (ENNReal.ofReal (M ^ p) * Q)) :=
          mul_le_mul_right (mul_le_mul_right (Finset.sum_le_sum fun ε _ => hbound ε) _) _
      _ = ENNReal.ofReal ((c ^ p)⁻¹ * M ^ p) * Q := by
          rw [hsumconst]
          exact hY
  -- ## Step 2: monotone convergence as the truncation goes to infinity
  have hmono : ∀ x : ℤ, Monotone (fun N : ℕ =>
      (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) := by
    intro x N M hNM
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hpq.le
    · exact Finset.range_subset_range.mpr hNM
    · intro i _ _; exact zero_le
  have haemeas : ∀ N : ℕ, AEMeasurable (fun x : ℤ =>
      (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) Measure.count := by
    intro N
    have h1 : AEMeasurable (fun x : ℤ =>
        ∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) Measure.count :=
      Finset.aemeasurable_fun_sum (Finset.range N) fun n _ =>
        AEMeasurable.pow_const (AEMeasurable.enorm (hmeas n f)) (2 : ℝ)
    exact AEMeasurable.pow_const h1 (p / 2)
  have hsup : (fun x : ℤ => (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
      = fun x : ℤ => ⨆ N : ℕ, (∑ n ∈ Finset.range N, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
    funext x
    rw [ENNReal.tsum_eq_iSup_nat]
    exact rpow_iSup_ennreal _ hpq
  rw [hsup]
  rw [lintegral_iSup' haemeas (Filter.Eventually.of_forall (fun x => hmono x))]
  exact iSup_le step1


end Work.KMTAreas.A7
