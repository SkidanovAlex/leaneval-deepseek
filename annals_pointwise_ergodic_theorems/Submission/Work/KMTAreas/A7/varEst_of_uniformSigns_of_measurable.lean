/-
# `varEst_of_uniformSigns` without the (unused) linearity hypothesis

`Work.KMTAreas.A7.varEst_of_uniformSigns` (`lacunaryBumpTransfer.lean`) turns a uniform-in-signs
`ℓᵖ` bound for a family of operators `T n` into the variational estimate
`‖𝕍^r(T n f)‖_p ≤ K M ‖f‖_p`.  Its statement carries a hypothesis `hlin : ∀ n, IsLinearMap ℂ (T n)`
which is *never used* in any of the proofs: neither in the Khintchine/Marcinkiewicz–Zygmund
linearisation `sqSum_lintegral_le_uniformSigns` (`sqSum_lintegral_le_uniformSigns.lean`) nor in the
passage from the square function to the variation.  This matters in the application of the paper's
§8 to the Ionescu–Wainger family `T n = Tle ρ l (Φ n)`, which is only additive on bounded inputs
and therefore admits no `IsLinearMap` instance.

This file removes the dead hypothesis: it contains a copy `sqSum_lintegral_le_uniformSigns'` of the
Khintchine step without `hlin`, and then the transfer `varEst_of_uniformSigns_of_measurable` whose
proof is the proof of `varEst_of_uniformSigns` with `hlin` deleted.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpTransfer
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The uniform sign bound implies the square-function bound, with no linearity hypothesis.**
This is `Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns` with the (unused) hypothesis
`hlin : ∀ n, IsLinearMap ℂ (T n)` removed; the proof is unchanged. -/
theorem sqSum_lintegral_le_uniformSigns' (p : ℝ) (hp : 1 < p) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ))
      (hmeas : ∀ n (f : ℤ → ℂ), AEMeasurable (T n f) MeasureTheory.Measure.count)
      (M : ℝ) (hM : 0 ≤ M)
      (hT : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
        ∫⁻ x : ℤ, ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * T n f x‖ₑ ^ p
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (M ^ p) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count)
      (f : ℤ → ℂ),
      ∫⁻ x : ℤ, (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * M ^ p) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count := by
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

/-- **The uniform-in-signs bound implies the variational estimate** — the statement of
`Work.KMTAreas.A7.varEst_of_uniformSigns` with the unused linearity hypothesis `hlin` removed.
This is the form in which the transfer is applicable to the Ionescu–Wainger family
`T n = Tle ρ l (Φ n)`, which is *not* additive on unbounded inputs.

Practical note for the proof: the binder `hlin` is *never used* in the bodies of either
`varEst_of_uniformSigns` (`KMTAreas/A7/lacunaryBumpTransfer.lean`) or
`sqSum_lintegral_le_uniformSigns` (`KMTAreas/A7/sqSum_lintegral_le_uniformSigns.lean`) — it appears
only in their signatures and `intro` lines.  So the proof is the text of `varEst_of_uniformSigns`
with `hlin` deleted, using a *copy* of `sqSum_lintegral_le_uniformSigns` with `hlin` deleted (or
inlining the Khintchine step); do not try to manufacture `IsLinearMap` for `T`. -/
theorem varEst_of_uniformSigns_of_measurable (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ))
      (hmeas : ∀ n (f : ℤ → ℂ), AEMeasurable (T n f) MeasureTheory.Measure.count)
      (M : ℝ) (hM : 0 ≤ M)
      (hT : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
        MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => enorm (∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * T n f x) ^ p)
          ≤ ENNReal.ofReal (M ^ p) * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun x : ℤ => enorm (f x) ^ p))
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => T n f x)) (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (K * M) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨K', hK'pos, hK'⟩ := sqSum_lintegral_le_uniformSigns' p hp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hp1p : (0 : ℝ) < 1 / p := one_div_pos.mpr hp0
  have hr2 : (2 : NNReal) ≤ r := le_of_lt hr
  set c : ℝ := 2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  refine ⟨c * K' ^ (1 / p), by positivity, ?_⟩
  intro T hmeas M hM hT f
  -- ## Step 1: the pointwise bound
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T n f x)
      ≤ ENNReal.ofReal c * (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    intro x
    have h := variationalNorm_le_sqSum hr2 (fun n : ℕ => T n f x)
    simpa only [hcdef] using h
  -- ## Step 2: pass to the `lintegral`
  have hmono : ∫⁻ x : ℤ,
        ‖PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T n f x)‖ₑ ^ p
          ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (ENNReal.ofReal c * (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ p
          ∂MeasureTheory.Measure.count := by
    refine lintegral_mono fun x => ?_
    rw [enorm_eq_self]
    exact ENNReal.rpow_le_rpow (hpt x) hp0.le
  have hpt_eq : ∀ x : ℤ,
      (ENNReal.ofReal c * (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ p
        = ENNReal.ofReal (c ^ p) * (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.ofReal_rpow_of_nonneg hcpos.le hp0.le]
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * p = p / 2 by ring]
  have hstep : ∫⁻ x : ℤ,
        ‖PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T n f x)‖ₑ ^ p
          ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (c ^ p) * ∫⁻ x : ℤ,
          (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
            ∂MeasureTheory.Measure.count := by
    calc ∫⁻ x : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T n f x)‖ₑ ^ p
          ∂MeasureTheory.Measure.count
        ≤ ∫⁻ x : ℤ, (ENNReal.ofReal c * (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ p
            ∂MeasureTheory.Measure.count := hmono
      _ = ∫⁻ x : ℤ, ENNReal.ofReal (c ^ p) *
            (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂MeasureTheory.Measure.count :=
          lintegral_congr hpt_eq
      _ = ENNReal.ofReal (c ^ p) * ∫⁻ x : ℤ,
            (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
              ∂MeasureTheory.Measure.count :=
          MeasureTheory.lintegral_const_mul (ENNReal.ofReal (c ^ p))
            (measurable_of_countable
              (fun x : ℤ => (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)))
  -- ## Step 3: the Khintchine/MZ bound for the square function
  have hsq := hK' T hmeas M hM hT f
  -- ## Step 4: combine
  have hfin : ∫⁻ x : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T n f x)‖ₑ ^ p
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (c ^ p * K' * M ^ p) *
          ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count := by
    refine hstep.trans ?_
    calc ENNReal.ofReal (c ^ p) * ∫⁻ x : ℤ,
          (∑' n : ℕ, ‖T n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (c ^ p) * (ENNReal.ofReal (K' * M ^ p) *
            ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count) :=
          mul_le_mul' le_rfl hsq
      _ = (ENNReal.ofReal (c ^ p) * ENNReal.ofReal (K' * M ^ p)) *
            ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count := by rw [mul_assoc]
      _ = ENNReal.ofReal (c ^ p * (K' * M ^ p)) *
            ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hcpos.le p)]
      _ = ENNReal.ofReal (c ^ p * K' * M ^ p) *
            ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count := by
          rw [show c ^ p * (K' * M ^ p) = c ^ p * K' * M ^ p by ring]
  -- ## Step 5: take the `p`-th root
  have hroot : (c ^ p * K' * M ^ p) ^ (1 / p) = c * K' ^ (1 / p) * M := by
    have h1 : (c ^ p) ^ (1 / p) = c := by
      rw [← Real.rpow_mul hcpos.le, show p * (1 / p) = 1 by field_simp, Real.rpow_one]
    have h2 : (M ^ p) ^ (1 / p) = M := by
      rw [← Real.rpow_mul hM, show p * (1 / p) = 1 by field_simp, Real.rpow_one]
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ c ^ p * K') (Real.rpow_nonneg hM p),
      Real.mul_rpow (Real.rpow_nonneg hcpos.le p) (le_of_lt hK'pos), h1, h2]
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  calc (∫⁻ x : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => T n f x)‖ₑ ^ p
          ∂MeasureTheory.Measure.count) ^ (1 / p)
      ≤ (ENNReal.ofReal (c ^ p * K' * M ^ p) *
          ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hfin hp1p.le
    _ = ENNReal.ofReal ((c ^ p * K' * M ^ p) ^ (1 / p)) *
          (∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp1p.le,
          ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ c ^ p * K' * M ^ p) hp1p.le]
    _ = ENNReal.ofReal (c * K' ^ (1 / p) * M) *
          (∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) := by rw [hroot]

end Work.KMTAreas.A7
