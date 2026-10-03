/-
**Uniform Rademacher--Menshov bound for bilinear forms at every exponent `q ≥ 1`.**

The companion lemma `Work.Analysis.Variation.rmVarBound_uniform` proves, for `1 ≤ q ≤ 2`, that the
`L^q` norm of the `2`-variation of the bilinear averages `k ↦ B (f k) (g k)` is bounded by
`Cb · ⟨log₂ K⟩² · C`, where `C` bounds the `L^q` norms of *all* signed bilinear sums, and where
`Cb` is *independent of the bilinear form* `B`.  The hypothesis `q ≤ 2` is an artefact of that
statement: the underlying Rademacher--Menshov reduction produces the factor
`⟨log₂ K⟩ ^ max 2 (2 / q)`, and `max 2 (2 / q) = 2` holds for **every** `q ≥ 1`.  This file removes
the restriction `q ≤ 2`.

The estimate with the exponent `max 2 (2 / q)` is stated as a *private* theorem of
`rmVarBound_uniform.lean`; we reproduce it here in a form valid for every `q > 0` and then improve
the exponent by monotonicity of `x ↦ ⟨log₂ K + 2⟩^x` (the base is `≥ 1`).
-/
import Mathlib
import Submission.Work.Analysis.Variation.rmVarBound_uniform
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ENNReal

namespace Work.Analysis.Variation

private lemma sgn_norm_le_one (b : Bool) : ‖sgn b‖ ≤ 1 := by
  rcases b with _ | _ <;> simp [sgn]

/-- **Rademacher--Menshov for bilinear forms, with a constant independent of the bilinear form**:
the same inequality as `Work.Analysis.Variation.rademacher_menshov_bilinear`, but with the
existential constant `C` *before* the bilinear form `B`, so that one constant serves all `B`. -/
private theorem rm_bilinear_uniform_Vr_of_pos
    {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [MeasurableSpace X] (μ : MeasureTheory.Measure X) (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : V → W → X → ℂ),
      (∀ v v' w, B (v + v') w = B v w + B v' w) →
      (∀ (c : ℂ) v w, B (c • v) w = c • B v w) →
      (∀ v w w', B v (w + w') = B v w + B v w') →
      (∀ (c : ℂ) v w, B v (c • w) = c • B v w) →
      ∀ (K : ℕ) (f : ℕ → V) (g : ℕ → W), f 0 = 0 → g 0 = 0 →
      (∀ k k' : ℕ, AEMeasurable (fun x => B (f k) (g k') x) μ) →
      MeasureTheory.eLpNorm (fun x => Vr 2 K (fun k => B (f k) (g k) x))
          (ENNReal.ofReal q) μ
        ≤ ENNReal.ofReal (C * ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q))) *
            ⨆ (e : Fin K → Bool) (e' : Fin K → Bool),
              MeasureTheory.eLpNorm
                (fun x => B (∑ k : Fin K, sgn (e k) • (f ((k : ℕ) + 1) - f (k : ℕ)))
                              (∑ k : Fin K, sgn (e' k) • (g ((k : ℕ) + 1) - g (k : ℕ))) x)
                (ENNReal.ofReal q) μ := by
  classical
  obtain ⟨C₂, hC₂pos, hC₂⟩ := rademacher_menshov_two_dim 2 (by norm_num : (1 : ℝ) < 2)
  obtain ⟨c, hc, hkh⟩ := double_khintchine hq
  refine ⟨C₂ * c⁻¹, by positivity, ?_⟩
  intro B hadd₁ hsmul₁ hadd₂ hsmul₂ K f g hf0 hg0 hmeas
  have hVm := aemeasurable_Vr_aux (μ := μ) 2 K (a := fun k x => B (f k) (g k) x) (fun k => hmeas k k)
  set M : ℕ := Nat.log2 K + 1 with hM
  set pairs : Finset (ℕ × ℕ) := (Finset.range M).product (Finset.range M) with hpairs
  set T : ℝ≥0∞ := ⨆ (e : Fin K → Bool) (e' : Fin K → Bool),
      eLpNorm (fun x => B (∑ k : Fin K, sgn (e k) • (f ((k : ℕ) + 1) - f (k : ℕ)))
          (∑ k : Fin K, sgn (e' k) • (g ((k : ℕ) + 1) - g (k : ℕ))) x)
        (ENNReal.ofReal q) μ with hTdef
  have hMcast : ((M * M : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((M : ℝ) ^ 2) := by
    rw [Nat.cast_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
    congr 1
    ring
  have hpairs_card : pairs.card = M * M := by
    change (Finset.range M ×ˢ Finset.range M).card = M * M
    rw [Finset.card_product, Finset.card_range]
  -- (1) pointwise Rademacher--Menshov
  have hpt : ∀ x, Vr 2 K (fun k => B (f k) (g k) x)
      ≤ ENNReal.ofReal C₂ * ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          incLp2 2 K (2 ^ m₁) (2 ^ m₂) (fun k₁ k₂ => B (f k₁) (g k₂) x) := by
    intro x
    have h1 : ∀ k : ℕ, (fun k₁ k₂ => B (f k₁) (g k₂) x) k 0 = 0 := by
      intro k
      show B (f k) (g 0) x = 0
      rw [hg0]
      exact congrFun (bil_zero₂ B hsmul₂ (f k)) x
    have h2 : ∀ k : ℕ, (fun k₁ k₂ => B (f k₁) (g k₂) x) 0 k = 0 := by
      intro k
      show B (f 0) (g k) x = 0
      rw [hf0]
      exact congrFun (bil_zero₁ B hsmul₁ (g k)) x
    exact hC₂ K (fun k₁ k₂ => B (f k₁) (g k₂) x) h1 h2
  -- (2) pass to `eLpNorm`
  have hRM : eLpNorm (fun x => Vr 2 K (fun k => B (f k) (g k) x)) (ENNReal.ofReal q) μ
      ≤ eLpNorm (fun x => ENNReal.ofReal C₂ * ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          incLp2 2 K (2 ^ m₁) (2 ^ m₂) (fun k₁ k₂ => B (f k₁) (g k₂) x))
        (ENNReal.ofReal q) μ :=
    eLpNorm_le_of_le (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hpt
  -- (3) move the constant inside the sum over the pairs
  have hsplit : (fun x => ENNReal.ofReal C₂ * ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        incLp2 2 K (2 ^ m₁) (2 ^ m₂) (fun k₁ k₂ => B (f k₁) (g k₂) x))
      = fun x => ∑ p ∈ pairs, ENNReal.ofReal C₂ *
          incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x) := by
    funext x
    rw [show (∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          incLp2 2 K (2 ^ m₁) (2 ^ m₂) (fun k₁ k₂ => B (f k₁) (g k₂) x))
        = ∑ p ∈ pairs, incLp2 2 K (2 ^ p.1) (2 ^ p.2)
            (fun k₁ k₂ => B (f k₁) (g k₂) x) from
      (Finset.sum_product (Finset.range M) (Finset.range M)
        (fun p => incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))).symm,
      Finset.mul_sum]
  -- (4) the per-pair estimate
  have hpair : ∀ p ∈ pairs, eLpNorm (fun x => incLp2 2 K (2 ^ p.1) (2 ^ p.2)
        (fun k₁ k₂ => B (f k₁) (g k₂) x)) (ENNReal.ofReal q) μ
      ≤ ENNReal.ofReal c⁻¹ * T := by
    intro p hp
    have hm₁ : 0 < 2 ^ p.1 := pow_pos (by norm_num) _
    have hm₂ : 0 < 2 ^ p.2 := pow_pos (by norm_num) _
    rw [incLp2_bilinear_eq B hadd₁ hsmul₁ hadd₂ hsmul₂ K (2 ^ p.1) (2 ^ p.2) f g]
    exact eLpNorm_blockFamily_le hq B hadd₁ hsmul₁ hadd₂ hsmul₂ hc hkh
      (n₁ := nb K (2 ^ p.1)) (n₂ := nb K (2 ^ p.2))
      (v := fun j => f (min (2 ^ p.1 * (j + 1)) K) - f (2 ^ p.1 * j))
      (w := fun j => g (min (2 ^ p.2 * (j + 1)) K) - g (2 ^ p.2 * j))
      (fun i j => aemeasurable_bilinear_sub B hadd₁ hsmul₁ hadd₂ hsmul₂ f g hmeas
        (min (2 ^ p.1 * (i + 1)) K) (2 ^ p.1 * i)
        (min (2 ^ p.2 * (j + 1)) K) (2 ^ p.2 * j))
      (T := T)
      (fun d₁ d₂ => by
        rw [tiling_bilinear_fun B K (2 ^ p.1) (2 ^ p.2) hm₁ hm₂ f g d₁ d₂]
        exact le_iSup_of_le (fun k : Fin K => d₁ ⟨(k : ℕ) / 2 ^ p.1, div_lt_nb hm₁ k.isLt⟩)
          (le_iSup_of_le (fun k : Fin K => d₂ ⟨(k : ℕ) / 2 ^ p.2, div_lt_nb hm₂ k.isLt⟩)
            le_rfl))
  have hHPair_meas : ∀ p ∈ pairs, _root_.AEMeasurable (fun x => ENNReal.ofReal C₂ *
      incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x)) μ :=
    fun p _ => (aemeasurable_incLp2_bilinear B hadd₁ hsmul₁ hadd₂ hsmul₂ f g hmeas K
      (2 ^ p.1) (2 ^ p.2)).const_mul _
  have hHPair_le : ∀ p ∈ pairs, eLpNorm (fun x => ENNReal.ofReal C₂ *
        incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
        (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C₂ * c⁻¹) * T := by
    intro p hp
    rw [eLpNorm_const_mul_ennreal (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top _
      (aemeasurable_incLp2_bilinear B hadd₁ hsmul₁ hadd₂ hsmul₂ f g hmeas K
        (2 ^ p.1) (2 ^ p.2))]
    refine (mul_le_mul' le_rfl (hpair p hp)).trans (le_of_eq ?_)
    rw [← mul_assoc, ← ENNReal.ofReal_mul hC₂pos.le]
  rcases lt_or_ge q 1 with hq1 | hq1
  · -- the case `q < 1`: the quasi-triangle inequality over the scale pairs
    have hquasi := eLpNorm_sum_rpow_le hq (le_of_lt hq1) pairs
      (fun p x => ENNReal.ofReal C₂ * incLp2 2 K (2 ^ p.1) (2 ^ p.2)
        (fun k₁ k₂ => B (f k₁) (g k₂) x)) hHPair_meas
    have hpow : (eLpNorm (fun x => ∑ p ∈ pairs, ENNReal.ofReal C₂ *
          incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
          (ENNReal.ofReal q) μ) ^ q
        ≤ ((M * M : ℕ) : ℝ≥0∞) * ((ENNReal.ofReal (C₂ * c⁻¹)) ^ q * T ^ q) := by
      calc (eLpNorm (fun x => ∑ p ∈ pairs, ENNReal.ofReal C₂ *
              incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
              (ENNReal.ofReal q) μ) ^ q
          ≤ ∑ p ∈ pairs, (eLpNorm (fun x => ENNReal.ofReal C₂ *
                incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
                (ENNReal.ofReal q) μ) ^ q := hquasi
        _ ≤ ∑ _p ∈ pairs, (ENNReal.ofReal (C₂ * c⁻¹) * T) ^ q :=
              Finset.sum_le_sum fun p hp => ENNReal.rpow_le_rpow (hHPair_le p hp) hq.le
        _ = (pairs.card : ℝ≥0∞) * ((ENNReal.ofReal (C₂ * c⁻¹)) ^ q * T ^ q) := by
              rw [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_rpow_of_nonneg _ _ hq.le]
        _ = ((M * M : ℕ) : ℝ≥0∞) * ((ENNReal.ofReal (C₂ * c⁻¹)) ^ q * T ^ q) := by
              rw [hpairs_card]
    have hfinal : eLpNorm (fun x => ∑ p ∈ pairs, ENNReal.ofReal C₂ *
          incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
          (ENNReal.ofReal q) μ
        ≤ ENNReal.ofReal (C₂ * c⁻¹ * ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q))) * T := by
      calc eLpNorm (fun x => ∑ p ∈ pairs, ENNReal.ofReal C₂ *
              incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
              (ENNReal.ofReal q) μ
          = ((eLpNorm (fun x => ∑ p ∈ pairs, ENNReal.ofReal C₂ *
                incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
                (ENNReal.ofReal q) μ) ^ q) ^ (1 / q) := by
              rw [← ENNReal.rpow_mul, show q * (1 / q) = 1 by field_simp, ENNReal.rpow_one]
        _ ≤ (((M * M : ℕ) : ℝ≥0∞) *
              ((ENNReal.ofReal (C₂ * c⁻¹)) ^ q * T ^ q)) ^ (1 / q) :=
              ENNReal.rpow_le_rpow hpow (by positivity)
        _ = ((M * M : ℕ) : ℝ≥0∞) ^ (1 / q) *
              (((ENNReal.ofReal (C₂ * c⁻¹)) ^ q * T ^ q)) ^ (1 / q) :=
              ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
        _ = ((M * M : ℕ) : ℝ≥0∞) ^ (1 / q) *
              (((ENNReal.ofReal (C₂ * c⁻¹)) ^ q) ^ (1 / q) * (T ^ q) ^ (1 / q)) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        _ = ENNReal.ofReal ((M : ℝ) ^ (2 / q)) *
              (ENNReal.ofReal (C₂ * c⁻¹) * T) := by
              rw [hMcast, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
                ← Real.rpow_two (M : ℝ),
                ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (M : ℝ)),
                show (2 : ℝ) * (1 / q) = 2 / q by ring,
                ← ENNReal.rpow_mul, show q * (1 / q) = 1 by field_simp, ENNReal.rpow_one,
                ← ENNReal.rpow_mul, show q * (1 / q) = 1 by field_simp, ENNReal.rpow_one]
        _ = ENNReal.ofReal ((M : ℝ) ^ (2 / q) * (C₂ * c⁻¹)) * T := by
              rw [← mul_assoc,
                ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ (2 / q))]
        _ ≤ ENNReal.ofReal (C₂ * c⁻¹ * ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q))) * T := by
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left (log2_rpow_le K q hq (le_of_lt hq1))
                (by positivity : (0 : ℝ) ≤ C₂ * c⁻¹)
    refine hRM.trans ?_
    rw [hsplit]
    exact hfinal
  · -- the case `q ≥ 1`: Minkowski's inequality over the scale pairs
    have hmink := Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
      (ENNReal.one_le_ofReal.mpr hq1) hHPair_meas
    have hsum : (∑ p ∈ pairs, eLpNorm (fun x => ENNReal.ofReal C₂ *
          incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
          (ENNReal.ofReal q) μ)
        ≤ ENNReal.ofReal ((M : ℝ) ^ 2 * (C₂ * c⁻¹)) * T := by
      calc ∑ p ∈ pairs, eLpNorm (fun x => ENNReal.ofReal C₂ *
              incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
              (ENNReal.ofReal q) μ
          ≤ ∑ _p ∈ pairs, ENNReal.ofReal (C₂ * c⁻¹) * T := Finset.sum_le_sum hHPair_le
        _ = (pairs.card : ℝ≥0∞) * (ENNReal.ofReal (C₂ * c⁻¹) * T) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((M * M : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (C₂ * c⁻¹) * T) := by rw [hpairs_card]
        _ = ENNReal.ofReal ((M : ℝ) ^ 2 * (C₂ * c⁻¹)) * T := by
              rw [hMcast, ← mul_assoc,
                ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ 2)]
    have hfinal : eLpNorm (fun x => ∑ p ∈ pairs, ENNReal.ofReal C₂ *
          incLp2 2 K (2 ^ p.1) (2 ^ p.2) (fun k₁ k₂ => B (f k₁) (g k₂) x))
          (ENNReal.ofReal q) μ
        ≤ ENNReal.ofReal (C₂ * c⁻¹ * ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q))) * T := by
      refine (hmink.trans hsum).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (log2_sq_le K q hq)
        (by positivity : (0 : ℝ) ≤ C₂ * c⁻¹)
    refine hRM.trans ?_
    rw [hsplit]
    exact hfinal
private theorem rm_bilinear_uniform_VrFull_of_pos
    {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [MeasurableSpace X] (μ : MeasureTheory.Measure X) (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : V → W → X → ℂ),
      (∀ v v' w, B (v + v') w = B v w + B v' w) →
      (∀ (c : ℂ) v w, B (c • v) w = c • B v w) →
      (∀ v w w', B v (w + w') = B v w + B v w') →
      (∀ (c : ℂ) v w, B v (c • w) = c • B v w) →
      ∀ (K : ℕ) (f : ℕ → V) (g : ℕ → W), f 0 = 0 → g 0 = 0 →
      (∀ k k' : ℕ, AEMeasurable (fun x => B (f k) (g k') x) μ) →
      MeasureTheory.eLpNorm (fun x => VrFull 2 K (fun k => B (f k) (g k) x))
          (ENNReal.ofReal q) μ
        ≤ ENNReal.ofReal (C * ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q))) *
            ⨆ (e : Fin K → Bool) (e' : Fin K → Bool),
              MeasureTheory.eLpNorm
                (fun x => B (∑ k : Fin K, sgn (e k) • (f ((k : ℕ) + 1) - f (k : ℕ)))
                              (∑ k : Fin K, sgn (e' k) • (g ((k : ℕ) + 1) - g (k : ℕ))) x)
                (ENNReal.ofReal q) μ := by
  obtain ⟨C, hC, h⟩ := rm_bilinear_uniform_Vr_of_pos (V := V) (W := W) (X := X) μ q hq
  refine ⟨2 * C, by positivity, ?_⟩
  intro B hadd₁ hsmul₁ hadd₂ hsmul₂ K f g hf hg hmeas
  have hVm := aemeasurable_Vr_aux (μ := μ) 2 K (a := fun k x => B (f k) (g k) x) (fun k => hmeas k k)
  have hVFm := aemeasurable_VrFull_aux (μ := μ) 2 K (a := fun k x => B (f k) (g k) x)
    (fun k => hmeas k k)
  set Z : ℝ≥0∞ := ⨆ (e : Fin K → Bool) (e' : Fin K → Bool),
      MeasureTheory.eLpNorm
        (fun x => B (∑ k : Fin K, sgn (e k) • (f ((k : ℕ) + 1) - f (k : ℕ)))
                      (∑ k : Fin K, sgn (e' k) • (g ((k : ℕ) + 1) - g (k : ℕ))) x)
        (ENNReal.ofReal q) μ with hZ
  have hB0 : ∀ x, B (f 0) (g 0) x = 0 := by
    intro x
    rw [hg]
    have h1 := congrFun (hsmul₂ (0 : ℂ) (f 0) 0) x
    simpa only [zero_smul, Pi.smul_apply, smul_eq_mul, zero_mul] using h1
  have hpoint : ∀ x, VrFull 2 K (fun k => B (f k) (g k) x)
      ≤ 2 * Vr 2 K (fun k => B (f k) (g k) x) := by
    intro x
    exact VrFull_le_two_mul_Vr (by norm_num : (1 : ℝ) ≤ 2) (by simpa using hB0 x)
  have hmain := h B hadd₁ hsmul₁ hadd₂ hsmul₂ K f g hf hg hmeas
  have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hqT : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmono : MeasureTheory.eLpNorm (fun x => VrFull 2 K (fun k => B (f k) (g k) x))
        (ENNReal.ofReal q) μ
      ≤ MeasureTheory.eLpNorm (fun x => 2 * Vr 2 K (fun k => B (f k) (g k) x))
        (ENNReal.ofReal q) μ := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqT,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqT]
    rw [ENNReal.toReal_ofReal hq.le]
    refine ENNReal.rpow_le_rpow (MeasureTheory.lintegral_mono (fun x => ?_)) (by positivity)
    simp only [enorm_eq_self]
    exact ENNReal.rpow_le_rpow (hpoint x) hq.le
  refine le_trans hmono ?_
  have hmul : MeasureTheory.eLpNorm (fun x => 2 * Vr 2 K (fun k => B (f k) (g k) x))
        (ENNReal.ofReal q) μ
      = 2 * MeasureTheory.eLpNorm (fun x => Vr 2 K (fun k => B (f k) (g k) x))
        (ENNReal.ofReal q) μ :=
    Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := 2) (by norm_num) hq0 hqT
  rw [hmul]
  have hstep : 2 * MeasureTheory.eLpNorm (fun x => Vr 2 K (fun k => B (f k) (g k) x))
        (ENNReal.ofReal q) μ
      ≤ 2 * (ENNReal.ofReal (C * ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q))) * Z) :=
    mul_le_mul_of_nonneg_left (by rw [hZ]; exact hmain)
      (show (0 : ℝ≥0∞) ≤ 2 by norm_num)
  refine le_trans hstep ?_
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * C),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (le_of_lt hC)]
  norm_num
  exact le_of_eq (by ring)

/-- **Uniform Rademacher--Menshov bound for bilinear forms.**  There is a constant
`Cb = Cb(q, μ) > 0`, *independent of the bilinear form* `B`, such that for every bilinear
`B : V → W → X → ℂ`, every `K`, every `f, g` with `f 0 = g 0 = 0` whose mixed values are
a.e.-measurable, and every bound `C` on the `L^q` norms of *all* the signed bilinear sums
`B (∑_{k<K} ε_k • (f (k+1) - f k)) (∑_{k<K} ε'_k • (g (k+1) - g k))` (`‖ε k‖, ‖ε' k‖ ≤ 1`), the
`L^q` norm of the `2`-variation of the bilinear averages is at most
`Cb ⟨log₂ K⟩² C`. -/

theorem rmVarBound_uniform_ge_one (q : ℝ) (hq1 : 1 ≤ q)
    {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [MeasurableSpace X] (μ : MeasureTheory.Measure X) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ (B : V → W → X → ℂ),
      (∀ v v' w, B (v + v') w = B v w + B v' w) →
      (∀ (c : ℂ) v w, B (c • v) w = c • B v w) →
      (∀ v w w', B v (w + w') = B v w + B v w') →
      (∀ (c : ℂ) v w, B v (c • w) = c • B v w) →
      ∀ (K : ℕ) (f : ℕ → V) (g : ℕ → W) (C : ENNReal), f 0 = 0 → g 0 = 0 →
        (∀ k k' : ℕ, AEMeasurable (fun x => B (f k) (g k') x) μ) →
        (∀ (ε ε' : ℕ → ℂ), (∀ k, ‖ε k‖ ≤ 1) → (∀ k, ‖ε' k‖ ≤ 1) →
          MeasureTheory.eLpNorm (fun x => B
            (∑ k ∈ Finset.range K, ε k • (f (k + 1) - f k))
            (∑ k ∈ Finset.range K, ε' k • (g (k + 1) - g k)) x)
            (ENNReal.ofReal q) μ ≤ C) →
        MeasureTheory.eLpNorm (fun x => Work.Analysis.Variation.VrFull 2 K
            (fun k : ℕ => B (f k) (g k) x)) (ENNReal.ofReal q) μ
          ≤ ENNReal.ofReal (Cb * ((Nat.log2 K : ℝ) + 2) ^ (2 : ℕ)) * C := by
  classical
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  obtain ⟨C₀, hC₀pos, hC₀⟩ := rm_bilinear_uniform_VrFull_of_pos (V := V) (W := W) (X := X) μ q hq0
  refine ⟨C₀, hC₀pos, ?_⟩
  intro B hadd₁ hsmul₁ hadd₂ hsmul₂ K f g C hf0 hg0 hmeas hbound
  have hmain := hC₀ B hadd₁ hsmul₁ hadd₂ hsmul₂ K f g hf0 hg0 hmeas
  have hsup : (⨆ (e : Fin K → Bool) (e' : Fin K → Bool),
      MeasureTheory.eLpNorm
        (fun x => B (∑ k : Fin K, sgn (e k) • (f ((k : ℕ) + 1) - f (k : ℕ)))
                      (∑ k : Fin K, sgn (e' k) • (g ((k : ℕ) + 1) - g (k : ℕ))) x)
        (ENNReal.ofReal q) μ) ≤ C := by
    refine iSup_le fun e => iSup_le fun e' => ?_
    set ε : ℕ → ℂ := fun k => (if h : k < K then sgn (e ⟨k, h⟩) else 0) with hε
    set ε' : ℕ → ℂ := fun k => (if h : k < K then sgn (e' ⟨k, h⟩) else 0) with hε'
    have hεnorm : ∀ k, ‖ε k‖ ≤ 1 := by
      intro k
      have h1 : ε k = (if h : k < K then sgn (e ⟨k, h⟩) else 0) := by rw [hε]
      rw [h1]
      by_cases hk : k < K
      · rw [dif_pos hk]; exact sgn_norm_le_one _
      · rw [dif_neg hk]; simp
    have hε'norm : ∀ k, ‖ε' k‖ ≤ 1 := by
      intro k
      have h1 : ε' k = (if h : k < K then sgn (e' ⟨k, h⟩) else 0) := by rw [hε']
      rw [h1]
      by_cases hk : k < K
      · rw [dif_pos hk]; exact sgn_norm_le_one _
      · rw [dif_neg hk]; simp
    have hsum₁ : (∑ k ∈ Finset.range K, ε k • (f (k + 1) - f k))
        = ∑ k : Fin K, sgn (e k) • (f ((k : ℕ) + 1) - f (k : ℕ)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => ε k • (f (k + 1) - f k)) K]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : ε (k : ℕ) = sgn (e k) := by
        have h1 : ε (k : ℕ) = (if h : (k : ℕ) < K then sgn (e ⟨(k : ℕ), h⟩) else 0) := by
          rw [hε]
        rw [h1, dif_pos k.isLt]
      rw [hk]
    have hsum₂ : (∑ k ∈ Finset.range K, ε' k • (g (k + 1) - g k))
        = ∑ k : Fin K, sgn (e' k) • (g ((k : ℕ) + 1) - g (k : ℕ)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => ε' k • (g (k + 1) - g k)) K]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : ε' (k : ℕ) = sgn (e' k) := by
        have h1 : ε' (k : ℕ) = (if h : (k : ℕ) < K then sgn (e' ⟨(k : ℕ), h⟩) else 0) := by
          rw [hε']
        rw [h1, dif_pos k.isLt]
      rw [hk]
    have hh := hbound ε ε' hεnorm hε'norm
    rwa [hsum₁, hsum₂] at hh
  have hmax : max 2 (2 / q) = ((2 : ℕ) : ℝ) := by
    have hq2' : 2 / q ≤ 2 := by rw [div_le_iff₀ hq0]; linarith
    have h1 : max 2 (2 / q) = (2 : ℝ) := le_antisymm (max_le le_rfl hq2') (le_max_left _ _)
    rw [h1]; norm_num
  have hfac : ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q)) = ((Nat.log2 K : ℝ) + 2) ^ (2 : ℕ) := by
    rw [hmax, Real.rpow_natCast]
  rw [hfac] at hmain
  exact hmain.trans (mul_le_mul' le_rfl hsup)

