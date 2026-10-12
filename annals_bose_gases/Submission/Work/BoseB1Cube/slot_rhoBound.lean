import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.FlatFib.flatFibSumEqZero
import Submission.Work.BoseFixB1S.intAbsCS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.slot_rhoBound` — the single-slot zero-mean bound

For a box `A ⊆ acube ℓ` of volume `V = |A|`, a state `Φ : X n → ℝ`, a slot `i : Fin n` and a
mean-zero test function `ρ` supported in `A` with `|ρ| ≤ Ξ`, the *single-slot* pairing is
dominated by the box projection `P_{A,i}Φ` and the mean-free part `Q_{A,i}Φ = 1_A Φ − P_{A,i}Φ`:

  `|∫_{abox n ℓ} ρ(xᵢ)·Φ²| ≤ Ξ·(2·√(‖PᵢΦ‖²·‖QᵢΦ‖²) + ‖QᵢΦ‖²)`.

## The proof

Write `P := boxPInd V A i Φ`, `Q := boxQInd V A i Φ`, so that `P x + Q x = 1_A(x i)·Φ x`
pointwise.  Since `ρ` vanishes off `A`,

  `ρ(xᵢ)·Φ² = ρ(xᵢ)·(P+Q)² = ρ(xᵢ)·P² + 2·ρ(xᵢ)·P·Q + ρ(xᵢ)·Q²`.

The three terms are estimated separately:

* `∫ ρ(xᵢ)·P² = 0`.  This is the *slot peel*: `ρ(xᵢ)·P² = ρ(xᵢ)·M²` where
  `M x = (1/V)·∫_{z∈A} Φ(x|i↦z)dz` is the slot-`i` fibre mean, which is *invariant* under a
  change of the `i`-th slot.  Under the measure-preserving insertion
  `kcInsN m i : E3 × X m ≃ᵐ X (m+1)` (`Work.BoseFixB1S.FlatFib.kcInsN_mp_abox`) the integral
  factors as `(∫_{acube ℓ} ρ)·(…)`, and `∫_{acube ℓ} ρ = ∫_A ρ = 0`.
* `|∫ ρ(xᵢ)·P·Q| ≤ Ξ·∫|P·Q| ≤ Ξ·√(∫P²)·√(∫Q²)` (Cauchy–Schwarz, `intAbsCS`), and
* `|∫ ρ(xᵢ)·Q²| ≤ Ξ·∫Q²`.

The Banach-space integral is `L²`-Hölder (`Work.BoseFixB1S.int_abs_mul_le_sqrt_mul_sqrt`); the
`√(∫P²·∫Q²) = √(∫P²)·√(∫Q²)` rewrite uses `∫P² ≥ 0`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseB1Cube

set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `|a| ≤ b` implies `|a ^ 2| ≤ b ^ 2`. -/
theorem abs_sq_le_sq_of_abs_le {a b : ℝ} (h : |a| ≤ b) : |a ^ 2| ≤ b ^ 2 := by
  have hb : 0 ≤ b := le_trans (abs_nonneg a) h
  rw [abs_of_nonneg (sq_nonneg a), ← sq_abs a, sq_le_sq, abs_of_nonneg hb]
  simpa using h

/-- `|a| ≤ c` and `|b| ≤ d` imply `|a * b| ≤ c * d`. -/
theorem abs_mul_le_of_abs_le {a b c d : ℝ} (ha : |a| ≤ c) (hb : |b| ≤ d) : |a * b| ≤ c * d := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) (le_trans (abs_nonneg a) ha)

/-- **The slot peel.**  If `H : X (m+1) → ℝ` is invariant under a change of the `i`-th slot, then
the `w(xᵢ)`-weighted box integral factors through the one-particle cube integral:

  `∫_{abox (m+1) ℓ} w(xᵢ)·H x = (∫_{acube ℓ} w)·(∫_{abox m ℓ} H(kcInsN m i (0,r)))`.

The insertion `kcInsN m i` identifies `(volume↾acube ℓ) × (volume↾abox m ℓ)` with
`volume↾abox (m+1) ℓ` as measure spaces (`Work.BoseFixB1S.FlatFib.kcInsN_mp_abox`), the slot-`i`
coordinate of `kcInsN m i (y,r)` is `y`, and `H` only sees the inserted value through its
invariance. -/
theorem slotWeightedPeel {m : ℕ} {ℓ : ℝ} (i : Fin (m + 1))
    {w : E3 → ℝ} {H : Submission.BoseGases.X (m + 1) → ℝ}
    (hHinv : ∀ (r : Submission.BoseGases.X m) (y y' : E3),
      H (Submission.BoseGases.kcInsN m i (y, r)) = H (Submission.BoseGases.kcInsN m i (y', r))) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ, w (x i) * H x)
      = (∫ y in Submission.BoseGases.acube ℓ, w y)
        * (∫ r in Submission.BoseGases.abox m ℓ,
            H (Submission.BoseGases.kcInsN m i (0, r))) := by
  have hmp := Work.BoseFixB1S.FlatFib.kcInsN_mp_abox (ℓ := ℓ) i
  have hc := hmp.integral_comp (Submission.BoseGases.kcInsN m i).measurableEmbedding
      (fun x : Submission.BoseGases.X (m + 1) => w (x i) * H x)
  have hL : (∫ p : E3 × Submission.BoseGases.X m,
        w (((Submission.BoseGases.kcInsN m i) p) i) * H ((Submission.BoseGases.kcInsN m i) p)
        ∂((volume.restrict (Submission.BoseGases.acube ℓ)).prod
           (volume.restrict (Submission.BoseGases.abox m ℓ))))
      = ∫ p : E3 × Submission.BoseGases.X m,
        w (p.1) * H ((Submission.BoseGases.kcInsN m i) p)
        ∂((volume.restrict (Submission.BoseGases.acube ℓ)).prod
           (volume.restrict (Submission.BoseGases.abox m ℓ))) := by
    apply integral_congr_ae
    filter_upwards with p
    obtain ⟨a, r⟩ := p
    simp [Submission.BoseGases.kc_insN_apply_same]
  rw [← hc, hL]
  have hrewrite : (∫ p : E3 × Submission.BoseGases.X m,
          w (p.1) * H ((Submission.BoseGases.kcInsN m i) p)
          ∂((volume.restrict (Submission.BoseGases.acube ℓ)).prod
             (volume.restrict (Submission.BoseGases.abox m ℓ))))
      = ∫ p : E3 × Submission.BoseGases.X m,
          w (p.1) * H ((Submission.BoseGases.kcInsN m i) (0, p.2))
          ∂((volume.restrict (Submission.BoseGases.acube ℓ)).prod
             (volume.restrict (Submission.BoseGases.abox m ℓ))) := by
    apply integral_congr_ae
    filter_upwards with p
    rw [hHinv p.2 p.1 0]
  rw [hrewrite]
  exact integral_prod_mul w (fun r => H (Submission.BoseGases.kcInsN m i (0, r)))

theorem slot_rhoBound {n : ℕ} {ℓ V Ξ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hVeq : V = (MeasureTheory.volume A).toReal)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {ρ : EuclideanSpace ℝ (Fin 3) → ℝ} (hρm : Measurable ρ) (hΞ0 : 0 ≤ Ξ)
    (hρb : ∀ z, |ρ z| ≤ Ξ) (hsupp : ∀ z, z ∉ A → ρ z = 0) (hρA : ∫ z in A, ρ z = 0)
    (i : Fin n) :
    |∫ x in Submission.BoseGases.abox n ℓ, ρ (x i) * (Φ x) ^ 2|
      ≤ Ξ * (2 * Real.sqrt ((∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
              * (∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2))
            + (∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)) := by
  classical
  cases n with
  | zero => exact i.elim0
  | succ m =>
    -- `Φ` is bounded on the compact box
    obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact (m + 1) hℓ).exists_bound_of_continuousOn
      (f := Φ) hΦc.continuousOn
    have hΦb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |Φ x| ≤ B :=
      fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
    -- the two pieces of the state
    set P : Submission.BoseGases.X (m + 1) → ℝ := Work.UBBInputs8.boxPInd V A i Φ with hPdef
    set Q : Submission.BoseGases.X (m + 1) → ℝ := Work.UBBInputs8.boxQInd V A i Φ with hQdef
    have hPm : Measurable P := by
      rw [hPdef]
      exact Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable
    have hQm : Measurable Q := by
      rw [hQdef]
      exact Work.SlotWord.measurable_boxQInd V A hA i hΦc.measurable
    have hPQ : ∀ x : Submission.BoseGases.X (m + 1),
        P x + Q x = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
      intro x
      rw [hPdef, hQdef]
      simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
      ring
    have hPb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |P x| ≤ B := by
      intro x hx
      rw [hPdef]
      exact Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hΦb x hx
    have hQb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |Q x| ≤ 2 * B := by
      intro x hx
      have hQx : Q x = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - P x := by
        rw [hQdef, hPdef]; rfl
      rw [hQx]
      have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases hxi : x i ∈ A
        · rw [Set.indicator_of_mem hxi]; norm_num
        · rw [Set.indicator_of_notMem hxi]; norm_num
      have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ 1 * B :=
        abs_mul_le_of_abs_le hind (hΦb x hx)
      calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - P x|
          ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| + |P x| := by
            have := norm_sub_le (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) (P x)
            simpa [Real.norm_eq_abs] using this
        _ ≤ 1 * B + B := add_le_add h1 (hPb x hx)
        _ = 2 * B := by ring
    -- integrability of the pieces on the box
    have hP2int : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => P x ^ 2)
        (Submission.BoseGases.abox (m + 1) ℓ) volume :=
      Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hPm hPb
    have hQ2int : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => Q x ^ 2)
        (Submission.BoseGases.abox (m + 1) ℓ) volume :=
      Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hQm hQb
    have hPQint : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => P x * Q x)
        (Submission.BoseGases.abox (m + 1) ℓ) volume :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hPm hQm hPb hQb
    have hρim : Measurable (fun x : Submission.BoseGases.X (m + 1) => ρ (x i)) :=
      hρm.comp (measurable_pi_apply i)
    have hρi_b : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |ρ (x i)| ≤ Ξ :=
      fun x _ => hρb (x i)
    have hPb2 : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |P x ^ 2| ≤ B ^ 2 :=
      fun x hx => abs_sq_le_sq_of_abs_le (hPb x hx)
    have hQb2 : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |Q x ^ 2| ≤ (2 * B) ^ 2 :=
      fun x hx => abs_sq_le_sq_of_abs_le (hQb x hx)
    have hPQb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |P x * Q x| ≤ B * (2 * B) :=
      fun x hx => abs_mul_le_of_abs_le (hPb x hx) (hQb x hx)
    have hρP2int : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => ρ (x i) * P x ^ 2)
        (Submission.BoseGases.abox (m + 1) ℓ) volume :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hρim (hPm.pow_const 2) hρi_b hPb2
    have hρQ2int : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => ρ (x i) * Q x ^ 2)
        (Submission.BoseGases.abox (m + 1) ℓ) volume :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hρim (hQm.pow_const 2) hρi_b hQb2
    have hρPQint : IntegrableOn
        (fun x : Submission.BoseGases.X (m + 1) => ρ (x i) * (P x * Q x))
        (Submission.BoseGases.abox (m + 1) ℓ) volume :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hρim (hPm.mul hQm) hρi_b hPQb
    -- the vanishing of the condensate term
    have hPzero : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * P x ^ 2) = 0 := by
      set M : Submission.BoseGases.X (m + 1) → ℝ :=
        fun x => (1 / V) * ∫ z in A, Φ (Function.update x i z) with hMdef
      have hPM : ∀ x : Submission.BoseGases.X (m + 1),
          P x = M x * A.indicator (fun _ => (1 : ℝ)) (x i) := by
        intro x
        rw [hPdef, hMdef]
        simp only [Work.UBBInputs8.boxPInd]
      have hpoint : ∀ x : Submission.BoseGases.X (m + 1),
          ρ (x i) * P x ^ 2 = ρ (x i) * M x ^ 2 := by
        intro x
        rw [hPM x]
        by_cases hxi : x i ∈ A
        · rw [Set.indicator_of_mem hxi, mul_one]
        · rw [Set.indicator_of_notMem hxi, hsupp (x i) hxi]; ring
      have hconv : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * P x ^ 2)
          = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * M x ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      rw [hconv]
      have hMinv : ∀ (r : Submission.BoseGases.X m) (y y' : E3),
          M (Submission.BoseGases.kcInsN m i (y, r)) ^ 2
            = M (Submission.BoseGases.kcInsN m i (y', r)) ^ 2 := by
        intro r y y'
        have h1 : ∀ y : E3, M (Submission.BoseGases.kcInsN m i (y, r))
            = (1 / V) * ∫ z in A, Φ (Submission.BoseGases.kcInsN m i (z, r)) := by
          intro y
          simp only [hMdef, Submission.BoseGases.update_kcInsN]
        rw [h1 y, h1 y']
      have hpeel := slotWeightedPeel (ℓ := ℓ) i (w := ρ) (H := fun x => M x ^ 2) hMinv
      have hpeel' : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * M x ^ 2)
          = (∫ y in Submission.BoseGases.acube ℓ, ρ y)
            * (∫ r in Submission.BoseGases.abox m ℓ,
                M (Submission.BoseGases.kcInsN m i (0, r)) ^ 2) := by
        simpa using hpeel
      rw [hpeel']
      have hρacube : (∫ y in Submission.BoseGases.acube ℓ, ρ y) = 0 := by
        have hcongr : (∫ y in Submission.BoseGases.acube ℓ, ρ y)
            = ∫ y in Submission.BoseGases.acube ℓ, A.indicator ρ y := by
          apply integral_congr_ae
          filter_upwards with y
          by_cases hy : y ∈ A
          · rw [Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem hy, hsupp y hy]
        rw [hcongr, MeasureTheory.integral_indicator
          (μ := volume.restrict (Submission.BoseGases.acube ℓ)) hA]
        rw [MeasureTheory.Measure.restrict_restrict_of_subset (μ := (volume : Measure E3)) hAc]
        exact hρA
      rw [hρacube, zero_mul]
    -- the two estimates
    have hCS : |∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * (P x * Q x)|
        ≤ Ξ * (Real.sqrt (∫ x in Submission.BoseGases.abox (m + 1) ℓ, P x ^ 2)
              * Real.sqrt (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Q x ^ 2)) := by
      have h1 : |∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * (P x * Q x)|
          ≤ ∫ x in Submission.BoseGases.abox (m + 1) ℓ, |ρ (x i) * (P x * Q x)| := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (μ := volume.restrict (Submission.BoseGases.abox (m + 1) ℓ))
            (fun x : Submission.BoseGases.X (m + 1) => ρ (x i) * (P x * Q x))
      have h2 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, |ρ (x i) * (P x * Q x)|)
          ≤ Ξ * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, |P x * Q x|) := by
        have hpt : ∀ x : Submission.BoseGases.X (m + 1),
            |ρ (x i) * (P x * Q x)| ≤ Ξ * |P x * Q x| := by
          intro x
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hρb (x i)) (abs_nonneg _)
        have hf : Integrable
            (fun x : Submission.BoseGases.X (m + 1) => |ρ (x i) * (P x * Q x)|)
            (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) := hρPQint.abs
        have hg : Integrable
            (fun x : Submission.BoseGases.X (m + 1) => Ξ * |P x * Q x|)
            (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) :=
          hPQint.abs.const_mul Ξ
        calc (∫ x in Submission.BoseGases.abox (m + 1) ℓ, |ρ (x i) * (P x * Q x)|)
            ≤ ∫ x in Submission.BoseGases.abox (m + 1) ℓ, Ξ * |P x * Q x| :=
              integral_mono_ae hf hg (Filter.Eventually.of_forall hpt)
          _ = Ξ * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, |P x * Q x|) :=
              integral_const_mul Ξ _
      have h3 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, |P x * Q x|)
          ≤ Real.sqrt (∫ x in Submission.BoseGases.abox (m + 1) ℓ, P x ^ 2)
            * Real.sqrt (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Q x ^ 2) :=
        Work.BoseFixB1S.int_abs_mul_le_sqrt_mul_sqrt hPm.aestronglyMeasurable
          hQm.aestronglyMeasurable hP2int hQ2int
      exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left h3 hΞ0))
    have hQest : |∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Q x ^ 2|
        ≤ Ξ * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Q x ^ 2) := by
      have h1 : |∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Q x ^ 2|
          ≤ ∫ x in Submission.BoseGases.abox (m + 1) ℓ, |ρ (x i) * Q x ^ 2| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (μ := volume.restrict (Submission.BoseGases.abox (m + 1) ℓ))
            (fun x : Submission.BoseGases.X (m + 1) => ρ (x i) * Q x ^ 2)
      have h2 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, |ρ (x i) * Q x ^ 2|)
          ≤ Ξ * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Q x ^ 2) := by
        have hpt : ∀ x : Submission.BoseGases.X (m + 1),
            |ρ (x i) * Q x ^ 2| ≤ Ξ * Q x ^ 2 := by
          intro x
          rw [abs_mul, abs_of_nonneg (sq_nonneg (Q x))]
          exact mul_le_mul_of_nonneg_right (hρb (x i)) (sq_nonneg _)
        have hf : Integrable (fun x : Submission.BoseGases.X (m + 1) => |ρ (x i) * Q x ^ 2|)
            (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) := hρQ2int.abs
        have hg : Integrable (fun x : Submission.BoseGases.X (m + 1) => Ξ * Q x ^ 2)
            (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) := hQ2int.const_mul Ξ
        calc (∫ x in Submission.BoseGases.abox (m + 1) ℓ, |ρ (x i) * Q x ^ 2|)
            ≤ ∫ x in Submission.BoseGases.abox (m + 1) ℓ, Ξ * Q x ^ 2 :=
              integral_mono_ae hf hg (Filter.Eventually.of_forall hpt)
          _ = Ξ * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Q x ^ 2) :=
              integral_const_mul Ξ _
      exact le_trans h1 h2
    -- the expansion `ρΦ² = ρP² + 2ρPQ + ρQ²`
    have hexpand : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Φ x ^ 2)
        = (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * P x ^ 2)
          + 2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * (P x * Q x))
          + (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Q x ^ 2) := by
      have h1 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Φ x ^ 2)
          = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * (P x + Q x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hPQ x]
        by_cases hx : x i ∈ A
        · rw [Set.indicator_of_mem hx]; ring
        · rw [Set.indicator_of_notMem hx, hsupp (x i) hx]; ring
      rw [h1]
      have hpt : ∀ x : Submission.BoseGases.X (m + 1),
          ρ (x i) * (P x + Q x) ^ 2
            = ρ (x i) * P x ^ 2 + 2 * (ρ (x i) * (P x * Q x)) + ρ (x i) * Q x ^ 2 := by
        intro x; ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      have h12 : Integrable
          (fun x : Submission.BoseGases.X (m + 1) =>
            ρ (x i) * P x ^ 2 + 2 * (ρ (x i) * (P x * Q x)))
          (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) :=
        hρP2int.add (hρPQint.const_mul 2)
      calc (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              ρ (x i) * P x ^ 2 + 2 * (ρ (x i) * (P x * Q x)) + ρ (x i) * Q x ^ 2)
          = (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
                ρ (x i) * P x ^ 2 + 2 * (ρ (x i) * (P x * Q x)))
            + (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Q x ^ 2) :=
              MeasureTheory.integral_add h12 hρQ2int
        _ = (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * P x ^ 2)
              + 2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * (P x * Q x))
              + (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Q x ^ 2) := by
              rw [MeasureTheory.integral_add hρP2int (hρPQint.const_mul 2),
                  MeasureTheory.integral_const_mul]
    have hAP : 0 ≤ ∫ x in Submission.BoseGases.abox (m + 1) ℓ, P x ^ 2 :=
      integral_nonneg (f := fun x : Submission.BoseGases.X (m + 1) => P x ^ 2)
        (fun x => sq_nonneg (P x))
    calc |∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Φ x ^ 2|
        = |(∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * P x ^ 2)
            + 2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * (P x * Q x))
            + (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Q x ^ 2)| := by
          rw [hexpand]
      _ = |2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * (P x * Q x))
            + (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Q x ^ 2)| := by
          rw [hPzero, zero_add]
      _ ≤ |2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * (P x * Q x))|
            + |∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Q x ^ 2| :=
          abs_add_le _ _
      _ = 2 * |∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * (P x * Q x)|
            + |∫ x in Submission.BoseGases.abox (m + 1) ℓ, ρ (x i) * Q x ^ 2| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (Ξ * (Real.sqrt (∫ x in Submission.BoseGases.abox (m + 1) ℓ, P x ^ 2)
              * Real.sqrt (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Q x ^ 2)))
            + Ξ * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Q x ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hCS (by norm_num)) hQest
      _ = Ξ * (2 * Real.sqrt ((∫ x in Submission.BoseGases.abox (m + 1) ℓ, P x ^ 2)
              * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Q x ^ 2))
            + (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Q x ^ 2)) := by
          rw [Real.sqrt_mul hAP]; ring

end Work.BoseB1Cube
