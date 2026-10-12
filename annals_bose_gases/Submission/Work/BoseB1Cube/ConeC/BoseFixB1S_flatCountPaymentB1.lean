import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxCrossExpansionB1S
import Submission.Work.BoseFixB1S.boxQSum_sub_boxA2_blockSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.flatCountPaymentB1` — the count bookkeeping of the flat branch

Two machine-checked pieces of the *flat branch* of `Work.BoseFixB1S.PerBoxF` (see
`Submission/Work/BoseFixB1S/FINDING_perBoxFWeightB1.md` §7.6, items (1) and (2)):

* `flatCountIdentity` — the **`n₀ + n₊ = n` identity in expectation** (FS `eq:smallboxnn0n+`):
  with `P_{B,i}`, `Q_{B,i}` the FS-faithful box projections of `Work.UBBInputs8`
  (`P_{B,i}Ψ = |B|⁻¹⟨1_B,·⟩1_B` in slot `i`, `Q_{B,i} = 1_{B,i} − P_{B,i}`),

      Σᵢ ∫_{abox} (P_{B,i}Φ)² + Σᵢ ∫_{abox} (Q_{B,i}Φ)²
        = ∫_{abox} (Σᵢ 1_A(xᵢ))·Φ² .

  Equivalently `boxFlatCount + boxQCount = ∫ Φ²·n` with `n = Σᵢ1_{A,i}` the (sharp) particle
  count of the box.  This is the passage that makes the *flat* hypothesis
  `boxQCount < γ N ‖Φ‖²` usable: it converts `boxQCount` small into
  `boxFlatCount ≥ ∫Φ² n − γN‖Φ‖²`, i.e. `n₀ ≈ n` in expectation, which is exactly what
  `A₀`'s condensate-count pair term `n₀(n₀−1)/(2|B|²)∬w₂` needs (FS `lm:appinteractionestimate`).

  The proof is the per-slot Pythagoras `(P_iΦ)² + (Q_iΦ)² = (1_A(·ᵢ)Φ)² − 2P_iΦ·Q_iΦ` together
  with the corpus's *proved* orthogonality `Work.BoseSplit.pIndOrth`
  (`∫ P_iΦ·Q_iΦ = 0`).

* `flatPairCountPay` — the **Cauchy–Schwarz pair payment** of the flat count:
  with `S := boxFlatCount`, `N := ‖Φ‖²`, the corpus's *proved* `boxFlatSqJensen`
  (`S² − S·N ≤ N·boxPairCount`) divided by `N > 0` gives

      S²/N − S  ≤  boxPairCount .

  This is `A₀`'s pair term at the state level with the *Cauchy–Schwarz* value `S²/N` in place of
  the exact `PP`-value `‖ΛΦ‖²` (`Λ = ΣᵢP_{B,i}`), which is larger — and *that* replacement is
  precisely why this route escapes the three refutations of the `PP`-count lower bounds
  `Work.BoseFixB1S.flatPairLower{,V2,V3}` (`FINDING_flatPairLower{,V2,V3}_false.md`).

Both statements are `sorry`-free; `#print axioms` is `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

/-- The box indicator is bounded by `1`. -/
private lemma abs_boxInd_le_one {A : Set (EuclideanSpace ℝ (Fin 3))}
    (t : EuclideanSpace ℝ (Fin 3)) : |A.indicator (fun _ => (1 : ℝ)) t| ≤ 1 := by
  by_cases ht : t ∈ A
  · rw [Set.indicator_of_mem ht]; norm_num
  · rw [Set.indicator_of_notMem ht]; norm_num

/-- Linearity of the box integral for two functions written with explicit applications
(the `Pi`-spine-free form, so that `calc` steps match definitionally). -/
private lemma integral_add_lambda {N : ℕ} {ℓ : ℝ} {f g : X N → ℝ}
    (hf : IntegrableOn f (abox N ℓ) volume) (hg : IntegrableOn g (abox N ℓ) volume) :
    (∫ x in abox N ℓ, f x + g x) = (∫ x in abox N ℓ, f x) + (∫ x in abox N ℓ, g x) :=
  MeasureTheory.integral_add hf hg

/-! ## 1. The per-slot Pythagoras for the box projections -/

/-- **Per-slot count identity.**  For each slot `i` the box projections split the box-supported
square: `∫(P_iΦ)² + ∫(Q_iΦ)² = ∫ 1_A(xᵢ)·Φ²`. -/
theorem flat_add_q_slot {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      = ∫ x in abox N ℓ, A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
  -- a bound for `Φ` on the box, hence for `PᵢΦ`, `QᵢΦ`
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (zero_mem_abox hℓ.le))
  have hbΦ : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  have hbP : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    abs_boxPInd_le (N := N) (A := A) hℓ hvol hA hvolA hAc i hbΦ
  have hbXi : ∀ x ∈ abox N ℓ,
      |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
    intro x hx
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
        = |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| := abs_mul _ _
      _ ≤ 1 * C := mul_le_mul (abs_boxInd_le_one (x i)) (hbΦ x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hbQ : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * C := by
    intro x hx
    have h2 : Work.UBBInputs8.boxQInd volA A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
          - Work.UBBInputs8.boxPInd volA A i Φ x := rfl
    rw [h2]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
            - Work.UBBInputs8.boxPInd volA A i Φ x|
        ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
            + |Work.UBBInputs8.boxPInd volA A i Φ x| := abs_sub _ _
      _ ≤ C + C := add_le_add (hbXi x hx) (hbP x hx)
      _ = 2 * C := by ring
  -- measurability
  have hmΦ : Measurable Φ := hΦc.measurable
  have him : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) :=
    (((measurable_const.indicator hA).comp (measurable_pi_apply i))).mul hmΦ
  have hmP : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    measurable_boxPInd volA A hA i hmΦ
  have hmQ : Measurable (Work.UBBInputs8.boxQInd volA A i Φ) := by
    have h2 : Work.UBBInputs8.boxQInd volA A i Φ
        = fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
            - Work.UBBInputs8.boxPInd volA A i Φ x := rfl
    rw [h2]
    exact him.sub hmP
  -- integrability of the three pieces
  have hIP : IntegrableOn (fun x : X N => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      (abox N ℓ) volume := integrableOn_sq_of_bound (N := N) hℓ hmP hbP
  have hIQ : IntegrableOn (fun x : X N => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      (abox N ℓ) volume := integrableOn_sq_of_bound (N := N) hℓ hmQ hbQ
  have hIX : IntegrableOn
      (fun x : X N => (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2) (abox N ℓ) volume :=
    integrableOn_sq_of_bound (N := N) hℓ him hbXi
  have hIPQ : IntegrableOn
      (fun x : X N => Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A i Φ x)
      (abox N ℓ) volume := integrableOn_mul_of_bound (N := N) hℓ hmP hmQ hbP hbQ
  have hPG : IntegrableOn
      (fun x : X N => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
        + 2 * (Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A i Φ x))
      (abox N ℓ) volume := hIP.add (hIPQ.const_mul 2)
  -- the orthogonality `∫ PᵢΦ·QᵢΦ = 0`
  have horth : (∫ x in abox N ℓ,
      Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A i Φ x) = 0 := by
    simpa only [Work.UBBInputs8.boxQInd] using
      (Work.BoseSplit.pIndOrth (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc i hΦc)
  -- the pointwise split `(P + Q)² = P² + 2(P·Q) + Q²`, `P + Q = 1_AΦ`, `(1_AΦ)² = 1_AΦ²`
  have hpt : ∀ x : X N,
      (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2
        = (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
          + 2 * (Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A i Φ x)
          + (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 := by
    intro x
    have hsum : Work.UBBInputs8.boxPInd volA A i Φ x + Work.UBBInputs8.boxQInd volA A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
      simp only [Work.UBBInputs8.boxQInd]
      ring
    rw [← hsum]
    ring
  have hpt2 : ∀ x : X N, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
    intro x
    by_cases hxi : x i ∈ A
    · rw [Set.indicator_of_mem hxi]; ring
    · rw [Set.indicator_of_notMem hxi]; ring
  -- integrate the pointwise identity, in three steps
  have hX' : (∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2)
      = ∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt2)
  have hmain : (∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2)
      = (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
          + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) := by
    calc (∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2)
        = ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
            + 2 * (Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A i Φ x)
            + (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ x in abox N ℓ, ((Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
              + 2 * (Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A i Φ x)))
            + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) :=
          integral_add_lambda hPG hIQ
      _ = ((∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
              + 2 * (∫ x in abox N ℓ,
                  Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxQInd volA A i Φ x))
            + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) := by
          rw [integral_add_lambda hIP (hIPQ.const_mul 2), MeasureTheory.integral_const_mul]
      _ = (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
            + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) := by
          rw [horth]; ring
  exact hmain.symm.trans hX'

/-! ## 2. The `n₀ + n₊ = n` identity in expectation -/

/-- **FS's `n₀ + n₊ = n` identity, in expectation.**  With `A` the (sharp) small box of the
sliding family, `volA = |A|`, `A ⊆ acube ℓ`,

    `boxFlatCount + boxQCount = ∫_{abox} (Σᵢ 1_A(xᵢ))·Φ²`,

i.e. `n₀ + n₊ = n` at the state level.  See the module docstring for why the flat branch of
`PerBoxF` needs exactly this. -/
theorem flatCountIdentity {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A Φ + Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = ∫ x in abox N ℓ,
          (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2 := by
  have hslot : ∀ i : Fin N,
      (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
          + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        = ∫ x in abox N ℓ, A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 :=
    fun i => flat_add_q_slot (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc hΦc i
  -- integrability of each slot integrand (needed to move the sum under the integral)
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (zero_mem_abox hℓ.le))
  have hbΦ : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  have hmΦ : Measurable Φ := hΦc.measurable
  have hInt : ∀ i : Fin N, IntegrableOn
      (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) (abox N ℓ) volume := by
    intro i
    have him : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) :=
      (((measurable_const.indicator hA).comp (measurable_pi_apply i))).mul (hmΦ.pow_const 2)
    have hb : ∀ x ∈ abox N ℓ, |A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2| ≤ C ^ 2 := by
      intro x hx
      calc |A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2|
          = |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ^ 2 := by
            rw [abs_mul, abs_pow]
        _ ≤ 1 * C ^ 2 := by
            refine mul_le_mul (abs_boxInd_le_one (x i)) ?_ (pow_nonneg (abs_nonneg _) 2)
              zero_le_one
            exact pow_le_pow_left₀ (abs_nonneg _) (hbΦ x hx) 2
        _ = C ^ 2 := one_mul _
    exact IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le) him.aestronglyMeasurable (|C ^ 2|) (by
      rw [ae_restrict_iff' (abox_measurable N ℓ)]
      refine ae_of_all _ (fun x hx => ?_)
      rw [Real.norm_eq_abs]
      exact le_trans (hb x hx) (le_abs_self _))
  -- sum the slot identities, then move the sum under the integral
  have hsum1 : (∑ i : Fin N, ((∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)))
      = ∑ i : Fin N, ∫ x in abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 :=
    Finset.sum_congr rfl fun i _ => hslot i
  rw [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount, ← Finset.sum_add_distrib, hsum1,
    ← MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hInt i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
      = (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2
  rw [Finset.sum_mul]

/-! ## 3. The Cauchy–Schwarz pair payment of the flat count -/

/-- **The pair payment of the flat count.**  Dividing the corpus's *proved* `boxFlatSqJensen`
(`S² − S·N ≤ N·boxPairCount`) by `N = ‖Φ‖² > 0` gives `S²/N − S ≤ boxPairCount`, i.e. the
`PP`-count dominates the *Cauchy–Schwarz* value of `A₀`'s condensate-count pair term. -/
theorem flatPairCountPay {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hN2 : 0 < ∫ x in abox N ℓ, (Φ x) ^ 2) :
    (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
        / (∫ x in abox N ℓ, (Φ x) ^ 2)
      - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
    ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
  have h := Work.BoseFixB1S.boxFlatSqJensen (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA
    hAc hΦc
  have hIne : (∫ x in abox N ℓ, (Φ x) ^ 2) ≠ 0 := ne_of_gt hN2
  have hdiv : (((Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * (∫ x in abox N ℓ, (Φ x) ^ 2))
        / (∫ x in abox N ℓ, (Φ x) ^ 2))
      ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
    have h' := div_le_div_of_nonneg_right h hN2.le
    rwa [mul_div_cancel_left₀ _ hIne] at h'
  have hrew : (((Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * (∫ x in abox N ℓ, (Φ x) ^ 2))
        / (∫ x in abox N ℓ, (Φ x) ^ 2))
      = (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) ^ 2
          / (∫ x in abox N ℓ, (Φ x) ^ 2)
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
    rw [sub_div, mul_div_cancel_right₀ _ hIne]
  rwa [hrew] at hdiv

end Work.BoseFixB1S
