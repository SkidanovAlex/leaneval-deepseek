import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero
import Submission.Work.BoseFixB1S.fluctuationDefsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.peelChiSq_le` — peeling the box-condensate square at `χ_{B(u)}²`

For the FS-faithful box projection `Pᵢ = boxPInd` of a continuous state `Φ`, the sliding cutoff
`χ = chiSmallB M ℓ d u` (supported in the sliding box `B(u) = dlBox ℓ d u`, `|B(u)| = boxMass`),
the square of the condensate part weighted by the cutoff is dominated by twice the `χ²`-mass of the
state plus twice the (weighted) excited count:

    ∑ᵢ ∫_{abox n ℓ} (PᵢΦ)² χ(xᵢ)²  ≤  2·flatScountB M ℓ d u Φ
        + 2·(chiSupAbs·chiSmallDecay M)²·cnPlusBoxInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) Φ .

## The mathematics

Everything is a pointwise identity on the support of the cutoff.  On the box indicator
`1_A(xᵢ)` one has `Φ = PᵢΦ + QᵢΦ` (`Qᵢ = boxQInd`), and `χ` vanishes off `A`, so

    Φ χ(xᵢ) = (PᵢΦ + QᵢΦ) χ(xᵢ) ,

hence, writing `F₁ = ∫(PᵢΦ)²χ(xᵢ)²`, `F₂ = ∫Φ²χ(xᵢ)²`, `F₃ = ∫(QᵢΦ)²χ(xᵢ)²`,
`F₄ = ∫(QᵢΦ)²` and `F₅ = ∫(PᵢΦ)(QᵢΦ)χ(xᵢ)²`,

    F₂ = F₁ + 2F₅ + F₃ .

The proved slot identity `Work.BoseFixB1S.Q0C.one_kernel` turns `F₁` into `κ·U` with
`κ = chiMass M ℓ d u = ∫χ²` and `U = ∫_{abox m ℓ}(oneRest …)² ≥ 0`; Cauchy–Schwarz gives
`F₅² ≤ F₁·F₃`; and `χ² ≤ C²` with `C = chiSupAbs·chiSmallDecay M` gives `F₃ ≤ C²F₄`.  Therefore

    F₁ + 4F₅ + 2F₃ + 2C²F₄ ≥ F₁ − 4√(F₁F₃) + 4F₃ = (√F₁ − 2√F₃)² ≥ 0 ,

i.e. `F₁ ≤ 2F₂ + 2C²F₄`, which is the per-slot inequality.  Summing over the slots and using
`flatScountB = Σᵢ∫Φ²χ(xᵢ)²` and the definition of `cnPlusBoxInd` gives the claim.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseB1Cube

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- The cutoff mass as a set integral: `∫_{dlBox ℓ d u} χ_{B(u)}² = chiMass M ℓ d u`. -/
theorem setIntegral_chiSmallB_sq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) :
    (∫ z in Submission.BoseGases.dlBox ℓ d u, (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
      = Work.SmallBoxSliding.chiMass M ℓ d u := by
  rw [Work.SmallBoxSliding.chiMass]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)
  by_contra hne
  have h0 : Submission.BoseGases.chiSmallB M ℓ d u z ≠ 0 := by
    intro hzero
    exact hne (by rw [hzero]; ring)
  exact hz (Work.BoseFixB1S.chiSmallB_support_subset_dlBox (M := M) hM hℓ hd u h0)

/-- `flatScountB` is the sum over the slots of the `χ²`-weighted squares:
`flatScountB M ℓ d u Φ = Σᵢ∫_{abox n ℓ}Φ²·χ(xᵢ)²`. -/
theorem flatScountB_eq_sum {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : E3) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1.flatScountB M ℓ d u Φ
      = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by
  rw [Work.BoseFixB1.flatScountB]
  simp only [Work.BoseFixB1.nCountB]
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
        = ∑ i : Fin n, (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by
    intro x
    rw [Finset.mul_sum]
  rw [show (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ∑ i : Fin n, (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
      from integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_finsetSum]
  intro i _
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := Φ) hΦc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (Submission.BoseGases.zero_mem_abox hℓ.le))
  have hχcont : Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.chiSmallB M ℓ d u (x i)) :=
    (Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).comp (continuous_apply i)
  have hχb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Submission.BoseGases.chiSmallB M ℓ d u (x i)|
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    fun x _ => Work.BoseFixB1S.abs_chiSmallB_le_supB hM u (x i)
  exact Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hΦc.measurable.pow_const 2)
    (hχcont.measurable.pow_const 2)
    (fun x hx => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (Φ x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB x hx) 2)
    (fun x hx => by
      rw [abs_of_nonneg (sq_nonneg _),
        ← sq_abs (Submission.BoseGases.chiSmallB M ℓ d u (x i))]
      exact pow_le_pow_left₀ (abs_nonneg _) (hχb x hx) 2)

/-- **The per-slot peeling inequality.**  For one slot `i` of the `(m+1)`-particle box,

    ∫(PᵢΦ)²χ(xᵢ)² ≤ 2∫Φ²χ(xᵢ)² + 2(chiSupAbs·chiSmallDecay M)²∫(QᵢΦ)² . -/
theorem slotPeel_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) {m : ℕ} {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦc : Continuous Φ)
    (i : Fin (m + 1)) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
      ≤ 2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
        + 2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            * (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) := by
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set χ : E3 → ℝ := Submission.BoseGases.chiSmallB M ℓ d u with hχdef
  set C : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M with hCdef
  set P : Submission.BoseGases.X (m + 1) → ℝ := Work.UBBInputs8.boxPInd V A i Φ with hPdef
  set Q : Submission.BoseGases.X (m + 1) → ℝ := Work.UBBInputs8.boxQInd V A i Φ with hQdef
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : V = (volume : Measure E3).real A := by
    rw [hVdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hVnn : 0 ≤ V := hVeq ▸ MeasureTheory.measureReal_nonneg
  have hχbd : ∀ z : E3, |χ z| ≤ C := by
    intro z
    rw [hχdef, hCdef]
    exact Work.BoseFixB1S.abs_chiSmallB_le_supB hM u z
  have hχcont : Continuous χ := by
    rw [hχdef]; exact Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u
  have hCnn : 0 ≤ C := le_trans (abs_nonneg (χ 0)) (hχbd 0)
  -- the pointwise link between `P`, `Q`, `Φ` and `χ`
  have hQeq : Q = fun x : Submission.BoseGases.X (m + 1) =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - P x := by
    rw [hQdef, hPdef]
    rfl
  have hPQ : ∀ x : Submission.BoseGases.X (m + 1),
      A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x = P x + Q x := by
    intro x
    rw [hQeq]
    ring
  have hχind : ∀ x : Submission.BoseGases.X (m + 1),
      χ (x i) * A.indicator (fun _ => (1 : ℝ)) (x i) = χ (x i) := by
    intro x
    by_cases h : x i ∈ A
    · rw [Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, mul_zero]
      have h0 : χ (x i) = 0 := by
        by_contra hne
        exact h (Work.BoseFixB1S.chiSmallB_support_subset_dlBox (M := M) hM hℓ hd u
          (by rwa [hχdef] at hne))
      rw [h0]
  rcases eq_or_lt_of_le hVnn with hV0 | hVpos
  · -- the sliding box is a null set: the projection vanishes identically
    have hPz : P = 0 := by
      rw [hPdef, ← hV0]
      funext x
      simp [Work.UBBInputs8.boxPInd]
    rw [hPz]
    have h1 : 0 ≤ (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Φ x) ^ 2 * (χ (x i)) ^ 2) :=
      integral_nonneg (fun x => by positivity)
    have h2 : 0 ≤ (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Q x) ^ 2) :=
      integral_nonneg (fun x => sq_nonneg _)
    have h3 : 0 ≤ 2 * C ^ 2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Q x) ^ 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) h2
    simp only [Pi.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, integral_zero]
    linarith
  · -- the generic case
    have hPmeas : Measurable P := by
      rw [hPdef]
      exact Work.BoseFixB1S.measurable_boxPInd V A hAmeas i hΦc.measurable
    have hQmeas : Measurable Q := by
      rw [hQeq]
      exact (((measurable_const.indicator hAmeas).comp (measurable_pi_apply i)).mul
        hΦc.measurable).sub hPmeas
    have hχimeas : Measurable (fun x : Submission.BoseGases.X (m + 1) => χ (x i)) :=
      hχcont.measurable.comp (measurable_pi_apply i)
    obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact (m + 1) hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox (m + 1) ℓ) (f := Φ) hΦc.continuousOn
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (Submission.BoseGases.zero_mem_abox hℓ.le))
    have hΦb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |Φ x| ≤ B :=
      fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
    have hPb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |P x| ≤ B := by
      intro x hx
      rw [hPdef]
      exact Work.BoseFixB1S.abs_boxPInd_le hℓ hVpos hAmeas hVeq hAc i hΦb x hx
    have hQb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |Q x| ≤ 2 * B := by
      intro x hx
      rw [hQeq]
      have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ B := by
        have h2 : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
          by_cases h : x i ∈ A
          · rw [Set.indicator_of_mem h]; norm_num
          · rw [Set.indicator_of_notMem h]; norm_num
        rw [abs_mul]
        calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x|
            ≤ 1 * B := mul_le_mul h2 (hΦb x hx) (abs_nonneg _) zero_le_one
          _ = B := one_mul B
      calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x + -P x|
          ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| + |-P x| := abs_add_le _ _
        _ = |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| + |P x| := by rw [abs_neg]
        _ ≤ B + B := add_le_add h1 (hPb x hx)
        _ = 2 * B := by ring
    -- integrability of the five integrands
    have hIP : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) =>
        (P x) ^ 2 * (χ (x i)) ^ 2) (Submission.BoseGases.abox (m + 1) ℓ) :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hPmeas.pow_const 2) (hχimeas.pow_const 2)
        (fun x hx => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (P x)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hPb x hx) 2)
        (fun x hx => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (χ (x i))]
          exact pow_le_pow_left₀ (abs_nonneg _) (hχbd (x i)) 2)
    have hIΦ : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) =>
        (Φ x) ^ 2 * (χ (x i)) ^ 2) (Submission.BoseGases.abox (m + 1) ℓ) :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hΦc.measurable.pow_const 2)
        (hχimeas.pow_const 2)
        (fun x hx => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (Φ x)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hΦb x hx) 2)
        (fun x hx => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (χ (x i))]
          exact pow_le_pow_left₀ (abs_nonneg _) (hχbd (x i)) 2)
    have hIQχ : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) =>
        (Q x) ^ 2 * (χ (x i)) ^ 2) (Submission.BoseGases.abox (m + 1) ℓ) :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hQmeas.pow_const 2) (hχimeas.pow_const 2)
        (fun x hx => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (Q x)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hQb x hx) 2)
        (fun x hx => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (χ (x i))]
          exact pow_le_pow_left₀ (abs_nonneg _) (hχbd (x i)) 2)
    have hIQ : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => (Q x) ^ 2)
        (Submission.BoseGases.abox (m + 1) ℓ) :=
      Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hQmeas hQb
    have hIPQχ : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) =>
        (P x * Q x) * (χ (x i)) ^ 2) (Submission.BoseGases.abox (m + 1) ℓ) :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ (hPmeas.mul hQmeas) (hχimeas.pow_const 2)
        (fun x hx => by
          rw [abs_mul]
          exact mul_le_mul (hPb x hx) (hQb x hx) (abs_nonneg _) hB0)
        (fun x hx => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (χ (x i))]
          exact pow_le_pow_left₀ (abs_nonneg _) (hχbd (x i)) 2)
    -- abbreviations
    set F1 : ℝ := ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (P x) ^ 2 * (χ (x i)) ^ 2
      with hF1def
    set F2 : ℝ := ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Φ x) ^ 2 * (χ (x i)) ^ 2
      with hF2def
    set F3 : ℝ := ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Q x) ^ 2 * (χ (x i)) ^ 2
      with hF3def
    set F4 : ℝ := ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Q x) ^ 2 with hF4def
    set F5 : ℝ := ∫ x in Submission.BoseGases.abox (m + 1) ℓ, P x * Q x * (χ (x i)) ^ 2
      with hF5def
    have hF1n : 0 ≤ F1 := by
      rw [hF1def]; exact integral_nonneg (fun x => by positivity)
    have hF3n : 0 ≤ F3 := by
      rw [hF3def]; exact integral_nonneg (fun x => by positivity)
    -- (1) `F2 = F1 + 2 F5 + F3`
    have hF2eq : F2 = F1 + 2 * F5 + F3 := by
      have hpt : ∀ x : Submission.BoseGases.X (m + 1),
          (Φ x) ^ 2 * (χ (x i)) ^ 2
            = ((P x) ^ 2 * (χ (x i)) ^ 2 + 2 * (P x * Q x * (χ (x i)) ^ 2))
              + (Q x) ^ 2 * (χ (x i)) ^ 2 := by
        intro x
        have hkey : χ (x i) * Φ x = χ (x i) * P x + χ (x i) * Q x := by
          have h1 : χ (x i) * Φ x
              = χ (x i) * (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) := by
            calc χ (x i) * Φ x
                = (χ (x i) * A.indicator (fun _ => (1 : ℝ)) (x i)) * Φ x := by rw [hχind x]
              _ = χ (x i) * (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) := by ring
          rw [h1, hPQ x]; ring
        calc (Φ x) ^ 2 * (χ (x i)) ^ 2
            = (χ (x i) * Φ x) ^ 2 := by ring
          _ = (χ (x i) * P x + χ (x i) * Q x) ^ 2 := by rw [hkey]
          _ = ((P x) ^ 2 * (χ (x i)) ^ 2 + 2 * (P x * Q x * (χ (x i)) ^ 2))
                + (Q x) ^ 2 * (χ (x i)) ^ 2 := by ring_nf
      have hcongr : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Φ x) ^ 2 * (χ (x i)) ^ 2)
          = ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              ((P x) ^ 2 * (χ (x i)) ^ 2 + 2 * (P x * Q x * (χ (x i)) ^ 2))
                + (Q x) ^ 2 * (χ (x i)) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
      have step1 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            ((P x) ^ 2 * (χ (x i)) ^ 2 + 2 * (P x * Q x * (χ (x i)) ^ 2))
              + (Q x) ^ 2 * (χ (x i)) ^ 2)
          = (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              (P x) ^ 2 * (χ (x i)) ^ 2 + 2 * (P x * Q x * (χ (x i)) ^ 2))
            + (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
                (Q x) ^ 2 * (χ (x i)) ^ 2) :=
        integral_add (hIP.add (hIPQχ.const_mul 2)) hIQχ
      have step2 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              (P x) ^ 2 * (χ (x i)) ^ 2 + 2 * (P x * Q x * (χ (x i)) ^ 2))
          = (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (P x) ^ 2 * (χ (x i)) ^ 2)
            + (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
                2 * (P x * Q x * (χ (x i)) ^ 2)) :=
        integral_add hIP (hIPQχ.const_mul 2)
      have step3 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            2 * (P x * Q x * (χ (x i)) ^ 2))
          = 2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              P x * Q x * (χ (x i)) ^ 2) :=
        integral_const_mul 2 _
      rw [hF2def, hF1def, hF5def, hF3def, hcongr, step1, step2, step3]
    -- (2) `F1 = κ U` via the slot identity
    have hUint : Integrable (fun z : E3 => χ z ^ 2) (volume.restrict A) := by
      have hfinA : (volume : Measure E3) A < ∞ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
      have : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfinA⟩
      refine Integrable.of_bound (hχcont.measurable.pow_const 2).aestronglyMeasurable (C ^ 2) ?_
      exact Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (χ z)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hχbd z) 2)
    have hF1eq : F1 = Work.SmallBoxSliding.chiMass M ℓ d u
        * ∫ r in Submission.BoseGases.abox m ℓ, (Work.BoseFixB1S.Q0C.oneRest V A i Φ r) ^ 2 := by
      have hker := Work.BoseFixB1S.Q0C.one_kernel (volA := V) (A := A) hℓ hVpos hAmeas hAc
        hVeq i (Ψ := Φ) hΦc (g := fun z : E3 => χ z ^ 2) hUint
      have hAr : (∫ z in A, (fun z : E3 => χ z ^ 2) z)
          = Work.SmallBoxSliding.chiMass M ℓ d u := by
        show (∫ z in A, χ z ^ 2) = Work.SmallBoxSliding.chiMass M ℓ d u
        rw [hAdef, hχdef]
        exact setIntegral_chiSmallB_sq hM hℓ hd u
      rw [hAr] at hker
      rw [hF1def, hPdef]
      exact hker
    -- (3) Cauchy–Schwarz: `F5² ≤ F1 F3`
    have : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top (m + 1) ℓ hℓ.le⟩
    have hCS : F5 ^ 2 ≤ F1 * F3 := by
      set f : Submission.BoseGases.X (m + 1) → ℝ := fun x => P x * χ (x i) with hfdef
      set g : Submission.BoseGases.X (m + 1) → ℝ := fun x => Q x * χ (x i) with hgdef
      have hfae : AEStronglyMeasurable f ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) ℓ)) := by
        rw [hfdef]; exact (hPmeas.mul hχimeas).aestronglyMeasurable
      have hga : AEStronglyMeasurable g ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) ℓ)) := by
        rw [hgdef]; exact (hQmeas.mul hχimeas).aestronglyMeasurable
      have h := Work.BoseFixB1S.Q0C.integral_mul_sq_le
        (μ := (volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) ℓ))
        (f := f) (g := g) (Cf := B * C) (Cg := 2 * B * C) hfae hga
        (by
          rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (m + 1) ℓ)]
          exact Filter.Eventually.of_forall (fun x hx => by
            rw [hfdef, abs_mul]
            exact mul_le_mul (hPb x hx) (hχbd (x i)) (abs_nonneg _) hB0))
        (by
          rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (m + 1) ℓ)]
          exact Filter.Eventually.of_forall (fun x hx => by
            rw [hgdef, abs_mul]
            exact mul_le_mul (hQb x hx) (hχbd (x i)) (abs_nonneg _) (by linarith)))
      have e1 : (∫ x, f x * g x ∂((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
            (Submission.BoseGases.abox (m + 1) ℓ))) = F5 := by
        rw [hF5def]
        apply integral_congr_ae
        filter_upwards with x
        rw [hfdef, hgdef]; ring
      have e2 : (∫ x, f x ^ 2 ∂((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
            (Submission.BoseGases.abox (m + 1) ℓ))) = F1 := by
        rw [hF1def]
        apply integral_congr_ae
        filter_upwards with x
        rw [hfdef]; ring
      have e3 : (∫ x, g x ^ 2 ∂((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
            (Submission.BoseGases.abox (m + 1) ℓ))) = F3 := by
        rw [hF3def]
        apply integral_congr_ae
        filter_upwards with x
        rw [hgdef]; ring
      rw [e1, e2, e3] at h
      exact h
    -- (4) `F3 ≤ C² F4`
    have hF34 : F3 ≤ C ^ 2 * F4 := by
      rw [hF3def, hF4def]
      have hmono : (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            (Q x) ^ 2 * (χ (x i)) ^ 2) ≤ ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            C ^ 2 * (Q x) ^ 2 :=
        setIntegral_mono_on hIQχ (hIQ.const_mul (C ^ 2))
          (Submission.BoseGases.abox_measurable (m + 1) ℓ) (fun x _ => by
            rw [show (Q x) ^ 2 * (χ (x i)) ^ 2 = (χ (x i)) ^ 2 * (Q x) ^ 2 by ring]
            have hsq : (χ (x i)) ^ 2 ≤ C ^ 2 := by
              rw [← sq_abs (χ (x i))]
              exact pow_le_pow_left₀ (abs_nonneg _) (hχbd (x i)) 2
            exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
      rw [MeasureTheory.integral_const_mul] at hmono
      linarith [hmono]
    -- assembly
    have hF5low : -Real.sqrt (F1 * F3) ≤ F5 := by
      have hs : F5 ^ 2 ≤ (Real.sqrt (F1 * F3)) ^ 2 := by
        rw [Real.sq_sqrt (mul_nonneg hF1n hF3n)]; exact hCS
      exact (abs_le.mp (abs_le_of_sq_le_sq hs (Real.sqrt_nonneg _))).1
    have hAM : 4 * Real.sqrt (F1 * F3) ≤ F1 + 4 * F3 := by
      have hsq : (Real.sqrt F1 - 2 * Real.sqrt F3) ^ 2
          = F1 + 4 * F3 - 4 * (Real.sqrt F1 * Real.sqrt F3) := by
        rw [sub_sq, Real.sq_sqrt hF1n, mul_pow, Real.sq_sqrt hF3n]; ring
      have hmul : Real.sqrt F1 * Real.sqrt F3 = Real.sqrt (F1 * F3) :=
        (Real.sqrt_mul hF1n F3).symm
      nlinarith [sq_nonneg (Real.sqrt F1 - 2 * Real.sqrt F3)]
    have hkey : 0 ≤ F1 + 4 * F5 + 2 * F3 + 2 * C ^ 2 * F4 := by
      nlinarith [hF5low, hAM, hF34]
    have hgoal : F1 ≤ 2 * F2 + 2 * C ^ 2 * F4 := by
      nlinarith [hkey, hF2eq]
    exact hgoal

/-- **The peeling of the box-condensate square.** -/
theorem peelChiSq_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
      ≤ 2 * Work.BoseFixB1.flatScountB M ℓ d u Φ
        + 2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) Φ := by
  cases n with
  | zero =>
    have h1 : 0 ≤ Work.BoseFixB1.flatScountB M ℓ d u Φ := by
      rw [Work.BoseFixB1.flatScountB]
      simp only [Work.BoseFixB1.nCountB]
      exact integral_nonneg (fun x => by positivity)
    have h2 : 0 ≤ Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) Φ := by
      rw [Work.UBBInputs8.cnPlusBoxInd]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have h3 : 0 ≤ 2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
        * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) Φ :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) h2
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    linarith
  | succ m =>
    have hflat := flatScountB_eq_sum (M := M) (d := d) hM hℓ u hΦc
    have hsum : (∑ i : Fin (m + 1), ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
            * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
        ≤ ∑ i : Fin (m + 1),
            (2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
                (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
              + 2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
                  * (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
                      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)) :=
      Finset.sum_le_sum (fun i _ => slotPeel_le (M := M) hM hℓ hd u hΦc i)
    have hsplit : (∑ i : Fin (m + 1),
            (2 * (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
                (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
              + 2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
                  * (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
                      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)))
        = 2 * (∑ i : Fin (m + 1), ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
          + 2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
              * ∑ i : Fin (m + 1), ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
                  (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hcn : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) Φ
        = ∑ i : Fin (m + 1), ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 := rfl
    rw [hcn, hflat]
    exact le_trans hsum (le_of_eq hsplit)

end Work.BoseB1Cube
