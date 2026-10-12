import ChallengeDeps
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB3.Eps.convI_abs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxFragmentsIntegrable`

The six `pairSet`-integrability fragments of the box potential split at the *singular* localised
kernels `wSmallPair M ℓ d u h` / `wSmall1Pair h M ℓ d u` of FS `eq:HBU` (they contain
`1/(χ_M⋆χ_M)` and are neither bounded nor continuous).

The tool is `Work.BoseFixB1.integrableOn_slot_wSmallPair`: a *bounded, a.e. strongly measurable*
slot multiplier `S` times `wSmallPair M ℓ d u f (x i) (x j)` is `IntegrableOn (abox N ℓ)` as soon
as `f` is integrable with `tsupport f ⊆ ball 0 R` and `R ≤ (ℓd)/16`.  The multipliers below are
products of box readings `P_i`/`Q_i` of a *continuous* `Φ`, hence bounded on the compact box
(`abs_boxPInd_le`, `abs_boxQInd_le` — restated here without the `0 < volA` hypothesis, since the
target does not provide `0 < boxMass ℓ d u`; when `volA = 0` the projections vanish identically);
the only non-continuous ingredient is the `ω`-factor, bounded a.e. by `1`
(`Submission.BoseGases.w0_abs_le_one_box_ae`).

No continuity or decay of `Φ` beyond continuity is used: compactness of `abox N ℓ` supplies the
bounds.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Clean

open Submission.BoseGases Work.UBBInputs8

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary helpers -/

/-- `v` vanishes outside `ball 0 R` (from the support hypothesis on its closed support). -/
private theorem vZeroB {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) {z : ℝ³} (hz : R ≤ ‖z‖) : v z = 0 := by
  by_contra h
  have hmem : z ∈ tsupport v := subset_tsupport v (by simpa using h)
  have hball : z ∈ Metric.ball (0 : ℝ³) R := hv_supp hmem
  have hlt : ‖z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hball
  linarith

/-- `|a·b| ≤ A·B` when `|a| ≤ A`, `|b| ≤ B` and `0 ≤ A`. -/
private theorem absMulBnd {a b A B : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

/-- **`P`-reading bound on the box**, without the hypothesis `0 < volA` (if `volA = 0` the
projection vanishes identically because `1 / 0 = 0` in `ℝ`). -/
theorem abs_boxPInd_le_nonneg {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 ≤ volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ : X N → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ abox N ℓ, |boxPInd volA A i Ψ x| ≤ C := by
  rcases lt_or_eq_of_le hvol with hpos | h0
  · exact Work.BoseFixB1S.abs_boxPInd_le hℓ hpos hA hvolA hAc i hC
  · intro x hx
    rw [← h0]
    simp only [Work.UBBInputs8.boxPInd, div_zero, zero_mul, abs_zero]
    exact hC0

/-- **`Q`-reading bound on the box**, without the hypothesis `0 < volA`. -/
theorem abs_boxQInd_le_nonneg {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 ≤ volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ : X N → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ abox N ℓ, |boxQInd volA A i Ψ x| ≤ 2 * C := by
  intro x hx
  have hP : |boxPInd volA A i Ψ x| ≤ C :=
    abs_boxPInd_le_nonneg hℓ hvol hA hvolA hAc i hC0 hC x hx
  have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hy : x i ∈ A
    · rw [Set.indicator_of_mem hy]; norm_num
    · rw [Set.indicator_of_notMem hy]; norm_num
  have hprod : |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x| ≤ C := by
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| ≤ 1 * C :=
          mul_le_mul hind (hC x hx) (abs_nonneg _) (by norm_num)
      _ = C := one_mul C
  have hQ : boxQInd volA A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x - boxPInd volA A i Ψ x := rfl
  rw [hQ]
  have htri : |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x - boxPInd volA A i Ψ x| ≤
      |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x| + |boxPInd volA A i Ψ x| := by
    simpa using abs_sub_le (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x) 0
      (boxPInd volA A i Ψ x)
  linarith

/-- `boxQInd` of a measurable state is measurable. -/
theorem measurable_boxQIndAux {N : ℕ} (volA : ℝ) (A : Set ℝ³) (hA : MeasurableSet A)
    (i : Fin N) {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (boxQInd volA A i Φ) := by
  show Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
    - boxPInd volA A i Φ x)
  exact (((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΦ).sub
    (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦ)

/-- **The integrability brick** (`a.e.`-bound form): a slot multiplier `S` which is a.e. strongly
measurable and a.e. bounded by `B` on the box, times the localised kernel
`wSmallPair M ℓ d u f`, is `IntegrableOn (abox N ℓ)`.  This is
`Work.BoseFixB1.integrableOn_slot_wSmallPair` verbatim. -/
private theorem segIntegrableAEB {N : ℕ} {ℓ d R : ℝ} {M : ℕ} {u : ℝ³} {i j : Fin N}
    {S : X N → ℝ} {B : ℝ} {f : ℝ³ → ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hM : 1 ≤ M)
    (hf : MeasureTheory.Integrable f)
    (hfsupp : ∀ z : ℝ³, R ≤ ‖z‖ → f z = 0)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hij : i ≠ j)
    (hSm : MeasureTheory.AEStronglyMeasurable S
      (MeasureTheory.volume.restrict (abox N ℓ)))
    (hB : 0 ≤ B)
    (hSb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)), |S x| ≤ B) :
    MeasureTheory.IntegrableOn (fun x : X N =>
      S x * Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j))
      (abox N ℓ) MeasureTheory.volume :=
  integrableOn_slot_wSmallPair hℓ hd hf hfsupp hM hR hRχ u hij hSm hB hSb

/-- The pointwise-bound version of `segIntegrableAEB`. -/
private theorem segIntegrableB {N : ℕ} {ℓ d R : ℝ} {M : ℕ} {u : ℝ³} {i j : Fin N}
    {S : X N → ℝ} {B : ℝ} {f : ℝ³ → ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hM : 1 ≤ M)
    (hf : MeasureTheory.Integrable f)
    (hfsupp : ∀ z : ℝ³, R ≤ ‖z‖ → f z = 0)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hij : i ≠ j)
    (hSm : MeasureTheory.AEStronglyMeasurable S
      (MeasureTheory.volume.restrict (abox N ℓ)))
    (hB : 0 ≤ B)
    (hSb : ∀ x ∈ abox N ℓ, |S x| ≤ B) :
    MeasureTheory.IntegrableOn (fun x : X N =>
      S x * Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j))
      (abox N ℓ) MeasureTheory.volume := by
  refine segIntegrableAEB hℓ hd hM hf hfsupp hR hRχ hij hSm hB ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  exact Filter.Eventually.of_forall (fun x hx => hSb x hx)

theorem boxFragmentsIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
                (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
            * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
                (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
            * (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)
                (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.1
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.2
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
            * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          (Work.BoseFixB1S.boxQ4B (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2
            * (Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairBlock (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) := by
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  set A : Set ℝ³ := Submission.BoseGases.dlBox ℓ d u with hAdef
  have hA : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : volA = (MeasureTheory.volume A).toReal := by
    rw [hvolAdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
      MeasureTheory.Measure.real_def]
  have hvol0 : 0 ≤ volA := by rw [hvolA]; exact ENNReal.toReal_nonneg
  -- `Φ` is bounded on the compact box
  obtain ⟨C, hCbd⟩ :=
    (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  have hCabs : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hCbd x hx
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (Φ 0))
    (hCabs 0 (Submission.BoseGases.zero_mem_abox (N := N) (ℓ := ℓ) hℓ.le))
  have h2C : (0 : ℝ) ≤ 2 * C := mul_nonneg (by norm_num) hC0
  have h4C : (0 : ℝ) ≤ 4 * C := mul_nonneg (by norm_num) hC0
  have hΦm : Measurable Φ := hΦc.measurable
  -- measurability of the box projections and their two-fold composites
  have hPm : ∀ k : Fin N, Measurable (boxPInd volA A k Φ) :=
    fun k => Work.BoseFixB1S.measurable_boxPInd volA A hA k hΦm
  have hQm : ∀ k : Fin N, Measurable (boxQInd volA A k Φ) :=
    fun k => measurable_boxQIndAux volA A hA k hΦm
  have hPPm : ∀ k l : Fin N,
      Measurable (fun x : X N => boxPInd volA A k (boxPInd volA A l Φ) x) :=
    fun k l => Work.BoseFixB1S.measurable_boxPInd volA A hA k (hPm l)
  have hPQm : ∀ k l : Fin N,
      Measurable (fun x : X N => boxPInd volA A k (boxQInd volA A l Φ) x) :=
    fun k l => Work.BoseFixB1S.measurable_boxPInd volA A hA k (hQm l)
  have hQPm : ∀ k l : Fin N,
      Measurable (fun x : X N => boxQInd volA A k (boxPInd volA A l Φ) x) :=
    fun k l => measurable_boxQIndAux volA A hA k (hPm l)
  have hQQm : ∀ k l : Fin N,
      Measurable (fun x : X N => boxQInd volA A k (boxQInd volA A l Φ) x) :=
    fun k l => measurable_boxQIndAux volA A hA k (hQm l)
  -- the `L∞` bounds of the two-slot readings of `Φ` on the box
  have hPΦ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |boxPInd volA A k Φ x| ≤ C :=
    fun k => abs_boxPInd_le_nonneg hℓ hvol0 hA hvolA hAc k hC0 hCabs
  have hQΦ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |boxQInd volA A k Φ x| ≤ 2 * C :=
    fun k => abs_boxQInd_le_nonneg hℓ hvol0 hA hvolA hAc k hC0 hCabs
  have hPa : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |boxPInd volA A k (boxPInd volA A l Φ) x| ≤ C :=
    fun k l => abs_boxPInd_le_nonneg hℓ hvol0 hA hvolA hAc k hC0 (hPΦ l)
  have hPb : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |boxPInd volA A k (boxQInd volA A l Φ) x| ≤ 2 * C :=
    fun k l => abs_boxPInd_le_nonneg (C := 2 * C) hℓ hvol0 hA hvolA hAc k h2C (hQΦ l)
  have hQa : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |boxQInd volA A k (boxPInd volA A l Φ) x| ≤ 2 * C :=
    fun k l => abs_boxQInd_le_nonneg hℓ hvol0 hA hvolA hAc k hC0 (hPΦ l)
  have hQb : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |boxQInd volA A k (boxQInd volA A l Φ) x| ≤ 4 * C := by
    intro k l x hx
    have hh := abs_boxQInd_le_nonneg (C := 2 * C) hℓ hvol0 hA hvolA hAc k h2C (hQΦ l) x hx
    linarith
  -- the three numerators (`v`, `g₂`, `g₀`), integrable with support in `ball 0 R0`
  have hvint : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hvsupp : ∀ z : ℝ³, R0 ≤ ‖z‖ → v z = 0 := fun z hz => vZeroB hv_supp hz
  have hg2int : MeasureTheory.Integrable (Submission.BoseGases.g2 v h) :=
    Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h
  have hg2supp : ∀ z : ℝ³, R0 ≤ ‖z‖ → Submission.BoseGases.g2 v h z = 0 :=
    fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0supp : ∀ z : ℝ³, R0 ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- fragment 1: `(P₁Q₂Φ)(P₁P₂Φ)·w₂`
    intro p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact segIntegrableB (N := N) (ℓ := ℓ) (d := d) (R := R0) (M := M) (u := u)
      (i := p.1) (j := p.2) (f := Submission.BoseGases.g2 v h)
      (S := fun x : X N =>
        boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
          * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x)
      (B := (2 * C) * C) hℓ hd hM hg2int hg2supp hR hRχ hij
      ((hPQm p.1 p.2).mul (hPPm p.1 p.2)).aestronglyMeasurable
      (mul_nonneg h2C hC0)
      (fun x hx => absMulBnd h2C (hPb p.1 p.2 x hx) (hPa p.1 p.2 x hx))
  · -- fragment 2: `(P₁Q₂Φ)(P₂Q₁Φ)·w₂`
    intro p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact segIntegrableB (N := N) (ℓ := ℓ) (d := d) (R := R0) (M := M) (u := u)
      (i := p.1) (j := p.2) (f := Submission.BoseGases.g2 v h)
      (S := fun x : X N =>
        boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
          * boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
      (B := (2 * C) * (2 * C)) hℓ hd hM hg2int hg2supp hR hRχ hij
      ((hPQm p.1 p.2).mul (hPQm p.2 p.1)).aestronglyMeasurable
      (mul_nonneg h2C h2C)
      (fun x hx => absMulBnd h2C (hPb p.1 p.2 x hx) (hPb p.2 p.1 x hx))
  · -- fragment 3: `(P₁Q₂Φ)(Q₂P₁Φ)·w₂`
    intro p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact segIntegrableB (N := N) (ℓ := ℓ) (d := d) (R := R0) (M := M) (u := u)
      (i := p.1) (j := p.2) (f := Submission.BoseGases.g2 v h)
      (S := fun x : X N =>
        boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
          * boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x)
      (B := (2 * C) * (2 * C)) hℓ hd hM hg2int hg2supp hR hRχ hij
      ((hPQm p.1 p.2).mul (hQPm p.2 p.1)).aestronglyMeasurable
      (mul_nonneg h2C h2C)
      (fun x hx => absMulBnd h2C (hPb p.1 p.2 x hx) (hQa p.2 p.1 x hx))
  · -- fragment 4: `(P₁Q₂Φ)(Q₂Q₁Φ)·w₁`
    intro p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have key := segIntegrableB (N := N) (ℓ := ℓ) (d := d) (R := R0) (M := M) (u := u)
      (i := p.1) (j := p.2) (f := Submission.BoseGases.g0 v h)
      (S := fun x : X N =>
        boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
          * boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x)
      (B := (2 * C) * (4 * C)) hℓ hd hM hg0int hg0supp hR hRχ hij
      ((hPQm p.1 p.2).mul (hQQm p.2 p.1)).aestronglyMeasurable
      (mul_nonneg h2C h4C)
      (fun x hx => absMulBnd h2C (hPb p.1 p.2 x hx) (hQb p.2 p.1 x hx))
    simpa only [Submission.BoseGases.wSmall1Pair] using key
  · -- fragment 5: `(Q₄B)²·w`
    intro p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hom := Submission.BoseGases.w0_abs_le_one_box_ae (N := N) (ℓ := ℓ) hℓ hR0 hv hvrad
      hv_supp h hij
    have hom' : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)),
        x ∈ Submission.BoseGases.abox N ℓ →
          |Classical.choose h (x p.1 - x p.2)| ≤ 1 :=
      (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mp hom
    have homT : MeasureTheory.AEStronglyMeasurable
        (fun x : X N => Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      have hd0 := Submission.BoseGases.w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij
        (w0 := Classical.choose h) (Classical.choose_spec h).2.lhs_integrable
      simpa only [Submission.BoseGases.omC] using hd0
    have hQ4Bm : MeasureTheory.AEStronglyMeasurable
        (fun x : X N => Work.BoseFixB1S.boxQ4B volA A
          (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      have heq : (fun x : X N => Work.BoseFixB1S.boxQ4B volA A
            (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
          = fun x : X N => boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
              + Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
                * (boxPInd volA A p.2 (boxPInd volA A p.1 Φ) x
                  + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x
                  + boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x) := rfl
      rw [heq]
      exact ((hQQm p.2 p.1).aestronglyMeasurable).add
        (homT.mul (((hPPm p.2 p.1).add (hPQm p.2 p.1)).add
          (hQPm p.2 p.1)).aestronglyMeasurable)
    have hS5m : MeasureTheory.AEStronglyMeasurable
        (fun x : X N => (Work.BoseFixB1S.boxQ4B volA A
          (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := hQ4Bm.pow 2
    have hS5b : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |(Work.BoseFixB1S.boxQ4B volA A
          (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2| ≤ (9 * C) ^ 2 := by
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      refine hom'.mono (fun x hx1 hxmem => ?_)
      have homx : |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)| ≤ 1 := by
        simpa only [Submission.BoseGases.omC] using hx1 hxmem
      have hq : |Work.BoseFixB1S.boxQ4B volA A
          (Submission.BoseGases.omC (Classical.choose h)) Φ p x| ≤ 9 * C := by
        rw [show Work.BoseFixB1S.boxQ4B volA A
              (Submission.BoseGases.omC (Classical.choose h)) Φ p x
            = boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
              + Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
                * (boxPInd volA A p.2 (boxPInd volA A p.1 Φ) x
                  + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x
                  + boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x) from rfl]
        have hQQ := hQb p.2 p.1 x hxmem
        have hPP := hPa p.2 p.1 x hxmem
        have hPQ := hPb p.2 p.1 x hxmem
        have hQP := hQa p.2 p.1 x hxmem
        have hsum : |boxPInd volA A p.2 (boxPInd volA A p.1 Φ) x
              + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x
              + boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x| ≤ 5 * C := by
          have h12 : |boxPInd volA A p.2 (boxPInd volA A p.1 Φ) x
              + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x| ≤ C + 2 * C :=
            le_trans (abs_add_le _ _) (add_le_add hPP hPQ)
          calc |boxPInd volA A p.2 (boxPInd volA A p.1 Φ) x
                + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x
                + boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x|
              ≤ |boxPInd volA A p.2 (boxPInd volA A p.1 Φ) x
                  + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x|
                + |boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x| := abs_add_le _ _
            _ ≤ (C + 2 * C) + 2 * C := add_le_add h12 hQP
            _ = 5 * C := by ring
        have hmul : |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
              * (boxPInd volA A p.2 (boxPInd volA A p.1 Φ) x
                + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x
                + boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x)| ≤ 1 * (5 * C) := by
          rw [abs_mul]
          exact mul_le_mul homx hsum (abs_nonneg _) (by norm_num)
        calc |boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
              + Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
                * (boxPInd volA A p.2 (boxPInd volA A p.1 Φ) x
                  + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x
                  + boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x)|
            ≤ |boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x|
              + |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
                * (boxPInd volA A p.2 (boxPInd volA A p.1 Φ) x
                  + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x
                  + boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x)| := abs_add_le _ _
          _ ≤ 4 * C + 1 * (5 * C) := add_le_add hQQ hmul
          _ = 9 * C := by ring
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hq 2
    exact segIntegrableAEB (N := N) (ℓ := ℓ) (d := d) (R := R0) (M := M) (u := u)
      (i := p.1) (j := p.2) (f := v)
      (S := fun x : X N => (Work.BoseFixB1S.boxQ4B volA A
        (Submission.BoseGases.omC (Classical.choose h)) Φ p x) ^ 2)
      (B := (9 * C) ^ 2) hℓ hd hM hvint hvsupp hR hRχ hij hS5m (by positivity) hS5b
  · -- fragment 6: `pairBlock`
    intro p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hom := Submission.BoseGases.w0_abs_le_one_box_ae (N := N) (ℓ := ℓ) hℓ hR0 hv hvrad
      hv_supp h hij
    have hom' : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)),
        x ∈ Submission.BoseGases.abox N ℓ →
          |Classical.choose h (x p.1 - x p.2)| ≤ 1 :=
      (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mp hom
    have homT : MeasureTheory.AEStronglyMeasurable
        (fun x : X N => Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      have hd0 := Submission.BoseGases.w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij
        (w0 := Classical.choose h) (Classical.choose_spec h).2.lhs_integrable
      simpa only [Submission.BoseGases.omC] using hd0
    -- the two summands of `pairBlock`
    have hS1m : MeasureTheory.AEStronglyMeasurable
        (fun x : X N =>
          (boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
            + (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
            + Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
              * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x) ^ 2)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (((hQQm p.2 p.1).aestronglyMeasurable.add
        ((hPQm p.1 p.2).add (hPQm p.2 p.1)).aestronglyMeasurable).add
          (homT.mul (hPPm p.1 p.2).aestronglyMeasurable)).pow 2
    have hS1b : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |(boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
            + (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
            + Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
              * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x) ^ 2| ≤ (9 * C) ^ 2 := by
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      refine hom'.mono (fun x hx1 hxmem => ?_)
      have homx : |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)| ≤ 1 := by
        simpa only [Submission.BoseGases.omC] using hx1 hxmem
      have hQQ := hQb p.2 p.1 x hxmem
      have hPQ := hPb p.1 p.2 x hxmem
      have hQP := hPb p.2 p.1 x hxmem
      have hPP := hPa p.1 p.2 x hxmem
      have hsum : |boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
            + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x| ≤ 2 * C + 2 * C :=
        le_trans (abs_add_le _ _) (add_le_add hPQ hQP)
      have h12 : |boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
            + (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)| ≤ 4 * C + (2 * C + 2 * C) :=
        le_trans (abs_add_le _ _) (add_le_add hQQ hsum)
      have hmul : |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
            * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x| ≤ 1 * C := by
        rw [abs_mul]
        exact mul_le_mul homx hPP (abs_nonneg _) (by norm_num)
      have hstep : |boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
            + (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
            + Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
              * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x| ≤ 9 * C := by
        calc |boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
              + (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                  + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
              + Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
                * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x|
            ≤ |boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
                + (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                    + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)|
              + |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
                * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x| := abs_add_le _ _
          _ ≤ (4 * C + (2 * C + 2 * C)) + 1 * C := add_le_add h12 hmul
          _ = 9 * C := by ring
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hstep 2
    have hS2m : MeasureTheory.AEStronglyMeasurable
        (fun x : X N =>
          2 * (1 - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2))
            * (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
            * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      ((((MeasureTheory.aestronglyMeasurable_const (b := (1 : ℝ))).sub homT).const_mul 2).mul
        ((hPQm p.1 p.2).add (hPQm p.2 p.1)).aestronglyMeasurable).mul
        (hPPm p.1 p.2).aestronglyMeasurable
    have hS2b : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |2 * (1 - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2))
            * (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
            * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x|
          ≤ 2 * 2 * (2 * C + 2 * C) * C := by
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      refine hom'.mono (fun x hx1 hxmem => ?_)
      have homx : |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)| ≤ 1 := by
        simpa only [Submission.BoseGases.omC] using hx1 hxmem
      have h1mom : |1 - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)| ≤ 2 := by
        calc |1 - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)|
            = |1 + (-(Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)))| := by
              rw [sub_eq_add_neg]
          _ ≤ |(1 : ℝ)| + |-(Submission.BoseGases.omC (Classical.choose h) (x p.1)
                (x p.2))| := abs_add_le _ _
          _ = 1 + |Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)| := by
              rw [abs_neg]; norm_num
          _ ≤ 2 := by linarith
      have hPQ := hPb p.1 p.2 x hxmem
      have hQP := hPb p.2 p.1 x hxmem
      have hPP := hPa p.1 p.2 x hxmem
      have hs : |boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
            + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x| ≤ 2 * C + 2 * C :=
        le_trans (abs_add_le _ _) (add_le_add hPQ hQP)
      have hs0 : (0 : ℝ) ≤ 2 * C + 2 * C :=
        add_nonneg (mul_nonneg (by norm_num) hC0) (mul_nonneg (by norm_num) hC0)
      have h1a : |2 * (1 - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2))|
          ≤ 2 * 2 :=
        absMulBnd (by norm_num) (by norm_num) h1mom
      have h2a : |2 * (1 - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2))
            * (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)|
          ≤ (2 * 2) * (2 * C + 2 * C) :=
        absMulBnd (mul_nonneg (by norm_num) (by norm_num)) h1a hs
      exact absMulBnd (mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) hs0) h2a hPP
    have h1 := segIntegrableAEB (N := N) (ℓ := ℓ) (d := d) (R := R0) (M := M) (u := u)
      (i := p.1) (j := p.2) (f := v)
      (S := fun x : X N =>
        (boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x
          + (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
              + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
          + Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
            * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x) ^ 2)
      (B := (9 * C) ^ 2) hℓ hd hM hvint hvsupp hR hRχ hij hS1m (by positivity) hS1b
    have h2 := segIntegrableAEB (N := N) (ℓ := ℓ) (d := d) (R := R0) (M := M) (u := u)
      (i := p.1) (j := p.2) (f := v)
      (S := fun x : X N =>
        2 * (1 - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2))
          * (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
              + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
          * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x)
      (B := 2 * 2 * (2 * C + 2 * C) * C) hℓ hd hM hvint hvsupp hR hRχ hij hS2m
      (by positivity) hS2b
    refine (h1.add h2).congr_fun ?_ (Submission.BoseGases.abox_measurable N ℓ)
    intro x hx
    simp only [Pi.add_apply, Work.BoseFixB1.pairBlock]

end Work.BoseFixB1.Clean
