import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.aesm_wSmallPair_pair
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
import Submission.Work.BoseFixB1.wSmall1Pair_fibre_abs_le
import Submission.Work.BoseFixB1S.BoxPotFrag
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1N

open MeasureTheory
open scoped Real Topology

set_option linter.unusedVariables false

/-- `v` vanishes outside `ball 0 R` (from the support hypothesis on its closed support). -/
private theorem vZero {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) {z : ℝ³} (hz : R ≤ ‖z‖) : v z = 0 := by
  by_contra h
  have hmem : z ∈ tsupport v := subset_tsupport v (by simpa using h)
  have hball : z ∈ Metric.ball (0 : ℝ³) R := hv_supp hmem
  have hlt : ‖z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hball
  linarith

/-- **`Q`-reading bound**: if `|Ψ| ≤ C` on the box then also `|Q_iΨ| ≤ 2C`, because
`Q_iΨ = 1_A(x_i)Ψ − P_iΨ` and both summands are bounded by `C`. -/
theorem abs_boxQInd_le {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ} {C : ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * C := by
  intro x hx
  have hP := Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hC x hx
  have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hy : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  have hprod : |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x| ≤ C := by
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| ≤ 1 * C :=
          mul_le_mul hind (hC x hx) (abs_nonneg _) (by norm_num)
      _ = C := one_mul C
  have hsub : |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
      - Work.UBBInputs8.boxPInd volA A i Ψ x|
      ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x|
        + |Work.UBBInputs8.boxPInd volA A i Ψ x| := by
    simpa using abs_sub_le (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x) 0
      (Work.UBBInputs8.boxPInd volA A i Ψ x)
  have hQ : Work.UBBInputs8.boxQInd volA A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
        - Work.UBBInputs8.boxPInd volA A i Ψ x := rfl
  rw [hQ]
  linarith

/-- `Q_iΨ` is globally measurable for measurable `Ψ`. -/
theorem measurable_boxQInd {N : ℕ} (volA : ℝ) (A : Set ℝ³) (hA : MeasurableSet A)
    (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Measurable Ψ) :
    Measurable (Work.UBBInputs8.boxQInd volA A i Ψ) := by
  have h1 : Measurable (fun x : Submission.BoseGases.X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i)) :=
    (measurable_const.indicator hA).comp (measurable_pi_apply i)
  have h2 : Measurable (fun x : Submission.BoseGases.X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
        - Work.UBBInputs8.boxPInd volA A i Ψ x) :=
    (h1.mul hΨ).sub (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΨ)
  exact h2

/-- `|(1/2)a²| ≤ (1/2)A²` for `|a| ≤ A`, `0 ≤ A`. -/
private theorem abs_half_sq_le {a A : ℝ} (hA : 0 ≤ A) (ha : |a| ≤ A) :
    |(1 / 2) * a ^ 2| ≤ (1 / 2) * A ^ 2 := by
  have hsq : a ^ 2 ≤ A ^ 2 := by
    have h1 : |a| ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg a) ha 2
    rwa [sq_abs] at h1
  have h2 : |(1 / 2) * a ^ 2| = (1 / 2) * a ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg (sq_nonneg a)]
  rw [h2]
  exact mul_le_mul_of_nonneg_left hsq (by norm_num)

/-- `|k·a·b| ≤ k·A·B` for `k, A, B ≥ 0` and `|a| ≤ A`, `|b| ≤ B`. -/
private theorem abs_mul_mul_le {k : ℝ} (hk : 0 ≤ k) {a b A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |k * a * b| ≤ k * A * B := by
  rw [abs_mul, abs_mul, abs_of_nonneg hk]
  have h1 : k * |a| ≤ k * A := mul_le_mul_of_nonneg_left ha hk
  calc k * |a| * |b| ≤ k * A * B :=
        mul_le_mul h1 hb (abs_nonneg b) (mul_nonneg hk hA)
    _ = k * A * B := by ring

/-- `|a·b| ≤ A·B` for `A, B ≥ 0` and `|a| ≤ A`, `|b| ≤ B`. -/
private theorem abs_mul_le' {a b A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

/-- **The integrability brick**: a slot multiplier `S` that is a.e. strongly measurable and
a.e. bounded by `B` on the box, times the localised kernel `wSmallPair M ℓ d u f`, is
`IntegrableOn (abox N ℓ)`.  This is `integrableOn_slot_wSmallPair` verbatim; it is recorded
here only because the two boundary shapes (pointwise and a.e. bounds on the multiplier) are
used repeatedly below. -/
private theorem segIntegrableAE {N : ℕ} {ℓ d R : ℝ} {M : ℕ} {u : ℝ³} {i j : Fin N}
    {S : Submission.BoseGases.X N → ℝ} {B : ℝ} {f : ℝ³ → ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hM : 1 ≤ M)
    (hf : MeasureTheory.Integrable f)
    (hfsupp : ∀ z : ℝ³, R ≤ ‖z‖ → f z = 0)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hij : i ≠ j)
    (hSm : MeasureTheory.AEStronglyMeasurable S
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    (hB : 0 ≤ B)
    (hSb : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)), |S x| ≤ B) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      S x * Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
  Work.BoseFixB1.integrableOn_slot_wSmallPair hℓ hd hf hfsupp hM hR hRχ u hij hSm hB hSb

/-- The pointwise-bound version of `segIntegrableAE`. -/
private theorem segIntegrable {N : ℕ} {ℓ d R : ℝ} {M : ℕ} {u : ℝ³} {i j : Fin N}
    {S : Submission.BoseGases.X N → ℝ} {B : ℝ} {f : ℝ³ → ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hM : 1 ≤ M)
    (hf : MeasureTheory.Integrable f)
    (hfsupp : ∀ z : ℝ³, R ≤ ‖z‖ → f z = 0)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hij : i ≠ j)
    (hSm : MeasureTheory.AEStronglyMeasurable S
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    (hB : 0 ≤ B)
    (hSb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |S x| ≤ B) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      S x * Submission.BoseGases.wSmallPair M ℓ d u f (x i) (x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  refine segIntegrableAE hℓ hd hM hf hfsupp hR hRχ hij hSm hB ?_
  rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  exact Filter.Eventually.of_forall (fun x hx => hSb x hx)

theorem boxFragsIntegrable_dlBox {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg0 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg1 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2a (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2b (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2c (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Φ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg3 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Φ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg4 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.omC (Classical.choose h)) Φ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  set A : Set ℝ³ := Submission.BoseGases.dlBox ℓ d u with hAdef
  have hA : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : volA = (MeasureTheory.volume A).toReal := by
    rw [hvolAdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
      MeasureTheory.Measure.real_def]
  -- `Φ` is bounded on the compact box
  obtain ⟨C, hCbd⟩ :=
    (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  have hCabs : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hCbd x hx
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (Φ 0))
    (hCabs 0 (Submission.BoseGases.zero_mem_abox (N := N) (ℓ := ℓ) hℓ.le))
  have hΦm : Measurable Φ := hΦc.measurable
  have hPm : ∀ k : Fin N, Measurable (Work.UBBInputs8.boxPInd volA A k Φ) :=
    fun k => Work.BoseFixB1S.measurable_boxPInd volA A hA k hΦm
  have hQm : ∀ k : Fin N, Measurable (Work.UBBInputs8.boxQInd volA A k Φ) :=
    fun k => measurable_boxQInd volA A hA k hΦm
  -- the `L∞` bounds of the two-slot readings of `Φ` on the box
  have hPΦ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A k Φ x| ≤ C :=
    fun k => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc k hCabs
  have hQΦ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A k Φ x| ≤ 2 * C :=
    fun k => abs_boxQInd_le hℓ hvol hA hvolA hAc k hCabs
  have hPa : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A k (Work.UBBInputs8.boxPInd volA A l Φ) x| ≤ C :=
    fun k l => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc k (hPΦ l)
  have hPb : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A k (Work.UBBInputs8.boxQInd volA A l Φ) x| ≤ 2 * C :=
    fun k l => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc k (hQΦ l)
  have hQa : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A k (Work.UBBInputs8.boxPInd volA A l Φ) x| ≤ 2 * C :=
    fun k l => abs_boxQInd_le hℓ hvol hA hvolA hAc k (hPΦ l)
  have hQb : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A k (Work.UBBInputs8.boxQInd volA A l Φ) x| ≤ 4 * C := by
    intro k l x hx
    have hh := abs_boxQInd_le hℓ hvol hA hvolA hAc k (hQΦ l) x hx
    linarith
  -- the three numerators
  have hg2int : MeasureTheory.Integrable (Submission.BoseGases.g2 v h) :=
    Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h
  have hg2supp : ∀ z : ℝ³, R0 ≤ ‖z‖ → Submission.BoseGases.g2 v h z = 0 :=
    fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0supp : ∀ z : ℝ³, R0 ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hvint : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hvsupp : ∀ z : ℝ³, R0 ≤ ‖z‖ → v z = 0 := fun z hz => vZero hv_supp hz
  -- the `ω`-factor: `|w₀(xᵢ − xⱼ)| ≤ 1` a.e. on the box
  have hom := Submission.BoseGases.w0_abs_le_one_box_ae (N := N) (ℓ := ℓ) hℓ hR0 hv hvrad
    hv_supp h hij
  have hom' : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)),
      x ∈ Submission.BoseGases.abox N ℓ → |Classical.choose h (x i - x j)| ≤ 1 :=
    (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mp hom
  have homA : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => Classical.choose h (x i - x j))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij
      (w0 := Classical.choose h) (Classical.choose_spec h).2.lhs_integrable
  -- the `Q₄` multiplier: a.e. strong measurability
  have hS4m : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N =>
        (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A
          (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
    have homT : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          Submission.BoseGases.omC (Classical.choose h) (x i) (x j))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      simpa only [Submission.BoseGases.omC] using homA
    have hTA : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
          + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) :=
      ((Work.BoseFixB1S.measurable_boxPInd volA A hA j (hPm i)).add
        (Work.BoseFixB1S.measurable_boxPInd volA A hA j (hQm i))).add
        (measurable_boxQInd volA A hA j (hPm i))
    have hQ4 : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h))
            Φ (i, j) x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (measurable_boxQInd volA A hA j (hQm i)).aestronglyMeasurable.add
        (homT.mul hTA.aestronglyMeasurable)
    exact (hQ4.pow 2).const_mul (1 / 2)
  -- the `Q₄` multiplier: a.e. bound `|Q₄B| ≤ 9C`
  have hb4 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      |(1 / 2) * (Work.BoseFixB1S.boxQ4B volA A
          (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2|
        ≤ (1 / 2) * (9 * C) ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    refine hom'.mono (fun x hx1 hxmem => ?_)
    have homx : |Submission.BoseGases.omC (Classical.choose h) (x i) (x j)| ≤ 1 := by
      simpa only [Submission.BoseGases.omC] using hx1 hxmem
    have hsum : |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
        + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
        + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x| ≤ 5 * C := by
      have h1 := hPa j i x hxmem
      have h2 := hPb j i x hxmem
      have h3 := hQa j i x hxmem
      calc |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
            + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
            + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x|
          ≤ |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
              + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x|
            + |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x| :=
            abs_add_le _ _
        _ ≤ (|Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x|
              + |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x|)
            + |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x| :=
            add_le_add (abs_add_le _ _) le_rfl
        _ ≤ 5 * C := by linarith
    have hmul : |Submission.BoseGases.omC (Classical.choose h) (x i) (x j)
        * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
          + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)|
        ≤ 1 * (5 * C) := by
      rw [abs_mul]
      exact mul_le_mul homx hsum (abs_nonneg _) (by norm_num)
    have hQ4b : |Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h))
        Φ (i, j) x| ≤ 9 * C := by
      have hQQ := hQb j i x hxmem
      have hexp : Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h))
          Φ (i, j) x
          = Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
            + Submission.BoseGases.omC (Classical.choose h) (x i) (x j)
              * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
                + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) := rfl
      rw [hexp]
      have htri := abs_add_le
        (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        (Submission.BoseGases.omC (Classical.choose h) (x i) (x j)
          * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
            + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
            + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x))
      linarith
    exact abs_half_sq_le (mul_nonneg (by norm_num) hC0) hQ4b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `fg0`: `(1/2)(P_iP_jΦ)² · w₂`
    exact segIntegrable (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N => (1 / 2) *
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      (B := (1 / 2) * C ^ 2) hℓ hd hM hg2int hg2supp hR hRχ hij
      (Measurable.const_mul
        ((Work.BoseFixB1S.measurable_boxPInd volA A hA i (hPm j)).pow_const 2)
        (1 / 2)).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_half_sq_le hC0 (hPa i j x hx))
  · -- `fg1`: `2 (P_iQ_jΦ)(P_iP_jΦ) · w₂`
    exact segIntegrable (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N => 2 *
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) *
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x))
      (B := 2 * (2 * C) * C) hℓ hd hM hg2int hg2supp hR hRχ hij
      (Measurable.const_mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQm j)) (2) |>.mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hA i (hPm j))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_mul_mul_le (k := 2) (by norm_num) (mul_nonneg (by norm_num) hC0) hC0
        (hPb i j x hx) (hPa i j x hx))
  · -- `fg2a`: `(P_iQ_jΦ)(P_jQ_iΦ) · w₂`
    exact segIntegrable (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) *
        (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
      (B := (2 * C) * (2 * C)) hℓ hd hM hg2int hg2supp hR hRχ hij
      ((Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQm j)).mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hA j (hQm i))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_mul_le' (mul_nonneg (by norm_num) hC0) (mul_nonneg (by norm_num) hC0)
        (hPb i j x hx) (hPb j i x hx))
  · -- `fg2b`: `(P_iQ_jΦ)(Q_jP_iΦ) · w₂`
    exact segIntegrable (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) *
        (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x))
      (B := (2 * C) * (2 * C)) hℓ hd hM hg2int hg2supp hR hRχ hij
      ((Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQm j)).mul
        (measurable_boxQInd volA A hA j (hPm i))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_mul_le' (mul_nonneg (by norm_num) hC0) (mul_nonneg (by norm_num) hC0)
        (hPb i j x hx) (hQa j i x hx))
  · -- `fg2c`: `(P_iP_jΦ)(Q_jQ_iΦ) · w₁`
    exact segIntegrable (f := Submission.BoseGases.g0 v h)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) *
        (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
      (B := C * (4 * C)) hℓ hd hM hg0int hg0supp hR hRχ hij
      ((Work.BoseFixB1S.measurable_boxPInd volA A hA i (hPm j)).mul
        (measurable_boxQInd volA A hA j (hQm i))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_mul_le' hC0 (mul_nonneg (by norm_num) hC0)
        (hPa i j x hx) (hQb j i x hx))
  · -- `fg3`: `2 (P_iQ_jΦ)(Q_jQ_iΦ) · w₁`
    exact segIntegrable (f := Submission.BoseGases.g0 v h)
      (S := fun x : Submission.BoseGases.X N => 2 *
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) *
        (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
      (B := 2 * (2 * C) * (4 * C)) hℓ hd hM hg0int hg0supp hR hRχ hij
      (Measurable.const_mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQm j)) (2) |>.mul
        (measurable_boxQInd volA A hA j (hQm i))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_mul_mul_le (k := 2) (by norm_num) (mul_nonneg (by norm_num) hC0)
        (mul_nonneg (by norm_num) hC0) (hPb i j x hx) (hQb j i x hx))
  · -- `fg4`: `(1/2)(Q₄B)² · w`, the `ω`-weighted square
    exact segIntegrableAE (f := v)
      (S := fun x : Submission.BoseGases.X N =>
        (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A
          (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2)
      (B := (1 / 2) * (9 * C) ^ 2) hℓ hd hM hvint hvsupp hR hRχ hij hS4m
      (by positivity) hb4

end Work.BoseFixB1N
