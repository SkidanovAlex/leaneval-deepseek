import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.BoxPotDefs
import Submission.Work.BoseFixB1S.Clean.Fragments
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1.SectorPiece

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary helpers -/

/-- **The integrability brick**, a.e. form: an a.e. strongly measurable slot multiplier `S`,
a.e. bounded by `B ≥ 0` on the box, times the localised kernel `wSmallPair M ℓ d u f` is
`IntegrableOn (abox N ℓ)`, provided `f` is integrable with support in `ball 0 R` and
`R ≤ (ℓd)/16`.  This is `Work.BoseFixB1.integrableOn_slot_wSmallPair` verbatim. -/
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
private theorem abs_kMul_mul_le {k : ℝ} (hk : 0 ≤ k) {a b A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |k * a * b| ≤ k * A * B := by
  rw [abs_mul, abs_mul, abs_of_nonneg hk]
  have h1 : k * |a| ≤ k * A := mul_le_mul_of_nonneg_left ha hk
  calc k * |a| * |b| ≤ k * A * B :=
        mul_le_mul h1 hb (abs_nonneg b) (mul_nonneg hk hA)
    _ = k * A * B := by ring

/-- `|a·b| ≤ A·B` for `A, B ≥ 0` and `|a| ≤ A`, `|b| ≤ B`. -/
private theorem abs_pair_mul_le {a b A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

/-- `v` vanishes outside `ball 0 R` (from the support hypothesis on its closed support). -/
private theorem vZero {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) {z : ℝ³} (hz : R ≤ ‖z‖) : v z = 0 := by
  by_contra h
  have hmem : z ∈ tsupport v := subset_tsupport v (by simpa using h)
  have hball : z ∈ Metric.ball (0 : ℝ³) R := hv_supp hmem
  have hlt : ‖z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hball
  linarith

/-! ## The target -/

theorem fragsIntegrable_of_measurable_bound {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨm : Measurable Ψ) {C : ℝ} (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C)
    {i j : Fin N} (hij : i ≠ j) :
    (MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg0 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Ψ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg1 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Ψ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2a (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Ψ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2b (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Ψ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg2c (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Ψ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg3 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Ψ i j x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.fg4 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.omC (Classical.choose h)) Ψ i j x)
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
  -- the bound `C` is nonnegative, `abox N ℓ` being nonempty
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (Ψ 0))
    (hΨb 0 (Submission.BoseGases.zero_mem_abox (N := N) (ℓ := ℓ) hℓ.le))
  have h2C : (0 : ℝ) ≤ 2 * C := by linarith
  have h4C : (0 : ℝ) ≤ 4 * C := by linarith
  -- measurability of the box projections of `Ψ` and of their two-fold composites
  have hPm : ∀ k : Fin N, Measurable (Work.UBBInputs8.boxPInd volA A k Ψ) :=
    fun k => Work.BoseFixB1S.measurable_boxPInd volA A hA k hΨm
  have hQm : ∀ k : Fin N, Measurable (Work.UBBInputs8.boxQInd volA A k Ψ) :=
    fun k => Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hA k hΨm
  -- the `L∞` bounds of the one- and two-slot readings of `Ψ` on the box
  have hPΨ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A k Ψ x| ≤ C :=
    fun k => Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg hℓ hvol0 hA hvolA hAc k hC0 hΨb
  have hQΨ : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A k Ψ x| ≤ 2 * C :=
    fun k => Work.BoseFixB1.Clean.abs_boxQInd_le_nonneg hℓ hvol0 hA hvolA hAc k hC0 hΨb
  have hPa : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A k (Work.UBBInputs8.boxPInd volA A l Ψ) x| ≤ C :=
    fun k l => Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg hℓ hvol0 hA hvolA hAc k hC0 (hPΨ l)
  have hPb : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A k (Work.UBBInputs8.boxQInd volA A l Ψ) x| ≤ 2 * C :=
    fun k l => Work.BoseFixB1.Clean.abs_boxPInd_le_nonneg (C := 2 * C) hℓ hvol0 hA hvolA hAc k
      h2C (hQΨ l)
  have hQa : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A k (Work.UBBInputs8.boxPInd volA A l Ψ) x| ≤ 2 * C :=
    fun k l => Work.BoseFixB1.Clean.abs_boxQInd_le_nonneg hℓ hvol0 hA hvolA hAc k hC0 (hPΨ l)
  have hQb : ∀ k l : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A k (Work.UBBInputs8.boxQInd volA A l Ψ) x| ≤ 4 * C := by
    intro k l x hx
    have hh := Work.BoseFixB1.Clean.abs_boxQInd_le_nonneg (C := 2 * C) hℓ hvol0 hA hvolA hAc k
      h2C (hQΨ l) x hx
    linarith
  -- the three numerators: integrability and support
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
  -- the `ω`-factor: `|w₀(xᵢ − xⱼ)| ≤ 1` a.e. on the box, and its a.e. strong measurability
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
          (Submission.BoseGases.omC (Classical.choose h)) Ψ (i, j) x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
    have homT : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          Submission.BoseGases.omC (Classical.choose h) (x i) (x j))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      simpa only [Submission.BoseGases.omC] using homA
    have hTA : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x
          + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x
          + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x) :=
      ((Work.BoseFixB1S.measurable_boxPInd volA A hA j (hPm i)).add
        (Work.BoseFixB1S.measurable_boxPInd volA A hA j (hQm i))).add
        (Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hA j (hPm i))
    have hQ4 : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h))
            Ψ (i, j) x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hA j (hQm i)).aestronglyMeasurable.add
        (homT.mul hTA.aestronglyMeasurable)
    exact (hQ4.pow 2).const_mul (1 / 2)
  -- the `Q₄` multiplier: a.e. bound `|(1/2)(Q₄B)²| ≤ (1/2)(9C)²`
  have hb4 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      |(1 / 2) * (Work.BoseFixB1S.boxQ4B volA A
          (Submission.BoseGases.omC (Classical.choose h)) Ψ (i, j) x) ^ 2|
        ≤ (1 / 2) * (9 * C) ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    refine hom'.mono (fun x hx1 hxmem => ?_)
    have homx : |Submission.BoseGases.omC (Classical.choose h) (x i) (x j)| ≤ 1 := by
      simpa only [Submission.BoseGases.omC] using hx1 hxmem
    have hsum : |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x
        + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x
        + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x| ≤ 5 * C := by
      have h1 := hPa j i x hxmem
      have h2 := hPb j i x hxmem
      have h3 := hQa j i x hxmem
      calc |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x
            + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x
            + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x|
          ≤ |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x
              + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x|
            + |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x| :=
            abs_add_le _ _
        _ ≤ (|Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x|
              + |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x|)
            + |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x| :=
            add_le_add (abs_add_le _ _) le_rfl
        _ ≤ 5 * C := by linarith
    have hmul : |Submission.BoseGases.omC (Classical.choose h) (x i) (x j)
        * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x
          + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x
          + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x)|
        ≤ 1 * (5 * C) := by
      rw [abs_mul]
      exact mul_le_mul homx hsum (abs_nonneg _) (by norm_num)
    have hQ4b : |Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h))
        Ψ (i, j) x| ≤ 9 * C := by
      have hQQ := hQb j i x hxmem
      have hexp : Work.BoseFixB1S.boxQ4B volA A (Submission.BoseGases.omC (Classical.choose h))
          Ψ (i, j) x
          = Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x
            + Submission.BoseGases.omC (Classical.choose h) (x i) (x j)
              * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x
                + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x
                + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x) := rfl
      rw [hexp]
      have htri := abs_add_le
        (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x)
        (Submission.BoseGases.omC (Classical.choose h) (x i) (x j)
          * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x
            + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x
            + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x))
      linarith
    exact abs_half_sq_le (mul_nonneg (by norm_num) hC0) hQ4b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `fg0`: `(1/2)(PᵢPⱼΨ)² · w₂`
    exact segIntegrable (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N => (1 / 2) *
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x) ^ 2)
      (B := (1 / 2) * C ^ 2) hℓ hd hM hg2int hg2supp hR hRχ hij
      (Measurable.const_mul
        ((Work.BoseFixB1S.measurable_boxPInd volA A hA i (hPm j)).pow_const 2)
        (1 / 2)).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_half_sq_le hC0 (hPa i j x hx))
  · -- `fg1`: `2 (PᵢQⱼΨ)(PᵢPⱼΨ) · w₂`
    exact segIntegrable (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N => 2 *
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) *
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x))
      (B := 2 * (2 * C) * C) hℓ hd hM hg2int hg2supp hR hRχ hij
      (Measurable.const_mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQm j)) (2) |>.mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hA i (hPm j))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_kMul_mul_le (k := 2) (by norm_num) (mul_nonneg (by norm_num) hC0) hC0
        (hPb i j x hx) (hPa i j x hx))
  · -- `fg2a`: `(PᵢQⱼΨ)(PⱼQᵢΨ) · w₂`
    exact segIntegrable (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) *
        (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x))
      (B := (2 * C) * (2 * C)) hℓ hd hM hg2int hg2supp hR hRχ hij
      ((Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQm j)).mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hA j (hQm i))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_pair_mul_le (mul_nonneg (by norm_num) hC0) (mul_nonneg (by norm_num) hC0)
        (hPb i j x hx) (hPb j i x hx))
  · -- `fg2b`: `(PᵢQⱼΨ)(QⱼPᵢΨ) · w₂`
    exact segIntegrable (f := Submission.BoseGases.g2 v h)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) *
        (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x))
      (B := (2 * C) * (2 * C)) hℓ hd hM hg2int hg2supp hR hRχ hij
      ((Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQm j)).mul
        (Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hA j (hPm i))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_pair_mul_le (mul_nonneg (by norm_num) hC0) (mul_nonneg (by norm_num) hC0)
        (hPb i j x hx) (hQa j i x hx))
  · -- `fg2c`: `(PᵢPⱼΨ)(QⱼQᵢΨ) · w₁`
    exact segIntegrable (f := Submission.BoseGases.g0 v h)
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x) *
        (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x))
      (B := C * (4 * C)) hℓ hd hM hg0int hg0supp hR hRχ hij
      ((Work.BoseFixB1S.measurable_boxPInd volA A hA i (hPm j)).mul
        (Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hA j (hQm i))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_pair_mul_le hC0 (mul_nonneg (by norm_num) hC0)
        (hPa i j x hx) (hQb j i x hx))
  · -- `fg3`: `2 (PᵢQⱼΨ)(QⱼQᵢΨ) · w₁`
    exact segIntegrable (f := Submission.BoseGases.g0 v h)
      (S := fun x : Submission.BoseGases.X N => 2 *
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Ψ) x) *
        (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Ψ) x))
      (B := 2 * (2 * C) * (4 * C)) hℓ hd hM hg0int hg0supp hR hRχ hij
      (Measurable.const_mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQm j)) (2) |>.mul
        (Work.BoseFixB1.Clean.measurable_boxQIndAux volA A hA j (hQm i))).aestronglyMeasurable
      (by positivity)
      (fun x hx => abs_kMul_mul_le (k := 2) (by norm_num) (mul_nonneg (by norm_num) hC0)
        (mul_nonneg (by norm_num) hC0) (hPb i j x hx) (hQb j i x hx))
  · -- `fg4`: `(1/2)(Q₄B)² · w`, the `ω`-weighted square
    exact segIntegrableAE (f := v)
      (S := fun x : Submission.BoseGases.X N =>
        (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A
          (Submission.BoseGases.omC (Classical.choose h)) Ψ (i, j) x) ^ 2)
      (B := (1 / 2) * (9 * C) ^ 2) hℓ hd hM hvint hvsupp hR hRχ hij hS4m
      (by positivity) hb4

end Work.BoseFixB1.SectorPiece
