import ChallengeDeps
import Submission.Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre
import Submission.Work.BoseFixB1.integrableOn_slot_wSmallPair
import Submission.Work.BoseFixB1.regime_sideAt_ge
import Submission.Work.BoseFixB1.wSmall1Pair_fibre_abs_le
import Submission.Work.BoseFixB1S.PerBoxCrudeB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.SbPotHalvesB1Fix`

The split of the localised potential word `sbPot` (FS `eq:HBU` / `lem:LocPotential` at FS's
small-box parameters) into its **fibre-loss** and **pair** halves:

    sbPot h μ u Φ = −μ · fibLoss h μ u Φ + ½ · pairTermB μ u Φ .

`sbPot = qLHSwordB h M ℓ d μ u Φ` unfolds (definitionally) into the *single* box integral

    ∫_{abox n ℓ} Φ² · (−μ Σᵢ (∫_y w_{1,B(u)}(xᵢ,y)) + ½ Σ_{p ∈ pairSet n} w_{B(u)}(x_p)) ,

while `fibLoss`/`pairTermB` are the *same* expression with the box integral pushed inside the
finite sums over the slots `i : Fin n` and the pairs `p ∈ pairSet n`.  The passage between the two
is linearity of the Bochner integral (`integral_add`, `integral_finsetSum`, `integral_const_mul`),
which in Mathlib **requires the integrability of the individual summands** (there is no
unconditional linearity: a non-integrable integrand has integral `0`, so e.g. `∫(f+g) = ∫f + ∫g`
fails for `f = 1_{x>0}`, `g = 1_{[0,1]} − 1_{x>0}` on `ℝ`).

Those integrability facts are supplied here from the source hypotheses — `MemLp v 1`,
`IsRadial v`, `0 < R`, `tsupport v ⊆ ball 0 R`, `0 < a v` — together with the dilute regime
`R ≤ ℓd/16`, `R ≤ ℓ·chiR0` produced by the free threshold `ε₀` (`regime_sideAt_ge`):

* the **pair** summands `Φ²·w_{B(u)}(x_p)` are `IntegrableOn (abox n ℓ)` by
  `wSmallPair_pair_integrableOn` below (the corpus slot lemma
  `Work.BoseFixB1.integrableOn_slot_wSmallPair` with the bounded factor `Φ²`);
* the **fibre** summands `Φ²·(∫_y w_{1,B(u)}(xᵢ,y))` are `IntegrableOn (abox n ℓ)` by
  `wSmall1Pair_slot_integrableOn` below: the fibre is uniformly bounded by the closed constant of
  `Work.BoseFixB1.wSmall1Pair_fibre_abs_le` and is a.e. strongly measurable by
  `Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre`, so
  `Submission.BoseGases.integrableOn_slot_fibre` applies to the continuous bounded factor `Φ²`.

The split identity itself is `sbPotSplit_of_integrable`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

set_option maxHeartbeats 1000000

/-! ## 1. Integrability of the pair summands -/

/-- **Integrability of the localised pair summands over the box.**

For continuous `Φ` and the dilute small-box regime `R0 ≤ ℓd/16`, `R0 ≤ ℓ·chiR0`, every pair
summand `x ↦ Φ(x)² · wSmallPair M ℓ d u v (x p.1) (x p.2)` (`p ∈ pairSet N`) is integrable over
`abox N ℓ`.  This is the corpus lemma `Work.BoseFixB1.integrableOn_slot_wSmallPair` with the
bounded factor `S = Φ²` (a continuous function on the compact box `abox N ℓ` is bounded). -/
theorem wSmallPair_pair_integrableOn {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv1 : MeasureTheory.MemLp v 1) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : ℝ³) {N : ℕ} (Φ : Submission.BoseGases.X N → ℝ) (hΦ : Continuous Φ) :
    ∀ p ∈ Submission.BoseGases.pairSet N,
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
        (Submission.BoseGases.abox N ℓ) := by
  intro p hp
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  have hvint : Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hvsupp : ∀ z : ℝ³, R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
  obtain ⟨B, hB⟩ :=
    (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox N ℓ)
      (f := fun x : Submission.BoseGases.X N => (Φ x) ^ 2) ((hΦ.pow 2).continuousOn)
  have hB0 : 0 ≤ B := by
    have hb0 := hB 0 (Submission.BoseGases.zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg _) hb0
  have hSb : ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ), |(Φ x) ^ 2| ≤ B := by
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact ae_of_all _ (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx)
  have hint := Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
    hℓ hd hvint hvsupp hM hR hRχ u hne
    (S := fun x : Submission.BoseGases.X N => (Φ x) ^ 2)
    ((hΦ.pow 2).aestronglyMeasurable) hB0 hSb
  simpa using hint

/-! ## 2. Integrability of the fibre summands -/

/-- **Integrability of the localised fibre summands over the box.**

For continuous `Φ` and the dilute small-box regime, every one-body summand
`x ↦ Φ(x)² · (∫_{acube ℓ} wSmall1Pair h M ℓ d u (x i) y)` is integrable over `abox N ℓ`.

The fibre `z ↦ ∫_y w_{1,B(u)}(z,y)` is *uniformly* bounded by the closed-form constant of
`Work.BoseFixB1.wSmall1Pair_fibre_abs_le` and is a.e. strongly measurable by
`Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre`; with the continuous bounded factor `Φ²`,
`Submission.BoseGases.integrableOn_slot_fibre` gives the claim. -/
theorem wSmall1Pair_slot_integrableOn {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : ℝ³) {N : ℕ} (Φ : Submission.BoseGases.X N → ℝ) (hΦ : Continuous Φ) :
    ∀ i : Fin N, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y))
      (Submission.BoseGases.abox N ℓ) := by
  intro i
  have hg0 : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hFm : AEStronglyMeasurable
      (fun z : ℝ³ => ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y)
      ((volume : Measure (ℝ³)).restrict (Submission.BoseGases.acube ℓ)) :=
    Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre M u hg0.aestronglyMeasurable.aemeasurable
  have hbnd := Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u
  have hC : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y|
        ≤ max 0 (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
            * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                / Work.SmallBoxSliding.smallConvLower M
                * (8 * Real.pi * _root_.BoseGases.a v))) :=
    fun z _ => le_trans (hbnd z) (le_max_right _ _)
  have hint := Submission.BoseGases.integrableOn_slot_fibre hℓ i hFm hC
    (S := fun x : Submission.BoseGases.X N => (Φ x) ^ 2) (hΦ.pow 2)
  simpa only [Submission.BoseGases.wSmall1Pair] using hint

/-! ## 3. The split identity, given the integrability of the two halves -/

/-- **The split of `sbPot` into its fibre-loss and pair halves**, with the integrability of the two
halves assumed: `h1` is the integrability of the per-slot loop integrands
`Φ²·∫_y w_{1,B(u)}(xᵢ,·)` over the box, `h2` that of the per-pair integrands
`Φ²·w_{B(u)}(x_p)`.  The proof is the unfolding of `sbPot`, `qLHSword`/`qLHSwordB`, `fibLoss`,
`pairTermB` followed by `integral_congr_ae`, `integral_add`, `integral_finsetSum` and
`integral_const_mul`. -/
theorem sbPotSplit_of_integrable {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (u : ℝ³)
    (h1 : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i) y))
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    (h2 : ∀ p ∈ Submission.BoseGases.pairSet n, IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * Submission.BoseGases.wSmallPair
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v (x p.1) (x p.2))
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :
    Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = -(μ * Work.BoseFixB1S.fibLoss h μ u (Φ : Submission.BoseGases.X n → ℝ))
        + (1 / 2) * Work.BoseFixB1S.pairTermB (v := v) μ u
            (Φ : Submission.BoseGases.X n → ℝ) := by
  simp only [Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword,
    Work.BoseFixB1S.fibLoss, Work.BoseFixB1S.pairTermB, Submission.BoseGases.w1Fibre]
  -- the two halves, as functions of the configuration
  set F : Fin n → Submission.BoseGases.X n → ℝ := fun i x =>
    ∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i) y with hF
  set G : Fin n × Fin n → Submission.BoseGases.X n → ℝ := fun p x =>
    Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v (x p.1) (x p.2) with hG
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * (-μ * (∑ i, F i x) + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n, G p x))
        = (∑ i, (Φ x) ^ 2 * (-μ * F i x))
          + (∑ p ∈ Submission.BoseGases.pairSet n, (Φ x) ^ 2 * ((1 / 2) * G p x)) := by
    intro x
    have hA : (Φ x) ^ 2 * (-μ * (∑ i, F i x)) = ∑ i, (Φ x) ^ 2 * (-μ * F i x) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    have hB : (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n, G p x))
        = ∑ p ∈ Submission.BoseGases.pairSet n, (Φ x) ^ 2 * ((1 / 2) * G p x) := by
      simp only [Finset.mul_sum]
    rw [mul_add, hA, hB]
  -- integrability of the two split halves
  have hint1 : IntegrableOn (fun x : Submission.BoseGases.X n => ∑ i, (Φ x) ^ 2 * (-μ * F i x))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
    refine MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ => ?_)
    refine ((h1 i).const_mul (-μ)).congr (Filter.Eventually.of_forall (fun x => ?_))
    ring
  have hint2 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      ∑ p ∈ Submission.BoseGases.pairSet n, (Φ x) ^ 2 * ((1 / 2) * G p x))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
    refine MeasureTheory.integrable_finsetSum (Submission.BoseGases.pairSet n) (fun p hp => ?_)
    refine ((h2 p hp).const_mul (1 / 2)).congr (Filter.Eventually.of_forall (fun x => ?_))
    ring
  -- per-slot, per-pair rewriting of the constants
  have hc1 : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * (-μ * F i x))
      = -μ * ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * F i x := by
    intro i
    rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (-μ * F i x))
        = fun x => (-μ) * ((Φ x) ^ 2 * F i x) from by funext x; ring,
      MeasureTheory.integral_const_mul]
  have hc2 : ∀ p ∈ Submission.BoseGases.pairSet n,
      (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * ((1 / 2) * G p x))
      = (1 / 2) * ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * G p x := by
    intro p hp
    rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ((1 / 2) * G p x))
        = fun x => (1 / 2) * ((Φ x) ^ 2 * G p x) from by funext x; ring,
      MeasureTheory.integral_const_mul]
  calc (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * (-μ * (∑ i, F i x)
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n, G p x)))
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((∑ i, (Φ x) ^ 2 * (-μ * F i x))
          + (∑ p ∈ Submission.BoseGases.pairSet n, (Φ x) ^ 2 * ((1 / 2) * G p x))) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ∑ i, (Φ x) ^ 2 * (-μ * F i x))
        + (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ∑ p ∈ Submission.BoseGases.pairSet n, (Φ x) ^ 2 * ((1 / 2) * G p x)) :=
        MeasureTheory.integral_add hint1 hint2
    _ = (∑ i, ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Φ x) ^ 2 * (-μ * F i x))
        + (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Φ x) ^ 2 * ((1 / 2) * G p x)) := by
        rw [MeasureTheory.integral_finsetSum _ (fun i _ => ((h1 i).const_mul (-μ)).congr
              (Filter.Eventually.of_forall (fun x => by ring))),
          MeasureTheory.integral_finsetSum _ (fun p hp => ((h2 p hp).const_mul (1 / 2)).congr
              (Filter.Eventually.of_forall (fun x => by ring)))]
    _ = -μ * (∑ i, ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Φ x) ^ 2 * F i x)
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Φ x) ^ 2 * G p x) := by
        rw [Finset.sum_congr rfl (fun i _ => hc1 i),
          Finset.sum_congr rfl (fun p hp => hc2 p hp), Finset.mul_sum, Finset.mul_sum]
  simp only [hF, hG, neg_mul]

/-! ## 4. The target -/

theorem SbPotHalvesB1Fix {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {n : ℕ}
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      (u : EuclideanSpace ℝ (Fin 3)),
      Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)
        = -(μ * Work.BoseFixB1S.fibLoss h μ u (Φ : Submission.BoseGases.X n → ℝ))
          + (1 / 2) * Work.BoseFixB1S.pairTermB (v := v) μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  -- the diluteness threshold at which the box side dominates the support radius
  obtain ⟨ε₀r, hε₀r, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min 1 ε₀r, lt_min one_pos hε₀r, ?_⟩
  intro μ hAdm n Φ u
  have hμ : 0 < μ := hAdm.1
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀r := le_trans hAdm.2.1 (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ hdil
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    norm_num [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  exact sbPotSplit_of_integrable h Φ u
    (wSmall1Pair_slot_integrableOn hv_supp hR hv hvrad h hM1 hℓ hd hR16 hRχ u
      (Φ : Submission.BoseGases.X n → ℝ) hΦc)
    (wSmallPair_pair_integrableOn hv_supp hR hv1 hM1 hℓ hd hR16 hRχ u
      (Φ : Submission.BoseGases.X n → ℝ) hΦc)

end Work.BoseFixB1S
