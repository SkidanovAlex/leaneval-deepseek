import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.perBoxF_localised
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The `F`-weight integral bound -/

/-- **The `F`-weight is dominated by the smooth count plus the state mass**:
`∫Φ²F(nCountB/χ) ≤ μ(χ⁻¹·scountB + μ‖Φ‖²)`, the integral of the pointwise bound
`F(t) ≤ μ(t+μ)` (`perBoxF_pieces.psiWeight_le_mu_mul_add`). -/
theorem psiWeight_integral_le_thick {μ : ℝ} (hμ : 0 < μ) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u))
      ≤ μ * ((chiMass M ℓ d u)⁻¹ * scountB M ℓ d u Φ
          + μ * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  have hchi0 : 0 ≤ chiMass M ℓ d u := chiMass_nonneg M ℓ d u
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((chiSmall_continuous hM).comp (by fun_prop))
  have hcont_num : Continuous (fun x : Submission.BoseGases.X n => nCountB M ℓ d u x) := by
    simp only [nCountB]
    exact continuous_finsetSum _ fun i _ => (hcB.comp (continuous_apply i)).pow 2
  have hInt1 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      μ * ((Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u)))
      (Submission.BoseGases.abox n ℓ) :=
    ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
      ((continuous_const.mul ((hΦc.pow 2).mul (hcont_num.div_const _))).continuousOn)
  have hInt2 : IntegrableOn (fun x : Submission.BoseGases.X n => μ ^ 2 * (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) :=
    ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
      ((continuous_const.mul (hΦc.pow 2)).continuousOn)
  have hmono : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          (μ * ((Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u)) + μ ^ 2 * (Φ x) ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) (hInt1.add hInt2)
      (Filter.Eventually.of_forall fun x => ?_)
    · exact mul_nonneg (sq_nonneg _)
        (perBoxFCase_psiWeight_nonneg (by norm_num) hμ
          (div_nonneg (nCountB_nonneg _ _ _ _ x) hchi0))
    · have ht : 0 ≤ nCountB M ℓ d u x / chiMass M ℓ d u :=
        div_nonneg (nCountB_nonneg _ _ _ _ x) hchi0
      have hb := psiWeight_le_mu_mul_add (μ := μ) hμ ht
      have h2 : 0 ≤ (Φ x) ^ 2 := sq_nonneg _
      calc (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u)
          ≤ (Φ x) ^ 2 * (μ * (nCountB M ℓ d u x / chiMass M ℓ d u + μ)) :=
            mul_le_mul_of_nonneg_left hb h2
        _ = μ * ((Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u)) + μ ^ 2 * (Φ x) ^ 2 := by
            ring
  calc (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          (μ * ((Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u)) + μ ^ 2 * (Φ x) ^ 2) := hmono
    _ = μ * (∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u))
          + μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
          rw [integral_add hInt1 hInt2, integral_const_mul, integral_const_mul]
    _ = μ * ((chiMass M ℓ d u)⁻¹ * scountB M ℓ d u Φ
          + μ * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
          rw [scountB]
          have : (∫ x in Submission.BoseGases.abox n ℓ,
              (Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u))
              = (chiMass M ℓ d u)⁻¹ * (∫ x in Submission.BoseGases.abox n ℓ,
                  (Φ x) ^ 2 * nCountB M ℓ d u x) := by
            rw [← integral_const_mul]
            exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
          rw [this]; ring

/-- **The `F`-weight is superlinear below `μ`**: for `μ/3 ≤ t` one has `F(t) ≤ μ t`
(the *linear* regime `t ≳ μ` of FS's weight, the regime in which the pair term pays). -/
theorem psiWeight_le_mu_mul {μ t : ℝ} (hμ : 0 < μ) (ht : μ / 3 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * t := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg (le_trans (div_nonneg hμ.le (by norm_num)) ht)
      (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have h1 : 1 + t * μ⁻¹ = (t + μ) / μ := by field_simp; ring
  rw [h1]
  have h2 : μ * t * ((t + μ) / μ) = t * (t + μ) := by field_simp
  rw [h2]
  nlinarith [ht, hμ, sq_nonneg (t - μ)]

/-- **The `F`-weight is bounded by `μ²` below `3μ`**: for `t ≤ 3μ` one has `F(t) ≤ μ²`
(the *quadratic* regime `t ≲ μ` of FS's weight, where the `½μ²W` background pays). -/
theorem psiWeight_le_mu_sq {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (ht3 : t ≤ 3 * μ) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ ^ 2 := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have h1 : 1 + t * μ⁻¹ = (t + μ) / μ := by field_simp; ring
  rw [h1]
  have h2 : μ ^ 2 * ((t + μ) / μ) = μ * (t + μ) := by field_simp
  rw [h2]
  nlinarith [ht, ht3, hμ, sq_nonneg (t - μ)]

/-! ## 2. The split of the localised potential word -/

/-- **Integrability of the fibre half of `sbPot`**: the state-level fibre sum
`∫Φ²·Σᵢ w1Fibre ℓ (wSmall1Pair h M ℓ d u) (xᵢ)` is integrable over the box, from the per-slot
integrability `Work.BoseFixB1S.wSmall1Pair_slot_integrableOn` and
`MeasureTheory.integrable_finsetSum`. -/
theorem integrableOn_fibSumIntegrand {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R0 : ℝ} (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      (Submission.BoseGases.abox n ℓ) := by
  have h1 : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y))
      (Submission.BoseGases.abox n ℓ) := fun i =>
    Work.BoseFixB1S.wSmall1Pair_slot_integrableOn (v := v) (R0 := R0)
      hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u Φ hΦc i
  have hfun : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      = fun x : Submission.BoseGases.X n => ∑ i : Fin n, (Φ x) ^ 2 *
          (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) := by
    funext x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Submission.BoseGases.w1Fibre]
  rw [hfun]
  exact integrable_finsetSum _ fun i _ => h1 i

/-- **Integrability of the pair half of `sbPot`**: the state-level pair sum
`∫Φ²·(½Σ_{p∈pairSet n} wSmallPair M ℓ d u v (x_{p.1}) (x_{p.2}))` is integrable over the box,
from the per-pair integrability `Work.BoseFixB1S.wSmallPair_pair_integrableOn`. -/
theorem integrableOn_pairSumIntegrand {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv1 : MeasureTheory.MemLp v 1) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
      (Submission.BoseGases.abox n ℓ) := by
  have h2 := Work.BoseFixB1S.wSmallPair_pair_integrableOn (v := v) (R0 := R0)
    hv_supp hR0 hv1 hM hℓ hd hR hRχ u Φ hΦc
  have hfun : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = fun x : Submission.BoseGases.X n => ∑ p ∈ Submission.BoseGases.pairSet n,
          ((1 / 2) * ((Φ x) ^ 2 *
            Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))) := by
    funext x
    rw [← mul_assoc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hfun]
  exact integrable_finsetSum _ fun p hp => (h2 p hp).const_mul (1 / 2)

/-- **The split of the localised potential word** (`qLHSwordB`) into its chemical-potential loss
and its pair term, at *arbitrary* box parameters `(M, ℓ, d)`:

    `qLHSwordB h M ℓ d μ u Φ = −μ·fibSum h M ℓ d u Φ + pairSum v M ℓ d u Φ`,

i.e. the single box integral of `qLHSword` is the sum of the two state-level integrals.  The passage
is `MeasureTheory.integral_add` + `integral_const_mul`, which needs the integrability of both halves
(`integrableOn_fibSumIntegrand`, `integrableOn_pairSumIntegrand`). -/
theorem qLHSwordB_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (M : ℕ) (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ
      = - (μ * Work.BoseFixB1.fibSum h M ℓ d u Φ)
        + Work.BoseFixB1.pairSum v M ℓ d u Φ := by
  have hfib := integrableOn_fibSumIntegrand (v := v) (h := h) (R0 := R0) hv_supp hR0 hv hvrad hM
    hℓ hd hR hRχ u hΦc
  have hpair := integrableOn_pairSumIntegrand (v := v) (R0 := R0) hv_supp hR0 hv1 hM hℓ hd hR hRχ
    u hΦc
  have h1 : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (-μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
          + (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
              Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = fun x : Submission.BoseGases.X n =>
          (-μ * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
            + (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))) := by
    funext x; ring
  calc Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          (-μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
            + (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) := by
        rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
    _ = ∫ x in Submission.BoseGases.abox n ℓ,
          (-μ * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
            + (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun h1 x)
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
          -μ * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
        + ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
            ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) :=
        integral_add (hfib.const_mul (-μ)) hpair
    _ = - (μ * Work.BoseFixB1.fibSum h M ℓ d u Φ)
        + Work.BoseFixB1.pairSum v M ℓ d u Φ := by
        rw [integral_const_mul]
        simp only [Work.BoseFixB1.fibSum, Work.BoseFixB1.pairSum, Submission.BoseGases.w1Fibre]
        ring

/-- **The split of `sbPot` at FS's parameters** — the form consumed by the per-box assembly. -/
theorem sbPot_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (u : EuclideanSpace ℝ (Fin 3))
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0) :
    Work.BoseFixB1.sbPot h μ u Φ
      = - (μ * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ)
        + Work.BoseFixB1.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ :=
  qLHSwordB_split (v := v) (h := h) (R0 := R) hv_supp hR hv hvrad hv1 _
    (by rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue])
    (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) hR16 hRχ u hΦc

/-! ## 3. The regime arithmetic of the gap payment -/

/-- **The `ε_T`-gap regime is automatic for admissible `μ`.**  At FS's parameters the hypothesis
`2(1+π⁻²)(dℓ c' √(μ a v))² ≤ ε_T` of `perBoxF_pieces.sbKin_ge_mu_av_cnPlus` reads, in closed form,
`2(1+π⁻²)c'²·t^{13/1292} ≤ 1` with `t = μ(a v)³`, so it holds for all admissible `μ` once
`ε₀ ≤ (1/(2(1+π⁻²)c'²+1))^{1292/13}`. -/
theorem gapRegime_of_adm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {c' : ℝ} (hc' : 0 ≤ c') :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      2 * (1 + (Real.pi ^ 2)⁻¹)
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * c'
              * Real.sqrt (μ * (_root_.BoseGases.a v))) ^ 2
        ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
  set A : ℝ := _root_.BoseGases.a v with hA
  set B : ℝ := 1 / (2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 + 1) with hB
  have hBpos : 0 < 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 + 1 := by
    have h1 : (0:ℝ) ≤ (1 + (Real.pi ^ 2)⁻¹) := by positivity
    nlinarith [sq_nonneg c']
  have hB0 : 0 < B := by rw [hB]; exact div_pos one_pos hBpos
  have hBkey : (2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 + 1) * B = 1 := by
    rw [hB]; field_simp
  refine ⟨min 1 (B ^ (1292 / 13 : ℝ)), lt_min one_pos (Real.rpow_pos_of_pos hB0 _), ?_⟩
  intro μ hAdm
  have hμ : 0 < μ := hAdm.1
  have ht0 : 0 < μ * A ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hε₀ : μ * A ^ 3 ≤ B ^ (1292 / 13 : ℝ) := le_trans hAdm.2.1 (min_le_right _ _)
  have hte : (μ * A ^ 3) ^ (13 / 1292 : ℝ) ≤ B := by
    have hb : (μ * A ^ 3) ^ (13 / 1292 : ℝ) ≤ (B ^ (1292 / 13 : ℝ)) ^ (13 / 1292 : ℝ) :=
      Real.rpow_le_rpow ht0.le hε₀ (by norm_num)
    rwa [← Real.rpow_mul hB0.le, show (1292:ℝ) / 13 * (13 / 1292) = 1 by norm_num,
      Real.rpow_one] at hb
  have hfinal : 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * (μ * A ^ 3) ^ (13 / 1292 : ℝ) ≤ 1 := by
    have h1 : 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * (μ * A ^ 3) ^ (13 / 1292 : ℝ)
        ≤ 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * B :=
      mul_le_mul_of_nonneg_left hte (by positivity)
    have h2 : 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * B
        ≤ (2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 + 1) * B := by nlinarith [hB0.le]
    linarith [h1, h2, hBkey]
  -- the closed form of the squared bracket
  have hsq : ((Work.BoseBox.paramsAt μ A).d * Work.BoseBox.sideAt μ A * c'
        * Real.sqrt (μ * A)) ^ 2 = c' ^ 2 * Work.BoseBox.fsXp (μ * A ^ 3) 9 := by
    have hd_eq : (Work.BoseBox.paramsAt μ A).d = Work.BoseBox.fsXp (μ * A ^ 3) 6 := rfl
    have hside_eq : Work.BoseBox.sideAt μ A = A * Work.BoseBox.fsXp (μ * A ^ 3) (-163) :=
      Work.BoseFixB1.sideAt_eq_fsXp (A := A) (μ := μ) hav hμ
    have hsqr : Real.sqrt (μ * A) ^ 2 = μ * A := Real.sq_sqrt (mul_nonneg hμ.le hav.le)
    have h1 : Work.BoseBox.fsXp (μ * A ^ 3) 6 * Work.BoseBox.fsXp (μ * A ^ 3) (-163)
        = Work.BoseBox.fsXp (μ * A ^ 3) (-157) := by
      rw [Work.BoseBox.fsXp_mul ht0]; norm_num
    have h2 : Work.BoseBox.fsXp (μ * A ^ 3) (-157) * Work.BoseBox.fsXp (μ * A ^ 3) (-157)
        = Work.BoseBox.fsXp (μ * A ^ 3) (-314) := by
      rw [Work.BoseBox.fsXp_mul ht0]; norm_num
    have h3 : (μ * A ^ 3) * Work.BoseBox.fsXp (μ * A ^ 3) (-314)
        = Work.BoseBox.fsXp (μ * A ^ 3) 9 := by
      calc (μ * A ^ 3) * Work.BoseBox.fsXp (μ * A ^ 3) (-314)
          = (μ * A ^ 3) ^ (1:ℝ) * (μ * A ^ 3) ^ ((-314:ℝ) / 323) := by
              rw [Real.rpow_one]; rfl
        _ = (μ * A ^ 3) ^ ((1:ℝ) + (-314:ℝ) / 323) := (Real.rpow_add ht0 1 _).symm
        _ = (μ * A ^ 3) ^ ((9:ℝ) / 323) := by congr 1; norm_num
        _ = Work.BoseBox.fsXp (μ * A ^ 3) 9 := rfl
    rw [mul_pow, mul_pow, mul_pow, hd_eq, hside_eq, hsqr]
    calc Work.BoseBox.fsXp (μ * A ^ 3) 6 ^ 2 * (A * Work.BoseBox.fsXp (μ * A ^ 3) (-163)) ^ 2
          * c' ^ 2 * (μ * A)
        = c' ^ 2 * ((μ * A ^ 3) * (Work.BoseBox.fsXp (μ * A ^ 3) 6
            * Work.BoseBox.fsXp (μ * A ^ 3) (-163))
            * (Work.BoseBox.fsXp (μ * A ^ 3) 6 * Work.BoseBox.fsXp (μ * A ^ 3) (-163))) := by
          ring
      _ = c' ^ 2 * ((μ * A ^ 3) * (Work.BoseBox.fsXp (μ * A ^ 3) (-157)
            * Work.BoseBox.fsXp (μ * A ^ 3) (-157))) := by rw [h1]; ring
      _ = c' ^ 2 * ((μ * A ^ 3) * Work.BoseBox.fsXp (μ * A ^ 3) (-314)) := by rw [h2]
      _ = c' ^ 2 * Work.BoseBox.fsXp (μ * A ^ 3) 9 := by rw [h3]
  rw [hsq]
  have hsplit : Work.BoseBox.fsXp (μ * A ^ 3) 9
      = Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) * Work.BoseBox.fsXp (μ * A ^ 3) (13 / 4) := by
    rw [Work.BoseBox.fsXp_mul ht0]; norm_num
  rw [hsplit]
  have heTpos : 0 < Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) := Work.BoseBox.fsXp_pos ht0
  have hfs : Work.BoseBox.fsXp (μ * A ^ 3) (13 / 4) = (μ * A ^ 3) ^ (13 / 1292 : ℝ) := by
    rw [Work.BoseBox.fsXp]; norm_num
  rw [hfs]
  calc 2 * (1 + (Real.pi ^ 2)⁻¹) * (c' ^ 2
        * (Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) * (μ * A ^ 3) ^ (13 / 1292 : ℝ)))
      = (2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * (μ * A ^ 3) ^ (13 / 1292 : ℝ))
          * Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) := by ring
    _ ≤ 1 * Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) :=
        mul_le_mul_of_nonneg_right hfinal heTpos.le
    _ = Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) := one_mul _

/-! ## 4. The "gap pays" branch of `PerBoxF` -/

/-- **`PerBoxF` holds whenever the excited count is a fixed fraction of `n‖Φ‖²`.**

With the *explicit* constants `C_s = chiSupAbs·chiSmallDecay mValue`, `K_av` the fibre constant of
`perBoxF_localised.fibSum_le`, `c₀ = (1/4)C_W C_s² + K_av C_s`, `c'² = 10^{100}c₀ + 1` and
`γ = c₀/c'² ≤ 10^{-100}`, every admissible state satisfying `γ·n·‖Φ‖² ≤ n₊(B)` (the FS-faithful
excited count `cnPlusBoxInd` of the sliding box) obeys `PerBoxF` at `c₁ = 1/4`; the `ε₀` is small
enough that FS's `ε_T`-gap absorbs `c'²μ(a v)·n₊(B)`. -/
theorem perBoxF_of_gapPayment {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C γ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < γ ∧ γ ≤ (1 / 10 : ℝ) ^ (100 : ℕ) ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          γ * (n : ℝ) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ) →
          PerBoxF v h R (1 / 4) C μ n Φ u := by
  obtain ⟨ε₁, hε₁, hsplit⟩ :=
    Work.BoseFixB1S.SbPotHalvesB1Fix (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₂, CW, hε₂, hCW0, hWle⟩ :=
    w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  obtain ⟨εr, hεr, hreg2⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  -- the explicit constants
  have hCs0 : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg _)
  have hKav0 : 0 ≤ 16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      Submission.BoseGases.chiSupAbs_nonneg)
      (Submission.BoseGases.chiSmallDecay_nonneg _))
      (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos _))
  set Cs : ℝ := Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue with hCs
  set Kav : ℝ := 16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue with hKav
  set c₀ : ℝ := (1 / 4) * CW * Cs ^ 2 + Kav * Cs with hc₀
  have hc₀0 : 0 ≤ c₀ := by
    rw [hc₀]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCW0) (sq_nonneg Cs))
      (mul_nonneg hKav0 hCs0)
  set csq : ℝ := (10 : ℝ) ^ (100 : ℕ) * (c₀ + 1) with hcsq
  have hcsq0 : 0 < csq := by
    rw [hcsq]
    have h1 : 0 < c₀ + 1 := by linarith
    positivity
  set c' : ℝ := Real.sqrt csq with hc'
  set γ : ℝ := (c₀ + 1) / csq with hγ
  have hc'0 : 0 ≤ c' := Real.sqrt_nonneg _
  have hc'2 : c' ^ 2 = csq := Real.sq_sqrt hcsq0.le
  have hγ0 : 0 < γ := by
    rw [hγ]
    exact div_pos (by linarith) hcsq0
  have hγeq : c' ^ 2 * γ = c₀ + 1 := by
    rw [hγ, hc'2]
    exact mul_div_cancel₀ (c₀ + 1) (ne_of_gt hcsq0)
  obtain ⟨ε₃, hε₃, hreg3⟩ := gapRegime_of_adm (v := v) hav (c' := c') hc'0
  have hγle : γ ≤ (1 / 10 : ℝ) ^ (100 : ℕ) := by
    have hne : c₀ + 1 ≠ 0 := by linarith
    have heq : (c₀ + 1) / ((10 : ℝ) ^ (100 : ℕ) * (c₀ + 1)) = (1 / 10 : ℝ) ^ (100 : ℕ) := by
      rw [div_eq_iff (by positivity : ((10 : ℝ) ^ (100 : ℕ) * (c₀ + 1)) ≠ 0)]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    rw [hγ, hcsq, heq]
  refine ⟨min (min (min ε₁ ε₂) ε₃) (min εr 1), 1, γ,
    lt_min (lt_min (lt_min hε₁ hε₂) hε₃) (lt_min hεr one_pos), zero_le_one, hγ0, hγle, ?_⟩
  intro μ hAdm n Φ u hpay
  have hμ : 0 < μ := hAdm.1
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- the admissible thresholds
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_left _ _)))
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hAdm₃ : Work.BoseBoxFix.Adm v ε₃ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmr : Work.BoseBoxFix.Adm v εr μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  -- the parameter facts
  have hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd0 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
  obtain ⟨hR16, hRχ'⟩ := hreg2 μ hμ hdil
  have hA0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  -- ### the ingredients
  have hF := psiWeight_integral_le_thick (μ := μ) hμ (M := (Work.BoseBox.paramsAt μ
    (_root_.BoseGases.a v)).M) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hM1 hℓ0 u hΦc
  have hsc := scountB_le (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hM1 u hΦc
  have hWle' := hWle μ hAdm₂ u
  have hfib := fibSum_le (v := v) (h := h) hv hvrad hR hv_supp hM1 hℓ0 hd0 hR16 hRχ' u hΦc
  have hchi := chiSum_le (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hM1 u hΦc
  have hpair0 := pairSum_nonneg (v := v) hv (M := (Work.BoseBox.paramsAt μ
    (_root_.BoseGases.a v)).M) (u := u) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (Φ : Submission.BoseGases.X n → ℝ)
  have hW0 := w1MassB_nonneg (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) h hv hvrad hR hv_supp hℓ0 hd0 u
  have hN0 := normB_nonneg (v := v) (μ := μ) (n := n) (Φ : Submission.BoseGases.X n → ℝ)
  have hchi0 := chiMass_nonneg (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
  have hsplit' := sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdm hΦc u hR16 hRχ'
  have hsb : sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
          (Φ : Submission.BoseGases.X n → ℝ)
        + (-(μ * fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ))
            + pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)) := by
    rw [sbWord, hsplit']
  have hgap := sbKin_ge_mu_av_cnPlus (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (u := u) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) (c' := c')
    (by positivity) hμ.le hc'0 (mul_pos hd0 hℓ0) (Work.BoseFixB1.adm_eT_pos hAdm)
    (hreg3 μ hAdm₃) (Work.BoseFixB1.tBwordKinInd_nonneg _)
  -- ### the arithmetic
  unfold PerBoxF
  simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] at hpay ⊢
  set N : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 with hN
  set χ : ℝ := chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hχ
  set W : ℝ := w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hW
  set Fterm : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
        / chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) with hFt
  set nps : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ) with hnps
  -- the two final bounds
  have hLHS : (1 / 4) * (W * Fterm) - (1 / 2) * μ ^ 2 * W * N
      - 1 * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * χ * N
          + μ * (_root_.BoseGases.a v) * N)
      ≤ (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := by
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h4 : 0 ≤ χ⁻¹ := inv_nonneg.mpr hchi0
    have h5 : 0 ≤ μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N) := by positivity
    -- the F-term, with the smooth count replaced by `n Cs² N`
    have h6 : Fterm ≤ μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N) := by
      have hmid : χ⁻¹ * scountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
          ≤ χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) := mul_le_mul_of_nonneg_left hsc h4
      have hmid2 : χ⁻¹ * scountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ) + μ * N
          ≤ χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N := by linarith
      exact le_trans hF (mul_le_mul_of_nonneg_left hmid2 hμ.le)
    have h7 : (1 / 4 : ℝ) * (W * Fterm)
        ≤ (1 / 4 : ℝ) * (W * (μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 hW0) (by norm_num)
    have h9 : (1 / 4 : ℝ) * (W * (μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N)))
        = (1 / 4) * W * μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N)) + (1 / 4) * W * μ ^ 2 * N := by
      ring
    have h10 : χ * χ⁻¹ ≤ 1 := by
      rcases eq_or_lt_of_le hchi0 with h | h
      · rw [← h, inv_zero, mul_zero]; norm_num
      · rw [mul_inv_cancel₀ (ne_of_gt h)]
    have h11 : W * χ⁻¹ ≤ CW * (_root_.BoseGases.a v) := by
      have h1 : W * χ⁻¹ ≤ (CW * (_root_.BoseGases.a v) * χ) * χ⁻¹ :=
        mul_le_mul_of_nonneg_right hWle' h4
      have h2 : (CW * (_root_.BoseGases.a v) * χ) * χ⁻¹
          = CW * (_root_.BoseGases.a v) * (χ * χ⁻¹) := by ring
      have h3 : CW * (_root_.BoseGases.a v) * (χ * χ⁻¹)
          ≤ CW * (_root_.BoseGases.a v) * 1 :=
        mul_le_mul_of_nonneg_left h10 (mul_nonneg hCW0 hA0)
      linarith [h1, h2, h3]
    have h12 : (1 / 4 : ℝ) * W * μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N))
        ≤ (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := by
      have hfac : (0:ℝ) ≤ (1/4) * μ * ((n : ℝ) * Cs^2 * N) := by positivity
      have h1 : (W * χ⁻¹) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N))
          ≤ (CW * (_root_.BoseGases.a v)) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N)) :=
        mul_le_mul_of_nonneg_right h11 hfac
      calc (1 / 4 : ℝ) * W * μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N))
          = (W * χ⁻¹) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N)) := by ring
        _ ≤ (CW * (_root_.BoseGases.a v)) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N)) := h1
        _ = (1/4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := by ring
    have h13 : 0 ≤ (1 / 4 : ℝ) * W * μ ^ 2 * N := by positivity
    have h14 : 0 ≤ μ * (_root_.BoseGases.a v) * N := by positivity
    have h15 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
        * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * χ * N := by
      have hKB : (0:ℝ) ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
        le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
      have h3 : (0:ℝ) ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg hA0 3)) _
      positivity
    linarith [h7, h9, h12, h13, h14, h15]
  have hRHS : c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
      - μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N
      ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [hsb]
    have h1 : μ * fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ μ * (Kav * (_root_.BoseGases.a v) * chiSum
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)) :=
      mul_le_mul_of_nonneg_left hfib hμ.le
    have h2 : μ * (Kav * (_root_.BoseGases.a v) * chiSum
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ))
        ≤ μ * (Kav * (_root_.BoseGases.a v) * ((n : ℝ) * Cs * N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hchi (mul_nonneg hKav0 hA0)) hμ.le
    have h3 : μ * (Kav * (_root_.BoseGases.a v) * ((n : ℝ) * Cs * N))
        = μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N := by ring
    linarith [h1, h2, h3, hgap, hpair0]
  have hkey : (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N
      ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
        - μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N := by
    have h1 : c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
        ≥ μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) * (c₀ + 1) := by
      have h2 : c' ^ 2 * μ * (_root_.BoseGases.a v) * (γ * (n : ℝ) * N)
          ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * nps :=
        mul_le_mul_of_nonneg_left hpay (by positivity)
      have h3 : c' ^ 2 * μ * (_root_.BoseGases.a v) * (γ * (n : ℝ) * N)
          = μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) * (c' ^ 2 * γ) := by ring
      rw [hγeq] at h3
      linarith [h2, h3]
    have h2 : μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) * (c₀ + 1)
        = (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N
          + μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N
          + μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) := by
      rw [hc₀]; ring
    have h3 : 0 ≤ μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) := by positivity
    linarith [h1, h2, h3]
  calc (1 / 4) * (W * Fterm) - (1 / 2) * μ ^ 2 * W * N
      - 1 * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * χ * N
          + μ * (_root_.BoseGases.a v) * N)
      ≤ (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := hLHS
    _ ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
        - μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N := hkey
    _ ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := hRHS

/-! ## 5. The reduction of the target to a single *flat-branch* atom -/

/-- **The thick case of the crux follows from the gap branch plus the flat branch.**

`perBoxF_of_gapPayment` (this file, PROVED) supplies the branch
`γ·n·‖Φ‖² ≤ n₊(B(u))` with an *explicit* threshold bound `γ ≤ 10^{-100}`; a statement of the
complementary branch — `n₊(B(u)) ≤ 10^{-100}·n·‖Φ‖²` implies `PerBoxF` — therefore completes the
dichotomy.  The parameter bookkeeping is `ε₀ = min`, `c₁ = min`, `C = max`, using the
monotonicity of `PerBoxF`'s left side in `c₁` (downwards) and `C` (upwards) (the `F`-term and the
error bracket are `≥ 0`). -/
theorem perBoxF_thick_of_flatBranch {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hflat : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          ¬ IsThinBox v h μ u →
          Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ)
                * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          PerBoxF v h R c₁ C μ n Φ u) :
    PerBoxF_thick v h R := by
  obtain ⟨εg, Cg, γg, hεg, hCg, hγg, hγg100, hgap⟩ :=
    perBoxF_of_gapPayment (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εa, c₁a, Ca, hεa, hc₁a, hCa, hflat'⟩ := hflat
  refine ⟨min εg εa, min (1 / 4) c₁a, max Cg Ca, lt_min hεg hεa, lt_min (by norm_num) hc₁a,
    le_max_of_le_left hCg, ?_⟩
  intro μ hAdm n Φ u hu hthick
  have hAdm_g : Work.BoseBoxFix.Adm v εg μ := Adm.mono hAdm (min_le_left _ _)
  have hAdm_a : Work.BoseBoxFix.Adm v εa μ := Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := hAdm.1
  have ha0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  -- the `F`-term and the error bracket of `PerBoxF` are nonnegative
  have hχ0 : 0 ≤ chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := chiMass_nonneg _ _ _ _
  have hF0 : 0 ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x /
            chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (perBoxFCase_psiWeight_nonneg (by norm_num) hμ
        (div_nonneg (nCountB_nonneg _ _ _ _ x) hχ0))
  have hW0 : 0 ≤ w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    w1MassB_nonneg (v := v) (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      h hv hvrad hR hv_supp (adm_ell_pos hAdm_g) (adm_d_pos hAdm_g) u
  have herr0 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v) *
        ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) *
        chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u *
        normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      + μ * (_root_.BoseGases.a v) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have hN0 : 0 ≤ normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      normB_nonneg (v := v) (μ := μ) (n := n) _
    have hKB : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
      le_of_lt (paramsAt_KB_pos hAdm_g)
    have h3 : 0 ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg ha0 3)) _
    have hS : 0 ≤ (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
      add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hKB 3) h3)
    positivity
  by_cases hcase : γg * (n : ℝ) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Φ : Submission.BoseGases.X n → ℝ)
  · have hp := hgap μ hAdm_g n Φ u hcase
    simp only [PerBoxF] at hp ⊢
    have h1 := mul_le_mul_of_nonneg_right (min_le_left (1 / 4) c₁a) (mul_nonneg hW0 hF0)
    have h2 := mul_le_mul_of_nonneg_right (le_max_left Cg Ca) herr0
    linarith
  · have hlt : Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Φ : Submission.BoseGases.X n → ℝ)
        ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ)
            * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
      have hN0 : 0 ≤ normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
        normB_nonneg (v := v) (μ := μ) (n := n) _
      have hstep : γg * (n : ℝ) ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hγg100 (Nat.cast_nonneg n)
      have hstep2 : γg * (n : ℝ) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ)
              * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
        mul_le_mul_of_nonneg_right hstep hN0
      have hlt2 : Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : Submission.BoseGases.X n → ℝ)
          < γg * (n : ℝ) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := not_le.mp hcase
      linarith
    have hp := hflat' μ hAdm_a n Φ u hu hthick hlt
    simp only [PerBoxF] at hp ⊢
    have h1 := mul_le_mul_of_nonneg_right (min_le_right (1 / 4) c₁a) (mul_nonneg hW0 hF0)
    have h2 := mul_le_mul_of_nonneg_right (le_max_right Cg Ca) herr0
    linarith

/-! ## 6. The target

**VERDICT (session 3): the target is FALSE as stated** — it is a *mis-statement* of FS
`thm:smallbox`: its credit is the count-free scalar `C(μ²(a v)Γ chiMass + μ(a v))‖Φ‖²`, whereas FS's
lemma (and the true statement) carries the **operator** credit `C a(v)(μ + n₀|B|⁻¹)n₊`, i.e. the
joint moment `⟨n₀n₊⟩`.  Read
`Submission/Work/BoseFixB1/FINDING_perBoxF_thick_VERDICT.md` (the ledger identity makes the payers of
`PerBoxF` a *closed* list, and on the soft pair-suppression (`dip`) family of a square-well potential
their sum is `Λβ + ρ(1−√β)² ≥ 0.75·D` while the demand is `D + o(D)` — a `D`-sized deficit no fixed
`(ε₀, c₁, C)` can pay).  `PerBoxF_thick` is *equivalent* to the corpus's crux `PerBoxFAll`
(`perBoxF_of_thin_thick` + the proved thin case), so the crux `perBoxFWeight_holds` as stated is
false too; the repair is to keep the joint moment (or a box-support hypothesis, as the corpus's only
axiom-clean per-box payment `a0A2PaymentAdm_holds` does). -/

/-- **The target, derived from the upstream crux `perBoxFWeight_holds`.**

This is formal only: the upstream statement (the a-priori chapter's crux, in its `∃`-form) is
*equivalent* to the target, and both are false as stated — see the section header above and
`FINDING_perBoxF_thick_VERDICT.md`.  Kept so that the file records the reduction. -/
theorem perBoxF_thick {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseFixB1.PerBoxF_thick v h R := by
  obtain ⟨ε₀, c₁, C, hε, hc, hC, H⟩ :=
    perBoxFWeight_holds (v := v) h hv hv1 hvrad hR hv_supp hav
  exact ⟨ε₀, c₁, C, hε, hc, hC, fun μ hAdm n Φ u hu _ => H μ hAdm n Φ u hu⟩

end Work.BoseFixB1
