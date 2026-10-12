import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.perBoxF_thick
import Submission.Work.BoseFixB1.qLHSwordB_ge_neg_bandS
import Submission.Work.BoseFixB1S.BandSizeArithB1
import Submission.Work.BoseFixB1S.integrableOn_phi_sq_indicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxCountBand` — the box-count form of the band bounds

## What the target is

`Work.BoseFixB1.BandCrudeLower` (FS l.4083 restricted to the band) is the corpus node
`Work.BoseFixB1B.CrudeLower` (the crude per-box bound `perBoxCrudeLower`, FS `final_v2.tex`
l.4083) with the extra hypothesis that `u` lies on the bad band

    u ∈ bandSet ℓ d μ,        ℓ = sideAt μ (a v),  d = (paramsAt μ (a v)).d,

and *without* any low-state (`IsLowB`) restriction.

The band restriction is what makes the unrestricted crude bound plausible: off the band, the
corpus's own machine-checked findings (`FINDING_perBoxCrudeB1.md`,
`FINDING_mfFlatRegimePaysB1_FALSE.md`) exhibit the *window-mismatch* family (the kinetic word is
windowed by the bump `chiB`, which vanishes on the part of the box outside its inscribed ball,
while the potential word, windowed by the cosine bump `chiSmallB`, is alive there); on the band
`chiSmallB ≤ bandS M ℓ d μ` pointwise with `bandS² = chiCs²·2^{2M}·t^{14.67}` (`t = μ(a v)³`)
*superpolynomially* small, which suppresses every family of that shape.

## What this file proves

Two reductions, both sorry-free.

* `sbWord_ge_neg_bandCount` — the **sharp band lower bound for the word**,

      sbWord h μ u Φ ≥ −μ · (bandK v h M · bandS M ℓ d μ ^ 2) · ⟨count⟩,

  where `⟨count⟩ = Σ_i ∫_{abox n ℓ} Φ² · 1_{B(u)}(x_i)` is the *box count*, not the particle
  number `n`.  This sharpens the corpus's `qLHSwordB_ge_neg_bandS`/`sbCore`, which bound by
  `−μ·(bandK·bandS²·n)·‖Φ‖²`: the localised fibre vanishes off the box
  (`chiSmallB_support_mem_dlBox`), so the loss only sees the box count.  (The `n`-version is
  *unpayably* lossy: adding arbitrarily many particles supported outside `B(u)` leaves `sbWord`
  unchanged while inflating `n` — the counterexample found in the review of the sibling node.)

* `bandCrudeLower_of_bandCount` — the target from the single count bound

      (CAP)   ∀ μ (Adm v ε₀ μ), sbWord h μ u Φ < 0 →
                ⟨count⟩ ≤ C · ℓ³ · (μ · chiMass M ℓ d u + 1) · normB v μ n Φ,

  which is the *box-count* form of the corpus node `Work.BoseFixB1B.ThinShellBandCount` (the
  low-state count cap) **without** the `IsLowB` restriction; it is delegated as
  `Work.BoseFixB1B.BandCountCapArbitrary`.  Given (CAP), the proved band arithmetic
  (`BandSizeArithB1`: `ℓ³·bandK·bandS² ≤ K·(a v)`) closes the target.

(CAP) is the project's central residual (FS §5's `thm:smallbox` in count form): nothing in the
workspace proves it.  Unlike the `n`-form, it is *not* refutable by the far-particle trick (which
changes `n` but not the box count).
-/

namespace Work.BoseFixB1

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. `normB`, the box count and their elementary properties -/

/-- The squared box norm of a state is the integral of `Φ²` over the box (definitional). -/
theorem normB_eq_integral {v : E3 → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    normB v μ n Φ = ∫ x in Submission.BoseGases.abox n (sideAt μ (a v)), (Φ x) ^ 2 := rfl

/-- `normB` is nonnegative. -/
theorem normB_nonneg_band {v : E3 → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : 0 ≤ normB v μ n Φ := by
  rw [normB_eq_integral]
  exact integral_nonneg fun x => sq_nonneg _

/-- The **box count** `Σ_i ∫ Φ² 1_{B(u)}(x_i)`. -/
noncomputable def boxCountAt (ℓ d : ℝ) (u : E3) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)

/-- The box count is nonnegative. -/
theorem boxCountAt_nonneg {ℓ d : ℝ} {u : E3} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : 0 ≤ boxCountAt ℓ d u Φ := by
  rw [boxCountAt]
  refine Finset.sum_nonneg fun i _ => integral_nonneg fun x => ?_
  exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-! ## 1. The sharp band fibre bound -/

/-- **The localised one-body fibre vanishes off the box.** -/
theorem w1Fibre_eq_zero_of_notMem_dlBox {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u x : E3}
    (hx : x ∉ Submission.BoseGases.dlBox ℓ d u) :
    (∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u x y) = 0 := by
  have hchi : Submission.BoseGases.chiSmallB M ℓ d u x = 0 := by
    by_contra hne
    exact hx (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)
  have hfun : (fun y : E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      = fun _ => (0 : ℝ) := by
    funext y
    simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair]
    rw [hchi]
    ring
  rw [hfun, integral_zero]

/-- **The sharp fibre bound on the band**: the localised one-body fibre is bounded by
`bandK·bandS²` and vanishes off the box, i.e. by `bandK·bandS²·1_{B(u)}`. -/
theorem fibre_le_band_indicator {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) (hreg : R ≤ ℓ * d / 16)
    (hregχ : R ≤ ℓ * Submission.BoseGases.chiR0) {u : E3} (hu : u ∈ bandSet ℓ d μ) (x : E3) :
    (∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      ≤ bandK v h M * bandS M ℓ d μ ^ 2
          * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hxB : x ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Set.indicator_of_mem hxB, mul_one]
    exact le_trans (le_abs_self _)
      (w1Fibre_abs_le_bandS_qLHS (v := v) (h := h) hR hv_supp hM hℓ hd hμ hreg hregχ hu x)
  · rw [Set.indicator_of_notMem hxB, mul_zero]
    exact le_of_eq (w1Fibre_eq_zero_of_notMem_dlBox (v := v) (h := h) hM hℓ hd hxB)

/-- **The loss is dominated by the band factor times the box count.** -/
theorem fibSum_le_band_boxCount {v : E3 → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) (hreg : R ≤ ℓ * d / 16)
    (hregχ : R ≤ ℓ * Submission.BoseGases.chiR0) {u : E3} (hu : u ∈ bandSet ℓ d μ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ) :
    fibSum h M ℓ d u Φ ≤ bandK v h M * bandS M ℓ d μ ^ 2 * boxCountAt ℓ d u Φ := by
  rw [fibSum, boxCountAt]
  have hBK : 0 ≤ bandK v h M * bandS M ℓ d μ ^ 2 :=
    mul_nonneg (bandK_nonneg _) (sq_nonneg _)
  have hmeasB : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hBac : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Set.inter_subset_left
  -- integrability of the majorant
  have hInt : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))
      (Submission.BoseGases.abox n ℓ) volume := fun i => by
    simpa only [one_mul] using
      Work.BoseFixB1S.integrableOn_phi_sq_indicator (c := 1) hℓ hmeasB hBac i hΦc
  have hmaj : Integrable (fun x : Submission.BoseGases.X n =>
      (bandK v h M * bandS M ℓ d μ ^ 2) *
        ((Φ x) ^ 2 * ∑ i : Fin n,
          (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)))
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
    have hsum : Integrable (fun x : Submission.BoseGases.X n => ∑ i : Fin n,
        (bandK v h M * bandS M ℓ d μ ^ 2) *
          ((Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)))
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
      integrable_finsetSum (s := Finset.univ)
        (f := fun i (x : Submission.BoseGases.X n) =>
          (bandK v h M * bandS M ℓ d μ ^ 2) *
            ((Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)))
        (fun i _ => (hInt i).const_mul _)
    refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum]
  -- the pointwise bound
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ (bandK v h M * bandS M ℓ d μ ^ 2) *
            ((Φ x) ^ 2 * ∑ i : Fin n,
              (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) := by
    intro x
    have h1 : ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ ∑ i : Fin n, (bandK v h M * bandS M ℓ d μ ^ 2
            * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) :=
      Finset.sum_le_sum fun i _ => fibre_le_band_indicator (v := v) (h := h) hR hv_supp hM
        hℓ hd hμ hreg hregχ hu (x i)
    have h2 : (∑ i : Fin n, (bandK v h M * bandS M ℓ d μ ^ 2
            * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)))
        = (bandK v h M * bandS M ℓ d μ ^ 2)
            * ∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator
                (fun _ => (1 : ℝ)) (x i) := by
      rw [Finset.mul_sum]
    rw [h2] at h1
    have h3 : (Φ x) ^ 2 * ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ (Φ x) ^ 2 * ((bandK v h M * bandS M ℓ d μ ^ 2)
            * ∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator
                (fun _ => (1 : ℝ)) (x i)) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    refine le_trans h3 (le_of_eq ?_)
    ring
  -- nonnegativity of the integrand
  have hnn : 0 ≤ᵐ[((volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ))] (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun i _ =>
        wSmall1Pair_fibre_nonneg (v := v) (R0 := R) hR hv hvrad hv_supp h u (x i))
  have hmono := integral_mono_of_nonneg hnn hmaj (Filter.Eventually.of_forall hpt)
  refine le_trans hmono (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  have hsplit : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ∑ i : Fin n,
          (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))
      = ∑ i : Fin n, (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) := by
    have hpt' : ∀ x : Submission.BoseGases.X n,
        (Φ x) ^ 2 * ∑ i : Fin n,
            (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
          = ∑ i : Fin n, (Φ x) ^ 2 *
              (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) :=
      fun x => Finset.mul_sum _ _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt')]
    exact integral_finset_sum _ (fun i _ => hInt i)
  rw [hsplit]

/-! ## 2. The sharp band lower bound for the word -/

/-- **The band lower bound for `sbWord` in terms of the box count.**  On the bad band the sliding
word is bounded below by `−μ·(bandK·bandS²)·⟨count⟩`, where `⟨count⟩` is the box count. -/
theorem sbWord_ge_neg_bandCount {v : E3 → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {εr μ : ℝ} (hadmr : Adm v εr μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) {u : E3}
    (hu : u ∈ bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)
    (hRd : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hRχ : R ≤ sideAt μ (a v) * Submission.BoseGases.chiR0) :
    -(μ * (bandK v h (paramsAt μ (a v)).M *
          bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2))
        * boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ)
      ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  have hμ : 0 < μ := adm_mu_pos hadmr
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hadmr
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hadmr
  have hM : 1 ≤ (paramsAt μ (a v)).M := by
    rw [M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hcont : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- the potential half
  have hsplit := sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hadmr hcont u
    hRd hRχ
  have hpair : 0 ≤ pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ) :=
    pairSum_nonneg (v := v) hv (M := (paramsAt μ (a v)).M) (ℓ := sideAt μ (a v))
      (d := (paramsAt μ (a v)).d) u (Φ : Submission.BoseGases.X n → ℝ)
  have hfib := fibSum_le_band_boxCount (v := v) (h := h) hv hvrad hR hv_supp hM hℓ hd hμ hRd hRχ hu
    (Φ : Submission.BoseGases.X n → ℝ) hcont
  -- the kinetic half
  have hkin : 0 ≤ sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : Submission.BoseGases.X n → ℝ) := by
    show 0 ≤ Work.UBBInputs8.tBwordBInd n (sideAt μ (a v)) (paramsAt μ (a v)).d
      (paramsAt μ (a v)).eT (sbCut μ (a v)) u (Φ : Submission.BoseGases.X n → ℝ)
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ (adm_eT_bounds hadmr).1 u _
  rw [sbWord, hsplit]
  have h1 : -(μ * (bandK v h (paramsAt μ (a v)).M *
        bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2))
      * boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ -(μ * fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hfib hμ.le]
  linarith [h1, hpair, hkin]

/-! ## 3. The reduction of the target to the box-count bound -/

/-- **The target from the box-count bound.**  Given (CAP) — the box-count bound on the band for
the states with negative word — the crude per-box bound on the band holds. -/
theorem bandCrudeLower_of_bandCount {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hcap : ∃ εc Cc : ℝ, 0 < εc ∧ 0 ≤ Cc ∧
      ∀ μ : ℝ, Adm v εc μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3),
          u ∈ bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) < 0 →
          boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Cc * (sideAt μ (a v)) ^ 3
                * (μ * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                      (paramsAt μ (a v)).d u + 1)
                * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
          (u : E3),
          u ∈ bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                      (paramsAt μ (a v)).d u
                + μ * (_root_.BoseGases.a v)))
              * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨εr, hεr, hregh⟩ := regime_sideAt_ge (v := v) hav hR
  obtain ⟨εa, Ka, hεa, hKa, harith⟩ :=
    Work.BoseFixB1S.BandSizeArithB1 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εc, Cc, hεc, hCc, hcap'⟩ := hcap
  refine ⟨min (min εc εa) εr, Cc * Ka,
    lt_min (lt_min hεc hεa) hεr, mul_nonneg hCc hKa, ?_⟩
  intro μ hAdm n Φ u hu
  have hAdmc : Adm v εc μ := Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdma : Adm v εa μ := Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmr : Adm v εr μ := Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := adm_mu_pos hAdm
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt (adm_a_pos hAdm)
  have hJ : 0 ≤ normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := normB_nonneg_band _
  have hcnt0 : 0 ≤ boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ) := boxCountAt_nonneg _
  have hChm : 0 ≤ chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
    chiMass_nonneg _ _ _ _
  have hX : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
      * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      + μ * (_root_.BoseGases.a v) :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hChm) (mul_nonneg hμ.le ha)
  obtain ⟨hRd, hRχ⟩ := hregh μ hμ (adm_dilute hAdmr)
  have hband := sbWord_ge_neg_bandCount (v := v) (h := h) hv hv1 hvrad hR hv_supp
    (εr := εr) hAdmr Φ hu hRd hRχ
  by_cases hneg : sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) < 0
  · have hcnt := hcap' μ hAdmc n Φ u hu hneg
    have har := harith μ hAdma
    have har' : (sideAt μ (a v)) ^ 3 * (bandK v h (paramsAt μ (a v)).M *
        bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
        ≤ Ka * (_root_.BoseGases.a v) := by
      simpa only [mul_assoc] using har
    have hBK : 0 ≤ bandK v h (paramsAt μ (a v)).M *
        bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2 :=
      mul_nonneg (bandK_nonneg _) (sq_nonneg _)
    have hkey : μ * (bandK v h (paramsAt μ (a v)).M *
          bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
        * boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
        ≤ (Cc * Ka) * (μ ^ 2 * (_root_.BoseGases.a v)
              * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            + μ * (_root_.BoseGases.a v))
          * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
      have h1 : μ * (bandK v h (paramsAt μ (a v)).M *
            bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
          * boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)
          ≤ μ * (bandK v h (paramsAt μ (a v)).M *
              bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
            * (Cc * (sideAt μ (a v)) ^ 3
                * (μ * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                      (paramsAt μ (a v)).d u + 1)
                * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :=
        mul_le_mul_of_nonneg_left hcnt (mul_nonneg hμ.le hBK)
      refine le_trans h1 ?_
      have h2 : μ * (bandK v h (paramsAt μ (a v)).M *
            bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
          * (Cc * (sideAt μ (a v)) ^ 3
              * (μ * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                    (paramsAt μ (a v)).d u + 1)
              * normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
          = Cc * (μ * (μ * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + 1))
            * ((sideAt μ (a v)) ^ 3 * (bandK v h (paramsAt μ (a v)).M *
                bandS (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d μ ^ 2))
            * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by ring
      rw [h2]
      have h3 : Cc * (μ * (μ * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + 1))
            * ((sideAt μ (a v)) ^ 3 * (bandK v h (paramsAt μ (a v)).M *
                bandS (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d μ ^ 2))
          ≤ Cc * (μ * (μ * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + 1)) * (Ka * (_root_.BoseGases.a v)) :=
        mul_le_mul_of_nonneg_left har'
          (mul_nonneg hCc (mul_nonneg hμ.le (by positivity)))
      refine le_trans (mul_le_mul_of_nonneg_right h3 hJ) (le_of_eq ?_)
      ring
    have hneg' : -((Cc * Ka) * (μ ^ 2 * (_root_.BoseGases.a v)
              * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            + μ * (_root_.BoseGases.a v))
          * normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
        ≤ -(μ * (bandK v h (paramsAt μ (a v)).M *
              bandS (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d μ ^ 2)
            * boxCountAt (sideAt μ (a v)) (paramsAt μ (a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ)) :=
      neg_le_neg hkey
    linarith [hband, hneg']
  · have hnn : 0 ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := not_lt.mp hneg
    have : 0 ≤ (Cc * Ka) * (μ ^ 2 * (_root_.BoseGases.a v)
          * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        + μ * (_root_.BoseGases.a v)) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCc hKa) hX) hJ
    linarith [hnn, this]


end Work.BoseFixB1
