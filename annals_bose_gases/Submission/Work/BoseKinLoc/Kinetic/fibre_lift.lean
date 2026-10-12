import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Kinetic.dSpace_fibre_eq
import Submission.Work.BoseKinLoc.Kinetic.fsT_bound_abs
import Submission.Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.integral_fibre_sq
import Submission.Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.momForm_le_box
import Submission.Work.BoseKinLoc.Kinetic.neuFrac_fibre_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral
import Submission.Work.BoseKinLoc.Residuals
import Submission.Work.BoseKinLoc.Word.fsT_eq_zero_of_lamBox_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.fibre_lift` — the `N`-body lifting of `lem:LocKinEn`

FS `lem:LocKinEn` (`∫_u 𝒯_u du ≤ −Δ`) is stated at the one-body level
(`Work.BoseKinLoc.KineticLocalisation`).  This file lifts it to `N` particles: for a smooth
`N`-body state `Φ` supported in the centred box `abox N ℓ`,

    `∫_u kinForm N ℓ d s εT b u Φ ≤ ∫_x Σᵢ Σ_k (∂_{i,k}Φ)²`,

i.e. the `u`-average of the localised kinetic word `Σᵢ 𝒯_u^{(i)}` is dominated by the total
kinetic energy (FS `thm:CompareBoxEnergy`'s kinetic step).

## Strategy

Write `N = n + 1`, fix the slot `i : Fin (n+1)` and let `Ψ r = liftFibre i Φ r` be the slot-`i`
fibre: `Ψ r z = Φ (kcInsN n i (z,r))`, so that the slot-`i` fibre of `Φ` at the configuration
`kcInsN n i (z,r)` is `Ψ r` (inserting `z` erases the inserted coordinate, `update_kcInsN`).
Then

* (`slotForm_eq_fibre_integral`) the slot word peels:
  `slotForm (n+1) q ℓ u i Φ = ∫_r q (Ψ r)`;
* the integrand `F(u,r) = fsT ℓ d s εT b u (Ψ r)` is jointly measurable
  (`*_fibre_aemeasurable`) and bounded by an integrable majorant
  (`fsT_bound_abs` + `momForm_le_box` + the support estimate below), so the `(u,r)` Fubini
  exchange is legitimate;
* for a.e. `r` the state `Ψ r` is smooth with compact support, so `hKin` applies to it;
* finally `∫_r dSpace (Ψ r) dr` is the total kinetic energy (`dSpace_fibre_eq`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The slot-`i` fibre of `Φ`, as a one-body state in the inserted variable `z`:
`z ↦ Φ (kcInsN n i (z,r))`.  This is `Work.BoseKinLoc.fibre (n+1) i Φ` evaluated at the
configuration `kcInsN n i (z,r)`. -/
def liftFibre {n : ℕ} (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (r : Submission.BoseGases.X n) : ℝ³ → ℝ :=
  fun z => Φ (Submission.BoseGases.kcInsN n i (z, r))

lemma liftFibre_eq_fibre {n : ℕ} (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (r : Submission.BoseGases.X n)
    (y z : ℝ³) :
    liftFibre i Φ r z = Work.BoseKinLoc.fibre (n + 1) i Φ
      (Submission.BoseGases.kcInsN n i (y, r)) z := by
  rw [liftFibre, Work.BoseKinLoc.fibre, Submission.BoseGases.update_kcInsN]

/-- The fibre is smooth. -/
lemma liftFibre_contDiff {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (r : Submission.BoseGases.X n) :
    ContDiff ℝ (⊤ : ENat) (liftFibre i Φ r) := by
  have hins : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ =>
      Submission.BoseGases.kcInsN n i (z, r)) := by
    have h1 : (fun z : ℝ³ => Submission.BoseGases.kcInsN n i (z, r))
        = Function.update (Submission.BoseGases.kcInsN n i (0, r)) i := by
      funext z
      exact Submission.BoseGases.kcInsN_update_zero i z r
    rw [h1]
    exact contDiff_update (⊤ : ENat) (Submission.BoseGases.kcInsN n i (0, r)) i
  show ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r)))
  exact hΦ.comp hins

/-- The fibre vanishes off the centred box `acube ℓ` when `Φ` is supported in `abox (n+1) ℓ`. -/
lemma liftFibre_eq_zero_of_not_mem_acube {n : ℕ} {ℓ : ℝ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ) (i : Fin (n + 1))
    {r : Submission.BoseGases.X n} {z : ℝ³} (hz : z ∉ Submission.BoseGases.acube ℓ) :
    liftFibre i Φ r z = 0 := by
  have hxabox : Submission.BoseGases.kcInsN n i (z, r)
      ∉ Submission.BoseGases.abox (n + 1) ℓ := by
    intro hmem
    have hcoord : Submission.BoseGases.kcInsN n i (z, r) i ∉ Submission.BoseGases.acube ℓ := by
      rwa [Submission.BoseGases.kc_insN_apply_same n i z r]
    exact hcoord (hmem i)
  show Φ (Submission.BoseGases.kcInsN n i (z, r)) = 0
  exact image_eq_zero_of_notMem_tsupport (fun h => hxabox (hsupp h))

/-- The `tsupport` of the fibre is contained in `acube ℓ`. -/
lemma liftFibre_tsupport_subset {n : ℕ} {ℓ : ℝ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ) (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) :
    tsupport (liftFibre i Φ r) ⊆ Submission.BoseGases.acube ℓ :=
  closure_minimal (fun z hz => by
      by_contra hzc
      exact hz (liftFibre_eq_zero_of_not_mem_acube hsupp i hzc))
    (Submission.BoseGases.acube_isClosed ℓ)

/-- The fibre is compactly supported (for `ℓ > 0`). -/
lemma liftFibre_hasCompactSupport {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ) (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) :
    HasCompactSupport (liftFibre i Φ r) :=
  IsCompact.of_isClosed_subset (Submission.BoseGases.acube_compact hℓ)
    (isClosed_tsupport _) (liftFibre_tsupport_subset hsupp i r)

/-! ## The support of `u ↦ fsT ℓ d s εT b u ψ`

`fsT u ψ` only sees the box `Λ(u) = ℓu + acube ℓ`.  If `ψ` is supported in the centred cube
`acube ℓ` then `Λ(u)` meets `acube ℓ` only for `u ∈ acube 2`, so `fsT u ψ` vanishes there.
-/

/-- The centred cube is closed under differences up to doubling of the side:
`y, w ∈ acube ℓ → y - w ∈ acube (2ℓ)`. -/
lemma mem_acube_sub {ℓ : ℝ} {y w : ℝ³}
    (hy : y ∈ Submission.BoseGases.acube ℓ) (hw : w ∈ Submission.BoseGases.acube ℓ) :
    y - w ∈ Submission.BoseGases.acube (2 * ℓ) := by
  rw [Submission.BoseGases.mem_acube_iff] at hy hw ⊢
  intro m
  have hy' := hy m
  have hw' := hw m
  rw [PiLp.sub_apply]
  rw [Set.mem_Icc] at hy' hw' ⊢
  have h2 : (2 * ℓ) / 2 = ℓ := by ring
  rw [h2]
  constructor <;> linarith [hy'.1, hy'.2, hw'.1, hw'.2]

/-- `ℓ • u ∈ acube (2ℓ)` forces `u ∈ acube 2` when `ℓ > 0`. -/
lemma mem_acube_two_of_smul_mem {ℓ : ℝ} (hℓ : 0 < ℓ) {u : ℝ³}
    (h : ℓ • u ∈ Submission.BoseGases.acube (2 * ℓ)) : u ∈ Submission.BoseGases.acube 2 := by
  rw [Submission.BoseGases.mem_acube_iff] at h ⊢
  intro m
  have hm := h m
  rw [PiLp.smul_apply, smul_eq_mul] at hm
  rw [Set.mem_Icc] at hm ⊢
  have h2 : (2 * ℓ) / 2 = ℓ := by ring
  rw [h2] at hm
  constructor <;> nlinarith [hm.1, hm.2, hℓ]

/-- If the box `Λ(u)` meets `acube ℓ` then `u ∈ acube 2`. -/
lemma mem_acube_two_of_mem_lamBox {ℓ : ℝ} (hℓ : 0 < ℓ) {u z : ℝ³}
    (hz : z ∈ Work.BoseKinLoc.lamBox ℓ u) (hz' : z ∈ Submission.BoseGases.acube ℓ) :
    u ∈ Submission.BoseGases.acube 2 := by
  have h2 : z - (z - ℓ • u) ∈ Submission.BoseGases.acube (2 * ℓ) := mem_acube_sub hz' hz
  rw [sub_sub_cancel] at h2
  exact mem_acube_two_of_smul_mem hℓ h2

/-- The localised kinetic word vanishes outside the doubled box, for a state supported in
`acube ℓ`. -/
lemma fsT_eq_zero_of_not_mem_acube_two {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {u : ℝ³}
    {ψ : ℝ³ → ℝ} (hψ : tsupport ψ ⊆ Submission.BoseGases.acube ℓ)
    (hu : u ∉ Submission.BoseGases.acube 2) :
    Work.BoseKinLoc.fsT ℓ d s εT b u ψ = 0 := by
  refine Work.BoseKinLoc.Word.fsT_eq_zero_of_lamBox_const (c := 0) hℓ u (fun z hz => ?_)
  by_contra hne
  exact hu (mem_acube_two_of_mem_lamBox hℓ hz
    (hψ (subset_tsupport ψ (Function.mem_support.mpr hne))))

theorem fibre_lift {c₀ : ℝ} (hKin : Work.BoseKinLoc.KineticLocalisation c₀) {N : ℕ}
    {ℓ d s εT b : ℝ} (hreg : Work.BoseKinLoc.KinRegime c₀ ℓ d s εT b)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N ℓ)
    (hint : MeasureTheory.Integrable (fun u : ℝ³ => Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)) :
    (∫ u : ℝ³, Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
      ≤ ∑ i : Fin N, ∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
          (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2 := by
  rcases N with _ | n
  · -- no particles: both sides vanish
    simp [Work.BoseKinLoc.kinForm]
  have hℓ : 0 < ℓ := hreg.1
  have hd : 0 < d := hreg.2.1
  have hcsΦ : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact (n + 1) hℓ)
      (isClosed_tsupport Φ) hsupp
  -- the absolute one-body bound, using the pointwise momentum bound
  obtain ⟨C, hC0, hCbd⟩ := Work.BoseKinLoc.Kinetic.fsT_bound_abs (ℓ := ℓ) (d := d) (s := s)
    (εT := εT) (b := b) hℓ hd (fun u ψ hψ hcs =>
      Work.BoseKinLoc.Kinetic.momForm_le_box hℓ hd u hψ hcs)
  -- the per-slot estimate
  have hstep : ∀ i : Fin (n + 1),
      MeasureTheory.Integrable (fun u : ℝ³ =>
          Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
        ∧ (∫ u : ℝ³, Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
            ≤ ∫ r : Submission.BoseGases.X n, Work.BSKinetic.dSpace (liftFibre i Φ r) := by
    intro i
    set F : ℝ³ → Submission.BoseGases.X n → ℝ := fun u r =>
      Work.BoseKinLoc.fsT ℓ d s εT b u (liftFibre i Φ r) with hF
    -- the peel
    have hpeel : ∀ u : ℝ³, Work.BoseKinLoc.slotForm (n + 1)
        (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ = ∫ r : Submission.BoseGases.X n, F u r := by
      intro u
      rw [Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral hℓ
        (Work.BoseKinLoc.fsT ℓ d s εT b u) u i Φ]
      rfl
    -- the majorant
    set M : Submission.BoseGases.X n → ℝ := fun r => (∫ z : ℝ³, (liftFibre i Φ r z) ^ 2)
      + ∑ k : Fin 3, ∫ z : ℝ³,
          (fderiv ℝ (liftFibre i Φ r) z (Submission.BoseGases.kcStdBasis k)) ^ 2 with hM
    have hAint : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
        ∫ z : ℝ³, (liftFibre i Φ r z) ^ 2) :=
      (Work.BoseKinLoc.Kinetic.integral_fibre_sq (n := n) hΦ hcsΦ i).1.congr
        (Filter.Eventually.of_forall (fun r => rfl))
    have hDint : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
        Work.BSKinetic.dSpace (liftFibre i Φ r)) :=
      (Work.BoseKinLoc.Kinetic.dSpace_fibre_eq (n := n) hΦ hcsΦ i).1.congr
        (Filter.Eventually.of_forall (fun r => rfl))
    have hMint : MeasureTheory.Integrable M := by
      rw [hM]
      exact hAint.add hDint
    -- joint measurability
    have hmeas : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
      have h1 := Work.BoseKinLoc.Kinetic.neuFrac_fibre_aemeasurable (ℓ := ℓ)
        (a2 := (d * ℓ) ^ (-2 : ℤ)) hℓ (by positivity) hΦ hsupp i
      have h1' : MeasureTheory.AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) q.1
            (Work.BoseKinLoc.Qfree ℓ q.1 (liftFibre i Φ q.2)))
          ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
        refine h1.congr (Filter.Eventually.of_forall (fun q => ?_))
        exact (Work.BoseKinLoc.NeuFrac.neuFrac_add_const_of_integrableSq (by positivity) q.1
          (liftFibre i Φ q.2) (-(Work.BoseKinLoc.meanU ℓ q.1 (liftFibre i Φ q.2)))
          (liftFibre_contDiff hΦ i q.2).continuous.measurable
          (Continuous.integrable_of_hasCompactSupport
            ((liftFibre_contDiff hΦ i q.2).continuous.pow 2)
            ((liftFibre_hasCompactSupport hℓ hsupp i q.2).comp_left
              (g := fun t : ℝ => t ^ 2) (by norm_num)))).symm
      have h2 := Work.BoseKinLoc.Kinetic.gapBare_fibre_aemeasurable (ℓ := ℓ) hΦ i
      have h3 := Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable (ℓ := ℓ) (d := d) hΦ i
      have h4 := Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable (ℓ := ℓ) (d := d)
        (s := s) (εT := εT) hΦ i
      have hsum : MeasureTheory.AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
          Work.BoseKinLoc.neuWord ℓ d εT q.1 (liftFibre i Φ q.2)
            + Work.BoseKinLoc.gapWord ℓ b q.1 (liftFibre i Φ q.2)
            + Work.BoseKinLoc.momWord ℓ d εT b q.1 (liftFibre i Φ q.2)
            + Work.BoseKinLoc.mainWord ℓ d s εT q.1 (liftFibre i Φ q.2))
          ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) :=
        (((h1'.const_mul ((1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ))).add
          (h2.const_mul (b * ℓ ^ (-2 : ℤ)))).add
          (h3.const_mul (b * εT * (d * ℓ) ^ (-2 : ℤ)))).add h4
      refine hsum.congr (Filter.Eventually.of_forall (fun q => ?_))
      exact (Work.BoseKinLoc.fsT_eq_sum ℓ d s εT b q.1 (liftFibre i Φ q.2)).symm
    -- the majorant is integrable
    have hind : MeasureTheory.Integrable (fun u : ℝ³ =>
        C * (Submission.BoseGases.acube 2).indicator (fun _ => (1 : ℝ)) u) := by
      refine MeasureTheory.Integrable.const_mul ?_ C
      rw [integrable_indicator_iff (Submission.BoseGases.acube_measurable 2)]
      exact integrableOn_const (by
        rw [Submission.BoseGases.acube_volume 2 (by norm_num)]
        exact ENNReal.ofReal_lt_top.ne) (by simp)
    have hGint : MeasureTheory.Integrable (fun q : ℝ³ × Submission.BoseGases.X n =>
        (C * (Submission.BoseGases.acube 2).indicator (fun _ => (1 : ℝ)) q.1) * M q.2)
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) :=
      MeasureTheory.Integrable.mul_prod hind hMint
    have hFint : MeasureTheory.Integrable (Function.uncurry F)
        ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
      refine MeasureTheory.Integrable.mono' hGint hmeas
        (Filter.Eventually.of_forall (fun q => ?_))
      obtain ⟨u, r⟩ := q
      change ‖F u r‖ ≤ (C * (Submission.BoseGases.acube 2).indicator (fun _ => (1 : ℝ)) u) * M r
      by_cases hu : u ∈ Submission.BoseGases.acube 2
      · have hb := hCbd u (liftFibre i Φ r) (liftFibre_contDiff hΦ i r)
          (liftFibre_hasCompactSupport hℓ hsupp i r)
        rw [Set.indicator_of_mem hu, mul_one]
        simpa only [hF, hM, Real.norm_eq_abs] using hb
      · rw [Set.indicator_of_notMem hu, mul_zero, zero_mul]
        rw [show F u r = 0 from Work.BoseKinLoc.Kinetic.fsT_eq_zero_of_not_mem_acube_two hℓ
          (liftFibre_tsupport_subset hsupp i r) hu, norm_zero]
    -- assemble
    have hper : ∀ᵐ r ∂(volume : Measure (Submission.BoseGases.X n)),
        MeasureTheory.Integrable (fun u : ℝ³ => F u r) :=
      ((MeasureTheory.integrable_prod_iff' hmeas).1 hFint).1
    refine ⟨hFint.integral_prod_left.congr
      (Filter.Eventually.of_forall (fun u => (hpeel u).symm)), ?_⟩
    calc (∫ u : ℝ³, Work.BoseKinLoc.slotForm (n + 1)
            (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ)
        = ∫ u : ℝ³, ∫ r : Submission.BoseGases.X n, F u r :=
          MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun u => hpeel u))
      _ = ∫ r : Submission.BoseGases.X n, ∫ u : ℝ³, F u r :=
          MeasureTheory.integral_integral_swap hFint
      _ ≤ ∫ r : Submission.BoseGases.X n, Work.BSKinetic.dSpace (liftFibre i Φ r) := by
          refine MeasureTheory.integral_mono_ae hFint.integral_prod_right hDint ?_
          filter_upwards [hper] with r hr
          exact hKin ℓ d s εT b hreg (liftFibre i Φ r)
            (liftFibre_contDiff hΦ i r) (liftFibre_hasCompactSupport hℓ hsupp i r) hr
  calc (∫ u : ℝ³, Work.BoseKinLoc.kinForm (n + 1) ℓ d s εT b u Φ)
      = ∑ i : Fin (n + 1), ∫ u : ℝ³,
          Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ := by
        simp_rw [Work.BoseKinLoc.kinForm_eq]
        exact MeasureTheory.integral_finsetSum _ (fun i _ => (hstep i).1)
    _ ≤ ∑ i : Fin (n + 1), ∫ r : Submission.BoseGases.X n,
          Work.BSKinetic.dSpace (liftFibre i Φ r) :=
        Finset.sum_le_sum (fun i _ => (hstep i).2)
    _ = ∑ i : Fin (n + 1), ∫ x : Submission.BoseGases.X (n + 1), ∑ k : Fin 3,
          (fderiv ℝ Φ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact (Work.BoseKinLoc.Kinetic.dSpace_fibre_eq (n := n) hΦ hcsΦ i).2.symm

end Work.BoseKinLoc.Kinetic
