import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.frkCore
import Submission.Work.BoseBoxFock.qCoeff_eq_kinFT_general
import Submission.Work.BoseBoxFock.qVec_eq_etaOf_of_pairing
import Submission.Work.BoseBoxFock.qVec_overlap_eq_cboxQ
import Submission.Work.BoseBoxFock.re_boxSlotSum_boxT0_le_cnPlusC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.boxSlotOf_self_re_le_fibre`

The **`τ`-row dictionary in operator form**: the box pairing of the rank-one slot
`|η_u⟩⟨η_u|` in the slot `j` with the box-restricted state `Θ = χ_Λ·Φ` is bounded by the box slot
integral of the lattice Fourier coefficient of the *fibre* `z ↦ Φ(x[j ↦ z])`.

Everything rests on the fibre structure of a first-quantised rank-one operator: on the box the
slot pairing *is* the squared modulus of the fibre component of the state along the mode, and the
Fourier coefficient of that fibre is the mode coefficient — which the hypothesis `hq` identifies
(a.e.) with the corpus mode `qVec ℓ (kmomLab ℓ N k)`.

The proof has four layers, all below:

* `peel_box_fibre` — the box-restricted fibre peel (`abox (p+1) ℓ ≃ acube ℓ × abox p ℓ` along
  `kcInsN p j`), replacing the `xⱼ`-integral by the volume `ℓ³`;
* `boxSlotPairing_congr` — the pairing depends only on the a.e. class of the mode (the `hq`
  replacement of `etaOf e (f k)` by the concrete mode `c · qVec ℓ (kmomLab ℓ N k)`);
* `lhsFibrePair` — the operator side: the pairing of `Θ` with the rank-one slot equals the box
  integral of the squared fibre mode;
* `qCoeff_eq_kinFT_general` (imported) — the per-fibre dictionary, no support hypothesis.
-/

/-- `f a` against the `0/1`-indicator of `s`, integrated, is the set integral of `f` over `s`. -/
private lemma integral_indicator_mul_one {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : α → ℂ) :
    (∫ a, f a * ((s.indicator (fun _ => (1:ℝ)) a : ℝ) : ℂ) ∂μ) = ∫ a in s, f a ∂μ := by
  rw [← MeasureTheory.integral_indicator hs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  by_cases ha : a ∈ s
  · simp [Set.indicator_of_mem ha]
  · simp [Set.indicator_of_notMem ha]

/-- **Box-restricted fibre peel.**  For `ℓ > 0`, the `(p+1)`-body box integral of an arbitrary
function of *the `j`-th fibre only*, weighted by the box indicator `indU ℓ 0 (x j)`, peels off the
`j`-th coordinate: under the measure-preserving equivalence `kcInsN p j` the box `abox (p+1) ℓ`
is the product `acube ℓ × abox p ℓ`, the fibre of the re-inserted configuration is
`z ↦ Φ (kcInsN p j (z, r))`, and the `xⱼ`-integral contributes the volume `ℓ³`. -/
private theorem peel_box_fibre {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin (p+1))
    (F : (E3 → ℝ) → ℝ) (Φ : Submission.BoseGases.X (p+1) → ℝ) :
    (∫ x in Submission.BoseGases.abox (p+1) ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * F (Work.BoseKinLoc.fibre (p+1) j Φ x))
      = ℓ ^ 3 * ∫ r in Submission.BoseGases.abox p ℓ,
          F (fun z => Φ (Submission.BoseGases.kcInsN p j (z, r))) := by
  classical
  have hInd : ∀ t : E3, Work.BoseKinLoc.indU ℓ 0 t
      = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) t := by
    intro t
    have hset : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
      ext x
      simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
    rw [Work.BoseKinLoc.indU, hset]
  have hmem : ∀ (t : E3) (r : Submission.BoseGases.X p),
      Submission.BoseGases.kcInsN p j (t,r) ∈ Submission.BoseGases.abox (p+1) ℓ
        ↔ (t ∈ Submission.BoseGases.acube ℓ ∧ r ∈ Submission.BoseGases.abox p ℓ) := by
    intro t r
    rw [Submission.BoseGases.mem_abox_iff, Submission.BoseGases.mem_abox_iff]
    constructor
    · intro h
      exact ⟨by simpa [Submission.BoseGases.kc_insN_apply_same] using h j,
        fun i => by simpa [Submission.BoseGases.kc_insN_apply_succ] using h (j.succAbove i)⟩
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = j
      · rw [hi]; simpa [Submission.BoseGases.kc_insN_apply_same] using h1
      · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
        simpa [Submission.BoseGases.kc_insN_apply_succ] using h2 i'
  have hpt : ∀ (t : E3) (r : Submission.BoseGases.X p),
      (Submission.BoseGases.abox (p+1) ℓ).indicator
          (fun x => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) (x j)
            * F (Work.BoseKinLoc.fibre (p+1) j Φ x))
          (Submission.BoseGases.kcInsN p j (t,r))
        = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) t
          * ((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r
              * F (fun z => Φ (Submission.BoseGases.kcInsN p j (z,r)))) := by
    intro t r
    have hfib : Work.BoseKinLoc.fibre (p+1) j Φ (Submission.BoseGases.kcInsN p j (t,r))
        = fun z => Φ (Submission.BoseGases.kcInsN p j (z,r)) := by
      funext z
      show Φ (Function.update (Submission.BoseGases.kcInsN p j (t,r)) j z)
        = Φ (Submission.BoseGases.kcInsN p j (z,r))
      rw [Submission.BoseGases.update_kcInsN]
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply,
      Submission.BoseGases.kc_insN_apply_same, hfib]
    by_cases ht : t ∈ Submission.BoseGases.acube ℓ
    · by_cases hr : r ∈ Submission.BoseGases.abox p ℓ
      · simp only [if_pos ((hmem t r).mpr ⟨ht, hr⟩), if_pos ht, Set.indicator_of_mem hr,
          one_mul, mul_one]
      · simp only [if_neg (fun h => hr ((hmem t r).mp h).2), if_pos ht, Set.indicator_of_notMem hr,
          mul_zero, zero_mul]
    · simp only [if_neg (fun h => ht ((hmem t r).mp h).1), if_neg ht, zero_mul]
  rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable (p+1) ℓ)
    (fun x _ => by rw [hInd])]
  rw [(MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable (p+1) ℓ)).symm]
  rw [← (Submission.BoseGases.kc_mp_insN p j).integral_comp'
    (fun x : Submission.BoseGases.X (p+1) => (Submission.BoseGases.abox (p+1) ℓ).indicator
      (fun x => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) (x j)
        * F (Work.BoseKinLoc.fibre (p+1) j Φ x)) x)]
  rw [show (fun q : E3 × Submission.BoseGases.X p =>
        (Submission.BoseGases.abox (p+1) ℓ).indicator
          (fun x => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) (x j)
            * F (Work.BoseKinLoc.fibre (p+1) j Φ x))
          (Submission.BoseGases.kcInsN p j q))
      = fun q : E3 × Submission.BoseGases.X p =>
          (Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) q.1
            * ((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) q.2
                * F (fun z => Φ (Submission.BoseGases.kcInsN p j (z,q.2)))) from by
      funext q; exact hpt q.1 q.2]
  rw [MeasureTheory.Measure.volume_eq_prod E3 (Submission.BoseGases.X p)]
  rw [MeasureTheory.integral_prod_mul
    (fun t : E3 => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) t)
    (fun r : Submission.BoseGases.X p => (Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r
      * F (fun z => Φ (Submission.BoseGases.kcInsN p j (z,r))))]
  rw [show (∫ t : E3, (Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) t) = ℓ ^ 3 from by
    rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ),
      MeasureTheory.setIntegral_const, MeasureTheory.Measure.real,
      Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
    simp]
  refine congrArg (fun x => ℓ ^ 3 * x) ?_
  rw [← MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable p ℓ)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ Submission.BoseGases.abox p ℓ
  · simp only [Set.indicator_of_mem hr, one_mul]
  · simp only [Set.indicator_of_notMem hr, zero_mul]

/-- **The pairing depends only on the a.e. class of the mode.**  For `u =ᵐ u'` on `ℝ³` and
arbitrary `Θ`, the box pairing `∫_{x ∈ abox n ℓ} conj(Θ x)·(u(xⱼ)·∫_z conj(u z)·Θ(x[j↦z]))` is
unchanged.  (The outer `x`-integrand is compared a.e. — the coordinate projection
`X n → ℝ³` is quasi-measure-preserving for the restricted measure `volume ↾ abox n ℓ`.) -/
private theorem boxSlotPairing_congr {n : ℕ} {ℓ : ℝ} {u u' : E3 → ℂ}
    (h : u =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure E3)] u')
    (Θ : Submission.BoseGases.X n → ℂ) (j : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ, star (Θ x) *
        (u (x j) * ∫ z, star (u z) * Θ (Function.update x j z))).re
      = (∫ x in Submission.BoseGases.abox n ℓ, star (Θ x) *
        (u' (x j) * ∫ z, star (u' z) * Θ (Function.update x j z))).re := by
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun x : Submission.BoseGases.X n => x j)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))
      (volume : Measure E3) := by
    refine ⟨measurable_pi_apply j, ?_⟩
    rw [Submission.BoseGases.restrict_abox_eq_pi, MeasureTheory.Measure.pi_map_eval]
    exact MeasureTheory.Measure.AbsolutelyContinuous.smul_left
      (MeasureTheory.Measure.absolutelyContinuous_of_le MeasureTheory.Measure.restrict_le_self) _
  refine congrArg Complex.re ?_
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hqmp.ae_eq h] with x hx
  have hx' : u (x j) = u' (x j) := hx
  have hz : (∫ z, star (u z) * Θ (Function.update x j z))
      = ∫ z, star (u' z) * Θ (Function.update x j z) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h] with z hz
    rw [hz]
  rw [hz, hx']

/-- **The operator side of the `τ`-row dictionary.**  For a box state `Θ = χ_Λ·Φ` (with `Φ`
smooth) the real part of the box pairing of the rank-one slot `|u⟩⟨u|` in the slot `j` with `Θ`
is the `abox p ℓ`-integral of the squared fibre mode
`∫_{z ∈ acube ℓ} conj(u z)·Φ(x[j↦z])`.  (Equality, not merely `≤`.) -/
private theorem lhsFibrePair {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin (p+1))
    {Φ : Submission.BoseGases.X (p+1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {u : E3 → ℂ} (hum : Measurable u) (hub : ∃ D, ∀ z, ‖u z‖ ≤ D)
    (huc : HasCompactSupport u) :
    (∫ x in Submission.BoseGases.abox (p+1) ℓ, star (boxRestrictC ℓ Φ x) *
        (u (x j) * ∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z))).re
      = ∫ r in Submission.BoseGases.abox p ℓ,
          ‖∫ z in Submission.BoseGases.acube ℓ,
            star (u z) * ((Φ (Submission.BoseGases.kcInsN p j (z, r)) : ℝ) : ℂ)‖ ^ 2 := by
  classical
  obtain ⟨D, hD0, hDb⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ z : E3, ‖u z‖ ≤ D := by
    obtain ⟨D, hD⟩ := hub
    exact ⟨max D 0, le_max_right D 0, fun z => (hD z).trans (le_max_left D 0)⟩
  have hAc_lt : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Submission.BoseGases.acube_lt_top ℓ hℓ.le
  have hAB_lt : (volume : Measure (Submission.BoseGases.X (p+1)))
      (Submission.BoseGases.abox (p+1) ℓ) < ⊤ :=
    Submission.BoseGases.abox_lt_top (p+1) ℓ hℓ.le
  have hABp_lt : (volume : Measure (Submission.BoseGases.X p)) (Submission.BoseGases.abox p ℓ) < ⊤ :=
    Submission.BoseGases.abox_lt_top p ℓ hℓ.le
  obtain ⟨M, hM0, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Submission.BoseGases.abox (p+1) ℓ, ‖Φ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (Submission.BoseGases.abox_compact (p+1) hℓ).exists_bound_of_continuousOn
      hΦ.continuous.continuousOn
    exact ⟨max M 0, le_max_right M 0, fun x hx => (hM x hx).trans (le_max_left M 0)⟩
  have hΘb : ∀ x : Submission.BoseGases.X (p+1), ‖boxRestrictC ℓ Φ x‖ ≤ M := by
    intro x
    rw [boxRestrictC, norm_mul, Complex.norm_real, Complex.norm_real]
    by_cases hx : x ∈ Submission.BoseGases.abox (p+1) ℓ
    · rw [Set.indicator_of_mem hx]
      simpa [Real.norm_eq_abs] using hMb x hx
    · rw [Set.indicator_of_notMem hx, norm_zero, mul_zero]
      exact hM0
  have hmem : ∀ (t : E3) (r : Submission.BoseGases.X p),
      Submission.BoseGases.kcInsN p j (t,r) ∈ Submission.BoseGases.abox (p+1) ℓ
        ↔ (t ∈ Submission.BoseGases.acube ℓ ∧ r ∈ Submission.BoseGases.abox p ℓ) := by
    intro t r
    rw [Submission.BoseGases.mem_abox_iff, Submission.BoseGases.mem_abox_iff]
    constructor
    · intro h
      exact ⟨by simpa [Submission.BoseGases.kc_insN_apply_same] using h j,
        fun i => by simpa [Submission.BoseGases.kc_insN_apply_succ] using h (j.succAbove i)⟩
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = j
      · rw [hi]; simpa [Submission.BoseGases.kc_insN_apply_same] using h1
      · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
        simpa [Submission.BoseGases.kc_insN_apply_succ] using h2 i'
  have hsplitC : ∀ (t : E3) (r : Submission.BoseGases.X p),
      (((Submission.BoseGases.abox (p+1) ℓ).indicator (fun _ => (1:ℝ))
          (Submission.BoseGases.kcInsN p j (t,r)) : ℝ) : ℂ)
        = (((Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) t : ℝ) : ℂ)
          * (((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ) := by
    intro t r
    rw [← Complex.ofReal_mul, Complex.ofReal_inj]
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    by_cases ht : t ∈ Submission.BoseGases.acube ℓ
    · by_cases hr : r ∈ Submission.BoseGases.abox p ℓ
      · rw [if_pos (hmem t r |>.mpr ⟨ht, hr⟩), if_pos ht, if_pos hr, mul_one]
      · rw [if_neg (fun h => hr ((hmem t r).mp h).2), if_pos ht, if_neg hr, mul_zero]
    · rw [if_neg (fun h => ht ((hmem t r).mp h).1), if_neg ht, zero_mul]
  have hinner : ∀ x ∈ Submission.BoseGases.abox (p+1) ℓ,
      ‖∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z)‖ ≤ D * M * ℓ ^ 3 := by
    intro x hx
    have hsupp : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ →
        star (u z) * boxRestrictC ℓ Φ (Function.update x j z) = 0 := by
      intro z hz
      have hnot : Function.update x j z ∉ Submission.BoseGases.abox (p+1) ℓ := by
        intro hcon
        exact hz (by have h := hcon j; rwa [Function.update_self] at h)
      rw [boxRestrictC, Set.indicator_of_notMem hnot]
      simp
    have hEq : (∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z))
        = ∫ z in Submission.BoseGases.acube ℓ,
            star (u z) * boxRestrictC ℓ Φ (Function.update x j z) := by
      rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by
        by_cases hz : z ∈ Submission.BoseGases.acube ℓ
        · simp only [Set.indicator_of_mem hz]
        · simp only [Set.indicator_of_notMem hz]
          exact hsupp z hz)
    rw [hEq]
    have h1 : ‖∫ z in Submission.BoseGases.acube ℓ,
          star (u z) * boxRestrictC ℓ Φ (Function.update x j z)‖
        ≤ (D * M) * (volume : Measure E3).real (Submission.BoseGases.acube ℓ) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (f := fun z : E3 => star (u z) * boxRestrictC ℓ Φ (Function.update x j z))
        (C := D * M) hAc_lt
        (fun z hz => by
          rw [norm_mul, norm_star]
          exact mul_le_mul (hDb z) (hΘb _) (norm_nonneg _) hD0)
    refine h1.trans_eq ?_
    rw [MeasureTheory.Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hΘmeas : Measurable (fun x : Submission.BoseGases.X (p+1) => boxRestrictC ℓ Φ x) := by
    simp only [boxRestrictC]
    exact (Complex.continuous_ofReal.measurable.comp hΦ.continuous.measurable).mul
      (Complex.continuous_ofReal.measurable.comp
        (measurable_const.indicator (Submission.BoseGases.abox_measurable (p+1) ℓ)))
  have hupd : Measurable fun q : Submission.BoseGases.X (p+1) × E3 => Function.update q.1 j q.2 := by
    rw [measurable_pi_iff]
    intro i
    by_cases hi : i = j
    · rw [hi]
      have huu : (fun q : Submission.BoseGases.X (p+1) × E3 => Function.update q.1 j q.2 j)
          = fun q => q.2 := by
        funext q; exact Function.update_self j q.2 q.1
      rw [huu]
      exact measurable_snd
    · have huu : (fun q : Submission.BoseGases.X (p+1) × E3 => Function.update q.1 j q.2 i)
          = fun q => q.1 i := by
        funext q; exact Function.update_of_ne hi q.2 q.1
      rw [huu]
      exact (measurable_pi_apply i).comp measurable_fst
  have hIntmeas : Measurable (fun x : Submission.BoseGases.X (p+1) =>
      ∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z)) := by
    have h1 : Measurable fun q : Submission.BoseGases.X (p+1) × E3 => star (u q.2) :=
      (Complex.continuous_conj.measurable.comp hum).comp measurable_snd
    have h2 : Measurable fun q : Submission.BoseGases.X (p+1) × E3 =>
        boxRestrictC ℓ Φ (Function.update q.1 j q.2) := hΘmeas.comp hupd
    have huncurry : StronglyMeasurable (fun q : Submission.BoseGases.X (p+1) × E3 =>
        star (u q.2) * boxRestrictC ℓ Φ (Function.update q.1 j q.2)) :=
      (h1.mul h2).stronglyMeasurable
    exact (MeasureTheory.StronglyMeasurable.integral_prod_right (ν := volume)
      (f := Function.curry (fun q : Submission.BoseGases.X (p+1) × E3 =>
        star (u q.2) * boxRestrictC ℓ Φ (Function.update q.1 j q.2)))
      (by simpa only [Function.uncurry_curry] using huncurry)).measurable
  have hFmeas : AEStronglyMeasurable (fun x : Submission.BoseGases.X (p+1) =>
      star (boxRestrictC ℓ Φ x) * (u (x j) * ∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z)))
      (volume : Measure (Submission.BoseGases.X (p+1))) :=
    ((Complex.continuous_conj.measurable.comp hΘmeas).mul
      ((hum.comp (measurable_pi_apply j)).mul hIntmeas)).aestronglyMeasurable
  have hFbd : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X (p+1))).restrict
        (Submission.BoseGases.abox (p+1) ℓ)),
      ‖star (boxRestrictC ℓ Φ x) * (u (x j) * ∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z))‖
        ≤ M * D * (D * M * ℓ ^ 3) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable (p+1) ℓ)]
      with x hx
    rw [norm_mul, norm_mul, norm_star]
    have h1 : ‖u (x j)‖ * ‖∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z)‖
        ≤ D * (D * M * ℓ ^ 3) :=
      mul_le_mul (hDb _) (hinner x hx) (norm_nonneg _) hD0
    have h2 : ‖boxRestrictC ℓ Φ x‖
          * (‖u (x j)‖ * ‖∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z)‖)
        ≤ M * (D * (D * M * ℓ ^ 3)) :=
      mul_le_mul (hΘb x) h1 (by positivity) hM0
    linarith
  have hInt : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (p+1) =>
      star (boxRestrictC ℓ Φ x) * (u (x j) * ∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z)))
      (Submission.BoseGases.abox (p+1) ℓ) volume :=
    MeasureTheory.IntegrableOn.of_bound hAB_lt
      (hFmeas.mono_measure MeasureTheory.Measure.restrict_le_self) (M * D * (D * M * ℓ ^ 3)) hFbd
  have hL := Submission.BoseGases.abox_integral_peel_gen (n := p) (ℓ := ℓ) (E := ℂ) j
      (fun x : Submission.BoseGases.X (p+1) => star (boxRestrictC ℓ Φ x) *
        (u (x j) * ∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z))) hInt
  let Z : Submission.BoseGases.X p → ℂ := fun r =>
      ∫ z, star (u z) * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ)
        * (((Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ)
  have hZeq : ∀ r : Submission.BoseGases.X p,
      Z r = ∫ z in Submission.BoseGases.acube ℓ,
        star (u z) * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ) :=
    fun r => integral_indicator_mul_one (Submission.BoseGases.acube_measurable ℓ)
      (fun z => star (u z) * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ))
  have hZinner : ∀ (y : E3) (r : Submission.BoseGases.X p),
      (∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update (Submission.BoseGases.kcInsN p j (y,r)) j z))
        = (((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ) * Z r := by
    intro y r
    rw [show (∫ z, star (u z) * boxRestrictC ℓ Φ
            (Function.update (Submission.BoseGases.kcInsN p j (y,r)) j z))
          = ∫ z, star (u z) * boxRestrictC ℓ Φ (Submission.BoseGases.kcInsN p j (z,r)) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by
          show star (u z) * boxRestrictC ℓ Φ (Function.update (Submission.BoseGases.kcInsN p j (y,r)) j z)
            = star (u z) * boxRestrictC ℓ Φ (Submission.BoseGases.kcInsN p j (z,r))
          rw [Submission.BoseGases.update_kcInsN])]
    have h1 : (∫ z, star (u z) * boxRestrictC ℓ Φ (Submission.BoseGases.kcInsN p j (z,r)))
        = ∫ z, (((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ)
            * ((((Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ) * star (u z)
                * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show star (u z) * boxRestrictC ℓ Φ (Submission.BoseGases.kcInsN p j (z,r)) = _
      rw [boxRestrictC, hsplitC z r]
      ring
    rw [h1, MeasureTheory.integral_const_mul, hZeq r]
    congr 1
    rw [show (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) z : ℝ) : ℂ)
            * star (u z) * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ))
          = fun z : E3 => (Submission.BoseGases.acube ℓ).indicator
              (fun z => star (u z) * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ)) z from by
        funext z
        by_cases hz : z ∈ Submission.BoseGases.acube ℓ
        · simp only [Set.indicator_of_mem hz, Complex.ofReal_one, one_mul]
        · simp only [Set.indicator_of_notMem hz, Complex.ofReal_zero, zero_mul],
        MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  have hconjZ : ∀ r : Submission.BoseGases.X p,
      (starRingEnd ℂ) (Z r) = ∫ z in Submission.BoseGases.acube ℓ,
        ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ) * u z := by
    intro r
    rw [hZeq r]
    rw [← integral_conj]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) (fun z hz => ?_)
    simp
    ring
  have hpt : ∀ r : Submission.BoseGases.X p,
      (∫ y in Submission.BoseGases.acube ℓ,
          star (boxRestrictC ℓ Φ (Submission.BoseGases.kcInsN p j (y,r))) *
            (u ((Submission.BoseGases.kcInsN p j (y,r)) j) *
              ∫ z, star (u z) * boxRestrictC ℓ Φ
                (Function.update (Submission.BoseGases.kcInsN p j (y,r)) j z)))
        = ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r) * ‖Z r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    have hrw : (((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ))
        * (((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ))
        = ((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) := by
      by_cases hr : r ∈ Submission.BoseGases.abox p ℓ
      · rw [Set.indicator_of_mem hr, mul_one]
      · rw [Set.indicator_of_notMem hr, zero_mul]
    have harith : (starRingEnd ℂ) (Z r)
          * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ)
            * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ) * Z r))
        = ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r) * ‖Z r‖ ^ 2 : ℝ) : ℂ) := by
      have h1 : (starRingEnd ℂ) (Z r)
            * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ)
              * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ) * Z r))
          = ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ)
              * (((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ))
            * ((starRingEnd ℂ) (Z r) * Z r) := by ring
      rw [h1, ← Complex.ofReal_mul, hrw, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
        ← Complex.ofReal_mul]
    calc (∫ y in Submission.BoseGases.acube ℓ,
          star (boxRestrictC ℓ Φ (Submission.BoseGases.kcInsN p j (y,r))) *
            (u ((Submission.BoseGases.kcInsN p j (y,r)) j) *
              ∫ z, star (u z) * boxRestrictC ℓ Φ
                (Function.update (Submission.BoseGases.kcInsN p j (y,r)) j z)))
        = ∫ y in Submission.BoseGases.acube ℓ,
            ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ)
              * ((Φ (Submission.BoseGases.kcInsN p j (y,r)) : ℝ) : ℂ) * u y
              * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ) * Z r)) := by
          refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
            (fun y hy => ?_)
          rw [hZinner y r, Submission.BoseGases.kc_insN_apply_same]
          rw [boxRestrictC, hsplitC y r]
          rw [Set.indicator_of_mem hy]
          simp
          ring
      _ = (∫ y in Submission.BoseGases.acube ℓ,
              ((Φ (Submission.BoseGases.kcInsN p j (y,r)) : ℝ) : ℂ) * u y)
            * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ)
              * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ) * Z r)) := by
          rw [show (fun y : E3 => (((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ)
                  * ((Φ (Submission.BoseGases.kcInsN p j (y,r)) : ℝ) : ℂ) * u y
                  * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ) * Z r))
                = fun y : E3 => (((Φ (Submission.BoseGases.kcInsN p j (y,r)) : ℝ) : ℂ) * u y)
                  * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ)
                    * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ) * Z r)) from by
              funext y; ring,
            MeasureTheory.integral_mul_const]
      _ = (starRingEnd ℂ) (Z r)
            * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ)
              * ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r : ℝ) : ℂ) * Z r)) := by
          rw [← hconjZ r]
      _ = ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r) * ‖Z r‖ ^ 2 : ℝ) : ℂ) := harith
  have hZb : ∀ r ∈ Submission.BoseGases.abox p ℓ, ‖Z r‖ ≤ D * M * ℓ ^ 3 := by
    intro r hr
    rw [hZeq r]
    have h1 : ‖∫ z in Submission.BoseGases.acube ℓ,
          star (u z) * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ)‖
        ≤ (D * M) * (volume : Measure E3).real (Submission.BoseGases.acube ℓ) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (f := fun z : E3 => star (u z) * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ))
        (C := D * M) hAc_lt
        (fun z hz => by
          rw [norm_mul, norm_star, Complex.norm_real]
          exact mul_le_mul (hDb z) (hMb _ ((hmem z r).mpr ⟨hz, hr⟩)) (norm_nonneg _) hD0)
    refine h1.trans_eq ?_
    rw [MeasureTheory.Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hZmeas : StronglyMeasurable Z := by
    have hjoint : StronglyMeasurable (fun q : Submission.BoseGases.X p × E3 =>
        star (u q.2) * ((Φ (Submission.BoseGases.kcInsN p j (q.2, q.1)) : ℝ) : ℂ)
          * (((Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) q.2 : ℝ) : ℂ)) := by
      have h1 : Measurable fun q : Submission.BoseGases.X p × E3 => star (u q.2) :=
        (Complex.continuous_conj.measurable.comp hum).comp measurable_snd
      have h2 : Measurable fun q : Submission.BoseGases.X p × E3 =>
          ((Φ (Submission.BoseGases.kcInsN p j (q.2, q.1)) : ℝ) : ℂ) :=
        Complex.continuous_ofReal.measurable.comp (hΦ.continuous.measurable.comp
          ((MeasurableEquiv.measurable (Submission.BoseGases.kcInsN p j)).comp measurable_swap))
      have h3 : Measurable fun q : Submission.BoseGases.X p × E3 =>
          (((Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) q.2 : ℝ) : ℂ) :=
        Complex.continuous_ofReal.measurable.comp
          ((measurable_const.indicator (Submission.BoseGases.acube_measurable ℓ)).comp measurable_snd)
      exact ((h1.mul h2).mul h3).stronglyMeasurable
    exact MeasureTheory.StronglyMeasurable.integral_prod_right (ν := volume)
      (f := Function.curry (fun q : Submission.BoseGases.X p × E3 =>
        star (u q.2) * ((Φ (Submission.BoseGases.kcInsN p j (q.2, q.1)) : ℝ) : ℂ)
          * (((Submission.BoseGases.acube ℓ).indicator (fun _ => (1:ℝ)) q.2 : ℝ) : ℂ)))
      (by simpa only [Function.uncurry_curry] using hjoint)
  have hZb' : ∀ᵐ r ∂((volume : Measure (Submission.BoseGases.X p)).restrict
        (Submission.BoseGases.abox p ℓ)),
      ‖(((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r) * ‖Z r‖ ^ 2)‖
        ≤ (D * M * ℓ ^ 3) ^ 2 := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable p ℓ)]
      with r hr
    rw [Real.norm_eq_abs, Set.indicator_of_mem hr, one_mul, abs_of_nonneg (sq_nonneg _)]
    have h1 : ‖Z r‖ ≤ D * M * ℓ ^ 3 := hZb r hr
    have h2 : 0 ≤ D * M * ℓ ^ 3 := by positivity
    nlinarith [h1, norm_nonneg (Z r), h2]
  have hZint : MeasureTheory.Integrable
      (fun r : Submission.BoseGases.X p =>
        (((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r) * ‖Z r‖ ^ 2))
      ((volume : Measure (Submission.BoseGases.X p)).restrict (Submission.BoseGases.abox p ℓ)) := by
    haveI : MeasureTheory.IsFiniteMeasure
        ((volume : Measure (Submission.BoseGases.X p)).restrict (Submission.BoseGases.abox p ℓ)) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hABp_lt⟩
    refine MeasureTheory.Integrable.of_bound ?_ _ hZb'
    exact ((measurable_const.indicator (Submission.BoseGases.abox_measurable p ℓ)).mul
      (hZmeas.measurable.norm.pow_const 2)).aestronglyMeasurable
  have hfin : (∫ x in Submission.BoseGases.abox (p+1) ℓ, star (boxRestrictC ℓ Φ x) *
        (u (x j) * ∫ z, star (u z) * boxRestrictC ℓ Φ (Function.update x j z)))
      = ((∫ r in Submission.BoseGases.abox p ℓ,
          (((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r) * ‖Z r‖ ^ 2) : ℝ) : ℂ) := by
    rw [hL]
    rw [show (∫ r in Submission.BoseGases.abox p ℓ, ∫ y in Submission.BoseGases.acube ℓ,
            star (boxRestrictC ℓ Φ (Submission.BoseGases.kcInsN p j (y,r))) *
              (u ((Submission.BoseGases.kcInsN p j (y,r)) j) *
                ∫ z, star (u z) * boxRestrictC ℓ Φ
                  (Function.update (Submission.BoseGases.kcInsN p j (y,r)) j z)))
          = ∫ r in Submission.BoseGases.abox p ℓ,
              ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r) * ‖Z r‖ ^ 2 : ℝ) : ℂ) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [show (fun r : Submission.BoseGases.X p =>
            ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r) * ‖Z r‖ ^ 2 : ℝ) : ℂ))
          = fun r : Submission.BoseGases.X p => Complex.ofRealCLM
              ((((Submission.BoseGases.abox p ℓ).indicator (fun _ => (1:ℝ)) r) * ‖Z r‖ ^ 2)) from rfl]
    rw [ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hZint]
    rfl
  rw [hfin, Complex.ofReal_re]
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable p ℓ)
    (fun r hr => ?_)
  rw [Set.indicator_of_mem hr, one_mul, hZeq r]

/-- The tau-row dictionary in operator form: the box pairing of the rank-one slot with the
box-restricted state is bounded by the box slot integral of the lattice Fourier coefficient of the
fibre (equality is expected to hold). -/
theorem boxSlotOf_self_re_le_fibre {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {N : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (f : Work.BoseBoxFock.Lab N → Fin m → ℝ)
    (hq : ∀ k : Work.BoseBoxFock.Lab N,
      Work.BoseK15.corpusBox.qVec ℓ (Work.BoseBoxFock.kmomLab ℓ N k)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))] fun x =>
        ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e (f k) x)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (j : Fin n) (k : Work.BoseBoxFock.Lab N) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        star ((Work.BoseBoxFock.boxRestrictC ℓ Φ) x) *
          Work.BoseDict.boxSlotOf e (f k) (f k) j (Work.BoseBoxFock.boxRestrictC ℓ Φ) x).re
      ≤ (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j) *
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2) := by
  classical
  rcases n with _ | p
  · exact j.elim0
  · set κ : E3 := Work.BoseBoxFock.kmomLab ℓ N k with hκ
    set c : ℂ := (((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ) : ℂ) with hc
    -- ## 1. the concrete mode `c · qVec ℓ κ` is a.e. the model mode `etaOf e (f k)`
    have hsqrt_ne : (Real.sqrt (ℓ ^ 3) : ℝ) ≠ 0 := by positivity
    have hcc : c * ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) = 1 := by
      rw [hc, ← Complex.ofReal_mul, inv_mul_cancel₀ hsqrt_ne, Complex.ofReal_one]
    have hηae : (fun z : E3 => c * Work.BoseK15.corpusBox.qVec ℓ κ z)
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure E3)] Work.BoseDict.etaOf e (f k) := by
      filter_upwards [hq k] with z hz
      have hz' : Work.BoseK15.corpusBox.qVec ℓ κ z
          = ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e (f k) z := hz
      rw [hz', ← mul_assoc, hcc, one_mul]
    -- ## 2. the concrete mode is measurable, bounded and compactly supported
    have hexp1 : ∀ (x : ℝ), ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
      intro x
      rw [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      simp
    have hqVec_meas : Measurable (Work.BoseK15.corpusBox.qVec ℓ κ) := by
      have h1 : Measurable (Work.BoseK15.corpusBox.modeVec ℓ κ) := by
        rw [show Work.BoseK15.corpusBox.modeVec ℓ κ = fun z : E3 =>
            Complex.exp (Complex.I * ((inner ℝ κ z : ℝ) : ℂ))
              * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
          from funext fun z => Work.BoseB4.BoxData.modeVec_apply _ _ _ _]
        exact (Complex.continuous_exp.measurable.comp
          (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
            (continuous_const.inner continuous_id).measurable))).mul
          (Complex.continuous_ofReal.measurable.comp (Work.BoseB4.BoxData.chiLam_cont _ ℓ).measurable)
      have h2 : Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
        rw [show Work.BoseK15.corpusBox.thetaFun ℓ
            = (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1:ℂ)) from
          funext fun z => by rw [Work.BoseB4.BoxData.thetaFun_apply]; rfl]
        exact measurable_const.indicator (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)
      rw [show Work.BoseK15.corpusBox.qVec ℓ κ = fun z : E3 =>
          Work.BoseK15.corpusBox.modeVec ℓ κ z
            - ((Work.BoseK15.corpusBox.hatChi (ℓ • κ) : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z
        from funext fun z => Work.BoseB4.BoxData.qVec_apply _ _ _ _]
      exact h1.sub (measurable_const.mul h2)
    have hηmeas : Measurable (fun z : E3 => c * Work.BoseK15.corpusBox.qVec ℓ κ z) :=
      measurable_const.mul hqVec_meas
    have hχbd : ∀ z : E3, |Work.BoseK15.corpusBox.chiLam ℓ z| ≤ Submission.BoseGases.chiSupAbs := by
      intro z
      rw [show Work.BoseK15.corpusBox.chiLam ℓ z = Submission.BoseGases.chiScale ℓ z from rfl]
      exact Submission.BoseGases.chiScale_abs_le_sup ℓ z
    have hηbd : ∃ D : ℝ, ∀ z : E3, ‖c * Work.BoseK15.corpusBox.qVec ℓ κ z‖ ≤ D := by
      refine ⟨‖c‖ * (Submission.BoseGases.chiSupAbs + |Work.BoseK15.corpusBox.hatChi (ℓ • κ)|),
        fun z => ?_⟩
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [show Work.BoseK15.corpusBox.qVec ℓ κ z
          = Work.BoseK15.corpusBox.modeVec ℓ κ z
            - ((Work.BoseK15.corpusBox.hatChi (ℓ • κ) : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z
        from Work.BoseB4.BoxData.qVec_apply _ _ _ _]
      have hθ1 : ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ ≤ 1 := by
        by_cases h : z ∈ Work.BoseK15.corpusBox.boxL ℓ
        · rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos h]; norm_num
        · rw [Work.BoseB4.BoxData.thetaFun_apply, if_neg h]; norm_num
      calc ‖Work.BoseK15.corpusBox.modeVec ℓ κ z
            - ((Work.BoseK15.corpusBox.hatChi (ℓ • κ) : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z‖
          ≤ ‖Work.BoseK15.corpusBox.modeVec ℓ κ z‖
            + ‖((Work.BoseK15.corpusBox.hatChi (ℓ • κ) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ z‖ := norm_sub_le _ _
        _ = |Work.BoseK15.corpusBox.chiLam ℓ z|
            + |Work.BoseK15.corpusBox.hatChi (ℓ • κ)| * ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ := by
            rw [show Work.BoseK15.corpusBox.modeVec ℓ κ z
                = Complex.exp (Complex.I * ((inner ℝ κ z : ℝ) : ℂ))
                  * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
              from Work.BoseB4.BoxData.modeVec_apply _ _ _ _, norm_mul, norm_mul, hexp1,
              Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, one_mul]
        _ ≤ Submission.BoseGases.chiSupAbs
            + |Work.BoseK15.corpusBox.hatChi (ℓ • κ)| * 1 := by
            refine add_le_add (hχbd z) (mul_le_mul_of_nonneg_left hθ1 (abs_nonneg _))
        _ = Submission.BoseGases.chiSupAbs + |Work.BoseK15.corpusBox.hatChi (ℓ • κ)| := by ring
    have hηcs : HasCompactSupport (fun z : E3 => c * Work.BoseK15.corpusBox.qVec ℓ κ z) := by
      refine (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).of_isClosed_subset
        (isClosed_tsupport _)
        (closure_minimal ?_ (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).isClosed)
      intro z hz
      exact support_qVec_subset hℓ κ (fun h0 => hz (by simp only [h0, mul_zero]))
    -- ## 3. the operator-side identity
    have hLHS : (∫ x in Submission.BoseGases.abox (p+1) ℓ,
          star ((boxRestrictC ℓ Φ) x) *
            Work.BoseDict.boxSlotOf e (f k) (f k) j (boxRestrictC ℓ Φ) x).re
        = ∫ r in Submission.BoseGases.abox p ℓ,
            ‖∫ z in Submission.BoseGases.acube ℓ, star (c * Work.BoseK15.corpusBox.qVec ℓ κ z)
              * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ)‖ ^ 2 := by
      rw [show (fun x : Submission.BoseGases.X (p+1) => star ((boxRestrictC ℓ Φ) x) *
            Work.BoseDict.boxSlotOf e (f k) (f k) j (boxRestrictC ℓ Φ) x)
          = fun x : Submission.BoseGases.X (p+1) => star ((boxRestrictC ℓ Φ) x) *
              (Work.BoseDict.etaOf e (f k) (x j)
                * ∫ z, star (Work.BoseDict.etaOf e (f k) z)
                  * (boxRestrictC ℓ Φ) (Function.update x j z))
        from funext fun x => rfl]
      rw [boxSlotPairing_congr (u := Work.BoseDict.etaOf e (f k))
        (u' := fun z : E3 => c * Work.BoseK15.corpusBox.qVec ℓ κ z) hηae.symm (boxRestrictC ℓ Φ) j]
      rw [lhsFibrePair (p := p) (ℓ := ℓ) hℓ j hΦ hηmeas hηbd hηcs]
    -- ## 4. the fibre dictionary
    have hupd0 : ∀ (r : Submission.BoseGases.X p) (z : E3),
        Submission.BoseGases.kcInsN p j (z,r)
          = Function.update (Submission.BoseGases.kcInsN p j (0,r)) j z := by
      intro r z
      funext i
      by_cases hi : i = j
      · rw [hi, Function.update_self, Submission.BoseGases.kc_insN_apply_same]
      · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
        rw [Function.update_of_ne (Fin.succAbove_ne j i'), Submission.BoseGases.kc_insN_apply_succ,
          Submission.BoseGases.kc_insN_apply_succ]
    have hfib : ∀ r : Submission.BoseGases.X p,
        ContDiff ℝ (⊤ : ℕ∞) (fun z : E3 => Φ (Submission.BoseGases.kcInsN p j (z,r))) := by
      intro r
      refine hΦ.comp ?_
      have hcd : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : E3 => Function.update (Submission.BoseGases.kcInsN p j (0,r)) j z) := by
        rw [contDiff_pi]
        intro i
        by_cases hi : i = j
        · have hz : (fun z : E3 =>
              Function.update (Submission.BoseGases.kcInsN p j (0,r)) j z i) = fun z => z := by
            funext z; rw [hi, Function.update_self]
          rw [hz]
          exact contDiff_id
        · have hz : (fun z : E3 =>
              Function.update (Submission.BoseGases.kcInsN p j (0,r)) j z i)
              = fun _ => (Submission.BoseGases.kcInsN p j (0,r)) i := by
            funext z; exact Function.update_of_ne hi z (Submission.BoseGases.kcInsN p j (0,r))
          rw [hz]
          exact contDiff_const
      rw [show (fun z : E3 => Submission.BoseGases.kcInsN p j (z,r))
          = fun z => Function.update (Submission.BoseGases.kcInsN p j (0,r)) j z from
        funext fun z => hupd0 r z]
      exact hcd
    have hc2 : ‖c‖ ^ 2 = (ℓ ^ 3)⁻¹ := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
        inv_pow, Real.sq_sqrt (by positivity)]
    have hper : ∀ r : Submission.BoseGases.X p,
        (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
            (winState ℓ (fun z => Φ (Submission.BoseGases.kcInsN p j (z,r)))) κ‖ ^ 2
          = ‖∫ z in Submission.BoseGases.acube ℓ, star (c * Work.BoseK15.corpusBox.qVec ℓ κ z)
              * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ)‖ ^ 2 := by
      intro r
      rw [← qCoeff_eq_kinFT_general hℓ (hfib r) κ]
      have hsupp : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ →
          star (c * Work.BoseK15.corpusBox.qVec ℓ κ z)
            * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ) = 0 := by
        intro z hz
        have hbox : z ∉ Work.BoseK15.corpusBox.boxL ℓ := by
          rw [corpusBox_boxL_eq_acube hℓ]; exact hz
        have hq0 : Work.BoseK15.corpusBox.qVec ℓ κ z = 0 := by
          by_contra hc0
          exact hbox (support_qVec_subset hℓ κ hc0)
        rw [hq0, mul_zero, star_zero, zero_mul]
      have hstep : (∫ z in Submission.BoseGases.acube ℓ, star (c * Work.BoseK15.corpusBox.qVec ℓ κ z)
              * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ))
          = star c * qCoeff ℓ κ (fun z => Φ (Submission.BoseGases.kcInsN p j (z,r))) := by
        rw [(MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)).symm]
        rw [show (fun z : E3 => (Submission.BoseGases.acube ℓ).indicator
              (fun z => star (c * Work.BoseK15.corpusBox.qVec ℓ κ z)
                * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ)) z)
              = fun z : E3 => star (c * Work.BoseK15.corpusBox.qVec ℓ κ z)
                * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ) from by
          funext z
          by_cases hz : z ∈ Submission.BoseGases.acube ℓ
          · simp only [Set.indicator_of_mem hz]
          · simp only [Set.indicator_of_notMem hz, hsupp z hz]]
        rw [show (fun z : E3 => star (c * Work.BoseK15.corpusBox.qVec ℓ κ z)
              * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ))
              = fun z : E3 => star c * (star (Work.BoseK15.corpusBox.qVec ℓ κ z)
                * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ)) from by
          funext z; rw [star_mul]; ring,
          MeasureTheory.integral_const_mul, qCoeff]
        simp only [starRingEnd_apply]
      rw [hstep, norm_mul, norm_star, mul_pow, hc2]
    -- ## 5. the right-hand side equals the same expression
    have hRHS : (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (p+1) ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j) *
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (winState ℓ (Work.BoseKinLoc.fibre (p+1) j Φ x)) κ‖ ^ 2)
        = ∫ r in Submission.BoseGases.abox p ℓ,
            ‖∫ z in Submission.BoseGases.acube ℓ, star (c * Work.BoseK15.corpusBox.qVec ℓ κ z)
              * ((Φ (Submission.BoseGases.kcInsN p j (z,r)) : ℝ) : ℂ)‖ ^ 2 := by
      rw [peel_box_fibre (p := p) (ℓ := ℓ) hℓ j
        (fun ψ => (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT (winState ℓ ψ) κ‖ ^ 2) Φ]
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hper)
    rw [hLHS, ← hRHS]

end Work.BoseBoxFock
