/-
Copyright: work module for the Elgindi finite-time singularity project.

# The interval-integral `ℋ`-membership (per-`z` version): the exchange and the averaging bound

This module contains, for a family `s ↦ H s` of profiles smooth on the open quadrant:

* `exch_point` — the exchange identity `D_z^j D_θ^i (∫_s H s) = ∫_s D_z^j D_θ^i (H s)` at a point
  of the open quadrant, deduced from the interface statement `ExchMixed` (proved elsewhere as
  `Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted`), using the uniform
  slot bounds on compacta;
* `cv_bound` — the pointwise Cauchy–Schwarz (averaging) bound
  `HkIntegrand α k (∫_s H s) ≤ (b-a) ∫_s HkIntegrand α k (H s)` on the open quadrant;
* the joint measurability of the family's slots in `(s,(z,θ))` and the measurability of the
  `s`-integrals of the slots (both as functions of `(z,θ)` and, for fixed `z > 0`, of `θ`);
* the joint and per-`z` measurability of the `ℋ^k`-integrand of the primitive.

All statements are conditional on the two interface hypotheses `CarathTheta` and `ExchMixed`
(see `PerzTools/Basic.lean`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EpsEngine.PerzTools.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.PerzTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The exchange identity at a point of the open quadrant.** -/
lemma exch_point {T a b : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ} (hexch : ExchMixed)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    {j i : ℕ} (hji : j + i ≤ k) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
      = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := by
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hzmem : z ∈ Set.Ioo (z / 2) (z + 1) := ⟨by linarith, by linarith⟩
  have hθmem : θ ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2) :=
    ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hboxQ : Set.Icc (z / 2) (z + 1) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2)
      ⊆ Work.FTS.EllipticEst.Q0 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨by linarith [hq1.1], by linarith [hq2.1],
      by linarith [hq2.2, Real.pi_pos]⟩
  obtain ⟨C, hC0, hC⟩ := hsup
    (Set.Icc (z / 2) (z + 1) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2))
    (isCompact_Icc.prod isCompact_Icc) hboxQ
  exact hexch haT hbT hab hC0 hsm hmeas
    (fun s hs j i hji q hq => hC s hs q hq j i hji) hboxQ hji z θ
    (Set.mem_prod.mpr ⟨hzmem, hθmem⟩)

/-- **The pointwise Cauchy–Schwarz (averaging) bound.** -/
lemma cv_bound {T a b : ℝ} {α : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ} (hexch : ExchMixed)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ
      ≤ (b - a) * ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ := by
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  obtain ⟨C, hC0, hC⟩ := hsup {(z, θ)} isCompact_singleton (by simpa using hzθ)
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  refine Work.FTS.StrongEps.E5G5.HkIntegrand_intervalIntegral_le_gen hab hC0 hz0 hθ0 hθ1
    ?_ ?_ ?_
  · intro j i hji
    exact (hmeas j i hji z θ hzθ).mono_measure (Measure.restrict_mono hsub le_rfl)
  · intro j i hji s hs
    exact hC s (hsub hs) (z, θ) (by simp) j i hji
  · intro j i hji
    exact exch_point hexch haT hbT hab hsm hmeas hsup hji hzθ

/-- Joint measurability of a slot of the family in `(s,(z,θ))`. -/
lemma all_aesm_slot3 {T : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    {j i : ℕ} (hji : j + i ≤ k) :
    AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i (H p.1) p.2.1 p.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) := by
  classical
  set g : ℝ → ℝ → ℝ → ℝ := fun s z θ =>
    if (z, θ) ∈ Work.FTS.EllipticEst.Q0 then Work.Spaces.mixed j i (H s) z θ else 0
  have hmain : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume) := by
    refine Work.FTS.EpsEngine.aesm_uncurry_restricted measurableSet_Icc ?_ ?_ ?_
    · intro s hs
      refine ((hsm s hs).mixed j i).continuousOn.congr ?_
      intro q hq
      show (if (q.1, q.2) ∈ Work.FTS.EllipticEst.Q0 then
        Work.Spaces.mixed j i (H s) q.1 q.2 else 0) = Work.Spaces.mixed j i (H s) q.1 q.2
      rw [ite_eq_left (by simpa only [Prod.mk.eta] using hq)]
    · intro s hs q hq
      show (if (q.1, q.2) ∈ Work.FTS.EllipticEst.Q0 then
        Work.Spaces.mixed j i (H s) q.1 q.2 else 0) = 0
      exact ite_eq_right (fun h => hq h)
    · intro q
      by_cases hq : q ∈ Work.FTS.EllipticEst.Q0
      · have hthis : (fun s : ℝ => g s q.1 q.2)
            = fun s : ℝ => Work.Spaces.mixed j i (H s) q.1 q.2 :=
          funext fun s => by simp only [g]; rw [ite_eq_left hq]
        rw [hthis]
        exact hmeas j i hji q.1 q.2 hq
      · have hthis : (fun s : ℝ => g s q.1 q.2) = fun _ : ℝ => (0 : ℝ) :=
          funext fun s => by simp only [g]; rw [ite_eq_right hq]
        rw [hthis]
        exact aestronglyMeasurable_const
  rw [prod_restrict_Iz_Iθ_eq_Q0]
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        (volume.restrict Work.FTS.EllipticEst.Q0)) :=
    hmain.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  refine h1.congr ?_
  change ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod
      (volume.restrict Work.FTS.EllipticEst.Q0)),
    g p.1 p.2.1 p.2.2 = Work.Spaces.mixed j i (H p.1) p.2.1 p.2.2
  have hae : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod
      (volume.restrict Work.FTS.EllipticEst.Q0)), p.2 ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × (ℝ × ℝ) =>
      p.2 ∈ Work.FTS.EllipticEst.Q0) (Work.FTS.EllipticEst.isOpen_Q0.measurableSet.preimage
        measurable_snd)]
    exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet)
  filter_upwards [hae] with p hp
  simp only [g]
  rw [ite_eq_left hp]

/-- Measurability of the `s`-integral of a slot, as a function of `(z,θ)`. -/
lemma aesm_intervalIntegral_slot {T a b : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    {j i : ℕ} (hji : j + i ≤ k) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => ∫ s in a..b, Work.Spaces.mixed j i (H s) q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have h3 := all_aesm_slot3 hsm hmeas hji
  have h3' : AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i (H p.1) p.2.1 p.2.2)
      ((volume.restrict (Set.uIoc a b)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :=
    h3.mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
  have hswap := h3'.prod_swap
  have hint := hswap.integral_prod_right'
  have hgoal : AEStronglyMeasurable
      (fun q : ℝ × ℝ => ∫ s in Set.Ioc a b, Work.Spaces.mixed j i (H s) q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Set.uIoc_of_le hab]
    exact hint
  have hfe : (fun q : ℝ × ℝ => ∫ s in a..b, Work.Spaces.mixed j i (H s) q.1 q.2)
      = fun q : ℝ × ℝ => ∫ s in Set.Ioc a b, Work.Spaces.mixed j i (H s) q.1 q.2 := by
    funext q
    rw [intervalIntegral.integral_of_le hab]
  rw [hfe]
  exact hgoal

/-- The per-`z` version of `aesm_intervalIntegral_slot`. -/
lemma aesm_intervalIntegral_slot_perz {T a b : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hcar : CarathTheta)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    {z : ℝ} (hz : 0 < z) {j i : ℕ} (hji : j + i ≤ k) :
    AEStronglyMeasurable (fun θ : ℝ => ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have h3 := perz_aesm_slot hcar hsm hmeas hz hji
  have h3' : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i (H p.1) z p.2)
      ((volume.restrict (Set.uIoc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    h3.mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
  have hswap := h3'.prod_swap
  have hint := hswap.integral_prod_right'
  have hgoal : AEStronglyMeasurable
      (fun θ : ℝ => ∫ s in Set.Ioc a b, Work.Spaces.mixed j i (H s) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [← Set.uIoc_of_le hab]
    exact hint
  have hfe : (fun θ : ℝ => ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ)
      = fun θ : ℝ => ∫ s in Set.Ioc a b, Work.Spaces.mixed j i (H s) z θ := by
    funext θ
    rw [intervalIntegral.integral_of_le hab]
  rw [hfe]
  exact hgoal

/-- **Joint measurability of the `ℋ^k`-integrand of the primitive** (as a function of `(z,θ)`). -/
lemma aesm_HkIntegrand_primitive {T a b : ℝ} {α : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hexch : ExchMixed)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C) :
    AEStronglyMeasurable
      (fun q : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  classical
  have hslot : ∀ (j i : ℕ), j + i ≤ k →
      AEStronglyMeasurable
        (fun q : ℝ × ℝ => Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    intro j i hji
    refine (aesm_intervalIntegral_slot haT hbT hab hsm hmeas hji).congr ?_
    filter_upwards [ae_mem_Q0] with q hq
    exact (exch_point hexch haT hbT hab hsm hmeas hsup hji hq).symm
  have hWt : AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_Wt_Q0 α
  have hW : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_wdivsin_Q0
  have hfun : (fun q : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2)
      = fun q : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
                * (Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
                    * Work.Spaces.Wt α q.1 q.2) ^ 2 else 0) :=
    funext fun q => rfl
  rw [hfun]
  refine AEStronglyMeasurable.add ?_ ?_
  · refine aesm_finsetSum_apply (fun i hi => ?_)
    have hik : i + 0 ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have h0 := hslot i 0 hik
    refine (h0.mul hW).pow 2 |>.congr ?_
    filter_upwards with p
    simp only [Pi.mul_apply, Pi.pow_apply, Work.Spaces.mixed_zero_right]
  · refine aesm_finsetSum_apply (fun i hi => aesm_finsetSum_apply (fun j hj => ?_))
    by_cases hij : 1 ≤ i ∧ i + j ≤ k
    · have hthis : (fun q : ℝ × ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
              * Work.Spaces.Wt α q.1 q.2) ^ 2 else 0))
          = fun q : ℝ × ℝ =>
            (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
              * Work.Spaces.Wt α q.1 q.2) ^ 2 :=
        funext fun q => ite_eq_left hij
      rw [hthis]
      refine ((hslot j i (by omega)).mul hWt).pow 2 |>.congr ?_
      filter_upwards with p
      simp only [Pi.mul_apply, Pi.pow_apply]
    · have hthis : (fun q : ℝ × ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
              * Work.Spaces.Wt α q.1 q.2) ^ 2 else 0)) = fun q : ℝ × ℝ => (0 : ℝ) :=
        funext fun q => ite_eq_right hij
      rw [hthis]
      exact aestronglyMeasurable_const

/-- **Per-`z` measurability of the `ℋ^k`-integrand of the primitive.** -/
lemma aesm_slice_HkIntegrand_primitive {T a b : ℝ} {α : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hcar : CarathTheta) (hexch : ExchMixed)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  classical
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hzero : (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [← hz0, HkIntegrand_fst_zero]
    rw [hzero]
    exact aestronglyMeasurable_const
  · have hslot : ∀ (j i : ℕ), j + i ≤ k →
        AEStronglyMeasurable
          (fun θ : ℝ => Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ)
          (volume.restrict Work.Spaces.Iθ) := by
      intro j i hji
      refine (aesm_intervalIntegral_slot_perz hcar haT hbT hab hsm hmeas hzpos hji).congr ?_
      have hIθ : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
      rw [← hIθ]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact (exch_point hexch haT hbT hab hsm hmeas hsup hji
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ⟩)).symm
    have hWt : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Wt α z θ)
        (volume.restrict Work.Spaces.Iθ) := Wt_aesm_Iθ α z
    have hW : AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        (volume.restrict Work.Spaces.Iθ) := wdivsin_aesm_Iθ z
    have hfun : (fun θ : ℝ =>
          Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ)
        = fun θ : ℝ =>
            (∑ i ∈ Finset.range (k + 1),
                (Work.Spaces.DzIter i (fun z θ => ∫ s in a..b, H s z θ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  (if 1 ≤ i ∧ i + j ≤ k then
                    (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
                      * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
      funext fun θ => rfl
    rw [hfun]
    refine AEStronglyMeasurable.add ?_ ?_
    · refine aesm_finsetSum_apply (fun i hi => ?_)
      have hik : i + 0 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      have h0 := hslot i 0 hik
      refine (h0.mul hW).pow 2 |>.congr ?_
      filter_upwards with p
      simp only [Pi.mul_apply, Pi.pow_apply, Work.Spaces.mixed_zero_right]
    · refine aesm_finsetSum_apply (fun i hi => aesm_finsetSum_apply (fun j hj => ?_))
      by_cases hij : 1 ≤ i ∧ i + j ≤ k
      · have hthis : (fun θ : ℝ =>
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun θ : ℝ =>
              (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 :=
          funext fun θ => ite_eq_left hij
        rw [hthis]
        refine ((hslot j i (by omega)).mul hWt).pow 2 |>.congr ?_
        filter_upwards with p
        simp only [Pi.mul_apply, Pi.pow_apply]
      · have hthis : (fun θ : ℝ =>
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)) = fun θ : ℝ => (0 : ℝ) :=
          funext fun θ => ite_eq_right hij
        rw [hthis]
        exact aestronglyMeasurable_const

end Work.FTS.EpsEngine.PerzTools
