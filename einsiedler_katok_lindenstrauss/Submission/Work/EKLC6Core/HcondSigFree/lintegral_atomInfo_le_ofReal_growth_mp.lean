import Mathlib
import Submission.Work.EKLC6Core.HcondSig_le_growth_plain
import Submission.Work.EKLC6Core.atomInfo_chain
import Submission.Work.EKLC6Core.growth_le_atomInfo_mp
import Submission.Work.EKLC6Core.goodset_borel
import Submission.Work.EKLC6Core.box_mass_asymptotic_condExp
import Submission.Work.EKLC6Core.atomInfo_aemeasurable
import Submission.Work.EKLC6Core.HcondSigFree.atomInfo_chain_mp
import Submission.Work.EKLC6Core.HcondSigFree.box_mass_asymptotic_condExp_mp

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.EKLC6Core.HcondSigFree

/-!
# `EKLC6Core.HcondSigFree.lintegral_atomInfo_le_ofReal_growth_mp`

The measure-preserving (single-parameter, ergodicity-free) form of the analytic half of the
shape comparison (Pisa 7.34/7.35).  It is
`Work.EKLC6Core.lintegral_atomInfo_le_ofReal_growth` with the hypothesis `IsAErgodic μ`
replaced by `MeasurePreserving (fun x => aDiag t • x) μ μ` for the single parameter `t`.  Every
step of that proof uses only the preservation of `μ` by `aDiag t`, so the whole argument
transfers.  The ingredients stated with the ergodic hypothesis are restated in the
measure-preserving form: `atomInfo_sum_le_log_UBox_mp` below (a port of
`EKLC6Core.atomInfo_sum_le_log_UBox`, using the delegated `atomInfo_chain_mp`) and the delegated
`box_mass_asymptotic_condExp_mp` (Pisa 7.18, conditional-expectation form).  The a.e. measurable
representative of `atomInfo` is supplied by the ergodicity-free `EKLC6Core.atomInfo_aemeasurable`.
-/

/-- **The good-time bound (Pisa 7.34/7.35), measure-preserving form.**  Same as
`EKLC6Core.atomInfo_sum_le_log_UBox`, with `IsAErgodic μ` weakened to
`MeasurePreserving (fun x => aDiag t • x) μ μ`. -/
theorem atomInfo_sum_le_log_UBox_mp (t : Fin 3 → ℝ) {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : X3 → MeasureTheory.Measure SL3} {X' X'' : Set X3}
    (hmp : MeasurePreserving (fun y : X3 => aDiag t • y) μ μ)
    (hL : IsLeafwise μ (Uminus t) ν X')
    (hcov : ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    {A : MeasurableSpace X3} {Z : Set X3}
    (hplq : IsPlaqueAlgebra (Uminus t) Z A) (hZ : μ Zᶜ = 0) {R : ℝ} (hR : 1 ≤ R) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      ((fun y : X3 => aDiag t • y)^[n]) x ∈ Z →
      shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x) ⊆ UBox (Uminus t) R →
      (∑ i ∈ Finset.range n,
          atomInfo A (Uminus t) ν t (((fun y : X3 => aDiag t • y)^[i]) x))
        ≤ Real.log ((ν x (conjBy (-((n : ℝ) • t)) (UBox (Uminus t) R))).toReal)
          - Real.log ((ν x (shape A (Uminus t) x)).toReal) := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hUc : IsClosed ((Uminus t : Subgroup SL3) : Set SL3) := hU.1
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  have hboxmeas : MeasurableSet (UBox (Uminus t) R) := measurableSet_UBox hUc R
  have hboxcomp : IsCompact (UBox (Uminus t) R) := isCompact_UBox hUc hR0
  -- the conull set of points all of whose iterates are good
  have hGae : ∀ᵐ x ∂μ, ∀ j : ℕ,
      ((fun y : X3 => aDiag t • y)^[j]) x ∈ X' ∩ X'' ∩ Z := by
    rw [ae_all_iff]
    intro j
    have hj : MeasurePreserving ((fun y : X3 => aDiag t • y)^[j]) μ μ := hmp.iterate j
    have h1 : ∀ᵐ x ∂μ, ((fun y : X3 => aDiag t • y)^[j]) x ∈ X' :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hL.conull)
    have h2 : ∀ᵐ x ∂μ, ((fun y : X3 => aDiag t • y)^[j]) x ∈ X'' :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hX'')
    have h3 : ∀ᵐ x ∂μ, ((fun y : X3 => aDiag t • y)^[j]) x ∈ Z :=
      hj.quasiMeasurePreserving.ae (ae_iff.mpr hZ)
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    exact ⟨⟨hx1, hx2⟩, hx3⟩
  have hchain := atomInfo_chain_mp (A := A) (Z := Z) t hmp hL hcov hX'' hplq hZ
  filter_upwards [hGae, hchain] with x hxG hchainx
  intro n hnZ hsub
  have hxG' : ∀ j : ℕ, j ≤ n + 1 →
      ((fun y : X3 => aDiag t • y)^[j]) x ∈ X' ∩ X'' := fun j _ => (hxG j).1
  have hxGZ' : ∀ j : ℕ, ((fun y : X3 => aDiag t • y)^[j]) x ∈ X' ∩ X'' ∩ Z := hxG
  -- the iterate identity for the shape at the tip and the box
  have htip : 0 < ν (((fun y : X3 => aDiag t • y)^[n]) x)
      (shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x)) ∧
      ν (((fun y : X3 => aDiag t • y)^[n]) x)
        (shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x)) < ⊤ :=
    shape_mass_pos hL hplq (hxG n).1.1 (hxG n).2
  have hboxpos : 0 < ν (((fun y : X3 => aDiag t • y)^[n]) x) (UBox (Uminus t) R) ∧
      ν (((fun y : X3 => aDiag t • y)^[n]) x) (UBox (Uminus t) R) < ⊤ :=
    ⟨lt_of_lt_of_le htip.1 (measure_mono hsub),
      (hL.radon _ (hxG n).1.1).lt_top_of_isCompact hboxcomp⟩
  -- (a) the iterate identity for the shape of the pulled-back atom
  have h1 : Real.log ((ν x (shape (MeasurableSpace.comap
        ((fun y : X3 => aDiag t • y)^[n]) A) (Uminus t) x)).toReal)
      = Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x)
            (shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x))).toReal)
        + ∑ i ∈ Finset.range n,
            growthFun (Uminus t) ν t (((fun y : X3 => aDiag t • y)^[(i+1)]) x) :=
    iterate_log_pointwise t hL hU hcov hplq hxGZ' n
  -- (b) the shape at the tip is inside the box
  have h2 : Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x)
          (shape A (Uminus t) (((fun y : X3 => aDiag t • y)^[n]) x))).toReal)
      ≤ Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x) (UBox (Uminus t) R)).toReal) :=
    Real.log_le_log (ENNReal.toReal_pos htip.1.ne' htip.2.ne)
      (ENNReal.toReal_mono hboxpos.2.ne (measure_mono hsub))
  -- (c) the mass of the conjugated box
  have h3 : Real.log ((ν (((fun y : X3 => aDiag t • y)^[n]) x) (UBox (Uminus t) R)).toReal)
        + ∑ i ∈ Finset.range n,
            growthFun (Uminus t) ν t (((fun y : X3 => aDiag t • y)^[(i+1)]) x)
      = Real.log ((ν x (conjBy (-((n : ℝ) • t)) (UBox (Uminus t) R))).toReal) :=
    (log_mass_conjBy_eq t hL hcov hxG' hboxmeas hboxpos).symm
  -- the initial atom shape has positive finite mass
  have hinit : 0 < ν x (shape A (Uminus t) x) ∧ ν x (shape A (Uminus t) x) < ⊤ :=
    shape_mass_pos hL hplq (hxG 0).1.1 (hxG 0).2
  rw [hchainx n]
  linarith [h1, h2, h3]

theorem lintegral_atomInfo_le_ofReal_growth_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    (S : Work.EKLRelCross.MSAlg) {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z S.m)
    (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) S.m ≤ S.m) :
    ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.atomInfo S.m (Work.EKLC6Core.Uminus t) ν t x) ∂μ
      ≤ ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) := by
  classical
  have hUc : IsClosed ((Uminus t : Subgroup SL3) : Set SL3) := (uminus_isHoro t).1.1
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  -- the conditional expectation of `growthFun` on the invariant σ-algebra
  set gb : X3 → ℝ := (fun x => condExp (MeasurableSpace.invariants (fun y : X3 => aDiag t • y))
    μ (growthFun (Uminus t) ν t) x) with hgb
  -- STEP 1: the countable family of good sets
  set G : ℕ → Set X3 :=
    (fun k => {y | y ∈ Z ∧ shape S.m (Uminus t) y ⊆ UBox (Uminus t) ((k : ℝ) + 2)}) with hG
  have hGmeas : ∀ k : ℕ, MeasurableSet (G k) := fun k => by
    simpa only [hG] using goodset_borel (A := S.m) (Z := Z) hUc hplq ((k : ℝ) + 2)
  have hcover : ∀ y ∈ Z, ∃ k : ℕ, y ∈ G k := by
    intro y hy
    obtain ⟨C, hC⟩ := (hplq.2.2.2 y hy).2.2.2
    refine ⟨⌈C⌉₊, ?_⟩
    simp only [hG, Set.mem_ofPred_eq]
    refine ⟨hy, fun u hu => ⟨hu.1, fun i j => ?_⟩⟩
    have h1 : |u i j| ≤ C := hC u hu i j
    have h3 : C ≤ ((⌈C⌉₊ : ℕ) : ℝ) := Nat.le_ceil C
    linarith
  -- STEP 2: Poincaré recurrence for the measure preserving `aDiag t ·`
  have hrec : ∀ k : ℕ, ∀ᵐ x ∂μ, x ∈ G k →
      ∃ᶠ n in atTop, ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k := fun k =>
    (hmp.conservative).ae_mem_imp_frequently_image_mem (hGmeas k).nullMeasurableSet
  have hgt : ∀ᵐ x ∂μ, ∃ k : ℕ, x ∈ G k ∧
      ∃ᶠ n in atTop, ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k := by
    have h1 : ∀ᵐ x ∂μ, x ∈ Z := by rw [ae_iff]; exact hZ
    have h2 : ∀ᵐ x ∂μ, ∀ k : ℕ, (x ∈ G k →
        ∃ᶠ n in atTop, ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k) := ae_all_iff.mpr hrec
    filter_upwards [h1, h2] with x hxZ hall
    obtain ⟨k, hk⟩ := hcover x hxZ
    exact ⟨k, hk, hall k hk⟩
  -- STEP 3: the box asymptotics (Pisa 7.18 in the non-ergodic case)
  have hbox : ∀ᵐ x ∂μ, ∀ k : ℕ, Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * Real.log
      ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)) atTop
      (𝓝 (gb x)) := by
    have h0 : ∀ k : ℕ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * Real.log
        ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)) atTop
        (𝓝 (gb x)) := by
      intro k
      have h2 : (2 : ℝ) ≤ ((k : ℝ) + 2) := by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      filter_upwards [box_mass_asymptotic_condExp_mp (μ := μ) (ν := ν) (X' := X') (X'' := X'') t hL
        hcov hX'' hmp hmeas hint h2] with x hx
      rw [hgb]
      exact hx
    exact ae_all_iff.mpr h0
  -- STEP 4: the shape sandwich at the good times
  have hsw : ∀ᵐ x ∂μ, ∀ (k n : ℕ), ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k →
      (∑ i ∈ Finset.range n,
        atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x))
        ≤ Real.log ((ν x (conjBy (-(((n : ℝ)) • t))
            (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)
          - Real.log ((ν x (shape S.m (Uminus t) x)).toReal) := by
    have h0 : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ n : ℕ, ((fun x : X3 => aDiag t • x)^[n]) x ∈ G k →
        (∑ i ∈ Finset.range n,
          atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x))
          ≤ Real.log ((ν x (conjBy (-(((n : ℝ)) • t))
              (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)
            - Real.log ((ν x (shape S.m (Uminus t) x)).toReal) := by
      intro k
      have h2 : (1 : ℝ) ≤ ((k : ℝ) + 2) := by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      filter_upwards [atomInfo_sum_le_log_UBox_mp (μ := μ) (ν := ν) (X' := X') (X'' := X'') t
        hmp hL hcov hX'' hplq hZ (R := ((k : ℝ) + 2)) h2] with x hx
      intro n hn
      exact hx n hn.1 hn.2
    exact ae_all_iff.mpr h0
  -- STEP 5: a measurable representative of `atomInfo` and the truncations
  obtain ⟨ai, hai_meas, hai_eq⟩ :=
    atomInfo_aemeasurable (μ := μ) (ν := ν) (X' := X') (A := S.m) (Z := Z) t hL hU hplq
  set fN : ℕ → X3 → ℝ := (fun N x => min (max (ai x) 0) N) with hfN
  have hfNmeas : ∀ N : ℕ, Measurable (fN N) := fun N => by
    rw [hfN]
    exact (hai_meas.max measurable_const).min measurable_const
  have hfNint : ∀ N : ℕ, Integrable (fN N) μ := by
    intro N
    refine Integrable.of_bound (hfNmeas N).aestronglyMeasurable (N : ℝ) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    have h1 : 0 ≤ fN N x := by
      rw [hfN]; simp only []
      exact le_min (le_max_right _ _) (Nat.cast_nonneg N)
    rw [abs_of_nonneg h1]
    rw [hfN]; simp only []
    exact min_le_right _ _
  have horb : ∀ᵐ x ∂μ, ∀ i : ℕ,
      atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x)
        = ai (((fun x : X3 => aDiag t • x)^[i]) x) := by
    have h0 : ∀ i : ℕ, ∀ᵐ x ∂μ,
        atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x)
          = ai (((fun x : X3 => aDiag t • x)^[i]) x) := fun i =>
      (hmp.iterate i).quasiMeasurePreserving.ae_eq_comp hai_eq
    exact ae_all_iff.mpr h0
  -- STEP 6: Birkhoff's theorem for the truncations
  have hbirk : ∀ᵐ x ∂μ, ∀ N : ℕ, Tendsto
      (fun n : ℕ => Work.EKLComp.Birkhoff.birkA (fun x : X3 => aDiag t • x) (fN N) n x) atTop
      (𝓝 (condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ (fN N) x)) :=
    ae_all_iff.mpr (fun N => Work.EKLComp.birkhoff_all μ (fun x : X3 => aDiag t • x) hmp
      (fN N) (hfNint N))
  -- STEP 7: the pointwise comparison at a.e. point, using the good return times
  have hcmp : ∀ᵐ x ∂μ, ∀ N : ℕ,
      condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ (fN N) x ≤ gb x := by
    filter_upwards [hgt, hbox, hsw, horb, hbirk] with x hgtx hboxx hswx horbx hbirkx
    intro N
    obtain ⟨k, -, hfreq⟩ := hgtx
    set B : ℕ → ℝ := (fun n => ((n : ℝ))⁻¹ * Real.log
      ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)
        - ((n : ℝ))⁻¹ * Real.log ((ν x (shape S.m (Uminus t) x)).toReal)) with hB
    have hAB : ∃ᶠ n in atTop,
        Work.EKLComp.Birkhoff.birkA (fun x : X3 => aDiag t • x) (fN N) n x ≤ B n := by
      refine hfreq.mono (fun n hn => ?_)
      have hS := hswx k n hn
      have hle : (∑ i ∈ Finset.range n, fN N (((fun x : X3 => aDiag t • x)^[i]) x))
          ≤ ∑ i ∈ Finset.range n,
              atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h0 : 0 ≤ atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x) :=
          atomInfo_nonneg_of_dec hdec _
        have h1 : ai (((fun x : X3 => aDiag t • x)^[i]) x)
            = atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x) :=
          (horbx i).symm
        rw [hfN]
        simp only []
        refine le_trans (min_le_left _ _) ?_
        rw [max_le_iff]
        exact ⟨by rw [h1], h0⟩
      have hπ : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
      calc Work.EKLComp.Birkhoff.birkA (fun x : X3 => aDiag t • x) (fN N) n x
          = ((n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
              fN N (((fun x : X3 => aDiag t • x)^[i]) x) := by
            rw [Work.EKLComp.Birkhoff.birkA_def]
        _ ≤ ((n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
              atomInfo S.m (Uminus t) ν t (((fun x : X3 => aDiag t • x)^[i]) x) :=
            mul_le_mul_of_nonneg_left hle hπ
        _ ≤ B n := by
            rw [hB]
            simpa only [mul_sub] using mul_le_mul_of_nonneg_left hS hπ
    have hAlim : Tendsto (fun n : ℕ =>
        Work.EKLComp.Birkhoff.birkA (fun x : X3 => aDiag t • x) (fN N) n x) atTop
        (𝓝 (condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ (fN N) x)) :=
      hbirkx N
    have hBlim : Tendsto B atTop (𝓝 (gb x)) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * Real.log
          ((ν x (conjBy (-(((n : ℝ)) • t)) (UBox (Uminus t) ((k : ℝ) + 2)))).toReal)) atTop
          (𝓝 (gb x)) := hboxx k
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹
          * Real.log ((ν x (shape S.m (Uminus t) x)).toReal)) atTop (𝓝 0) := by
        have h3 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        simpa using h3.mul_const (Real.log ((ν x (shape S.m (Uminus t) x)).toReal))
      have h4 := h1.sub h2
      rw [sub_zero] at h4
      refine h4.congr' (Filter.Eventually.of_forall (fun n => ?_))
      rw [hB]
    exact le_of_frequently_le_of_tendsto hAlim hBlim hAB
  -- STEP 8: integration
  have hgbint : Integrable gb μ := by
    rw [hgb]
    exact MeasureTheory.integrable_condExp (m := MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) (μ := μ) (f := growthFun (Uminus t) ν t)
  have hInt1 : ∀ N : ℕ, ∫ x, fN N x ∂μ ≤ ∫ x, gb x ∂μ := by
    intro N
    have h2 : ∫ x, condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ
          (fN N) x ∂μ ≤ ∫ x, gb x ∂μ := by
      refine integral_mono_ae (MeasureTheory.integrable_condExp (m := MeasurableSpace.invariants
        (fun x : X3 => aDiag t • x)) (μ := μ) (f := fN N)) hgbint ?_
      exact hcmp.mono (fun x hx => hx N)
    have h3 : ∫ x, condExp (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) μ
          (fN N) x ∂μ = ∫ x, fN N x ∂μ :=
      MeasureTheory.integral_condExp (m := MeasurableSpace.invariants
        (fun x : X3 => aDiag t • x)) (μ := μ) (f := fN N)
        (MeasurableSpace.invariants_le (fun x : X3 => aDiag t • x))
    rw [h3] at h2
    exact h2
  have hIntg : ∫ x, gb x ∂μ = ∫ x, growthFun (Uminus t) ν t x ∂μ := by
    rw [hgb]
    exact MeasureTheory.integral_condExp (m := MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) (μ := μ) (f := growthFun (Uminus t) ν t)
      (MeasurableSpace.invariants_le (fun x : X3 => aDiag t • x))
  -- STEP 9: monotone convergence in `N`
  have hMCT : ∫⁻ x, ENNReal.ofReal (atomInfo S.m (Uminus t) ν t x) ∂μ
      = ⨆ N : ℕ, ∫⁻ x, ENNReal.ofReal (fN N x) ∂μ := by
    have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (atomInfo S.m (Uminus t) ν t x)
        = ⨆ N : ℕ, ENNReal.ofReal (fN N x) := by
      filter_upwards [hai_eq.symm] with x hx1
      rw [← hx1]
      have hc0 : (0 : ℝ) ≤ ai x := by
        have h0 : 0 ≤ atomInfo S.m (Uminus t) ν t x := atomInfo_nonneg_of_dec hdec x
        rwa [← hx1] at h0
      have hfNc : ∀ N : ℕ, fN N x = min (ai x) N := by
        intro N
        rw [hfN]; simp only []
        rw [max_eq_left hc0]
      refine le_antisymm ?_ ?_
      · refine le_trans ?_ (le_iSup (fun N : ℕ => ENNReal.ofReal (fN N x)) ⌈ai x⌉₊)
        rw [hfNc ⌈ai x⌉₊, min_eq_left (Nat.le_ceil (ai x))]
      · refine iSup_le (fun N => ENNReal.ofReal_le_ofReal ?_)
        rw [hfNc N]
        exact min_le_left _ _
    have hmono : Monotone (fun N x => ENNReal.ofReal (fN N x)) := by
      intro i j hij x
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hfN]; simp only []
      exact min_le_min le_rfl (Nat.cast_le.mpr hij)
    have hmeas' : ∀ N : ℕ, Measurable (fun x => ENNReal.ofReal (fN N x)) :=
      fun N => ENNReal.measurable_ofReal.comp (hfNmeas N)
    have hmain := lintegral_iSup (μ := μ) (f := fun N x => ENNReal.ofReal (fN N x)) hmeas' hmono
    rw [← hmain]
    exact lintegral_congr_ae hpt
  calc ∫⁻ x, ENNReal.ofReal (atomInfo S.m (Uminus t) ν t x) ∂μ
      = ⨆ N : ℕ, ∫⁻ x, ENNReal.ofReal (fN N x) ∂μ := hMCT
    _ = ⨆ N : ℕ, ENNReal.ofReal (∫ x, fN N x ∂μ) := by
        refine iSup_congr (fun N => ?_)
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfNint N)
          (ae_of_all _ (fun x => by
            rw [hfN]; simp only []
            exact le_min (le_max_right _ _) (Nat.cast_nonneg N)))).symm
    _ ≤ ENNReal.ofReal (∫ x, growthFun (Uminus t) ν t x ∂μ) := by
        refine iSup_le (fun N => ENNReal.ofReal_le_ofReal ?_)
        exact le_trans (hInt1 N) (le_of_eq hIntg)

end Work.EKLC6Core.HcondSigFree
