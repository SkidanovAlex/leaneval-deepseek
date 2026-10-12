import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.L1Tails.chiChiCoulAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `χχ`-images kernel splits into its `26` nearest-neighbour images

`chiChiImages ℓ W w y = χ_ℓ(w)·χ_ℓ(y)·Σ'_{m ≠ 0} W(w − y + ℓ•latVec m)`.  On the box
`Λ(ℓ) = boxL ℓ` only the `26` lattice vectors of `{−1,0,1}³` can contribute: if `m` has a
coordinate of modulus `≥ 2` and `χ_ℓ(w)χ_ℓ(y) ≠ 0`, then `‖w‖, ‖y‖ < ℓ/2`, whence
`‖w − y + ℓ•latVec m‖ ≥ 2ℓ − ℓ = ℓ > R` and `W` vanishes there; while if `χ_ℓ(w)χ_ℓ(y) = 0` then
both sides of the pointwise identity are `0`.  Consequently the box pairing of the images kernel
is the sum of the `26` box pairings of the single images, i.e. the split that reduces `T7` to the
`26` substitution identities.

The proof is elementary: the pointwise collapse of the `tsum`, integrability of each of the `26`
terms against the product of the two restricted box measures (`L¹`-domination by the shift of `W`,
plus quasi-measure-preservation of the difference map for the a.e. strong measurability), and the
finite triangle inequality `‖Σ_m z_m‖ ≤ Σ_m ‖z_m‖`.
-/

namespace Work.BoseBoxFock.L1Tails

noncomputable section

open MeasureTheory
open scoped BigOperators Real Topology ContDiff

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Box" l:70 => Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox l
local notation "Mbox" l:70 =>
  MeasureTheory.Measure.restrict (volume : Measure E3)
    (Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox l)
local notation "Near" =>
  Finset.erase (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)) 0

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. Lattice separation -/

/-- A lattice vector with a coordinate of modulus `≥ 2` has norm `≥ 2`. -/
private lemma two_le_norm_latVec {m : Fin 3 → ℤ} (hm : ∃ i, (2 : ℤ) ≤ |m i|) :
    (2 : ℝ) ≤ ‖latVec m‖ := by
  obtain ⟨i, hi⟩ := hm
  have h1 : ‖(latVec m).ofLp i‖ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i
  rw [Work.BoseBoxFock.latVec_apply, Real.norm_eq_abs] at h1
  have h2 : (2 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by exact_mod_cast hi
  linarith

/-- `chiScale ℓ x ≠ 0` forces `‖x‖ < ℓ/2`: the bump is supported in the open ball of radius
`ℓ/2`. -/
private lemma norm_lt_half_of_chiScale_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : Submission.BoseGases.chiScale ℓ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  have h1 : Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • x) ≠ 0 := by
    simpa only [Submission.BoseGases.chiScale] using hx
  have h2 : ‖(ℓ⁻¹ : ℝ) • x‖ < 1 / 2 := by
    by_contra hcon
    exact h1 (Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), inv_mul_eq_div] at h2
  have h3 := (div_lt_iff₀ hℓ).mp h2
  linarith

/-- **Separation at the lattice scale.**  If `m` has a coordinate of absolute value at least `2`,
then for `w, z` in the support of `chiScale ℓ` the point `w − z + ℓ • latVec m` is at distance
`> R` from the origin (whenever `R ≤ ℓ/2`). -/
private lemma lt_norm_of_latVec_far {ℓ R : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ / 2)
    {m : Fin 3 → ℤ} (hm : ∃ i, (2 : ℤ) ≤ |m i|) {w z : E3}
    (hw : Submission.BoseGases.chiScale ℓ w ≠ 0)
    (hz : Submission.BoseGases.chiScale ℓ z ≠ 0) : R < ‖w - z + ℓ • latVec m‖ := by
  have hlat : (2 : ℝ) ≤ ‖latVec m‖ := two_le_norm_latVec hm
  have hw' : ‖w‖ < ℓ / 2 := norm_lt_half_of_chiScale_ne_zero hℓ hw
  have hz' : ‖z‖ < ℓ / 2 := norm_lt_half_of_chiScale_ne_zero hℓ hz
  have hlat2 : (2 : ℝ) * ℓ ≤ ‖ℓ • latVec m‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
    have := mul_le_mul_of_nonneg_left hlat hℓ.le
    linarith
  have hsub : ‖w - z‖ < ℓ := by
    have := norm_sub_le w z
    linarith
  have hkey : ‖ℓ • latVec m‖ - ‖w - z‖ ≤ ‖w - z + ℓ • latVec m‖ := by
    have h6 := abs_norm_sub_norm_le (ℓ • latVec m) (w - z + ℓ • latVec m)
    have hsub6 : ℓ • latVec m - (w - z + ℓ • latVec m) = -(w - z) := by abel
    rw [hsub6, norm_neg] at h6
    have h7 := (abs_le.mp h6).2
    linarith
  have hRlt : R < ℓ := lt_of_le_of_lt hRℓ (by linarith)
  linarith

/-- A lattice vector outside `{−1,0,1}³` has a coordinate of modulus `≥ 2`. -/
private lemma exists_two_le_abs_of_notMem {m : Fin 3 → ℤ}
    (hm : m ∉ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)) :
    ∃ i, (2 : ℤ) ≤ |m i| := by
  have hnot : ¬ ∀ i : Fin 3, m i ∈ Finset.Icc (-1 : ℤ) 1 := fun h =>
    hm (by rw [Fintype.mem_piFinset]; exact h)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  refine ⟨i, ?_⟩
  have h2 : ¬ (-(1 : ℤ) ≤ m i ∧ m i ≤ 1) := by simpa only [Finset.mem_Icc] using hi
  have hlt : m i < -1 ∨ 1 < m i := by omega
  rcases hlt with hh | hh
  · exact le_trans (by omega : (2 : ℤ) ≤ -(m i)) (neg_le_abs (m i))
  · exact le_trans (by omega : (2 : ℤ) ≤ m i) (le_abs_self (m i))

/-! ## 2. The pointwise splitting -/

/-- **The images kernel is the sum of its `26` nearest-neighbour images.** -/
private lemma chiChiImages_eq_finsum {ℓ R : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ / 2)
    {W : E3 → ℝ} (hWs : ∀ x : E3, R ≤ ‖x‖ → W x = 0) (w y : E3) :
    chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y
      = ∑ m ∈ Near, ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
  rw [chiChiImages]
  by_cases hχw : Submission.BoseGases.chiScale ℓ w = 0
  · simp [hχw]
  by_cases hχy : Submission.BoseGases.chiScale ℓ y = 0
  · simp [hχy]
  have hcollapse : (∑' m : Fin 3 → ℤ,
        (if m = 0 then (0 : ℂ) else ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)))
      = ∑ m ∈ Near, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    refine (tsum_eq_sum (s := Near) (f := fun m : Fin 3 → ℤ =>
        (if m = 0 then (0 : ℂ) else ((W (w - y + ℓ • latVec m) : ℝ) : ℂ))) ?_).trans ?_
    · intro m hmNear
      by_cases hm0 : m = 0
      · rw [if_pos hm0]
      · rw [if_neg hm0]
        have hmT : m ∉ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1) := by
          intro hmem
          exact hmNear (Finset.mem_erase.mpr ⟨hm0, hmem⟩)
        have hmem : ∃ i, (2 : ℤ) ≤ |m i| := exists_two_le_abs_of_notMem hmT
        have hfar : R < ‖w - y + ℓ • latVec m‖ := lt_norm_of_latVec_far hℓ hRℓ hmem hχw hχy
        rw [hWs _ (le_of_lt hfar), Complex.ofReal_zero]
    · exact Finset.sum_congr rfl (fun m hm => by
        rw [if_neg (Finset.mem_erase.mp hm).1])
  rw [hcollapse, Finset.mul_sum]

/-! ## 3. Integrability of one image -/

/-- The `m`-th image of the kernel, as a function of `(w,y)`. -/
private def chiTerm (ℓ : ℝ) (W : E3 → ℝ) (G : E3 → E3 → ℂ) (m : Fin 3 → ℤ) :
    E3 → E3 → ℂ :=
  fun w y => ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
      * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
      * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) * G w y

/-- **Integrability of a single image** against the product of the two restricted box measures.

The bound is pointwise on `Λ(ℓ) × Λ(ℓ)` (`χ_ℓ` is bounded by `chiSup` and `G` is bounded on the
compact box), and the `y`-integral of `‖W(w − y + ℓ•latVec m)‖` is the shift-invariant
`∫‖W‖`. -/
private lemma integrable_chiTerm {ℓ : ℝ} {W : E3 → ℝ} (hWi : Integrable W)
    {G : E3 → E3 → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hGc : Continuous (Function.uncurry G))
    (hGbd : ∀ w : E3, w ∈ Box ℓ → ∀ y : E3, y ∈ Box ℓ → ‖G w y‖ ≤ C)
    (m : Fin 3 → ℤ) :
    Integrable (Function.uncurry (chiTerm ℓ W G m)) ((Mbox ℓ).prod (Mbox ℓ)) := by
  classical
  set C₁ : ℝ := Submission.BoseGases.chiSup * Submission.BoseGases.chiSup * C with hC₁
  have hC₁nn : 0 ≤ C₁ := by
    rw [hC₁]
    exact mul_nonneg
      (mul_nonneg Submission.BoseGases.chiSup_pos.le Submission.BoseGases.chiSup_pos.le) hC
  have hUmeas : MeasurableSet (Box ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hUcomp : IsCompact (Box ℓ) :=
    Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ
  have hUfin : (Mbox ℓ) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hUcomp.measure_lt_top
  -- (a) the pointwise bound on the box
  have hpt : ∀ w : E3, w ∈ Box ℓ → ∀ y : E3, y ∈ Box ℓ →
      ‖chiTerm ℓ W G m w y‖ ≤ C₁ * ‖W (w - y + ℓ • latVec m)‖ := by
    intro w hw y hy
    have hχ1 : ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)‖
        ≤ Submission.BoseGases.chiSup := by
      simpa using Submission.BoseGases.abs_chiScale_le_chiSup ℓ w
    have hχ2 : ‖((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)‖
        ≤ Submission.BoseGases.chiSup := by
      simpa using Submission.BoseGases.abs_chiScale_le_chiSup ℓ y
    have hWn : ‖((W (w - y + ℓ • latVec m) : ℝ) : ℂ)‖ = ‖W (w - y + ℓ • latVec m)‖ := by
      simp
    have hGn : ‖G w y‖ ≤ C := hGbd w hw y hy
    show ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
        * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) * G w y‖
      ≤ C₁ * ‖W (w - y + ℓ • latVec m)‖
    calc ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) * G w y‖
        = ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)‖
            * ‖((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)‖
            * ‖((W (w - y + ℓ • latVec m) : ℝ) : ℂ)‖ * ‖G w y‖ := by
          rw [norm_mul, norm_mul, norm_mul]
      _ = ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)‖
            * ‖((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)‖
            * ‖W (w - y + ℓ • latVec m)‖ * ‖G w y‖ := by rw [hWn]
      _ ≤ Submission.BoseGases.chiSup * Submission.BoseGases.chiSup
            * ‖W (w - y + ℓ • latVec m)‖ * C := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hχ1 hχ2 (norm_nonneg _)
            Submission.BoseGases.chiSup_pos.le) le_rfl (norm_nonneg _)
            (mul_nonneg Submission.BoseGases.chiSup_pos.le Submission.BoseGases.chiSup_pos.le))
            hGn (norm_nonneg _) (mul_nonneg (mul_nonneg Submission.BoseGases.chiSup_pos.le
              Submission.BoseGases.chiSup_pos.le) (norm_nonneg _))
      _ = C₁ * ‖W (w - y + ℓ • latVec m)‖ := by rw [hC₁]; ring
  -- (b) a.e. strong measurability of the joint integrand
  have hAESM : AEStronglyMeasurable (Function.uncurry (chiTerm ℓ W G m))
      ((Mbox ℓ).prod (Mbox ℓ)) := by
    have hle : (Mbox ℓ).prod (Mbox ℓ) ≤ (volume : Measure E3).prod volume := by
      rw [Measure.prod_restrict]
      exact Measure.restrict_le_self
    refine (?_ : AEStronglyMeasurable (Function.uncurry (chiTerm ℓ W G m))
      ((volume : Measure E3).prod volume)).mono_measure hle
    have h1 : Continuous (fun p : E3 × E3 => ((Submission.BoseGases.chiScale ℓ p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((Submission.BoseGases.chiScale_continuous ℓ).comp
        continuous_fst)
    have h2 : Continuous (fun p : E3 × E3 => ((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((Submission.BoseGases.chiScale_continuous ℓ).comp
        continuous_snd)
    have h3 : Continuous (fun p : E3 × E3 => G p.1 p.2) := hGc
    have hW' : AEStronglyMeasurable (fun p : E3 × E3 =>
        ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ)) ((volume : Measure E3).prod volume) := by
      have hK : AEStronglyMeasurable (fun z : E3 => ((W z : ℝ) : ℂ)) (volume : Measure E3) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable hWi.aestronglyMeasurable
      have hq1 : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
          ((volume : Measure E3).prod volume) (volume : Measure E3) :=
        quasiMeasurePreserving_sub_of_right_invariant _ _
      have hq2 : Measure.QuasiMeasurePreserving (fun z : E3 => z + ℓ • latVec m)
          (volume : Measure E3) (volume : Measure E3) :=
        (measurePreserving_add_right (volume : Measure E3) (ℓ • latVec m)).quasiMeasurePreserving
      exact hK.comp_quasiMeasurePreserving (hq2.comp hq1)
    show AEStronglyMeasurable (fun p : E3 × E3 =>
        ((Submission.BoseGases.chiScale ℓ p.1 : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ p.2 : ℝ) : ℂ)
          * ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ) * G p.1 p.2)
      ((volume : Measure E3).prod volume)
    exact ((h1.measurable.aestronglyMeasurable.mul h2.measurable.aestronglyMeasurable).mul
      hW').mul h3.measurable.aestronglyMeasurable
  refine ⟨hAESM, ?_⟩
  -- (c) the inner (`y`-)integral bound, pointwise in `w`
  have hinner : ∀ w : E3, w ∈ Box ℓ →
      (∫⁻ y, ‖Function.uncurry (chiTerm ℓ W G m) (w, y)‖ₑ ∂(Mbox ℓ))
        ≤ ENNReal.ofReal (C₁ * ∫ z : E3, ‖W z‖) := by
    intro w hw
    have hstep1 : (∫⁻ y, ‖Function.uncurry (chiTerm ℓ W G m) (w, y)‖ₑ ∂(Mbox ℓ))
        = ∫⁻ y, ENNReal.ofReal ‖chiTerm ℓ W G m w y‖ ∂(Mbox ℓ) := by
      refine lintegral_congr (fun y => ?_)
      simpa only [Function.uncurry] using (ofReal_norm (chiTerm ℓ W G m w y)).symm
    have hstep2 : (∫⁻ y, ENNReal.ofReal ‖chiTerm ℓ W G m w y‖ ∂(Mbox ℓ))
        ≤ ∫⁻ y, ENNReal.ofReal (C₁ * ‖W (w - y + ℓ • latVec m)‖) ∂(Mbox ℓ) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict hUmeas] with y hy
      exact ENNReal.ofReal_le_ofReal (hpt w hw y hy)
    have hstep3 : (∫⁻ y, ENNReal.ofReal (C₁ * ‖W (w - y + ℓ • latVec m)‖) ∂(Mbox ℓ))
        = ENNReal.ofReal C₁
            * ∫⁻ y, ENNReal.ofReal ‖W (w - y + ℓ • latVec m)‖ ∂(Mbox ℓ) := by
      rw [show (fun y : E3 => ENNReal.ofReal (C₁ * ‖W (w - y + ℓ • latVec m)‖))
            = fun y : E3 => ENNReal.ofReal C₁
                * ENNReal.ofReal ‖W (w - y + ℓ • latVec m)‖ from
          funext fun y => ENNReal.ofReal_mul hC₁nn]
      rw [lintegral_const_mul' (ENNReal.ofReal C₁) _ ENNReal.ofReal_ne_top]
    have hstep4 : (∫⁻ y, ENNReal.ofReal ‖W (w - y + ℓ • latVec m)‖ ∂(Mbox ℓ))
        ≤ ∫⁻ y, ENNReal.ofReal ‖W (w - y + ℓ • latVec m)‖ ∂(volume : Measure E3) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    have hstep5 : (∫⁻ y, ENNReal.ofReal ‖W (w - y + ℓ • latVec m)‖ ∂(volume : Measure E3))
        = ENNReal.ofReal (∫ z : E3, ‖W z‖) := by
      have hshift : (∫⁻ y, ENNReal.ofReal ‖W (w - y + ℓ • latVec m)‖ ∂(volume : Measure E3))
          = ∫⁻ y, ENNReal.ofReal ‖W ((w + ℓ • latVec m) - y)‖ ∂(volume : Measure E3) := by
        refine lintegral_congr (fun y => ?_)
        rw [show w - y + ℓ • latVec m = (w + ℓ • latVec m) - y from by abel]
      rw [hshift]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (f := fun y : E3 => ‖W ((w + ℓ • latVec m) - y)‖)
        ((hWi.norm).comp_sub_left (w + ℓ • latVec m))
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
      rw [MeasureTheory.integral_sub_left_eq_self (fun z : E3 => ‖W z‖)
        (volume : Measure E3) (w + ℓ • latVec m)]
    calc (∫⁻ y, ‖Function.uncurry (chiTerm ℓ W G m) (w, y)‖ₑ ∂(Mbox ℓ))
        = ∫⁻ y, ENNReal.ofReal ‖chiTerm ℓ W G m w y‖ ∂(Mbox ℓ) := hstep1
      _ ≤ ∫⁻ y, ENNReal.ofReal (C₁ * ‖W (w - y + ℓ • latVec m)‖) ∂(Mbox ℓ) := hstep2
      _ = ENNReal.ofReal C₁
            * ∫⁻ y, ENNReal.ofReal ‖W (w - y + ℓ • latVec m)‖ ∂(Mbox ℓ) := hstep3
      _ ≤ ENNReal.ofReal C₁
            * ∫⁻ y, ENNReal.ofReal ‖W (w - y + ℓ • latVec m)‖ ∂(volume : Measure E3) :=
          mul_le_mul_of_nonneg_left hstep4 (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal C₁)
      _ = ENNReal.ofReal C₁ * ENNReal.ofReal (∫ z : E3, ‖W z‖) := by rw [hstep5]
      _ = ENNReal.ofReal (C₁ * ∫ z : E3, ‖W z‖) := by
          rw [← ENNReal.ofReal_mul hC₁nn]
  -- (d) Tonelli and the outer bound
  have hbound : (∫⁻ p, ‖Function.uncurry (chiTerm ℓ W G m) p‖ₑ ∂((Mbox ℓ).prod (Mbox ℓ)))
      ≤ ENNReal.ofReal (C₁ * ∫ z : E3, ‖W z‖) * (Mbox ℓ) Set.univ := by
    calc (∫⁻ p, ‖Function.uncurry (chiTerm ℓ W G m) p‖ₑ ∂((Mbox ℓ).prod (Mbox ℓ)))
        = ∫⁻ w, (∫⁻ y,
            (fun p : E3 × E3 => ‖Function.uncurry (chiTerm ℓ W G m) p‖ₑ) (w, y)
            ∂(Mbox ℓ)) ∂(Mbox ℓ) :=
          lintegral_prod (μ := Mbox ℓ) (ν := Mbox ℓ)
            (f := fun p : E3 × E3 => ‖Function.uncurry (chiTerm ℓ W G m) p‖ₑ) hAESM.enorm
      _ = ∫⁻ w, (∫⁻ y, ‖Function.uncurry (chiTerm ℓ W G m) (w, y)‖ₑ ∂(Mbox ℓ)) ∂(Mbox ℓ) :=
          rfl
      _ ≤ ∫⁻ w, ENNReal.ofReal (C₁ * ∫ z : E3, ‖W z‖) ∂(Mbox ℓ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict hUmeas] with w hw
          exact hinner w hw
      _ = ENNReal.ofReal (C₁ * ∫ z : E3, ‖W z‖) * (Mbox ℓ) Set.univ :=
          lintegral_const _
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUfin)

/-! ## 4. The split -/

theorem chiChiImages_split {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hRℓ : R ≤ ℓ / 4)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hWs : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → W x = 0)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
      ≤ ∑ m ∈ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)).erase 0,
          ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
              ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
                * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
                * ((W (w - y + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) * G w y‖ := by
  classical
  have hRℓ2 : R ≤ ℓ / 2 := by linarith
  have hUmeas : MeasurableSet (Box ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hUcomp : IsCompact (Box ℓ) :=
    Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ
  obtain ⟨C₀, hC₀⟩ :=
    (hUcomp.prod hUcomp).exists_bound_of_continuousOn hG.continuous.continuousOn
  set C : ℝ := max C₀ 0 with hC
  have hCnn : 0 ≤ C := le_max_right _ _
  have hGbd : ∀ w : E3, w ∈ Box ℓ → ∀ y : E3, y ∈ Box ℓ → ‖G w y‖ ≤ C := by
    intro w hw y hy
    have h1 : ‖Function.uncurry G (w, y)‖ ≤ C₀ := hC₀ (w, y) (Set.mem_prod.mpr ⟨hw, hy⟩)
    exact le_trans h1 (le_max_left _ _)
  have hGc : Continuous (Function.uncurry G) := hG.continuous
  have hIntT : ∀ m : Fin 3 → ℤ,
      Integrable (Function.uncurry (chiTerm ℓ W G m)) ((Mbox ℓ).prod (Mbox ℓ)) :=
    fun m => integrable_chiTerm hWi hCnn hGc hGbd m
  have hpoint : ∀ w y : E3, chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y
      = ∑ m ∈ Near, chiTerm ℓ W G m w y := by
    intro w y
    rw [chiChiImages_eq_finsum hℓ hRℓ2 hWs w y, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [chiTerm]
  have hIntF : Integrable (Function.uncurry (fun w y : E3 =>
      chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y))
      ((Mbox ℓ).prod (Mbox ℓ)) := by
    have hsum : Integrable (fun p : E3 × E3 =>
        ∑ m ∈ Near, Function.uncurry (chiTerm ℓ W G m) p) ((Mbox ℓ).prod (Mbox ℓ)) :=
      integrable_finsetSum Near (fun m _ => hIntT m)
    refine hsum.congr ?_
    filter_upwards with p
    simp only [Function.uncurry]
    exact (hpoint p.1 p.2).symm
  have hA : (∫ w in Box ℓ, ∫ y in Box ℓ,
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y)
      = ∫ p, Function.uncurry (fun w y : E3 =>
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y) p
          ∂((Mbox ℓ).prod (Mbox ℓ)) :=
    (integral_prod _ hIntF).symm
  have hB : (∫ p, Function.uncurry (fun w y : E3 =>
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y) p
        ∂((Mbox ℓ).prod (Mbox ℓ)))
      = ∫ p, (∑ m ∈ Near, Function.uncurry (chiTerm ℓ W G m) p)
          ∂((Mbox ℓ).prod (Mbox ℓ)) := by
    refine integral_congr_ae ?_
    filter_upwards with p
    simp only [Function.uncurry]
    exact hpoint p.1 p.2
  have hCs : (∫ p, (∑ m ∈ Near, Function.uncurry (chiTerm ℓ W G m) p)
        ∂((Mbox ℓ).prod (Mbox ℓ)))
      = ∑ m ∈ Near, ∫ p, Function.uncurry (chiTerm ℓ W G m) p
          ∂((Mbox ℓ).prod (Mbox ℓ)) :=
    integral_finsetSum Near (fun m _ => hIntT m)
  have hD : ∀ m : Fin 3 → ℤ, (∫ w in Box ℓ, ∫ y in Box ℓ, chiTerm ℓ W G m w y)
      = ∫ p, Function.uncurry (chiTerm ℓ W G m) p ∂((Mbox ℓ).prod (Mbox ℓ)) :=
    fun m => (integral_prod _ (hIntT m)).symm
  have hmain : (∫ w in Box ℓ, ∫ y in Box ℓ,
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y)
      = ∑ m ∈ Near, ∫ w in Box ℓ, ∫ y in Box ℓ, chiTerm ℓ W G m w y := by
    rw [hA, hB, hCs]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    exact (hD m).symm
  calc ‖∫ w in Box ℓ, ∫ y in Box ℓ,
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
      = ‖∑ m ∈ Near, ∫ w in Box ℓ, ∫ y in Box ℓ, chiTerm ℓ W G m w y‖ := by rw [hmain]
    _ ≤ ∑ m ∈ Near, ‖∫ w in Box ℓ, ∫ y in Box ℓ, chiTerm ℓ W G m w y‖ := norm_sum_le _ _
    _ = ∑ m ∈ Near, ‖∫ w in Box ℓ, ∫ y in Box ℓ,
          ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
            * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) * G w y‖ := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        simp only [chiTerm]

end

end Work.BoseBoxFock.L1Tails
