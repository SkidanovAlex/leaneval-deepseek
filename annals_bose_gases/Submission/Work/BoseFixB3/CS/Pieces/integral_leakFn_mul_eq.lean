import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.integrable_ind_mul_lowMult_int
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.integral_leakFn_mul_eq`

Self-adjointness of the box-truncated low-momentum multiplier `lowMult fc κ ℓ` (= FS's
`f_L(√−Δ)`, the free Fourier multiplier `f(‖p‖/κ)` applied to the extension by `0` of the box
restriction) at the level of the box integrals:

    ∫_{Λ} leakFn·G = ∫_{Λ} (G − lowMult G),        leakFn = 1 − lowMult (fun _ => 1),

for `G` integrable with `tsupport G ⊆ Λ = acube ℓ`.  Since `leakFn = 1 − lowMult 1`, this is
equivalent to `⟨lowMult 1, G⟩_Λ = ⟨lowMult G, 1⟩_Λ`, i.e. to the symmetry of the real,
even-symbol multiplier, which is proved here by writing both sides as momentum-space pairings
(`HighMassAux.lowMult_pairing`, applied once with `φ = G`, `Ψ = 1` and once with `φ = 1_Λ`,
`Ψ = G`) and comparing the `p`-integrands pointwise.

The only integrability input beyond the two pairings is that `1_Λ · lowMult G` is integrable
(`CS/Pieces/integrable_ind_mul_lowMult_int`); `1_Λ · G` and `1_Λ · (lowMult 1 · G)` are
integrable by the hypotheses (`hInt` and `hG`).
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `Re(conj a · r · b) = Re(conj b · r · a)` for real `r`. -/
lemma re_conj_mul_mul_comm (a b : ℂ) (r : ℝ) :
    (starRingEnd ℂ a * (r : ℂ) * b).re = (starRingEnd ℂ b * (r : ℂ) * a).re := by
  rw [show starRingEnd ℂ a * (r : ℂ) * b = (r : ℂ) * (starRingEnd ℂ a * b) from by ring,
    show starRingEnd ℂ b * (r : ℂ) * a = (r : ℂ) * (starRingEnd ℂ b * a) from by ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  congr 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The set integral over the centred cube is the full-space integral against its indicator. -/
lemma integral_cubInd_mul (ℓ : ℝ) (F : E3 → ℝ) :
    (∫ y, (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) y * F y)
      = ∫ y in Submission.BoseGases.acube ℓ, F y := by
  have h1 : (fun y : E3 => (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) y * F y)
      = (Submission.BoseGases.acube ℓ).indicator F := by
    funext y
    by_cases h : y ∈ Submission.BoseGases.acube ℓ
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [h1, MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]

theorem integral_leakFn_mul_eq (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {G : EuclideanSpace ℝ (Fin 3) → ℝ} (hG : MeasureTheory.Integrable G)
    (hGsupp : tsupport G ⊆ Submission.BoseGases.acube ℓ)
    (hInt : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y)) :
    ∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y
      = ∫ y in Submission.BoseGases.acube ℓ,
          (G y - Work.BoseBoxFix.lowMult fc κ ℓ G y) := by
  classical
  set ind : E3 → ℝ := (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) with hind
  have hac : MeasurableSet (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_measurable ℓ
  have hΛc : IsCompact (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_compact hℓ
  have hΛtop : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Submission.BoseGases.acube_lt_top ℓ hℓ.le
  have hind_notMem : ∀ y, y ∉ Submission.BoseGases.acube ℓ → ind y = 0 := by
    intro y hy; simp [hind, Set.indicator_of_notMem hy]
  have hGzero : ∀ y, y ∉ Submission.BoseGases.acube ℓ → G y = 0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hGsupp h))
  have hindG : ∀ y, ind y * G y = G y := by
    intro y
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · simp [hind, Set.indicator_of_mem hy]
    · rw [hind_notMem y hy, hGzero y hy, zero_mul]
  have hind_int : Integrable ind := by
    have h : MeasureTheory.MemLp ((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)))
        1 (volume : Measure E3) :=
      MeasureTheory.memLp_indicator_const (μ := (volume : Measure E3)) 1 hac (1 : ℝ) (Or.inr hΛtop.ne)
    simpa [hind] using MeasureTheory.memLp_one_iff_integrable.mp h
  have hind_cs : HasCompactSupport ind := by
    show IsCompact (tsupport ind)
    refine hΛc.of_isClosed_subset (isClosed_tsupport ind) ?_
    refine closure_minimal ?_ hΛc.isClosed
    intro y hy
    by_contra h
    exact hy (hind_notMem y h)
  have hG_cs : HasCompactSupport G := by
    show IsCompact (tsupport G)
    exact hΛc.of_isClosed_subset (isClosed_tsupport G) hGsupp
  have hG_intOn : IntegrableOn G (Submission.BoseGases.acube ℓ) := hG.integrableOn
  have hOne_intOn : IntegrableOn Work.BoseFixB3.CS.oneFn (Submission.BoseGases.acube ℓ) := by
    rw [← MeasureTheory.integrable_indicator_iff hac]
    have h2 : (Submission.BoseGases.acube ℓ).indicator Work.BoseFixB3.CS.oneFn
        = (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) := rfl
    rw [h2]
    exact MeasureTheory.memLp_one_iff_integrable.mp
      (MeasureTheory.memLp_indicator_const (μ := (volume : Measure E3)) 1 hac (1 : ℝ) (Or.inr hΛtop.ne))
  have hcs : HasCompactSupport (fun p : E3 => fc.f (‖p‖ / κ)) :=
    Work.BoseFixB3.HighMass.lowcut_symbol_hasCompactSupport hκ
  -- the Fourier transform of the box indicator of `oneFn` agrees with that of `ind`
  have hkind : (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Work.BoseFixB3.CS.oneFn z : ℝ) : ℂ))
      = fun z : E3 => ((ind z : ℝ) : ℂ) := rfl
  -- the box indicator of `G` agrees with `G` itself
  have hkindGz : (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator G z : ℝ) : ℂ))
      = fun z : E3 => (G z : ℂ) := by
    funext z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hGzero z hz]
  -- the two momentum-space pairings
  have hp1 := Work.BoseFixB3.HighMassAux.lowMult_pairing (fc := fc) (κ := κ) (ℓ := ℓ) hℓ
      (φ := G) hG hG_cs hOne_intOn hcs
  rw [hkind] at hp1
  have hp2 := Work.BoseFixB3.HighMassAux.lowMult_pairing (fc := fc) (κ := κ) (ℓ := ℓ) hℓ
      (φ := ind) hind_int hind_cs hG_intOn hcs
  rw [hkindGz] at hp2
  -- the two `p`-integrands agree pointwise (real part of a symmetric pairing, real weight)
  have hP : (∫ p : E3, ((starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z : E3 => (G z : ℂ)) p)
          * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT (fun z : E3 => ((ind z : ℝ) : ℂ)) p).re)
      = ∫ p : E3, ((starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z : E3 => ((ind z : ℝ) : ℂ)) p)
          * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT (fun z : E3 => (G z : ℂ)) p).re := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    exact re_conj_mul_mul_comm _ _ _
  -- the key identity `∫_Λ lowMult 1 · G = ∫_Λ lowMult G`
  have hkey : (∫ y : E3, ind y * (Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y * G y))
      = ∫ y : E3, ind y * Work.BoseBoxFix.lowMult fc κ ℓ G y := by
    calc ∫ y : E3, ind y * (Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y * G y)
        = ∫ y : E3, G y * Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [show ind y * (Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y * G y)
              = (ind y * G y) * Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y from by ring,
            hindG y]
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ((starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z : E3 => (G z : ℂ)) p)
            * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT (fun z : E3 => ((ind z : ℝ) : ℂ)) p).re := hp1
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ((starRingEnd ℂ) (Submission.BoseGases.kinFT (fun z : E3 => ((ind z : ℝ) : ℂ)) p)
            * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT (fun z : E3 => (G z : ℂ)) p).re := by rw [hP]
      _ = ∫ y : E3, ind y * Work.BoseBoxFix.lowMult fc κ ℓ G y := hp2.symm
  -- integrability of the three pieces
  have h1 : Integrable (fun y : E3 => ind y * G y) :=
    hG.congr (Filter.Eventually.of_forall (fun y => (hindG y).symm))
  have hA : Integrable (fun y : E3 => ind y * (Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y)) :=
    hInt.congr (Filter.Eventually.of_forall (fun y => by
      calc Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y
          = Work.BoseFixB3.CS.leakFn fc κ ℓ y * (ind y * G y) := by rw [hindG y]
        _ = ind y * (Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y) := by ring))
  have h2 : Integrable (fun y : E3 =>
      ind y * (Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y * G y)) := by
    have hD : Integrable (fun y : E3 =>
        -(ind y * (Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y) - ind y * G y)) := (hA.sub h1).neg
    refine hD.congr (Filter.Eventually.of_forall (fun y => ?_))
    unfold Work.BoseFixB3.CS.leakFn
    ring
  have h3 : Integrable (fun y : E3 => ind y * Work.BoseBoxFix.lowMult fc κ ℓ G y) := by
    simpa [hind] using integrable_ind_mul_lowMult_int (fc := fc) hκ hℓ hG_intOn
  -- the two sides
  have hL : ∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y
      = (∫ y : E3, ind y * G y)
        - ∫ y : E3, ind y * (Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y * G y) := by
    rw [show (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y)
        = ∫ y : E3, ind y * (Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y) from by
          rw [hind]
          exact (integral_cubInd_mul ℓ (fun y => Work.BoseFixB3.CS.leakFn fc κ ℓ y * G y)).symm]
    rw [← MeasureTheory.integral_sub h1 h2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    unfold Work.BoseFixB3.CS.leakFn
    ring
  have hR : ∫ y in Submission.BoseGases.acube ℓ, (G y - Work.BoseBoxFix.lowMult fc κ ℓ G y)
      = (∫ y : E3, ind y * G y) - ∫ y : E3, ind y * Work.BoseBoxFix.lowMult fc κ ℓ G y := by
    rw [show (∫ y in Submission.BoseGases.acube ℓ, (G y - Work.BoseBoxFix.lowMult fc κ ℓ G y))
        = ∫ y : E3, ind y * (G y - Work.BoseBoxFix.lowMult fc κ ℓ G y) from by
          rw [hind]
          exact (integral_cubInd_mul ℓ (fun y => G y - Work.BoseBoxFix.lowMult fc κ ℓ G y)).symm]
    rw [← MeasureTheory.integral_sub h1 h3]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    ring
  rw [hL, hR, hkey]

end Work.BoseFixB3.CS.Pieces
