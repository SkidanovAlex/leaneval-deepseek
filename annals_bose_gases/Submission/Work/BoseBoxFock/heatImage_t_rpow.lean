import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.integrable_kinFT_mom_triple
import Submission.Work.BoseBoxFock.touchingSum_fourierForm
import Submission.Work.BoseFixB3.HighMassAux.parseval_L1L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.heatImage_t_rpow`

The `t`-integration of the heat-weighted momentum integral of the kinetic Fourier transform
against the touching-image cosine:

    ∫_{t>0} t^{-3/2} ∫_p ‖kinFT g p‖² e^{-t‖p‖²} cos⟪ℓ•latVec m, p⟫ dp dt
      = -(2√π) ∫_p ‖kinFT g p‖² ‖p‖ cos⟪ℓ•latVec m, p⟫ dp        (`m ≠ 0`),

for `g` smooth with `tsupport g ⊆ closedBall 0 (ℓ/2)`.

## Route

Write `a = ℓ • latVec m`, `F p = ‖kinFT g p‖²`, `Z(t) = ∫_p F p e^{-t‖p‖²} cos⟪a,p⟫`.

* **The zero mode** (`heatCosZeroMode`): `Z(0) = ∫_p F p cos⟪a,p⟫ = 0`.  The Parseval pairing
  `Work.BoseFixB3.HighMassAux.kinFT_parseval_c` applied to the pair `(g(·-a), g)` gives
  `∫_p ⟪kinFT (g(·-a)) p, kinFT g p⟫ = (2π)³ ∫_x ⟪g(x-a), g x⟫`; by the shift lemma
  `kinFT (g(·-a)) p = e^{-i⟪a,p⟫} kinFT g p` (`kinFT_sub_right`) the left side has real part
  `Z(0)`, and the right side is `(2π)³ · (autocorr g a).re = (2π)³ · aliasKernel g a = 0`
  (`aliasKernel_latVec_eq_zero_closed`: the two support balls touch at most).
* **The swap** (`heatCosFubini`): the doubly iterated integral of
  `t^{-3/2} F(p) cos⟪a,p⟫ (e^{-t‖p‖²} - 1)` is absolutely convergent — it is dominated by the
  product of the integrable functions `min (t^{-1/2}) (t^{-3/2})` and `(1+‖p‖²)F p` — so Fubini
  applies; combined with `Z(0) = 0` this identifies the `t`-integral with the iterated form.
* **The pointwise `t`-integral** (`heatCos_tper`): `∫_{t>0} t^{-3/2}(e^{-tc}-1) dt = -2√π √c`,
  the sign-reversed form of the subordination `Work.BoseBoxFock.SqrtKin.subordination_rpow`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. The translation covariance of the `p`-convention Fourier transform -/

/-- The shift lemma: translating the state by `-a` multiplies `kinFT` by the phase `e^{-i⟪a,p⟫}`. -/
theorem kinFT_sub_right (g : E3 → ℂ) (a p : E3) :
    Submission.BoseGases.kinFT (fun z => g (z - a)) p
      = Complex.exp (-(Complex.I * (inner ℝ a p : ℂ))) * Submission.BoseGases.kinFT g p := by
  have h1 : (fun z : E3 => g (z - a)) = fun z : E3 => g (z + (-a)) := by
    funext z; rw [sub_eq_add_neg]
  rw [h1, Work.BSKinetic.Decomp.kinFT_comp_add]
  congr 2
  rw [inner_neg_right, real_inner_comm a p]
  push_cast
  ring

/-! ## 2. The integrability of the `t`-majorant `min t^{-1/2} t^{-3/2}` -/

/-- `t ↦ min (t^{-1/2}) (t^{-3/2})` is integrable on `(0,∞)`: it equals `t^{-1/2}` on `(0,1]` and
`t^{-3/2}` on `(1,∞)`. -/
theorem integrableOn_min_rpow :
    IntegrableOn (fun t : ℝ => min (t ^ (-(1 : ℝ) / 2)) (t ^ (-(3 : ℝ) / 2))) (Set.Ioi 0) := by
  have hIoc : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Set.Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr
      ((intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)).mpr
        (by norm_num))
  have hIoi : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hset : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro h
      rcases le_or_gt t 1 with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr h1
    · rintro (⟨h, _⟩ | h)
      · exact h
      · linarith
  rw [hset]
  refine integrableOn_union.mpr ⟨?_, ?_⟩
  · refine hIoc.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    have hle : t ^ (-(1 : ℝ) / 2) ≤ t ^ (-(3 : ℝ) / 2) := by
      have hinv : 1 ≤ t⁻¹ := (one_le_inv₀ ht0).mpr ht.2
      calc t ^ (-(1 : ℝ) / 2) = t ^ (-(1 : ℝ) / 2) * 1 := (mul_one _).symm
        _ ≤ t ^ (-(1 : ℝ) / 2) * t⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg ht0.le _)
        _ = t ^ (-(3 : ℝ) / 2) := by
            rw [← Real.rpow_neg_one t, ← Real.rpow_add ht0]
            congr 1
            norm_num
    rw [min_eq_left hle]
  · refine hIoi.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hle : t ^ (-(3 : ℝ) / 2) ≤ t ^ (-(1 : ℝ) / 2) := by
      have hinv : t⁻¹ ≤ 1 := (inv_le_one₀ ht0).mpr ht.le
      calc t ^ (-(3 : ℝ) / 2) = t ^ (-(1 : ℝ) / 2) * t⁻¹ := by
            rw [← Real.rpow_neg_one t, ← Real.rpow_add ht0]
            congr 1
            norm_num
        _ ≤ t ^ (-(1 : ℝ) / 2) * 1 :=
            mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg ht0.le _)
        _ = t ^ (-(1 : ℝ) / 2) := mul_one _
    rw [min_eq_right hle]

/-! ## 3. The zero mode `∫_p ‖kinFT g p‖² cos⟪a,p⟫ = 0` -/

/-- **The vanishing of the zero mode.**  For `g` smooth with `tsupport g ⊆ closedBall 0 (ℓ/2)` and
`m ≠ 0` the cosine moment of `p ↦ ‖kinFT g p‖²` at the lattice image `ℓ • latVec m` vanishes. -/
theorem heatCosZeroMode {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
        Real.cos (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p)) = 0 := by
  set a : E3 := ℓ • latVec m with ha
  have hgc : HasCompactSupport g := hcc_of_closedBall hgsupp
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hg1 : MemLp g 1 volume := MeasureTheory.memLp_one_iff_integrable.mpr hgint
  have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  -- the shifted state `G z = g (z - a)`
  have hGcont : Continuous (fun z : E3 => g (z - a)) :=
    hg.continuous.comp (continuous_id.sub continuous_const)
  have hGcs : HasCompactSupport (fun z : E3 => g (z - a)) := by
    have h := hgc.comp_homeomorph (Homeomorph.subRight a)
    simpa [Function.comp_def, Homeomorph.coe_subRight] using h
  have hGint : Integrable (fun z : E3 => g (z - a)) :=
    hGcont.integrable_of_hasCompactSupport hGcs
  have hG1 : MemLp (fun z : E3 => g (z - a)) 1 volume :=
    MeasureTheory.memLp_one_iff_integrable.mpr hGint
  have hG2 : MemLp (fun z : E3 => g (z - a)) 2 volume :=
    hGcont.memLp_of_hasCompactSupport hGcs
  -- Parseval for the pair `(g(·-a), g)`
  have hpar := Work.BoseFixB3.HighMassAux.kinFT_parseval_c hG1 hG2 hg1 hg2
  -- integrability of the momentum pairing
  have hintL : Integrable (fun p : E3 => inner ℂ
      (Submission.BoseGases.kinFT (fun z : E3 => g (z - a)) p)
      (Submission.BoseGases.kinFT g p)) :=
    Work.BoseFixB3.HighMassAux.integrable_inner_kinFT hG1 hG2 hg1 hg2
  -- the pointwise formula for the momentum pairing
  have hLpt : ∀ p : E3, (inner ℂ (Submission.BoseGases.kinFT (fun z : E3 => g (z - a)) p)
        (Submission.BoseGases.kinFT g p)).re
      = ‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.cos (inner ℝ a p) := by
    intro p
    rw [kinFT_sub_right g a p, RCLike.inner_apply, map_mul]
    have hconj : (starRingEnd ℂ) (Complex.exp (-(Complex.I * (inner ℝ a p : ℂ))))
        = Complex.exp (Complex.I * (inner ℝ a p : ℂ)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hconj]
    have hww : Submission.BoseGases.kinFT g p *
        (starRingEnd ℂ) (Submission.BoseGases.kinFT g p)
        = ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hz : Submission.BoseGases.kinFT g p *
          (Complex.exp (Complex.I * (inner ℝ a p : ℂ)) *
            (starRingEnd ℂ) (Submission.BoseGases.kinFT g p))
        = Complex.exp (Complex.I * (inner ℝ a p : ℂ)) *
            ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) := by
      rw [show Submission.BoseGases.kinFT g p *
            (Complex.exp (Complex.I * (inner ℝ a p : ℂ)) *
              (starRingEnd ℂ) (Submission.BoseGases.kinFT g p))
          = Complex.exp (Complex.I * (inner ℝ a p : ℂ)) *
              (Submission.BoseGases.kinFT g p *
                (starRingEnd ℂ) (Submission.BoseGases.kinFT g p)) from by ring,
        hww]
    rw [hz]
    have hsplit : (Complex.exp (Complex.I * (inner ℝ a p : ℂ)) *
          ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ)).re
        = (Complex.exp (Complex.I * (inner ℝ a p : ℂ))).re *
            ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hsplit, Complex.exp_re]
    have hr : (Complex.I * (inner ℝ a p : ℂ)).re = 0 := by simp [Complex.mul_re]
    have hi : (Complex.I * (inner ℝ a p : ℂ)).im = inner ℝ a p := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hr, hi, Real.exp_zero, one_mul]
    ring
  -- the value of the momentum integral
  have hL : (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
        Real.cos (inner ℝ a p))
      = (∫ p : E3, inner ℂ (Submission.BoseGases.kinFT (fun z : E3 => g (z - a)) p)
          (Submission.BoseGases.kinFT g p)).re :=
    (integral_congr_ae (Filter.Eventually.of_forall hLpt)).symm.trans (integral_re hintL)
  -- the position-space integral is the autocorrelation
  have hR1 : (∫ x : E3, inner ℂ ((fun z : E3 => g (z - a)) x) (g x)) = autocorr g a := by
    have hpt : ∀ x : E3, inner ℂ ((fun z : E3 => g (z - a)) x) (g x)
        = g x * (starRingEnd ℂ) (g (x - a)) := by
      intro x
      rw [RCLike.inner_apply, mul_comm]
    rw [show (∫ x : E3, inner ℂ ((fun z : E3 => g (z - a)) x) (g x))
        = ∫ x : E3, g x * (starRingEnd ℂ) (g (x - a)) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rfl
  have hR2 : ((∫ x : E3, inner ℂ ((fun z : E3 => g (z - a)) x) (g x))).re
      = aliasKernel g a := by
    rw [hR1]
    rfl
  -- combine
  have hmain : (∫ p : E3, inner ℂ (Submission.BoseGases.kinFT (fun z : E3 => g (z - a)) p)
        (Submission.BoseGases.kinFT g p)).re
      = (2 * Real.pi) ^ 3 * aliasKernel g a := by
    have h := congrArg Complex.re hpar
    rw [Complex.re_ofReal_mul] at h
    rw [h, hR2]
  have hfin : aliasKernel g a = 0 := by
    simp only [ha]
    exact aliasKernel_latVec_eq_zero_closed hℓ hg hgsupp hm
  rw [hL, hmain, hfin, mul_zero]

/-! ## 4. The pointwise `t`-integral -/

/-- `∫_{t>0} t^{-3/2}(e^{-tc}-1) dt = -2√π √c` for `c ≥ 0` (sign-reversed subordination). -/
theorem heatCos_tper (c : ℝ) (hc : 0 ≤ c) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * (Real.exp (-(t * c)) - 1))
      = -(2 * Real.sqrt Real.pi) * Real.sqrt c := by
  have h1 : (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) * (Real.exp (-(t * c)) - 1))
      = -(∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-(c * t))) * t ^ (-(3 : ℝ) / 2)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    have he : Real.exp (-(t * c)) = Real.exp (-(c * t)) := by rw [mul_comm t c]
    rw [he]
    ring
  rw [h1, SqrtKin.subordination_rpow c hc]
  ring

/-! ## 5. The Fubini swap of the `(t,p)` double integral -/

/-- **The `t`-`p` Fubini swap.**  For `g` smooth with compact support and `m ≠ 0`, the doubly
iterated integral of `t^{-3/2}‖kinFT g p‖² cos⟪ℓ•latVec m,p⟫(e^{-t‖p‖²}-1)` may be exchanged. -/
theorem heatCosFubini {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
        (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
          Real.cos (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p) *
          (Real.exp (-(t * ‖p‖ ^ 2)) - 1)))
      = ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
          Real.cos (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p) *
          (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
            (Real.exp (-(t * ‖p‖ ^ 2)) - 1)) := by
  set a : E3 := ℓ • latVec m with ha
  obtain ⟨hFint, hFm2, _⟩ := integrable_kinFT_mom_triple (t := 1) one_pos hg hgc
  -- the separable majorant
  have hPa : Integrable (fun p : E3 => (1 + ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    have h := hFint.add hFm2
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.add_apply]
    ring
  have hmaj : Integrable
      (fun x : ℝ × E3 => min (x.1 ^ (-(1 : ℝ) / 2)) (x.1 ^ (-(3 : ℝ) / 2)) *
        ((1 + ‖x.2‖ ^ 2) * ‖Submission.BoseGases.kinFT g x.2‖ ^ 2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
    integrableOn_min_rpow.mul_prod hPa
  -- the pointwise domination, for `t > 0`
  have hbound : ∀ t : ℝ, 0 < t → ∀ p : E3,
      ‖t ^ (-(3 : ℝ) / 2) * (‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.cos (inner ℝ a p) *
          (Real.exp (-(t * ‖p‖ ^ 2)) - 1))‖
        ≤ min (t ^ (-(1 : ℝ) / 2)) (t ^ (-(3 : ℝ) / 2)) *
            ((1 + ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    intro t ht p
    have hFnn : 0 ≤ ‖Submission.BoseGases.kinFT g p‖ ^ 2 := sq_nonneg _
    have hcnn : 0 ≤ ‖p‖ ^ 2 := sq_nonneg _
    have htnn : 0 ≤ t ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg ht.le _
    have hminnn : 0 ≤ min (t ^ (-(1 : ℝ) / 2)) (t ^ (-(3 : ℝ) / 2)) :=
      le_min (Real.rpow_nonneg ht.le _) htnn
    have hargnn : 0 ≤ (1 + ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
      mul_nonneg (by linarith [hcnn]) hFnn
    have h1m : 0 ≤ 1 - Real.exp (-(t * ‖p‖ ^ 2)) := by
      rw [sub_nonneg, Real.exp_le_one_iff]
      exact neg_nonpos.mpr (mul_nonneg ht.le hcnn)
    have hnonpos : Real.exp (-(t * ‖p‖ ^ 2)) - 1 ≤ 0 := by
      have := Real.exp_pos (-(t * ‖p‖ ^ 2)); linarith
    -- the elementary `t`-inequality `t^{-3/2}(1-e^{-tc}) ≤ min(t^{-1/2},t^{-3/2})(1+c)`
    have hcore : t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))
        ≤ min (t ^ (-(1 : ℝ) / 2)) (t ^ (-(3 : ℝ) / 2)) * (1 + ‖p‖ ^ 2) := by
      have h1 : 1 - Real.exp (-(t * ‖p‖ ^ 2)) ≤ t * ‖p‖ ^ 2 := by
        have h := Real.add_one_le_exp (-(t * ‖p‖ ^ 2))
        have hp := Real.exp_pos (-(t * ‖p‖ ^ 2))
        linarith
      have h2 : 1 - Real.exp (-(t * ‖p‖ ^ 2)) ≤ 1 := by
        have hp := Real.exp_pos (-(t * ‖p‖ ^ 2))
        linarith
      have h3 : t ^ (-(3 : ℝ) / 2) * (t * ‖p‖ ^ 2) = t ^ (-(1 : ℝ) / 2) * ‖p‖ ^ 2 := by
        calc t ^ (-(3 : ℝ) / 2) * (t * ‖p‖ ^ 2)
            = t ^ (-(3 : ℝ) / 2) * (t ^ (1 : ℝ) * ‖p‖ ^ 2) := by rw [Real.rpow_one]
          _ = t ^ (-(3 : ℝ) / 2) * t ^ (1 : ℝ) * ‖p‖ ^ 2 := by ring
          _ = t ^ (-(3 : ℝ) / 2 + 1) * ‖p‖ ^ 2 := by rw [Real.rpow_add ht]
          _ = t ^ (-(1 : ℝ) / 2) * ‖p‖ ^ 2 := by
              congr 1
              norm_num
      have h4 : t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))
          ≤ t ^ (-(1 : ℝ) / 2) * ‖p‖ ^ 2 := by
        calc t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))
            ≤ t ^ (-(3 : ℝ) / 2) * (t * ‖p‖ ^ 2) := mul_le_mul_of_nonneg_left h1 htnn
          _ = t ^ (-(1 : ℝ) / 2) * ‖p‖ ^ 2 := h3
      have h5 : t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))
          ≤ t ^ (-(3 : ℝ) / 2) := by
        calc t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))
            ≤ t ^ (-(3 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left h2 htnn
          _ = t ^ (-(3 : ℝ) / 2) := mul_one _
      rcases le_total (t ^ (-(1 : ℝ) / 2)) (t ^ (-(3 : ℝ) / 2)) with h | h
      · rw [min_eq_left h]
        exact le_trans h4 (mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg ht.le _))
      · rw [min_eq_right h]
        refine le_trans h5 ?_
        simpa using mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + ‖p‖ ^ 2 by linarith) htnn
    -- the two norms
    have hnormL : ‖t ^ (-(3 : ℝ) / 2) * (‖Submission.BoseGases.kinFT g p‖ ^ 2 *
          Real.cos (inner ℝ a p) * (Real.exp (-(t * ‖p‖ ^ 2)) - 1))‖
        = t ^ (-(3 : ℝ) / 2) * (‖Submission.BoseGases.kinFT g p‖ ^ 2 *
            |Real.cos (inner ℝ a p)| * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg htnn, abs_of_nonneg hFnn,
        abs_of_nonpos hnonpos]
      ring
    rw [hnormL]
    calc t ^ (-(3 : ℝ) / 2) * (‖Submission.BoseGases.kinFT g p‖ ^ 2 *
            |Real.cos (inner ℝ a p)| * (1 - Real.exp (-(t * ‖p‖ ^ 2))))
        = (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
            (‖Submission.BoseGases.kinFT g p‖ ^ 2 * |Real.cos (inner ℝ a p)|) := by ring
      _ ≤ (t ^ (-(3 : ℝ) / 2) * (1 - Real.exp (-(t * ‖p‖ ^ 2)))) *
            ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg htnn h1m)
          exact mul_le_of_le_one_right hFnn (Real.abs_cos_le_one _)
      _ ≤ (min (t ^ (-(1 : ℝ) / 2)) (t ^ (-(3 : ℝ) / 2)) * (1 + ‖p‖ ^ 2)) *
            ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcore hFnn
      _ = min (t ^ (-(1 : ℝ) / 2)) (t ^ (-(3 : ℝ) / 2)) *
            ((1 + ‖p‖ ^ 2) * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by ring
  -- joint integrability
  have hH : Integrable (Function.uncurry (fun (t : ℝ) (p : E3) =>
      t ^ (-(3 : ℝ) / 2) * (‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.cos (inner ℝ a p) *
        (Real.exp (-(t * ‖p‖ ^ 2)) - 1))))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    refine Integrable.mono' hmaj ?_ ?_
    · have h1 : AEStronglyMeasurable (fun x : ℝ × E3 => x.1 ^ (-(3 : ℝ) / 2))
          ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
        (by fun_prop : Measurable (fun x : ℝ × E3 => x.1 ^ (-(3 : ℝ) / 2))).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun x : ℝ × E3 => ‖Submission.BoseGases.kinFT g x.2‖ ^ 2)
          ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
        hFint.aestronglyMeasurable.comp_snd
      have h3 : AEStronglyMeasurable (fun x : ℝ × E3 => Real.cos (inner ℝ a x.2))
          ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
        (by fun_prop : Continuous (fun x : ℝ × E3 =>
          Real.cos (inner ℝ a x.2))).aestronglyMeasurable
      have h4 : AEStronglyMeasurable (fun x : ℝ × E3 => Real.exp (-(x.1 * ‖x.2‖ ^ 2)) - 1)
          ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
        (by fun_prop : Continuous (fun x : ℝ × E3 =>
          Real.exp (-(x.1 * ‖x.2‖ ^ 2)) - 1)).aestronglyMeasurable
      exact h1.mul ((h2.mul h3).mul h4)
    · have hae : ∀ᵐ x ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure E3)),
          0 < x.1 := by
        refine (MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun x : ℝ × E3 => 0 < x.1) ?_).mpr ?_
        · exact (isOpen_lt continuous_const continuous_fst).measurableSet
        · filter_upwards [MeasureTheory.self_mem_ae_restrict (μ := volume)
            (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi] with t ht
          exact Filter.Eventually.of_forall (fun y => ht)
      filter_upwards [hae] with x hx
      exact hbound x.1 hx x.2
  -- the swap
  have hswap := MeasureTheory.integral_integral_swap hH
  -- pull the `t`-weight inside the inner integral
  have hstep1 : (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
        (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.cos (inner ℝ a p) *
          (Real.exp (-(t * ‖p‖ ^ 2)) - 1)))
      = ∫ t in Set.Ioi (0 : ℝ), ∫ p : E3, t ^ (-(3 : ℝ) / 2) *
          (‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.cos (inner ℝ a p) *
            (Real.exp (-(t * ‖p‖ ^ 2)) - 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [integral_const_mul]
  -- pull the `p`-weight outside the swapped inner integral
  have hstep2 : (∫ p : E3, ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
        (‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.cos (inner ℝ a p) *
          (Real.exp (-(t * ‖p‖ ^ 2)) - 1)))
      = ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.cos (inner ℝ a p) *
          (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
            (Real.exp (-(t * ‖p‖ ^ 2)) - 1)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only
    rw [show (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
          (‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.cos (inner ℝ a p) *
            (Real.exp (-(t * ‖p‖ ^ 2)) - 1)))
        = ∫ t in Set.Ioi (0 : ℝ), (‖Submission.BoseGases.kinFT g p‖ ^ 2 *
            Real.cos (inner ℝ a p)) * (t ^ (-(3 : ℝ) / 2) *
              (Real.exp (-(t * ‖p‖ ^ 2)) - 1)) from
      setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)]
    rw [integral_const_mul]
  rw [hstep1, hswap, hstep2]

/-! ## 6. The main theorem -/

theorem heatImage_t_rpow {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
        (∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
          Real.exp (-(t * ‖p‖ ^ 2)) *
            Real.cos (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p)))
      = -(2 * Real.sqrt Real.pi) *
        ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2 * ‖p‖ *
          Real.cos (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p) := by
  have hgc : HasCompactSupport g := hcc_of_closedBall hgsupp
  obtain ⟨hFint, hFm2, _⟩ := integrable_kinFT_mom_triple (t := 1) one_pos hg hgc
  have hZ0 := heatCosZeroMode hℓ hg hgsupp hm
  have hFcos : Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
      Real.cos (inner ℝ (ℓ • latVec m) p)) :=
    hFint.mul_bdd
      ((by fun_prop : Continuous
        (fun p : E3 => Real.cos (inner ℝ (ℓ • latVec m) p))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _))
  -- step 1: `Z(t) = Z(t) - Z(0)`
  have hstep : ∀ t : ℝ, 0 < t →
      (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.exp (-(t * ‖p‖ ^ 2)) *
          Real.cos (inner ℝ (ℓ • latVec m) p))
        = ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
            Real.cos (inner ℝ (ℓ • latVec m) p) * (Real.exp (-(t * ‖p‖ ^ 2)) - 1) := by
    intro t ht
    have hA : Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
        Real.cos (inner ℝ (ℓ • latVec m) p) * Real.exp (-(t * ‖p‖ ^ 2))) :=
      hFcos.mul_bdd
        ((by fun_prop : Continuous
          (fun p : E3 => Real.exp (-(t * ‖p‖ ^ 2)))).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun p => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
          exact neg_nonpos.mpr (mul_nonneg ht.le (sq_nonneg _))))
    have hsplit : (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
          Real.cos (inner ℝ (ℓ • latVec m) p) * (Real.exp (-(t * ‖p‖ ^ 2)) - 1))
        = (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
            Real.cos (inner ℝ (ℓ • latVec m) p) * Real.exp (-(t * ‖p‖ ^ 2)))
          - (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
            Real.cos (inner ℝ (ℓ • latVec m) p)) := by
      rw [← integral_sub hA hFcos]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))
    rw [hsplit, hZ0, sub_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))
  calc (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
        (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 * Real.exp (-(t * ‖p‖ ^ 2)) *
          Real.cos (inner ℝ (ℓ • latVec m) p)))
      = ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
          (∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
            Real.cos (inner ℝ (ℓ • latVec m) p) * (Real.exp (-(t * ‖p‖ ^ 2)) - 1)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [hstep t ht])
    _ = ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
          Real.cos (inner ℝ (ℓ • latVec m) p) *
          (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ) / 2) *
            (Real.exp (-(t * ‖p‖ ^ 2)) - 1)) := heatCosFubini hℓ hg hgc hm
    _ = ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 *
          Real.cos (inner ℝ (ℓ • latVec m) p) * (-(2 * Real.sqrt Real.pi) * ‖p‖) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only
        rw [heatCos_tper (‖p‖ ^ 2) (sq_nonneg _), Real.sqrt_sq (norm_nonneg p)]
    _ = -(2 * Real.sqrt Real.pi) *
        ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 * ‖p‖ *
          Real.cos (inner ℝ (ℓ • Work.BoseBoxFock.latVec m) p) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only
        ring

end Work.BoseBoxFock
