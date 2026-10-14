import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RXT.st1_fb_theta
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.StabilityFar.St4
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_farStrip_holder_pos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

open Work.LWP

/-- The operator of the far-field within-derivative. -/
noncomputable def farBlock (ω : R3 → ℝ → R3) (p : R3 × ℝ) : (R3 × ℝ) →L[ℝ] R3 :=
  (fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
    + (ContinuousLinearMap.snd ℝ R3 ℝ).smulRight
        (biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1)

theorem farBlock_apply (ω : R3 → ℝ → R3) (p : R3 × ℝ) (v : R3) (s : ℝ) :
    farBlock ω p (v, s)
      = fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1 v
        + s • biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1 := by
  simp [farBlock]

/-- The `smulRight` of `snd` by a vector has operator norm at most the norm of the vector. -/
theorem norm_snd_smulRight_le (b : R3) :
    ‖(ContinuousLinearMap.snd ℝ R3 ℝ).smulRight b‖ ≤ ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b) fun w => ?_
  have hw : ‖w‖ = max ‖w.1‖ |w.2| := rfl
  rw [ContinuousLinearMap.smulRight_apply]
  calc ‖w.2 • b‖ = |w.2| * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖b‖ * max ‖w.1‖ |w.2| := by
        rw [mul_comm ‖b‖]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg b)
    _ = ‖b‖ * ‖w‖ := by rw [hw]

theorem norm_farBlock_sub_le (ω : R3 → ℝ → R3) (p q : R3 × ℝ) :
    ‖farBlock ω p - farBlock ω q‖
      ≤ ‖fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1
          - fderiv ℝ (fun z => biotSavart (fun y => ω y q.2) z) q.1‖
        + ‖biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1
          - biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1‖ := by
  have hstep : ∀ w : R3 × ℝ, (farBlock ω p - farBlock ω q) w
      = (fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1
          - fderiv ℝ (fun z => biotSavart (fun y => ω y q.2) z) q.1) w.1
        + w.2 • (biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1
          - biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1) := by
    intro w
    rw [sub_apply, farBlock_apply, farBlock_apply, sub_apply, smul_sub]
    abel
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [hstep]
  set A := fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1 with hA
  set A' := fderiv ℝ (fun z => biotSavart (fun y => ω y q.2) z) q.1 with hA'
  set b := biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1 with hb
  set b' := biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1 with hb'
  have h1 : ‖A - A'‖ * ‖w.1‖ ≤ ‖A - A'‖ * ‖w‖ :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
  have h2 : ‖b - b'‖ * |w.2| ≤ ‖b - b'‖ * ‖w‖ :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
  calc ‖(A - A') w.1 + w.2 • (b - b')‖
      ≤ ‖(A - A') w.1‖ + ‖w.2 • (b - b')‖ := norm_add_le _ _
    _ ≤ ‖A - A'‖ * ‖w.1‖ + ‖b - b'‖ * |w.2| := by
        refine add_le_add (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [norm_smul, Real.norm_eq_abs, mul_comm |w.2| ‖b - b'‖]
    _ ≤ ‖A - A'‖ * ‖w‖ + ‖b - b'‖ * ‖w‖ := add_le_add h1 h2
    _ = (‖A - A'‖ + ‖b - b'‖) * ‖w‖ := by ring

/-- **Taylor remainder in `t`.** -/
theorem timeDeriv_remainder_le {ω : R3 → ℝ → R3} {N₁ c t τ : ℝ} {y : R3} (hN₁ : 0 ≤ N₁)
    (hA : ∀ s ∈ Icc (min t τ) (max t τ),
      HasDerivAt (fun u : ℝ => ω y u) (FiniteTimeSingularity.timeDeriv ω y s) s)
    (hB : ∀ s ∈ Icc (min t τ) (max t τ),
      ‖FiniteTimeSingularity.timeDeriv ω y s - FiniteTimeSingularity.timeDeriv ω y t‖
        ≤ N₁ * |s - t| ^ c) (hc : 0 < c) :
    ‖(ω y τ - ω y t) - (τ - t) • FiniteTimeSingularity.timeDeriv ω y t‖
      ≤ N₁ * |τ - t| ^ (c + 1) := by
  set f : ℝ → R3 := fun u => ω y u - u • FiniteTimeSingularity.timeDeriv ω y t with hf
  have hconv : Convex ℝ (Icc (min t τ) (max t τ)) := convex_Icc _ _
  have hdiff : ∀ s ∈ Icc (min t τ) (max t τ), DifferentiableAt ℝ f s := by
    intro s hs
    rw [hf]
    exact ((hA s hs).differentiableAt).sub (differentiableAt_id.smul_const _)
  have hderiv : ∀ s ∈ Icc (min t τ) (max t τ),
      deriv f s = FiniteTimeSingularity.timeDeriv ω y s - FiniteTimeSingularity.timeDeriv ω y t := by
    intro s hs
    have h : HasDerivAt f (FiniteTimeSingularity.timeDeriv ω y s
        - FiniteTimeSingularity.timeDeriv ω y t) s := by
      rw [hf]
      have h1 : HasDerivAt (fun u : ℝ => ω y u) (FiniteTimeSingularity.timeDeriv ω y s) s := hA s hs
      have h2 : HasDerivAt (fun u : ℝ => u • FiniteTimeSingularity.timeDeriv ω y t)
          (FiniteTimeSingularity.timeDeriv ω y t) s := by
        simpa using (hasDerivAt_id s).smul_const (FiniteTimeSingularity.timeDeriv ω y t)
      exact h1.sub h2
    exact h.deriv
  have hbound : ∀ s ∈ Icc (min t τ) (max t τ), ‖deriv f s‖ ≤ N₁ * |τ - t| ^ c := by
    intro s hs
    rw [hderiv s hs]
    refine (hB s hs).trans ?_
    have h1 : |s - t| ≤ |τ - t| := by
      obtain ⟨hs1, hs2⟩ := hs
      rcases le_total t τ with hle | hle
      · have hts : t ≤ s := by rw [← min_eq_left hle]; exact hs1
        have hsτ : s ≤ τ := by rw [← max_eq_right hle]; exact hs2
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ τ - t),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]
        linarith
      · have hτs : τ ≤ s := by rw [← min_eq_right hle]; exact hs1
        have hst : s ≤ t := by rw [← max_eq_left hle]; exact hs2
        rw [abs_of_nonpos (by linarith : τ - t ≤ (0:ℝ)),
          abs_of_nonpos (by linarith : s - t ≤ (0:ℝ))]
        linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) h1 (le_of_lt hc)) hN₁
  have htI : t ∈ Icc (min t τ) (max t τ) := ⟨min_le_left t τ, le_max_left t τ⟩
  have hτI : τ ∈ Icc (min t τ) (max t τ) := ⟨min_le_right t τ, le_max_right t τ⟩
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconv htI hτI
  have hfeq : f τ - f t = (ω y τ - ω y t) - (τ - t) • FiniteTimeSingularity.timeDeriv ω y t := by
    rw [hf]
    module
  rw [hfeq, Real.norm_eq_abs] at hmain
  have hxy : |τ - t| ^ (c + 1) = |τ - t| ^ c * |τ - t| := by
    rcases lt_or_eq_of_le (abs_nonneg (τ - t)) with hpos | hzero
    · rw [Real.rpow_add hpos c 1, Real.rpow_one]
    · rw [← hzero, Real.zero_rpow (by linarith : c + 1 ≠ 0),
        Real.zero_rpow (ne_of_gt hc), mul_zero]
  calc ‖(ω y τ - ω y t) - (τ - t) • FiniteTimeSingularity.timeDeriv ω y t‖
      ≤ N₁ * |τ - t| ^ c * |τ - t| := hmain
    _ = N₁ * |τ - t| ^ (c + 1) := by rw [hxy, mul_assoc]

/-- `x ^ (α+1) = x ^ α * x` for `x ≥ 0`, `α > 0`. -/
lemma rpow_succ_eq {α : NNReal} (hα : 0 < (α : ℝ)) {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((α : ℝ) + 1) = x ^ (α : ℝ) * x := by
  rcases lt_or_eq_of_le hx with h | h
  · rw [Real.rpow_add h (α : ℝ) 1, Real.rpow_one]
  · rw [← h, Real.zero_rpow (by linarith : (α : ℝ) + 1 ≠ 0),
      Real.zero_rpow (ne_of_gt hα), mul_zero]

/-- The final numerical combination of the three error estimates. -/
lemma estimate_combine {α : NNReal} {C K ε r s d : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hε : 0 < ε)
    (hd : 0 ≤ d) (_hr : 0 ≤ r) (hrd : r ≤ d) (hs : 0 ≤ s) (hsd : s ≤ d)
    (h3 : r ^ (α : ℝ) ≤ ε / 3 / (C + 1)) (hKd : K * d ≤ ε / 3)
    (hrr : r ^ ((α : ℝ) + 1) ≤ r ^ (α : ℝ) * d) :
    C * r ^ ((α : ℝ) + 1) + K * r * s + ε / 3 * s ≤ ε * d := by
  have h2a : C * r ^ (α : ℝ) ≤ ε / 3 := by
    have h := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ C + 1)
    rw [div_mul_cancel₀ _ (by positivity : (C + 1) ≠ 0)] at h
    nlinarith [h, hC]
  have h1 : C * r ^ ((α : ℝ) + 1) ≤ ε / 3 * d :=
    calc C * r ^ ((α : ℝ) + 1) ≤ C * (r ^ (α : ℝ) * d) :=
          mul_le_mul_of_nonneg_left hrr hC
      _ = (C * r ^ (α : ℝ)) * d := by ring
      _ ≤ ε / 3 * d := mul_le_mul_of_nonneg_right h2a hd
  have h2 : K * r * s ≤ ε / 3 * d :=
    calc K * r * s ≤ K * d * d := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hrd hK) hsd hs ?_
          exact mul_nonneg hK hd
      _ = (K * d) * d := by ring
      _ ≤ ε / 3 * d := mul_le_mul_of_nonneg_right hKd hd
  have h4 : ε / 3 * s ≤ ε / 3 * d := mul_le_mul_of_nonneg_left hsd (by linarith)
  linarith [h1, h2, h4]

/-- **The within-derivative on the far strip.** -/
theorem hasFDerivWithinAt_farStrip {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : R3 → ℝ → R3} {R S : ℝ} (hS : 0 < S) (hbun : BSAdmissibleStripFull α ω R S) :
    ∀ p ∈ Work.StabilityFar.farRegion (2 * R + 5) ×ˢ Set.Icc (0:ℝ) S,
      HasFDerivWithinAt (fun q : R3 × ℝ => biotSavart (fun y => ω y q.2) q.1) (farBlock ω p)
        (Work.StabilityFar.farRegion (2 * R + 5) ×ˢ Set.Icc (0:ℝ) S) p := by
  intro p hp
  have hsuppD := slicesSupportedStrip_timeDeriv hS hbun
  obtain ⟨⟨hRpos, hsupp, ⟨M, hMb⟩, ⟨H, hHb⟩, ⟨N, hNb⟩, hmeas⟩,
    ⟨hdc, ⟨M₁, hM₁b⟩, hmeasD⟩, ⟨N₁, hN₁b⟩⟩ := hbun
  obtain ⟨x, t⟩ := p
  simp only [Work.StabilityFar.mem_farRegion, Set.mem_prod, Set.mem_Icc] at hp
  obtain ⟨hx, ht⟩ := hp
  have hx2 : 2 * R ≤ ‖x‖ := by linarith
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hM₁0 : 0 ≤ max M₁ 0 := le_max_right _ _
  have hN₀ : 0 ≤ max N 0 := le_max_right _ _
  have hN₁0 : 0 ≤ max N₁ 0 := le_max_right _ _
  have hRnn : 0 ≤ R := hRpos.le
  have hαnn : 0 ≤ (α : ℝ) := le_of_lt hα
  rw [hasFDerivWithinAt_iff_isLittleOTVS, Asymptotics.isLittleOTVS_iff_isLittleO,
    Asymptotics.isLittleO_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  have hε3nn : 0 ≤ ε / 3 := le_of_lt hε3
  -- ### the per-slice far differentiability at `(x,t)`
  have hfar := Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far (ω := fun y => ω y t) hRpos hM0
    (fun y => le_trans (hMb t ht y) (le_max_left _ _)) (fun y => hsupp t ht y) (hmeas t ht) hx2
  have hevent : ∀ᶠ z in 𝓝 x, ‖biotSavart (fun y => ω y t) z - biotSavart (fun y => ω y t) x
      - fderiv ℝ (fun z => biotSavart (fun y => ω y t) z) x (z - x)‖ ≤ (ε / 3) * ‖z - x‖ := by
    have h := (Asymptotics.isLittleO_iff.mp hfar.2.isLittleO) hε3
    filter_upwards [h] with z hz
    rwa [hfar.2.fderiv]
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.mp hevent
  -- ### the Lipschitz bound for the `∂ₜ`-block near `x`
  have hlip := Work.LWP.BiotSavart.biotSavart_lipschitzOn_far hRnn hM₁0
    (fun z => le_trans (hM₁b t ht z) (le_max_left _ _)) (fun z hz => hsuppD t ht z hz)
    (hmeasD t ht) hx2
  rw [lipschitzOnWith_iff_norm_sub_le] at hlip
  -- ### the Taylor remainder in `t`
  have hrem : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : R3,
      ‖(ω z τ - ω z t) - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t‖
        ≤ max N₁ 0 * |τ - t| ^ ((α : ℝ) + 1) := by
    intro τ hτ z
    refine timeDeriv_remainder_le (ω := ω) (N₁ := max N₁ 0) (c := (α : ℝ)) (t := t) (τ := τ)
      (y := z) hN₁0 ?_ ?_ hα
    · intro s hs
      exact hdc s ⟨le_trans (le_min ht.1 hτ.1) hs.1, le_trans hs.2 (max_le ht.2 hτ.2)⟩ z
    · intro s hs
      have hsI : s ∈ Set.Icc (0:ℝ) S :=
        ⟨le_trans (le_min ht.1 hτ.1) hs.1, le_trans hs.2 (max_le ht.2 hτ.2)⟩
      exact le_trans (hN₁b z s hsI t ht)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))
  have hrem_supp : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : R3,
      (ω z τ - ω z t) - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t ≠ 0 →
        z ∈ Metric.closedBall 0 R := by
    intro τ hτ z hz
    by_contra hzc
    refine hz ?_
    have h1 : ω z τ = 0 := by by_contra h; exact hzc (hsupp τ hτ z h)
    have h2 : ω z t = 0 := by by_contra h; exact hzc (hsupp t ht z h)
    have h3 : FiniteTimeSingularity.timeDeriv ω z t = 0 := by
      by_contra h; exact hzc (hsuppD t ht z h)
    rw [h1, h2, h3, sub_zero, smul_zero, sub_zero]
  have hbs_rem : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : R3, 2 * R ≤ ‖z‖ →
      ‖biotSavart
          (fun y => (ω y τ - ω y t) - (τ - t) • FiniteTimeSingularity.timeDeriv ω y t) z‖
        ≤ (max N₁ 0 * R / 3) * |τ - t| ^ ((α : ℝ) + 1) := by
    intro τ hτ z hz2
    have hMc : 0 ≤ max N₁ 0 * |τ - t| ^ ((α : ℝ) + 1) :=
      mul_nonneg hN₁0 (Real.rpow_nonneg (abs_nonneg _) _)
    have h := Work.LWP.BiotSavart.farField_decay_const hRnn hMc
      (fun y => hrem τ hτ y) (fun y => hrem_supp τ hτ y) z hz2
    have hkey : R ^ 3 / ‖z‖ ^ 2 ≤ R / 4 := by
      have hXpos : 0 < ‖z‖ ^ 2 := pow_pos (by linarith) 2
      rw [div_le_iff₀ hXpos, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
      have h2 : (2 * R) ^ 2 ≤ ‖z‖ ^ 2 := by
        have h1 : 0 ≤ 2 * R := by linarith
        simpa using pow_le_pow_left₀ h1 hz2 2
      nlinarith [h2]
    have hstep : 4 / 3 * (max N₁ 0 * |τ - t| ^ ((α:ℝ) + 1)) * R ^ 3 / ‖z‖ ^ 2
        = 4 / 3 * (max N₁ 0 * |τ - t| ^ ((α:ℝ) + 1)) * (R ^ 3 / ‖z‖ ^ 2) := by ring
    refine (h.trans ?_)
    rw [hstep]
    calc 4 / 3 * (max N₁ 0 * |τ - t| ^ ((α:ℝ) + 1)) * (R ^ 3 / ‖z‖ ^ 2)
        ≤ 4 / 3 * (max N₁ 0 * |τ - t| ^ ((α:ℝ) + 1)) * (R / 4) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (max N₁ 0 * R / 3) * |τ - t| ^ ((α:ℝ) + 1) := by ring
  -- ### the constants and the radius
  have hK0 : 0 ≤ 2 ^ 17 * max M₁ 0 := by positivity
  have hC0 : 0 ≤ max N₁ 0 * R / 3 := by positivity
  have hαne : (α : ℝ) ≠ 0 := ne_of_gt hα
  set δ' : ℝ := (ε / 3 / (max N₁ 0 * R / 3 + 1)) ^ (1 / (α : ℝ)) with hδ'def
  set δ : ℝ := min (min η 1)
      (min (ε / 3 / (2 ^ 17 * max M₁ 0 + 1)) δ') with hδdef
  have hδ'pow : δ' ^ (α : ℝ) = ε / 3 / (max N₁ 0 * R / 3 + 1) := by
    rw [hδ'def, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ _), one_div, inv_mul_cancel₀ hαne,
      Real.rpow_one]
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine lt_min (lt_min hηpos one_pos) (lt_min (by positivity) ?_)
    rw [hδ'def]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hδη : δ ≤ η := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδK : δ ≤ ε / 3 / (2 ^ 17 * max M₁ 0 + 1) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hδC : δ ≤ δ' := le_trans (min_le_right _ _) (min_le_right _ _)
  -- ### the estimate
  rw [eventually_nhdsWithin_iff]
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (x, t) hδpos) ?_
  rintro q hq hqs
  obtain ⟨y, τ⟩ := q
  simp only [Set.mem_prod, Set.mem_Icc] at hqs
  obtain ⟨hy, hτ⟩ := hqs
  have hqnorm : ‖(y, τ) - (x, t)‖ < δ := by
    rw [Metric.mem_ball, dist_eq_norm] at hq
    exact hq
  have hyn : ‖y - x‖ ≤ ‖(y, τ) - (x, t)‖ := by simp
  have hτn : |τ - t| ≤ ‖(y, τ) - (x, t)‖ := by simp
  have hδy : ‖y - x‖ < δ := lt_of_le_of_lt hyn hqnorm
  have hδη' : ‖y - x‖ < η := lt_of_lt_of_le hδy hδη
  have hδτ : |τ - t| < δ := lt_of_le_of_lt hτn hqnorm
  -- (i) the `∂ₜ`-block Lipschitz bound
  have hb1 : ‖biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
        - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x‖
      ≤ 2 ^ 17 * max M₁ 0 * ‖y - x‖ := by
    have hyl : y ∈ Metric.ball x (‖x‖ / 4) := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hδy, hδ1, hx]
    have hxl : x ∈ Metric.ball x (‖x‖ / 4) := Metric.mem_ball_self (by linarith)
    have h1 := hlip hyl hxl
    have h2 : (((2 ^ 20 : ℝ) * max M₁ 0 * R ^ 3 / ‖x‖ ^ 3).toNNReal : ℝ) ≤ 2 ^ 17 * max M₁ 0 := by
      rw [Real.coe_toNNReal _ (by positivity)]
      have hxpos : 0 < ‖x‖ := by linarith
      have hxx : (2 * R) ^ 3 ≤ ‖x‖ ^ 3 := pow_le_pow_left₀ (by linarith) hx2 3
      have h8 : (2 * R) ^ 3 = 8 * R ^ 3 := by ring
      rw [div_le_iff₀ (pow_pos hxpos 3)]
      have hstep : 2 ^ 17 * max M₁ 0 * (8 * R ^ 3) ≤ 2 ^ 17 * max M₁ 0 * ‖x‖ ^ 3 :=
        mul_le_mul_of_nonneg_left (by rw [← h8]; exact hxx) (by positivity)
      have hpow : (2:ℝ) ^ 20 = 2 ^ 17 * 8 := by norm_num
      nlinarith [hstep, hpow]
    calc ‖biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
          - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x‖
        ≤ (((2 ^ 20 : ℝ) * max M₁ 0 * R ^ 3 / ‖x‖ ^ 3).toNNReal : ℝ) * ‖y - x‖ := h1
      _ ≤ 2 ^ 17 * max M₁ 0 * ‖y - x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  -- (ii) the remainder term
  have hb2 : ‖biotSavart (fun z => (ω z τ - ω z t)
        - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y‖
      ≤ (max N₁ 0 * R / 3) * |τ - t| ^ ((α : ℝ) + 1) := by
    refine hbs_rem τ hτ y ?_
    have h1 : ‖y‖ ≥ ‖x‖ - ‖y - x‖ := by
      have h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := norm_le_insert' x y
      rw [norm_sub_rev] at h2
      linarith
    linarith
  -- (iii) the spatial remainder
  have hb3 : ‖biotSavart (fun z => ω z t) y - biotSavart (fun z => ω z t) x
        - fderiv ℝ (fun z => biotSavart (fun w => ω w t) z) x (y - x)‖
      ≤ (ε / 3) * ‖y - x‖ :=
    hη (y := y) (by rw [dist_eq_norm]; exact hδη')
  -- ### the decomposition of the error
  have hRmeas : MeasureTheory.AEStronglyMeasurable
      (fun z => (ω z τ - ω z t) - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t)
      MeasureTheory.volume :=
    ((hmeas τ hτ).sub (hmeas t ht)).sub (by
      convert (hmeasD t ht).const_smul (τ - t) using 1)
  have hdiffM : ∀ z : R3, ‖ω z τ - ω z t‖ ≤ max N 0 * |τ - t| ^ (α : ℝ) := by
    intro z
    exact le_trans (hNb z τ hτ t ht)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))
  have hdiffSupp : ∀ z : R3, ω z τ - ω z t ≠ 0 → z ∈ Metric.closedBall 0 R := by
    intro z hz
    by_contra hzc
    refine hz ?_
    have h1 : ω z τ = 0 := by by_contra h; exact hzc (hsupp τ hτ z h)
    have h2 : ω z t = 0 := by by_contra h; exact hzc (hsupp t ht z h)
    rw [h1, h2, sub_zero]
  have hdiffMeas : MeasureTheory.AEStronglyMeasurable (fun z => ω z τ - ω z t)
      MeasureTheory.volume := (hmeas τ hτ).sub (hmeas t ht)
  have hbD0 : 0 ≤ max N 0 * |τ - t| ^ (α : ℝ) :=
    mul_nonneg hN₀ (Real.rpow_nonneg (abs_nonneg _) _)
  have hlin : biotSavart (fun z => ω z τ) y - biotSavart (fun z => ω z t) y
      = (τ - t) • biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
        + biotSavart (fun z => (ω z τ - ω z t)
            - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y := by
    have h1 : biotSavart (fun z => ω z τ - ω z t) y
        = biotSavart (fun z => ω z τ) y - biotSavart (fun z => ω z t) y :=
      Work.StabilityFar.Decay.biotSavart_sub (f := fun z => ω z τ) (g := fun z => ω z t)
        (R := R) (M := max M 0) hRnn hM0
        (fun z => le_trans (hMb τ hτ z) (le_max_left _ _))
        (fun z => le_trans (hMb t ht z) (le_max_left _ _))
        (fun z => hsupp τ hτ z) (fun z => hsupp t ht z) (hmeas τ hτ) (hmeas t ht) y
    have h2 : biotSavart (fun z => (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y
        = (τ - t) • biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y :=
      biotSavart_smul (τ - t) (ω := fun z => FiniteTimeSingularity.timeDeriv ω z t) (R := R)
        (M := max M₁ 0) (fun z => le_trans (hM₁b t ht z) (le_max_left _ _))
        (fun z => hsuppD t ht z) (hmeasD t ht) y
    have h3 : biotSavart (fun z => (ω z τ - ω z t)
          - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y
        = biotSavart (fun z => ω z τ - ω z t) y
          - biotSavart (fun z => (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y :=
      Work.StabilityFar.Decay.biotSavart_sub (f := fun z => ω z τ - ω z t)
        (g := fun z => (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) (R := R)
        (M := max (max N 0 * |τ - t| ^ (α : ℝ)) (|τ - t| * max M₁ 0)) hRnn
        (le_trans hbD0 (le_max_left _ _)) (fun z => le_trans (hdiffM z) (le_max_left _ _))
        (fun z => le_trans (by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (le_trans (hM₁b t ht z) (le_max_left _ _))
            (abs_nonneg _)) (le_max_right _ _))
        hdiffSupp (fun z hz => hsuppD t ht z (fun hc => hz (by rw [hc, smul_zero])))
        hdiffMeas (by
          convert (hmeasD t ht).const_smul (τ - t) using 1) y
    rw [h3, h2, h1]
    abel
  have herr : (fun q : R3 × ℝ => biotSavart (fun z => ω z q.2) q.1) (y, τ)
        - (fun q : R3 × ℝ => biotSavart (fun z => ω z q.2) q.1) (x, t)
        - farBlock ω (x, t) ((y, τ) - (x, t))
      = biotSavart (fun z => (ω z τ - ω z t)
            - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y
        + (τ - t) • (biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
            - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x)
        + (biotSavart (fun z => ω z t) y - biotSavart (fun z => ω z t) x
            - fderiv ℝ (fun z => biotSavart (fun w => ω w t) z) x (y - x)) := by
    have hf := farBlock_apply ω (x, t) (y - x) (τ - t)
    rw [show (y, τ) - (x, t) = (y - x, τ - t) from rfl, hf]
    rw [show (fun q : R3 × ℝ => biotSavart (fun z => ω z q.2) q.1) (y, τ)
        = biotSavart (fun z => ω z τ) y from rfl,
      show (fun q : R3 × ℝ => biotSavart (fun z => ω z q.2) q.1) (x, t)
        = biotSavart (fun z => ω z t) x from rfl]
    have hsplit : biotSavart (fun z => ω z τ) y - biotSavart (fun z => ω z t) x
        = (biotSavart (fun z => ω z τ) y - biotSavart (fun z => ω z t) y)
          + (biotSavart (fun z => ω z t) y - biotSavart (fun z => ω z t) x) := by abel
    rw [hsplit, hlin]
    simp only [smul_sub]
    abel
  rw [herr]
  -- ### the final combination
  have hsum : ‖biotSavart (fun z => (ω z τ - ω z t)
        - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y
      + (τ - t) • (biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
          - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x)
      + (biotSavart (fun z => ω z t) y - biotSavart (fun z => ω z t) x
          - fderiv ℝ (fun z => biotSavart (fun w => ω w t) z) x (y - x))‖
      ≤ (max N₁ 0 * R / 3) * |τ - t| ^ ((α : ℝ) + 1)
        + 2 ^ 17 * max M₁ 0 * |τ - t| * ‖y - x‖ + (ε / 3) * ‖y - x‖ := by
    have h2 : ‖(τ - t) • (biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
          - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x)‖
        ≤ 2 ^ 17 * max M₁ 0 * |τ - t| * ‖y - x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |τ - t| * ‖biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
            - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x‖
          ≤ |τ - t| * (2 ^ 17 * max M₁ 0 * ‖y - x‖) :=
            mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
        _ = 2 ^ 17 * max M₁ 0 * |τ - t| * ‖y - x‖ := by ring
    calc ‖biotSavart (fun z => (ω z τ - ω z t)
            - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y
          + (τ - t) • (biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
              - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x)
          + (biotSavart (fun z => ω z t) y - biotSavart (fun z => ω z t) x
              - fderiv ℝ (fun z => biotSavart (fun w => ω w t) z) x (y - x))‖
        ≤ ‖biotSavart (fun z => (ω z τ - ω z t)
              - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y
            + (τ - t) • (biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
                - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x)‖
          + ‖biotSavart (fun z => ω z t) y - biotSavart (fun z => ω z t) x
              - fderiv ℝ (fun z => biotSavart (fun w => ω w t) z) x (y - x)‖ := norm_add_le _ _
      _ ≤ (‖biotSavart (fun z => (ω z τ - ω z t)
              - (τ - t) • FiniteTimeSingularity.timeDeriv ω z t) y‖
            + ‖(τ - t) • (biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
                - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x)‖)
          + ‖biotSavart (fun z => ω z t) y - biotSavart (fun z => ω z t) x
              - fderiv ℝ (fun z => biotSavart (fun w => ω w t) z) x (y - x)‖ := by
          refine add_le_add (norm_add_le _ _) le_rfl
      _ ≤ _ := by linarith [hb2, h2, hb3]
  have hfin : (max N₁ 0 * R / 3) * |τ - t| ^ ((α : ℝ) + 1)
        + 2 ^ 17 * max M₁ 0 * |τ - t| * ‖y - x‖ + (ε / 3) * ‖y - x‖
      ≤ ε * ‖(y, τ) - (x, t)‖ := by
    refine estimate_combine (α := α) hC0 hK0 hε (norm_nonneg _) (abs_nonneg _) hτn
      (norm_nonneg _) hyn ?_ ?_ ?_
    · have h1 : |τ - t| ^ (α : ℝ) ≤ δ ^ (α : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (le_of_lt hδτ) hαnn
      have h2 : δ ^ (α : ℝ) ≤ δ' ^ (α : ℝ) :=
        Real.rpow_le_rpow (le_of_lt hδpos) hδC hαnn
      rw [hδ'pow] at h2
      exact le_trans h1 h2
    · have h8 : ‖(y, τ) - (x, t)‖ < ε / 3 / (2 ^ 17 * max M₁ 0 + 1) :=
        lt_of_lt_of_le hqnorm hδK
      have h9 : (2 ^ 17 * max M₁ 0) * ‖(y, τ) - (x, t)‖ ≤ ε / 3 := by
        have h10 : ‖(y, τ) - (x, t)‖ * (2 ^ 17 * max M₁ 0 + 1) ≤ ε / 3 := by
          calc ‖(y, τ) - (x, t)‖ * (2 ^ 17 * max M₁ 0 + 1)
              ≤ ε / 3 / (2 ^ 17 * max M₁ 0 + 1) * (2 ^ 17 * max M₁ 0 + 1) :=
                mul_le_mul_of_nonneg_right (le_of_lt h8) (by positivity)
            _ = ε / 3 := div_mul_cancel₀ _ (by positivity)
        nlinarith [h10, hK0]
      exact h9
    · rw [rpow_succ_eq hα (abs_nonneg _)]
      exact mul_le_mul_of_nonneg_left hτn (Real.rpow_nonneg (abs_nonneg _) _)
  linarith [hsum, hfin]


/-- **Pointwise bound for the block operator.** -/
theorem norm_farBlock_le (ω : R3 → ℝ → R3) (p : R3 × ℝ) :
    ‖farBlock ω p‖
      ≤ ‖fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1‖
        + ‖biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [farBlock_apply]
  have hw : ‖w‖ = max ‖w.1‖ ‖w.2‖ := rfl
  calc ‖fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1 w.1
        + w.2 • biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1‖
      ≤ ‖fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1 w.1‖
        + ‖w.2 • biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1‖ :=
        norm_add_le _ _
    _ ≤ ‖fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1‖ * ‖w.1‖
        + ‖biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1‖ * |w.2| := by
        refine add_le_add (ContinuousLinearMap.le_opNorm _ _) ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact le_of_eq (mul_comm |w.2| ‖biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1‖)
    _ ≤ ‖fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1‖ * ‖w‖
        + ‖biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1‖ * ‖w‖ := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
    _ = (‖fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1‖
        + ‖biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1‖) * ‖w‖ := by
        ring

/-- **The far-strip `C^{1,α}` clause, corrected form (`0 < S`).** -/
theorem biotSavart_farStrip_holder_pos {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : R3 → ℝ → R3} {R S : ℝ} (hS : 0 < S) (hbun : BSAdmissibleStripFull α ω R S) :
    IsContDiffHolderOn ℝ α
      (fun q : R3 × ℝ => biotSavart (fun y => ω y q.2) q.1)
      (Work.StabilityFar.farRegion (2 * R + 5) ×ˢ Set.Icc (0:ℝ) S) := by
  obtain ⟨M, At, A, hM0, hAt0, hA0, hbddD, hthD, hlipD⟩ := farStrip_estimates_fderiv hα hα1 hbun
  obtain ⟨M₁, Atu, A₁, hM₁0, hAtu0, hA₁0, hbddE, hthE, hlipE⟩ :=
    farStrip_estimates_timeBlock hα hα1 hS hbun
  obtain ⟨hcontD, hcontE⟩ := continuousOn_farStrip_blocks hα hS hbun
  have hαle : (α : ℝ) ≤ 1 := le_of_lt hα1
  set sr : Set (R3 × ℝ) := Work.StabilityFar.farRegion (2 * R + 5) ×ˢ Set.Icc (0:ℝ) S with hsr
  have hRpos : 0 < R := hbun.1.1
  have hRnn : 0 ≤ R := hRpos.le
  have hρpos : 0 < 2 * R + 5 := by linarith
  -- ### uniqueness of the within-derivative on the strip
  have huniq : ∀ p ∈ sr, UniqueDiffWithinAt ℝ sr p := by
    intro p hp
    obtain ⟨hx, ht⟩ := hp
    exact UniqueDiffWithinAt.prod
      ((Work.StabilityFar.isOpen_farRegion (2 * R + 5)).uniqueDiffWithinAt hx)
      (Work.StabilityFar.uniqueDiffWithinAt_Icc hS ht)
  have huniqOn : UniqueDiffOn ℝ sr := fun p hp => huniq p hp
  -- ### the within-derivative is `farBlock`
  have hfw : ∀ p ∈ sr, fderivWithin ℝ (fun q : R3 × ℝ => biotSavart (fun y => ω y q.2) q.1) sr p
      = farBlock ω p := by
    intro p hp
    exact (hasFDerivWithinAt_farStrip hα hα1 hS hbun p hp).fderivWithin (huniq p hp)
  -- ### continuity of `farBlock` on the strip
  have hcont : ContinuousOn (fun p : R3 × ℝ => farBlock ω p) sr := by
    intro p hp
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hD0 : Tendsto (fun q : R3 × ℝ =>
        ‖fderiv ℝ (fun z => biotSavart (fun y => ω y q.2) z) q.1
          - fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1‖) (𝓝[sr] p) (𝓝 0) := by
      have hc : Tendsto (fun _ : R3 × ℝ =>
          fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1)
          (𝓝[sr] p) (𝓝 (fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1)) :=
        tendsto_const_nhds
      have hsub : Tendsto (fun q : R3 × ℝ =>
          fderiv ℝ (fun z => biotSavart (fun y => ω y q.2) z) q.1
            - fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1) (𝓝[sr] p) (𝓝 0) := by
        have h := (hcontD p hp).tendsto.sub hc
        simpa only [sub_self] using h
      simpa using hsub.norm
    have hE0 : Tendsto (fun q : R3 × ℝ =>
        ‖biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1
          - biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1‖)
        (𝓝[sr] p) (𝓝 0) := by
      have hc : Tendsto (fun _ : R3 × ℝ =>
          biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1)
          (𝓝[sr] p) (𝓝 (biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1)) :=
        tendsto_const_nhds
      have hsub : Tendsto (fun q : R3 × ℝ =>
          biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1
            - biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1)
          (𝓝[sr] p) (𝓝 0) := by
        have h := (hcontE p hp).tendsto.sub hc
        simpa only [sub_self] using h
      simpa using hsub.norm
    have hsum : Tendsto (fun q : R3 × ℝ =>
        ‖fderiv ℝ (fun z => biotSavart (fun y => ω y q.2) z) q.1
            - fderiv ℝ (fun z => biotSavart (fun y => ω y p.2) z) p.1‖
          + ‖biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1
            - biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1‖)
        (𝓝[sr] p) (𝓝 0) := by
      simpa using hD0.add hE0
    exact squeeze_zero (fun q => norm_nonneg _) (fun q => norm_farBlock_sub_le ω q p) hsum
  -- ### the uniform bound on the block operator
  have hK0 : 0 ≤ 2 ^ 20 * M * R ^ 3 / (2 * R + 5) ^ 3 + (4 / 3) * M₁ * R ^ 3 / (2 * R + 5) ^ 2 := by
    positivity
  have hbound : ∀ p ∈ sr, ‖farBlock ω p‖ ≤
      2 ^ 20 * M * R ^ 3 / (2 * R + 5) ^ 3 + (4 / 3) * M₁ * R ^ 3 / (2 * R + 5) ^ 2 := by
    intro p hp
    obtain ⟨hx, ht⟩ := hp
    have hx' : 2 * R + 5 < ‖p.1‖ := hx
    have hx2 : 2 * R ≤ ‖p.1‖ := by linarith
    have hxm : 2 * R + 5 ≤ ‖p.1‖ := le_of_lt hx'
    refine le_trans (norm_farBlock_le ω p) (add_le_add ?_ ?_)
    · refine le_trans (hbddD p.2 ht p.1 hx2) ?_
      have h3 : (2 * R + 5) ^ 3 ≤ ‖p.1‖ ^ 3 := pow_le_pow_left₀ (by linarith) hxm 3
      gcongr
    · refine le_trans (hbddE p.2 ht p.1 hx2) ?_
      have h2 : (2 * R + 5) ^ 2 ≤ ‖p.1‖ ^ 2 := pow_le_pow_left₀ (by linarith) hxm 2
      gcongr
  -- ### the local Hölder bound and the global bound
  have hloc : ∀ p ∈ sr, ∀ q ∈ sr, dist p q ≤ 1 →
      ‖farBlock ω p - farBlock ω q‖ ≤ (A + At + A₁ + Atu) * dist p q ^ (α : ℝ) := by
    intro p hp q hq hpq
    obtain ⟨x, t⟩ := p
    obtain ⟨y, τ⟩ := q
    obtain ⟨hx, ht⟩ := hp
    obtain ⟨hy, hτ⟩ := hq
    have hx' : 2 * R + 5 < ‖x‖ := hx
    have hy' : 2 * R + 5 < ‖y‖ := hy
    have hx2 : 2 * R < ‖x‖ := by linarith
    have hy2 : 2 * R < ‖y‖ := by linarith
    have hdist1 : ‖x - y‖ ≤ dist (x, t) (y, τ) := by
      rw [Prod.dist_eq, dist_eq_norm]
      exact le_max_left _ _
    have hdist2 : |t - τ| ≤ dist (x, t) (y, τ) := by
      rw [Prod.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    have hxy1 : ‖x - y‖ ≤ 1 := le_trans hdist1 hpq
    have hdist_le : dist (x, t) (y, τ) ≤ dist (x, t) (y, τ) ^ (α : ℝ) :=
      Real.self_le_rpow_of_le_one dist_nonneg hpq hαle
    have hrpow : |t - τ| ^ (α : ℝ) ≤ dist (x, t) (y, τ) ^ (α : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) hdist2 (le_of_lt hα)
    have hxyle : ‖x - y‖ ≤ dist (x, t) (y, τ) ^ (α : ℝ) := le_trans hdist1 hdist_le
    have hDdiff : ‖fderiv ℝ (biotSavart (fun z => ω z t)) x
          - fderiv ℝ (biotSavart (fun z => ω z τ)) y‖
        ≤ A * ‖x - y‖ + At * |t - τ| ^ (α : ℝ) := by
      have h1 : ‖fderiv ℝ (biotSavart (fun z => ω z t)) x
            - fderiv ℝ (biotSavart (fun z => ω z t)) y‖ ≤ A * ‖x - y‖ :=
        hlipD t ht x y hx2 hy2
      have h2 : ‖fderiv ℝ (biotSavart (fun z => ω z t)) y
            - fderiv ℝ (biotSavart (fun z => ω z τ)) y‖ ≤ At * |t - τ| ^ (α : ℝ) :=
        hthD y hy2 t ht τ hτ
      calc ‖fderiv ℝ (biotSavart (fun z => ω z t)) x
            - fderiv ℝ (biotSavart (fun z => ω z τ)) y‖
          = ‖(fderiv ℝ (biotSavart (fun z => ω z t)) x - fderiv ℝ (biotSavart (fun z => ω z t)) y)
              + (fderiv ℝ (biotSavart (fun z => ω z t)) y
                - fderiv ℝ (biotSavart (fun z => ω z τ)) y)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ A * ‖x - y‖ + At * |t - τ| ^ (α : ℝ) := add_le_add h1 h2
    have hEdiff : ‖biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x
          - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z τ) y‖
        ≤ A₁ * ‖x - y‖ + Atu * |t - τ| ^ (α : ℝ) := by
      have h1 : ‖biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x
            - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y‖
          ≤ A₁ * ‖x - y‖ := hlipE t ht x y (by linarith) hxy1
      have h2 : ‖biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
            - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z τ) y‖
          ≤ Atu * |t - τ| ^ (α : ℝ) := hthE y hy2 t ht τ hτ
      calc ‖biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x
            - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z τ) y‖
          = ‖(biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x
                - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y)
              + (biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y
                - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z τ) y)‖ := by
              congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ A₁ * ‖x - y‖ + Atu * |t - τ| ^ (α : ℝ) := add_le_add h1 h2
    calc ‖farBlock ω (x, t) - farBlock ω (y, τ)‖
        ≤ ‖fderiv ℝ (biotSavart (fun z => ω z t)) x - fderiv ℝ (biotSavart (fun z => ω z τ)) y‖
          + ‖biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x
            - biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z τ) y‖ :=
          norm_farBlock_sub_le ω (x, t) (y, τ)
      _ ≤ (A * ‖x - y‖ + At * |t - τ| ^ (α : ℝ))
          + (A₁ * ‖x - y‖ + Atu * |t - τ| ^ (α : ℝ)) := add_le_add hDdiff hEdiff
      _ = (A + A₁) * ‖x - y‖ + (At + Atu) * |t - τ| ^ (α : ℝ) := by ring
      _ ≤ (A + A₁) * dist (x, t) (y, τ) ^ (α : ℝ)
          + (At + Atu) * dist (x, t) (y, τ) ^ (α : ℝ) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hxyle (by linarith)
          · exact mul_le_mul_of_nonneg_left hrpow (by linarith)
      _ = (A + At + A₁ + Atu) * dist (x, t) (y, τ) ^ (α : ℝ) := by ring
  have hbdd2 : ∀ p ∈ sr, ∀ q ∈ sr,
      ‖farBlock ω p - farBlock ω q‖
        ≤ 2 * (2 ^ 20 * M * R ^ 3 / (2 * R + 5) ^ 3
            + (4 / 3) * M₁ * R ^ 3 / (2 * R + 5) ^ 2) := by
    intro p hp q hq
    calc ‖farBlock ω p - farBlock ω q‖ ≤ ‖farBlock ω p‖ + ‖farBlock ω q‖ := norm_sub_le _ _
      _ ≤ (2 ^ 20 * M * R ^ 3 / (2 * R + 5) ^ 3 + (4 / 3) * M₁ * R ^ 3 / (2 * R + 5) ^ 2)
          + (2 ^ 20 * M * R ^ 3 / (2 * R + 5) ^ 3 + (4 / 3) * M₁ * R ^ 3 / (2 * R + 5) ^ 2) :=
          add_le_add (hbound p hp) (hbound q hq)
      _ = 2 * (2 ^ 20 * M * R ^ 3 / (2 * R + 5) ^ 3
          + (4 / 3) * M₁ * R ^ 3 / (2 * R + 5) ^ 2) := by ring
  -- ### assembly
  refine ⟨?_, ?_, ?_⟩
  · refine contDiffOn_succ_of_fderivWithin (n := 0)
      (f := fun q : R3 × ℝ => biotSavart (fun y => ω y q.2) q.1) ?_ ?_ ?_
    · intro p hp
      exact (hasFDerivWithinAt_farStrip hα hα1 hS hbun p hp).differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · rw [contDiffOn_zero]
      refine hcont.congr ?_
      intro p hp
      exact hfw p hp
  · rw [IsBoundedFunOn, isBounded_iff_forall_norm_le]
    refine ⟨2 ^ 20 * M * R ^ 3 / (2 * R + 5) ^ 3
        + (4 / 3) * M₁ * R ^ 3 / (2 * R + 5) ^ 2, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [hfw p hp]
    exact hbound p hp
  · refine ⟨Real.toNNReal (max (A + At + A₁ + Atu)
        (2 * (2 ^ 20 * M * R ^ 3 / (2 * R + 5) ^ 3
          + (4 / 3) * M₁ * R ^ 3 / (2 * R + 5) ^ 2))), ?_⟩
    refine Work.StabilityFar.holderOnWith_of_local_holder_bounded
      (f := fun p => fderivWithin ℝ (fun q : R3 × ℝ => biotSavart (fun y => ω y q.2) q.1) sr p)
      (by positivity) (by positivity) ?_ ?_
    · intro p hp q hq hpq
      rw [hfw p hp, hfw q hq]
      exact hloc p hp q hq hpq
    · intro p hp q hq
      rw [hfw p hp, hfw q hq]
      exact hbdd2 p hp q hq

end Work.CoreResiduals.BiotSavart
end
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.fderiv_slice_ext_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- The spatial derivative of a time slice of a two-variable map, from its joint derivative at
`(x,t)`: the chain rule with the inclusion `y ↦ (y,t)` (whose Fréchet derivative is
`ContinuousLinearMap.inl ℝ R3 ℝ`). -/
private theorem fderiv_slice_eq_aux {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    fderiv ℝ (fun y => u y t) x
      = (fderiv ℝ u.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  rw [show (fun y : R3 => u y t) = u.uncurry ∘ (fun y => (y, t)) from rfl]
  rw [fderiv_comp x h (hasFDerivAt_prodMk_left x t).differentiableAt]
  rw [(hasFDerivAt_prodMk_left x t).fderiv]

/-- **The first block of `fderiv ℝ (extField ω S)` on the strip.**  For a point `(x,t)` with
`t ∈ Icc 0 S` at which the spacetime field `extField ω S : R3 × ℝ → R3` (defined in
`Submission/Work/CoreResiduals/BiotSavart/continuousOn_farStrip_blocks.lean` as
`fun p => BS (windowExt ω S · p.2) p.1`) is `C¹`, the composition of its Fréchet derivative with
the spatial inclusion `ContinuousLinearMap.inl ℝ R3 ℝ` is the spatial derivative of the slice:
`fderiv ℝ (BS (ω(·,t))) x`.

Proof: `extField ω S = Function.uncurry (bsSTField (windowExt ω S))` (`extField_eq_uncurry`), so
`(fun x' => extField ω S (x',t)) = fun x' => BS (windowExt ω S · t) x'`; the chain rule with
`hasFDerivAt_prodMk_left` (and `ContDiffAt.differentiableAt`/`HasFDerivAt.comp`) gives
`(fderiv ℝ (extField ω S) (x,t)).comp (inl ℝ R3 ℝ)` as the derivative of that map at `x`; then
`windowExt_of_mem_Icc ht` gives `(fun y => windowExt ω S y t) = (fun y => ω y t)`, hence the same
Biot–Savart fields. -/
theorem fderiv_slice_ext_eq {ω : R3 → ℝ → R3} {S : ℝ} {x : R3} {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) S)
    (hcd : ContDiffAt ℝ 1 (extField ω S) (x, t)) :
    fderiv ℝ (Work.LWP.biotSavart (fun y => ω y t)) x
      = (fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  have hdiff : DifferentiableAt ℝ (extField ω S) (x, t) := hcd.differentiableAt (by norm_num)
  have hwindow : (fun y => windowExt ω S y t) = (fun y => ω y t) :=
    funext fun y => windowExt_of_mem_Icc ht
  have hslice := fderiv_slice_eq_aux (u := bsSTField (windowExt ω S)) (x := x) (t := t) hdiff
  simp only [bsSTField, hwindow] at hslice
  exact hslice

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.fderiv_time_ext_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-- **The second block of `fderiv ℝ (extField ω S)` on the strip.**  For `0 < R`, an `ω` whose
two-sided extension `windowExt ω S` satisfies the window bundle `BSAdmissibleOnWindow` (supplied by
`windowExt_windowBundle`), and a point `(x,t)` with `t ∈ Icc 0 S` at which the field
`extField ω S` (defined in
`Submission/Work/CoreResiduals/BiotSavart/continuousOn_farStrip_blocks.lean` as
`fun p => BS (windowExt ω S · p.2) p.1`) is `C¹`, the time-block of its Fréchet derivative
evaluated at `1` is the Biot–Savart field of the time-derivative slice of the extension:
`BS (∂ₜ(windowExt ω S)(·,t)) x`.

Proof: the chain rule with `hasFDerivAt_prodMk_right` identifies
`(fderiv ℝ (extField ω S) (x,t)).comp (inr ℝ R3 ℝ)` with
`fderiv ℝ (fun s => bsSTField (windowExt ω S) x s) t`; since `t ∈ Icc 0 S ⊆ preWindow (S+1)`, the
local clauses of the bundle around `t` let `hasFDerivAt_bsSTField_time` identify that with
`bsTDeriv (windowExt ω S) x t`, whose value at `1` is
`1 • BS (timeDeriv (windowExt ω S) · t) x = BS (timeDeriv (windowExt ω S) · t) x`
(`bsTDeriv` is `ContinuousLinearMap.toSpanSingleton ℝ _`; use `toSpanSingleton_apply`). -/
theorem fderiv_time_ext_eq {ω : R3 → ℝ → R3} {R S : ℝ} (hR : 0 < R)
    (hbun : Work.CoreResiduals.BSAdmissibleOnWindow (windowExt ω S) R (S + 1))
    {x : R3} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) S)
    (hcd : ContDiffAt ℝ 1 (extField ω S) (x, t)) :
    Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv (windowExt ω S) y t) x
      = ((fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inr ℝ R3 ℝ)) 1 := by
  -- `t` lies in the half-window on which the bundle's local clauses apply
  have htpre : t ∈ Work.ConstructionInstance.preWindow (S + 1) := by
    rw [Work.ConstructionInstance.preWindow, Set.mem_Ioo]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- unpack the window bundle
  obtain ⟨hRpos, hsupp, hbddL, hholdL, haesmL, hdcL, hbddDL, haesmDL⟩ := hbun
  obtain ⟨ε₁, hε₁, M, hMb⟩ := hbddL t htpre
  obtain ⟨ε₃, hε₃, haesm⟩ := haesmL t htpre
  obtain ⟨ε₄, hε₄, hdc⟩ := hdcL t htpre
  obtain ⟨ε₅, hε₅, M₁, hM₁b⟩ := hbddDL t htpre
  -- a single window on which all the local clauses hold simultaneously
  set δ : ℝ := min (min ε₁ ε₃) (min ε₄ ε₅) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (lt_min hε₁ hε₃) (lt_min hε₄ hε₅)
  have hδ1 : δ ≤ ε₁ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ3 : δ ≤ ε₃ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ4 : δ ≤ ε₄ := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ5 : δ ≤ ε₅ := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsub : ∀ {ε : ℝ}, δ ≤ ε → Set.Ioo (t - δ) (t + δ) ⊆ Set.Ioo (t - ε) (t + ε) := by
    intro ε hε s hs
    exact ⟨by linarith [hs.1, hε], by linarith [hs.2, hε]⟩
  -- the `t`-derivative of the spacetime Biot–Savart field, from the bundle
  have hbsT : HasFDerivAt (fun s : ℝ => bsSTField (windowExt ω S) x s)
      (bsTDeriv (windowExt ω S) x t) t :=
    hasFDerivAt_bsSTField_time (ω := windowExt ω S) (R := R) (M := max M 0) (M₁ := max M₁ 0)
      (ε := δ) hR.le (le_max_right _ _) (le_max_right _ _) hδpos
      (fun s hs y => le_trans (hMb s (hsub hδ1 hs) y) (le_max_left _ _))
      (fun s hs y => le_trans (hM₁b s (hsub hδ5 hs) y) (le_max_left _ _))
      (fun s hs y => hdc s (hsub hδ4 hs) y)
      (fun s hs y hy => hsupp s y hy)
      (fun s hs => haesm s (hsub hδ3 hs))
      x
  -- the chain rule: the derivative of `s ↦ extField ω S (x,s)` is the `t`-block
  have hdf : HasFDerivAt (extField ω S) (fderiv ℝ (extField ω S) (x, t)) (x, t) :=
    (hcd.hasStrictFDerivAt (by simp)).hasFDerivAt
  have hpmk : HasFDerivAt (fun s : ℝ => (x, s)) (ContinuousLinearMap.inr ℝ R3 ℝ) t :=
    hasFDerivAt_prodMk_right x t
  have hcomp : HasFDerivAt (fun s : ℝ => bsSTField (windowExt ω S) x s)
      ((fderiv ℝ (extField ω S) (x, t)).comp (ContinuousLinearMap.inr ℝ R3 ℝ)) t := by
    simpa only [Function.comp_def, extField, bsSTField] using hdf.comp t hpmk
  -- uniqueness of the derivative identifies the `t`-block with `bsTDeriv`
  rw [hcomp.unique hbsT]
  simp [bsTDeriv, ContinuousLinearMap.toSpanSingleton_apply]

end Work.CoreResiduals.BiotSavart
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.radGreen_general_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.RadialWAux (radPhi radPsi radK radP radQ radK_pos radQ_pos)
open Work.FTS.PhiStar.Radial (radGreen)
open Work.FTS.PhiStar.Series.SmoothAux.Deleg (radPhi_general radPsi_rec)

namespace Work.FTS.PhiStar.Honesty.CptQSmooth

/-- Additivity of `iteratedDeriv` for a sum, from `HasDerivAt` chains at all lower levels. -/
private lemma iteratedDeriv_add_of_chain {f g : ℝ → ℝ} :
    ∀ k : ℕ, (∀ n : ℕ, n < k → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x) →
      (∀ n : ℕ, n < k → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g x) x) →
      ∀ x : ℝ, 0 < x → iteratedDeriv k (f + g) x = iteratedDeriv k f x + iteratedDeriv k g x := by
  intro k
  induction k with
  | zero => intro hf hg x hx; simp
  | succ k ih =>
      intro hf hg x hx
      have hfk : ∀ n : ℕ, n < k → ∀ y : ℝ, 0 < y →
          HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f y) y :=
        fun n hn => hf n (by omega)
      have hgk : ∀ n : ℕ, n < k → ∀ y : ℝ, 0 < y →
          HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g y) y :=
        fun n hn => hg n (by omega)
      have hev : iteratedDeriv k (f + g) =ᶠ[𝓝 x]
          fun y => iteratedDeriv k f y + iteratedDeriv k g y := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact ih hfk hgk y hy
      rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq hev, iteratedDeriv_succ,
        iteratedDeriv_succ]
      exact deriv_add (hf k (Nat.lt_succ_self k) x hx).differentiableAt
        (hg k (Nat.lt_succ_self k) x hx).differentiableAt

/-- The value of the `k`-th derivative of `radGreen` as `radK·(Φ^{(k)} + Ψ^{(k)})`. -/
private lemma radGreen_step {α : ℝ} (hα : 0 < α) {m : ℕ} {c : ℝ → ℝ} {N : ℕ}
    (hchainΦ : ∀ n : ℕ, n + 1 ≤ N → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPhi α m c)) (iteratedDeriv (n + 1) (radPhi α m c) x) x)
    (hchainΨ : ∀ n : ℕ, n + 1 ≤ N → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPsi α m c)) (iteratedDeriv (n + 1) (radPsi α m c) x) x)
    {k : ℕ} (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (radGreen α m c) x
      = radK α m * (iteratedDeriv k (radPhi α m c) x + iteratedDeriv k (radPsi α m c) x) := by
  have hev : radGreen α m c =ᶠ[𝓝 x]
      fun w => radK α m * (radPhi α m c w + radPsi α m c w) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with w hw
    exact Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled hα m c w hw
  have hadd := iteratedDeriv_add_of_chain k (fun n hn => hchainΦ n (by omega))
    (fun n hn => hchainΨ n (by omega)) x hx
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hev, iteratedDeriv_const_mul_field]
  exact congrArg (fun v => radK α m * v) hadd

/-- The `a`-th derivative of `radGreen` differentiates to the `(a+1)`-st one. -/
private lemma radGreen_conj1_of_chains {α : ℝ} (hα : 0 < α) {a : ℕ} {m : ℕ} {c : ℝ → ℝ}
    (hchainΦ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPhi α m c)) (iteratedDeriv (n + 1) (radPhi α m c) x) x)
    (hchainΨ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPsi α m c)) (iteratedDeriv (n + 1) (radPsi α m c) x) x)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (iteratedDeriv a (radGreen α m c)) (iteratedDeriv (a + 1) (radGreen α m c) z) z := by
  have hΦ := hchainΦ a le_rfl z hz
  have hΨ := hchainΨ a le_rfl z hz
  have hmul := (hΦ.add hΨ).const_mul (radK α m)
  have h2 := radGreen_step hα hchainΦ hchainΨ (k := a + 1) le_rfl hz
  have hfin : HasDerivAt (fun w => radK α m * (iteratedDeriv a (radPhi α m c) w
      + iteratedDeriv a (radPsi α m c) w)) (iteratedDeriv (a + 1) (radGreen α m c) z) z := by
    rw [h2]
    exact hmul
  have hev : iteratedDeriv a (radGreen α m c) =ᶠ[𝓝 z]
      fun w => radK α m * (iteratedDeriv a (radPhi α m c) w
        + iteratedDeriv a (radPsi α m c) w) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    exact radGreen_step hα hchainΦ hchainΨ (k := a) (Nat.le_succ a) hw
  exact hfin.congr_of_eventuallyEq hev

theorem radGreen_general_bound {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {a₀ b z₀ : ℝ}
    (ha₀ : 0 < a₀) (hz₀ : 0 < z₀) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ → ℝ} {K : ℝ}, 0 ≤ K →
      ContDiffOn ℝ (↑(a + 1)) c (Set.Ioi 0) → Work.FTS.PhiStar.BddDeriv (a + 1) c K →
      (∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) →
      (∀ m : ℕ, ∀ z : ℝ, 0 < z →
        HasDerivAt (fun z' => iteratedDeriv a (fun z'' => Work.FTS.PhiStar.Radial.radGreen α m c z'') z')
          (iteratedDeriv (a + 1) (fun z'' => Work.FTS.PhiStar.Radial.radGreen α m c z'') z) z)
      ∧ (∀ m : ℕ, ∀ z : ℝ, z₀ ≤ z →
        |iteratedDeriv a (fun z'' => Work.FTS.PhiStar.Radial.radGreen α m c z'') z|
          ≤ C * ((m : ℝ) + 1) ^ a * K) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    radPsi_zero_bound_hasDerivAt (α := α) (a := a) (a₀ := a₀) (b := b) (z₀ := z₀) ha₀ hz₀
  set C₁ : ℝ := max 1 (2 / (α * z₀) + ((a : ℝ) + 2) / z₀) with hC₁
  have hC₁1 : 1 ≤ C₁ := by rw [hC₁]; exact le_max_left _ _
  have hC₁nn : 0 ≤ C₁ := le_trans zero_le_one hC₁1
  have hC₁pow : 0 ≤ C₁ ^ a := pow_nonneg hC₁nn a
  set Cv : ℝ := 1 / (4 * α) * (1 + C₂ + 2 * C₁ ^ a) + 1 with hCv
  have hCv0 : 0 ≤ Cv := by
    rw [hCv]
    have h1 : 0 ≤ 1 / (4 * α) := by positivity
    have h2 : 0 ≤ 1 + C₂ + 2 * C₁ ^ a := by linarith
    exact add_nonneg (mul_nonneg h1 h2) zero_le_one
  have hle1 : ∀ m : ℕ, (1 : ℝ) ≤ (a : ℝ) + radQ α m := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hq : 1 < radQ α m := by
      simp only [radQ, Work.FTS.PhiStar.RadialWAux.radQ]
      rw [lt_div_iff₀ hα]
      nlinarith [hα2, hm0]
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    linarith
  have hradK_le : ∀ m : ℕ, radK α m ≤ 1 / (4 * α) := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp only [radK, Work.FTS.PhiStar.RadialWAux.radK]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hα, hm0]
  refine ⟨Cv, hCv0, ?_⟩
  intro c K hK hc hb hsupp
  have key : ∀ m : ℕ,
      (∀ z : ℝ, 0 < z → HasDerivAt (iteratedDeriv a (radGreen α m c))
        (iteratedDeriv (a + 1) (radGreen α m c) z) z)
      ∧ (∀ z : ℝ, z₀ ≤ z → |iteratedDeriv a (radGreen α m c) z|
        ≤ Cv * ((m : ℝ) + 1) ^ a * K) := by
    intro m
    have hPhil := radPhi_general (α := α) (m := m) (N := a + 1) (c := c) (K := K)
      hα hK hc hb
    have hchainΦ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPhi α m c)) (iteratedDeriv (n + 1) (radPhi α m c) x) x := by
      intro n hn x hx
      have h1 := (hPhil n (by omega) x hx).2.2 hn
      have h3 : iteratedDeriv (n + 1) (radPhi α m c) x
          = ∫ u in (0 : ℝ)..1, iteratedDeriv (n + 1) c (x * u)
              * u ^ ((n : ℝ) + 1 + radQ α m - 1) := by
        rw [(hPhil (n + 1) (by omega) x hx).1]
        apply intervalIntegral.integral_congr
        intro u _
        rw [show (((n + 1 : ℕ) : ℝ) + radQ α m - 1) = ((n : ℝ) + 1 + radQ α m - 1) from by
          push_cast; ring]
      rwa [h3]
    have hPhiK : ∀ x : ℝ, 0 < x → |iteratedDeriv a (radPhi α m c) x| ≤ K := by
      intro x hx
      refine le_trans (hPhil a (by omega) x hx).2.1 ?_
      rw [div_le_iff₀ (by have := radQ_pos hα m; positivity)]
      nlinarith [hK, hle1 m]
    rcases eq_or_ne m 0 with hm | hm
    · have hΨfun : radPsi α m c = radPsi α 0 c := by rw [hm]
      have h0 := hC₂ (c := c) (K := K) hK hc hb hsupp
      have hchainΨ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
          HasDerivAt (iteratedDeriv n (radPsi α m c)) (iteratedDeriv (n + 1) (radPsi α m c) x) x := by
        intro n hn x hx
        rw [hΨfun]
        exact h0.2 n hn x hx
      have hPsi_bd : ∀ z : ℝ, z₀ ≤ z → |iteratedDeriv a (radPsi α m c) z| ≤ C₂ * K := by
        intro z hz
        rw [hΨfun]
        exact h0.1 a le_rfl z hz
      refine ⟨fun z hz => radGreen_conj1_of_chains hα hchainΦ hchainΨ hz, fun z hz => ?_⟩
      have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
      have hstep := radGreen_step hα hchainΦ hchainΨ (k := a) (Nat.le_succ a) hzpos
      have hb1 : |iteratedDeriv a (radPhi α m c) z + iteratedDeriv a (radPsi α m c) z|
          ≤ K + C₂ * K :=
        (abs_add_le _ _).trans (add_le_add (hPhiK z hzpos) (hPsi_bd z hz))
      have hA : |iteratedDeriv a (radGreen α m c) z| ≤ 1 / (4 * α) * (1 + C₂) * K := by
        calc |iteratedDeriv a (radGreen α m c) z|
            = radK α m * |iteratedDeriv a (radPhi α m c) z
                + iteratedDeriv a (radPsi α m c) z| := by
                rw [hstep, abs_mul, abs_of_pos (radK_pos hα m)]
          _ ≤ 1 / (4 * α) * (K + C₂ * K) :=
                mul_le_mul (hradK_le m) hb1 (abs_nonneg _) (by positivity)
          _ = 1 / (4 * α) * (1 + C₂) * K := by ring
      have hB : 1 / (4 * α) * (1 + C₂) * K ≤ Cv * K := by
        refine mul_le_mul_of_nonneg_right ?_ hK
        have h4 : 1 + C₂ ≤ 1 + C₂ + 2 * C₁ ^ a := by linarith
        have h5 : 1 / (4 * α) * (1 + C₂) ≤ 1 / (4 * α) * (1 + C₂ + 2 * C₁ ^ a) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        rw [hCv]
        linarith
      have hCe : Cv * K ≤ Cv * ((m : ℝ) + 1) ^ a * K := by
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hpow : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ a :=
          one_le_pow₀ (by linarith)
        calc Cv * K = Cv * 1 * K := by ring
          _ ≤ Cv * ((m : ℝ) + 1) ^ a * K :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCv0) hK
      exact le_trans hA (le_trans hB hCe)
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hmr1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hp1 : 1 < radP α m := by
        simp only [radP, Work.FTS.PhiStar.RadialWAux.radP]
        rw [lt_div_iff₀ hα]
        nlinarith [hmr1, hα2]
      set M : ℝ := max 1 ((radP α m + ((a + 1 : ℕ) : ℝ) + 1) / z₀) with hM
      have hM1 : 1 ≤ M := by rw [hM]; exact le_max_left _ _
      have hMz : (radP α m + ((a + 1 : ℕ) : ℝ) + 1) / z₀ ≤ M := by
        rw [hM]; exact le_max_right _ _
      have hPe := radPsi_rec (α := α) (m := m) (N := a + 1) (c := c) (K := K) (M := M)
        (z₀ := z₀) hα hK hc hb hp1 hz₀ hM1 hMz
      have hchainΨ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
          HasDerivAt (iteratedDeriv n (radPsi α m c)) (iteratedDeriv (n + 1) (radPsi α m c) x) x :=
        fun n hn x hx => hPe.2 n hn x hx
      have hPsi_bd : ∀ z : ℝ, z₀ ≤ z → |iteratedDeriv a (radPsi α m c) z| ≤ 2 * M ^ a * K :=
        fun z hz => hPe.1 a (Nat.le_succ a) z hz
      refine ⟨fun z hz => radGreen_conj1_of_chains hα hchainΦ hchainΨ hz, fun z hz => ?_⟩
      have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
      have hstep := radGreen_step hα hchainΦ hchainΨ (k := a) (Nat.le_succ a) hzpos
      have hb1 : |iteratedDeriv a (radPhi α m c) z + iteratedDeriv a (radPsi α m c) z|
          ≤ K + 2 * M ^ a * K :=
        (abs_add_le _ _).trans (add_le_add (hPhiK z hzpos) (hPsi_bd z hz))
      have hMle : M ≤ C₁ * ((m : ℝ) + 1) := by
        have hcast : (((a + 1 : ℕ) : ℝ)) = (a : ℝ) + 1 := by push_cast; ring
        refine max_le ?_ ?_
        · nlinarith [hC₁1, hmr1]
        · rw [div_le_iff₀ hz₀, hcast]
          have hT : 2 / (α * z₀) + ((a : ℝ) + 2) / z₀ ≤ C₁ := by
            rw [hC₁]; exact le_max_right _ _
          have hkey : radP α m + ((a : ℝ) + 1) + 1
              ≤ (2 / (α * z₀) + ((a : ℝ) + 2) / z₀) * (z₀ * ((m : ℝ) + 1)) := by
            rw [show (2 / (α * z₀) + ((a : ℝ) + 2) / z₀) * (z₀ * ((m : ℝ) + 1))
                = (2 / α) * ((m : ℝ) + 1) + ((a : ℝ) + 2) * ((m : ℝ) + 1) from by
              field_simp]
            have h1 : radP α m ≤ (2 / α) * ((m : ℝ) + 1) := by
              rw [show radP α m = (2 / α) * (m : ℝ) from by
                simp only [radP, Work.FTS.PhiStar.RadialWAux.radP]; ring]
              exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            have h2 : (a : ℝ) + 2 ≤ ((a : ℝ) + 2) * ((m : ℝ) + 1) :=
              le_mul_of_one_le_right (by positivity) (by linarith)
            linarith
          calc radP α m + ((a : ℝ) + 1) + 1
              ≤ (2 / (α * z₀) + ((a : ℝ) + 2) / z₀) * (z₀ * ((m : ℝ) + 1)) := hkey
            _ ≤ C₁ * (z₀ * ((m : ℝ) + 1)) := mul_le_mul_of_nonneg_right hT (by positivity)
            _ = C₁ * ((m : ℝ) + 1) * z₀ := by ring
      have hMpow : M ^ a ≤ C₁ ^ a * ((m : ℝ) + 1) ^ a := by
        calc M ^ a ≤ (C₁ * ((m : ℝ) + 1)) ^ a :=
              pow_le_pow_left₀ (by positivity) hMle a
          _ = C₁ ^ a * ((m : ℝ) + 1) ^ a := by rw [mul_pow]
      have hstep1 : K + 2 * M ^ a * K ≤ (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a * K := by
        have h3 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ a := one_le_pow₀ (by linarith)
        have h5 : 2 * M ^ a ≤ 2 * C₁ ^ a * ((m : ℝ) + 1) ^ a := by linarith
        have h4 : (1 : ℝ) + 2 * M ^ a ≤ (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a :=
          calc (1 : ℝ) + 2 * M ^ a ≤ ((m : ℝ) + 1) ^ a + 2 * C₁ ^ a * ((m : ℝ) + 1) ^ a :=
                add_le_add h3 h5
            _ = (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a := by ring
        calc K + 2 * M ^ a * K = K * (1 + 2 * M ^ a) := by ring
          _ ≤ K * ((1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a) := mul_le_mul_of_nonneg_left h4 hK
          _ = (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a * K := by ring
      have hsum0 : (0 : ℝ) ≤ K + 2 * M ^ a * K := by
        have h : (0 : ℝ) ≤ M ^ a := pow_nonneg (le_trans zero_le_one hM1) a
        nlinarith [hK, h]
      calc |iteratedDeriv a (radGreen α m c) z|
          = radK α m * |iteratedDeriv a (radPhi α m c) z
              + iteratedDeriv a (radPsi α m c) z| := by
              rw [hstep, abs_mul, abs_of_pos (radK_pos hα m)]
        _ ≤ 1 / (4 * α) * (K + 2 * M ^ a * K) :=
              mul_le_mul (hradK_le m) hb1 (abs_nonneg _) (by positivity)
        _ ≤ 1 / (4 * α) * ((1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a * K) :=
              mul_le_mul_of_nonneg_left hstep1 (by positivity)
        _ = 1 / (4 * α) * (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a * K := by ring
        _ ≤ Cv * ((m : ℝ) + 1) ^ a * K := by
              have hP : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ a := by positivity
              have h4 : 1 + 2 * C₁ ^ a ≤ 1 + C₂ + 2 * C₁ ^ a := by linarith [hC₂0]
              have h5 : 1 / (4 * α) * (1 + 2 * C₁ ^ a)
                  ≤ 1 / (4 * α) * (1 + C₂ + 2 * C₁ ^ a) :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
              have h8 := mul_le_mul_of_nonneg_right h5 hP
              rw [hCv]
              refine mul_le_mul_of_nonneg_right ?_ hK
              nlinarith [h8, hP]
  exact ⟨fun m z hz => (key m).1 z hz, fun m z hz => (key m).2 z hz⟩

end Work.FTS.PhiStar.Honesty.CptQSmooth
end
end
