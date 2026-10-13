/-
# The boundary derivative: the abstract `ε`-estimate

This module isolates the analytic content of `hasFDerivWithinAt_potOn_uncurry_boundary` from the
concrete potential: for *abstract* data

* `F : ℝ³ × ℝ → ℝ`, `A : ℝ³ × ℝ → ℝ³`, `c : ℝ³ × ℝ → ℝ`,
* `F` and `c` continuous on the closed strip `bstrip T = ℝ³ × [0,T/2]`, `A` continuous on the half
  open strip `bstripO T = ℝ³ × [0,T/2)`,
* the spatial partial derivative of the slice `F (·,σ)` at positive times `σ` is `innerSL ℝ (A (·,σ))`,
* the time derivative of the slice `s ↦ F (y₀,s)` is `c (y₀,·)` at positive times,

the uncurried `F` has within derivative `innerSL ℝ (A (y₀,0)) ∘ fst + c (y₀,0) • snd` at `(y₀,0)`
within the closed box `B(x₀,1) × [0,T/2)`.

The estimate is: the spatial part by the convex mean value inequality applied to the slices
`F (·,σ)` (with a limiting argument for the degenerate slice `σ = 0`), the time part by the one
dimensional mean value estimate `rightDeriv_zero_of_hasDerivAt_Ioo` applied to `s ↦ F (y₀,s)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtData
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.rightDeriv_zero_of_hasDerivAt_Ioo
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.norm_sub_fderiv_le_of_convex

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn.Connect

noncomputable section

theorem hasFDerivWithinAt_of_boundary_data {F : R3 × ℝ → ℝ} {A : R3 × ℝ → R3}
    {c : R3 × ℝ → ℝ} {x₀ y₀ : R3} {T : ℝ} (hT : 0 < T)
    (hy₀ : y₀ ∈ Metric.ball x₀ 1)
    (hFcont : ContinuousOn F (bstrip T))
    (hAcont : ContinuousOn A (bstripO T))
    (hcCont : ContinuousOn c (bstrip T))
    (hspace : ∀ σ ∈ Set.Ioo 0 (T / 2), ∀ z : R3,
      HasFDerivAt (fun v => F (v, σ)) (innerSL ℝ (A (z, σ))) z)
    (htime : ∀ σ ∈ Set.Ioo 0 (T / 2),
      HasDerivAt (fun s => F (y₀, s)) (c (y₀, σ)) σ) :
    HasFDerivWithinAt F
      ((innerSL ℝ (A (y₀, 0))).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
        + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) (c (y₀, 0)))
      (Metric.ball x₀ 1 ×ˢ Set.Ico 0 (T / 2)) (y₀, 0) := by
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hy₀O : (y₀, 0) ∈ bstripO T := ⟨trivial, le_refl 0, hT2⟩
  have hy₀s : (y₀, 0) ∈ bstrip T := bstripO_subset_bstrip T hy₀O
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  -- product neighbourhoods of `(y₀,0)` giving the two continuity bounds
  have hA : ∀ᶠ p : R3 × ℝ in 𝓝 y₀ ×ˢ 𝓝 (0 : ℝ),
      p ∈ bstripO T → ‖A p - A (y₀, 0)‖ < ε / 4 := by
    rw [← nhds_prod_eq, ← eventually_nhdsWithin_iff]
    refine ((Metric.tendsto_nhds.mp (hAcont.continuousWithinAt hy₀O)) (ε / 4) hε4).mono ?_
    exact fun p hp => by rwa [dist_eq_norm] at hp
  rcases mem_prod_iff.mp hA with ⟨u, hu, v, hv, huv⟩
  obtain ⟨δ₁, hδ₁0, hδ₁u⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨δ₂, hδ₂0, hδ₂v⟩ := Metric.mem_nhds_iff.mp hv
  have hG : ∀ (z : R3) (σ : ℝ), dist z y₀ < δ₁ → |σ| < δ₂ → (z, σ) ∈ bstripO T →
      ‖A (z, σ) - A (y₀, 0)‖ < ε / 4 := by
    intro z σ hz hσ hm
    refine huv ⟨hδ₁u hz, hδ₂v ?_⟩ hm
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero]
  have hB : ∀ᶠ p : R3 × ℝ in 𝓝 y₀ ×ˢ 𝓝 (0 : ℝ),
      p ∈ bstrip T → ‖c p - c (y₀, 0)‖ < ε / 4 := by
    rw [← nhds_prod_eq, ← eventually_nhdsWithin_iff]
    refine ((Metric.tendsto_nhds.mp (hcCont.continuousWithinAt hy₀s)) (ε / 4) hε4).mono ?_
    exact fun p hp => by rwa [dist_eq_norm] at hp
  rcases mem_prod_iff.mp hB with ⟨u', hu', v', hv', huv'⟩
  obtain ⟨δ₃, hδ₃0, hδ₃u⟩ := Metric.mem_nhds_iff.mp hu'
  obtain ⟨δ₄, hδ₄0, hδ₄v⟩ := Metric.mem_nhds_iff.mp hv'
  have hD : ∀ (z : R3) (σ : ℝ), dist z y₀ < δ₃ → |σ| < δ₄ → (z, σ) ∈ bstrip T →
      ‖c (z, σ) - c (y₀, 0)‖ < ε / 4 := by
    intro z σ hz hσ hm
    refine huv' ⟨hδ₃u hz, hδ₄v ?_⟩ hm
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero]
  -- the common window
  obtain ⟨e, he0, heδ₁, heδ₂, heδ₃, heδ₄, heT⟩ : ∃ e : ℝ,
      0 < e ∧ e ≤ δ₁ ∧ e ≤ δ₂ ∧ e ≤ δ₃ ∧ e ≤ δ₄ ∧ e ≤ T / 2 :=
    ⟨min (min (min δ₁ δ₂) δ₃) (min δ₄ (T / 2)),
      lt_min (lt_min (lt_min hδ₁0 hδ₂0) hδ₃0) (lt_min hδ₄0 hT2),
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)),
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  -- reduce to the product neighbourhood `B(y₀,e) × B(0,e)`
  rw [eventually_nhdsWithin_iff, nhds_prod_eq]
  refine mem_prod_iff.mpr ⟨Metric.ball y₀ e, Metric.ball_mem_nhds y₀ he0,
    Metric.ball (0 : ℝ) e, Metric.ball_mem_nhds 0 he0, ?_⟩
  rintro ⟨y, s⟩ ⟨hy, hs⟩ hpb
  have hye : dist y y₀ < e := Metric.mem_ball.mp hy
  have hse : |s| < e := by
    have h := Metric.mem_ball.mp hs
    rwa [Real.dist_eq, sub_zero] at h
  have hys : dist y y₀ < δ₁ := lt_of_lt_of_le hye heδ₁
  have hsδ₂ : |s| < δ₂ := lt_of_lt_of_le hse heδ₂
  have hsIco : s ∈ Set.Ico 0 (T / 2) := hpb.2
  have hsT : s < T / 2 := hsIco.2
  have hseub : s < e := (abs_lt.mp hse).2
  -- the space mean value estimate at the positive times
  have hMy : ∀ σ : ℝ, 0 < σ → σ < e →
      ‖F (y, σ) - F (y₀, σ) - (innerSL ℝ (A (y₀, σ))) (y - y₀)‖
        ≤ (ε / 2) * dist y y₀ := by
    intro σ hσ hσe
    have hσT : σ < T / 2 := lt_of_lt_of_le hσe heT
    have hσδ₂ : |σ| < δ₂ := by rw [abs_of_pos hσ]; exact lt_of_lt_of_le hσe heδ₂
    rw [dist_eq_norm]
    refine BoundaryTime.norm_sub_fderiv_le_of_convex (B := Metric.ball y₀ δ₁)
      (f := fun v => F (v, σ)) (L := fun z => innerSL ℝ (A (z, σ)))
      (x := y₀) (η := ε / 2) (convex_ball y₀ δ₁) (Metric.mem_ball_self hδ₁0) ?_ ?_
      y (Metric.mem_ball.mpr hys)
    · intro z hz
      exact hspace σ ⟨hσ, hσT⟩ z
    · intro z hz
      have hzbs := hG z σ (Metric.mem_ball.mp hz) hσδ₂ ⟨trivial, hσ.le, hσT⟩
      have hub : ‖A (y₀, σ) - A (y₀, 0)‖ < ε / 4 :=
        hG y₀ σ (by rw [dist_self]; exact hδ₁0) hσδ₂ ⟨trivial, hσ.le, hσT⟩
      have hsplit2 : A (z, σ) - A (y₀, σ)
          = (A (z, σ) - A (y₀, 0)) - (A (y₀, σ) - A (y₀, 0)) := by abel
      rw [show innerSL ℝ (A (z, σ)) - innerSL ℝ (A (y₀, σ))
          = innerSL ℝ (A (z, σ) - A (y₀, σ)) from ((innerSL ℝ).map_sub _ _).symm,
        innerSL_apply_norm, hsplit2]
      calc ‖(A (z, σ) - A (y₀, 0)) - (A (y₀, σ) - A (y₀, 0))‖
          ≤ ‖A (z, σ) - A (y₀, 0)‖ + ‖A (y₀, σ) - A (y₀, 0)‖ := norm_sub_le _ _
        _ ≤ ε / 4 + ε / 4 := add_le_add hzbs.le hub.le
        _ = ε / 2 := by ring
  -- the time mean value estimate
  have hMt : ∀ σ ∈ Set.Icc 0 e,
      ‖F (y₀, σ) - F (y₀, 0) - σ * c (y₀, 0)‖ ≤ (ε / 4) * σ := by
    have hcurve : ContinuousOn (fun τ : ℝ => ((y₀, τ) : R3 × ℝ)) (Set.Icc 0 e) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmap : Set.MapsTo (fun τ : ℝ => ((y₀, τ) : R3 × ℝ)) (Set.Icc 0 e) (bstrip T) :=
      fun τ hτ => ⟨trivial, hτ.1, le_trans hτ.2 heT⟩
    have hg : ContinuousOn (fun σ => F (y₀, σ)) (Set.Icc 0 e) := by
      refine (hFcont.comp hcurve hmap).congr ?_
      intro σ hσ
      rfl
    have hc : ContinuousOn (fun σ => c (y₀, σ)) (Set.Icc 0 e) := by
      refine (hcCont.comp hcurve hmap).congr ?_
      intro σ hσ
      rfl
    have hd : ∀ σ ∈ Set.Ioo 0 e, HasDerivAt (fun σ' => F (y₀, σ')) (c (y₀, σ)) σ := by
      intro σ hσ
      exact htime σ ⟨hσ.1, lt_of_lt_of_le hσ.2 heT⟩
    have hb : ∀ σ ∈ Set.Ioo 0 e, ‖c (y₀, σ) - c (y₀, 0)‖ ≤ ε / 4 := by
      intro σ hσ
      have hσδ₃ : dist y₀ y₀ < δ₃ := by rw [dist_self]; exact hδ₃0
      have hσδ₄ : |σ| < δ₄ := by rw [abs_of_pos hσ.1]; exact lt_of_lt_of_le hσ.2 heδ₄
      exact (hD y₀ σ hσδ₃ hσδ₄ ⟨trivial, hσ.1.le, le_of_lt (lt_of_lt_of_le hσ.2 heT)⟩).le
    exact (BoundaryTime.rightDeriv_zero_of_hasDerivAt_Ioo he0 hg hc hd).2 (ε / 4) hb
  -- the explicit form of the candidate derivative
  have hM : ∀ (a : R3) (σ : ℝ),
      (((innerSL ℝ (A (y₀, 0))).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
        + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) (c (y₀, 0))) ((a, σ)))
      = (innerSL ℝ (A (y₀, 0))) a + σ * c (y₀, 0) := by
    intro a σ
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul]
  -- the third summand of the decomposition
  have hIII : ∀ v : R3, ‖v - A (y₀, 0)‖ < ε / 4 →
      ‖(innerSL ℝ v) (y - y₀) - (innerSL ℝ (A (y₀, 0))) (y - y₀)‖
        ≤ (ε / 4) * dist y y₀ := by
    intro v hv
    rw [← ContinuousLinearMap.sub_apply,
      show innerSL ℝ v - innerSL ℝ (A (y₀, 0)) = innerSL ℝ (v - A (y₀, 0)) from
        ((innerSL ℝ).map_sub _ _).symm]
    calc ‖(innerSL ℝ (v - A (y₀, 0))) (y - y₀)‖
        ≤ ‖innerSL ℝ (v - A (y₀, 0))‖ * ‖y - y₀‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖v - A (y₀, 0)‖ * ‖y - y₀‖ := by rw [innerSL_apply_norm]
      _ ≤ (ε / 4) * ‖y - y₀‖ := mul_le_mul_of_nonneg_right (le_of_lt hv) (norm_nonneg _)
      _ = (ε / 4) * dist y y₀ := by rw [dist_eq_norm]
  have hnorm : ‖((y, s) : R3 × ℝ) - (y₀, 0)‖ = max (dist y y₀) |s| := by
    rw [← dist_eq_norm, Prod.dist_eq, Real.dist_eq, sub_zero]
  rcases eq_or_lt_of_le hsIco.1 with h0s | hs0
  · -- the slice `s = 0`: a limiting argument in time
    obtain rfl : s = 0 := h0s.symm
    show ‖F (y, 0) - F (y₀, 0) - ((innerSL ℝ (A (y₀, 0))).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
        + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) (c (y₀, 0)))
        ((y - y₀, 0 - 0))‖ ≤ ε * ‖((y, 0) : R3 × ℝ) - (y₀, 0)‖
    rw [sub_zero, hM (y - y₀) 0, zero_mul, add_zero]
    have hlim : Tendsto (fun σ : ℝ => ‖F (y, σ) - F (y₀, σ) - (innerSL ℝ (A (y₀, 0))) (y - y₀)‖)
        (𝓝[Set.Ioo 0 e] 0)
        (𝓝 ‖F (y, 0) - F (y₀, 0) - (innerSL ℝ (A (y₀, 0))) (y - y₀)‖) := by
      have hmap : Set.MapsTo (fun σ : ℝ => ((y, σ) : R3 × ℝ)) (Set.Ioo 0 e) (bstrip T) :=
        fun σ hσ => ⟨trivial, hσ.1.le, le_of_lt (lt_of_lt_of_le hσ.2 heT)⟩
      have hmap' : Set.MapsTo (fun σ : ℝ => ((y₀, σ) : R3 × ℝ)) (Set.Ioo 0 e) (bstrip T) :=
        fun σ hσ => ⟨trivial, hσ.1.le, le_of_lt (lt_of_lt_of_le hσ.2 heT)⟩
      have hγ : ContinuousWithinAt (fun σ : ℝ => ((y, σ) : R3 × ℝ)) (Set.Ioo 0 e) 0 :=
        (continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt
      have hγ₀ : ContinuousWithinAt (fun σ : ℝ => ((y₀, σ) : R3 × ℝ)) (Set.Ioo 0 e) 0 :=
        (continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt
      have hy : ContinuousWithinAt (fun σ : ℝ => F (y, σ)) (Set.Ioo 0 e) 0 := by
        have hm : (y, 0) ∈ bstrip T := ⟨trivial, le_refl 0, hT2.le⟩
        exact (hFcont.continuousWithinAt hm).comp hγ hmap
      have hy₀' : ContinuousWithinAt (fun σ : ℝ => F (y₀, σ)) (Set.Ioo 0 e) 0 :=
        (hFcont.continuousWithinAt hy₀s).comp hγ₀ hmap'
      exact ((hy.sub hy₀').sub continuousWithinAt_const).norm
    have hmem : Set.Ioo 0 e ∈ 𝓝[Set.Ioi 0] (0 : ℝ) :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Set.Iio e, isOpen_Iio.mem_nhds he0, fun x hx => ⟨hx.2, hx.1⟩⟩
    have hle : 𝓝[Set.Ioi 0] (0 : ℝ) ≤ 𝓝[Set.Ioo 0 e] 0 := nhdsWithin_le_iff.mpr hmem
    refine le_of_tendsto (hlim.mono_left hle) ?_
    filter_upwards [hmem] with σ hσ
    rw [hnorm, abs_zero, max_eq_left dist_nonneg]
    have hMy' := hMy σ hσ.1 hσ.2
    have hIII' := hIII (A (y₀, σ))
      (hG y₀ σ (by rw [dist_self]; exact hδ₁0) (by
        rw [abs_of_pos hσ.1]; exact lt_of_lt_of_le hσ.2 heδ₂)
        ⟨trivial, hσ.1.le, lt_of_lt_of_le hσ.2 heT⟩)
    have hsplit : F (y, σ) - F (y₀, σ) - (innerSL ℝ (A (y₀, 0))) (y - y₀)
        = (F (y, σ) - F (y₀, σ) - (innerSL ℝ (A (y₀, σ))) (y - y₀))
          + ((innerSL ℝ (A (y₀, σ))) (y - y₀) - (innerSL ℝ (A (y₀, 0))) (y - y₀)) := by
      ring
    rw [hsplit]
    calc ‖_ + _‖
        ≤ ‖F (y, σ) - F (y₀, σ) - (innerSL ℝ (A (y₀, σ))) (y - y₀)‖
          + ‖(innerSL ℝ (A (y₀, σ))) (y - y₀) - (innerSL ℝ (A (y₀, 0))) (y - y₀)‖ :=
          norm_add_le _ _
      _ ≤ (ε / 2) * dist y y₀ + (ε / 4) * dist y y₀ := add_le_add hMy' hIII'
      _ = (3 * ε / 4) * dist y y₀ := by ring
      _ ≤ ε * dist y y₀ := by
          have hd0 : (0 : ℝ) ≤ dist y y₀ := dist_nonneg
          nlinarith [hε, hd0]
  · -- the slice `s > 0`
    show ‖F (y, s) - F (y₀, 0) - ((innerSL ℝ (A (y₀, 0))).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
        + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) (c (y₀, 0)))
        ((y - y₀, s - 0))‖ ≤ ε * ‖((y, s) : R3 × ℝ) - (y₀, 0)‖
    have hMy' := hMy s hs0 hseub
    have hII := hMt s ⟨hsIco.1, hseub.le⟩
    have hIII' := hIII (A (y₀, s))
      (hG y₀ s (by rw [dist_self]; exact hδ₁0) hsδ₂ ⟨trivial, hsIco.1, hsT⟩)
    have hsplit : F (y, s) - F (y₀, 0)
        - ((innerSL ℝ (A (y₀, 0))) (y - y₀) + s * c (y₀, 0))
        = (F (y, s) - F (y₀, s) - (innerSL ℝ (A (y₀, s))) (y - y₀))
          + (F (y₀, s) - F (y₀, 0) - s * c (y₀, 0))
          + ((innerSL ℝ (A (y₀, s))) (y - y₀) - (innerSL ℝ (A (y₀, 0))) (y - y₀)) := by
      ring
    rw [sub_zero, hM (y - y₀) s, hsplit]
    calc ‖(_ + _) + _‖
        ≤ ‖F (y, s) - F (y₀, s) - (innerSL ℝ (A (y₀, s))) (y - y₀)
            + (F (y₀, s) - F (y₀, 0) - s * c (y₀, 0))‖
          + ‖(innerSL ℝ (A (y₀, s))) (y - y₀) - (innerSL ℝ (A (y₀, 0))) (y - y₀)‖ :=
          norm_add_le _ _
      _ ≤ (‖F (y, s) - F (y₀, s) - (innerSL ℝ (A (y₀, s))) (y - y₀)‖
            + ‖F (y₀, s) - F (y₀, 0) - s * c (y₀, 0)‖)
          + ‖(innerSL ℝ (A (y₀, s))) (y - y₀) - (innerSL ℝ (A (y₀, 0))) (y - y₀)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((ε / 2) * dist y y₀ + (ε / 4) * s) + (ε / 4) * dist y y₀ := by
          linarith [hMy', hII, hIII']
      _ ≤ ε * max (dist y y₀) |s| := by
          rcases le_total (dist y y₀) |s| with h | h
          · rw [max_eq_right h]
            have hd0 : (0 : ℝ) ≤ dist y y₀ := dist_nonneg
            nlinarith [hε, hd0, h, abs_nonneg s, le_abs_self s]
          · rw [max_eq_left h]
            nlinarith [hε, (dist_nonneg : (0 : ℝ) ≤ dist y y₀), abs_nonneg s, h, le_abs_self s]
      _ = ε * ‖((y, s) : R3 × ℝ) - (y₀, 0)‖ := by rw [hnorm]

end

end Work.FTS.PressureOn.Connect
