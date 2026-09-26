import Mathlib
import Submission.Work.Asymptotics.TSasm.cuspOneLowHalfTile_TS

set_option maxHeartbeats 1600000

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Topology

noncomputable section

/-!
# The `r`-seminorm bound for the layer on the cusp-half `R⁻` low strip

The target region of this file is

  `R⁻_low = {τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2, τ - 1 ∈ Tregion, Im (S • τ) < 1/2}`

where `Tregion = {w ∈ 𝒟 : 1/2 ≤ Im (S • w) ≤ 2}`.

## The geometry of `R⁻_low`

Writing `τ = x + iy`, `u := τ - 1`, the two hypotheses `Im (S • u) ≥ 1/2` and
`Im (S • τ) < 1/2` say `‖u‖² ≤ 2 Im u = 2y` and `2y < ‖τ‖²`, i.e.

  `(x-1)² + (y-1)² ≤ 1`  and  `x² + (y-1)² > 1`,

so `τ` lies in the lune inside the disk of radius `1` about `1 + i` and outside the disk of
radius `1` about `i`.  Subtracting the two inequalities gives `x² > (x-1)²`, hence `x > 1/2`,
and `τ ∈ 𝒟` gives `x < 1`.  Consequently `τ` is never far from the cusp-`1` half tile; it splits
into two regimes:

* **`3/4 < x`**: then `τ ∈ lowBadSet = {τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2, 3/4 < |Re τ|}`, the region where
  the pole `z = τ - 1` of `z ↦ K(τ,z)` grazes the contour.  There the layer is (pointwise in `r`)
  the pole-split layer `blLowF2 ℓ d τ ·`, whose `r`-seminorms are bounded by
  `Work.Asymptotics.blLowF2_seminorm` — the same derivation as the one inside
  `Work.Asymptotics.layerSemi_Tregion`.
* **`x ≤ 3/4`**: then `x² + (y-1)² > 1` forces `|y - 1| > √7/4 > 33/50`, whence `y > 33/20`, and
  `τ` lies in the Euclidean box `K = {1/2 ≤ Re ≤ 3/4, 33/20 ≤ Im ≤ 2}`, which is compact and
  contained in `𝒟` (its points are at distance `> 1/2` from `±1/2` and `Re` is bounded away from
  `±1`).  On a compact subset of `𝒟` the layer seminorms are bounded by
  `Work.Asymptotics.layer_seminorm_on_compact`.

Both bounds are *uniform constants*, so the target holds with `N = 0` and `C` the sum of the two
constants (recall `scale τ ≥ 1`).
-/

/-! ## Geometry of the region `R⁻_low` -/

/-- **The real part in `R⁻_low`.**  For `τ ∈ 𝒟` with `τ - 1 ∈ Tregion` and `Im (S • τ) < 1/2`
the real part satisfies `1/2 < Re τ`; with `τ ∈ 𝒟` this gives `1/2 < Re τ < 1`.

The two hypotheses are `‖τ - 1‖² ≤ 2 Im τ` and `2 Im τ < ‖τ‖²`; subtracting, `Re τ² > (Re τ - 1)²`
and hence `Re τ > 1/2`. -/
private lemma tsR_re_bounds {τ : UpperHalfPlane} (hD : τ ∈ DomainD)
    (hm1 : ((-1 : ℝ) +ᵥ τ) ∈ Tregion)
    (hS : ¬ ((1 : ℝ) / 2 ≤ (ModularGroup.S • τ).im)) :
    (1 : ℝ) / 2 < τ.re ∧ τ.re < 1 := by
  have hstep : ‖((((-1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ)‖ ^ 2 ≤ 2 * ((-1 : ℝ) +ᵥ τ).im :=
    (ts_half_le_im_S_iff _).mp (mem_Tregion.mp hm1).2.1
  have hoff : 2 * τ.im < ‖(τ : ℂ)‖ ^ 2 := by
    have hlt : (ModularGroup.S • τ).im < 1 / 2 := not_le.mp hS
    rw [ts_im_S_smul] at hlt
    have hpos : (0 : ℝ) < ‖(τ : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr τ.ne_zero) 2
    rw [div_lt_iff₀ hpos] at hlt
    linarith
  rw [ts_normSq_eq, UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_im] at hstep
  rw [ts_normSq_eq] at hoff
  exact ⟨by nlinarith [hstep, hoff], hD.2.1⟩

/-- **The imaginary part in the compact piece of `R⁻_low`.**  If in addition `Re τ ≤ 3/4` then
`Im τ ≥ 33/20`: from `Re τ² + (Im τ - 1)² > 1` and `Re τ ≤ 3/4` we get
`(Im τ - 1)² > 7/16 > (33/50)²`, and `Im τ ≥ 1/2` excludes the negative sign. -/
private lemma tsR_im_lower {τ : UpperHalfPlane} (him : (1 : ℝ) / 2 ≤ τ.im)
    (hre1 : (1 : ℝ) / 2 ≤ τ.re) (hre2 : τ.re ≤ 3 / 4)
    (hm1 : ((-1 : ℝ) +ᵥ τ) ∈ Tregion)
    (hS : ¬ ((1 : ℝ) / 2 ≤ (ModularGroup.S • τ).im)) :
    (33 : ℝ) / 20 ≤ τ.im := by
  have hstep : ‖((((-1 : ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ)‖ ^ 2 ≤ 2 * ((-1 : ℝ) +ᵥ τ).im :=
    (ts_half_le_im_S_iff _).mp (mem_Tregion.mp hm1).2.1
  have hoff : 2 * τ.im < ‖(τ : ℂ)‖ ^ 2 := by
    have hlt : (ModularGroup.S • τ).im < 1 / 2 := not_le.mp hS
    rw [ts_im_S_smul] at hlt
    have hpos : (0 : ℝ) < ‖(τ : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr τ.ne_zero) 2
    rw [div_lt_iff₀ hpos] at hlt
    linarith
  rw [ts_normSq_eq, UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_im] at hstep
  rw [ts_normSq_eq] at hoff
  -- `(Im τ - 1)² > 1 - Re τ² ≥ 7/16`
  have hkey : ((33 : ℝ) / 50) ^ 2 < (τ.im - 1) ^ 2 := by
    have h1 : 1 - τ.re ^ 2 < (τ.im - 1) ^ 2 := by nlinarith [hstep, hoff]
    nlinarith [h1, hre2, hre1]
  have habs : (33 : ℝ) / 50 < |τ.im - 1| := by
    have h := sq_lt_sq.mp hkey
    rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 33 / 50)] at h
  rcases le_or_gt (τ.im - 1) 0 with hle | hgt
  · -- the negative branch is impossible because `Im τ ≥ 1/2`
    have h' : |τ.im - 1| = -(τ.im - 1) := abs_of_nonpos hle
    rw [h'] at habs
    linarith
  · rw [abs_of_pos hgt] at habs
    linarith

/-! ## The compact piece -/

/-- The closed Euclidean box `{1/2 ≤ Re ≤ 3/4, 33/20 ≤ Im ≤ 2}` inside which the compact part of
`R⁻_low` lives. -/
private def Kc : Set ℂ :=
  {z | (1 : ℝ) / 2 ≤ z.re} ∩ {z | z.re ≤ 3 / 4} ∩ {z | (33 : ℝ) / 20 ≤ z.im} ∩ {z | z.im ≤ 2}

private lemma mem_Kc {z : ℂ} : z ∈ Kc ↔
    (1 : ℝ) / 2 ≤ z.re ∧ z.re ≤ 3 / 4 ∧ (33 : ℝ) / 20 ≤ z.im ∧ z.im ≤ 2 := by
  simp only [Kc, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

private lemma isClosed_Kc : IsClosed Kc := by
  have h1 : IsClosed {z : ℂ | (1 : ℝ) / 2 ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have h2 : IsClosed {z : ℂ | z.re ≤ 3 / 4} :=
    isClosed_le Complex.continuous_re continuous_const
  have h3 : IsClosed {z : ℂ | (33 : ℝ) / 20 ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have h4 : IsClosed {z : ℂ | z.im ≤ 2} :=
    isClosed_le Complex.continuous_im continuous_const
  exact ((h1.inter h2).inter h3).inter h4

private lemma isCompact_Kc : IsCompact Kc := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 3) isClosed_Kc ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [mem_Kc] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hre : |z.re| ≤ 3 / 4 := abs_le.mpr ⟨by linarith, h2⟩
  have him : |z.im| ≤ 2 := abs_le.mpr ⟨by linarith, h4⟩
  have : ‖z‖ ^ 2 ≤ 9 := by
    nlinarith [sq_abs z.re, sq_abs z.im, abs_nonneg z.re, abs_nonneg z.im, hnorm, hre, him]
  nlinarith [norm_nonneg z]

/-- The corresponding closed subset of `ℍ`. -/
private def KK : Set UpperHalfPlane := (↑) ⁻¹' Kc

private lemma mem_KK {τ : UpperHalfPlane} : τ ∈ KK ↔
    (1 : ℝ) / 2 ≤ τ.re ∧ τ.re ≤ 3 / 4 ∧ (33 : ℝ) / 20 ≤ τ.im ∧ τ.im ≤ 2 := by
  rw [KK, Set.mem_preimage, mem_Kc, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]

private lemma isCompact_KK : IsCompact KK := by
  have hrange : Kc ⊆ Set.range ((↑) : UpperHalfPlane → ℂ) := by
    intro z hz
    rw [UpperHalfPlane.range_coe]
    rw [mem_Kc] at hz
    exact lt_of_lt_of_le (by norm_num) hz.2.2.1
  exact UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage' isCompact_Kc hrange

private lemma KK_subset_DomainD : KK ⊆ DomainD := by
  intro τ hτ
  rw [mem_KK] at hτ
  obtain ⟨h1, h2, h3, h4⟩ := hτ
  have hre : (1 : ℝ) / 2 ≤ τ.re := h1
  refine mem_DomainD.mpr ⟨by linarith, by linarith, ?_, ?_⟩
  · have h := Complex.abs_im_le_norm ((τ : ℂ) - (1 / 2 : ℂ))
    have him : (((τ : ℂ) - (1 / 2 : ℂ)).im) = τ.im := by
      simp
    rw [him, abs_of_pos τ.im_pos] at h
    linarith
  · have h := Complex.abs_re_le_norm ((τ : ℂ) + (1 / 2 : ℂ))
    have hre' : (((τ : ℂ) + (1 / 2 : ℂ)).re) = τ.re + 1 / 2 := by
      simp
    rw [hre'] at h
    have hpos : (0 : ℝ) < τ.re + 1 / 2 := by linarith
    rw [abs_of_pos hpos] at h
    linarith

/-! ## The two region bounds -/

/-- **The bound on `lowBadSet`.**  On the low bad-line region
`{τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2, 3/4 < |Re τ|}` the layer is pointwise the pole-split layer
`blLowF2 ℓ d τ ·`, whose seminorms are bounded uniformly by `blLowF2_seminorm`; this is the same
derivation as the first step of `Work.Asymptotics.layerSemi_Tregion`. -/
private lemma tsR_lowBad_set_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      Work.Asymptotics.HalfFunnel.lowBadSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖ ≤ C := by
  obtain ⟨Cks, hCks, hks⟩ := Work.HFN.HalfFunnel.lowBad_kernel_spike_b ℓ d hd
  obtain ⟨Cdec, hCdec, hdec1, hdec2⟩ :=
    Work.HFN.HalfFunnel.lowBad_spike_b_adapter ℓ d hCks hks
  obtain ⟨Ct, Mt, hCt, hMt, htail⟩ := Work.HFN.HalfFunnel.lowBad_Aexp_tail ℓ d hd
  obtain ⟨C, hC, hb⟩ := Work.HFN.blLowF2_seminorm ℓ d hd hCdec hdec1 hdec2
    ⟨Ct, Mt, hCt, hMt, htail⟩
    (fun m N => Work.Asymptotics.HalfFunnel.lowBad_PhiSpike_deriv ℓ d hd m N)
    (fun m N => Work.HFN.HalfFunnel.lowBad_Phi12_deriv ℓ d hd Cdec hCdec hdec1 m N)
    k l
  refine ⟨C, hC, fun τ r hτ => ?_⟩
  have hfun : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
      = fun s : ℝ => Work.HFN.blLowF2 ℓ d τ s := by
    funext s
    rw [Work.Asymptotics.layer, Work.HFN.blLowF2]
    by_cases hs : s = 0
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      exact (Work.HFN.HalfFunnel.lowF2_eq_paperLayer ℓ d hd Cdec hCdec hdec1 hdec2
        τ s hτ).symm
  rw [hfun]
  exact hb τ r hτ

/-! ## The target -/

theorem layer_cuspHalf_Rminus_lowstrip (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
        τ.im ≤ 2 → ((-1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.Tregion →
        ¬ ((1 : ℝ) / 2 ≤ (ModularGroup.S • τ).im) → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N := by
  intro k l
  obtain ⟨C₁, hC₁, hb₁⟩ := tsR_lowBad_set_seminorm ℓ d hd k l
  have hG : ∀ i j : Fin 2,
      Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (Work.Asymptotics.Gcusp ℓ d i j) :=
    fun i j => Work.HFN.Gcusp_moderate ℓ d i j
  have h8 : d = 8 → ∀ j : Fin 2, Work.Asymptotics.Gcusp ℓ d 1 j = 0 := by
    intro h8d j
    rw [Work.Asymptotics.Gcusp, if_pos h8d]
    funext τ
    fin_cases j <;> simp [Work.Asymptotics.Gcusp8]
  obtain ⟨C₂, hC₂, hb₂⟩ := Work.HFN.layer_seminorm_on_compact ℓ d hd
    (Work.Asymptotics.Gcusp ℓ d) hG h8 isCompact_KK KK_subset_DomainD
    (Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd isCompact_KK KK_subset_DomainD)
    (Work.HFN.cusp_expansion_of_kernel ℓ d hd isCompact_KK KK_subset_DomainD) k l
  refine ⟨C₁ + C₂, 0, by linarith, le_rfl, ?_⟩
  intro τ hD him1 him2 hm1 hS r
  obtain ⟨hre1, -⟩ := tsR_re_bounds hD hm1 hS
  have hpow : (Work.Kernels.scale τ) ^ (0 : ℝ) = 1 := Real.rpow_zero _
  have hfin : ∀ {c : ℝ}, 0 ≤ c → c ≤ C₁ + C₂ →
      c ≤ (C₁ + C₂) * (Work.Kernels.scale τ) ^ (0 : ℝ) := by
    intro c hc hcle
    rw [hpow, mul_one]
    exact hcle
  by_cases hcut : τ.re ≤ 3 / 4
  · have hK : τ ∈ KK := by
      rw [mem_KK]
      exact ⟨le_of_lt hre1, hcut,
        tsR_im_lower him1 (le_of_lt hre1) hcut hm1 hS, him2⟩
    exact le_trans (hb₂ τ r hK) (hfin hC₂ (by linarith))
  · have hlB : Work.Asymptotics.HalfFunnel.lowBadSet τ :=
      ⟨hD, him1, him2, Or.inl (not_le.mp hcut)⟩
    exact le_trans (hb₁ τ r hlB) (hfin hC₁ (by linarith))

end

end Work.Asymptotics
