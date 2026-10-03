import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.uOf_differentiableOn

/-!
# `Work.Repel.wOfCell_surj_SrcC` : the cell composite is onto the target ball

For a cell `q = (j, k, n)` of Shishikura's §6 count whose shifted fibre
`fib j k = (· + k) '' W j` lies in the level-1 disc `Sm1`, the map

  `wOfCell q w = wOf (ĥ^[j] (uOf (s·(π w))) - k)`

of `chain_v9_chase` maps the *source region*

  `SrcC j k n = Raw j k ∩ ball (w_c + n) (1/2)`

of `chain_v9_src` **onto** the whole target ball `ball wt₀ ρ₀`.

Both directions are the level-1 chase read backwards:

* `⊆`: `w ∈ Raw j k` means `s·π w = φ₁ u` for some `u ∈ fib j k`; since `fib j k ⊆ Sm1` and
  `φ₁` is injective there (`uOf_unique`), the level-1 source `uOfSrc q w` is that very `u`, so
  the walk `ĥ^[j] u - k` lands in `W 0` (`chain_image_mem`) and `wOf` maps it into `ball wt₀ ρ₀`
  by construction (`wOf_spec`).
* `⊇`: given `z ∈ ball wt₀ ρ₀`, the target control `htgt'` produces `u₀ ∈ ball cbase ρ₁ ⊆ W 0`
  with `φ₁ u₀ = s·π z`; `chain_preimage_mem` lifts `u₀` to `u ∈ fib j k` with `ĥ^[j] u = u₀ + k`;
  and the *explicit* lift `lift j k n u ∈ Raw j k` of `chain_v9_src` lies within `1/2` of the
  centre `w_c + n` (the estimate `lift_mem_ball_half` below), so it is a point of `SrcC j k n`.
  On it `uOfSrc` recovers `u` (injectivity of `φ₁` on `Sm1`) and `wOf (ĥ^[j] u - k) = wOf u₀`,
  which equals `z` because `π` is injective on `ball wt₀ ρ₀` (`ρ₀ ≤ 1/2`) and
  `π (wOf u₀) = φ₁ u₀ / s = π z`.

The only quantitative input is `lift_mem_ball_half`: the fibre `fib j k` has diameter `< 1/2`
(`IsChain.bounded`) and lies in `Dsm (±η₁)`, where `τ₀ ∘ φ₁ = -1/φ₁` is `2`-Lipschitz
(`φ_star_deriv` plus the mean value theorem on the convex disc `Sm1`) and `|1/φ₁| ≥ 29η₁/40`
(`phi_norm_bounds`); hence the *relative* error of `φ₁` across the fibre is `≤ 40/(29η₁)`, the
logarithm of the ratio is `≤ 60/(29η₁)` in norm (`Complex.norm_log_one_add_half_le_self`), and
dividing by `2πi` (with `η₁ ≥ 64`, `hsize`) gives the `< 1/2` bound.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-! ## Elementary geometry of the level-1 disc `Sm1` -/

/-- A point of `Sm1` lies in one of the two discs `Dsm (±η₁)` on which the `PertData` fields of
`P₁` are stated. -/
lemma srcC_Sm1_mem_Dsm_union (V : V10) {z : ℂ} (hz : z ∈ V.Sm1) :
    z ∈ MandelDim.Dsm V.η₁ ∪ MandelDim.Dsm (-V.η₁) := by
  rw [V10.Sm1] at hz
  split at hz
  · exact Or.inl hz
  · exact Or.inr hz

/-- `Sm1` is convex (it is one of the closed discs `closedBall (±iη₁) (η₁/4)`). -/
lemma srcC_Sm1_convex (V : V10) : Convex ℝ V.Sm1 := by
  rw [V10.Sm1]
  split <;> exact convex_closedBall _ _

/-- `φ₁` does not vanish on `Sm1` (`phi_norm_bounds` gives `‖φ₁‖ ≥ 40/(51η₁)` there). -/
lemma srcC_Sm1_phi_ne_zero (V : V10) {z : ℂ} (hz : z ∈ V.Sm1) : V.P₁.φ z ≠ 0 := by
  have h := (V.phi_bounds_of_mem_Sm1 hz).1
  have hpos : 0 < 40 / (51 * V.η₁) := div_pos (by norm_num) (mul_pos (by norm_num) V.hη₁pos)
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- `τ₀ ∘ φ₁` is differentiable (as a complex function) at every point of `Sm1`. -/
lemma srcC_Sm1_tau0_phi_differentiableAt (V : V10) {z : ℂ} (hz : z ∈ V.Sm1) :
    DifferentiableAt ℂ (fun w => MandelDim.tau0 (V.P₁.φ w)) z := by
  have hdφ : DifferentiableAt ℂ V.P₁.φ z :=
    V.P₁.φ_holo.differentiableAt (V.P₁.Dφ_open.mem_nhds (V.Sm1_sub_Dφ hz))
  have hne : V.P₁.φ z ≠ 0 := srcC_Sm1_phi_ne_zero V hz
  have h : DifferentiableAt ℂ (fun w : ℂ => (-1 : ℂ) / V.P₁.φ w) z :=
    (differentiableAt_const (-1)).div hdφ hne
  convert h using 1
  funext w
  rfl

/-- The derivative of `τ₀ ∘ φ₁` is bounded by `2` on `Sm1` (`φ_star_deriv`). -/
lemma srcC_Sm1_tau0_phi_deriv_le_two (V : V10) {z : ℂ} (hz : z ∈ V.Sm1) :
    ‖deriv (fun w => MandelDim.tau0 (V.P₁.φ w)) z‖ ≤ 2 := by
  have h := (V.P₁.φ_star_deriv z (srcC_Sm1_mem_Dsm_union V hz)).2
  linarith

/-- **The mean value theorem on `Sm1`.**  `ψ = τ₀ ∘ φ₁ = -1/φ₁` is `2`-Lipschitz on the convex
disc `Sm1`; this is the replacement of the (relative) derivative bound for `φ₁`. -/
lemma srcC_Sm1_tau0_phi_lipschitz (V : V10) {u u' : ℂ} (hu : u ∈ V.Sm1) (hu' : u' ∈ V.Sm1) :
    ‖MandelDim.tau0 (V.P₁.φ u') - MandelDim.tau0 (V.P₁.φ u)‖ ≤ 2 * ‖u' - u‖ := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le (f := fun w => MandelDim.tau0 (V.P₁.φ w))
    (s := V.Sm1) (C := 2) (fun z hz => srcC_Sm1_tau0_phi_differentiableAt V hz)
    (fun z hz => srcC_Sm1_tau0_phi_deriv_le_two V hz) (srcC_Sm1_convex V) hu hu'

/-- `|τ₀ (φ₁ w)| = |1/φ₁ w| ≥ 29η₁/40` on `Sm1` (`phi_norm_bounds` gives `|φ₁ w| ≤ 40/(29η₁)`). -/
lemma srcC_Sm1_tau0_phi_lower (V : V10) {w : ℂ} (hw : w ∈ V.Sm1) :
    29 * V.η₁ / 40 ≤ ‖MandelDim.tau0 (V.P₁.φ w)‖ := by
  have h := (V.phi_bounds_of_mem_Sm1 hw).2
  have hne : V.P₁.φ w ≠ 0 := srcC_Sm1_phi_ne_zero V hw
  have hnorm : ‖MandelDim.tau0 (V.P₁.φ w)‖ = 1 / ‖V.P₁.φ w‖ := by
    rw [MandelDim.tau0, norm_div, norm_neg, norm_one]
  rw [hnorm]
  have h1 : 1 / (40 / (29 * V.η₁)) ≤ 1 / ‖V.P₁.φ w‖ :=
    one_div_le_one_div_of_le (norm_pos_iff.mpr hne) h
  have h2 : 1 / (40 / (29 * V.η₁)) = 29 * V.η₁ / 40 := by
    field_simp
  linarith [h1, h2]

/-- `64 ≤ η₁` (`hsize : 64 (C₀ + 1) ≤ η₁` and `C₀ > 0`). -/
lemma srcC_eta1_ge_64 (V : V10) : 64 ≤ V.η₁ := by
  have hC : (1 : ℝ) < V.C₀ + 1 := by linarith [V.hC₀]
  nlinarith [V.hsize]

/-! ## The relative error of `φ₁` across a chain fibre -/

/-- **The relative error of `φ₁` on a fibre is `≤ 40/(29η₁)`.**  For `u ∈ fib j k ⊆ Sm1` (and
`u_c = uc j + k` the chosen reference point of the fibre),

  `φ₁ u / φ₁ u_c - 1 = (ψ u_c - ψ u)/ψ u`,  `ψ = -1/φ₁`,

so the Lipschitz bound `‖ψ u_c - ψ u‖ ≤ 2‖u_c - u‖ ≤ 1` (fibre diameter `< 1/2`) divided by
`|ψ u| ≥ 29η₁/40` gives the estimate. -/
lemma srcC_phi_ratio_close (V : V10) {j : ℕ} {k : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    {u : ℂ} (hu : u ∈ V.fib j k) :
    ‖V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) - 1‖ ≤ 40 / (29 * V.η₁) := by
  obtain ⟨w, hw, rfl⟩ := hu
  set uc : ℂ := V.uc j + ((k : ℤ) : ℂ) with hucdef
  have hucfib : uc ∈ V.fib j k := by
    rw [hucdef]; exact V.uc_fib j k
  have huSm : w + ((k : ℤ) : ℂ) ∈ V.Sm1 := hSm ⟨w, hw, rfl⟩
  have hucSm : uc ∈ V.Sm1 := hSm hucfib
  -- the fibre has diameter `< 1/2`
  have hbdd := (V.hIsChain.bounded j).1
  have hdiam := (V.hIsChain.bounded j).2
  have hdist : dist w (V.uc j) ≤ Metric.diam (V.W j) :=
    Metric.dist_le_diam_of_mem hbdd hw (V.uc_mem j)
  have hdist' : ‖w - V.uc j‖ ≤ Metric.diam (V.W j) := by rwa [dist_eq_norm] at hdist
  have hnormlt : ‖w + ((k : ℤ) : ℂ) - uc‖ < 1 / 2 := by
    rw [hucdef]
    have h1 : ‖w + ((k : ℤ) : ℂ) - (V.uc j + ((k : ℤ) : ℂ))‖ = ‖w - V.uc j‖ := by
      congr 1; ring
    rw [h1]
    exact lt_of_le_of_lt hdist' hdiam
  -- `ψ` is `2`-Lipschitz
  have hlip := srcC_Sm1_tau0_phi_lipschitz V hucSm huSm
  rw [norm_sub_rev] at hlip
  have hψlt : ‖MandelDim.tau0 (V.P₁.φ uc)
      - MandelDim.tau0 (V.P₁.φ (w + ((k : ℤ) : ℂ)))‖ < 1 := by
    linarith [hlip, hnormlt]
  -- the algebraic identity `φ₁ u/φ₁ u_c - 1 = (ψ u_c - ψ u)/ψ u`
  have hid : V.P₁.φ (w + ((k : ℤ) : ℂ)) / V.P₁.φ uc - 1 =
      (MandelDim.tau0 (V.P₁.φ uc) - MandelDim.tau0 (V.P₁.φ (w + ((k : ℤ) : ℂ))))
        / MandelDim.tau0 (V.P₁.φ (w + ((k : ℤ) : ℂ))) := by
    have ha : V.P₁.φ (w + ((k : ℤ) : ℂ)) ≠ 0 := srcC_Sm1_phi_ne_zero V huSm
    have hb : V.P₁.φ uc ≠ 0 := srcC_Sm1_phi_ne_zero V hucSm
    rw [MandelDim.tau0, MandelDim.tau0]
    field_simp
    ring
  rw [hid, norm_div]
  set A := ‖MandelDim.tau0 (V.P₁.φ uc) - MandelDim.tau0 (V.P₁.φ (w + ((k : ℤ) : ℂ)))‖ with hA
  set B := ‖MandelDim.tau0 (V.P₁.φ (w + ((k : ℤ) : ℂ)))‖ with hB
  have hnum : A ≤ 1 := hψlt.le
  have hden : 29 * V.η₁ / 40 ≤ B := srcC_Sm1_tau0_phi_lower V huSm
  have hpos : 0 < 29 * V.η₁ / 40 := div_pos (mul_pos (by norm_num) V.hη₁pos) (by norm_num)
  have hBpos : 0 < B := lt_of_lt_of_le hpos hden
  have h3a : A / B ≤ 1 / B := div_le_div_of_nonneg_right hnum hBpos.le
  have h3b : 1 / B ≤ 1 / (29 * V.η₁ / 40) := one_div_le_one_div_of_le hpos hden
  have h4 : 1 / (29 * V.η₁ / 40) = 40 / (29 * V.η₁) := by field_simp
  linarith [h3a, h3b, h4]

/-! ## The explicit lift lies in the source region of the cell -/

/-- **The explicit lift of a fibre point lies in the round period box.**  For `u ∈ fib j k`,

  `lift j k n u - (w_c + n) = log (φ₁ u / φ₁ (uc j + k)) / (2πi)`,

whose norm is bounded by `(3/2)·(40/(29η₁))/(2π) < 1/2` (`Complex.norm_log_one_add_half_le_self`
and `srcC_phi_ratio_close`). -/
lemma lift_mem_ball_half (V : V10) {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    {u : ℂ} (hu : u ∈ V.fib j k) :
    ‖V.lift j k n u - (V.wc j k + ((n : ℤ) : ℂ))‖ < 1 / 2 := by
  rw [V10.lift]
  have hcancel : V.wc j k + ((n : ℤ) : ℂ)
      + Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) / (2 * ↑Real.pi * Complex.I)
      - (V.wc j k + ((n : ℤ) : ℂ))
      = Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))
        / (2 * ↑Real.pi * Complex.I) := by
    ring
  rw [hcancel]
  have hratio := srcC_phi_ratio_close V hSm hu
  have hη := srcC_eta1_ge_64 V
  have hhalf : ‖V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) - 1‖ ≤ 1 / 2 := by
    refine hratio.trans ?_
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 29 * V.η₁)]
    linarith
  have hlog : ‖Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))‖
      ≤ 3 / 2 * (40 / (29 * V.η₁)) := by
    have h := Complex.norm_log_one_add_half_le_self hhalf
    have hRe : (1 : ℂ) + (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) - 1)
        = V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) := by ring
    rw [hRe] at h
    have h2 := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  have hden : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    norm_num
  rw [norm_div, hden]
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hup : ‖Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))‖ / (2 * Real.pi)
      ≤ (3 / 2 * (40 / (29 * V.η₁))) / (2 * Real.pi) := by
    gcongr
  have hfin : (3 / 2 * (40 / (29 * V.η₁))) / (2 * Real.pi) < 1 / 2 := by
    rw [div_lt_iff₀ h2pi]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hηpos : 0 < V.η₁ := V.hη₁pos
    have h60 : 3 / 2 * (40 / (29 * V.η₁)) < 1 := by
      rw [show (3 : ℝ) / 2 * (40 / (29 * V.η₁)) = 60 / (29 * V.η₁) by ring,
        div_lt_one (by linarith : (0 : ℝ) < 29 * V.η₁)]
      linarith
    linarith
  linarith [hup, hfin]

/-! ## The surjectivity -/

theorem wOfCell_image_subset_ball (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) :
    V.wOfCell (j, k, n) '' V.SrcC j k n ⊆ Metric.ball V.wt₀ V.ρ₀ := by
-- a source point maps into the target ball
    rintro y ⟨w, hw, rfl⟩
    have hraw : V.s * MandelDim.piExp w ∈ V.P₁.φ '' V.fib j k := hw.1
    obtain ⟨u, hu, hφu⟩ := hraw
    have huSm : u ∈ V.Sm1 := hSm hu
    -- `uOfSrc` recovers the fibre point by injectivity of `φ₁` on `Sm1`
    have huof : V.uOfSrc (j, k, n) w = u := by
      rw [V10.uOfSrc]
      exact V.uOf_unique huSm hφu
    rw [V10.wOfCell, huof]
    have hmem : (fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ) ∈ V.W 0 :=
      chain_image_mem V hu
    exact (V.wOf_spec hmem).1

/-- **The restricted surjectivity (v10).**  A point `z` of the target ball whose `φ₀`-image lies in
`ball 0 σ₀` is hit by `wOfCell (j,k,n)` on the source region `SrcC j k n`.  This is all that the
assembly uses (`Giw_nonempty`, `Isl_surj`, both applied to points of `ball p r ⊆ ball 0 σ₀`); the
unrestricted form would require `V.htgt'` for every point of `ball wt₀ ρ₀`. -/
theorem wOfCell_mem_image_of_phi_mem (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) {z : ℂ} (hz : z ∈ Metric.ball V.wt₀ V.ρ₀)
    (hσ : V.P₀.φ z ∈ Metric.ball 0 V.σ₀) :
    z ∈ V.wOfCell (j, k, n) '' V.SrcC j k n := by
-- the level-1 preimage of `s·π z` in the base disc `W 0`
    obtain ⟨u₀, hu₀ball, hu₀φ⟩ := V.htgt' z hz hσ
    have hu₀W : u₀ ∈ V.W 0 := by
      rw [V.hbase]
      exact Metric.ball_subset_ball V.hρ₁le hu₀ball
    -- lift it backwards along the chain: `u ∈ fib j k`, `ĥ^[j] u = u₀ + k`
    obtain ⟨u, ⟨hu_fib, hu_eq⟩, -⟩ :=
      chain_preimage_mem V.hIsChain V.hReq (j := j) (k := k) hu₀W
    refine ⟨V.lift j k n u, ⟨V.lift_mem_Raw (n := n) hSm hu_fib, ?_⟩, ?_⟩
    · rw [Metric.mem_ball]
      simpa [dist_eq_norm] using lift_mem_ball_half V (n := n) hSm hu_fib
    -- the lift realises the value `z`
    have hpi : MandelDim.piExp (V.lift j k n u) = V.P₁.φ u / V.s :=
      V.lift_piExp (n := n) hSm hu_fib
    have hsu : V.s * MandelDim.piExp (V.lift j k n u) = V.P₁.φ u := by
      rw [hpi, mul_div_cancel₀ _ V.hs]
    have huo : V.uOfSrc (j, k, n) (V.lift j k n u) = u := by
      rw [V10.uOfSrc, hsu]
      exact V.uOf_unique (hSm hu_fib) rfl
    have hiter : (fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ) = u₀ := by
      rw [hu_eq]; ring
    have hwz : V.wOf u₀ = z := by
      have h1 := (V.wOf_spec hu₀W).2
      have h2 : MandelDim.piExp (V.wOf u₀) = MandelDim.piExp z := by
        rw [h1, hu₀φ, mul_div_cancel_left₀ _ V.hs]
      exact piExp_injOn_ball_lift (a := V.wt₀) (ρ := V.ρ₀) V.hρ₀le (V.wOf_spec hu₀W).1 hz h2
    rw [V10.wOfCell, huo, hiter, hwz]

end

end Work.Repel
