import Mathlib
import Submission.Work.Repel.V10.chain_v9_setup
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.chain_v9_chase
import Submission.Work.Repel.V10.chain_v9_diff
import Submission.Work.Repel.V10.chain_v9_walk
import Submission.Work.Repel.V10.chain_v9_isl
import Submission.Work.Repel.V10.chain_v9_final
import Submission.Work.Repel.V10.chainV9_cells
import Submission.Work.Repel.V10.Isl_sub_halfball
import Submission.Work.Repel.V10.Isl_deriv
import Submission.Work.Repel.V10.Raw_open
import Submission.Work.Repel.V10.SrcC_isConnected
import Submission.Work.Repel.V10.SrcC_sub_Dflat
import Submission.Work.Repel.V10.uOf_differentiableOn
import Submission.Work.Repel.V10.chain_image_mem
import Submission.Work.Repel.V10.wOfCell_differentiableOn
import Submission.Work.Repel.V10.deriv_relation
import Submission.Work.Repel.V10.wOf_deriv
import Submission.Work.Repel.V10.SrcC_disjoint
import Submission.Work.Repel.V10.isOpen_phi_image_SrcC
import Submission.Work.Repel.V10.wOfCell_injOn_SrcC
import Submission.Work.Repel.invFunOn_differentiableOn
import Submission.Work.Repel.koebe_covering_scaled
import Submission.Work.Repel.growth_le_quarter_alt
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Work.L62.chain
import Submission.Work.Repel.Spec
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Repel.chain_returns_v10` : the §6 link, v10

This file proves the v10 form of the §6 link `Work.Repel.chain_returns_v10`: the hypothesis list of
`chain_returns_v9` with

* `hinjφ₁` and `hcov₁` stated on the **whole** disc `ball cbase ρ = W 0` (v9 had a smaller
  `ball cbase ρ₁`, `ρ₁ ≤ ρ`, which made row 14 — injectivity of `f^[N]` on the source region —
  unprovable; see `NOTES_chain_returns_v9_session2.md` §3 and `chain_v9_fold.lean`);
* `htgt'` restricted to the part of `ball wt₀ ρ₀` whose `φ₀`-image lies in `ball 0 σ₀` (the
  unrestricted form, together with `htgt`, would force `P₁.φ '' W 0 = s·π '' ball wt₀ ρ₀`).

Everything else is H2270's v9 machinery, reused through the module copies in
`Submission/Work/Repel/V10/` (the only change there is the weak `htgt'` field and the three
lemmas that consumed it: `wOfCell_mem_image_of_phi_mem`, `Giw_nonempty`, `Isl_surj`).

## Architecture of the proof

* bundle the hypotheses into `V : Work.Repel.V10` (with `ρ₁ := ρ`);
* `chainV9_cells` supplies `S` with `|S| ≥ N₀`, `fib q.1 q.2.1 ⊆ Sm1`, `|q.2.2| ≤ η/10+1`,
  `1 ≤ q.1`;
* `SrcC_uniform_iterate` supplies one iterate `Nf q` per cell with the composite identity on
  `SrcC q`; `Isl_surj` (row 13) gives `ball p r ⊆ f^{Nf q} '' Isl q`; `Isl_sub_halfball`
  (row 2) gives `Isl q ⊆ ball p (r/2)`; `Isl_deriv` (row 15) gives the derivative bound;
* row 14 is the new content, in three pieces (`srcZ_open`, `cell_room`, `cell_injOn`,
  `cell_ball_data` below):
  - `f^{Nf q}` maps the source region `srcZ q = φ₀ '' SrcC q` **onto** a disc of radius `σ₀`
    about `0` (`cell_room`: apply `hcov₀` to `z ∈ ball 0 σ₀` and then the weak `htgt'` at the
    `hcov₀`-preimage of `z`, as in row 13);
  - `f^{Nf q}` is **injective** on `srcZ q` (`cell_injOn`): `wOfCell` is injective on `SrcC q`
    because `wOf` is injective on `W 0 = ball cbase ρ` (this is exactly the v10 hypothesis
    `hinjφ₁`) and each step of the composite is injective, and `φ₀` is injective on
    `ball wt₀ ρ₀`;
  - the inverse branch `G = (f^{Nf q}|_{srcZ q})⁻¹` is defined on `ball 0 σ₀ ⊇ ball p R`
    (`R := 6·r`), Koebe's one-quarter theorem gives `ball (G p) (R/4 ‖G'p‖) ⊆ srcZ q`, and the
    growth bound `growth_le_quarter_alt` gives `Isl q = G '' (ball p r) ⊆ ball (G p) (R/4 ‖G'p‖)`;
    distinct cells have disjoint `SrcC` (`SrcC_disjoint`), hence disjoint enclosing balls.

The two radii `ρg := 27/(10η)`, `ρk := 271/(100η)` in `cell_ball_data` implement the room needed
to contain the island in a *closed* ball and still have the *open* Koebe ball inside the source
region: `‖p‖ + ρk = 3.76/η < 4/η ≤ σ₀` and `ρg/6 = r`, `ρg < ρk`.
-/

set_option maxHeartbeats 400000

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-! ### Helpers -/

/-- The §6 source region of a cell in the dynamical (z-)plane. -/
def srcZ (V : Work.Repel.V10) (j : ℕ) (k n : ℤ) : Set ℂ := V.P₀.φ '' V.SrcC j k n

theorem srcZ_open (V : Work.Repel.V10) {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) : IsOpen (srcZ V j k n) :=
  V10.isOpen_phi_image_SrcC V hSm hn

/-- **The §6 source region of a cell is mapped onto a disc of radius `σ₀` about `0`.** -/
theorem cell_room (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) {N : ℕ}
    (hN : ∀ w ∈ V.SrcC j k n, V.f ^[N] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (j, k, n) w)) :
    Metric.ball 0 V.σ₀ ⊆ V.f ^[N] '' srcZ V j k n := by
  intro z hz
  obtain ⟨w₁, hw₁, hw₁eq⟩ := V.hcov₀ hz
  have hσ : V.P₀.φ w₁ ∈ Metric.ball 0 V.σ₀ := by rw [hw₁eq]; exact hz
  obtain ⟨w, hw, hweq⟩ := wOfCell_mem_image_of_phi_mem V hj hSm hw₁ hσ
  refine ⟨V.P₀.φ w, ⟨w, hw, rfl⟩, ?_⟩
  rw [hN w hw, hweq, hw₁eq]

/-- **`f^[N]` is injective on the source region of a cell.** -/
theorem cell_injOn (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) (hW0 : Set.InjOn V.P₁.φ (V.W 0)) {N : ℕ}
    (hN : ∀ w ∈ V.SrcC j k n, V.f ^[N] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (j, k, n) w)) :
    Set.InjOn (V.f ^[N]) (srcZ V j k n) := by
  intro y hy y' hy' heq
  obtain ⟨w₁, hw₁, hw₁eq⟩ := hy
  obtain ⟨w₂, hw₂, hw₂eq⟩ := hy'
  rw [← hw₁eq, ← hw₂eq]
  have hconv : V.P₀.φ (V.wOfCell (j, k, n) w₁) = V.P₀.φ (V.wOfCell (j, k, n) w₂) := by
    have e1 : V.P₀.φ (V.wOfCell (j, k, n) w₁) = (V.f ^[N]) y := by
      rw [← hN w₁ hw₁, hw₁eq]
    have e2 : V.P₀.φ (V.wOfCell (j, k, n) w₂) = (V.f ^[N]) y' := by
      rw [← hN w₂ hw₂, hw₂eq]
    rw [e1, e2, heq]
  have h1 : V.wOfCell (j, k, n) w₁ = V.wOfCell (j, k, n) w₂ :=
    V.hinjφ₀ (V.wOfCell_mem_ball hj hSm hw₁) (V.wOfCell_mem_ball hj hSm hw₂) hconv
  have h2 : w₁ = w₂ := V10.wOfCell_injOn_SrcC V hW0 hSm hw₁ hw₂ h1
  rw [h2]

/-- **Every §6 cell carries an enclosing ball inside the source region.** -/
theorem cell_ball_data (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1)
    (hW0 : Set.InjOn V.P₁.φ (V.W 0)) {N : ℕ}
    (hN : ∀ w ∈ V.SrcC j k n, V.f ^[N] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (j, k, n) w)) :
    ∃ u : ℂ, ∃ δ : ℝ, 0 < δ ∧ V.Isl j k n ⊆ Metric.ball u δ ∧
      Metric.ball u δ ⊆ srcZ V j k n := by
  have hDopen : IsOpen (srcZ V j k n) := srcZ_open V hSm hn
  have hFdiff : DifferentiableOn ℂ (V.f ^[N]) (srcZ V j k n) :=
    (V.hfdiff.iterate N).differentiableOn
  have hFinj : Set.InjOn (V.f ^[N]) (srcZ V j k n) := cell_injOn V hj hSm hW0 hN
  have hroom : Metric.ball 0 V.σ₀ ⊆ V.f ^[N] '' srcZ V j k n := cell_room V hj hSm hN
  set G : ℂ → ℂ := Function.invFunOn (V.f ^[N]) (srcZ V j k n) with hGdef
  have hGmem : ∀ z ∈ V.f ^[N] '' srcZ V j k n,
      G z ∈ srcZ V j k n ∧ V.f ^[N] (G z) = z := by
    intro z hz
    have hz' : ∃ a ∈ srcZ V j k n, V.f ^[N] a = z := by simpa [Set.mem_image] using hz
    exact ⟨Function.invFunOn_mem hz', Function.invFunOn_eq hz'⟩
  have hGdiff : DifferentiableOn ℂ G (V.f ^[N] '' srcZ V j k n) :=
    invFunOn_differentiableOn hDopen hFinj hFdiff
  set ρg : ℝ := 27 / (10 * V.η) with hρg
  set ρk : ℝ := 271 / (100 * V.η) with hρk
  have hηpos : 0 < V.η := V.hηpos
  have hρgpos : 0 < ρg := by rw [hρg]; positivity
  have hρkpos : 0 < ρk := by rw [hρk]; positivity
  have hgk : ρg < ρk := by
    rw [hρg, hρk]
    have e : (27:ℝ) / (10 * V.η) = 270 / (100 * V.η) := by ring
    rw [e, div_lt_div_iff_of_pos_right (mul_pos (by norm_num) hηpos)]
    norm_num
  have hρg6 : ρg / 6 = V.r := by
    rw [hρg, V10.r]; field_simp; ring
  have hcl_ball : Metric.closedBall V.p ρk ⊆ Metric.ball 0 V.σ₀ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have hpn : ‖V.p‖ = 1.05 / V.η := V.norm_p
    have h1 : ‖z‖ ≤ ‖z - V.p‖ + ‖V.p‖ := by
      calc ‖z‖ = ‖(z - V.p) + V.p‖ := by congr 1; ring
        _ ≤ ‖z - V.p‖ + ‖V.p‖ := norm_add_le _ _
    have h2 : (271 : ℝ) / (100 * V.η) + 105 / (100 * V.η) < V.σ₀ := by
      have e1 : (271:ℝ)/(100*V.η) + 105/(100*V.η) = 376/(100*V.η) := by ring
      have e2 : (376:ℝ)/(100*V.η) = (94/25)/V.η := by ring
      have e3 : (94/25 : ℝ)/V.η < 4/V.η := by
        rw [div_lt_div_iff_of_pos_right hηpos]; norm_num
      linarith [V.hσ₀big, e1, e2, e3]
    have h3 : ‖V.p‖ = 105/(100*V.η) := by rw [hpn]; ring
    linarith [h1, hz, h2, h3]
  have hcl_room : Metric.closedBall V.p ρk ⊆ V.f ^[N] '' srcZ V j k n :=
    hcl_ball.trans hroom
  have hGdiffk : DifferentiableOn ℂ G (Metric.closedBall V.p ρk) := hGdiff.mono hcl_room
  have hGinjk : Set.InjOn G (Metric.ball V.p ρk) := by
    intro x hx y hy hxy
    have hx' : x ∈ V.f ^[N] '' srcZ V j k n := hcl_room (Metric.ball_subset_closedBall hx)
    have hy' : y ∈ V.f ^[N] '' srcZ V j k n := hcl_room (Metric.ball_subset_closedBall hy)
    have h1 : V.f ^[N] (G x) = x := (hGmem x hx').2
    have h2 : V.f ^[N] (G y) = y := (hGmem y hy').2
    rw [hxy] at h1
    exact h1.symm.trans h2
  have hGder : deriv G V.p ≠ 0 :=
    Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hρkpos
      (hGdiffk.analyticAt (Metric.closedBall_mem_nhds _ hρkpos)) hGinjk
  have hkoebe : Metric.ball (G V.p) (ρk / 4 * ‖deriv G V.p‖) ⊆ srcZ V j k n := by
    refine (koebe_covering_scaled hρkpos hGdiffk hGinjk).trans ?_
    rintro y ⟨x, hx, rfl⟩
    exact (hGmem x (hcl_room (Metric.ball_subset_closedBall hx))).1
  refine ⟨G V.p, ρk / 4 * ‖deriv G V.p‖, ?_, ?_, hkoebe⟩
  · have hpos : 0 < ‖deriv G V.p‖ := norm_pos_iff.mpr hGder
    positivity
  · rintro y ⟨w, hw, rfl⟩
    obtain ⟨hwSrc, hwtgt⟩ := hw
    set z : ℂ := V.P₀.φ (V.wOfCell (j, k, n) w) with hzdef
    have hzball : z ∈ Metric.ball V.p V.r := hwtgt
    have hFy : V.f ^[N] (V.P₀.φ w) = z := by rw [hzdef, hN w hwSrc]
    have hzin : z ∈ V.f ^[N] '' srcZ V j k n := ⟨V.P₀.φ w, ⟨w, hwSrc, rfl⟩, hFy⟩
    have hGy : G z = V.P₀.φ w := by
      have h1 : V.f ^[N] (G z) = z := (hGmem z hzin).2
      refine hFinj (hGmem z hzin).1 ⟨w, hwSrc, rfl⟩ ?_
      rw [h1, hFy]
    have hzcl : z ∈ Metric.closedBall V.p (ρg / 6) := by
      rw [hρg6]; exact Metric.ball_subset_closedBall hzball
    have hGdiffg : DifferentiableOn ℂ G (Metric.closedBall V.p ρg) :=
      hGdiff.mono (fun x hx => hcl_room (Metric.closedBall_subset_closedBall (le_of_lt hgk) hx))
    have hGinjgg : Set.InjOn G (Metric.ball V.p ρg) :=
      hGinjk.mono (Metric.ball_subset_ball (le_of_lt hgk))
    have hgrowth := growth_le_quarter_alt hρgpos hGdiffg hGinjgg z hzcl
    rw [Metric.mem_ball, dist_eq_norm, ← hGy]
    have hp : 0 < ‖deriv G V.p‖ := norm_pos_iff.mpr hGder
    have hstep2 : ‖deriv G V.p‖ * (ρg / 4) < ‖deriv G V.p‖ * (ρk / 4) := by
      nlinarith [hgk, hp]
    calc ‖G z - G V.p‖ ≤ ‖deriv G V.p‖ * (ρg / 4) := hgrowth
      _ < ‖deriv G V.p‖ * (ρk / 4) := hstep2
      _ = ρk / 4 * ‖deriv G V.p‖ := by ring

theorem chain_returns_v10
    {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d₀ : MandelDim.ParabData f₀ D₀) (hd : MandelDim.HornData d₀)
    (f : ℂ → ℂ) (hfdiff : Differentiable ℂ f)
    (η y₀ : ℝ) (K₀ K₀' : Set ℂ) (δ : ℝ)
    (P₀ : MandelDim.PertData d₀ f Set.univ η y₀ K₀ K₀' δ)
    (wt₀ : ℂ) (hφwt₀ : d₀.φ wt₀ = 0)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hK₀' : K₀' = Metric.closedBall wt₀ (2 * r₀))
    (ρ₀ σ₀ : ℝ) (hρ₀ : 0 < ρ₀) (hρ₀le : ρ₀ ≤ 1 / 2) (hσ₀ : 0 < σ₀)
    (hσ₀big : 4 / η ≤ σ₀)
    (hwt₀ : ‖wt₀‖ + ρ₀ ≤ 2 * η)
    (hinjφ₀ : Set.InjOn P₀.φ (Metric.ball wt₀ ρ₀))
    (hcov₀ : Metric.ball 0 σ₀ ⊆ P₀.φ '' Metric.ball wt₀ ρ₀)
    (hsub₀ : Metric.ball wt₀ ρ₀ ⊆ P₀.Dφ)
    (hDflatDR : Work.Repel.Dflat η ⊆ P₀.DR)
    (s : ℂ) (hs : s ≠ 0)
    (η₁ y₁' : ℝ) (K₂ K₂' : Set ℂ) (δ₁ : ℝ)
    (d₁ : MandelDim.ParabData (Work.Repel.g0germ d₀) (Work.Repel.Dg0germ d₀ hd))
    (P₁ : MandelDim.PertData d₁ (Work.Repel.germ1 s P₀.R) (Work.Repel.Dgerm1 s P₀.DR)
      η₁ y₁' K₂ K₂' δ₁)
    (R : ℂ → ℂ) (DR : Set ℂ) (β : ℂ) (ζa ζb : ℂ) (ρ sgn C₀ C₁ C₁' : ℝ) (W : ℕ → Set ℂ)
    (b : ℝ) (hb : 0 < b)
    (hR : R = fun w => P₁.R w + 1 / MandelDim.rotOf (Work.Repel.germ1 s P₀.R))
    (hk : ∃ k : ℕ, 2 ≤ k ∧ 1 / MandelDim.rotOf (Work.Repel.germ1 s P₀.R) = β + k)
    (hβre : 0 ≤ β.re) (hβre' : β.re < 1) (hβim : |β.im| ≤ b)
    (hDRopen : IsOpen DR) (hReq : MandelDim.IsTEquivariantOn R DR)
    (hRdiff : DifferentiableOn ℂ R DR)
    (hDRsub : DR ⊆ P₁.DR)
    (hIsChain : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W)
    (hanchor : ∃ j₀ : ℕ, ∃ w ∈ W j₀, sgn * w.im < η₁ / 4)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hC₁' : 0 < C₁')
    (hη : 100 ≤ η) (hη₁ : η₁ * ‖s‖ = Real.exp (2 * Real.pi * η))
    (hsize : 64 * (C₀ + 1) ≤ η₁)
    (cbase : ℂ) (hbase : W 0 = Metric.ball cbase ρ)
    (hK₂' : Metric.closedBall cbase (2 * ρ) ⊆ K₂')
    (σ₁ : ℝ) (hσ₁ : 0 < σ₁)
    (hinjφ₁ : Set.InjOn P₁.φ (Metric.ball cbase ρ))
    (hcov₁ : Metric.ball (d₁.φ cbase) σ₁ ⊆ P₁.φ '' Metric.ball cbase ρ)
    (hsub₁ : Metric.ball cbase ρ ⊆ P₁.Dφ)
    (hcbase : ‖cbase‖ + ρ ≤ η₁ / 2)
    (htgt' : ∀ w ∈ Metric.ball wt₀ ρ₀, P₀.φ w ∈ Metric.ball 0 σ₀ →
      s * MandelDim.piExp w ∈ P₁.φ '' Metric.ball cbase ρ)
    (htgt : ∀ u' ∈ W 0, ∃ w ∈ Metric.ball wt₀ ρ₀,
      MandelDim.piExp w = P₁.φ u' / s)
    -- the target-side derivative constant (`Cb`) and its defining bound
    (Cb : ℝ) (hCbpos : 0 < Cb)
    (hCbbd : ∀ u' ∈ W 0, ∀ w ∈ Metric.ball wt₀ ρ₀, MandelDim.piExp w = P₁.φ u' / s →
      ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ ≤
        Cb * ‖s‖ * ‖deriv MandelDim.piExp w‖)
    -- (v8) the target-side LOWER bound (Shishikura Step 4 is two-sided) and the fit it implies
    (cb : ℝ) (hcbpos : 0 < cb)
    (hcblo : ∀ u' ∈ W 0, ∀ w ∈ Metric.ball wt₀ ρ₀, MandelDim.piExp w = P₁.φ u' / s →
      cb * ‖s‖ * ‖deriv MandelDim.piExp w‖ ≤ ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖)
    (hfitlo : 4 * (η * η₁ ^ 2 / (320 * (C₀ + 1))) ≤ (C₁ * cb * η ^ 2 * η₁ / 10) ^ 2)
    -- the fit condition (see the file docstring)
    (hfit : η * η₁ ^ 2 / (320 * (C₀ + 1)) ≤
      (10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁) ^ 2 / 256)
    (hangle₀ : ∀ w w' : ℂ, ‖w‖ ≤ 2 * η → ‖w'‖ ≤ 2 * η →
      |Complex.arg (w' + 1 / (2 * MandelDim.rotOf f) - w)| < 2 * Real.pi / 3)
    (hangle₁ : ∀ u u' : ℂ, ‖u‖ ≤ 2 * η₁ → ‖u'‖ ≤ 2 * η₁ →
      |Complex.arg (u' + 1 / (2 * MandelDim.rotOf (Work.Repel.germ1 s P₀.R)) - u)|
        < 2 * Real.pi / 3) :
    ∃ (p : ℂ) (r Kc : ℝ), 0 < r ∧ (p = 1.05 * Complex.I / η ∨ p = -1.05 * Complex.I / η) ∧
      ∃ RD : Work.Repel.ReturnData f p r Kc,
        η * η₁ ^ 2 / (320 * (C₀ + 1)) ≤ (RD.N : ℝ) ∧
        Kc ≤ 10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁ := by
  classical
  have hρpos : 0 < ρ := by
    obtain ⟨w₀, hw₀⟩ := (hIsChain.open_conn 0).2.nonempty
    rw [hbase] at hw₀
    exact lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hw₀)
  let V : Work.Repel.V10 :=
    { f₀ := f₀, D₀ := D₀, d₀ := d₀, hd := hd, f := f, hfdiff := hfdiff, η := η, y₀ := y₀,
      K₀ := K₀, K₀' := K₀', δ := δ, P₀ := P₀, wt₀ := wt₀, hφwt₀ := hφwt₀, r₀ := r₀, hr₀ := hr₀,
      hK₀' := hK₀', ρ₀ := ρ₀, σ₀ := σ₀, hρ₀ := hρ₀, hρ₀le := hρ₀le, hσ₀ := hσ₀,
      hσ₀big := hσ₀big, hwt₀ := hwt₀, hinjφ₀ := hinjφ₀, hcov₀ := hcov₀, hsub₀ := hsub₀,
      hDflatDR := hDflatDR, s := s, hs := hs, η₁ := η₁, y₁' := y₁', K₂ := K₂, K₂' := K₂',
      δ₁ := δ₁, d₁ := d₁, P₁ := P₁, R := R, DR := DR, β := β, ζa := ζa, ζb := ζb, ρ := ρ,
      sgn := sgn, C₀ := C₀, C₁ := C₁, C₁' := C₁', W := W, b := b, hb := hb, hR := hR, hk := hk,
      hβre := hβre, hβre' := hβre', hβim := hβim, hDRopen := hDRopen, hReq := hReq,
      hRdiff := hRdiff, hDRsub := hDRsub, hIsChain := hIsChain, hanchor := hanchor, hC₀ := hC₀,
      hC₁ := hC₁, hC₁' := hC₁', hη := hη, hη₁ := hη₁, hsize := hsize, cbase := cbase,
      hbase := hbase, hK₂' := hK₂', ρ₁ := ρ, σ₁ := σ₁, hρ₁ := hρpos, hρ₁le := le_refl ρ,
      hσ₁ := hσ₁, hinjφ₁ := hinjφ₁, hcov₁ := hcov₁, hsub₁ := hsub₁, hcbase := hcbase,
      htgt' := htgt', htgt := htgt, Cb := Cb, hCbpos := hCbpos, hCbbd := hCbbd, cb := cb,
      hcbpos := hcbpos, hcblo := hcblo, hfitlo := hfitlo, hfit := hfit, hangle₀ := hangle₀,
      hangle₁ := hangle₁ }
  have hW0 : Set.InjOn V.P₁.φ (V.W 0) := by rw [V.hbase]; exact V.hinjφ₁
  obtain ⟨S, hScard, hSmS, hnS, hjS⟩ := chainV9_cells V
  have hiter_exists : ∀ q ∈ S, ∃ N : ℕ, 1 ≤ N ∧ ∀ w ∈ V.SrcC q.1 q.2.1 q.2.2,
      V.f ^[N] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (q.1, q.2.1, q.2.2) w) :=
    fun q hq => V.SrcC_uniform_iterate (hjS q hq) (hSmS q hq) (hnS q hq)
  let Nf : ℕ × ℤ × ℤ → ℕ := fun q => if h : q ∈ S then Classical.choose (hiter_exists q h) else 1
  have hNf : ∀ q ∈ S, 1 ≤ Nf q ∧ ∀ w ∈ V.SrcC q.1 q.2.1 q.2.2,
      V.f ^[Nf q] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (q.1, q.2.1, q.2.2) w) := by
    intro q hq
    have h1 : Nf q = Classical.choose (hiter_exists q hq) := dif_pos hq
    rw [h1]
    exact Classical.choose_spec (hiter_exists q hq)
  have hball_exists : ∀ q ∈ S, ∃ u : ℂ, ∃ δ : ℝ, 0 < δ ∧
      V.Isl q.1 q.2.1 q.2.2 ⊆ Metric.ball u δ ∧
      Metric.ball u δ ⊆ V.P₀.φ '' V.SrcC q.1 q.2.1 q.2.2 :=
    fun q hq => cell_ball_data V (hjS q hq) (hSmS q hq) (hnS q hq) hW0 (hNf q hq).2
  let u : ℕ × ℤ × ℤ → ℂ := fun q => if h : q ∈ S then Classical.choose (hball_exists q h) else 0
  let δ : ℕ × ℤ × ℤ → ℝ :=
    fun q => if h : q ∈ S then Classical.choose (Classical.choose_spec (hball_exists q h)) else 1
  have hspec : ∀ q ∈ S, 0 < δ q ∧ V.Isl q.1 q.2.1 q.2.2 ⊆ Metric.ball (u q) (δ q) ∧
      Metric.ball (u q) (δ q) ⊆ V.P₀.φ '' V.SrcC q.1 q.2.1 q.2.2 := by
    intro q hq
    have hu : u q = Classical.choose (hball_exists q hq) := dif_pos hq
    have hδ : δ q = Classical.choose (Classical.choose_spec (hball_exists q hq)) := dif_pos hq
    rw [hu, hδ]
    exact Classical.choose_spec (Classical.choose_spec (hball_exists q hq))
  have hdisj : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' →
      Disjoint (Metric.ball (u q) (δ q)) (Metric.ball (u q') (δ q')) := by
    intro q hq q' hq' hne
    have hdq := V10.SrcC_disjoint V (hSmS q hq) (hSmS q' hq') hne
    have hdZ : Disjoint (V.P₀.φ '' V.SrcC q.1 q.2.1 q.2.2)
        (V.P₀.φ '' V.SrcC q'.1 q'.2.1 q'.2.2) := by
      rw [Set.disjoint_left] at hdq ⊢
      intro y hy hy'
      obtain ⟨w, hw, hwy⟩ := hy
      obtain ⟨w', hw', hw'y⟩ := hy'
      have hwD : w ∈ MandelDim.Dsm V.η :=
        Work.Repel.Dflat_subset_Dsm V.η (SrcC_sub_Dflat V (hSmS q hq) (hnS q hq) hw)
      have hw'D : w' ∈ MandelDim.Dsm V.η :=
        Work.Repel.Dflat_subset_Dsm V.η (SrcC_sub_Dflat V (hSmS q' hq') (hnS q' hq') hw')
      have hφeq : V.P₀.φ w = V.P₀.φ w' := by rw [hwy, hw'y]
      have hww : w = w' := V.P₀.φ_inj_up hwD hw'D hφeq
      exact hdq hw (by rw [hww]; exact hw')
    exact Disjoint.mono (hspec q hq).2.2 (hspec q' hq').2.2 hdZ
  have hInj : ∀ q ∈ S, Set.InjOn (V.f ^[Nf q]) (V.P₀.φ '' V.SrcC q.1 q.2.1 q.2.2) :=
    fun q hq => cell_injOn V (hjS q hq) (hSmS q hq) hW0 (hNf q hq).2
  obtain ⟨p, r, Kc, hr, hp, RD, hNbound, hKbound⟩ :=
    chain_returns_v9_assembly V S Nf hScard hSmS hjS hNf hInj u δ
      (fun q hq => (hspec q hq).1) (fun q hq => (hspec q hq).2.1)
      (fun q hq => (hspec q hq).2.2) hdisj
      (fun q hq => Isl_sub_halfball V (hSmS q hq) (hnS q hq))
      (fun q hq z hz => Isl_deriv V (hjS q hq) (hSmS q hq) (hnS q hq) (hNf q hq).2 z hz)
  exact ⟨p, r, Kc, hr, hp, RD, hNbound, hKbound⟩


end

end Work.Repel
