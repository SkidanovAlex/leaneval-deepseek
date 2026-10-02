import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.IFT.Basic
import Submission.Work.NAKANE2.Surgery.admissible_glueMuW
import Submission.Work.NAKANE2.Surgery.glueMuW_invariant
import Submission.Work.NAKANE2.Surgery.glueMuW_eq_zero_of_mem
import Submission.Work.NAKANE2.Surgery.gv_ratio
import Submission.Work.NAKANE2.Surgery.gv_basic
import Submission.Work.NAKANE2.Surgery.gv_W_hits
import Submission.Work.NAKANE2.Surgery.W_basic
import Submission.Work.FBif.bounded_conj_of_decay
import Submission.Work.MRMT.Found.norm_symm_sub_le
import Submission.Work.NAKANE2.Surgery.norm_glueMuW_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

open LeanEval.ComplexAnalysis (Tantibar)
open Filter Set Function
open scoped Topology

set_option autoImplicit false

noncomputable section

/-! ## Geometry of the conformal region `W` -/

/-- A point of `W c₀` keeps `T_{c₀} z` strictly outside the ball of radius `ρ`: the band
condition bounds `G` by `9 g₀/8` on that ball whereas `G (T_{c₀} z) = 2 G z > 3 g₀/2`. -/
theorem W_dist_Tantibar {c₀ : ℂ} (D : SurgeryData c₀) {z : ℂ} (hz : z ∈ W c₀) :
    D.ρ < dist (Tantibar c₀ z) c₀ := by
  by_contra hcon
  have hle : dist (Tantibar c₀ z) c₀ ≤ D.ρ := not_lt.mp hcon
  have hmem : Tantibar c₀ z ∈ Metric.closedBall c₀ (3 * D.ρ) := by
    rw [Metric.mem_closedBall]
    linarith [D.hρ]
  have hband : G c₀ (Tantibar c₀ z) < 9 / 8 * Gcrit c₀ := (D.hband hmem).2
  have hG : G c₀ (Tantibar c₀ z) = 2 * G c₀ z := gvW_G_Tantibar c₀ z
  rw [mem_W] at hz
  linarith [D.Gcrit_pos]

/-- Consequently the bump vanishes at `T_{c₀} z` for `z ∈ W c₀`. -/
theorem chiC_Tantibar_eq_zero_of_mem_W {c₀ : ℂ} (D : SurgeryData c₀) {z : ℂ}
    (hz : z ∈ W c₀) : chiC c₀ D.χ (Tantibar c₀ z) = 0 := by
  have hle : D.χ.rOut ≤ dist (Tantibar c₀ z) c₀ := by
    rw [D.hrOut]
    exact le_of_lt (W_dist_Tantibar D hz)
  have h0 : D.χ (Tantibar c₀ z) = 0 := ContDiffBump.zero_of_le_dist D.χ hle
  change ((D.χ (Tantibar c₀ z) : ℝ) : ℂ) = 0
  rw [h0, Complex.ofReal_zero]

/-- The deformed map `g_v` maps the forward-invariant conformal region `W c₀` into itself
(indeed it coincides with `T_{c₀}` there). -/
theorem gv_W_maps {c₀ : ℂ} (D : SurgeryData c₀) (v : ℂ) {z : ℂ} (hz : z ∈ W c₀) :
    gv c₀ D.χ v z ∈ W c₀ := by
  have hchi := chiC_Tantibar_eq_zero_of_mem_W D hz
  have h1 : gv c₀ D.χ v z = Tantibar c₀ z := by
    rw [gv_apply, hchi, zero_mul, add_zero]
  rw [h1]
  exact (W_basic D).2.2 z hz

/-- If the orbit of `z` under `g_v` never enters `W c₀` then `∂g_v z = 0`. -/
theorem gv_dz_eq_zero_of_never_hits {c₀ : ℂ} (D : SurgeryData c₀) {v : ℂ}
    (hv : ‖v‖ < rConst D) {z : ℂ} (h : ∀ n : ℕ, ((gv c₀ D.χ v)^[n]) z ∉ W c₀) :
    Work.MRMT.dz (gv c₀ D.χ v) z = 0 := by
  by_contra hne
  exact h 1 (by rw [Function.iterate_one]; exact (gv_W_hits D hv).2 z hne)

/-- The singleton `{0}` is "discrete" in the sense needed by MRMT `M2″`. -/
theorem eventually_notMem_singleton (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ∉ ({0} : Set ℂ) := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds
      (isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff]))

/-- **Far-field evaluation of the straightening parameter** (complex version of the sibling
`Work.NAKANE2.Surgery.far_bound_of_conj`, needed here because the additive constants `c`, `c'`
of the quadratic antipolynomials are complex; the proof is the same and purely algebraic in
`c, c'`).  Let `Φ` be a homeomorphism of `ℂ` which is `C/‖z‖`-close to the identity outside the
ball of radius `R` (`R ≥ 1`, `C ≥ 0`), let `F` agree outside that ball with the antiholomorphic
quadratic `z ↦ (star z)^2 + c`, and suppose that `Φ ∘ F ∘ Φ⁻¹` agrees everywhere with
`z ↦ (star z)^2 + c'`.  Then `‖c' - c‖ ≤ 3 C`.

At a real point `z = M` far out, `w := Φ⁻¹ z` is still far out and
`c' - c = (Φ (F w) - F w) + ((star w)^2 - (star z)^2)`, whose two terms are bounded by
`C/2` and `2C + C^2/‖w‖^2 ≤ 2C + C/2` respectively. -/
theorem far_bound_of_conjC {c c' : ℂ} {C R : ℝ} {Φ : ℂ ≃ₜ ℂ} {F : ℂ → ℂ}
    (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hdec : ∀ z : ℂ, R ≤ ‖z‖ → ‖Φ z - z‖ ≤ C / ‖z‖)
    (hasymp : ∀ z : ℂ, R ≤ ‖z‖ → F z = (star z) ^ 2 + c)
    (hconj : ∀ z : ℂ, Φ (F ((Φ.symm : ℂ → ℂ) z)) = (star z) ^ 2 + c') :
    ‖c' - c‖ ≤ 3 * C := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
  -- A far-out real point `z = M`, large compared to `R`, `C` and `‖c‖`.
  set M : ℝ := 8 * (R + C + 1) + 4 * (R + ‖c‖ + 2) + 4 * (C + 1) + 4 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; nlinarith [hR0, hc0, hC]
  have hM8 : 8 * (R + C + 1) ≤ M := by rw [hMdef]; nlinarith [hR0, hc0, hC]
  have hMR : R ≤ M / 2 := by rw [hMdef]; nlinarith [hR0, hc0, hC]
  have hM2C : 2 * C + 2 ≤ M / 2 := by rw [hMdef]; nlinarith [hR0, hc0, hC]
  have hMcR : ‖c‖ + R + 2 ≤ M / 2 := by rw [hMdef]; nlinarith [hR0, hc0, hC]
  have hM4C : 4 * C ≤ M ^ 2 := by
    have h8C : 8 * C + 8 ≤ M := by rw [hMdef]; nlinarith [hR0, hc0, hC]
    nlinarith [h8C, hC, sq_nonneg M, sq_nonneg (8 * C + 8)]
  set z : ℂ := (M : ℂ) with hzdef
  have hnormz : ‖z‖ = M := by
    rw [hzdef]
    simp [abs_of_pos hMpos]
  set w : ℂ := (Φ.symm : ℂ → ℂ) z with hwdef
  -- `w = Φ⁻¹ z` is still far out.
  have hwz : ‖w - z‖ ≤ 2 * C / M := by
    have h := Work.MRMT.Found.norm_symm_sub_le (F := Φ) hR hC hdec z (by rw [hnormz]; exact hM8)
    rw [hwdef, ← hnormz]
    exact h
  have hwlow : M - 2 * C / M ≤ ‖w‖ := by
    have h1 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      have h := norm_add_le (z - w) w
      rw [sub_add_cancel] at h
      rw [norm_sub_rev z w] at h
      linarith [h]
    rw [hnormz] at h1
    linarith [hwz]
  have hwM2 : M / 2 ≤ ‖w‖ := by
    have h2c : 2 * C / M ≤ M / 2 := by
      rw [div_le_iff₀ hMpos]
      nlinarith [hM4C]
    linarith [hwlow, h2c]
  have hwR : R ≤ ‖w‖ := le_trans hMR hwM2
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (by linarith [hMpos] : (0 : ℝ) < M / 2) hwM2
  -- Rewriting the conjugacy relation.
  have hPhi_w : Φ w = z := by
    rw [hwdef]; exact Φ.apply_symm_apply z
  have hFw : F w = (star w) ^ 2 + c := hasymp w hwR
  have hPhiFw : Φ (F w) = (star z) ^ 2 + c' := by
    rw [hwdef]; exact hconj z
  have hkey : c' - c = (Φ (F w) - F w) + ((star w) ^ 2 - (star z) ^ 2) := by
    rw [hPhiFw, hFw]; ring
  -- Size bounds on `w`.
  have hwge : ‖c‖ + R + 2 ≤ ‖w‖ := le_trans hMcR hwM2
  have hsqw : ‖c‖ + R + 2 ≤ ‖w‖ ^ 2 := by
    have h1 : 1 ≤ ‖w‖ := by linarith [hwge, hR0]
    nlinarith [hwge, h1, sq_nonneg (‖w‖ - 1)]
  -- The asymptotic term.
  have hnormFw : R + 2 ≤ ‖F w‖ := by
    have h2 : ‖(star w) ^ 2‖ = ‖w‖ ^ 2 := by rw [norm_pow, norm_star]
    have h1 : ‖(star w) ^ 2‖ - ‖c‖ ≤ ‖F w‖ := by
      have h := norm_sub_norm_le ((star w) ^ 2) ((-c : ℂ))
      rw [hFw]
      simpa using h
    rw [h2] at h1
    linarith [hsqw]
  have hA : ‖Φ (F w) - F w‖ ≤ C / 2 := by
    have h1 : ‖Φ (F w) - F w‖ ≤ C / ‖F w‖ := hdec (F w) (by linarith [hnormFw])
    have h2 : C / ‖F w‖ ≤ C / 2 :=
      div_le_div_of_nonneg_left hC (by norm_num) (by linarith [hnormFw] : (2 : ℝ) ≤ ‖F w‖)
    linarith
  -- The quadratic difference term.
  have hB : ‖(star w) ^ 2 - (star z) ^ 2‖ ≤ 2 * C + C ^ 2 / ‖w‖ ^ 2 := by
    have hfac : (star w) ^ 2 - (star z) ^ 2 = (star w - star z) * (star w + star z) := by ring
    rw [hfac, norm_mul]
    have h1 : ‖star w - star z‖ ≤ C / ‖w‖ := by
      have h := hdec w hwR
      rw [hPhi_w] at h
      rw [← star_sub, norm_star, norm_sub_rev w z]
      exact h
    have h2 : ‖star w + star z‖ ≤ 2 * ‖w‖ + C / ‖w‖ := by
      have ha : star w + star z = star (w + z) := by rw [star_add]
      have hb : ‖w + z‖ ≤ ‖w‖ + ‖z‖ := norm_add_le w z
      have hz : ‖z‖ ≤ ‖w‖ + C / ‖w‖ := by
        have h := hdec w hwR
        rw [hPhi_w] at h
        have h2' : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
          have hh := norm_add_le w (z - w)
          rwa [add_sub_cancel] at hh
        linarith
      rw [ha, norm_star]
      linarith [hb, hz]
    have hCw : 0 ≤ C / ‖w‖ := div_nonneg hC (norm_nonneg w)
    calc ‖star w - star z‖ * ‖star w + star z‖
        ≤ (C / ‖w‖) * (2 * ‖w‖ + C / ‖w‖) := mul_le_mul h1 h2 (norm_nonneg _) hCw
      _ = 2 * C + C ^ 2 / ‖w‖ ^ 2 := by
          field_simp
  have hC2 : C ^ 2 / ‖w‖ ^ 2 ≤ C / 2 := by
    have hsq : 2 * C ≤ ‖w‖ ^ 2 := by
      have h : 2 * C + 2 ≤ ‖w‖ := le_trans hM2C hwM2
      nlinarith [h, hC]
    rw [div_le_iff₀ (pow_pos hwpos 2)]
    nlinarith [hsq, hC]
  rw [hkey]
  calc ‖(Φ (F w) - F w) + ((star w) ^ 2 - (star z) ^ 2)‖
      ≤ ‖Φ (F w) - F w‖ + ‖(star w) ^ 2 - (star z) ^ 2‖ := norm_add_le _ _
    _ ≤ C / 2 + (2 * C + C ^ 2 / ‖w‖ ^ 2) := add_le_add hA hB
    _ ≤ 3 * C := by linarith [hC2]

/-- Route.  Let `μ := glueMuW (gv c₀ D.χ v) (W c₀)`, `θ := principal μ`, `κ := 2 * D.Λ * ‖v‖`.
`admissible_glueMuW` gives `Admissible μ` (with `κ ≤ 1/2`, support in `closedBall 0 D.R₀`),
`norm_glueMuW_le` gives `‖μ z‖ ≤ κ`, `glueMuW_invariant` gives `μ = pullRev μ (gv)`, and
`gv_ratio`/`gv_basic` give the hypotheses of MRMT `principal_conj_contDiff` (M2″) with `S = {0}`.
So `G := θ ∘ gv ∘ θ.symm` is antiholomorphic.  `Work.FBif.principal_decay_bound` gives
`‖θ z - z‖ ≤ C/‖z‖` for `‖z‖ ≥ max (2*(R₀+1)) 1` with `C ≤ 4κ(R₀+1)²`; hence
`‖G z - (star z)^2‖` is bounded (compact part by continuity of `G`, far part because `gv = T_{c₀}`
off the bounded set `V` and `(star(θ.symm z))^2 - (star z)^2 = O(1)`), and
`Work.FBif.antiholo_of_norm_sub_sq_bounded` yields `c'` with `G = T_{c'}`.  Finally
`c' - c₀ = G z - (star z)^2` at a far point `z`, computed from `θ u = u + e u` with `‖e u‖ ≤ C/‖u‖`,
gives `‖c' - c₀‖ ≤ 3C`. -/
theorem straighten {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) {v : ℂ}
    (hv : ‖v‖ < Work.NAKANE2.rConst D) :
    ∃ c' : ℂ,
      (∀ z : ℂ,
        Work.MRMT.Found.principal (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀))
            (Work.NAKANE2.gv c₀ D.χ v z)
          = LeanEval.ComplexAnalysis.Tantibar c'
            (Work.MRMT.Found.principal
              (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀)) z)) ∧
      ‖c' - c₀‖ ≤ Work.NAKANE2.Kconst D * ‖v‖ := by
  classical
  obtain ⟨hratio, hrev⟩ := gv_ratio D hv
  obtain ⟨hconf, hone⟩ := gv_W_hits D hv
  have hΛpos : 0 < D.Λ := by linarith [D.hΛ1]
  have hvn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  -- ## the constants
  have hκ0 : 0 ≤ 2 * D.Λ * ‖v‖ := by nlinarith
  have hκhalf : 2 * D.Λ * ‖v‖ ≤ 1 / 2 := by
    have h := norm_mul_Λ_le D hv
    nlinarith
  have hκ1 : 2 * D.Λ * ‖v‖ < 1 := by linarith
  -- ## admissibility of the invariant coefficient
  have hμadm : Work.MRMT.Found.Admissible
      (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀)) :=
    admissible_glueMuW (F := Work.NAKANE2.gv c₀ D.χ v) (W := Work.NAKANE2.W c₀)
      (κ := 2 * D.Λ * ‖v‖) (R := D.R₀) hκ0 hκ1
      ((gv_basic D v).1.continuous.measurable) ((W_basic D).1.measurableSet)
      hratio hone (fun z hz => glueMuW_eq_zero_of_mem hz) D.hWc
  have hsupp : Function.support
      (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀))
        ⊆ Metric.closedBall 0 D.R₀ := by
    intro z hz
    by_contra hcon
    have hzW : z ∈ Work.NAKANE2.W c₀ := by
      by_contra hW
      exact hcon (D.hWc hW)
    exact (Function.mem_support.mp hz) (glueMuW_eq_zero_of_mem hzW)
  have hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀) z‖
        ≤ 2 * D.Λ * ‖v‖ :=
    Filter.Eventually.of_forall (norm_glueMuW_le hratio hκ0 hone)
  -- ## the far-field normalisation
  obtain ⟨C, hC0, hCub, hdecay⟩ :=
    Work.FBif.principal_decay_bound hμadm hκ0 hκhalf hsupp hb
  -- ## invariance of the coefficient under `g_v`
  have hinv : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀) z
        = Work.MRMT.Found.pullRev
            (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀))
            (Work.NAKANE2.gv c₀ D.χ v) z :=
    Filter.Eventually.of_forall
      (glueMuW_invariant (fun z hz => gv_W_maps D v hz) hconf
        (fun z h => gv_dz_eq_zero_of_never_hits D hv h))
  -- ## antiholomorphy of the conjugate map
  have hAnti := Work.MRMT.Found.principal_conj_contDiff (hμ := hμadm)
    (f := Work.NAKANE2.gv c₀ D.χ v) (S := ({0} : Set ℂ))
    (gv_basic D v).1 eventually_notMem_singleton hrev hinv
  -- ## uniform boundedness of `G z - (star z)^2`
  set R1 : ℝ := max (2 * (D.R₀ + 1)) 1 with hR1def
  have hR1ge1 : 1 ≤ R1 := le_max_right _ _
  have hR1geR0 : D.R₀ ≤ R1 := by
    have h : D.R₀ ≤ 2 * (D.R₀ + 1) := by linarith [D.hR₀]
    exact le_trans h (le_max_left _ _)
  have hhasymp : ∀ z : ℂ, R1 ≤ ‖z‖ →
      Work.NAKANE2.gv c₀ D.χ v z = (star z) ^ 2 + c₀ := by
    intro z hz
    have hzR0 : D.R₀ < ‖z‖ := by
      have h2 : 2 * (D.R₀ + 1) ≤ R1 := le_max_left _ _
      linarith [D.hR₀]
    have hzW : z ∈ Work.NAKANE2.W c₀ := by
      by_contra hW
      have hmem := D.hWc hW
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      linarith
    have hchi := chiC_Tantibar_eq_zero_of_mem_W D hzW
    have h1 : Work.NAKANE2.gv c₀ D.χ v z = Tantibar c₀ z := by
      rw [Work.NAKANE2.gv_apply, hchi, zero_mul, add_zero]
    rw [h1]
    simp only [Tantibar, starRingEnd_apply]
  have hbound : ∃ K : ℝ, ∀ z : ℂ,
      ‖Work.MRMT.Found.principal
          (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀))
        (Work.NAKANE2.gv c₀ D.χ v
          (((Work.MRMT.Found.principal
              (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀))).symm
            : ℂ → ℂ) z)) - (star z) ^ 2‖ ≤ K :=
    Work.FBif.bounded_conj_of_decay (c := c₀)
      (Φ := Work.MRMT.Found.principal
        (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀)))
      (F := Work.NAKANE2.gv c₀ D.χ v) (R := R1) (C := C)
      hR1ge1 hC0 (gv_basic D v).1.continuous hdecay hhasymp
  -- ## Liouville
  obtain ⟨c', hc'⟩ := Work.FBif.antiholo_of_norm_sub_sq_bounded hAnti hbound
  have hc'' : ∀ z : ℂ,
      Work.MRMT.Found.principal
          (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀))
        (Work.NAKANE2.gv c₀ D.χ v
          (((Work.MRMT.Found.principal
              (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀))).symm
            : ℂ → ℂ) z)) = Tantibar c' z := by
    intro z
    simpa only [Function.comp_apply] using hc' z
  refine ⟨c', ?_, ?_⟩
  · intro z
    have h := hc''
      (Work.MRMT.Found.principal
        (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀)) z)
    rwa [Homeomorph.symm_apply_apply] at h
  · have hconj : ∀ z : ℂ,
        Work.MRMT.Found.principal
            (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀))
          (Work.NAKANE2.gv c₀ D.χ v
            (((Work.MRMT.Found.principal
                (Work.NAKANE2.glueMuW (Work.NAKANE2.gv c₀ D.χ v) (Work.NAKANE2.W c₀))).symm
              : ℂ → ℂ) z)) = (star z) ^ 2 + c' := by
      intro z
      rw [hc'' z]
      simp only [Tantibar, starRingEnd_apply]
    have h3C : ‖c' - c₀‖ ≤ 3 * C :=
      far_bound_of_conjC (c := c₀) (c' := c') (C := C) (R := R1)
        hR1ge1 hC0 hdecay hhasymp hconj
    calc ‖c' - c₀‖ ≤ 3 * C := h3C
      _ ≤ 24 * D.Λ * (D.R₀ + 1) ^ 2 * ‖v‖ := by
          have hstep : 3 * C ≤ 3 * (4 * (2 * D.Λ * ‖v‖) * (D.R₀ + 1) ^ 2) := by
            linarith [hCub]
          have hexp : 3 * (4 * (2 * D.Λ * ‖v‖) * (D.R₀ + 1) ^ 2)
              = 24 * D.Λ * (D.R₀ + 1) ^ 2 * ‖v‖ := by ring
          linarith [hstep, hexp.le, hexp.ge]
      _ = Work.NAKANE2.Kconst D * ‖v‖ := rfl

end

end Work.NAKANE2.Surgery
