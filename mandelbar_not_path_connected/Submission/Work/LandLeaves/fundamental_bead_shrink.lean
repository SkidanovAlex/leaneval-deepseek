/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The fundamental bead shrinks

For a dynamical Böttcher datum `hN : Work.EL.DynB c φ` together with a Böttcher coordinate
`hφ : Work.ParamRays.IsDynBottcher c φ`, the points `Work.EL.rayPt hN θ t` (`t > 1`) of the
dynamic ray of angle `θ` become *uniformly close* as the level window `t ≤ s ≤ t ^ D` shrinks to
the unit circle:

`Work.LandLeaves.fundamental_bead_shrink`:
for every `D ≥ 2` and every `ε > 0` there is `ρ > 1` such that, for **every** angle `θ`, every
base level `t` with `1 < t < ρ` and every pair `t ≤ s₁ ≤ s₂ ≤ t ^ D`,

`‖rayPt hN θ s₂ - rayPt hN θ s₁‖ ≤ ε`.

## Route

The mathematical content is exactly the "beads shrink" lemma `Work.LandLeaves.rayPt_bead` of
`Submission/Work/LandLeaves/rayAccum_subset_fixp.lean`, but stated (i) for an *arbitrary*
dynamical Böttcher datum rather than the canonical one `Work.SeedDyn.dynB hc`, and (ii) with the
quantifier on the angle `θ` *inside* the choice of `ρ`, so that a single `ρ` works simultaneously
for all angles.  Both are formal generalisations, not new mathematics:

* `Work.LandLeaves.invBottcher_infDist_frontier_le_gen` and
  `Work.LandLeaves.invBottcherCloseFilledJulia_gen` are the generalisations of the same-named
  mandelbar-parameter statements to an arbitrary datum `hN` (the only ingredient that needs
  `c ∈ M*`, `nonempty_frontier_escapingSet`, is supplied here from `hφ` through
  `Work.LandLeaves.dynBottcherOnlyOnMandelbar`);
* `Work.LandLeaves.rayPt_bead_angle` is `rayPt_bead` with the angle quantified last — the proof is
  verbatim, since the radius `ρ` it produces (from `invBottcherCloseFilledJulia_gen`) does not
  involve `θ`.

Assembly.  Koebe's quarter theorem (`Work.LandLeaves.koebeDerivBound`) together with
`invBottcherCloseFilledJulia_gen` gives `‖rayPt hN θ r - rayPt hN θ t‖ ≤ ε` for every `r` in a
window of *geometric* length `M` above the base level `t`, uniformly in `θ`.  Given the exponent
`D`, choose `ρ := ρ₀ ^ (1 / D)` where `ρ₀` is the (θ-independent) radius of the geometric-window
statement: then `t < ρ` forces `t ^ D < ρ ^ D = ρ₀`, so both `s₁` and `s₂` lie in the window; the
triangle inequality through the base point `rayPt hN θ t` finishes.

## Main results

* `Work.LandLeaves.invBottcher_infDist_frontier_le_gen`
* `Work.LandLeaves.invBottcherCloseFilledJulia_gen`
* `Work.LandLeaves.rayPt_bead_angle`
* `Work.LandLeaves.fundamental_bead_shrink`
-/
import Mathlib
import Submission.Work.LandLeaves.rayAccum_subset_fixp
import Submission.Work.ELTop.All
import Submission.Work.SeedDyn.Main
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Set Metric Filter
open scoped Topology ComplexConjugate

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet filledJulia)

/-! ## The inverse Böttcher coordinate near the unit circle, for an arbitrary datum -/

/-- **The inverse Böttcher coordinate maps a neighbourhood of the unit circle close to the
frontier of the escaping set**, for an arbitrary dynamical Nakane datum `hN : DynB c φ`.  This is
the generalisation of `Work.LandLeaves.invBottcher_infDist_frontier_le` (there stated for the
canonical datum `Work.SeedDyn.dynB hc`); the proof is identical. -/
theorem invBottcher_infDist_frontier_le_gen {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : IsDynBottcher c φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < ρ →
      Metric.infDist (Work.ELRig.invBottcher hN w)
        (frontier (escapingSet c)) ≤ ε := by
  obtain ⟨R, -, hR⟩ := invBottcher_norm_le hN hφ
  obtain ⟨δ, hδpos, hδ⟩ := exists_gap_infDist_frontier (c := c) (M := R) hε
  refine ⟨min 2 (Real.exp (min δ 1 / 2)), ?_, ?_⟩
  · refine lt_min (by norm_num) ?_
    rw [Real.one_lt_exp_iff]
    have h := lt_min hδpos one_pos
    linarith
  · intro w hw hwr
    have hw2 : ‖w‖ < 2 := lt_of_lt_of_le hwr (min_le_left _ _)
    have hesc : Escaping c (Work.ELRig.invBottcher hN w) := by
      have h := (Work.ELRig.invBottcher_spec hN hw).1
      rw [Work.Bottcher.Contraction.escapeSet_eq_escapingSet c] at h
      exact h
    have hmod : Work.ParamRays.greenFun c (Work.ELRig.invBottcher hN w) = Real.log ‖w‖ :=
      greenFun_eq_log_norm hφ hesc (Work.ELRig.invBottcher_spec hN hw).2
    have hlogr : Real.log (min 2 (Real.exp (min δ 1 / 2))) ≤ δ := by
      have hpos1 : (0 : ℝ) < min 2 (Real.exp (min δ 1 / 2)) :=
        lt_min (by norm_num) (Real.exp_pos _)
      have h1 : Real.log (min 2 (Real.exp (min δ 1 / 2))) ≤
          Real.log (Real.exp (min δ 1 / 2)) := Real.log_le_log hpos1 (min_le_right _ _)
      rw [Real.log_exp] at h1
      have h2 : min δ 1 / 2 ≤ δ := by linarith [min_le_left δ 1]
      linarith
    have hGlt : Work.ParamRays.greenFun c (Work.ELRig.invBottcher hN w) < δ := by
      rw [hmod]
      have hwpos : (0 : ℝ) < ‖w‖ := lt_trans zero_lt_one hw
      have h1 := Real.log_lt_log hwpos hwr
      linarith
    by_contra hcon
    push Not at hcon
    have hle := hδ _ hesc (hR w hw hw2) (le_of_lt hcon)
    linarith

/-- **The inverse Böttcher coordinate is close to the filled Julia set near the unit circle**,
for an arbitrary dynamical Böttcher datum.  This is the generalisation of
`Work.LandLeaves.invBottcherCloseFilledJulia` to an arbitrary `hN : DynB c φ`; the only ingredient
that needs a mandelbar parameter is the nonemptiness of `frontier (escapingSet c)`, which is
supplied from `hφ` via `Work.LandLeaves.dynBottcherOnlyOnMandelbar`. -/
theorem invBottcherCloseFilledJulia_gen {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : IsDynBottcher c φ) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < ρ →
      ∃ y ∈ filledJulia c, ‖y - Work.ELRig.invBottcher hN w‖ ≤ ε := by
  have hc : c ∈ Mandelbar := dynBottcherOnlyOnMandelbar c ⟨φ, hφ⟩
  intro ε hε
  obtain ⟨ρ₀, hρ₀one, hρ₀⟩ := invBottcher_infDist_frontier_le_gen hN hφ hε
  refine ⟨min ρ₀ 2, lt_min hρ₀one (by norm_num), min_le_right _ _, ?_⟩
  intro w hw hwr
  have hwr₀ : ‖w‖ < ρ₀ := lt_of_lt_of_le hwr (min_le_left _ _)
  have hinf : Metric.infDist (Work.ELRig.invBottcher hN w)
      (frontier (escapingSet c)) ≤ ε := hρ₀ w hw hwr₀
  obtain ⟨y, hyfront, hydist⟩ := (isClosed_frontier (s := escapingSet c)).exists_infDist_eq_dist
    (nonempty_frontier_escapingSet c hc) (Work.ELRig.invBottcher hN w)
  refine ⟨y, frontier_escapingSet_subset_filledJulia c hyfront, ?_⟩
  have h1 : dist (Work.ELRig.invBottcher hN w) y ≤ ε := by
    rw [← hydist]
    exact hinf
  simpa [dist_comm, dist_eq_norm] using h1

/-! ## The beads shrink, uniformly in the angle -/

/-- **The beads of the dynamic ray shrink**, for an arbitrary dynamical Böttcher datum and with
the angle quantified inside the choice of `ρ` (so that a single `ρ` works for all angles).  If
`1 < r₁ ≤ r₂` with `r₂ < ρ` and `log r₂ ≤ M log r₁` (`M ≥ 2`), then the corresponding points of
the ray are close, uniformly in `θ`.

This is `Work.LandLeaves.rayPt_bead` with the angle moved inside, proved for an arbitrary datum
`hN` instead of `Work.SeedDyn.dynB hc`; the proof is otherwise verbatim (the radius it produces
comes from `invBottcherCloseFilledJulia_gen` and does not involve `θ`). -/
theorem rayPt_bead_angle {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : IsDynBottcher c φ)
    (M : ℕ) (hM : 2 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧
      ∀ θ : ℝ, ∀ r₁ r₂ : ℝ, 1 < r₁ → r₁ ≤ r₂ → r₂ < ρ →
        Real.log r₂ ≤ (M : ℝ) * Real.log r₁ →
          ‖Work.EL.rayPt hN θ r₂ - Work.EL.rayPt hN θ r₁‖ ≤ ε := by
  intro ε hε
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  set C : ℝ := 4 * (2 : ℝ) ^ M with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  set ε₀ : ℝ := ε / (C + 1) with hε₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; positivity
  have hkey : 4 * (2 : ℝ) ^ M * ε₀ ≤ ε := by
    rw [hε₀def, ← hCdef, mul_div_assoc', div_le_iff₀ (by linarith : 0 < C + 1)]
    nlinarith [hCnn, hε]
  obtain ⟨ρ, hρ1, hρ2, hρ⟩ := invBottcherCloseFilledJulia_gen hN hφ ε₀ hε₀pos
  refine ⟨ρ, hρ1, hρ2, ?_⟩
  intro θ r₁ r₂ hr₁ hr₁₂ hr₂ρ hlog
  set u : ℂ := Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) with hudef
  have hunorm : ‖u‖ = 1 := by
    rw [hudef, Complex.norm_exp]
    simp
  have hray : ∀ t : ℝ, Work.Top.NakaneData.rayPoint θ t = (t : ℂ) * u := by
    intro t
    rw [Work.Top.NakaneData.rayPoint, hudef]
  have hrayPt : ∀ t : ℝ, 1 < t →
      Work.ELRig.invBottcher hN (Work.Top.NakaneData.rayPoint θ t)
        = Work.EL.rayPt hN θ t := by
    intro t ht
    rw [Work.ELRig.invBottcher_rayPoint hN ht]
  have hr₂pos : 0 < r₂ := by linarith
  have hr₁pos : 0 < r₁ := by linarith
  have hr₁ne : r₁ ≠ 1 := by linarith
  have hr₁2 : r₁ ≤ 2 := le_trans hr₁₂ (le_trans hr₂ρ.le hρ2)
  -- (1) the levels lie in a bounded geometric window
  have hr₂pow : r₂ ≤ r₁ ^ M := by
    have h1 : Real.log r₂ ≤ Real.log (r₁ ^ M) := by
      rw [Real.log_pow]
      exact hlog
    calc r₂ = Real.exp (Real.log r₂) := (Real.exp_log hr₂pos).symm
      _ ≤ Real.exp (Real.log (r₁ ^ M)) := Real.exp_le_exp.mpr h1
      _ = r₁ ^ M := Real.exp_log (by positivity)
  have hratio : (r₂ - 1) / (r₁ - 1) ≤ (2 : ℝ) ^ M := by
    have hr₁1 : 0 < r₁ - 1 := by linarith
    have h2 : (r₂ - 1) / (r₁ - 1) ≤ (r₁ ^ M - 1) / (r₁ - 1) :=
      div_le_div_of_nonneg_right (by linarith : r₂ - 1 ≤ r₁ ^ M - 1)
        (by linarith : (0:ℝ) ≤ r₁ - 1)
    have h3 : (r₁ ^ M - 1) / (r₁ - 1) = ∑ i ∈ Finset.range M, r₁ ^ i :=
      (geom_sum_eq hr₁ne M).symm
    have h4 : ∑ i ∈ Finset.range M, r₁ ^ i ≤ ∑ i ∈ Finset.range M, (2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ r₁) hr₁2 i)
    have h5 : ∑ i ∈ Finset.range M, (2 : ℝ) ^ i = (2 : ℝ) ^ M - 1 := by
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) M]
      norm_num
    have h6 : (2 : ℝ) ^ M - 1 ≤ (2 : ℝ) ^ M := by
      have : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
      linarith
    linarith [h2, h3, h4, h5, h6]
  -- (2) the pointwise bound on the derivative along the bead
  have hpoint : ∀ t ∈ Set.Ico r₁ r₂,
      ‖deriv (Work.ELRig.invBottcher hN) (Work.Top.NakaneData.rayPoint θ t)‖
        ≤ 4 * ε₀ / (r₁ - 1) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hr₁ ht.1
    have htpos : 0 < t := by linarith
    have htr₁ : r₁ ≤ t := ht.1
    have htρ : t < ρ := lt_trans ht.2 hr₂ρ
    have hwt : ‖Work.Top.NakaneData.rayPoint θ t‖ = t := by
      rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos htpos]
    obtain ⟨y, hyK, hyε⟩ := hρ _ (by rw [hwt]; exact ht1) (by rw [hwt]; exact htρ)
    have hyesc : y ∉ escapingSet c := by
      rw [← Work.ParamRays.compl_filledJulia c, Set.mem_compl_iff, not_not]
      exact hyK
    have hkoebe := koebeDerivBound hN hφ
      (Work.Top.NakaneData.rayPoint θ t)
      (by rw [hwt]; exact ht1) y hyesc
    rw [hwt] at hkoebe
    have h4 : ‖deriv (Work.ELRig.invBottcher hN)
        (Work.Top.NakaneData.rayPoint θ t)‖ * (t - 1) ≤ 4 * ε₀ := by
      have := le_trans hkoebe hyε
      linarith
    have h5 : ‖deriv (Work.ELRig.invBottcher hN)
        (Work.Top.NakaneData.rayPoint θ t)‖ * (t - 1) / (t - 1) ≤ 4 * ε₀ / (t - 1) :=
      div_le_div_of_nonneg_right h4 (by linarith)
    have h6 : ‖deriv (Work.ELRig.invBottcher hN)
        (Work.Top.NakaneData.rayPoint θ t)‖ * (t - 1) / (t - 1)
          = ‖deriv (Work.ELRig.invBottcher hN)
        (Work.Top.NakaneData.rayPoint θ t)‖ := by
      rw [mul_div_assoc, div_self (by linarith : (t - 1) ≠ 0), mul_one]
    rw [h6] at h5
    refine le_trans h5 (div_le_div_of_nonneg_left (by positivity)
      (by linarith : 0 < r₁ - 1) (by linarith : r₁ - 1 ≤ t - 1))
  -- (3) the mean value inequality
  have hMVT : ‖Work.EL.rayPt hN θ r₂ - Work.EL.rayPt hN θ r₁‖
      ≤ (4 * ε₀ / (r₁ - 1)) * (r₂ - r₁) := by
    have hderiv : ∀ x ∈ Set.Icc r₁ r₂,
        HasDerivWithinAt (fun t : ℝ => Work.ELRig.invBottcher hN
            (Work.Top.NakaneData.rayPoint θ t))
          (deriv (Work.ELRig.invBottcher hN)
            (Work.Top.NakaneData.rayPoint θ x) * u) (Set.Icc r₁ r₂) x := by
      intro x hx
      have hx1 : 1 < x := lt_of_lt_of_le hr₁ hx.1
      have hwt : 1 < ‖Work.Top.NakaneData.rayPoint θ x‖ := by
        rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
        exact hx1
      have han : AnalyticAt ℂ (Work.ELRig.invBottcher hN)
          (Work.Top.NakaneData.rayPoint θ x) :=
        Work.ELRig.analyticAt_invBottcher hN
          (Work.ELRig.analyticOnNhd_dynBottcher hφ) hwt
      have h2 : HasDerivAt (fun s : ℝ => Work.Top.NakaneData.rayPoint θ s) u x := by
        have hc' : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := (hasDerivAt_id x).ofReal_comp
        have := hc'.mul_const u
        simpa [hray] using this
      exact ((han.differentiableAt.hasDerivAt).comp x h2).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico r₁ r₂,
        ‖deriv (Work.ELRig.invBottcher hN)
          (Work.Top.NakaneData.rayPoint θ x) * u‖ ≤ 4 * ε₀ / (r₁ - 1) := by
      intro x hx
      rw [norm_mul, hunorm, mul_one]
      exact hpoint x hx
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => Work.ELRig.invBottcher hN
        (Work.Top.NakaneData.rayPoint θ t))
      (a := r₁) (b := r₂) hderiv hbound r₂ ⟨hr₁₂, le_rfl⟩
    rw [hrayPt r₂ (by linarith), hrayPt r₁ hr₁] at hmain
    exact hmain
  -- (4) assemble
  calc ‖Work.EL.rayPt hN θ r₂ - Work.EL.rayPt hN θ r₁‖
      ≤ (4 * ε₀ / (r₁ - 1)) * (r₂ - r₁) := hMVT
    _ = 4 * ε₀ * ((r₂ - r₁) / (r₁ - 1)) := by ring
    _ ≤ 4 * ε₀ * ((r₂ - 1) / (r₁ - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ ≤ 4 * ε₀ * (2 : ℝ) ^ M := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ ε := by linarith [hkey]

/-! ## The fundamental bead shrinks -/

/-- **The fundamental bead of the dynamic ray shrinks.**  For every exponent `D ≥ 2` and every
`ε > 0` there is `ρ > 1` such that, uniformly over the angle `θ`, the portion of the ray of angle
`θ` between the levels `t` and `t ^ D` has Euclidean diameter `≤ ε` whenever `1 < t < ρ`.

Assembly: the geometric-window statement `Work.LandLeaves.rayPt_bead_angle` (with `M := D`) gives
a common radius `ρ₀ ≤ 2` such that any two levels in one geometric window of ratio `≤ D` above a
common base are within `ε / 2`.  Take `ρ := ρ₀ ^ (1 / D)`, so that `t < ρ` implies
`t ^ D < ρ ^ D = ρ₀`; then both `s₁` and `s₂` lie in the window above the base `t`, and the
triangle inequality through `rayPt hN θ t` gives the claim. -/
theorem fundamental_bead_shrink {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (D : ℕ) (hD : 2 ≤ D) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 1 < ρ ∧ ∀ θ : ℝ, ∀ t : ℝ, 1 < t → t < ρ →
      ∀ s₁ s₂ : ℝ, t ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ t ^ D →
        ‖Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ s₁‖ ≤ ε := by
  intro ε hε
  obtain ⟨ρ₀, hρ₀1, hρ₀2, hρ₀⟩ := rayPt_bead_angle hN hφ D hD (ε / 2) (by linarith)
  set ρ : ℝ := ρ₀ ^ (1 / (D : ℝ)) with hρdef
  have hρgt : 1 < ρ := by
    rw [hρdef]
    exact Real.one_lt_rpow hρ₀1 (by positivity)
  have hρpow : ρ ^ D = ρ₀ := by
    rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hρ₀1)),
      div_mul_cancel₀ 1 (by positivity : ((D : ℕ) : ℝ) ≠ 0), Real.rpow_one]
  refine ⟨ρ, hρgt, ?_⟩
  intro θ t ht1 htρ s₁ s₂ hs₁ hs₁₂ hs₂
  have htD : t ^ D < ρ₀ := by
    rw [← hρpow]
    exact pow_lt_pow_left₀ htρ (by linarith) (by omega : D ≠ 0)
  have hs₂ρ : s₂ < ρ₀ := lt_of_le_of_lt hs₂ htD
  have hs₁ρ : s₁ < ρ₀ := lt_of_le_of_lt (le_trans hs₁₂ hs₂) htD
  have hlog₂ : Real.log s₂ ≤ (D : ℝ) * Real.log t := by
    have hpos : 0 < s₂ := by linarith
    have hthis := Real.log_le_log hpos hs₂
    rwa [Real.log_pow] at hthis
  have hlog₁ : Real.log s₁ ≤ (D : ℝ) * Real.log t := by
    have hpos : 0 < s₁ := by linarith
    have hle : s₁ ≤ t ^ D := le_trans hs₁₂ hs₂
    have hthis := Real.log_le_log hpos hle
    rwa [Real.log_pow] at hthis
  have h2 := hρ₀ θ t s₂ ht1 (le_trans hs₁ hs₁₂) hs₂ρ hlog₂
  have h1 := hρ₀ θ t s₁ ht1 hs₁ hs₁ρ hlog₁
  have hb : ‖Work.EL.rayPt hN θ t - Work.EL.rayPt hN θ s₁‖ ≤ ε / 2 := by
    rw [norm_sub_rev]; exact h1
  have hsplit : Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ s₁
      = (Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ t)
        + (Work.EL.rayPt hN θ t - Work.EL.rayPt hN θ s₁) := by ring
  calc ‖Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ s₁‖
      = ‖(Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ t)
          + (Work.EL.rayPt hN θ t - Work.EL.rayPt hN θ s₁)‖ := by rw [hsplit]
    _ ≤ ‖Work.EL.rayPt hN θ s₂ - Work.EL.rayPt hN θ t‖
          + ‖Work.EL.rayPt hN θ t - Work.EL.rayPt hN θ s₁‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h2 hb
    _ = ε := by ring

end Work.LandLeaves
