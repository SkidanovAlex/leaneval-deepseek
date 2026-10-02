import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.NAKANE.GreenJoint
import Submission.Work.Escape.log_half_le_green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open Classical Filter

namespace Work.SeedDyn

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **D10 (properness of the critical Böttcher coordinate).**

For `c ∈ M*` the canonical critical Böttcher coordinate `φ = varphiCrit c` is proper on its
domain when tested against compacta that avoid the closed unit disc: for every compact
`K ⊆ {1 < ‖w‖}` the set `esc c ∩ φ ⁻¹' K` is compact.

Indeed, by `norm_varphiCrit_esc` we have `‖φ z‖ = exp (G_c z)` on the escaping set `esc c`, so

* (closedness) `esc c ∩ φ ⁻¹' K = {z | log (1+δ) ≤ G_c z} ∩ φ ⁻¹' K` for `δ > 0` chosen with
  `1 + δ ≤ ‖w‖` on `K`, and the right hand side is closed because `G_c` is continuous
  (`Work.NAKANE.continuous_greenFun`), `K` is closed and `φ` is continuous on the *closed* set
  `{log (1+δ) ≤ G_c z}` (which lies in the critical domain, where `φ` is analytic);
* (boundedness) on `esc c ∩ φ ⁻¹' K` we have `G_c z ≤ log M` for a bound `M` of `K`, and
  `Work.Escape.log_half_le_green` gives `log (‖z‖ / 2) ≤ G_c z` as soon as
  `max 2 ‖c‖ < ‖z‖`, hence `‖z‖ ≤ 2M` there.

Heine–Borel (`Metric.isCompact_iff_isClosed_bounded`) finishes. -/
theorem isCompact_varphiCrit_preimage {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    {K : Set ℂ} (hK : IsCompact K) (hK1 : ∀ w ∈ K, 1 < ‖w‖) :
    IsCompact (Work.SeedDyn.esc c ∩ Work.Bottcher.varphiCrit c ⁻¹' K) := by
  -- a positive gap between `1` and the moduli of the points of `K`
  obtain ⟨a', ha'1, ha'K⟩ :=
    hK.exists_forall_le' continuous_norm.continuousOn (a := (1 : ℝ))
      (fun b hb => hK1 b hb)
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set M : ℝ := max r 1 with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  have hKle : ∀ w ∈ K, ‖w‖ ≤ M := by
    intro w hw
    have h := Metric.mem_closedBall.mp (hr hw)
    rw [dist_zero_right] at h
    exact le_trans h (le_max_left r 1)
  -- the escaping set meets `φ ⁻¹' K` exactly where `G_c ≥ log (1 + (a' - 1))`
  have hset : Work.SeedDyn.esc c ∩ Work.Bottcher.varphiCrit c ⁻¹' K
      = {z : ℂ | Real.log (1 + (a' - 1)) ≤ Work.ParamRays.greenFun c z}
        ∩ Work.Bottcher.varphiCrit c ⁻¹' K := by
    ext z
    constructor
    · rintro ⟨hzesc, hzK⟩
      refine ⟨?_, hzK⟩
      have h1 : 1 + (a' - 1) ≤ ‖Work.Bottcher.varphiCrit c z‖ := by
        have := ha'K _ hzK
        linarith
      have h2 : ‖Work.Bottcher.varphiCrit c z‖
          = Real.exp (Work.ParamRays.greenFun c z) :=
        Work.SeedDyn.norm_varphiCrit_esc hc hzesc
      rw [h2] at h1
      calc Real.log (1 + (a' - 1))
          ≤ Real.log (Real.exp (Work.ParamRays.greenFun c z)) :=
            Real.log_le_log (by linarith) h1
        _ = Work.ParamRays.greenFun c z := Real.log_exp _
    · rintro ⟨hlog, hzK⟩
      have hlt : 1 < 1 + (a' - 1) := by linarith
      have hpos : 0 < Work.ParamRays.greenFun c z :=
        lt_of_lt_of_le (Real.log_pos hlt) hlog
      exact ⟨Work.SeedDyn.mem_esc.mpr
        ((Work.ParamRays.greenFun_pos_iff_escaping c z).mp hpos), hzK⟩
  rw [hset]
  have hgreen : Continuous (fun z : ℂ => Work.ParamRays.greenFun c z) := by
    have h1 : Continuous (fun p : ℂ × ℂ => Work.ParamRays.greenFun p.1 p.2) :=
      Work.NAKANE.continuous_greenFun
    have h2 : Continuous (fun z : ℂ => (c, z)) := continuous_const.prodMk continuous_id
    exact (h1.comp h2).congr (fun z => by simp)
  have hAclosed : IsClosed {z : ℂ | Real.log (1 + (a' - 1)) ≤ Work.ParamRays.greenFun c z} :=
    isClosed_le continuous_const hgreen
  have hAcrit : {z : ℂ | Real.log (1 + (a' - 1)) ≤ Work.ParamRays.greenFun c z}
      ⊆ Work.ParamRays.critDomain c := by
    intro z hz
    rw [Work.SeedDyn.critDomain_eq_escapingSet hc]
    exact (Work.ParamRays.greenFun_pos_iff_escaping c z).mp
      (lt_of_lt_of_le (Real.log_pos (by linarith : (1:ℝ) < 1 + (a' - 1))) hz)
  have hcontA : ContinuousOn (Work.Bottcher.varphiCrit c)
      {z : ℂ | Real.log (1 + (a' - 1)) ≤ Work.ParamRays.greenFun c z} :=
    (Work.Bottcher.varphiCrit_continuousOn c).mono hAcrit
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · -- closedness
    exact ContinuousOn.preimage_isClosed_of_isClosed hcontA hAclosed hK.isClosed
  · -- boundedness
    refine (Metric.isBounded_closedBall (x := (0 : ℂ))
      (r := max (2 * M) (max 2 ‖c‖))).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    obtain ⟨hlog, hzK⟩ := hz
    have hlt : 1 < 1 + (a' - 1) := by linarith
    have hzesc : z ∈ Work.SeedDyn.esc c :=
      Work.SeedDyn.mem_esc.mpr ((Work.ParamRays.greenFun_pos_iff_escaping c z).mp
        (lt_of_lt_of_le (Real.log_pos hlt) hlog))
    have hgreenle : Work.ParamRays.greenFun c z ≤ Real.log M := by
      have h2 : ‖Work.Bottcher.varphiCrit c z‖
          = Real.exp (Work.ParamRays.greenFun c z) :=
        Work.SeedDyn.norm_varphiCrit_esc hc hzesc
      have hM' : Real.exp (Work.ParamRays.greenFun c z) ≤ M := by
        rw [← h2]; exact hKle _ hzK
      calc Work.ParamRays.greenFun c z
          = Real.log (Real.exp (Work.ParamRays.greenFun c z)) := (Real.log_exp _).symm
        _ ≤ Real.log M := Real.log_le_log (Real.exp_pos _) hM'
    by_cases hfar : max 2 ‖c‖ < ‖z‖
    · have hloghalf : Real.log (‖z‖ / 2) ≤ Work.ParamRays.greenFun c z := by
        have h := Work.Escape.log_half_le_green (Tantibar c) 2 ‖c‖
          (Work.Escape.monicGrowth_Tantibar c) le_rfl (z := z) hfar
        rwa [← Work.NAKANE.greenFun_eq_green c z] at h
      have hzn : 0 < ‖z‖ / 2 := by
        have h2 : (2 : ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) hfar
        linarith
      have hle : ‖z‖ / 2 ≤ M :=
        (Real.log_le_log_iff hzn hMpos).mp (le_trans hloghalf hgreenle)
      have : ‖z‖ ≤ 2 * M := by linarith
      exact le_trans this (le_max_left _ _)
    · push Not at hfar
      exact le_trans hfar (le_max_right _ _)

end Work.SeedDyn
