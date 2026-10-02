import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.ccBet_v2_defs
import Submission.Work.LandLeaves.gmLocalOrder
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.InArcHard.BasicClean
import Submission.Work.LandLeaves.pairSide_nesting_farArc
import Submission.Work.LandLeaves.rayPt_iterate_angDouble
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.HardCase.Sector
import Submission.Work.LandLeaves.InArcHard.localCore
import Submission.Work.LandLeaves.InArcHard.extAngleLift
import Submission.Work.FSeed.Rays.landsAt_periodic
import Submission.Work.ELTop.All
import Submission.Work.ELTop.paramRay_subset_pairSide

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves.InArcHard

open Classical
open scoped Topology

noncomputable section

/-- **Side transfer across the second return map.**

Let `y` be a repelling periodic point of odd period `k` of the tricorn `T_c = Tantibar c`, let
`φ` be a Böttcher coordinate, and let `u`, `v` be two angles whose dynamic rays accumulate at
the single point `y` and which are incongruent modulo `1` (so that the co-landing pair
`P_uv` has a well-defined far side `pairSide P_uv`, the component of the complement of
`P_uv.curve` containing the ray of the mid angle of the arc `(u,v)`).

Then, near `y`, the second return map `τ = (T_c)^{2k}` carries the far side of `P_uv` into the
far side of the pair of the two image angles `σ u`, `σ v` (where `σ = (angDouble)^[2k]`):

`∃ ε > 0, τ '' (pairSide P_uv ∩ B(y,ε)) ⊆ pairSide P_{σu,σv}`.

This is the sign-free "chirality" content of Goldberg–Milnor II Lemma 2.2: it never asks which of
the two sectors cut out by the two rays at `y` is the far one — only that `τ`, being a
holomorphic local biholomorphism at `y` with `τ y = y` and `τ' y ≠ 0` (orientation preserving),
carries the *far* sector to the *far* sector. -/
theorem sectorTransfer {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {u v : ℝ} (hu : Work.Landing.rayAccum c φ u = {y}) (hv : Work.Landing.rayAccum c φ v = {y})
    (hnd : Int.fract (v - u) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ,
      z ∈ Work.EL.pairSide (Work.LandLeaves.mkPair (Work.LandLeaves.dynBNakane hφ)
            (Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ hu)
            (Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ hv)) →
      ‖z - y‖ < ε →
      (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z ∈
        Work.EL.pairSide (Work.LandLeaves.mkPair (Work.LandLeaves.dynBNakane hφ)
          (Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ
            (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hu))
          (Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ
            (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hv))) := by
  classical
  have hk : 0 < k := hrep.1.1
  let hN : Work.EL.DynB c φ := Work.LandLeaves.dynBNakane hφ
  -- ## The landing data of the shifted angles `fract u`, `fract v`
  have hacc_u' : Work.Landing.rayAccum c φ (Int.fract u) = {y} := by
    rw [← Work.FSeed.rayAccum_add_int c φ (Int.fract u) ⌊u⌋, Int.fract_add_floor u]
    exact hu
  have hacc_v' : Work.Landing.rayAccum c φ (Int.fract v) = {y} := by
    rw [← Work.FSeed.rayAccum_add_int c φ (Int.fract v) ⌊v⌋, Int.fract_add_floor v]
    exact hv
  have hL_u : Work.EL.LandsN hN u y :=
    Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ hu
  have hL_v : Work.EL.LandsN hN v y :=
    Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ hv
  have hL_u' : Work.EL.LandsN hN (Int.fract u) y :=
    (Work.ELTop.landsN_iff_landsAt hN hφ (Int.fract u) y).mpr
      (Work.LandLeaves.landsAt_of_rayAccum hφ hacc_u')
  have hL_v' : Work.EL.LandsN hN (Int.fract v) y :=
    (Work.ELTop.landsN_iff_landsAt hN hφ (Int.fract v) y).mpr
      (Work.LandLeaves.landsAt_of_rayAccum hφ hacc_v')
  -- ## The image angles and their landing points
  have hL_su : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] u) y :=
    Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ
      (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hu)
  have hL_sv : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] v) y :=
    Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ
      (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hv)
  -- ## The two pairs
  set P : Work.EL.CoPair hN := Work.LandLeaves.mkPair hN hL_u' hL_v' with hPdef
  set P' : Work.EL.CoPair hN := Work.LandLeaves.mkPair hN hL_su hL_sv with hP'def
  have hPa : P.a = Int.fract u := by rw [hPdef]; rfl
  have hPb : P.b = Int.fract v := by rw [hPdef]; rfl
  have hPa' : P'.a = (Work.Landing.angDouble)^[2 * k] u := by rw [hP'def]; rfl
  have hPb' : P'.b = (Work.Landing.angDouble)^[2 * k] v := by rw [hP'def]; rfl
  have hPy : P.y = y := by rw [hPdef]; rfl
  have hP'y : P'.y = y := by rw [hP'def]; rfl
  -- ## The far side of `P` is the far side of the given pair `(u,v)`
  have hside : Work.EL.pairSide P
      = Work.EL.pairSide (Work.LandLeaves.mkPair hN hL_u hL_v) := by
    rw [hPdef, Work.EL.pairSide_eq, Work.EL.pairSide_eq]
    show Work.EL.RawPair.side hN (⟨Int.fract u, Int.fract v, y⟩ : Work.EL.RawPair)
      = Work.EL.RawPair.side hN (⟨u, v, y⟩ : Work.EL.RawPair)
    have h1 : (⟨u, v, y⟩ : Work.EL.RawPair)
        = (⟨Int.fract u + (⌊u⌋ : ℝ), Int.fract v + (⌊v⌋ : ℝ), y⟩ : Work.EL.RawPair) := by
      rw [Int.fract_add_floor u, Int.fract_add_floor v]
    rw [h1]
    exact (Work.LandLeaves.InArcHard.Core.rawSide_add_int_aux hN (Int.fract u) (Int.fract v) y
      ⌊u⌋ ⌊v⌋).symm
  -- ## Non-degeneracy
  have hndP : Work.EL.arcLen P.a P.b ≠ 0 := by
    rw [hPa, hPb, Work.EL.arcLen, Work.LandLeaves.InArcHard.Core.fract_fract_sub_eq u v]
    exact hnd
  have hndP' : Work.EL.arcLen P'.a P'.b ≠ 0 := by
    rw [hPa', hPb']
    exact Work.LandLeaves.InArcHard.Core.fract_sub_angDouble_ne_zero hφ hrep hu hv hnd
  have hS : Work.EL.PairSides hN P :=
    Work.ELTop.pairSides hN Work.TopJordan.jordanForm P hndP
  have hS' : Work.EL.PairSides hN P' :=
    Work.ELTop.pairSides hN Work.TopJordan.jordanForm P' hndP'
  have hPab : P.a ≠ P.b := by
    rw [hPa, hPb]
    intro h
    refine hnd ?_
    rw [← Work.LandLeaves.InArcHard.Core.fract_fract_sub_eq u v, h]
    simp [Work.EL.arcLen]
  -- ## The witnesses for the `4^k`-congruence
  have hwit_u : ∃ m : ℤ, P'.a = (4 : ℝ) ^ k * P.a + m := by
    rw [hPa', hPa]
    refine ⟨(4 : ℤ) ^ k * ⌊u⌋ - ⌊(4 : ℝ) ^ k * u⌋, ?_⟩
    rw [Work.LandLeaves.angDouble_iterate_two_mul hk u]
    push_cast
    exact Work.LandLeaves.InArcHard.Core.fract_mul_eq ((4 : ℝ) ^ k) u
  have hwit_v : ∃ m : ℤ, P'.b = (4 : ℝ) ^ k * P.b + m := by
    rw [hPb', hPb]
    refine ⟨(4 : ℤ) ^ k * ⌊v⌋ - ⌊(4 : ℝ) ^ k * v⌋, ?_⟩
    rw [Work.LandLeaves.angDouble_iterate_two_mul hk v]
    push_cast
    exact Work.LandLeaves.InArcHard.Core.fract_mul_eq ((4 : ℝ) ^ k) v
  -- ## The local preimage identity at `y`
  have hPTa : ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε →
      Work.LandLeaves.InArcHard.Core.tauC c k z ∈ Work.EL.paramRay hN P'.a →
      z ∈ Work.EL.paramRay hN P.a := by
    obtain ⟨ε, hε, h⟩ :=
      Work.LandLeaves.InArcHard.Core.tauC_preimage_tail_aux hN hφ hrep hacc_u'
    refine ⟨ε, hε, fun z hz hmem => h z hz P'.a ?_ hmem⟩
    rw [← hPa]
    exact hwit_u
  have hPTb : ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε →
      Work.LandLeaves.InArcHard.Core.tauC c k z ∈ Work.EL.paramRay hN P'.b →
      z ∈ Work.EL.paramRay hN P.b := by
    obtain ⟨ε, hε, h⟩ :=
      Work.LandLeaves.InArcHard.Core.tauC_preimage_tail_aux hN hφ hrep hacc_v'
    refine ⟨ε, hε, fun z hz hmem => h z hz P'.b ?_ hmem⟩
    rw [← hPb]
    exact hwit_v
  -- ## The local angle transfer
  have hPaIco : P.a ∈ Set.Ico (0 : ℝ) 1 := by
    rw [hPa]
    exact ⟨Int.fract_nonneg u, Int.fract_lt_one u⟩
  have hPbIco : P.b ∈ Set.Ico (0 : ℝ) 1 := by
    rw [hPb]
    exact ⟨Int.fract_nonneg v, Int.fract_lt_one v⟩
  have hLA : ∀ p : ℂ, p ∈ Work.EL.paramRay hN P.a ∪ Work.EL.paramRay hN P.b → ∃ δ > 0,
      ∀ z : ℂ, z ∈ Metric.ball p δ → z ∉ Work.EL.pairCurve P →
        Work.LandLeaves.InArcHard.Core.tauC c k z ∉ Work.EL.pairCurve P' ∧
        (z ∈ Work.EL.pairSide P ↔
          Work.LandLeaves.InArcHard.Core.tauC c k z ∈ Work.EL.pairSide P') :=
    fun p hp =>
      Work.LandLeaves.InArcHard.Core.localAngleGen_lift hN hφ hk P P' hS hS'
        hPaIco hPbIco hPab hwit_u hwit_v hndP' hp
  -- ## The clopen argument
  obtain ⟨ε, hεpos, hε⟩ :=
    Work.LandLeaves.InArcHard.Core.cop_sides_gen hN hk hrep P P' hPy hP'y hS hS' hndP' hPTa hPTb hLA
  refine ⟨ε, hεpos, fun z hz hzb => ?_⟩
  have hzside : z ∈ Work.EL.pairSide P := by
    rw [hside]
    exact hz
  have hzmem : z ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hzb
  have hznot : z ∉ Work.EL.pairCurve P := by
    intro hc
    exact (connectedComponentIn_subset (Work.EL.pairCurve P)ᶜ
      (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2) hzside) hc
  have hres : Work.LandLeaves.InArcHard.Core.tauC c k z ∈ Work.EL.pairSide P' :=
    ((hε z hzmem hznot).mp) hzside
  rw [Work.LandLeaves.InArcHard.Core.tauC_apply] at hres
  exact hres

end

end Work.LandLeaves.InArcHard
