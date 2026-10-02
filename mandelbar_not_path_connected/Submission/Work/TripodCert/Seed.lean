/-
# TripodCert — the seed certificate: TRI at the certified parameter box

Area `Submission/Work/TripodCert/`.  This is the assembly of the certificate: at every parameter
`c` of the parameter box `Xb` (the certified root point of the period-5 component) and every
`c ∈ M*`, the landing point of the `22/63`-ray is fixed by `Tsq c` (TRI), and consequently the
three tripod rays land at one point (`tripod_of_fixed`).
-/
import Mathlib
import Submission.Work.TripodCert.Basic
import Submission.Work.TripodCert.Chain
import Submission.Work.TripodCert.Unique
import Submission.Work.TripodCert.Transfer
import Submission.Work.LandLeaves.periodicRaysLand
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.SeedDyn.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.TripodCert

open Work.SeedCertRay
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The landing point of a ray lies in its accumulation set. -/
theorem mem_rayAccum_of_landsN {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) : y ∈ Work.Landing.rayAccum c φ θ := by
  rw [Work.ELTop.rayAccum_eq_closure hN θ]
  intro ρ hρ
  have hmem : Set.Ioc (1 : ℝ) ρ ∈ nhdsWithin 1 (Set.Ioi 1) := by
    refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hρ))) ?_
    intro t ht
    exact ⟨ht.1, le_of_lt ht.2⟩
  refine mem_closure_of_tendsto h (Filter.mem_of_superset hmem ?_)
  intro t ht
  rw [Work.ELTop.rayPiece_eq_image hN hρ]
  exact ⟨t, ht, rfl⟩

/-- `(Tsq c)^[3]` commutes with `Tsq c` (both are iterates). -/
theorem tsq_iterate_three_comm (c y : ℂ) :
    (Work.Landing.Tsq c)^[3] ((Work.Landing.Tsq c) y)
      = (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[3] y) := by
  have h4 : (Work.Landing.Tsq c)^[4] y
      = (Work.Landing.Tsq c)^[3] ((Work.Landing.Tsq c) y) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
  have h5 : (Work.Landing.Tsq c)^[4] y
      = (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[3] y) := by
    rw [show (4 : ℕ) = 1 + 3 from rfl, Function.iterate_add_apply, Function.iterate_one]
  rw [← h4, h5]

/-- **(T3) TRI at the certified box.**  For `c` in the parameter box `Xb` of the seed
certificate and in the mandelbar, the landing point of the `22/63`-ray is fixed by
`Tsq c = (T_c)^2`. -/
theorem seed_tri {c : ℂ} (hc : c ∈ Mandelbar) (hcX : Xb.mem c) :
    ∃ y : ℂ, Work.Landing.landsAt c (22 / 63) y ∧ Work.Landing.Tsq c y = y := by
  obtain ⟨y, hy⟩ := Work.LandLeaves.periodicRaysLand c hc (22 / 63) isPeriodicAngle_angA
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    (Work.SeedDyn.isDynBottcherHomeo hc).1
  have hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c) := Work.SeedDyn.dynB hc
  have hc2 : ‖c‖ ≤ 2 := by
    have h := hUCm hcX
    norm_num [UCmq] at h ⊢
    linarith
  have hL0 : Work.EL.LandsN hN (theta 0) y :=
    (Work.ELTop.landsN_iff_landsAt hN hφ (22 / 63) y).mpr hy
  have hchain := chainT hN hφ hc hc2 hcX
  have hyCT : y ∈ CT KT 0 := landsN_mem_CT hN hchain hL0
  have hyD : y ∈ Metric.closedBall uZ0 uRUr := CT_KT_zero_sub hyCT
  have hL2 : Work.EL.LandsN hN (theta 2) (Work.Landing.Tsq c y) := by
    have h := Work.ELNest.landsN_iterate hN hφ 2 hL0
    have e1 : (Work.EL.T^[2]) (theta 0) = theta 2 := rfl
    have e2 : (Tantibar c)^[2] y = Work.Landing.Tsq c y := by
      rw [Work.ELNest.Tsq_eq_comp c]
    rw [e1, e2] at h
    exact h
  have hy2CT : Work.Landing.Tsq c y ∈ CT KT 2 := landsN_mem_CT hN hchain hL2
  have hy2D : Work.Landing.Tsq c y ∈ Metric.closedBall uZ0 uRUr := CT_KT_two_sub hy2CT
  have hyacc : y ∈ Work.Landing.rayAccum c (Work.ParamRays.dynPhiOf c) (22 / 63) :=
    mem_rayAccum_of_landsN hN hL0
  have hy6 : (Tantibar c)^[6] y = y :=
    Work.LandLeaves.rayAccum_subset_fixp c hc (by norm_num) periodicAngle_angA y hyacc
  have hfix : (Work.Landing.Tsq c)^[3] y = y := by
    rw [Tsq_iterate_three]
    exact hy6
  have hfix2 : (Work.Landing.Tsq c)^[3] (Work.Landing.Tsq c y) = Work.Landing.Tsq c y := by
    rw [tsq_iterate_three_comm, hfix]
  have hyy : Work.Landing.Tsq c y = y := tsq_three_fixp_unique hcX hy2D hyD hfix2 hfix
  exact ⟨y, hy, hyy⟩

/-- **The tripod at the seed parameter.**  For `c ∈ M*` in the parameter box, the three tripod
rays `22/63`, `25/63`, `37/63` land at one point (the `b₂`-tripod of `Work.EL`). -/
noncomputable def seed_tripod {c : ℂ} (hc : c ∈ Mandelbar) (hcX : Xb.mem c) :
    Work.EL.Tripod (Work.SeedDyn.dynB hc) :=
  tripod_of_fixed (Work.SeedDyn.dynB hc) ((Work.SeedDyn.isDynBottcherHomeo hc).1)
    ((Work.ELTop.landsN_iff_landsAt (Work.SeedDyn.dynB hc)
        ((Work.SeedDyn.isDynBottcherHomeo hc).1) (22 / 63)
        (Classical.choose (seed_tri hc hcX))).mpr
      (Classical.choose_spec (seed_tri hc hcX)).1)
    (Classical.choose_spec (seed_tri hc hcX)).2

/-- **The tripod at the final parameter.**  From the seed certificate (`c ∈ Xb ∩ M*`) and the FQC
deformation datum `(θ, hb, hb₂, hesc)` — the same four objects the `hzero` call site uses — the
three tripod rays of `T_{c₂}` land at one point.  No conjugacy identity is needed: the tripod
statement is transported ray by ray (`Work.FQC.transfer_rays`). -/
noncomputable def tripod_of_seed_transfer {c c₂ : ℂ} {φ ψ : ℂ → ℂ} (θ : ℂ ≃ₜ ℂ)
    (hb : Work.ParamRays.IsDynBottcher c φ)
    (hb₂ : Work.ParamRays.IsDynBottcher c₂ (φ ∘ (θ.symm : ℂ → ℂ)))
    (hesc : ∀ z : ℂ, Work.ParamRays.Escaping c₂ (θ z) ↔ Work.ParamRays.Escaping c z)
    (hN₂ : Work.EL.DynB c₂ ψ) (hψ : Work.ParamRays.IsDynBottcher c₂ ψ)
    (hc : c ∈ Mandelbar) (hcX : Xb.mem c) : Work.EL.Tripod hN₂ :=
  tripod_of_transfer θ hb hb₂ hesc hN₂ hψ (y := (seed_tripod hc hcX).y) (fun ϑ hϑ => by
    rcases mem_tripodAngles.mp hϑ with h | h | h
    · rw [h]
      exact (Work.ELTop.landsN_iff_landsAt (Work.SeedDyn.dynB hc)
        ((Work.SeedDyn.isDynBottcherHomeo hc).1) (22 / 63) _).mp (seed_tripod hc hcX).lands₁
    · rw [h]
      exact (Work.ELTop.landsN_iff_landsAt (Work.SeedDyn.dynB hc)
        ((Work.SeedDyn.isDynBottcherHomeo hc).1) (25 / 63) _).mp (seed_tripod hc hcX).lands₂
    · rw [h]
      exact (Work.ELTop.landsN_iff_landsAt (Work.SeedDyn.dynB hc)
        ((Work.SeedDyn.isDynBottcherHomeo hc).1) (37 / 63) _).mp (seed_tripod hc hcX).lands₃)

end Work.TripodCert
