import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELTop.polyRegion_eq_inter_pairSideNear
import Submission.Work.ELTop.polyCurve_isJordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology
noncomputable section
namespace Work.ELAssembly
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem Dmem_of {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d) {L : ℝ} (hL : 1 < L) (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [N.Za n, N.Zb n, N.Zc n]) (hndA : ∀ n : ℕ, Work.EL.arcLen (N.Za n).a (N.Za n).b ≠ 0) (hndB : ∀ n : ℕ, Work.EL.arcLen (N.Zb n).a (N.Zb n).b ≠ 0) (hndC : ∀ n : ℕ, Work.EL.arcLen (N.Zc n).a (N.Zc n).b ≠ 0) (n : ℕ) : Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n) = Work.EL.pairSideNear (N.Za n) ∩ Work.EL.pairSideNear (N.Zb n) ∩ Work.EL.pairSideNear (N.Zc n) ∩ {z : ℂ | Work.EL.pot d.hN z < Real.log (Work.ELNest.Dlev L n)} := by
  have hR : 1 < Work.ELNest.Dlev L n := by
    rw [Work.ELNest.Dlev]; exact Real.one_lt_rpow hL (by positivity)
  have hnd : ∀ P ∈ [N.Za n, N.Zb n, N.Zc n], Work.EL.arcLen P.a P.b ≠ 0 := by
    intro P hP
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl
    · exact hndA n
    · exact hndB n
    · exact hndC n
  have hC := Work.ELTop.polyCurve_isJordan d.hN [N.Za n, N.Zb n, N.Zc n] (hadm n) hR
  rw [Work.ELTop.polyRegion_eq_inter_pairSideNear d.hN Work.TopJordan.jordanForm
    [N.Za n, N.Zb n, N.Zc n] (hadm n) hnd hR hC]
  ext z
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hall, hp⟩
    exact ⟨⟨⟨hall _ (by simp), hall _ (by simp)⟩, hall _ (by simp)⟩, hp⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, hp⟩
    exact ⟨fun P hP => by rcases hP with rfl | rfl | rfl <;> assumption, hp⟩

end Work.ELAssembly
