import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.ExtGen.pairIso_of_linearEquiv
import Submission.Work.KT.bott_aux

/-!
# `Work.KT.SG` — transport of `K̃(Kpair ·) = 0` along linear isomorphisms

A linear equivalence `e : V ≃ₗ[ℝ] V'` of finite-dimensional real normed spaces induces the algebra
isomorphism `ExtGen.pairIsoEV e : Kpair V ≃ₐ[ℂ] Kpair V'` (`Submission/Work/KT/ExtGen/
pairIso_of_linearEquiv.lean`), and `ExtGen.pairIsoEV_aug` records that it carries the augmentation
at `y' ∈ bdry V'` to the augmentation at `psiBall e y' ∈ bdry V`.  Consequently the vanishing of
the reduced group `K̃(Kpair ·) = ker (augPair · y0)` transfers across `e`.
-/

namespace Work.KT
namespace SG

open Matrix

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

/-- The boundary of the unit sphere of a nontrivial finite-dimensional real normed space is
nonempty. -/
theorem bdry_nonempty {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] :
    ∃ y : Ball E, y ∈ bdry E := by
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr zero_le_one
  have hv1 : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
  exact ⟨⟨v, by simp [Metric.mem_closedBall, dist_zero_right, hv1]⟩, hv1⟩

/-- `K̃(Kpair ·) = 0` transfers along a linear isomorphism: if the augmentation is injective on
`K₀(Kpair V)` then it is injective on `K₀(Kpair V')` for any `V ≃ₗ[ℝ] V'`. -/
theorem kpair_vanishing_transfer {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    (e : V ≃ₗ[ℝ] V') (y' : Ball V') (hy' : y' ∈ bdry V')
    (h : ∀ (y : Ball V), y ∈ bdry V → ∀ z : K0 (Kpair V), K0.mapA (augPair V y) z = 0 → z = 0) :
    ∀ z : K0 (Kpair V'), K0.mapA (augPair V' y') z = 0 → z = 0 := by
  intro z hz
  set w : K0 (Kpair V) := K0.mapA (ExtGen.pairIsoEV e).symm.toAlgHom z with hwdef
  have hΦw : K0.mapA (ExtGen.pairIsoEV e).toAlgHom w = z := by
    rw [hwdef]
    exact ba_mapA_apply_symm (A := Kpair V) (B := Kpair V') (ExtGen.pairIsoEV e) z
  have h2 : K0.mapA (augPair V' y') z
      = K0.mapA (augPair V (ExtGen.psiBall e y')) w := by
    rw [← hΦw]
    rw [ba_mapA_comp_apply (A := Kpair V) (B := Kpair V') (C := ℂ)
      (ExtGen.pairIsoEV e).toAlgHom (augPair V' y') w]
    rw [ExtGen.pairIsoEV_aug e y']
  have hw : w = 0 :=
    h (ExtGen.psiBall e y') (ExtGen.psiBall_mem_bdry e hy') w (by rw [← h2]; exact hz)
  rw [← hΦw, hw, map_zero]

end

end SG

end Work.KT
