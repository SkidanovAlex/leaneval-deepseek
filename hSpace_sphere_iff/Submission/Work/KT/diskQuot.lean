import Mathlib
import Submission.Work.KT.DiskAux
import Submission.Work.KT.diskQuotSurj

/-!
# `D^d / S^{d-1} ≅ S^d`

The map `qc d : C(Ball (Euc d), Sph (ModelSphere d))` of `Submission.Work.KT.DiskAux` collapses the
boundary sphere `S^{d-1}` of the closed disc `D^d` to the north pole of `S^d` and is injective off
the boundary. This file proves that it is a quotient map onto `S^d` and that its fibres are exactly
the boundary, i.e. the statement `Work.KT.diskQuot`.
-/

namespace Work.KT

noncomputable section

/-- The fibres of `qc d` are the singletons of the interior together with the boundary. -/
lemma qc_eq_iff (d : ℕ) (x x' : Ball (Euc d)) :
    qc d x = qc d x' ↔ x = x' ∨ (x ∈ bdry (Euc d) ∧ x' ∈ bdry (Euc d)) := by
  rw [Subtype.ext_iff, qc_apply, qc_apply, qMapDisk_eq_iff_disk]
  constructor
  · rintro ⟨h1, h2⟩
    have hxle : ‖(x : Euc d)‖ ≤ 1 := norm_le_one_of_mem_ball d x
    have hxle' : ‖(x' : Euc d)‖ ≤ 1 := norm_le_one_of_mem_ball d x'
    have hxnn : (0 : ℝ) ≤ ‖(x : Euc d)‖ := norm_nonneg _
    have hxnn' : (0 : ℝ) ≤ ‖(x' : Euc d)‖ := norm_nonneg _
    have hmem : Real.pi * ‖(x : Euc d)‖ ∈ Set.Icc 0 Real.pi :=
      ⟨mul_nonneg Real.pi_pos.le hxnn, mul_le_of_le_one_right Real.pi_pos.le hxle⟩
    have hmem' : Real.pi * ‖(x' : Euc d)‖ ∈ Set.Icc 0 Real.pi :=
      ⟨mul_nonneg Real.pi_pos.le hxnn', mul_le_of_le_one_right Real.pi_pos.le hxle'⟩
    have hpeq : Real.pi * ‖(x : Euc d)‖ = Real.pi * ‖(x' : Euc d)‖ :=
      Real.strictAntiOn_cos.injOn hmem hmem' h2
    have hreq : ‖(x : Euc d)‖ = ‖(x' : Euc d)‖ := mul_left_cancel₀ Real.pi_ne_zero hpeq
    by_cases hrx : ‖(x : Euc d)‖ = 1
    · right
      refine ⟨show x ∈ bdry (Euc d) from hrx, ?_⟩
      show ‖(x' : Euc d)‖ = 1
      rw [← hreq]
      exact hrx
    · left
      have hlt : ‖(x : Euc d)‖ < 1 := lt_of_le_of_ne hxle hrx
      have h1' : sfun ‖(x : Euc d)‖ • (x : Euc d) = sfun ‖(x : Euc d)‖ • (x' : Euc d) := by
        rw [← hreq] at h1
        exact h1
      have hsub : sfun ‖(x : Euc d)‖ • ((x : Euc d) - (x' : Euc d)) = 0 := by
        rw [smul_sub, h1', sub_self]
      have hvsub : (x : Euc d) - (x' : Euc d) = 0 := by
        rcases smul_eq_zero.mp hsub with hz | hz
        · exact absurd hz (sfun_ne_zero hxnn hlt)
        · exact hz
      exact Subtype.ext (sub_eq_zero.mp hvsub)
  · rintro (rfl | ⟨hxb, hx'b⟩)
    · exact ⟨rfl, rfl⟩
    · exact (qMapDisk_eq_iff_disk d x x').mp
        (by rw [qMapDisk_bdry_val d x (show ‖(x : Euc d)‖ = 1 from hxb),
              qMapDisk_bdry_val d x' (show ‖(x' : Euc d)‖ = 1 from hx'b)])

/-- The quotient map `qc d` exhibits `S^d` as the quotient of the disc `D^d` by its boundary. -/
theorem diskQuot (d : ℕ) (hd : 1 ≤ d) :
    ∃ q : C(Ball (Euc d), Sph (ModelSphere d)),
      Topology.IsQuotientMap q ∧
      (∀ x ∈ bdry (Euc d), q x = sphKT_northPole d) ∧
      ∀ x x' : Ball (Euc d), q x = q x' ↔
        x = x' ∨ (x ∈ bdry (Euc d) ∧ x' ∈ bdry (Euc d)) := by
  exact ⟨qc d, Topology.IsQuotientMap.of_surjective_continuous (diskQuotSurj d hd) (qc d).continuous,
    fun x hx => qc_bdry d x hx, fun x x' => qc_eq_iff d x x'⟩

end

end Work.KT
