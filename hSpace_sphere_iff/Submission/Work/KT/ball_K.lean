import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.BallKFrame
import Submission.Work.KT.ballK_dim1
import Submission.Work.KT.ballK_dim2
import Submission.Work.KT.ballK_transfer
import Submission.Work.KT.ballK_step

/-!
# Node `ball_K`: `K̃(D_V/S_V) = K̃(S^d)`

`K̃(D_V/S_V) = K̃(S^d)`, `d = dim V`: infinite cyclic with `ψ^k = k^j` if `d = 2j`, zero if `d`
is odd.

This file assembles the statement from four ingredients (each a separate node, imported at the
end of the development):

* `ballK_transfer` (change of norm and dimension): a linear isomorphism `V ≃ₗ W` of
  finite-dimensional real normed spaces induces an algebra isomorphism `Kpair W ≃ₐ Kpair V`
  carrying the augmentation to the augmentation, so `BallKStmt` is transported along it;
* `ballK_dim1`: `K̃(D¹/S⁰) = 0`, i.e. the augmentation on `K₀(Kpair ℝ)` is injective;
* `ballK_dim2`: the base case on `S²`: `K̃(D²/S¹) = ℤ·H` with `ψ² H = 2 H`, `ψ³ H = 3 H`;
* `ballK_step` (the induction step `d → d+2`): the suspension by `S²` via the external product
  with the Bott class (`bott_susp`, Bott periodicity `fund_product` in the form needed here).

The main induction below is over the dimension: `0` is vacuous, `1` and `2` are the base cases,
and `d ≥ 3` is `V ≅ ℝ^{d-2} × ℝ²` with the step applied to `ℝ^{d-2}`.
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 1600000

/-- The augmentation on `Kpair V` does not depend on the boundary point. -/
lemma augPair_eq {V : Type} [NormedAddCommGroup V] (y0 y0' : Ball V)
    (hy0 : y0 ∈ bdry V) (hy0' : y0' ∈ bdry V) : augPair V y0 = augPair V y0' := by
  ext g
  exact g.2 y0 hy0 y0' hy0'

/-- `BallKStmt` does not depend on the boundary point. -/
lemma ballKStmt_congr_aug {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {y0 y0' : Ball V} (hy0 : y0 ∈ bdry V) (hy0' : y0' ∈ bdry V) (j : ℕ)
    (h : BallKStmt V y0 hy0 j) : BallKStmt V y0' hy0' j := by
  have haug : (K0.mapA (augPair V y0) : K0 (Kpair V) →+ K0 ℂ) =
      K0.mapA (augPair V y0') := by
    rw [augPair_eq y0 y0' hy0 hy0']
  unfold BallKStmt at h ⊢
  rw [← haug]
  exact h

/-- In positive dimension the boundary is nonempty. -/
lemma bdry_nonempty {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] :
    ∃ y : Ball E, y ∈ bdry E := by
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr zero_le_one
  have hv1 : ‖v‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hv
  exact ⟨⟨v, by simp [Metric.mem_closedBall, dist_zero_right, hv1]⟩, hv1⟩

/-- The main theorem of this file, from the four ingredient statements. -/
theorem ball_K_of
    (htrans : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
      (φ : V ≃ₗ[ℝ] W) (y0 : Ball V) (hy0 : y0 ∈ bdry V)
      (y0' : Ball W) (hy0' : y0' ∈ bdry W) (j : ℕ),
      BallKStmt W y0' hy0' j → BallKStmt V y0 hy0 j)
    (hbase1 : ∀ (y0 : Ball ℝ), y0 ∈ bdry ℝ →
      ∀ z : K0 (Kpair ℝ), K0.mapA (augPair ℝ y0) z = 0 → z = 0)
    (hbase2 : ∀ (y0W : Ball (EuclideanSpace ℝ (Fin 2)))
      (hy0W : y0W ∈ bdry (EuclideanSpace ℝ (Fin 2))),
      BallKStmt (EuclideanSpace ℝ (Fin 2)) y0W hy0W 1)
    (hstep : ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
      (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W)
      (y0 : Ball (V × W)) (hy0 : y0 ∈ bdry (V × W))
      (hVd : 1 ≤ Module.finrank ℝ V) (hWd : Module.finrank ℝ W = 2) (j : ℕ),
      BallKStmt V y0V hV j → BallKStmt (V × W) y0 hy0 (j + 1))
    : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      (y0 : Ball V) (hy0 : y0 ∈ bdry V) (j : ℕ), BallKStmt V y0 hy0 j := by
  suffices key : ∀ d, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
      [FiniteDimensional ℝ V], Module.finrank ℝ V = d →
      ∀ (y0 : Ball V) (hy0 : y0 ∈ bdry V) (j : ℕ), BallKStmt V y0 hy0 j by
    intro V _ _ _ y0 hy0 j
    exact key _ V rfl y0 hy0 j
  intro d
  refine @Nat.strong_induction_on (fun d => ∀ (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℝ V] [FiniteDimensional ℝ V], Module.finrank ℝ V = d →
      ∀ (y0 : Ball V) (hy0 : y0 ∈ bdry V) (j : ℕ), BallKStmt V y0 hy0 j) d ?_
  intro d ih V _ _ _ hd y0 hy0 j
  by_cases hsmall : d < 3
  · interval_cases d
    · -- dimension `0`: the boundary is empty
      haveI : Subsingleton V := (Module.finrank_eq_zero_iff_of_free ℝ V).mp hd
      exact absurd (by
        have h1 : ‖(y0 : V)‖ = 1 := hy0
        rw [Subsingleton.elim (y0 : V) 0, norm_zero] at h1
        exact h1.symm) one_ne_zero
    · -- dimension `1`: `K̃(S¹) = 0`
      obtain ⟨y0ℝ, hy0ℝ⟩ := bdry_nonempty (E := ℝ)
      have hbase : BallKStmt ℝ y0ℝ hy0ℝ j :=
        ⟨fun hh => by rw [Module.finrank_self] at hh; omega,
          fun _ z hz => hbase1 y0ℝ hy0ℝ z hz⟩
      exact htrans V ℝ (LinearEquiv.ofFinrankEq V ℝ (by
        rw [hd, Module.finrank_self])) y0 hy0 y0ℝ hy0ℝ j hbase
    · -- dimension `2`: the Bott class
      obtain ⟨y0W, hy0W⟩ := bdry_nonempty (E := EuclideanSpace ℝ (Fin 2))
      have hfr2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by
        rw [finrank_euclideanSpace_fin]
      refine htrans V (EuclideanSpace ℝ (Fin 2)) (LinearEquiv.ofFinrankEq V _
        (by rw [hfr2]; exact hd)) y0 hy0 y0W hy0W j ?_
      refine ⟨fun hh => ?_, fun hh => by rw [hfr2] at hh; omega⟩
      rw [hfr2] at hh
      have hj : j = 1 := by omega
      subst hj
      exact (hbase2 y0W hy0W).1 (by rw [hfr2])
  · -- dimension `≥ 3`: the suspension step
    have hd3 : 3 ≤ d := by omega
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      exact ⟨fun hh => absurd hh (by omega), fun hh => absurd hh (by omega)⟩
    · haveI : Nonempty (Fin (d - 2)) := ⟨⟨0, by omega⟩⟩
      obtain ⟨y0V', hy0V'⟩ := bdry_nonempty (E := EuclideanSpace ℝ (Fin (d - 2)))
      obtain ⟨y0W', hy0W'⟩ := bdry_nonempty (E := EuclideanSpace ℝ (Fin 2))
      obtain ⟨y0c, hy0c⟩ := bdry_nonempty (E := EuclideanSpace ℝ (Fin (d - 2))
        × EuclideanSpace ℝ (Fin 2))
      have hfrW : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by
        rw [finrank_euclideanSpace_fin]
      have hfrV' : Module.finrank ℝ (EuclideanSpace ℝ (Fin (d - 2))) = d - 2 := by
        rw [finrank_euclideanSpace_fin]
      have ihV' : BallKStmt (EuclideanSpace ℝ (Fin (d - 2))) y0V' hy0V' (j - 1) :=
        ih (d - 2) (by omega) _ (by rw [hfrV']) y0V' hy0V' (j - 1)
      have hstep' : BallKStmt ((EuclideanSpace ℝ (Fin (d - 2))) × (EuclideanSpace ℝ (Fin 2)))
          y0c hy0c (j - 1 + 1) :=
        hstep (EuclideanSpace ℝ (Fin (d - 2))) (EuclideanSpace ℝ (Fin 2))
          y0V' hy0V' y0W' hy0W' y0c hy0c (by rw [hfrV']; omega) hfrW (j - 1) ihV'
      have hj : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hjpos
      rw [hj] at hstep'
      exact htrans V ((EuclideanSpace ℝ (Fin (d - 2))) × (EuclideanSpace ℝ (Fin 2)))
        (LinearEquiv.ofFinrankEq V _ (by
          rw [hd, Module.finrank_prod, hfrV', hfrW]; omega)) y0 hy0 y0c hy0c j hstep'

/-- `K̃(D_V / S_V) = K̃(S^d)`, `d = dim V`: infinite cyclic with `ψ^k = k^j` if `d = 2j`,
zero if `d` is odd. -/
theorem ball_K (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (y0 : Ball V) (hy0 : y0 ∈ bdry V) (j : ℕ) :
    (Module.finrank ℝ V = 2 * j →
      (∃ g : K0 (Kpair V), K0.mapA (augPair V y0) g = 0 ∧ (∀ k : ℤ, k • g = 0 → k = 0) ∧
        ∀ z, K0.mapA (augPair V y0) z = 0 → ∃ k : ℤ, z = k • g) ∧
      (∀ ψ : K0 (Kpair V) →+ K0 (Kpair V), IsPsi2 ψ →
        ∀ z, K0.mapA (augPair V y0) z = 0 → ψ z = (2 ^ j : ℤ) • z) ∧
      (∀ ψ : K0 (Kpair V) →+ K0 (Kpair V), IsPsi3 ψ →
        ∀ z, K0.mapA (augPair V y0) z = 0 → ψ z = (3 ^ j : ℤ) • z)) ∧
    (Module.finrank ℝ V = 2 * j + 1 → ∀ z, K0.mapA (augPair V y0) z = 0 → z = 0) := by
  refine ball_K_of (htrans := ballK_transfer) (hbase1 := ballK_dim1) (hbase2 := ?_)
    (hstep := ballK_step) V y0 hy0 j
  intro y0W hy0W
  refine ⟨fun _ => ?_, fun hh => ?_⟩
  · obtain ⟨H, hH0, hH1, hH2, hHpsi2, hHpsi3⟩ := ballK_dim2 y0W hy0W
    refine ⟨⟨H, hH0, hH1, hH2⟩, ?_, ?_⟩
    · intro ψ hψ z hz
      obtain ⟨k, hk⟩ := hH2 z hz
      rw [hk, map_zsmul, hHpsi2 ψ hψ]
      rw [show (2 : ℤ) ^ 1 = 2 from by norm_num]
      first
        | exact smul_comm k 2 H
        | rw [smul_comm k 2 H]
        | simp only [smul_smul, mul_comm]
        | rw [← mul_smul k 2 H, ← mul_smul 2 k H, mul_comm]
    · intro ψ hψ z hz
      obtain ⟨k, hk⟩ := hH2 z hz
      rw [hk, map_zsmul, hHpsi3 ψ hψ]
      rw [show (3 : ℤ) ^ 1 = 3 from by norm_num]
      first
        | exact smul_comm k 3 H
        | rw [smul_comm k 3 H]
        | simp only [smul_smul, mul_comm]
        | rw [← mul_smul k 3 H, ← mul_smul 3 k H, mul_comm]
  · rw [finrank_euclideanSpace_fin] at hh
    omega

end

end Work.KT
