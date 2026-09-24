import Submission.Work.Mori.Defs
import Submission.Work.Mori.Circle
import Submission.Work.Mori.exists_sphere_eq_empty
import Submission.Work.Mori.not_hasZeroFeketeCapacity_closedBall

/-!
# The API of polar sets, with dot notation

The definitions live in `Submission/Work/Mori/Defs.lean` (`Work.Mori.IsPolar`,
`Work.Mori.HasZeroFeketeCapacity`, `Work.Mori.feketeMean`) and the thinness of a polar set at each of
its points is `Work.Mori.exists_sphere_eq_empty` (imported here).  This module adds the namespaced
aliases, so that callers can write `hpolar.exists_sphere_eq_empty hclosed hp`.
-/

open scoped Manifold ContDiff Topology

noncomputable section

namespace Work.Mori

namespace IsPolar

/-- **A polar closed set is thin at each of its points**: around every `p ∈ K` there is a circle
centred at `p` that misses `K`.  (`Work.Mori.exists_sphere_eq_empty`.) -/
theorem exists_sphere_eq_empty {K : Set ℂ} (hK : IsPolar K) (hKc : IsClosed K) {p : ℂ}
    (hp : p ∈ K) : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ K, ‖z - p‖ ≠ r :=
  Work.Mori.exists_sphere_eq_empty hK hKc hp

end IsPolar


/-- **A closed disc is not polar**: it is a compact set of positive Fekete capacity. -/
theorem not_isPolar_closedBall (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ¬ IsPolar (Metric.closedBall x ε) :=
  fun h => not_hasZeroFeketeCapacity_closedBall x hε
    (h _ subset_rfl (isCompact_closedBall x ε))

/-- **The complement of a closed polar set is dense.**  If a ball of positive radius around some point
were contained in the polar closed set `K`, then `K` would contain a closed disc, which is not polar
(`Work.Mori.not_isPolar_closedBall`), contradicting `IsPolar.mono`. -/
theorem IsPolar.dense_compl {K : Set ℂ} (hK : IsPolar K) (hKc : IsClosed K) : Dense Kᶜ := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_contra hcon
  push_neg at hcon
  have hsub : Metric.closedBall x (ε / 2) ⊆ K := by
    intro y hy
    by_contra hyK
    have hdist : dist x y ≤ ε / 2 := by
      rw [dist_comm]; exact Metric.mem_closedBall.mp hy
    have := hcon y hyK
    linarith
  exact not_isPolar_closedBall x (by linarith) (hK.mono hsub)

/-- **Finite sets have vanishing Fekete capacity.**  Choose `n` larger than the cardinality of `K`:
then two of any `n` points of `K` coincide, so the Fekete mean vanishes (a product of pairwise
distances with a zero factor). -/
theorem HasZeroFeketeCapacity.of_finite {K : Set ℂ} [Finite ↥K] : HasZeroFeketeCapacity K := by
  intro ε hε
  haveI := Fintype.ofFinite ↥K
  refine ⟨Nat.card ↥K + 2, by omega, fun z => ?_⟩
  obtain ⟨i, j, hij, hzij⟩ := Fintype.exists_ne_map_eq_of_card_lt z (by simp)
  have hval : (z i : ℂ) = (z j : ℂ) := congrArg Subtype.val hzij
  have hzero : (∏ i : Fin (Nat.card ↥K + 2), ∏ j ∈ Finset.Ioi i,
      ‖(z i : ℂ) - (z j : ℂ)‖) = 0 := by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_Ioi.mpr hlt)
        (by rw [hval, sub_self, norm_zero]))
    · exact Finset.prod_eq_zero (Finset.mem_univ j) (Finset.prod_eq_zero (Finset.mem_Ioi.mpr hlt)
        (by rw [← hval, sub_self, norm_zero]))
  have hC : (0 : ℕ) < (Nat.card ↥K + 2) * (Nat.card ↥K + 2 - 1) / 2 := by
    apply Nat.div_pos
    · calc (2:ℕ) = 2 * 1 := by norm_num
        _ ≤ (Nat.card ↥K + 2) * (Nat.card ↥K + 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
    · norm_num
  have hexp : (1 : ℝ) / (((Nat.card ↥K + 2) * (Nat.card ↥K + 2 - 1) / 2 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (one_div_pos.mpr (Nat.cast_pos.mpr hC))
  rw [feketeMean, hzero, Real.zero_rpow hexp]
  exact hε

/-- **Every finite subset of `ℂ` is polar**: its compact subsets are finite, and finite sets have
vanishing Fekete capacity. -/
theorem IsPolar.of_finite {K : Set ℂ} [Finite ↥K] : IsPolar K := fun L hL _ =>
  haveI : Finite ↥L := Finite.of_injective (fun x : ↥L => (⟨(x : ℂ), hL x.2⟩ : ↥K))
    (fun a b hab => Subtype.ext (congrArg (fun w : ↥K => (w : ℂ)) hab))
  HasZeroFeketeCapacity.of_finite (K := L)

end Work.Mori
