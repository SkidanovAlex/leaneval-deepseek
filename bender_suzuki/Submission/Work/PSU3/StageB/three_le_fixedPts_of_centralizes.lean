import Mathlib
import Submission.Work.PSU3.StageB.NotFpfAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Stage B / B2 — `three_le_fixedPts_of_centralizes`

In the split rank-one datum `H = Q ⋊ D` with `D = twoPoint H t = H ∩ H^t` and
`Ω = G ⧸ H`, if a subgroup `P ≤ D` centralises a nontrivial element `y ∈ Q`, then `P` fixes
at least three points of `Ω`, namely

* `∞ = pt H = H` (fixed by all of `H`),
* `t • ∞ = tH` (fixed by all of `D`), and
* `qPt H t y = y • (t • ∞) = y t H` (fixed by every `p ∈ P`, because `p` commutes with `y`
  and the `D`-part `p` is absorbed across `t`).

The three points are pairwise distinct: `t ∉ H` separates the first two, `y ∈ Q` with
`Q ∩ D = 1` separates `∞` from `y t H` (`qPt_ne_pt`), and the same `Q ∩ D = 1` separates
`t • ∞` from `y t H`.
-/

set_option autoImplicit false

open Submission.Blueprint

namespace Work.PSU3.StageB

/-- A `d ∈ D = twoPoint H t` fixes the point `t • ∞ = t • pt H`: the `D`-part is absorbed
across `t` because `t d t ∈ H`. -/
theorem smul_t_smul_pt_eq {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {d : G} (hd : d ∈ twoPoint H t) :
    d • (t • Work.RankOneUniqueness.pt H) = t • Work.RankOneUniqueness.pt H := by
  have h2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one h
  have hdtH : t * d * t ∈ H := Work.RankOneUniqueness.t_mul_mul_t_mem_of_mem_twoPoint h2 hd
  have hsplit : t * (t * d * t) = d * t := by
    rw [← mul_assoc t (t * d) t, Work.RankOneUniqueness.mul_self_mul h d]
  rw [Work.RankOneUniqueness.smul_pt, Work.RankOneUniqueness.smul_mk, ← hsplit,
    QuotientGroup.mk_mul_of_mem t hdtH]

/-- If `d ∈ D = twoPoint H t` commutes with `y`, then `d` fixes the point
`qPt H t y = y • (t • ∞)`. -/
theorem smul_qPt_of_centralizes {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {d y : G}
    (hd : d ∈ twoPoint H t) (hdy : d * y = y * d) :
    d • Work.RankOneUniqueness.qPt H t y = Work.RankOneUniqueness.qPt H t y := by
  rw [Work.RankOneUniqueness.qPt_eq_smul, ← mul_smul, hdy, mul_smul, smul_t_smul_pt_eq h hd]

/-- `p⁻¹ * y * p = y` is equivalent to `y` commuting with `p`. -/
theorem mul_comm_of_conj_eq_self {G : Type} [Group G] {p y : G}
    (hpyp : p⁻¹ * y * p = y) : y * p = p * y := by
  calc y * p = p * (p⁻¹ * y * p) := by group
    _ = p * y := by rw [hpyp]

/-- **Stage B / B2, fixed-point count.** A subgroup `P ≤ D = H ∩ H^t` of the split rank-one
datum centralising a nontrivial `y ∈ Q` fixes at least three points of `Ω = G ⧸ H`
(namely `∞`, `t • ∞` and `y t · ∞`). -/
theorem three_le_fixedPts_of_centralizes {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {P : Subgroup G}
    (hPD : P ≤ Submission.Blueprint.twoPoint H t) {y : G}
    (hyQ : y ∈ Q) (hy1 : y ≠ 1) (hyc : ∀ p ∈ P, p⁻¹ * y * p = y) :
    3 ≤ (Submission.Blueprint.fixedPts H P).ncard := by
  -- `P ≤ H`, and every `p ∈ P` commutes with `y`.
  have hPH : P ≤ H := hPD.trans (Work.RankOneUniqueness.twoPoint_le_left H t)
  have hcomm : ∀ p ∈ P, p * y = y * p :=
    fun p hp => (mul_comm_of_conj_eq_self (hyc p hp)).symm
  -- The three fixed points.
  have hmem0 : Work.RankOneUniqueness.pt H ∈ Submission.Blueprint.fixedPts H P := by
    intro p hp
    exact Work.RankOneUniqueness.smul_pt_of_mem H (hPH hp)
  have hmem1 : t • Work.RankOneUniqueness.pt H ∈ Submission.Blueprint.fixedPts H P := by
    intro p hp
    exact smul_t_smul_pt_eq h (hPD hp)
  have hmem2 : Work.RankOneUniqueness.qPt H t y ∈ Submission.Blueprint.fixedPts H P := by
    intro p hp
    exact smul_qPt_of_centralizes h (hPD hp) (hcomm p hp)
  -- Pairwise distinctness.
  have e01 : Work.RankOneUniqueness.pt H ≠ t • Work.RankOneUniqueness.pt H :=
    fun hh => Work.RankOneUniqueness.t_smul_pt_ne h hh.symm
  have e02 : Work.RankOneUniqueness.pt H ≠ Work.RankOneUniqueness.qPt H t y :=
    fun hh => Work.RankOneUniqueness.qPt_ne_pt h hyQ hh.symm
  have e12 : t • Work.RankOneUniqueness.pt H ≠ Work.RankOneUniqueness.qPt H t y := by
    intro heq
    have h1 : (t : G ⧸ H) = ((y * t : G) : G ⧸ H) := by
      rw [← Work.RankOneUniqueness.smul_pt H t, heq, Work.RankOneUniqueness.qPt_def]
    have hmemH : t⁻¹ * y * t ∈ H := by
      have hq := QuotientGroup.eq.mp h1
      rwa [show t⁻¹ * (y * t) = t⁻¹ * y * t from by rw [mul_assoc]] at hq
    have hyconj : y ∈ Submission.Blueprint.conj t H := by
      rw [Work.RankOneUniqueness.mem_conj_iff]
      exact ⟨t⁻¹ * y * t, hmemH, by group⟩
    have hmemD : y ∈ Q ⊓ Submission.Blueprint.twoPoint H t :=
      ⟨hyQ, h.le hyQ, hyconj⟩
    rw [h.inf_eq, Subgroup.mem_bot] at hmemD
    exact hy1 hmemD
  -- The three points lie in `fixedPts H P`.
  have hsub : ({Work.RankOneUniqueness.pt H, t • Work.RankOneUniqueness.pt H,
      Work.RankOneUniqueness.qPt H t y} : Set (G ⧸ H)) ⊆
      Submission.Blueprint.fixedPts H P := by
    intro ω hω
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
    rcases hω with rfl | rfl | rfl
    · exact hmem0
    · exact hmem1
    · exact hmem2
  -- They are three distinct points, so this set has cardinality `3`.
  have hn0 : Work.RankOneUniqueness.pt H ∉
      ({t • Work.RankOneUniqueness.pt H, Work.RankOneUniqueness.qPt H t y} :
        Set (G ⧸ H)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨e01, e02⟩
  have hn1 : t • Work.RankOneUniqueness.pt H ∉
      ({Work.RankOneUniqueness.qPt H t y} : Set (G ⧸ H)) := by
    simpa using e12
  have hcard : ({Work.RankOneUniqueness.pt H, t • Work.RankOneUniqueness.pt H,
      Work.RankOneUniqueness.qPt H t y} : Set (G ⧸ H)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hn0, Set.ncard_insert_of_notMem hn1, Set.ncard_singleton]
  calc 3 = _ := hcard.symm
    _ ≤ (Submission.Blueprint.fixedPts H P).ncard := Set.ncard_le_ncard hsub

end Work.PSU3.StageB
