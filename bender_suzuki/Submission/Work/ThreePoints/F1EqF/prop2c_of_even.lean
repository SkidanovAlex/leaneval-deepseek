import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.centD_eq_centralizer_of_involution

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.F1EqF

open Submission.Blueprint

/-!
# Peterfalvi I Ch. II §4 Prop. 2 (c), conditional on the `hEven` hypothesis

`Work.ThreePoints.F1EqF.prop2c_of_even` is Prop. 2 (c) of Peterfalvi I Ch. II §4, in the
"even centraliser" form: the hypothesis `hEven` is exactly Ch. II §4 Prop. 1 (a)
(`Work.ThreePoints.even_card_centralizer_of_fixes_three`) with the FT/ThmA/ThmC/Situation
inputs packaged into a single statement about `|C_M(X)|` being even.  The argument is the
Prop. 2 (c) half of `Work.ThreePoints.centD_eq_centralizer_of_involution`: if `x ∈ K#` fixed
`≥ 3` points, then `C_H(x)` would have even order, hence contain an involution, and
`Work.ThreePoints.inv_conj_injective_on_invertedBy` would force `x = 1`.
-/

/-- **Peterfalvi I Ch. II §4 Prop. 2 (c)**, with the even-cardinality input `hEven` (Prop. 1 (a))
taken as a hypothesis rather than derived: every non-trivial element `x` of `K = J(D,t)`,
`D = twoPoint H t`, fixes exactly two points of `Ω = G ⧸ H`. -/
theorem prop2c_of_even {G : Type} [Group G] [Finite G]
    (hC : Submission.Blueprint.ThmCProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H)
    (hEven : ∀ (X M : Subgroup G), (∃ g : G, M = Submission.Blueprint.conj g H) → X ≤ M →
      3 ≤ (Submission.Blueprint.fixedPts H X).ncard →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)))
    {x : G} (hx : x ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t)
    (hx1 : x ≠ 1) :
    (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard = 2 := by
  classical
  have hxD : x ∈ Submission.Blueprint.twoPoint H t := hx.1
  have hxH : x ∈ H := (Work.ThreePoints.mem_twoPoint.mp hxD).1
  have hxt : x ∈ Submission.Blueprint.conj t H :=
    Work.ThreePoints.mem_conj_iff.mpr (Work.ThreePoints.mem_twoPoint.mp hxD).2
  have hmem1 : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk,
      Work.ThreePoints.conj_one]
    exact Subgroup.zpowers_le.mpr hxH
  have hmemt : (t : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk]
    exact Subgroup.zpowers_le.mpr hxt
  have h1t : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact htH (by simpa using hcon)
  refine le_antisymm ?_ ?_
  · -- `≤ 2`: otherwise Prop. 1(a) (`hEven`) produces an involution of `H` centralising `x`
    by_contra hle
    have hge3 : 3 ≤ (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard := by omega
    have hEv : Even (Nat.card
        (H ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) : Subgroup G)) :=
      hEven (Subgroup.zpowers x) H ⟨1, by rw [Work.ThreePoints.conj_one]⟩
        (Subgroup.zpowers_le.mpr hxH) hge3
    obtain ⟨v, hv_mem, hv2⟩ := Work.ThreePoints.exists_orderOf_two_of_even_card hEv
    have hvH : v ∈ H := (Subgroup.mem_inf.mp hv_mem).1
    have hvC : v ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hv_mem).2
    have hvx : x * v = v * x :=
      Subgroup.mem_centralizer_iff.mp hvC x (Subgroup.mem_zpowers x)
    have heq : x⁻¹ * v * x = (1 : G)⁻¹ * v * 1 := by
      rw [inv_one, one_mul, mul_one, mul_assoc, ← hvx, ← mul_assoc, inv_mul_cancel, one_mul]
    have hx1' : x = 1 :=
      Work.ThreePoints.inv_conj_injective_on_invertedBy hH ht htH hvH hv2 x hx 1
        (Work.ThreePoints.one_mem_invertedBy _ _) heq
    exact hx1 hx1'
  · -- `≥ 2`: the two points `H` and `tH` are fixed by `x`
    have h2 : ({((1 : G) : G ⧸ H), (t : G ⧸ H)} : Set (G ⧸ H)).ncard = 2 :=
      Set.ncard_pair h1t
    calc 2 = _ := h2.symm
      _ ≤ (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard :=
          Set.ncard_le_ncard (by
            intro y hy
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · exact hmem1
            · exact hmemt)

end Work.ThreePoints.F1EqF
