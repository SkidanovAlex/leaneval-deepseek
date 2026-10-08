import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.FMap
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.PSU3.RankOne.H16
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.PSU3.RankOne.canon_mul_ne_one
import Submission.Work.PSU3.StageC.e_zc_eq
import Submission.Work.PSU3.StageC.FSuz

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.PSU3.StageB

namespace Work.PSU3.StageC

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `FRel` forces `y` to be the canonical `f(x)`. -/
theorem eq_fcan_of_FRel (hS : Work.PSU3.PSU3Hyp H Q t) {x y : Q} (hx : (x : G) ≠ 1)
    (h : Work.RankOneUniqueness.FRel H t (x : G) (y : G)) :
    (y : G) = (fcan hS.split x : G) := by
  obtain ⟨m, hm, hmeq⟩ := h
  have hc := Work.PSU3.StageB.canon_spec hS.split hx
  have hmem : (gcan hS.split x : G) * (hcan hS.split x : G) ∈ H :=
    H.mul_mem (hS.split.le (gcan hS.split x).2)
      (Work.RankOneUniqueness.twoPoint_le_left H t (hcan hS.split x).2)
  exact (Work.RankOneUniqueness.canon_unique hS.split hm hmem y.2 (fcan hS.split x).2
    (by rw [← hmeq, hc])).2

/-- The agreement on `Q₀`. -/
theorem agree_Q0 (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x)) :
    ∀ u : Q, (u : G) ∈ fr.Q0 →
      e (fcan hS.split u) = Work.PSU3.fMapTot (e u) := by
  intro u hu
  obtain ⟨v, hv, hzv⟩ := fr.zc_surj u hu
  have hueq : u = zcQ fr v hv := by
    apply Subtype.ext
    show (u : G) = fr.zc v
    rw [hzv]
  rw [hueq]
  by_cases hv0 : v = 0
  · have hzc0 : zcQ fr v hv = 1 := by
      apply Subtype.ext
      show fr.zc v = 1
      rw [hv0]
      exact Work.PSU3.StageB.zc_zero fr
    rw [hzc0]
    have hf1 : fcan hS.split (1 : Q) = 1 := by
      simp [Work.PSU3.StageB.fcan]
    rw [hf1, map_one, Work.PSU3.fMapTot_one]
  · have hfcan : fcan hS.split (zcQ fr v hv) = (zcQ fr v⁻¹ (by rw [map_inv₀, hv]) : Q) := by
      apply Subtype.ext
      show (fcan hS.split (zcQ fr v hv) : G) = fr.zc v⁻¹
      exact (fgcan_zcQ hS fr hsq v hv hv0).1
    rw [hfcan,
      e_zcQ (hS := hS) (hsq := hsq) (e := e) (μ := μ) (hex := hex) (hes := hes)
        (heq := heq) (v := v⁻¹) (hv := by rw [map_inv₀, hv]),
      e_zcQ (hS := hS) (hsq := hsq) (e := e) (μ := μ) (hex := hex) (hes := hes)
        (heq := heq) (v := v) (hv := hv)]
    have hne : (⟨0, v, by rw [hv, CharTwo.add_self_eq_zero, zero_mul]⟩ :
        SZ (Work.PSU3.E n)) ≠ 1 := by
      intro hcon
      have hy : (⟨0, v, by rw [hv, CharTwo.add_self_eq_zero, zero_mul]⟩ :
          SZ (Work.PSU3.E n)).y = 0 := congrArg (fun z => z.y) hcon
      simp at hy
      exact hv0 hy
    rw [Work.PSU3.fMapTot_of_ne_one hne]
    apply SZ.ext
    · simp [SZ.fMap_x]
    · simp [SZ.fMap_y]

end Work.PSU3.StageC
