import Mathlib
import Submission.Work.PSU3.StageB.Omega.fcan_zU_eq_vSeq
import Submission.Work.PSU3.StageB.Omega.orderOf_beta_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `bS β i ≠ 0` for `1 ≤ i < orderOf β`. -/
private lemma bS_ne_zero_of_lt_orderOf_zU {β : E n} (hβ : β ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    (hlt : i < orderOf β) : bS β i ≠ 0 := by
  rw [bS_ne_zero_iff β hβ i]
  intro hbi
  have hdvd : orderOf β ∣ i := orderOf_dvd_iff_pow_eq_one.mpr hbi
  exact absurd (Nat.le_of_dvd hi hdvd) (by omega)

/-- `bar` kills the `Q₀`-element `zc v`. -/
lemma bar_zcQ (fr : CoarseFrame H Q t n) (v : E n) (hv : σE v = v) :
    fr.bar (zcQ fr v hv) = 1 := by
  rw [fr.bar_eq_one_iff]
  exact fr.zc_mem v hv

/-- Conjugating `y · zc v` by the `KW`-element `d` multiplies the `E`-coordinate by `κ d`. -/
lemma toAdd_bar_qconj_zcQ (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW)
    (y : Q) (v : E n) (hv : σE v = v) :
    Multiplicative.toAdd (fr.bar (qconj hS.split ⟨(d : fr.KW), fr.KW_le d.2⟩
        (y * zcQ fr v hv))) =
      (fr.κ d : E n) * Multiplicative.toAdd (fr.bar y) := by
  rw [show qconj hS.split ⟨(d : fr.KW), fr.KW_le d.2⟩ (y * zcQ fr v hv)
      = kact hS fr d (y * zcQ fr v hv) from Subtype.ext rfl, kact_bar]
  congr 1
  rw [map_mul, bar_zcQ fr v hv, mul_one]

lemma zU_mem_selfOrbitSet {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    {β : Work.PSU3.E n} (hβ : β ≠ 0) (hσ : Work.PSU3.σE β = β ∨ Work.PSU3.σE β = β⁻¹)
    (hβα : β + β⁻¹ = Work.PSU3.StageB.fval α) :
    ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 →
      Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
        (ω * Work.PSU3.StageB.Omega.zU fr β hβ hσ i)))
        ∈ Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω)) := by
  have hα0 : fval α ≠ 0 := Units.ne_zero α.1
  have hα : σE (fval α) = fval α := α.2
  -- `orderOf β = orderOf ζ`, so `S_i ≠ 0` for `1 ≤ i ≤ orderOf ζ - 1`
  have hord : orderOf β = orderOf fr.ζ := orderOf_beta_eq hS fr hω hωf hβ hβα
  have hmpos : 1 ≤ orderOf fr.ζ :=
    Nat.one_le_iff_ne_zero.mpr (orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite fr.ζ))
  set lam : ℕ → ↥(FX n) := lamSeq (fval α) β hα hσ with hlamdef
  have hN : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → bS β i ≠ 0 := by
    intro i hi hiN
    refine bS_ne_zero_of_lt_orderOf_zU hβ hi ?_
    rw [hord]
    omega
  have hlam : ∀ i, 1 ≤ i → i ≤ orderOf fr.ζ - 1 → fval (lam i) = wSeq (fval α) β i := by
    intro i hi hiN
    exact fval_lamSeq (fval α) β hα hσ (wSeq_ne_zero (fval α) β hα0 i (hN i hi hiN))
  intro i hi hiN
  -- §2 (17), sharp form: `f (ω zc u_i) = (ω zc v_i)^{d_i}`
  have heq := fcan_zU_eq_vSeq hS fr hω hωf hβ hσ hβα lam hlam hN i hi hiN
  rw [heq]
  -- the `E`-coordinate of the conjugate is `κ d_i` times that of `ω`
  refine ⟨dSeq hS fr lam i, ?_⟩
  exact toAdd_bar_qconj_zcQ hS fr (dSeq hS fr lam i) ω (vSeq (fval α) β i) _

end Work.PSU3.StageB.Omega
