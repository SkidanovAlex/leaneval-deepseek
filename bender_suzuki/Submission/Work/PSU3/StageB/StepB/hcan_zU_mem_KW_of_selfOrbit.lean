/-
# `Work.PSU3.StageB.StepB.hcan_zU_mem_KW_of_selfOrbit`

The **base case** of the §2 (p. 274) layer of `exists_omega_of_fpf_rebuilt`: for a good element
`ω ∈ Q ∖ Q₀` (i.e. `f(ω) = ζ⁻¹ (ω · zc α) ζ`) whose `h`-component lies in `W ≤ fr.KW`, the
`h`-components of the translates `ω · zU fr β hβ hσ i` along the §2 (13) sequence

  `uSeq β i = u_i`,  `uSeq β 1 = 0`,  `zU fr β hβ hσ i = zc (u_i)`,

are all in `fr.KW` for `1 ≤ i ≤ N`.

The proof is the induction along the μ-orbit of `0`:

* `u_{i+1} = 1/(α + u_i)` is `Omega.uSeq_rec_alpha`, i.e. `u_i = α + u_{i+1}⁻¹`;
* the §2 (18) recursion as a membership criterion (`StepB.hcan_mul_zcQF_mem_KW_iff`) gives

  `h (ω · zc u) ∈ fr.KW ↔ h (ω · zc (α + u⁻¹)) ∈ fr.KW`,

  so `h (ω · zc u_{i+1}) ∈ fr.KW ↔ h (ω · zc u_i) ∈ fr.KW`;
* the base point `i = 1` has `u_1 = 0`, i.e. `zU fr β hβ hσ 1 = 1`, and
  `h(ω) ∈ W ≤ fr.KW` is a hypothesis.

The non-degeneracy hypotheses `bS β i ≠ 0` (for `1 ≤ i ≤ N`) are exactly what is needed to make
`u_i ≠ 0` (`Omega.uSeq_ne_zero`), so that `u_i` is an element of the fixed field `F*`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.beta_pow_setup
import Submission.Work.PSU3.StageB.Omega.fcan_zU_eq_vSeq
import Submission.Work.PSU3.StageB.Omega.hcan_pow_m_eq_one
import Submission.Work.PSU3.StageB.StepB.hcan_mul_zcQF_mem_KW_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB.StepB

open Work.PSU3.StageB.Omega
open Work.PSU3.StageB

theorem hcan_zU_mem_KW_of_selfOrbit {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hWKW : Work.ThmF.W H t ≤ fr.KW)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω * Work.PSU3.StageB.zcQF fr α))
    (hWω : ((Work.PSU3.StageB.hcan hS.split ω : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈
      Work.ThmF.W H t)
    {β : Work.PSU3.E n} (hβ : β ≠ 0) (hσ : σE β = β ∨ σE β = β⁻¹)
    (hβα : β + β⁻¹ = Work.PSU3.StageB.fval α) {N : ℕ}
    (hN : ∀ i, 1 ≤ i → i ≤ N → Work.PSU3.StageB.Omega.bS β i ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ N →
      (((Work.PSU3.StageB.hcan hS.split (ω * Work.PSU3.StageB.Omega.zU fr β hβ hσ i) :
          ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) := by
  intro i hi hiN
  -- The membership statement, in the `zU`-form of the target.
  have hmem : ∀ m, 1 ≤ m → m ≤ N →
      (((Work.PSU3.StageB.hcan hS.split
          (ω * Work.PSU3.StageB.Omega.zU fr β hβ hσ m) :
          ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) := by
    -- induction along the μ-orbit of `0`: `u_1 = 0`, `u_i = α + u_{i+1}⁻¹`
    refine Nat.le_induction (m := 1)
      (P := fun m _ => m ≤ N →
        (((Work.PSU3.StageB.hcan hS.split
            (ω * Work.PSU3.StageB.Omega.zU fr β hβ hσ m) :
            ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW)) ?base ?step
    · -- base point: `u_1 = 0`, so `zU fr β hβ hσ 1 = 1` and `h(ω) ∈ W ≤ fr.KW`
      intro _
      have hzU1 : Work.PSU3.StageB.Omega.zU fr β hβ hσ 1 = 1 := by
        apply Subtype.ext
        simp [Work.PSU3.StageB.Omega.zU_coe, Work.PSU3.StageB.Omega.uSeq_one,
          Work.PSU3.StageB.zc_zero]
      rw [hzU1, mul_one]
      exact hWKW hWω
    · -- the §2 (13) step `u_m = α + u_{m+1}⁻¹`, run through §2 (18)
      intro m hm ih hmN
      have hmN' : m ≤ N := by omega
      have hbm : Work.PSU3.StageB.Omega.bS β m ≠ 0 := hN m hm hmN'
      have hbm1 : Work.PSU3.StageB.Omega.bS β (m + 1) ≠ 0 := hN (m + 1) (by omega) hmN
      -- `u_{m+1}` as an element of `F*`
      set U : ↥(Work.PSU3.StageB.FX n) :=
        Work.PSU3.StageB.mkFX (Work.PSU3.StageB.Omega.uSeq β (m + 1))
          (Work.PSU3.StageB.Omega.uSeq_fixed β hβ hσ (m + 1))
          (Work.PSU3.StageB.Omega.uSeq_ne_zero β hβ m hbm hbm1) with hUdef
      have hU : Work.PSU3.StageB.fval U = Work.PSU3.StageB.Omega.uSeq β (m + 1) := rfl
      -- §2 (13): `u_m = α + u_{m+1}⁻¹`
      have huv : Work.PSU3.StageB.Omega.uSeq β m =
          Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval U)⁻¹ := by
        rw [hU]
        exact (Work.PSU3.StageB.Omega.uSeq_rec_alpha (Work.PSU3.StageB.fval α) β hβα hβ
          hm hbm hbm1).symm
      -- §2 (18) as a membership criterion
      have hiff := Work.PSU3.StageB.StepB.hcan_mul_zcQF_mem_KW_iff (hS := hS) (fr := fr)
        hWKW hω hωf hWω (U := U) (v := Work.PSU3.StageB.Omega.uSeq β m)
        (Work.PSU3.StageB.Omega.uSeq_fixed β hβ hσ m) huv
      -- the induction hypothesis, in `zcQ`-form
      have hstep : (((Work.PSU3.StageB.hcan hS.split
          (ω * Work.PSU3.StageB.zcQ fr (Work.PSU3.StageB.Omega.uSeq β m)
            (Work.PSU3.StageB.Omega.uSeq_fixed β hβ hσ m)) :
          ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) := ih hmN'
      -- the next index `m+1` is the `zcQF fr U`-translate of `ω`
      have hL : ω * Work.PSU3.StageB.Omega.zU fr β hβ hσ (m + 1) =
          ω * Work.PSU3.StageB.zcQF fr U := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Work.PSU3.StageB.Omega.zU_coe,
          Work.PSU3.StageB.zcQF_coe, hU]
      rw [hL]
      exact hiff.mpr hstep
  exact hmem i hi hiN

end Work.PSU3.StageB.StepB
