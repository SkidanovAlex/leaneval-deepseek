import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.Omega.fcan_step10
import Submission.Work.PSU3.StageB.Theta
import Submission.Work.PSU3.StageB.ThetaOmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB.NotFpfStep4

open Work.PSU3
open Work.PSU3.StageB
open Work.PSU3.StageB.Omega

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Elementary facts about `Q₀` -/

/-- `zcQF fr u ∈ Q₀` is trivial under `bar`. -/
lemma bar_fcan_step4_3_bar_zcQF (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    fr.bar (zcQF fr u) = 1 :=
  bar_eq_one_of_mem_Q0 fr (by rw [zcQF_coe]; exact fr.zc_mem (fval u) u.2)

/-- `sᵘ = zcQF fr (nmF fr u)` lies in `Q₀`. -/
lemma bar_fcan_step4_3_sconjF_mem_Q0 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (u : ↥(FX n)) : (sconjF fr u : G) ∈ fr.Q0 := by
  rw [sconjF_eq_zcQF fr hS u, zcQF_coe]
  exact fr.zc_mem (fval (nmF fr u)) (nmF fr u).2

/-- `bar (f (ω · zc u))` is unchanged when the second argument of `f` is a `Q₀`-element:
the recursion of §2 (10) holds at the `bar`-level. -/
lemma bar_fcan_step10 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {u v : ↥(FX n)} (huv : fval v = fval α + (fval u)⁻¹)
    (h1 : ((ω * zcQF fr u : ↥Q) : G) ≠ 1) :
    Multiplicative.toAdd (fr.bar (fcan hS.split (ω * zcQF fr u))) =
      (fr.κ (zetaExp hS fr u) : E n) *
        Multiplicative.toAdd (fr.bar (fcan hS.split (ω * zcQF fr v))) := by
  have hstep := fcan_step10 hS fr hω hωf huv h1
  have hbar := fr.act_bar (zetaExp hS fr u)
    (fcan hS.split (ω * zcQF fr v) * zcQF fr u) (fcan hS.split (ω * zcQF fr u)) hstep
  rw [hbar]
  congr 1
  rw [map_mul, toAdd_mul, bar_fcan_step4_3_bar_zcQF fr u, toAdd_one, add_zero]

/-- The scalar `κ (ζ a⁻²)` for `a = kElF (τ (nmF fr a))`: since `τ (nm u) = u`, this is
`κ ζ · (fval a)⁻¹ · (fval a)⁻¹`. -/
lemma kappa_zetaExp_nmF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (a : ↥(FX n)) :
    (fr.κ (zetaExp hS fr (nmF fr a)) : E n) =
      (fr.κ fr.ζ : E n) * ((fval a)⁻¹ * (fval a)⁻¹) := by
  have h : zetaExp hS fr (nmF fr a) = fr.ζ * (kElF fr a)⁻¹ * (kElF fr a)⁻¹ := by
    simp only [zetaExp, tau_nm]
  rw [h]
  simp only [map_mul, map_inv, kElF_kappa, Units.val_mul, Units.val_inv_eq_inv_val, fval]
  rw [mul_assoc]

theorem bar_fcan_step4_3 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω * Work.PSU3.StageB.zcQF fr α))
    {a b : ↥(Work.PSU3.StageB.FX n)}
    (hb : Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr b) =
      Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a))⁻¹) :
    Multiplicative.toAdd
        (fr.bar (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.sconjF fr a))) =
      (fr.κ fr.ζ : Work.PSU3.E n) * ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) *
        Multiplicative.toAdd
          (fr.bar (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.sconjF fr b))) := by
  rw [sconjF_eq_zcQF fr hS a, sconjF_eq_zcQF fr hS b]
  have h1 : ((ω * zcQF fr (nmF fr a) : ↥Q) : G) ≠ 1 := by
    intro hc
    have hmem : ((zcQF fr (nmF fr a) : ↥Q) : G) ∈ fr.Q0 := by
      rw [zcQF_coe]; exact fr.zc_mem (fval (nmF fr a)) (nmF fr a).2
    have heq : (ω : G) =
        ((ω * zcQF fr (nmF fr a) : ↥Q) : G) * (((zcQF fr (nmF fr a) : ↥Q) : G))⁻¹ := by
      rw [Subgroup.coe_mul]; group
    refine hω ?_
    rw [heq, hc, one_mul]
    exact fr.Q0.inv_mem hmem
  rw [bar_fcan_step10 hS fr hω hωf hb h1, kappa_zetaExp_nmF hS fr a]

end Work.PSU3.StageB.NotFpfStep4
