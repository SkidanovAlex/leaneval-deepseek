/-
# `Work.PSU3.StageB.StepB.hcan_inv_mul_zcQF_mem_KW`

Peterfalvi II Ch. VII §2 (the Proposition of p. 274), the third of the three `h ∈ KW`
instances consumed by `Omega.square_eq_shift_of_good_cover_hKW`: the `h`-component of
`x₅ = ωₖ⁻¹ · zc r` lies in `fr.KW`.

The reference's single appeal outside the orbit bookkeeping is

> "Moreover by H4, `h(ω_k⁻¹(0,r)) ∈ KW`."

The point of the argument is that **all** the required data is on the frame: writing
`x₂ = ω₁ · (zc r · zc α)` for the argument of the cross relation `hd₂`, one has

* `ω₁ · zc r = ω₁⁻¹` (`hsq : ω₁ * ω₁ = zc r`, so `ω₁⁴ = 1`), hence
  `x₂ = (ω₁ · zc α)⁻¹` — the *inverse* of the good translate; so by H4b,
  `h(x₂) = t · h(ω₁ · zc α)⁻¹ · t`, and `h(ω₁ · zc α) ∈ fr.KW` is
  `StepB.hcan_mul_zcQF_alpha_mem_KW`;
* H4c (`h(f y) = h(y)⁻¹`) and H4a at the conjugating element `d₂` turn the cross relation
  `hd₂ : f(x₂) = kact fr d₂ (ωₖ · zc r)` into
  `h(ωₖ · zc r) = (t d₂ t) · h(x₂)⁻¹ · d₂⁻¹ ∈ fr.KW`;
* finally `ωₖ⁻¹ · zc r = (ωₖ · zc r)⁻¹`, so H4b plus the `t`-stability `htN` of `fr.KW`
  give the conclusion.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Omega.square_eq_shift_of_good_cover_hKW
import Submission.Work.PSU3.StageB.Omega.omegaHyp_of_sq
import Submission.Work.PSU3.StageB.StepB.hcan_mul_zcQF_alpha_mem_KW
import Submission.Work.PSU3.StageB.StepB.hcan_mul_zcQF_mem_KW_iff
import Submission.Work.PSU3.StageB.Canon

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB.StepB

theorem hcan_inv_mul_zcQF_mem_KW {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (htN : ∀ w : fr.KW, t * (w : G) * t ∈ fr.KW)
    (hWKW : Work.ThmF.W H t ≤ fr.KW)
    {ω₁ : ↥Q} (hω₁ : (ω₁ : G) ∉ fr.Q0) {α r : ↥(Work.PSU3.StageB.FX n)}
    (hω₁f : Work.PSU3.StageB.fcan hS.split ω₁ =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω₁ * Work.PSU3.StageB.zcQF fr α))
    (hsq : ω₁ * ω₁ = Work.PSU3.StageB.zcQF fr r)
    (hWω₁ : ((Work.PSU3.StageB.hcan hS.split ω₁ :
      ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ Work.ThmF.W H t)
    {ωₖ : ↥Q} (hωₖ : (ωₖ : G) ∉ fr.Q0) {d₂ : fr.KW}
    (hd₂ : Work.PSU3.StageB.fcan hS.split
        (ω₁ * (Work.PSU3.StageB.zcQF fr r * Work.PSU3.StageB.zcQF fr α)) =
      Work.PSU3.StageB.kact hS fr d₂ (ωₖ * Work.PSU3.StageB.zcQF fr r)) :
    ((Work.PSU3.StageB.hcan hS.split (ωₖ⁻¹ * Work.PSU3.StageB.zcQF fr r) :
      ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW := by
  -- ## Elementary facts about the two `Q₀`-translates involved
  have hzrQ0 : ((Work.PSU3.StageB.zcQF fr r : ↥Q) : G) ∈ fr.Q0 := by
    rw [Work.PSU3.StageB.zcQF_coe]; exact fr.zc_mem (Work.PSU3.StageB.fval r) r.2
  have hzαQ0 : ((Work.PSU3.StageB.zcQF fr α : ↥Q) : G) ∈ fr.Q0 := by
    rw [Work.PSU3.StageB.zcQF_coe]; exact fr.zc_mem (Work.PSU3.StageB.fval α) α.2
  have hzrαQ0 : ((Work.PSU3.StageB.zcQF fr r * Work.PSU3.StageB.zcQF fr α : ↥Q) : G) ∈ fr.Q0 :=
    (fr.Q0).mul_mem hzrQ0 hzαQ0
  -- non-identity of the three relevant elements
  have hwzα1 : (((ω₁ * Work.PSU3.StageB.zcQF fr α : ↥Q)) : G) ≠ 1 :=
    Work.PSU3.StageB.Omega.mul_Q0_ne_one fr hω₁ hzαQ0
  have hx₂1 : (((ω₁ * (Work.PSU3.StageB.zcQF fr r * Work.PSU3.StageB.zcQF fr α) : ↥Q)) : G) ≠ 1 :=
    Work.PSU3.StageB.Omega.mul_Q0_ne_one fr hω₁ hzrαQ0
  have hy1 : (((ωₖ * Work.PSU3.StageB.zcQF fr r : ↥Q)) : G) ≠ 1 :=
    Work.PSU3.StageB.Omega.mul_Q0_ne_one fr hωₖ hzrQ0
  -- ## Step 1: `h(ω₁ · zc α) ∈ fr.KW` (H4a/H4c, §2 (2))
  have hαKW : ((Work.PSU3.StageB.hcan hS.split
      (ω₁ * Work.PSU3.StageB.zcQF fr α) :
      ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW :=
    hcan_mul_zcQF_alpha_mem_KW hS fr hWKW hω₁ hω₁f hWω₁
  -- ## Step 2: `x₂ = ω₁ · (zc r · zc α)` is the inverse of `ω₁ · zc α`
  have hω₁inv : (ω₁⁻¹ : ↥Q) = ω₁ * Work.PSU3.StageB.zcQF fr r := by
    apply Subtype.ext
    rw [Subgroup.coe_inv, Subgroup.coe_mul]
    exact Work.PSU3.StageB.Omega.inv_eq_mul_zcQF_of_sq fr hsq
  have hx₂_eq : ω₁ * (Work.PSU3.StageB.zcQF fr r * Work.PSU3.StageB.zcQF fr α) =
      (ω₁ * Work.PSU3.StageB.zcQF fr α)⁻¹ := by
    rw [Work.PSU3.StageB.Omega.inv_mul_Q0' fr hzαQ0, hω₁inv, mul_assoc]
  -- ## Step 3: `h(x₂) ∈ fr.KW` (H4b at the good translate)
  have hx₂KW : ((Work.PSU3.StageB.hcan hS.split
      (ω₁ * (Work.PSU3.StageB.zcQF fr r * Work.PSU3.StageB.zcQF fr α)) :
      ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW := by
    rw [hx₂_eq, hcan_inv hS.split hwzα1]
    exact htN ⟨((Work.PSU3.StageB.hcan hS.split
      (ω₁ * Work.PSU3.StageB.zcQF fr α) : ↥(Submission.Blueprint.twoPoint H t)) : G)⁻¹,
      (fr.KW).inv_mem hαKW⟩
  -- ## Step 4: transport through `hd₂`: `h(ωₖ · zc r) ∈ fr.KW`
  -- H4a (conjugation by `d₂`) at `y = ωₖ · zc r`, with `d₂⁻¹ y d₂ = f(x₂)` by `hd₂`.
  obtain ⟨xa, hxa, -, -, hhxa⟩ :=
    canon_conj_fun hS.split hy1 (⟨(d₂ : G), fr.KW_le d₂.2⟩ : ↥(Submission.Blueprint.twoPoint H t))
  have hxa_eq : xa = Work.PSU3.StageB.fcan hS.split
      (ω₁ * (Work.PSU3.StageB.zcQF fr r * Work.PSU3.StageB.zcQF fr α)) := by
    apply Subtype.ext
    rw [hxa, hd₂, Work.PSU3.StageB.kact_coe]
  have hfy : (Work.PSU3.StageB.hcan hS.split (ωₖ * Work.PSU3.StageB.zcQF fr r) : G) =
      (t * (d₂ : G) * t) *
        ((Work.PSU3.StageB.hcan hS.split
          (ω₁ * (Work.PSU3.StageB.zcQF fr r * Work.PSU3.StageB.zcQF fr α)) :
          ↥(Submission.Blueprint.twoPoint H t)) : G)⁻¹ * (d₂ : G)⁻¹ := by
    have hstep : (Work.PSU3.StageB.hcan hS.split
        (Work.PSU3.StageB.fcan hS.split
          (ω₁ * (Work.PSU3.StageB.zcQF fr r * Work.PSU3.StageB.zcQF fr α))) : G) =
        ((Work.PSU3.StageB.hcan hS.split
          (ω₁ * (Work.PSU3.StageB.zcQF fr r * Work.PSU3.StageB.zcQF fr α)) :
          ↥(Submission.Blueprint.twoPoint H t)) : G)⁻¹ :=
      (fcan_fcan hS.split hx₂1).2.1
    rw [hxa_eq] at hhxa
    rw [hstep] at hhxa
    rw [hhxa]
    group
  have hyKW : (Work.PSU3.StageB.hcan hS.split (ωₖ * Work.PSU3.StageB.zcQF fr r) : G) ∈ fr.KW := by
    rw [hfy]
    exact (fr.KW).mul_mem ((fr.KW).mul_mem (htN d₂) ((fr.KW).inv_mem hx₂KW))
      ((fr.KW).inv_mem d₂.2)
  -- ## Step 5: `ωₖ⁻¹ · zc r = (ωₖ · zc r)⁻¹`, H4b and `htN` conclude.
  have hx₅_eq : ωₖ⁻¹ * Work.PSU3.StageB.zcQF fr r = (ωₖ * Work.PSU3.StageB.zcQF fr r)⁻¹ := by
    rw [Work.PSU3.StageB.Omega.inv_mul_Q0' fr hzrQ0]
  rw [hx₅_eq, hcan_inv hS.split hy1]
  exact htN ⟨((Work.PSU3.StageB.hcan hS.split
    (ωₖ * Work.PSU3.StageB.zcQF fr r) : ↥(Submission.Blueprint.twoPoint H t)) : G)⁻¹,
    (fr.KW).inv_mem hyKW⟩

end Work.PSU3.StageB.StepB
