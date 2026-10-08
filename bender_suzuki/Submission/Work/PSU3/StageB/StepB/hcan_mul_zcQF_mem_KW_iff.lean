/-
# `Work.PSU3.StageB.StepB.hcan_mul_zcQF_mem_KW_iff`

Peterfalvi II Ch. VII §2 (18): for a *good* element `ω ∈ Q ∖ Q₀` (i.e.
`f(ω) = ζ⁻¹ (ω · zc α) ζ`) whose `h`-component already lies in `W ≤ fr.KW`, the
`h`-components of the two translates of `ω` by the `Q₀`-elements `zc u` and `zc (α + u⁻¹)`
are either both in `fr.KW` or both outside it.

The point is that the §2 (18) recursion `Omega.hcan_mul_zcQF_rec`,

  `h(ω · zc u) = h(ω) · ζ⁻¹ · h(ω · zc (α + u⁻¹)) · ζ · (kElF (τ u))²`,

expresses `h(ω · zc u)` as `h(ω · zc (α + u⁻¹))` multiplied on the left and on the right by
elements of the subgroup `fr.KW` (namely `h(ω)·ζ⁻¹` — using `h(ω) ∈ W ≤ fr.KW` and
`ζ ∈ fr.KW` — and `ζ·(kElF (τ u))²`).  Since a subgroup is closed under left and right
translation by its own elements, membership in `fr.KW` agrees for the two arguments.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.hcan_pow_m_eq_one
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.Frame

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.StepB

theorem hcan_mul_zcQF_mem_KW_iff {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hWKW : Work.ThmF.W H t ≤ fr.KW)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω * Work.PSU3.StageB.zcQF fr α))
    (hWω : ((Work.PSU3.StageB.hcan hS.split ω : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈
      Work.ThmF.W H t)
    {U : ↥(Work.PSU3.StageB.FX n)} {v : Work.PSU3.E n} (hv : σE v = v)
    (huv : v = Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval U)⁻¹) :
    (((Work.PSU3.StageB.hcan hS.split (ω * Work.PSU3.StageB.zcQF fr U) :
        ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) ↔
      (((Work.PSU3.StageB.hcan hS.split (ω * Work.PSU3.StageB.zcQ fr v hv) :
        ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW) := by
  -- §2 (18): the recursion relating the `h`-components of `ω · zc u` and `ω · zc (α + u⁻¹)`.
  have hrec := Work.PSU3.StageB.Omega.hcan_mul_zcQF_rec hS fr hω hωf hv huv
  -- the two `fr.KW`-factors of the recursion
  set k2 : fr.KW := (Work.PSU3.StageB.kElF fr (Work.PSU3.StageB.tau hS fr U)) ^ 2 with hk2
  set A : G := (Work.PSU3.StageB.hcan hS.split ω : G) * (fr.ζ : G)⁻¹ with hA
  set B : G := (fr.ζ : G) * (k2 : G) with hB
  have hAmem : A ∈ fr.KW := by
    rw [hA]; exact (fr.KW).mul_mem (hWKW hWω) ((fr.KW).inv_mem fr.ζ.2)
  have hBmem : B ∈ fr.KW := by
    rw [hB]; exact (fr.KW).mul_mem fr.ζ.2 k2.2
  -- the recursion, with the two factors packaged
  have hrec' : (Work.PSU3.StageB.hcan hS.split (ω * Work.PSU3.StageB.zcQF fr U) : G) =
      A * (Work.PSU3.StageB.hcan hS.split (ω * Work.PSU3.StageB.zcQ fr v hv) : G) * B := by
    rw [hrec, hA, hB, hk2]; group
  constructor
  · -- `h(ω · zc u) ∈ KW` implies `h(ω · zc (α + u⁻¹)) = A⁻¹ · h(ω · zc u) · B⁻¹ ∈ KW`
    intro h1
    have key : (Work.PSU3.StageB.hcan hS.split (ω * Work.PSU3.StageB.zcQ fr v hv) : G) =
        A⁻¹ * (Work.PSU3.StageB.hcan hS.split (ω * Work.PSU3.StageB.zcQF fr U) : G) * B⁻¹ := by
      rw [hrec']; group
    rw [key]
    exact (fr.KW).mul_mem ((fr.KW).mul_mem ((fr.KW).inv_mem hAmem) h1) ((fr.KW).inv_mem hBmem)
  · -- conversely `h(ω · zc u) = A · h(ω · zc (α + u⁻¹)) · B ∈ KW`
    intro h2
    rw [hrec']
    exact (fr.KW).mul_mem ((fr.KW).mul_mem hAmem h2) hBmem

end Work.PSU3.StageB.StepB
