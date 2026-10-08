import Mathlib
import Submission.Work.AppXIShadow.AppII7
import Submission.Work.ThreePoints.P3Sub.twoTransitive_of_regular

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIShadow.CGP_twoTransitive` — `C_G(P)` acts 2-transitively on `Ω_P = fixP H P`

Peterfalvi II Ch. V §3 step (2) (second half), i.e. Appendix XI Prop. 1's transitivity input:
in the standing context `CtxF H Q t s r P`, the centraliser `C_G(P)` acts 2-transitively on the
set `fixedPts H P = fixP H P` of fixed points of `P` on `Ω = G ⧸ H`.

This is a purely formal consequence of A1 (`Work.AppXIShadow.CQ_regular_on_fixP`): `C_Q(P)` is
sharply transitive on `fixP H P ∖ {∞}` (and `C_Q(P) ≤ C_G(P)` fixes `∞`), while `C_G(P)`
contains `t`, which moves `∞` to the distinguished point `t • ∞`.  The assembly is

`Work.ThreePoints.P3Sub.twoTransitive_of_regular` with `F = C_G(P)`, `Z = C_Q(P)`,
`S = fixedPts H P`, `a = ∞ = 1 • H`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.AppXIShadow

open Work.ThmF.ChV3

/-- `t • ∞ = t • H` is the distinguished point `t • basePt`. -/
theorem t_smul_base_eq {G : Type} [Group G] {H : Subgroup G} {t : G} :
    t • (((1 : G) : G ⧸ H)) = ((t : G) : G ⧸ H) := by
  rw [Work.ThreePoints.smul_mk, mul_one]

/-- `C_Q(P) ≤ stabilizer_G ∞`, since `C_Q(P) ≤ H`. -/
theorem CQ_le_stabilizer_base {G : Type} [Group G] [Finite G] {H Q P : Subgroup G} {t s r : G}
    (c : CtxF H Q t s r P) :
    CQ Q P ≤ MulAction.stabilizer G (((1 : G) : G ⧸ H)) := by
  intro z hz
  rw [MulAction.mem_stabilizer_iff, Work.ThreePoints.smul_mk, QuotientGroup.eq]
  simpa using CQ_le_H c hz

/-- `C_Q(P)` is transitive on `fixP H P ∖ {∞}`: this is the content of A1. -/
theorem CQ_transitive_on_fixP_remove_base {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s r : G} {P : Subgroup G} (c : CtxF H Q t s r P) {c' : G ⧸ H}
    (hc' : c' ∈ fixP H P) (hc'ne : c' ≠ ((1 : G) : G ⧸ H)) {d : G ⧸ H}
    (hd : d ∈ fixP H P) (hdne : d ≠ ((1 : G) : G ⧸ H)) :
    ∃ z ∈ CQ Q P, z • c' = d := by
  obtain ⟨htfix, hreg⟩ := CQ_regular_on_fixP c
  obtain ⟨y, hy, -⟩ := hreg c' hc' hc'ne
  obtain ⟨y', hy', -⟩ := hreg d hd hdne
  refine ⟨(y' : G) * (y : G)⁻¹,
    Subgroup.mul_mem (CQ Q P) y'.2 (Subgroup.inv_mem (CQ Q P) y.2), ?_⟩
  show ((y' : G) * (y : G)⁻¹) • c' = d
  rw [← hy, mul_smul, inv_smul_smul, hy']

/-- `C_G(P)` is transitive on `fixP H P`: every fixed point of `P` is either `∞ = H` or
`y • (t • ∞)` for some `y ∈ C_Q(P)`, and `(y * t) • ∞ = y • (t • ∞)`. -/
theorem centP_transitive_on_fixP {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s r : G} {P : Subgroup G} (c : CtxF H Q t s r P) {x : G ⧸ H} (hx : x ∈ fixP H P) :
    ∃ f ∈ Subgroup.centralizer (P : Set G), f • (((1 : G) : G ⧸ H)) = x := by
  by_cases hx1 : x = (((1 : G) : G ⧸ H))
  · exact ⟨1, Subgroup.one_mem _, by rw [hx1, one_smul]⟩
  · obtain ⟨htfix, hreg⟩ := CQ_regular_on_fixP c
    obtain ⟨y, hy, -⟩ := hreg x hx hx1
    refine ⟨(y : G) * t,
      Subgroup.mul_mem _ (CQ_le_CGP c y.2) (t_mem_centP c), ?_⟩
    show (((y : G) * t)) • (((1 : G) : G ⧸ H)) = x
    rw [mul_smul, t_smul_base_eq, hy]

/-- **Peterfalvi II Ch. V §3 step (2), second half.**  In the standing context
`CtxF H Q t s r P`, the group `C_G(P)` acts 2-transitively on `fixP H P = fixedPts H P`. -/
theorem CGP_twoTransitive {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.centralizer (P : Set G))
      (Submission.Blueprint.fixedPts H P) :=
  Work.ThreePoints.P3Sub.twoTransitive_of_regular
    (F := Subgroup.centralizer (P : Set G)) (Z := CQ Q P) (S := fixedPts H P)
    (a := ((1 : G) : G ⧸ H)) (one_mem_fixP c)
    (fun f hf x hx => smul_mem_fixP H P hf hx)
    (CQ_le_CGP c) (CQ_le_stabilizer_base c)
    (fun _ hc hcne _ hd hdne => CQ_transitive_on_fixP_remove_base c hc hcne hd hdne)
    (fun _ hx => centP_transitive_on_fixP c hx)

end Work.AppXIShadow
