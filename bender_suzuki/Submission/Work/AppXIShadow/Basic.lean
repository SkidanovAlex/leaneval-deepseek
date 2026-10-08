import Mathlib
import Submission.Work.AppXIShadow.Defs
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV12.lemma2a
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.ChV12.lemma2a_Q_regular
import Submission.Work.ThmF.ChV12.lemma2a_card_omega
import Submission.Work.ThmF.ChV12.lemma2a_factor_unique
import Submission.Work.ThmF.Prove.centDLowerCentralizerS
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive
import Submission.Work.DoubleTransitivity.App2.app2_7

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIShadow.Basic` — the elementary `CtxF` API and the `C_G(P)`-action on `fixP`

Notation of the standing context `CtxF H Q t s r P` (Peterfalvi II Ch. V §3):
`D = twoPoint H t`, `V = centD H t = C_D(t)`, `c.P_le : P ≤ V` with `|P|` prime,
`C_Q(P) = CQ Q P`, `Ker H Q P t = D ⊓ C_G(C_Q(P)) ⊓ C_G(P)`, `s` the distinguished involution
of `Q` relative to `t` (`t s t = r⁻¹ t r`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.AppXIShadow

open Work.ThmF.ChV3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}

section Ctx

/-- `P ≤ D = H ⊓ Hᵗ`. -/
theorem P_le_twoPoint (c : CtxF H Q t s r P) : P ≤ twoPoint H t := fun x hx => (Subgroup.mem_inf.mp (c.P_le hx)).1

/-- `P ≤ H`. -/
theorem P_le_H (c : CtxF H Q t s r P) : P ≤ H := le_trans (P_le_twoPoint c) inf_le_left

/-- `P ≤ Hᵗ`. -/
theorem P_le_conjH (c : CtxF H Q t s r P) : P ≤ conj t H := le_trans (P_le_twoPoint c) inf_le_right

/-- `P` centralises `t`. -/
theorem P_le_centralizer_t (c : CtxF H Q t s r P) : P ≤ Subgroup.centralizer ({t} : Set G) :=
  fun x hx => (Subgroup.mem_inf.mp (c.P_le hx)).2

/-- `t` is an involution. -/
theorem t_mul_t (c : CtxF H Q t s r P) : t * t = 1 := by
  rw [← pow_two, ← c.split.invol]; exact pow_orderOf_eq_one t

/-- `s` is an involution. -/
theorem s_mul_s (c : CtxF H Q t s r P) : s * s = 1 := by
  rw [← pow_two, ← c.s_inv]; exact pow_orderOf_eq_one s

/-- `t ∉ H`. -/
theorem t_not_mem_H (c : CtxF H Q t s r P) : t ∉ H := c.split.not_mem

/-- `s ≠ 1`. -/
theorem s_ne_one (c : CtxF H Q t s r P) : s ≠ 1 := by
  intro h
  have h2 := c.s_inv
  rw [h, orderOf_one] at h2
  omega

/-- `x ∈ P` fixes `t • ∞`. -/
theorem smul_t_eq_t (c : CtxF H Q t s r P) {x : G} (hx : x ∈ P) : x • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
  rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
  have hcomm : x * t = t * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (P_le_centralizer_t c hx)
  have h1 : (x * t)⁻¹ * t = x⁻¹ := by rw [hcomm]; group
  rw [h1]
  exact H.inv_mem (P_le_H c hx)

/-- The base point `∞ = H` is fixed by `P`. -/
theorem one_mem_fixP (c : CtxF H Q t s r P) : ((1 : G) : G ⧸ H) ∈ fixP H P := by
  intro x hx
  rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
  simpa using P_le_H c hx

/-- `t • ∞` is fixed by `P`. -/
theorem t_mem_fixP (c : CtxF H Q t s r P) : ((t : G) : G ⧸ H) ∈ fixP H P := fun x hx => smul_t_eq_t c hx

/-- `s ∈ C_Q(P)`. -/
theorem s_mem_CQ (c : CtxF H Q t s r P) : s ∈ CQ Q P := by
  refine ⟨c.s_mem, ?_⟩
  show s ∈ Subgroup.centralizer (P : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hV : x ∈ centD H t := c.P_le hx
  have h1 : x ∈ Subgroup.centralizer ({s} : Set G) :=
    Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid hV
  exact Subgroup.mem_centralizer_singleton_iff.mp h1

/-- `C_Q(P) ≤ H`. -/
theorem CQ_le_H (c : CtxF H Q t s r P) : CQ Q P ≤ H := le_trans inf_le_left c.split.le

/-- `C_Q(P) ≤ C_G(P)`. -/
theorem CQ_le_CGP (c : CtxF H Q t s r P) : CQ Q P ≤ Subgroup.centralizer (P : Set G) := inf_le_right

/-- `Ker ≤ D`. -/
theorem Ker_le_twoPoint (c : CtxF H Q t s r P) : Ker H Q P t ≤ twoPoint H t := le_trans inf_le_left inf_le_left

/-- `Ker ≤ C_G(C_Q(P))`. -/
theorem Ker_le_centralizer_CQ (c : CtxF H Q t s r P) :
    Ker H Q P t ≤ Subgroup.centralizer ((CQ Q P : Subgroup G) : Set G) :=
  le_trans inf_le_left inf_le_right

/-- `Ker ≤ C_G(P)`. -/
theorem Ker_le_CGP (c : CtxF H Q t s r P) : Ker H Q P t ≤ Subgroup.centralizer (P : Set G) := inf_le_right

/-- `D = twoPoint H t` has odd order. -/
theorem odd_card_twoPoint (c : CtxF H Q t s r P) : Odd (Nat.card ↥(twoPoint H t)) :=
  c.split.stronglyEmbedded.2.2 t c.split.not_mem

/-- `Ker` has odd order. -/
theorem odd_card_Ker (c : CtxF H Q t s r P) : Odd (Nat.card ↥(Ker H Q P t)) :=
  Odd.of_dvd_nat (odd_card_twoPoint c) (Subgroup.card_dvd_of_le (Ker_le_twoPoint c))

end Ctx

section Action

variable (H P : Subgroup G)

/-- The conjugation action of `C_G(P)` on `G ⧸ H` preserves the set `fixP H P` of fixed points
of `P`. -/
theorem smul_mem_fixP {g : G} (hg : g ∈ Subgroup.centralizer (P : Set G)) {ω : G ⧸ H}
    (hω : ω ∈ fixP H P) : g • ω ∈ fixP H P := by
  intro x hx
  have hmem : g⁻¹ * x * g ∈ P := by
    have hcomm : g * x = x * g := (Subgroup.mem_centralizer_iff.mp hg x hx).symm
    have h1 : x = g⁻¹ * x * g := by
      calc x = g⁻¹ * (g * x) := by group
        _ = g⁻¹ * (x * g) := by rw [hcomm]
        _ = g⁻¹ * x * g := by group
    rw [← h1]; exact hx
  calc x • (g • ω) = (x * g) • ω := by rw [mul_smul]
    _ = (g * (g⁻¹ * x * g)) • ω := by rw [show x * g = g * (g⁻¹ * x * g) from by group]
    _ = g • ((g⁻¹ * x * g) • ω) := by rw [mul_smul]
    _ = g • ω := by rw [hω _ hmem]

/-- The action of `C_G(P)` on the set `fixP H P` of fixed points of `P`. -/
instance instMulActionFixP : MulAction ↥(Subgroup.centralizer (P : Set G)) ↥(fixP H P) where
  smul g ω := ⟨(g : G) • (ω : G ⧸ H), smul_mem_fixP H P g.2 ω.2⟩
  one_smul ω := Subtype.ext (one_smul _ _)
  mul_smul a b ω := Subtype.ext (mul_smul _ _ _)

@[simp]
theorem fixP_smul_coe {g : ↥(Subgroup.centralizer (P : Set G))} {ω : ↥(fixP H P)} :
    (((g • ω : ↥(fixP H P)) : G ⧸ H)) = (g : G) • (ω : G ⧸ H) := rfl

/-- The base point `∞ = H` of `fixP H P`, as an element of the `C_G(P)`-set. -/
def fixPBase (hPH : P ≤ H) : ↥(fixP H P) :=
  ⟨((1 : G) : G ⧸ H), fun x hx => by
    rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
    simpa using hPH hx⟩

@[simp]
theorem fixPBase_coe (hPH : P ≤ H) :
    ((fixPBase H P hPH : ↥(fixP H P)) : G ⧸ H) = ((1 : G) : G ⧸ H) := rfl

/-- The stabiliser of the base point in `C_G(P)` is `C_G(P) ⊓ H`. -/
theorem stabilizer_fixPBase (hPH : P ≤ H) :
    MulAction.stabilizer ↥(Subgroup.centralizer (P : Set G)) (fixPBase H P hPH)
      = (Subgroup.centralizer (P : Set G) ⊓ H).subgroupOf
          (Subgroup.centralizer (P : Set G)) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨g.2, ?_⟩
    have h1 : (g : G) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      have h2 := congrArg Subtype.val h
      rw [fixP_smul_coe, fixPBase_coe] at h2
      exact h2
    rw [Work.ThreePoints.smul_mk, QuotientGroup.eq] at h1
    simpa using H.inv_mem h1
  · rintro ⟨-, hgH⟩
    refine Subtype.ext ?_
    rw [fixP_smul_coe, fixPBase_coe]
    show (g : G) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
    simpa using hgH

end Action

section Abbrev

variable {H Q : Subgroup G} {t s r : G} {P : Subgroup G}

/-- `C_G(P)`, the group acting on `fixP H P`. -/
abbrev centP (P : Subgroup G) : Subgroup G := Subgroup.centralizer (P : Set G)

/-- The kernel `Ker H Q P t` of step (2), as a subgroup of `C_G(P)`. -/
abbrev KerIn (H Q P : Subgroup G) (t : G) : Subgroup ↥(centP P) :=
  (Ker H Q P t).subgroupOf (centP P)

/-- The base point `∞` of the `C_G(P)`-set `fixP H P`. -/
abbrev fixPBaseC (c : CtxF H Q t s r P) : ↥(fixP H P) := fixPBase H P (P_le_H c)

/-- The stabiliser of the base point in `C_G(P)`, i.e. `C_H(P)`. -/
abbrev fixPStab (c : CtxF H Q t s r P) : Subgroup ↥(centP P) :=
  MulAction.stabilizer ↥(centP P) (fixPBaseC c)

theorem fixPStab_eq (c : CtxF H Q t s r P) : fixPStab c = (centP P ⊓ H).subgroupOf (centP P) :=
  stabilizer_fixPBase H P (P_le_H c)

/-- `t ∈ C_G(P)`. -/
theorem t_mem_centP (c : CtxF H Q t s r P) : t ∈ centP P := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (P_le_centralizer_t c hx)

/-- `s ∈ C_G(P)`. -/
theorem s_mem_centP (c : CtxF H Q t s r P) : s ∈ centP P := CQ_le_CGP c (s_mem_CQ c)

/-- The element `st ∈ C_G(P)`, the one whose order is `f = o(st)` in App. XI Prop. 1. -/
abbrev sMulT (c : CtxF H Q t s r P) : ↥(centP P) :=
  ⟨s * t, Subgroup.mul_mem _ (s_mem_centP c) (t_mem_centP c)⟩

@[simp]
theorem sMulT_coe (c : CtxF H Q t s r P) : ((sMulT c : ↥(centP P)) : G) = s * t := rfl

end Abbrev

end Work.AppXIShadow
