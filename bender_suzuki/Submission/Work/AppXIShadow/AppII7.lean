import Mathlib
import Submission.Work.AppXIShadow.Defs
import Submission.Work.AppXIShadow.Basic
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIShadow.AppII7` — App. II (7): `C_Q(P)` is regular on `fixP H P` and the kernel of
`C_G(P)`

A1 (`CQ_regular_on_fixP`) and A2 (`fixP_kernel_iff`) of the design file
`_design17/ThmF17_AppXI.lean` (BS pass 17, round 2), copied **verbatim** — the design file
carries complete proofs for both.

* A1: the fixed points of `P` on `Ω = G ⧸ H` are `∞ = H` together with the `C_Q(P)`-translates
  of `t • ∞`; the map `y ↦ y • (t • ∞)` is a bijection `C_Q(P) → fixP H P ∖ {∞}`.
* A2: for `g ∈ C_G(P)`, `g` fixes `fixP H P` pointwise iff `g ∈ Ker H Q P t`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.AppXIShadow

open Work.ThmF.ChV3 Work.ThmF
open Work.ZassenhausTwoGroup.IsTIQ

/-- **A1** (App. II (7)). -/
theorem CQ_regular_on_fixP {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : CtxF H Q t s r P) :
    ((t : G ⧸ H) ∈ fixP H P) ∧
    ∀ ω ∈ fixP H P, ω ≠ ((1 : G) : G ⧸ H) →
      ∃! y : ↥(CQ Q P), (y : G) • ((t : G) : G ⧸ H) = ω := by
  have hsplit := c.split
  have hPD : P ≤ twoPoint H t := c.P_le.trans inf_le_left
  have htfix : (t : G ⧸ H) ∈ fixP H P := fun x hx =>
    ((mem_twoPoint_iff_smul H t x).mp (hPD hx)).2
  have ht : (t : G ⧸ H) ≠ basePt H := (basePt_ne_iff H t).mpr hsplit.not_mem
  refine ⟨htfix, ?_⟩
  intro ω hω hω1
  -- existence: `ω = q • (t • ∞)` with `q ∈ Q`
  obtain ⟨g, hgH, hg⟩ := h_transitive hsplit (t : G ⧸ H) ω ht hω1
  obtain ⟨q, hqQ, e, heD, hqe⟩ := Work.RankOneUniqueness.fact_exists hsplit hgH
  have he : e • (t : G ⧸ H) = (t : G ⧸ H) := ((mem_twoPoint_iff_smul H t e).mp heD).2
  have hq : q • (t : G ⧸ H) = ω := by
    rw [← he, ← mul_smul, ← hqe, hg]
  -- `q` centralises `P`
  have hqP : q ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxH : x ∈ H := (hPD hx).1
    have hxt : x⁻¹ • (t : G ⧸ H) = (t : G ⧸ H) := by
      have := htfix x hx
      calc x⁻¹ • (t : G ⧸ H) = x⁻¹ • (x • (t : G ⧸ H)) := by rw [this]
        _ = (t : G ⧸ H) := inv_smul_smul x _
    have hmem : x * q * x⁻¹ ∈ Q := Work.RankOneUniqueness.conj_mem_of_mem hsplit hxH hqQ
    have hfix : ((x * q * x⁻¹)⁻¹ * q) • (t : G ⧸ H) = (t : G ⧸ H) := by
      have h1 : (x * q * x⁻¹) • (t : G ⧸ H) = q • (t : G ⧸ H) := by
        rw [mul_smul, mul_smul, hxt, hq, hω x hx]
      rw [mul_smul, ← h1, inv_smul_smul]
    have hone := Q_smul_eq_self hsplit (Q.mul_mem (Q.inv_mem hmem) hqQ) hfix ht
    have hxq : x * q * x⁻¹ = q := inv_mul_eq_one.mp hone
    calc x * q = x * q * x⁻¹ * x := by group
      _ = q * x := by rw [hxq]
  refine ⟨⟨q, hqQ, hqP⟩, hq, ?_⟩
  -- uniqueness: `Q` is regular on `Ω ∖ {∞}`
  rintro ⟨y, hyQ, hyP⟩ hy
  apply Subtype.ext
  show y = q
  have hfix : (q⁻¹ * y) • (t : G ⧸ H) = (t : G ⧸ H) := by
    rw [mul_smul, hy, ← hq, inv_smul_smul]
  have h1 := Q_smul_eq_self hsplit (Q.mul_mem (Q.inv_mem hqQ) hyQ) hfix ht
  calc y = q * (q⁻¹ * y) := by group
    _ = q := by rw [h1, mul_one]

/-- **A2**: an element of `C_G(P)` fixes `Ω_P` pointwise iff it lies in `Ker H Q P t`. -/
theorem fixP_kernel_iff {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : CtxF H Q t s r P) {g : G}
    (hg : g ∈ Subgroup.centralizer (P : Set G)) :
    (∀ ω ∈ fixP H P, g • ω = ω) ↔ g ∈ Ker H Q P t := by
  have hsplit := c.split
  obtain ⟨htfix, hreg⟩ := CQ_regular_on_fixP c
  have ht : (t : G ⧸ H) ≠ basePt H := (basePt_ne_iff H t).mpr hsplit.not_mem
  have hPD : P ≤ twoPoint H t := c.P_le.trans inf_le_left
  have hinf : basePt H ∈ fixP H P := fun x hx =>
    (Work.RankOneUniqueness.smul_pt_iff H x).mpr (hPD hx).1
  -- `y • (t • ∞) ∈ Ω_P` for `y ∈ C_Q(P)`
  have hyfix : ∀ y ∈ CQ Q P, y • (t : G ⧸ H) ∈ fixP H P := by
    intro y hy x hx
    have hyx : x * y = y * x := Subgroup.mem_centralizer_iff.mp hy.2 x hx
    rw [← mul_smul, hyx, mul_smul, htfix x hx]
  constructor
  · intro hall
    have hgH : g ∈ H := (Work.RankOneUniqueness.smul_pt_iff H g).mp (hall _ hinf)
    have hgD : g ∈ twoPoint H t := (mem_twoPoint_iff_smul H t g).mpr ⟨hgH, hall _ htfix⟩
    refine ⟨⟨hgD, ?_⟩, hg⟩
    show g ∈ Subgroup.centralizer ((CQ Q P : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hmemQ : g * y * g⁻¹ ∈ Q := Work.RankOneUniqueness.conj_mem_of_mem hsplit hgH hy.1
    have hfix : ((g * y * g⁻¹)⁻¹ * y) • (t : G ⧸ H) = (t : G ⧸ H) := by
      have hgt : g⁻¹ • (t : G ⧸ H) = (t : G ⧸ H) := by
        calc g⁻¹ • (t : G ⧸ H) = g⁻¹ • (g • (t : G ⧸ H)) := by rw [hall _ htfix]
          _ = (t : G ⧸ H) := inv_smul_smul g _
      have h1 : (g * y * g⁻¹) • (t : G ⧸ H) = y • (t : G ⧸ H) := by
        rw [mul_smul, mul_smul, hgt, hall _ (hyfix y hy)]
      rw [mul_smul, ← h1, inv_smul_smul]
    have hone := Q_smul_eq_self hsplit (Q.mul_mem (Q.inv_mem hmemQ) hy.1) hfix ht
    have hgy : g * y * g⁻¹ = y := inv_mul_eq_one.mp hone
    calc y * g = g * y * g⁻¹ * g := by rw [hgy]
      _ = g * y := by group
  · rintro ⟨⟨hgD, hgC⟩, -⟩ ω hω
    by_cases hω1 : ω = basePt H
    · rw [hω1]; exact (Work.RankOneUniqueness.smul_pt_iff H g).mpr hgD.1
    obtain ⟨⟨y, hy⟩, hyω, -⟩ := hreg ω hω hω1
    have hgt : g • (t : G ⧸ H) = (t : G ⧸ H) := ((mem_twoPoint_iff_smul H t g).mp hgD).2
    have hyg : y * g = g * y := Subgroup.mem_centralizer_iff.mp hgC y hy
    rw [← hyω, ← mul_smul, ← hyg, mul_smul, hgt]

end Work.AppXIShadow
