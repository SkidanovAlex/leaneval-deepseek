import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.canonicalForm` — the canonical form of an element outside `H`

Peterfalvi II, Ch. V §1.  For a split rank-one datum `H = Q ⋊ D` (`D = H ∩ Hᵗ`,
`t` an involution outside `H`, `Q ⊴ H` with `Q ⊓ D = ⊥`, `Q ⊔ D = H`) every element
`z ∉ H` has a **unique** expression

  `z = a * t * q`,  `a ∈ H`, `q ∈ Q`.

Equivalently, the map `H × Q → G`, `(a,q) ↦ a t q`, is a bijection onto `G ∖ H`.

* Existence.  `G` acts 2-transitively on `Ω = G ⧸ H`, so the stabiliser `H` of the base
  point `pt H` is transitive on `Ω ∖ {pt H}`; applied to the pairs `(pt H, t·pt H)` and
  `(pt H, z·pt H)` (both consisting of distinct points, since `t, z ∉ H`) this produces
  `g ∈ H` with `z = g * t * h` for some `h ∈ H`.  Writing `h = d * q` with `d ∈ D`,
  `q ∈ Q` (`H = D · Q`, the normal factor `Q` moves across `D`) and using `t d t ∈ H`
  (`D` is `t`-stable) gives the required form with `a = g * (t * d * t)`.
* Uniqueness.  If `a t q = a' t q'` then `a'⁻¹ a = t u t⁻¹` with `u = q' q⁻¹ ∈ Q`, and
  `u = t⁻¹ (a'⁻¹ a) t ∈ Hᵗ`; hence `u ∈ Q ⊓ (H ⊓ Hᵗ) = ⊥`, so `q = q'` and `a = a'`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint

variable {G : Type*} [Group G] {H Q : Subgroup G} {t : G}

/-! ## Auxiliary facts about a split rank-one datum -/

/-- In a split rank-one datum, `t` is an involution. -/
private lemma data_mul_self_eq_one (h : IsSplitRankOneData G H Q t) : t * t = 1 := by
  have h2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.invol] at this
  simpa [pow_two] using h2

/-- In a split rank-one datum, `t⁻¹ = t`. -/
private lemma data_inv_eq_self (h : IsSplitRankOneData G H Q t) : t⁻¹ = t := by
  have h2 : t * t = 1 := data_mul_self_eq_one h
  calc t⁻¹ = (t * t) * t⁻¹ := by rw [h2, one_mul]
    _ = t := by rw [mul_assoc, mul_inv_cancel, mul_one]

/-- `Q` is normalised by `H`, elementwise form. -/
private lemma data_conj_mem (h : IsSplitRankOneData G H Q t) {g a : G} (hg : g ∈ H)
    (ha : a ∈ Q) : g * a * g⁻¹ ∈ Q :=
  ((Subgroup.mem_normalizer_iff.mp (h.normal hg)) a).mp ha

/-- Every element of `H = Q ⋊ D` is a product `q * d` with `q ∈ Q` and `d ∈ D`. -/
private lemma data_fact_exists (h : IsSplitRankOneData G H Q t) {a : G} (ha : a ∈ H) :
    ∃ q ∈ Q, ∃ d ∈ twoPoint H t, a = q * d := by
  have key : ∀ x ∈ Subgroup.closure ((Q : Set G) ∪ (twoPoint H t : Set G)),
      ∃ q ∈ Q, ∃ d ∈ twoPoint H t, x = q * d := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ =>
      ∃ q ∈ Q, ∃ d ∈ twoPoint H t, x = q * d) (fun y hy => ?_) ?_
      (fun u v _ _ ihu ihv => ?_) (fun u _ ihu => ?_) hx
    · rcases hy with hy | hy
      · exact ⟨y, hy, 1, Subgroup.one_mem _, (mul_one y).symm⟩
      · exact ⟨1, Subgroup.one_mem _, y, hy, (one_mul y).symm⟩
    · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, (mul_one 1).symm⟩
    · obtain ⟨q₁, hq₁, d₁, hd₁, rfl⟩ := ihu
      obtain ⟨q₂, hq₂, d₂, hd₂, rfl⟩ := ihv
      refine ⟨q₁ * (d₁ * q₂ * d₁⁻¹), Q.mul_mem hq₁
          (data_conj_mem h (Work.RankOneUniqueness.mem_twoPoint_iff.mp hd₁).1 hq₂), d₁ * d₂,
        (twoPoint H t).mul_mem hd₁ hd₂, ?_⟩
      group
    · obtain ⟨q₁, hq₁, d₁, hd₁, rfl⟩ := ihu
      refine ⟨d₁⁻¹ * q₁⁻¹ * (d₁⁻¹)⁻¹, data_conj_mem h
        (H.inv_mem (Work.RankOneUniqueness.mem_twoPoint_iff.mp hd₁).1) (Q.inv_mem hq₁), d₁⁻¹,
        (twoPoint H t).inv_mem hd₁, ?_⟩
      group
  exact key a (by rw [← Subgroup.sup_eq_closure, h.sup_eq]; exact ha)

/-- Every element of `H = D ⋅ Q`: the other order of the factorisation (`Q` is normal). -/
private lemma data_fact_exists' (h : IsSplitRankOneData G H Q t) {a : G} (ha : a ∈ H) :
    ∃ d ∈ twoPoint H t, ∃ q ∈ Q, a = d * q := by
  obtain ⟨q, hq, d, hd, hqd⟩ := data_fact_exists h ha
  have hmem : d⁻¹ * q * d ∈ Q := by
    have h' := data_conj_mem h (H.inv_mem (Work.RankOneUniqueness.twoPoint_le_left H t hd)) hq
    rwa [inv_inv] at h'
  refine ⟨d, hd, d⁻¹ * q * d, hmem, ?_⟩
  rw [hqd]
  group

/-- `t` conjugates the two-point stabiliser `D = H ⊓ Hᵗ` into `H` (via `t d t = dᵗ`). -/
private lemma data_twoPoint_conj_mem (h : IsSplitRankOneData G H Q t) {d : G}
    (hd : d ∈ twoPoint H t) : t * d * t ∈ H :=
  Work.RankOneUniqueness.t_mul_mul_t_mem_of_mem_twoPoint (data_mul_self_eq_one h) hd

/-- **Uniqueness of the canonical form** `a * t * q`, `a ∈ H`, `q ∈ Q` (Peterfalvi II
Ch. V §1). -/
private lemma data_canon_unique (h : IsSplitRankOneData G H Q t) {a a' q q' : G}
    (ha : a ∈ H) (ha' : a' ∈ H) (hq : q ∈ Q) (hq' : q' ∈ Q)
    (heq : a * t * q = a' * t * q') : a = a' ∧ q = q' := by
  have hinv : t⁻¹ = t := data_inv_eq_self h
  set u : G := q' * q⁻¹ with hu
  have huQ : u ∈ Q := Q.mul_mem hq' (Q.inv_mem hq)
  have h1 : a'⁻¹ * a * t * q = t * q' := by
    calc a'⁻¹ * a * t * q = a'⁻¹ * (a * t * q) := by group
      _ = a'⁻¹ * (a' * t * q') := by rw [heq]
      _ = t * q' := by group
  have h2 : a'⁻¹ * a * t = t * u := by
    calc a'⁻¹ * a * t = a'⁻¹ * a * t * q * q⁻¹ := by group
      _ = t * q' * q⁻¹ := by rw [h1]
      _ = t * u := by rw [hu]; group
  have hkey : a'⁻¹ * a = t * u * t⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * a * t * t⁻¹ := by group
      _ = t * u * t⁻¹ := by rw [h2]
  have huConj : u ∈ conj t H := by
    -- `u = t * (a'⁻¹ * a) * t`, and `a'⁻¹ * a ∈ H`
    have hut : u = t * (a'⁻¹ * a) * t := by
      rw [hkey]
      rw [show t * (t * u * t⁻¹) * t = (t * t) * u * (t⁻¹ * t) by group,
        data_mul_self_eq_one h, inv_mul_cancel, one_mul, mul_one]
    rw [Work.RankOneUniqueness.mem_conj_iff]
    exact ⟨a'⁻¹ * a, H.mul_mem (H.inv_mem ha') ha, by rw [hinv]; exact hut.symm⟩
  have hbot : u ∈ (⊥ : Subgroup G) := by
    have hmem : u ∈ Q ⊓ (H ⊓ conj t H) := ⟨huQ, h.le huQ, huConj⟩
    rwa [h.inf_eq] at hmem
  have hu1 : u = 1 := Subgroup.mem_bot.mp hbot
  have hqq : q = q' := by
    have hq1 : q' * q⁻¹ = 1 := by rw [← hu]; exact hu1
    exact (mul_inv_eq_one.mp hq1).symm
  have haa : a = a' := by
    have h4 : a'⁻¹ * a * t = t := by rw [h2, hu1, mul_one]
    have h5 : a'⁻¹ * a = 1 := by
      have h6 := congrArg (fun x => x * t⁻¹) h4
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using h6
    have h7 : a'⁻¹ * a = a'⁻¹ * a' := by rw [h5, inv_mul_cancel]
    exact mul_left_cancel h7
  exact ⟨haa, hqq⟩

/-- **Existence of the canonical form** (Peterfalvi II Ch. V §1): `2`-transitivity of
`G` on `G ⧸ H` puts every `z ∉ H` into the double coset `H t Q = H t H`. -/
private lemma data_canon_exists (h : IsSplitRankOneData G H Q t) {z : G} (hz : z ∉ H) :
    ∃ a ∈ H, ∃ q ∈ Q, a * t * q = z := by
  have hne1 : Work.RankOneUniqueness.pt H ≠ (t : G ⧸ H) := by
    simp only [Ne, eq_comm, Work.RankOneUniqueness.mk_eq_pt_iff]
    exact h.not_mem
  have hne2 : Work.RankOneUniqueness.pt H ≠ (z : G ⧸ H) := by
    simp only [Ne, eq_comm, Work.RankOneUniqueness.mk_eq_pt_iff]
    exact hz
  -- 2-transitivity: `(pt H, t pt H) ↦ (pt H, z pt H)`
  have h2t : ∀ {a b c d : G ⧸ H}, a ≠ b → c ≠ d →
      ∃ g : G, g • a = c ∧ g • b = d := MulAction.is_two_pretransitive_iff.mp h.twoTransitive
  obtain ⟨g, hg1, hg2⟩ := h2t hne1 hne2
  -- `g` fixes the base point, so `g ∈ H`
  have hgH : g ∈ H := Work.RankOneUniqueness.mem_of_smul_pt H hg1
  -- the second component: `(g * t) H = z H`, i.e. `(g * t)⁻¹ * z ∈ H`
  have heqQ : ((g * t : G) : G ⧸ H) = ((z : G) : G ⧸ H) := by
    rw [← Work.RankOneUniqueness.smul_mk H g t]
    exact hg2
  have hmem : (g * t)⁻¹ * z ∈ H := QuotientGroup.eq.mp heqQ
  -- factor `(g * t)⁻¹ * z = d * q`, `d ∈ D`, `q ∈ Q`
  obtain ⟨d, hd, q, hq, hdq⟩ := data_fact_exists' h hmem
  have hTdT : t * d * t ∈ H := data_twoPoint_conj_mem h hd
  refine ⟨g * (t * d * t), H.mul_mem hgH hTdT, q, hq, ?_⟩
  have hz' : z = (g * t) * (d * q) := by rw [← hdq]; group
  have htdt : t * d * t = t * d * t⁻¹ := by rw [data_inv_eq_self h]
  rw [hz', htdt]
  group

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem canonicalForm {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} (h : IsSplitRankOneData G H Q t) : ∀ z : G, z ∉ H → ∃! p : G × G, p.1 ∈ H ∧ p.2 ∈ Q ∧ p.1 * t * p.2 = z := by
  intro z hz
  obtain ⟨a, ha, q, hq, haq⟩ := data_canon_exists h hz
  refine ⟨(a, q), ⟨ha, hq, haq⟩, ?_⟩
  rintro ⟨a', q'⟩ ⟨ha', hq', ha'q'⟩
  have heq : a' * t * q' = a * t * q := by rw [ha'q', haq]
  obtain ⟨h1, h2⟩ := data_canon_unique h ha' ha hq' hq heq
  exact Prod.ext h1 h2

end Work.ThmF.ChV12
