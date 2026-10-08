import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.isTI_Q`

In the split rank-one situation of Peterfalvi II, Ch. VII §1 (`H = Q ⋊ D` with
`D = H ∩ Hᵗ = twoPoint H t`, `t ∉ H` an involution, `G` 2-transitive on `G ⧸ H`), the
subgroup `Q` is **TI**: `Q ∩ Qˣ = ⊥` for every `x ∉ H`.  The Zassenhaus hypothesis of the
area statement is not needed for this: in a split BN-pair of rank one the subgroup `Q` acts
regularly — hence freely — on the complement of the base point of `G ⧸ H`.

The proof is the classical geometric one.  Let `Ω = G ⧸ H` and `∞ = H`.

* `G` is 2-transitive on `Ω`, so the point stabiliser `H` is transitive on `Ω ∖ {∞}`
  (`h_transitive`).
* `D = H ∩ Hᵗ` is exactly the stabiliser in `H` of the second point `t • ∞`
  (`mem_twoPoint_iff_smul`), and `Q ⊓ D = ⊥` (`IsSplitRankOne.inf_eq`).  Hence a
  non-identity `q ∈ Q` fixes **no** point of `Ω ∖ {∞}` (`Q_smul_eq_self`): if `q • ω = ω` with
  `ω ≠ ∞`, pick `g ∈ H` with `g • ω = t • ∞`; then `g q g⁻¹ ∈ Q` (since `H ≤ N(Q)`) fixes
  `t • ∞`, so `g q g⁻¹ ∈ Q ⊓ D = 1`, forcing `q = 1`.
* Finally, if `1 ≠ y ∈ Q ⊓ Qˣ`, write `y = x q x⁻¹` with `q ∈ Q`.  Then `y` fixes the point
  `x • ∞`, which is different from `∞` because `x ∉ H`; this contradicts the previous point.

Nothing here needs finiteness.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

namespace IsTIQ

variable {G : Type*} [Group G]

/-! ## The permutation action on `Ω = G ⧸ H` -/

/-- The base point `∞ = H` of `Ω = G ⧸ H`, for the left action of `G`. -/
abbrev basePt (H : Subgroup G) : G ⧸ H := ((1 : G) : G ⧸ H)

/-- `g • ∞` is the coset `gH`. -/
lemma smul_basePt (H : Subgroup G) (g : G) : g • basePt H = (g : G ⧸ H) := by
  rw [basePt, MulAction.Quotient.smul_coe]
  show (((g * 1 : G)) : G ⧸ H) = (g : G ⧸ H)
  rw [mul_one]

/-- `∞` is fixed exactly by `H`. -/
lemma smul_basePt_eq_iff (H : Subgroup G) (g : G) : g • basePt H = basePt H ↔ g ∈ H := by
  rw [basePt, MulAction.Quotient.smul_coe]
  show (((g * 1 : G)) : G ⧸ H) = (((1 : G)) : G ⧸ H) ↔ g ∈ H
  rw [mul_one, QuotientGroup.eq]
  simp

/-- An element of `H` fixes the base point. -/
lemma smul_basePt_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) : g • basePt H = basePt H :=
  (smul_basePt_eq_iff H g).mpr hg

/-- `gH ≠ ∞` iff `g ∉ H`. -/
lemma basePt_ne_iff (H : Subgroup G) (g : G) : (g : G ⧸ H) ≠ basePt H ↔ g ∉ H := by
  rw [← smul_basePt H g, not_iff_not, smul_basePt_eq_iff]

/-- `d ∈ Hᵗ` iff `t⁻¹ d t ∈ H`. -/
lemma mem_conj_iff_inv (H : Subgroup G) (t d : G) : d ∈ conj t H ↔ t⁻¹ * d * t ∈ H := by
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [show (MulEquiv.toMonoidHom (MulAut.conj t)) e = t * e * t⁻¹ from
      MulAut.conj_apply t e]
    convert he using 1
    group
  · intro hd
    refine ⟨t⁻¹ * d * t, hd, ?_⟩
    rw [show (MulEquiv.toMonoidHom (MulAut.conj t)) (t⁻¹ * d * t)
        = t * (t⁻¹ * d * t) * t⁻¹ from MulAut.conj_apply t _]
    group

/-- The two-point stabiliser `D = H ⊓ Hᵗ` is the set of `d ∈ H` fixing the point `t • ∞`. -/
lemma mem_twoPoint_iff_smul (H : Subgroup G) (t d : G) :
    d ∈ twoPoint H t ↔ d ∈ H ∧ d • (t : G ⧸ H) = (t : G ⧸ H) := by
  have hd : d • (t : G ⧸ H) = ((d * t : G) : G ⧸ H) := by
    rw [← smul_basePt H t, ← mul_smul, smul_basePt H (d * t)]
  have ht : (t : G ⧸ H) = ((t * 1 : G) : G ⧸ H) := by rw [mul_one]
  rw [hd, ht, QuotientGroup.eq]
  simp only [mul_one]
  rw [show (d * t)⁻¹ * t = (t⁻¹ * d * t)⁻¹ by group]
  rw [twoPoint, Subgroup.mem_inf, mem_conj_iff_inv]
  constructor
  · rintro ⟨hdH, hdt⟩
    exact ⟨hdH, H.inv_mem_iff.mpr hdt⟩
  · rintro ⟨hdH, hdt⟩
    exact ⟨hdH, H.inv_mem_iff.mp hdt⟩

/-- In the split rank-one situation the stabiliser `H` of `∞` is transitive on `Ω ∖ {∞}`:
this is 2-transitivity of `G` on `Ω = G ⧸ H`. -/
lemma h_transitive {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) :
    ∀ ω₁ ω₂ : G ⧸ H, ω₁ ≠ basePt H → ω₂ ≠ basePt H → ∃ g ∈ H, g • ω₁ = ω₂ := by
  intro ω₁ ω₂ h1 h2
  have h2t : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := h.twoTransitive
  rw [MulAction.is_two_pretransitive_iff] at h2t
  obtain ⟨g, hg1, hg2⟩ := h2t (show basePt H ≠ ω₁ from fun hc => h1 hc.symm)
    (show basePt H ≠ ω₂ from fun hc => h2 hc.symm)
  exact ⟨g, (smul_basePt_eq_iff H g).mp hg1, hg2⟩

/-- A non-identity element of `Q` fixes no point of `Ω ∖ {∞}`: `Q` acts freely there. -/
lemma Q_smul_eq_self {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t)
    {q : G} (hq : q ∈ Q) {ω : G ⧸ H} (hfix : q • ω = ω) (hω : ω ≠ basePt H) :
    q = 1 := by
  by_contra hq1
  have ht : (t : G ⧸ H) ≠ basePt H := (basePt_ne_iff H t).mpr h.not_mem
  obtain ⟨g, hgH, hg⟩ := h_transitive h ω (t : G ⧸ H) hω ht
  have hdQ : g * q * g⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (h.normal hgH) q).mp hq
  have hdH : g * q * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hgH (h.le hq)) (H.inv_mem hgH)
  have hdsmul : (g * q * g⁻¹) • (t : G ⧸ H) = (t : G ⧸ H) := by
    calc (g * q * g⁻¹) • (t : G ⧸ H)
        = (g * q * g⁻¹) • (g • ω) := by rw [hg]
      _ = ((g * q * g⁻¹) * g) • ω := by rw [← mul_smul]
      _ = (g * q) • ω := by rw [show (g * q * g⁻¹) * g = g * q by group]
      _ = g • (q • ω) := by rw [mul_smul]
      _ = g • ω := by rw [hfix]
      _ = (t : G ⧸ H) := hg
  have hmem : g * q * g⁻¹ ∈ twoPoint H t :=
    (mem_twoPoint_iff_smul H t (g * q * g⁻¹)).mpr ⟨hdH, hdsmul⟩
  have hbot : g * q * g⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← h.inf_eq]
    exact ⟨hdQ, hmem⟩
  have hone : g * q * g⁻¹ = 1 := Subgroup.mem_bot.mp hbot
  have h1 : g * q = g * 1 := by
    rw [mul_one]
    calc g * q = (g * q * g⁻¹) * g := by group
      _ = 1 * g := by rw [hone]
      _ = g := one_mul g
  exact hq1 (mul_left_cancel h1)

end IsTIQ

open IsTIQ

/-- In a split rank-one configuration (`IsSplitRankOne H Q t`) the subgroup `Q` is TI: distinct
`H`-conjugates of `Q` intersect trivially.  (The Zassenhaus hypothesis is not needed.) -/
theorem isTI_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H) :
    ∀ x : G, x ∉ H → Q ⊓ Submission.Blueprint.conj x Q = ⊥ := by
  intro x hx
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyQ, hyC⟩ := hy
  by_contra hy1
  obtain ⟨q, hqQ, hqy⟩ := Subgroup.mem_map.mp hyC
  -- `y = x q x⁻¹`, so `y` fixes the point `x • ∞` and `q ∈ Q`
  have hyx : y * x = x * q := by
    rw [show (MulEquiv.toMonoidHom (MulAut.conj x)) q = x * q * x⁻¹ from
      MulAut.conj_apply x q] at hqy
    rw [← hqy]
    group
  have hω : x • basePt H ≠ basePt H := by
    rw [smul_basePt]
    exact (basePt_ne_iff H x).mpr hx
  have hfix : y • (x • basePt H) = x • basePt H := by
    calc y • (x • basePt H) = (y * x) • basePt H := by rw [← mul_smul]
      _ = (x * q) • basePt H := by rw [hyx]
      _ = x • (q • basePt H) := by rw [mul_smul]
      _ = x • basePt H := by rw [smul_basePt_of_mem H (h.le hqQ)]
  exact hy1 (Q_smul_eq_self h hyQ hfix hω)

end Work.ZassenhausTwoGroup
