import Mathlib
import Submission.Work.Reductions.Defs
import Submission.Work.Reductions.stronglyEmbedded_centralizer_le
import Submission.Work.Reductions.stronglyEmbedded_normalizer_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# An involution lies in a unique conjugate of a strongly embedded subgroup

`Work.Reductions.stronglyEmbedded_eq_of_mem_conj`: if `H` is strongly embedded in `G` and the
involution `t` lies in both `H^x` and `H^y`, then `H^x = H^y`.

This is the elementary "two-point stabiliser" fact underlying the whole Bender–Suzuki
induction: strongly embedded subgroups are self-normalising, so `G` acts on the set of its
conjugates, and this lemma says that this action is *sharply* transitive on the involutions
that occur in some conjugate (equivalently: the two-point stabiliser `H ⊓ H^g` for
`g ∉ N_G(H)` contains no involution, which is exactly the strong embeddedness condition).

Proof.  Put `z = x⁻¹ y` and `u = x⁻¹ t x`.  By hypothesis `u ∈ H`; and unravelling
`t ∈ H^y` gives `z⁻¹ u z = y⁻¹ t y ∈ H`, so `u` lies in the intersection `H ⊓ H^z`.  As `u`
is again an involution, `⟨u⟩` is a subgroup of order `2` of `H ⊓ H^z`, hence `2` divides
`|H ⊓ H^z|`, which is therefore even.  Strong embeddedness forces `z ∈ H`, and then
`H^z = H`, so `H^y = H^{xz} = (H^z)^x = H^x`.
-/

set_option autoImplicit false

namespace Work.Reductions

open LeanEval.GroupTheory.Defs

section ConjCalculus

variable {G : Type} [Group G]

/-- Conjugating by `b` and then by `a` is conjugating by `a * b`. -/
theorem conj_map_mul' (a b : G) (H : Subgroup G) :
    Submission.Blueprint.conj a (Submission.Blueprint.conj b H) =
      Submission.Blueprint.conj (a * b) H := by
  rw [Submission.Blueprint.conj, Submission.Blueprint.conj, Submission.Blueprint.conj,
    Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

/-- Membership in a conjugate, unwound: `x ∈ g H g⁻¹ ↔ g⁻¹ x g ∈ H`. -/
theorem mem_conj_map_iff' (g x : G) (H : Subgroup G) :
    x ∈ Submission.Blueprint.conj g H ↔ g⁻¹ * x * g ∈ H := by
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhx⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hhx
    have : g⁻¹ * x * g = h := by rw [← hhx]; group
    rw [this]; exact hh
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

/-- An element of `H` conjugates `H` to itself. -/
theorem conj_eq_self_of_mem' {H : Subgroup G} {z : G} (hz : z ∈ H) :
    Submission.Blueprint.conj z H = H := by
  have hn : z ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer hz
  have hiff : ∀ w : G, w ∈ H ↔ z * w * z⁻¹ ∈ H := Subgroup.mem_normalizer_iff.mp hn
  ext w
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, hvw⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hvw
    rw [← hvw]
    exact H.mul_mem (H.mul_mem hz hv) (H.inv_mem hz)
  · intro hw
    refine ⟨z⁻¹ * w * z, ?_, ?_⟩
    · apply (hiff (z⁻¹ * w * z)).mpr
      have : z * (z⁻¹ * w * z) * z⁻¹ = w := by group
      rw [this]; exact hw
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group

end ConjCalculus

/-- If an involution `t` lies in two conjugates of a strongly embedded subgroup `H`, those
conjugates are equal.  Equivalently: for `g ∉ N_G(H)` the two-point stabiliser `H ⊓ H^g`
contains no involution, which is the defining property of strong embeddedness. -/
theorem stronglyEmbedded_eq_of_mem_conj {G : Type} [Group G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) {x y : G}
    (hx : t ∈ Submission.Blueprint.conj x H) (hy : t ∈ Submission.Blueprint.conj y H) :
    Submission.Blueprint.conj x H = Submission.Blueprint.conj y H := by
  obtain ⟨hne, heven, hodd⟩ := hH
  obtain ⟨z, hzdef⟩ : ∃ z, z = x⁻¹ * y := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u, u = x⁻¹ * t * x := ⟨_, rfl⟩
  -- `u = x⁻¹ t x` lies in `H`, and `z⁻¹ u z = y⁻¹ t y` lies in `H` as well
  have hxH : u ∈ H := by
    rw [hudef]
    exact (mem_conj_map_iff' x t H).mp hx
  have hyH : y⁻¹ * t * y ∈ H := (mem_conj_map_iff' y t H).mp hy
  have hzu : z⁻¹ * u * z = y⁻¹ * t * y := by rw [hzdef, hudef]; group
  have huK : u ∈ H ⊓ Submission.Blueprint.conj z H := by
    rw [Subgroup.mem_inf]
    exact ⟨hxH, (mem_conj_map_iff' z u H).mpr (by rw [hzu]; exact hyH)⟩
  -- `u` is an involution
  have hu_order : orderOf u = 2 := by
    have h1 : u = MulAut.conj x⁻¹ t := by rw [MulAut.conj_apply, hudef]; group
    rw [h1, MulEquiv.orderOf_eq, ht]
  -- hence `|H ⊓ H^z|` is even
  have hdvd : 2 ∣ Nat.card ↥(H ⊓ Submission.Blueprint.conj z H) := by
    have h := Subgroup.card_subgroup_dvd_card
      (Subgroup.zpowers (⟨u, huK⟩ : ↥(H ⊓ Submission.Blueprint.conj z H)))
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu_order] at h
    exact h
  -- so strong embeddedness forces `z ∈ H`
  have hzH : z ∈ H := by
    by_contra hznot
    have hoddK : Odd (Nat.card ↥(H ⊓ Submission.Blueprint.conj z H)) := hodd z hznot
    exact (Nat.not_even_iff_odd.mpr hoddK) (even_iff_two_dvd.mpr hdvd)
  have hz_conj : Submission.Blueprint.conj z H = H := conj_eq_self_of_mem' hzH
  have hxy : x * z = y := by rw [hzdef]; group
  calc Submission.Blueprint.conj x H
      = Submission.Blueprint.conj x (Submission.Blueprint.conj z H) := by rw [hz_conj]
    _ = Submission.Blueprint.conj (x * z) H := conj_map_mul' x z H
    _ = Submission.Blueprint.conj y H := by rw [hxy]

end Work.Reductions
