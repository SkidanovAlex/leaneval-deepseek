/-
# Support lemmas for `Work.ThreePoints.prop1a_descent`

Elementary group-theoretic bookkeeping used by Peterfalvi I Ch. II §4 Prop. 1(a) (the descent
step): transporting conjugation of subgroups of `↥F` down to the ambient group `G`, and the
relation between `F ⊓ M` and `F ⊓ M^t` for `t ∈ F`.
-/
import Mathlib
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G]

/-- Evenness of the order of a subgroup transfers to any supergroup. -/
theorem even_card_of_le {A B : Subgroup G} (h : A ≤ B) (hev : Even (Nat.card A)) :
    Even (Nat.card B) :=
  even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hev) (Subgroup.card_dvd_of_le h))

/-- Conjugation of a subgroup of `↥F` by `t : ↥F`, pushed down to `G` by the inclusion. -/
theorem map_subtype_conj {F : Subgroup G} {K : Subgroup ↥F} {t : ↥F} :
    Subgroup.map F.subtype (Submission.Blueprint.conj t K) =
      Submission.Blueprint.conj (t : G) (Subgroup.map F.subtype K) := by
  have hcomp : F.subtype.comp (MulAut.conj t).toMonoidHom
      = (MulAut.conj (t : G)).toMonoidHom.comp F.subtype := by
    ext k; simp [MulAut.conj_apply]
  rw [Submission.Blueprint.conj, Submission.Blueprint.conj, Subgroup.map_map, hcomp,
    ← Subgroup.map_map]

/-- `(F ⊓ M)` viewed inside `↥F` is the same thing as `M` viewed inside `↥F`. -/
theorem subgroupOf_inf_left (F M : Subgroup G) :
    (F ⊓ M).subgroupOf F = M.subgroupOf F := by
  ext x
  simp [Subgroup.mem_subgroupOf]

/-- `Subgroup.map F.subtype ((F ⊓ M).subgroupOf F) = F ⊓ M`. -/
theorem map_subtype_subgroupOf_inf (F M : Subgroup G) :
    Subgroup.map F.subtype ((F ⊓ M).subgroupOf F) = F ⊓ M := by
  rw [Subgroup.subgroupOf_map_subtype]
  simp only [inf_assoc, inf_comm, inf_left_comm, inf_idem, inf_left_idem]

/-- If `conj t M = M'` for an element `t` of `F`, then inside `↥F` the conjugate of the
subgroup `F ⊓ M` is `F ⊓ M'` (note that conjugation by `t ∈ F` preserves `F`). -/
theorem conj_subgroupOf_inf {F M M' : Subgroup G} {t : ↥F}
    (h : Submission.Blueprint.conj (t : G) M = M') :
    Submission.Blueprint.conj t ((F ⊓ M).subgroupOf F) = (F ⊓ M').subgroupOf F := by
  apply Subgroup.map_injective F.subtype_injective
  rw [map_subtype_conj, map_subtype_subgroupOf_inf, map_subtype_subgroupOf_inf,
    conj_inf, conj_eq_self_of_mem t.2, h]

/-- Conjugation of an element of `F` by an element of `F` stays in `F` (used to see that
`conj t F = F` for `t ∈ F`). -/
theorem mem_conj_self (F : Subgroup G) {t : G} (ht : t ∈ F) {x : G} (hx : x ∈ F) :
    t * x * t⁻¹ ∈ F :=
  F.mul_mem (F.mul_mem ht hx) (F.inv_mem ht)

/-- Normalisers are compatible with the inclusion `↥F → G`: an element `x` of `F` normalises a
subgroup `Q ≤ ↥F` iff the corresponding element of `G` normalises the image of `Q`. -/
theorem prop1a_norm_map {F : Subgroup G} {Q : Subgroup ↥F} {x : ↥F} :
    (x : G) ∈ Subgroup.normalizer ((Subgroup.map F.subtype Q : Subgroup G) : Set G) ↔
      x ∈ Subgroup.normalizer (Q : Set ↥F) := by
  rw [← Subgroup.mem_subgroupOf,
    Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le Q)]
  have h1 : (Subgroup.map F.subtype Q).subgroupOf F = Q := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective (f := F.subtype) Subtype.coe_injective Q
  rw [h1]

/-- **The `p`-group quotient step.**  In a finite group `F = C ⊔ P` with `C` normal and `P` a
`p`-group for an odd prime `p`, every element of order `≤ 2` lies in `C`. -/
theorem prop1a_p_quotient {F : Type} [Group F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {C P : Subgroup F} (hC : C.Normal)
    (hCP : C ⊔ P = ⊤) (hP : IsPGroup p P) {u : F} (hu : u ^ 2 = 1) : u ∈ C := by
  haveI : Fact p.Prime := ⟨hp⟩
  have htop : Subgroup.map (QuotientGroup.mk' C) P = ⊤ := by
    have h1 : Subgroup.map (QuotientGroup.mk' C) (C ⊔ P) = ⊤ := by
      rw [hCP, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
  have hPgroup : IsPGroup p (F ⧸ C) := by
    have h2 : IsPGroup p ↥(Subgroup.map (QuotientGroup.mk' C) P) := hP.map _
    rw [htop] at h2
    exact IsPGroup.of_equiv h2 Subgroup.topEquiv
  obtain ⟨k, hk⟩ := hPgroup (QuotientGroup.mk' C u)
  have hmem : u ^ (p ^ k) ∈ C := by
    rw [← QuotientGroup.ker_mk' C, MonoidHom.mem_ker, map_pow]
    exact hk
  have hpow : u ^ (p ^ k) = u := by
    obtain ⟨m, hm⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
    rw [hm, pow_succ, pow_mul, hu, one_pow, one_mul]
  rwa [hpow] at hmem

end Work.ThreePoints
