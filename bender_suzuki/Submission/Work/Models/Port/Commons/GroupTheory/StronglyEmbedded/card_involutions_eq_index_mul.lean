import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.sylow2_mem_conj
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.self_normalizing
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.involution_mem_conj
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.eq_of_mem_map_conj_of_orderTwo
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.mem_map_conj_iff
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.orderOf_conj
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.map_conj_eq_of_mem

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- The set of involutions of a group. -/
private abbrev Invol (G : Type*) [Group G] : Type _ := {t : G // orderOf t = 2}

variable {G : Type*} [Group G]

/-- The order of an element is invariant under `t ↦ g⁻¹ * t * g`. -/
private theorem orderOf_inv_conj (g t : G) : orderOf (g⁻¹ * t * g) = orderOf t := by
  have h := orderOf_conj g⁻¹ t
  rwa [inv_inv] at h

/-- If conjugation by `g` preserves a subgroup `M`, then `g` lies in its normalizer. -/
private theorem mem_normalizer_of_map_conj_eq (M : Subgroup G) {g : G}
    (h : M.map (MulAut.conj g).toMonoidHom = M) :
    g ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  rw [← mem_map_conj_iff (A := M) (z := g), h]

/-- If two conjugates of `M` coincide, then the conjugating elements differ by an
element of `M`. -/
private theorem inv_mul_mem_of_map_conj_eq (M : Subgroup G)
    (hN : Subgroup.normalizer (M : Set G) = M)
    {a b : G} (h : M.map (MulAut.conj a).toMonoidHom = M.map (MulAut.conj b).toMonoidHom) :
    b⁻¹ * a ∈ M := by
  have hcomp : (MulAut.conj (b⁻¹ * a)).toMonoidHom
      = (MulAut.conj b⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcomp2 : (MulAut.conj b⁻¹).toMonoidHom.comp (MulAut.conj b).toMonoidHom
      = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  have hmap : M.map (MulAut.conj (b⁻¹ * a)).toMonoidHom = M := by
    rw [hcomp, ← Subgroup.map_map, h, Subgroup.map_map, hcomp2, Subgroup.map_id]
  rw [← hN]
  exact mem_normalizer_of_map_conj_eq M hmap

/-- Pairs `(g, t)` with `t` an involution lying in the conjugate `g M g⁻¹`. -/
private def TRel (M : Subgroup G) : Type _ :=
  {p : G × Invol G // (p.2 : G) ∈ M.map (MulAut.conj p.1).toMonoidHom}

/-- The canonical bijection: for each `g`, the involutions of the conjugate
`g M g⁻¹` correspond to the involutions of `M` via `t ↦ g⁻¹ t g`. -/
private noncomputable def e1 (M : Subgroup G) : TRel M ≃ G × Invol M where
  toFun := fun p =>
    (p.1.1, ⟨⟨p.1.1⁻¹ * (p.1.2 : G) * p.1.1,
        (mem_map_conj_iff (A := M) (z := p.1.1) (u := (p.1.2 : G))).mp p.2⟩, by
      rw [← Subgroup.orderOf_coe]
      show orderOf (p.1.1⁻¹ * (p.1.2 : G) * p.1.1) = 2
      exact (orderOf_inv_conj p.1.1 (p.1.2 : G)).trans p.1.2.2⟩)
  invFun := fun q =>
    ⟨(q.1, ⟨q.1 * (q.2.1 : G) * q.1⁻¹, by
      exact (orderOf_conj q.1 (q.2.1 : G)).trans ((Subgroup.orderOf_coe q.2.1).trans q.2.2)⟩), by
      exact Subgroup.mem_map.mpr ⟨(q.2.1 : G), q.2.1.2,
        by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      show p.1.1 * (p.1.1⁻¹ * (p.1.2 : G) * p.1.1) * p.1.1⁻¹ = (p.1.2 : G)
      group
  right_inv := by
    intro q
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      show q.1⁻¹ * (q.1 * (q.2.1 : G) * q.1⁻¹) * q.1 = (q.2.1 : G)
      group

/-- A choice, for every involution `t`, of an element `g₀` with `t ∈ g₀ M g₀⁻¹`
(possible because every involution is conjugate into `M`). -/
private noncomputable def g0 (M : Subgroup G) [Finite G]
    (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (t : Invol G) : G :=
  Classical.choose (involution_mem_conj M hEven hOdd t.2)

private theorem g0_spec (M : Subgroup G) [Finite G]
    (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (t : Invol G) :
    (t : G) ∈ M.map (MulAut.conj (g0 M hEven hOdd t)).toMonoidHom :=
  Classical.choose_spec (involution_mem_conj M hEven hOdd t.2)

open Classical in
/-- The second bijection: the fibre of `TRel M → Invol G` over an involution `t`
is a right coset of `M`, hence in bijection with `M` via `g ↦ g₀⁻¹ g`. -/
private noncomputable def e2 (M : Subgroup G) [Finite G]
    (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)))) :
    TRel M ≃ Invol G × M where
  toFun := fun p =>
    (p.1.2, ⟨(g0 M hEven hOdd p.1.2)⁻¹ * p.1.1, by
      have hN := self_normalizing M hEven hOdd
      have h1 := eq_of_mem_map_conj_of_orderTwo M hOdd (t := (p.1.2 : G))
        (x := p.1.1) (y := g0 M hEven hOdd p.1.2) p.1.2.2 p.2 (g0_spec M hEven hOdd p.1.2)
      exact inv_mul_mem_of_map_conj_eq M hN h1⟩)
  invFun := fun q =>
    ⟨(g0 M hEven hOdd q.1 * (q.2 : G), q.1), by
      have hcomp : (MulAut.conj (g0 M hEven hOdd q.1 * (q.2 : G))).toMonoidHom
          = (MulAut.conj (g0 M hEven hOdd q.1)).toMonoidHom.comp
            (MulAut.conj (q.2 : G)).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have hmap : M.map (MulAut.conj (g0 M hEven hOdd q.1 * (q.2 : G))).toMonoidHom
          = M.map (MulAut.conj (g0 M hEven hOdd q.1)).toMonoidHom := by
        rw [hcomp, ← Subgroup.map_map, map_conj_eq_of_mem M (q.2.2)]
      rw [hmap]
      exact g0_spec M hEven hOdd q.1⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · dsimp only
      group
    · rfl
  right_inv := by
    intro q
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp only
      group

/-- **Counting involutions relative to a strongly embedded subgroup.**

If `M` is a proper subgroup of a finite group `G` of even order such that for every
`g ∉ M` the intersection `M ⊓ Mᵍ = M ∩ g M g⁻¹` has odd order, then the number of
involutions of `G` equals `[G : M]` times the number of involutions of `M`.

The proof double-counts the set `TRel M = {(g, t) : t² = 1, t ∈ g M g⁻¹}`.  Grouping
by `g` gives `|G| · |Invol M|`; grouping by `t` gives `|Invol G| · |M|` (each
involution lies in a unique conjugate of `M`, so the fibre over `t` is a coset of
`M`).  Hence `|G| · |Invol M| = |Invol G| · |M|`, and cancelling `|M|` together with
`|G| = [G : M] · |M|` yields the claim. -/
theorem card_involutions_eq_index_mul {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hM : M ≠ ⊤) (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)))) :
    Nat.card {t : G // orderOf t = 2} = M.index * Nat.card {t : M // orderOf t = 2} := by
  classical
  change Nat.card (Invol G) = M.index * Nat.card (Invol M)
  have h1 : Nat.card (TRel M) = Nat.card G * Nat.card (Invol M) := by
    rw [Nat.card_congr (e1 M), Nat.card_prod]
  have h2 : Nat.card (TRel M) = Nat.card (Invol G) * Nat.card M := by
    rw [Nat.card_congr (e2 M hEven hOdd), Nat.card_prod]
  have hmain : Nat.card G * Nat.card (Invol M) = Nat.card (Invol G) * Nat.card M :=
    h1.symm.trans h2
  have hindex : Nat.card G = M.index * Nat.card M := (Subgroup.index_mul_card M).symm
  rw [hindex] at hmain
  have hpos : 0 < Nat.card M := Nat.card_pos
  have hkey : (M.index * Nat.card (Invol M)) * Nat.card M
      = Nat.card (Invol G) * Nat.card M := by
    rw [← hmain]; ring
  exact (Nat.mul_right_cancel hpos hkey).symm

end Commons.GroupTheory.StronglyEmbedded
