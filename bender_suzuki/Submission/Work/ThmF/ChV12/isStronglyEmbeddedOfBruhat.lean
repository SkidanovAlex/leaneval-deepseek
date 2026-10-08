import Mathlib
import Submission.Work.ThmF.ChV12.L5Struct

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `isStronglyEmbeddedOfBruhat`

Suppose a finite group `X` admits a "Bruhat decomposition" `X = B ∪ B τ B` with respect to a
subgroup `B ≠ ⊤`, that `|B|` is even, and that the "torus" `B ∩ B^τ` has **odd** order.
Then `B` is strongly embedded in `X`.

The point is that the hypothesis `Odd |B ∩ B^τ|` propagates to *all* elements outside `B`: if
`g = b₁ τ b₂` with `bᵢ ∈ B`, then

* `B ∩ B^{ub} = B ∩ B^u` for `b ∈ B` (right multiplication of the conjugating element by an
  element of `B` does not change the intersection at all, since `b` normalises `B`), and
* `B ∩ B^{bu} = (B ∩ B^u)^b` (left multiplication conjugates the intersection by `b`,
  which does not change its cardinality).

Applying this with `u = τ`, `b = b₂` and then `b = b₁` gives `|B ∩ B^g| = |B ∩ B^τ|`, which is
odd by hypothesis.

## Main results

* `Work.ThmF.ChV12.mem_map_conj_iff`
* `Work.ThmF.ChV12.map_conj_eq_self`
* `Work.ThmF.ChV12.inf_map_conj_mul_mem`
* `Work.ThmF.ChV12.inf_map_conj_eq_map`
* `Work.ThmF.ChV12.natCard_inf_map_conj_three`
* `Work.ThmF.ChV12.isStronglyEmbeddedOfBruhat`
-/

namespace Work.ThmF.ChV12

universe u

variable {G : Type u} [Group G]

/-- Membership in `H.map (conj w)`, spelled out: `x ∈ H^w ↔ w⁻¹ * x * w ∈ H`. -/
theorem mem_map_conj_iff (H : Subgroup G) (w x : G) :
    x ∈ H.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * x * w ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert hy using 1
    group
  · intro h
    exact ⟨w⁻¹ * x * w, h, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

/-- An element `b ∈ H` normalises `H`: `H^b = H`. -/
theorem map_conj_eq_self (H : Subgroup G) {b : G} (hb : b ∈ H) :
    H.map (MulAut.conj b).toMonoidHom = H := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact H.mul_mem (H.mul_mem hb hy) (H.inv_mem hb)
  · intro x hx
    refine ⟨b⁻¹ * x * b, H.mul_mem (H.mul_mem (H.inv_mem hb) hx) hb, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

/-- Right multiplication of the conjugating element by an element `b ∈ H` does not change the
intersection `H ⊓ H^u`. -/
theorem inf_map_conj_mul_mem (H : Subgroup G) {b : G} (hb : b ∈ H) (u : G) :
    H ⊓ H.map (MulAut.conj (u * b)).toMonoidHom
      = H ⊓ H.map (MulAut.conj u).toMonoidHom := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_map_conj_iff, mem_map_conj_iff]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have h2 : b⁻¹ * (u⁻¹ * x * u) * b ∈ H := by
      have heq : (u * b)⁻¹ * x * (u * b) = b⁻¹ * (u⁻¹ * x * u) * b := by group
      rwa [heq] at h
    rw [← map_conj_eq_self H hb, mem_map_conj_iff]
    exact h2
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have h2 : b⁻¹ * (u⁻¹ * x * u) * b ∈ H := by
      rw [← mem_map_conj_iff H b (u⁻¹ * x * u), map_conj_eq_self H hb]
      exact h
    have heq : (u * b)⁻¹ * x * (u * b) = b⁻¹ * (u⁻¹ * x * u) * b := by group
    rw [heq]
    exact h2

/-- Left multiplication of the conjugating element by an element `b ∈ H` conjugates the
intersection `H ⊓ H^u` by `b` (hence does not change its cardinality). -/
theorem inf_map_conj_eq_map (H : Subgroup G) {b : G} (hb : b ∈ H) (u : G) :
    (H ⊓ H.map (MulAut.conj u).toMonoidHom).map (MulAut.conj b).toMonoidHom
      = H ⊓ H.map (MulAut.conj (b * u)).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [Subgroup.mem_inf, mem_map_conj_iff] at hy
    obtain ⟨hyH, hyu⟩ := hy
    rw [Subgroup.mem_inf, mem_map_conj_iff]
    rw [← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨H.mul_mem (H.mul_mem hb hyH) (H.inv_mem hb), ?_⟩
    convert hyu using 1
    group
  · rintro ⟨hxH, hxu⟩
    have hxu' : x ∈ H.map (MulAut.conj (b * u)).toMonoidHom := hxu
    rw [mem_map_conj_iff] at hxu'
    refine ⟨b⁻¹ * x * b, ?_, ?_⟩
    · rw [Subgroup.mem_inf, mem_map_conj_iff]
      refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hb) hxH) hb, ?_⟩
      convert hxu' using 1
      group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

/-- The cardinality of `H ⊓ H^u` is unchanged when `u` is multiplied on the left and on the
right by elements of `H`. -/
theorem natCard_inf_map_conj_three (H : Subgroup G) (u : G) {b₁ b₂ : G}
    (h₁ : b₁ ∈ H) (h₂ : b₂ ∈ H) :
    Nat.card ↥(H ⊓ H.map (MulAut.conj (b₁ * u * b₂)).toMonoidHom)
      = Nat.card ↥(H ⊓ H.map (MulAut.conj u).toMonoidHom) := by
  have hstep1 : H ⊓ H.map (MulAut.conj (b₁ * u * b₂)).toMonoidHom
      = H ⊓ H.map (MulAut.conj (b₁ * u)).toMonoidHom := inf_map_conj_mul_mem H h₂ (b₁ * u)
  rw [hstep1]
  have hstep2 := inf_map_conj_eq_map H h₁ u
  rw [← hstep2]
  exact Subgroup.card_map_of_injective
    (f := (MulAut.conj b₁).toMonoidHom) (fun x y h => (MulAut.conj b₁).injective h)

/-- **Bender's criterion for a Bruhat decomposition.**  If a finite group `X` is the union of
`B` and the double coset `B τ B`, with `B ≠ ⊤`, `|B|` even and `B ∩ B^τ` of odd order, then `B`
is strongly embedded in `X`: the 2-part of `B ∩ B^g` is trivial for every `g ∉ B`. -/
theorem isStronglyEmbeddedOfBruhat {X : Type} [Group X] [Finite X]
    (B : Subgroup X) (τ : X)
    (hcov : ∀ g : X, g ∈ B ∨ ∃ b₁ b₂ : ↥B, g = (b₁ : X) * τ * (b₂ : X))
    (hne : B ≠ ⊤) (hev : Even (Nat.card B))
    (hodd : Odd (Nat.card ↥(B ⊓ B.map (MulAut.conj τ).toMonoidHom))) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded B := by
  refine ⟨hne, hev, ?_⟩
  intro g hg
  rcases hcov g with h | ⟨b₁, b₂, hg_eq⟩
  · exact absurd h hg
  · rw [hg_eq]
    rw [natCard_inf_map_conj_three B τ b₁.2 b₂.2]
    exact hodd

end Work.ThmF.ChV12
