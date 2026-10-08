import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BSLit.BenderFacts2

/-- Conjugation commutes with the image under a `MulEquiv`, in the form needed below:
`(H^e)^(e x) = (H^x)^e`, where `H^e = H.map e`. -/
private lemma map_map_conj_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (g : G') :
    (H.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom
      = (H.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

/-- The intersection of `H.map e` with the conjugate of `H.map e` by `g` is the image under `e`
of the corresponding intersection in `G`. -/
private lemma map_inf_conj_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (g : G') :
    (H.map e.toMonoidHom) ⊓ (H.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom
      = (H ⊓ H.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
  rw [map_map_conj_mulEquiv e H g,
    ← Subgroup.map_inf H (H.map (MulAut.conj (e.symm g)).toMonoidHom) e.toMonoidHom
      e.injective]

/-- A subgroup of `G` is everything iff its image under a `MulEquiv` is. -/
private lemma map_eq_top_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) :
    H.map e.toMonoidHom = ⊤ ↔ H = ⊤ := by
  constructor
  · intro h
    exact Subgroup.map_injective e.injective
      (by rw [h, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective])
  · intro h
    rw [h, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

/-- A subgroup of `G` is everything iff its image under a `MulEquiv` is (contrapositive form). -/
private lemma map_ne_top_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) :
    H.map e.toMonoidHom ≠ ⊤ ↔ H ≠ ⊤ := by
  rw [ne_eq, ne_eq, map_eq_top_iff]

/-- **Strong embedding is invariant under a group isomorphism**: `H ≤ G` is strongly embedded
(`H ≠ ⊤`, `|H|` even, and `|H ⊓ H^g|` odd for every `g ∉ H`) iff its image `H.map e` in `G'` is.
Route: `g ∉ H.map e ↔ e.symm g ∉ H`; `(H.map e).map (conj g) = (H.map (conj (e.symm g))).map e`
because `g * e x * g⁻¹ = e (e.symm g * x * (e.symm g)⁻¹)`; and `Nat.card ↥(K.map e) = Nat.card ↥K`
for injective `e` (`Subgroup.card_map_of_injective`), so parity of orders and of the two-point
stabilisers is preserved (`Nat.card_congr` via `Subgroup.equivMapOfInjective`, or `Subgroup.map_inf`
for injective homomorphisms). -/
theorem isStronglyEmbedded_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H.map e.toMonoidHom) ↔
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded H := by
  have hf : Function.Injective (e.toMonoidHom : G →* G') := e.injective
  have hcard : Nat.card ↥(H.map e.toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective hf
  unfold LeanEval.GroupTheory.Defs.IsStronglyEmbedded
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(map_ne_top_iff e H).mp h1, ?_, ?_⟩
    · rwa [hcard] at h2
    · intro g hg
      have hmem : e g ∉ H.map e.toMonoidHom := fun hm =>
        hg ((Subgroup.mem_map_iff_mem hf).mp hm)
      have hodd := h3 (e g) hmem
      have key := map_inf_conj_map_mulEquiv e H (e g)
      rw [MulEquiv.symm_apply_apply] at key
      rwa [key, Subgroup.card_map_of_injective hf] at hodd
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(map_ne_top_iff e H).mpr h1, ?_, ?_⟩
    · rwa [hcard]
    · intro g hg
      have hmem : e.symm g ∉ H := fun hm => hg (by
        rw [← e.apply_symm_apply g]
        exact Subgroup.mem_map_of_mem e.toMonoidHom hm)
      have hodd := h3 (e.symm g) hmem
      rw [map_inf_conj_map_mulEquiv e H g, Subgroup.card_map_of_injective hf]
      exact hodd

end Work.BSLit.BenderFacts2
