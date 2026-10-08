import Mathlib
import Submission.Work.BSLit.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.BenderFacts2.threePointAPI` — the three-point condition for `IsZassenhaus`

`Submission.Blueprint.IsZassenhaus H` says that the pointwise stabiliser of any three distinct
points of `Ω = G ⧸ H` is trivial.  This file sets up the (universe-polymorphic) coset and
conjugation API needed to rewrite that condition in the purely group-theoretic form

`∀ x y, x ∉ H → y ∉ H → x⁻¹ * y ∉ H → H ⊓ x H x⁻¹ ⊓ y H y⁻¹ = ⊥`

and proves the easy direction of the equivalence.  Here `H ⧸` is Mathlib's quotient of `G` by the
*left* cosets of `H`, with left action `x • gH = (xg)H` (`Quotient.smul_mk`); consequently the
stabiliser of the point `xH` is the conjugate `x H x⁻¹` (`Submission.Blueprint.conj x H`).
-/

set_option autoImplicit false

namespace Work.BSLit.BenderFacts2

variable {G : Type*} [Group G]

/-- The action on left cosets: `x • (gH) = (xg)H`. -/
theorem coset_smul_mk (H : Subgroup G) (x g : G) :
    x • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk (x * g) := rfl

/-- The coset `xH` is the base point `H` iff `x ∈ H`. -/
@[simp] theorem coset_mk_eq_one_iff {H : Subgroup G} {x : G} :
    (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk 1 ↔ x ∈ H := by
  rw [QuotientGroup.eq]; simp

/-- Two cosets `xH` and `yH` coincide iff `x⁻¹ * y ∈ H`. -/
theorem coset_mk_eq_mk_iff {H : Subgroup G} {x y : G} :
    (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk y ↔ x⁻¹ * y ∈ H :=
  QuotientGroup.eq

/-- Membership in a conjugate, in terms of the conjugating element. -/
theorem mem_conj_iff {H : Subgroup G} {g x : G} :
    x ∈ Submission.Blueprint.conj g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · intro hx
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hx
    have key : g⁻¹ * x * g = h := by
      rw [← hhx]
      change g⁻¹ * (MulAut.conj g) h * g = h
      rw [MulAut.conj_apply]
      group
    rwa [key]
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hx, ?_⟩
    change (MulAut.conj g) (g⁻¹ * x * g) = x
    rw [MulAut.conj_apply]
    group

/-- `g` fixes the point `xH` iff `g ∈ x H x⁻¹`. -/
theorem coset_smul_mk_eq_mk_iff {H : Subgroup G} {g x : G} :
    g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x ↔
      g ∈ Submission.Blueprint.conj x H := by
  rw [coset_smul_mk, coset_mk_eq_mk_iff, mem_conj_iff,
    show (g * x)⁻¹ * x = (x⁻¹ * g * x)⁻¹ from by group, Subgroup.inv_mem_iff]

/-- Conjugation distributes over intersections. -/
theorem conj_inf (g : G) (A B : Subgroup G) :
    Submission.Blueprint.conj g (A ⊓ B) =
      Submission.Blueprint.conj g A ⊓ Submission.Blueprint.conj g B :=
  Subgroup.map_inf A B _ (MulAut.conj g).injective

/-- Conjugation commutes with the image under a `MulEquiv`:
`(x H x⁻¹)^e = (e x) H^e (e x)⁻¹`. -/
theorem conj_map_mulEquiv {G' : Type*} [Group G'] (H : Subgroup G) (e : G ≃* G') (x : G) :
    (Submission.Blueprint.conj x H).map e.toMonoidHom =
      Submission.Blueprint.conj (e x) (H.map e.toMonoidHom) := by
  rw [Submission.Blueprint.conj, Submission.Blueprint.conj, Subgroup.map_map, Subgroup.map_map]
  have hfun : e.toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (e x)).toMonoidHom.comp e.toMonoidHom := by
    ext y
    simp [MulAut.conj_apply]
  rw [hfun]

/-- **The easy half of the three-point condition.**  If the pointwise stabiliser of three
distinct points of `G ⧸ H` is trivial, then `H ⊓ x H x⁻¹ ⊓ y H y⁻¹ = ⊥` for all `x, y` whose
three cosets `H`, `xH`, `yH` are distinct. -/
theorem inf_conj_eq_bot_of_isZassenhaus (H : Subgroup G)
    (h : Submission.Blueprint.IsZassenhaus H) :
    ∀ x y : G, x ∉ H → y ∉ H → x⁻¹ * y ∉ H →
      H ⊓ Submission.Blueprint.conj x H ⊓ Submission.Blueprint.conj y H = ⊥ := by
  intro x y hx hy hxy
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at hg
  obtain ⟨⟨hgH, hgx⟩, hgy⟩ := hg
  have h1 : g • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 := by
    rw [coset_smul_mk, mul_one, coset_mk_eq_one_iff]
    exact hgH
  have h2 : g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x :=
    coset_smul_mk_eq_mk_iff.mpr hgx
  have h3 : g • (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk y :=
    coset_smul_mk_eq_mk_iff.mpr hgy
  exact h (QuotientGroup.mk 1) (QuotientGroup.mk x) (QuotientGroup.mk y)
    (fun hcon => hx (coset_mk_eq_one_iff.mp hcon.symm))
    (fun hcon => hy (coset_mk_eq_one_iff.mp hcon.symm))
    (fun hcon => hxy (coset_mk_eq_mk_iff.mp hcon))
    g h1 h2 h3

end Work.BSLit.BenderFacts2
