import Mathlib
import Submission.Work.BSLit.BenderFacts2.threePointAPI

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.BenderFacts2.isZassenhaus_of_inf_conj_eq_bot`

The hard half of the three-point condition for `Submission.Blueprint.IsZassenhaus`: the purely
group-theoretic condition

`∀ x y, x ∉ H → y ∉ H → x⁻¹ * y ∉ H → H ⊓ x H x⁻¹ ⊓ y H y⁻¹ = ⊥`

forces the pointwise stabiliser of every triple of distinct points of `Ω = G ⧸ H` to be trivial.

The reduction is the standard one: the left action of `G` on the left cosets `G ⧸ H` is transitive,
so an arbitrary triple can be moved to the base triple `(H, xH, yH)`; the pointwise stabiliser of a
triple is carried to the stabiliser of its image by conjugation, so triviality transfers back.
-/

set_option autoImplicit false

namespace Work.BSLit.BenderFacts2

variable {G : Type*} [Group G]

/-- **Conjugating a point stabiliser.**  Membership of the conjugate `w⁻¹ g w` in the stabiliser
`z H z⁻¹` of the point `zH` is the same as membership of `g` in the stabiliser of the conjugate
point `(w z)H`.  Equivalently, the stabiliser of the point `zH` is carried by the conjugation
automorphism `x ↦ w x w⁻¹` to the stabiliser of `(w z)H`. -/
theorem mem_conj_inv_mul_mul (H : Subgroup G) (w z g : G) :
    w⁻¹ * g * w ∈ Submission.Blueprint.conj z H ↔
      g ∈ Submission.Blueprint.conj (w * z) H := by
  rw [← coset_smul_mk_eq_mk_iff, ← coset_smul_mk_eq_mk_iff, ← coset_smul_mk, mul_smul, mul_smul,
    inv_smul_eq_iff]

/-- **The hard half of the three-point condition for `IsZassenhaus`.**  If for all `x y : G` whose cosets `H`, `xH`, `yH` are three distinct points of `Ω = G ⧸ H` the pointwise stabiliser `H ⊓ x H x⁻¹ ⊓ y H y⁻¹` of the triple is trivial, then the pointwise stabiliser of *every* triple of distinct points of `Ω` is trivial, i.e. `H` is Zassenhaus.  Route: `G` acts transitively on `Ω`, so replace an arbitrary triple `(a,b,c)` by `w⁻¹ • (a,b,c)` with `w := a.out`; then `a` becomes the base point `H`, and the primitive triple is `(H, xH, yH)`, whose points are distinct exactly when `x ∉ H`, `y ∉ H`, `x⁻¹ * y ∉ H`.  The conjugation by `w` conjugates the pointwise stabiliser, so triviality transfers back. -/
theorem isZassenhaus_of_inf_conj_eq_bot {G : Type*} [Group G] (H : Subgroup G)
    (h : ∀ x y : G, x ∉ H → y ∉ H → x⁻¹ * y ∉ H →
      H ⊓ Submission.Blueprint.conj x H ⊓ Submission.Blueprint.conj y H = ⊥) :
    Submission.Blueprint.IsZassenhaus H := by
  intro a b c hab hac hbc g hga hgb hgc
  -- Move the base point of the triple to `H`: `w := a.out` with `w • (w⁻¹ • a) = a`.
  set w : G := a.out with hw
  set x : G := w⁻¹ * b.out with hx
  set y : G := w⁻¹ * c.out with hy
  have hwa : (QuotientGroup.mk w : G ⧸ H) = a := by rw [hw]; exact a.out_eq
  have hwb : (QuotientGroup.mk b.out : G ⧸ H) = b := b.out_eq
  have hwc : (QuotientGroup.mk c.out : G ⧸ H) = c := c.out_eq
  -- The shifted triple is `(H, xH, yH) = (w⁻¹ • a, w⁻¹ • b, w⁻¹ • c)`.
  have hbase : (QuotientGroup.mk (1 : G) : G ⧸ H) = w⁻¹ • a := by
    rw [← hwa, coset_smul_mk, inv_mul_cancel]
  have hmx : (QuotientGroup.mk x : G ⧸ H) = w⁻¹ • b := by
    rw [hx, ← coset_smul_mk, hwb]
  have hmy : (QuotientGroup.mk y : G ⧸ H) = w⁻¹ • c := by
    rw [hy, ← coset_smul_mk, hwc]
  -- The shifted triple consists of three distinct points.
  have hne1 : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ QuotientGroup.mk x := by
    intro hcon
    apply hab
    rw [hbase, hmx] at hcon
    have hh := congrArg (fun p : G ⧸ H => w • p) hcon
    rwa [smul_inv_smul, smul_inv_smul] at hh
  have hne2 : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ QuotientGroup.mk y := by
    intro hcon
    apply hac
    rw [hbase, hmy] at hcon
    have hh := congrArg (fun p : G ⧸ H => w • p) hcon
    rwa [smul_inv_smul, smul_inv_smul] at hh
  have hne12 : (QuotientGroup.mk x : G ⧸ H) ≠ QuotientGroup.mk y := by
    intro hcon
    apply hbc
    rw [hmx, hmy] at hcon
    have hh := congrArg (fun p : G ⧸ H => w • p) hcon
    rwa [smul_inv_smul, smul_inv_smul] at hh
  -- Distinctness in coset language.
  have hxH : x ∉ H := fun hxmem => hne1 (coset_mk_eq_one_iff.mpr hxmem).symm
  have hyH : y ∉ H := fun hymem => hne2 (coset_mk_eq_one_iff.mpr hymem).symm
  have hxyH : x⁻¹ * y ∉ H := fun hm => hne12 (coset_mk_eq_mk_iff.mpr hm)
  -- Apply the hypothesis to the shifted triple.
  have hbot := h x y hxH hyH hxyH
  have hmem : w⁻¹ * g * w ∈ H ⊓ Submission.Blueprint.conj x H ⊓ Submission.Blueprint.conj y H := by
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- `w⁻¹ g w` fixes the base point, hence lies in `H`.
      have hgw : g • (QuotientGroup.mk w : G ⧸ H) = QuotientGroup.mk w := by
        rw [hwa]; exact hga
      exact mem_conj_iff.mp (coset_smul_mk_eq_mk_iff.mp hgw)
    · -- `w⁻¹ g w` fixes `xH`.
      refine coset_smul_mk_eq_mk_iff.mp ?_
      rw [hmx, mul_smul, mul_smul, smul_inv_smul, hgb]
    · -- `w⁻¹ g w` fixes `yH`.
      refine coset_smul_mk_eq_mk_iff.mp ?_
      rw [hmy, mul_smul, mul_smul, smul_inv_smul, hgc]
  have hgw1 : w⁻¹ * g * w = 1 := Subgroup.mem_bot.mp (hbot ▸ hmem)
  calc g = w * (w⁻¹ * g * w) * w⁻¹ := by group
    _ = 1 := by rw [hgw1]; simp

/-- **The three-point condition, in full.**  `H` is Zassenhaus (the pointwise stabiliser of every
triple of distinct points of `G ⧸ H` is trivial) if and only if `H ⊓ x H x⁻¹ ⊓ y H y⁻¹ = ⊥` for
all `x, y` for which the three cosets `H`, `xH`, `yH` are distinct. -/
theorem isZassenhaus_iff_inf_conj_eq_bot (H : Subgroup G) :
    Submission.Blueprint.IsZassenhaus H ↔
      ∀ x y : G, x ∉ H → y ∉ H → x⁻¹ * y ∉ H →
        H ⊓ Submission.Blueprint.conj x H ⊓ Submission.Blueprint.conj y H = ⊥ :=
  ⟨inf_conj_eq_bot_of_isZassenhaus H, fun h => isZassenhaus_of_inf_conj_eq_bot H h⟩

end Work.BSLit.BenderFacts2
