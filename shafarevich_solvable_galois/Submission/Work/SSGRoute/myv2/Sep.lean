import Mathlib
import Submission.Work.SSGRoute.EscapeCoreLib.charSeparation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Separation of points of a finite abelian group of exponent `p` by characters into `ZMod p`

`Work.SSGRoute.N2v2.mem_of_forall_monoidHom_eq_one` is the multiplicative form of
`Work.SSGRoute.EscapeCoreLib.mem_of_forall_linearMap_eq_zero`, in the exact shape in which the
orthogonality argument of the escape-form Grünwald theorem consumes it: for a finite abelian group
`A` of exponent `p`, a subgroup `B ≤ A` and `a : A` such that every character
`χ : A →* Multiplicative (ZMod p)` killing `B` also kills `a`, one has `a ∈ B`.
-/

namespace Work.SSGRoute.N2v2

/-- **Characters into `ZMod p` separate the points of a finite abelian group of exponent `p`
modulo a subgroup.** -/
theorem mem_of_forall_monoidHom_eq_one {p : ℕ} [Fact p.Prime] {A : Type} [CommGroup A] [Finite A]
    (hp : ∀ a : A, a ^ p = 1) (B : Subgroup A) {a : A}
    (h : ∀ χ : A →* Multiplicative (ZMod p), B ≤ χ.ker → χ a = 1) : a ∈ B := by
  classical
  by_contra ha
  haveI : Finite (A ⧸ B) := Quotient.finite _
  have hexp : ∀ q : A ⧸ B, q ^ p = 1 := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective B q
    rw [← map_pow, hp y, map_one]
  haveI : Module (ZMod p) (Additive (A ⧸ B)) :=
    AddCommGroup.zmodModule (fun x => by
      obtain ⟨q, rfl⟩ := Additive.ofMul.surjective x
      show p • Additive.ofMul q = 0
      rw [← ofMul_pow, hexp q, ofMul_one])
  set q : A ⧸ B := QuotientGroup.mk' B a with hqdef
  have hq : q ≠ 1 := fun h1 => ha ((QuotientGroup.eq_one_iff a).mp h1)
  have hy : Additive.ofMul q ≠ 0 := fun h0 => hq ((ofMul_eq_zero).mp h0)
  obtain ⟨f, hf⟩ :=
    Work.SSGRoute.EscapeCoreLib.exists_dual_apply_ne_zero (p := p) (y := Additive.ofMul q) hy
  let χ : A →* Multiplicative (ZMod p) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (f (Additive.ofMul (QuotientGroup.mk' B x))))
      (fun x y => by
        simp only [map_mul, ofMul_mul, map_add, ofAdd_add])
  have hχapp : ∀ x : A, χ x =
      Multiplicative.ofAdd (f (Additive.ofMul (QuotientGroup.mk' B x))) := fun x => rfl
  have hker : B ≤ χ.ker := by
    intro x hx
    have hx1 : QuotientGroup.mk' B x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    show Multiplicative.ofAdd (f (Additive.ofMul (QuotientGroup.mk' B x))) = 1
    rw [hx1]
    simp [ofMul_one]
  have h1 := h χ hker
  have h2 : χ a = Multiplicative.ofAdd (f (Additive.ofMul q)) := hχapp a
  rw [h2, ofAdd_eq_one] at h1
  exact hf h1

end Work.SSGRoute.N2v2
