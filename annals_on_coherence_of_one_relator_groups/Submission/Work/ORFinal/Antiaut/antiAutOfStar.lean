/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The antipode `ι (gen g) = (gen g)⁻¹` of the division closure, for a real coefficient
embedding

`Work.ORBridgeTor.Mirror` / `HSwap` transport Jaikin-Zapirain--Linton's §5 lemmas from left to
right modules along an *antipode* `ι : AntiAut K S` of `S = D(G)` with `ι (gen g) = (gen g)⁻¹`.
The paper's antipode is `J ∘ *` (conjugation of coefficients followed by the involution); here we
show that when the coefficient embedding `φK : K →+* ℂ` is **real**
(`hreal : ∀ k, star (algebraMap K E.U k) = algebraMap K E.U k`), the involution `star` of the
envelope `U(G)` *itself* is `K`-linear, and hence restricts to a `K`-linear anti-automorphism
`ι` of the division closure `D E φK H`, reversing the group basis.

## Main results

* `Work.ORFinal.Antiaut.star_gen` — `star (gen g) = (gen g)⁻¹` in `U(G)`;
* `Work.ORFinal.Antiaut.star_smul_algebraMap` — for real scalars, `star` is `K`-linear:
  `star (c • x) = c • star x`;
* `Work.ORFinal.Antiaut.star_toUK_mem`, `...star_mem_D` — `star` preserves the division closure
  `D E φK H` (the only point needing care: `D` is closed under *right* inverses of its elements,
  and `U(G)` is directly finite, `Work.ORBridgeLinnell.directlyFinite_of_faithful`);
* `Work.ORFinal.Antiaut.antiAutOfStar` — the antipode itself.
-/
import Mathlib
import Submission.Work.ORFinal.Antiaut
import Submission.Work.ORBridgeLinnell.Countable
import Submission.Work.ORBridgeTor.Defs

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.ORFinal.Antiaut

open Work.ORVonNeumann Work.ORBridgeLinnell

/-- **The involution of `U(G)` inverts the group basis**: `star (gen g) = (gen g)⁻¹`.
This is `E.ι_star` applied to `MonoidAlgebra.star_single`. -/
theorem star_gen {G : Type*} [Group G] (E : StarRegularEnvelope G) (g : G) :
    star ((gen E g : E.Uˣ) : E.U) = ((gen E g)⁻¹ : E.Uˣ) := by
  rw [gen_apply E g, ← E.ι_star, gen_inv_apply E g]
  congr 1
  rw [MonoidAlgebra.star_single]
  simp

/-- **`star` is `K`-linear for a real coefficient embedding.**  Since `star` reverses products,

`star (c • x) = star (algebraMap K E.U c * x) = star x * star (algebraMap K E.U c)`

and `hreal` turns the last factor into `algebraMap K E.U c`, which is central in the `K`-algebra
`E.U` (`Algebra.commutes`). -/
theorem star_smul_algebraMap {G : Type*} [Group G] (E : StarRegularEnvelope G) {K : Type*}
    [Field K] [Algebra K E.U] (hreal : ∀ k : K, star (algebraMap K E.U k) = algebraMap K E.U k)
    (c : K) (x : E.U) : star (c • x) = c • star x := by
  rw [Algebra.smul_def, star_mul, hreal, ← Algebra.commutes c (star x), ← Algebra.smul_def]

/-- `star` carries the image of `K[H]` in `U(G)` into the division closure `D E φK H`.  On the
group basis `toUK (single h k) = k • gen h` this is `star_gen` together with `hreal`; the general
case follows by the `K`-linearity `star_smul_algebraMap`. -/
theorem star_toUK_mem {G : Type*} [Group G] (E : StarRegularEnvelope G) {K : Type*} [Field K]
    (φK : K →+* ℂ) [Algebra K E.U]
    (hreal : ∀ k : K, star (algebraMap K E.U k) = algebraMap K E.U k) (H : Subgroup G)
    (y : MonoidAlgebra K ↥H) : star (toUK E φK H y) ∈ D E φK H := by
  induction y using MonoidAlgebra.induction_on with
  | of m =>
    rw [toUK_of]
    have h1 : star ((gen E (m : G) : E.Uˣ) : E.U) = ((gen E (m : G))⁻¹ : E.Uˣ) :=
      star_gen E (m : G)
    rw [show genU E (m : G) = ((gen E (m : G) : E.Uˣ) : E.U) from (gen_apply E (m : G)).symm,
      h1]
    refine isDivisionClosed_D E φK H (gen E (m : G) : E.U) (gen_mem_D' E φK (H := H) m.2)
      ↑((gen E (m : G))⁻¹) ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  | add a b ha hb =>
    rw [map_add, star_add]
    exact (D E φK H).add_mem ha hb
  | smul r a ha =>
    rw [map_smul, star_smul_algebraMap E hreal r (toUK E φK H a), Algebra.smul_def]
    exact (D E φK H).mul_mem (algebraMap_mem_D E φK H r) ha

/-- **`star` preserves the division closure `D E φK H`.**  The subring
`A = {x : U(G) | star x ∈ D E φK H}` contains the image of `K[H]` (previous lemma) and is
division closed: if `a ∈ A` and `a * b = 1`, then `b * a = 1` by the direct finiteness of `U(G)`
(`Work.ORBridgeLinnell.directlyFinite_of_faithful`, from the faithful rank function `E.rk`), so
`star a * star b = star (b * a) = 1` exhibits `star b` as the (right) inverse in `D` of
`star a ∈ D`.  Minimality of the division closure (`D_minimal`) then gives `D ≤ A`. -/
theorem star_mem_D {G : Type*} [Group G] (E : StarRegularEnvelope G) {K : Type*} [Field K]
    (φK : K →+* ℂ) [Algebra K E.U]
    (hreal : ∀ k : K, star (algebraMap K E.U k) = algebraMap K E.U k) (H : Subgroup G)
    {x : E.U} (hx : x ∈ D E φK H) : star x ∈ D E φK H := by
  let A : Subring E.U :=
    { carrier := {x : E.U | star x ∈ D E φK H}
      mul_mem' := fun {a b} ha hb => by
        show star (a * b) ∈ D E φK H
        rw [star_mul]
        exact (D E φK H).mul_mem hb ha
      one_mem' := by
        show star 1 ∈ D E φK H
        rw [star_one]
        exact (D E φK H).one_mem
      add_mem' := fun {a b} ha hb => by
        show star (a + b) ∈ D E φK H
        rw [star_add]
        exact (D E φK H).add_mem ha hb
      zero_mem' := by
        show star 0 ∈ D E φK H
        rw [star_zero]
        exact (D E φK H).zero_mem
      neg_mem' := fun {a} ha => by
        show star (-a) ∈ D E φK H
        rw [star_neg]
        exact (D E φK H).neg_mem ha }
  have hsub : Set.range (toUK E φK H) ⊆ (A : Set E.U) := by
    rintro _ ⟨y, rfl⟩
    exact star_toUK_mem E φK hreal H y
  have hdc : IsDivisionClosed A := by
    intro a ha b hab
    show star b ∈ D E φK H
    have hba : b * a = 1 :=
      Work.ORBridgeLinnell.directlyFinite_of_faithful E.rk E.rk_faithful hab
    have h1 : star a * star b = 1 := by rw [← star_mul, hba, star_one]
    exact isDivisionClosed_D E φK H (star a) ha (star b) h1
  exact D_minimal E φK hsub hdc hx

/-- **The antipode of the division closure.**  For a real coefficient embedding `φK`, the
involution `star` of the envelope restricts to a `K`-linear anti-automorphism of the subalgebra
`DAlg K E φK H` of `U(G)`, and it inverts the group basis.  This is the datum
`Work.ORFinal.AntiAut'` consumed by the `Work.ORBridgeTor` mirrors. -/
theorem antiAutOfStar (K : Type*) [Field K] {G : Type*} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ)
    [Algebra K E.U] (hreal : ∀ k : K, star (algebraMap K E.U k) = algebraMap K E.U k)
    (H : Subgroup G) :
    ∃ ι : Work.ORFinal.AntiAut' K ↥(Work.ORFinal.DAlg K E φK H),
      ∀ h : ↥H, ι ⟨(Work.ORBridgeLinnell.gen E (h : G) : E.U),
          Work.ORBridgeLinnell.gen_mem_D' E φK (H := H) h.2⟩
        = ⟨↑((Work.ORBridgeLinnell.gen E (h : G))⁻¹),
          Work.ORBridgeLinnell.gen_mem_D' E φK (H := H) (inv_mem h.2)⟩ := by
  let σ : ↥(DAlg K E φK H) → ↥(DAlg K E φK H) :=
    fun x => ⟨star (x : E.U), star_mem_D E φK hreal H x.2⟩
  refine ⟨{ toLinearEquiv :=
              { toFun := σ
                invFun := σ
                left_inv := fun x => Subtype.ext (star_star (x : E.U))
                right_inv := fun x => Subtype.ext (star_star (x : E.U))
                map_add' := fun x y => Subtype.ext (star_add (x : E.U) (y : E.U))
                map_smul' := fun c x => Subtype.ext (star_smul_algebraMap E hreal c (x : E.U)) }
            map_mul' := fun a b => Subtype.ext (star_mul (a : E.U) (b : E.U))
            map_one' := Subtype.ext (star_one E.U) }, ?_⟩
  intro h
  exact Subtype.ext (star_gen E (h : G))

end Work.ORFinal.Antiaut
