import Mathlib
import Submission.Work.ORHughesFree.StarRegular

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.StarRegular

open Work.ORHughesFree

/-!
## The `∗`-regular closure is contained in every `∗`-regular subring

The main result of this file is `starRegularClosure_le`: the `∗`-regular closure of a
`∗`-subring `R` of a `∗`-regular ring `U` is contained in every `∗`-regular `∗`-subring `S`
of `U` containing `R`.  The point is that a `∗`-regular subring is closed under relative
inverses *taken in `U`*: this uses that relative (Moore--Penrose) inverses exist in a ring
which is von Neumann regular with a proper involution (Berberian) and are unique.

We prove the existence and uniqueness of relative inverses here from scratch, so that the
file is self-contained apart from the definitions in `Submission.Work.ORHughesFree.StarRegular`.
-/

section Core

variable {U : Type*} [Ring U] [StarRing U] [IsStarRegular U]

theorem star_mul_twice {e : U} (he : e * e = e) : star e * star e = star e := by
  rw [← star_mul, he]

theorem one_sub_mul_self {e : U} (he : e * e = e) : (1 - e) * e = 0 := by
  rw [sub_mul, one_mul, he, sub_self]

theorem one_sub_star_mul_star {e : U} (he : e * e = e) : (1 - star e) * star e = 0 := by
  rw [sub_mul, one_mul, star_mul_twice he, sub_self]

theorem star_mul_one_sub_star {e : U} (he : e * e = e) : star e * (1 - star e) = 0 := by
  rw [mul_sub, mul_one, star_mul_twice he, sub_self]

theorem one_sub_star_mul_one_sub_star {e : U} (he : e * e = e) :
    (1 - star e) * (1 - star e) = 1 - star e := by
  have h : (1 - star e) * (1 - star e) = 1 - star e - star e + star e * star e := by
    noncomm_ring
  rw [h, star_mul_twice he]; abel

theorem mul_self_star_mul_add {e : U} (he : e * e = e) :
    (star e * e + (1 - star e) * (1 - e)) * e = star e * e := by
  rw [add_mul, mul_assoc (star e) e e, he, mul_assoc (1 - star e) (1 - e) e,
    one_sub_mul_self he, mul_zero, add_zero]

theorem star_mul_star_mul_add {e : U} (he : e * e = e) :
    star e * (star e * e + (1 - star e) * (1 - e)) = star e * e := by
  rw [mul_add, ← mul_assoc (star e) (star e) e, star_mul_twice he,
    ← mul_assoc (star e) (1 - star e) (1 - e), star_mul_one_sub_star he, zero_mul, add_zero]

/-- In a `∗`-regular ring, for an idempotent `e`, the element
`z = star e * e + (1 - star e) * (1 - e)` has a self-adjoint two-sided inverse `w`. -/
theorem exists_inv_star_mul_add {e : U} (he : e * e = e) :
    ∃ w : U, (star e * e + (1 - star e) * (1 - e)) * w = 1 ∧
      w * (star e * e + (1 - star e) * (1 - e)) = 1 ∧ star w = w := by
  set z : U := star e * e + (1 - star e) * (1 - e) with hz
  have hez : star e * z = star e * e := by rw [hz]; exact star_mul_star_mul_add he
  have hzstar : star z = z := by
    rw [hz]; simp only [star_add, star_mul, star_sub, star_one, star_star]
  have hhfez : (1 - star e) * z = (1 - star e) * (1 - e) := by
    rw [hz, mul_add, ← mul_assoc (1 - star e) (star e) e, one_sub_star_mul_star he, zero_mul,
      ← mul_assoc (1 - star e) (1 - star e) (1 - e), one_sub_star_mul_one_sub_star he, zero_add]
  have hzerol : ∀ y : U, z * y = 0 → y = 0 := by
    intro y hy
    have h2 : star y * star e * z * y = 0 := by
      rw [mul_assoc (star y * star e) z y, hy, mul_zero]
    have h4 : star y * (star e * e) * y = 0 := by
      rw [← hez, ← mul_assoc (star y) (star e) z]; exact h2
    have hey : e * y = 0 := by
      refine IsStarRegular.proper (e * y) ?_
      rw [star_mul, mul_assoc (star y) (star e) (e * y), ← mul_assoc (star e) e y,
        ← mul_assoc (star y) (star e * e) y]
      exact h4
    have h2f : star y * (1 - star e) * z * y = 0 := by
      rw [mul_assoc (star y * (1 - star e)) z y, hy, mul_zero]
    have h4f : star y * ((1 - star e) * (1 - e)) * y = 0 := by
      rw [← hhfez, ← mul_assoc (star y) (1 - star e) z]; exact h2f
    have hfy : (1 - e) * y = 0 := by
      refine IsStarRegular.proper ((1 - e) * y) ?_
      rw [star_mul, star_sub, star_one, mul_assoc (star y) (1 - star e) ((1 - e) * y),
        ← mul_assoc (1 - star e) (1 - e) y, ← mul_assoc (star y) ((1 - star e) * (1 - e)) y]
      exact h4f
    calc
      y = 1 * y := (one_mul y).symm
      _ = (e + (1 - e)) * y := by rw [show e + (1 - e) = (1 : U) by abel]
      _ = e * y + (1 - e) * y := add_mul _ _ _
      _ = 0 := by rw [hey, hfy, add_zero]
  obtain ⟨c, hc⟩ := (inferInstance : VonNeumannRegularRing U).exists_mul_inverse z
  have hcz : c * z = 1 := by
    have h : z * (1 - c * z) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc z c z, hc, sub_self]
    exact (sub_eq_zero.mp (hzerol (1 - c * z) h)).symm
  have h2 : z * star c = 1 := by
    have h := congrArg star hcz
    simpa only [star_mul, hzstar, star_one] using h
  have hcs : star c = c := by
    calc
      star c = 1 * star c := (one_mul _).symm
      _ = (c * z) * star c := by rw [hcz]
      _ = c * (z * star c) := mul_assoc c z (star c)
      _ = c := by rw [h2, mul_one]
  have hzc : z * c = 1 := by rw [← hcs]; exact h2
  exact ⟨c, hzc, hcz, hcs⟩

/-- **Rectification of an idempotent.**  In a `∗`-regular ring, the right ideal generated by
an idempotent `e` is generated by a projection `p`, with `p * e = e` and `e * p = p`. -/
theorem exists_isProjection_spanning {e : U} (he : e * e = e) :
    ∃ p : U, IsProjection p ∧ p * e = e ∧ e * p = p := by
  obtain ⟨w, hzw, hwz, hwstar⟩ := exists_inv_star_mul_add he
  have hsee : star e * star e = star e := star_mul_twice he
  have h1 : w * (star e * e) = e := by
    rw [← mul_self_star_mul_add he,
      ← mul_assoc w (star e * e + (1 - star e) * (1 - e)) e, hwz, one_mul]
  have h2 : star e * e * w = star e := by
    rw [← star_mul_star_mul_add he, mul_assoc, hzw, mul_one]
  refine ⟨e * w * star e, ⟨?_, ?_⟩, ?_, ?_⟩
  · calc
      star (e * w * star e) = e * (star w * star e) := by
        rw [star_mul, star_star, star_mul]
      _ = e * w * star e := by rw [hwstar]; noncomm_ring
  · calc
      e * w * star e * (e * w * star e) = e * w * (star e * e * w) * star e := by
        noncomm_ring
      _ = e * w * star e * star e := by rw [h2]
      _ = e * w * (star e * star e) := by noncomm_ring
      _ = e * w * star e := by rw [hsee]
  · calc
      e * w * star e * e = e * (w * (star e * e)) := by noncomm_ring
      _ = e * e := by rw [h1]
      _ = e := he
  · calc
      e * (e * w * star e) = (e * e) * w * star e := by noncomm_ring
      _ = e * w * star e := by rw [he]

/-- **Left rectification of an idempotent.**  In a `∗`-regular ring, the left ideal generated
by an idempotent `h` is generated by a projection `q`, with `q * h = q` and `h * q = h`. -/
theorem exists_isProjection_spanning_left {h : U} (hh : h * h = h) :
    ∃ q : U, IsProjection q ∧ q * h = q ∧ h * q = h := by
  obtain ⟨q, hqproj, hq1, hq2⟩ :=
    exists_isProjection_spanning (e := star h) (by rw [← star_mul, hh])
  refine ⟨q, hqproj, ?_, ?_⟩
  · have h := congrArg star hq2
    rw [star_mul, star_star, hqproj.1] at h
    exact h
  · have h := congrArg star hq1
    rw [star_mul, star_star, hqproj.1] at h
    exact h

/-- **Berberian.**  Every element of a `∗`-regular ring has a relative (Moore--Penrose)
inverse. -/
theorem exists_isRelativeInverse_aux (a : U) : ∃ y : U, IsRelativeInverse a y := by
  obtain ⟨c, hc⟩ := (inferInstance : VonNeumannRegularRing U).exists_mul_inverse a
  have hg : (a * c) * (a * c) = a * c := by
    rw [show (a * c) * (a * c) = ((a * c) * a) * c from (mul_assoc (a * c) a c).symm, hc]
  have hh : (c * a) * (c * a) = c * a := by
    rw [mul_assoc c a (c * a), ← mul_assoc a c a, hc]
  obtain ⟨f, hfproj, hfg, hgf⟩ := exists_isProjection_spanning hg
  obtain ⟨e, heproj, heh, hhe⟩ := exists_isProjection_spanning_left hh
  have ha_h : a * (c * a) = a := by rw [← mul_assoc a c a]; exact hc
  have hae : a * e = a := by
    calc
      a * e = (a * (c * a)) * e := by rw [ha_h]
      _ = a * ((c * a) * e) := mul_assoc a (c * a) e
      _ = a * (c * a) := by rw [hhe]
      _ = a := ha_h
  have hfa : f * a = a := by
    have hga : (a * c) * a = a := hc
    calc
      f * a = f * ((a * c) * a) := by rw [hga]
      _ = (f * (a * c)) * a := (mul_assoc f (a * c) a).symm
      _ = (a * c) * a := by rw [hfg]
      _ = a := hga
  have hay : a * (e * c * f) = f := by
    calc
      a * (e * c * f) = (a * e) * (c * f) := by noncomm_ring
      _ = a * (c * f) := by rw [hae]
      _ = (a * c) * f := (mul_assoc a c f).symm
      _ = f := hgf
  have hya : (e * c * f) * a = e := by
    calc
      e * c * f * a = (e * c) * (f * a) := by noncomm_ring
      _ = (e * c) * a := by rw [hfa]
      _ = e * (c * a) := mul_assoc e c a
      _ = e := heh
  have hee : e * e = e := heproj.2
  refine ⟨e * c * f, ?_, ?_, ?_, ?_⟩
  · calc
      a * (e * c * f) * a = (a * e) * (c * (f * a)) := by noncomm_ring
      _ = a * (c * a) := by rw [hae, hfa]
      _ = a := by rw [← mul_assoc a c a, hc]
  · calc
      e * c * f * a * (e * c * f) = ((e * c * f) * a) * (e * c * f) := rfl
      _ = e * (e * c * f) := by rw [hya]
      _ = (e * e) * c * f := by noncomm_ring
      _ = e * c * f := by rw [hee]
  · rw [hay, hfproj.1]
  · rw [hya, heproj.1]

/-- Relative inverses are unique: only the two self-adjointness conditions are used. -/
theorem isRelativeInverse_unique_aux {x y z : U} (hy : IsRelativeInverse x y)
    (hz : IsRelativeInverse x z) : y = z := by
  have hFE : x * y = (x * z) * (x * y) := by
    calc
      x * y = (x * z * x) * y := by rw [hz.left]
      _ = (x * z) * (x * y) := mul_assoc (x * z) x y
  have hEF : x * y = (x * y) * (x * z) := by
    calc
      x * y = star (x * y) := hy.star_left.symm
      _ = star ((x * z) * (x * y)) := congrArg star hFE
      _ = star (x * y) * star (x * z) := star_mul (x * z) (x * y)
      _ = (x * y) * (x * z) := by rw [hy.star_left, hz.star_left]
  have hFE' : x * z = (x * y) * (x * z) := by
    calc
      x * z = (x * y * x) * z := by rw [hy.left]
      _ = (x * y) * (x * z) := mul_assoc (x * y) x z
  have hxy : x * y = x * z := hEF.trans hFE'.symm
  have hyx : y * x = (y * x) * (z * x) := by
    calc
      y * x = y * ((x * z) * x) := by rw [hz.left]
      _ = (y * (x * z)) * x := (mul_assoc y (x * z) x).symm
      _ = ((y * x) * z) * x := by rw [← mul_assoc y x z]
      _ = (y * x) * (z * x) := mul_assoc (y * x) z x
  have hyx' : y * x = (z * x) * (y * x) := by
    calc
      y * x = star (y * x) := hy.star_right.symm
      _ = star ((y * x) * (z * x)) := congrArg star hyx
      _ = star (z * x) * star (y * x) := star_mul (y * x) (z * x)
      _ = (z * x) * (y * x) := by rw [hy.star_right, hz.star_right]
  have hzx : z * x = (z * x) * (y * x) := by
    calc
      z * x = z * ((x * y) * x) := by rw [hy.left]
      _ = (z * (x * y)) * x := (mul_assoc z (x * y) x).symm
      _ = ((z * x) * y) * x := by rw [← mul_assoc z x y]
      _ = (z * x) * (y * x) := mul_assoc (z * x) y x
  have hyx_eq : y * x = z * x := hyx'.trans hzx.symm
  calc
    y = y * x * y := hy.right.symm
    _ = (y * x) * y := rfl
    _ = (z * x) * y := by rw [hyx_eq]
    _ = z * (x * y) := mul_assoc z x y
    _ = z * (x * z) := by rw [hxy]
    _ = z * x * z := (mul_assoc z x z).symm
    _ = z := hz.right

end Core

/-- A relative inverse in a `∗`-subring is a relative inverse in the ambient ring. -/
theorem isRelativeInverse_lift {U : Type*} [Ring U] [StarRing U] (S : StarSubring U)
    {x y : S} (h : IsRelativeInverse x y) : IsRelativeInverse (x : U) (y : U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val h.left
  · exact congrArg Subtype.val h.right
  · exact congrArg Subtype.val h.star_left
  · exact congrArg Subtype.val h.star_right

theorem starRegularClosure_le {U : Type*} [Ring U] [StarRing U] [IsStarRegular U] {R S : StarSubring U}
    [IsStarRegular S] (hR : (R : Set U) ⊆ (S : Set U)) :
    (starRegularClosure R : Set U) ⊆ (S : Set U) := by
  have key : ∀ n, (starRegularChain R n : Set U) ⊆ (S : Set U) := by
    intro n
    induction n with
    | zero => exact hR
    | succ n ih =>
      have hstep :
          ((starRegularChain R n : Set U) ∪ relativeInverses (starRegularChain R n : Set U))
            ⊆ (S : Set U) := by
        intro x hx
        rcases hx with hx | hx
        · exact ih hx
        · rcases hx with ⟨a, ha, hay⟩
          obtain ⟨z, hz⟩ := exists_isRelativeInverse_aux (U := S) ⟨a, ih ha⟩
          have hz' : IsRelativeInverse a (z : U) := isRelativeInverse_lift S hz
          have hxz : x = (z : U) := isRelativeInverse_unique_aux hay hz'
          rw [hxz]
          exact z.2
      exact starSubringClosure_le hstep
  show (starSubringClosure (⋃ n, (starRegularChain R n : Set U)) : Set U) ⊆ (S : Set U)
  exact starSubringClosure_le fun x hx => by
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    exact key n hn

end Work.ORHughesFree.StarRegular
