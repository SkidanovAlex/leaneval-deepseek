import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.no_two_torsion_fixingSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary theory for `involutions_eq_one_or_conjugate`
-/

namespace Work.SSGRoute
namespace InvAux

open TwoTorsion

variable {Ω : Type*} [Field Ω]

/-- The fixed field of an involutive ring automorphism `c`. -/
def fixSub (c : Ω ≃+* Ω) : Subfield Ω where
  carrier := {x | c x = x}
  mul_mem' := by intro a b ha hb; show c (a * b) = a * b; rw [map_mul, ha, hb]
  one_mem' := by show c 1 = 1; simp
  add_mem' := by intro a b ha hb; show c (a + b) = a + b; rw [map_add, ha, hb]
  zero_mem' := by show c 0 = 0; simp
  neg_mem' := by intro a ha; show c (-a) = -a; rw [map_neg, ha]
  inv_mem' := by intro a ha; show c a⁻¹ = a⁻¹; rw [map_inv₀, ha]

@[simp] lemma mem_fixSub {c : Ω ≃+* Ω} {x : Ω} : x ∈ fixSub c ↔ c x = x := Iff.rfl

/-- Any element of `Ω` is at most quadratic over `F = Ω^c`. -/
lemma exists_quadratic {c : Ω ≃+* Ω} [CharZero Ω] (hc : c * c = 1) (x : Ω) :
    ∃ a : Ω, c a = a ∧ ∃ e : Ω, c e = e ∧ (x - a) ^ 2 = e := by
  refine ⟨(x + c x) / 2, ?_, ((x - c x) / 2) ^ 2, ?_, ?_⟩
  · rw [map_div₀, map_add, apply_apply hc x, map_ofNat, div_eq_mul_inv, div_eq_mul_inv]
    ring
  · rw [map_pow, map_div₀, map_sub, apply_apply hc x, map_ofNat, div_eq_mul_inv,
        div_eq_mul_inv]
    ring
  · rw [div_eq_mul_inv]
    field_simp
    ring


section Minpoly

variable {c : Ω ≃+* Ω}

/-- `x` satisfies a monic quadratic over `F = Ω^c`, so `minpoly F x` has degree at most two. -/
theorem minpoly_natDegree_le_two [CharZero Ω] (hc : c * c = 1) (x : Ω) :
    (minpoly ↥(fixSub c) x).natDegree ≤ 2 := by
  obtain ⟨a, ha, e, he, hq⟩ := exists_quadratic hc x
  let aF : ↥(fixSub c) := ⟨a, ha⟩
  let eF : ↥(fixSub c) := ⟨e, he⟩
  have hcoea : algebraMap ↥(fixSub c) Ω aF = a := rfl
  have hcoee : algebraMap ↥(fixSub c) Ω eF = e := rfl
  let q : Polynomial (↥(fixSub c)) :=
    Polynomial.X ^ 2 - Polynomial.C (2 * aF) * Polynomial.X + Polynomial.C (aF ^ 2 - eF)
  have hroot : (Polynomial.aeval x) q = 0 := by
    show (Polynomial.aeval x) (Polynomial.X ^ 2 - Polynomial.C (2 * aF) * Polynomial.X
      + Polynomial.C (aF ^ 2 - eF)) = 0
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      map_ofNat, hcoea, hcoee]
    linear_combination hq
  have hne : q ≠ 0 := by
    have h2 : q.natDegree = 2 := by
      show (Polynomial.X ^ 2 - Polynomial.C (2 * aF) * Polynomial.X
        + Polynomial.C (aF ^ 2 - eF)).natDegree = 2
      compute_degree!
    intro h; rw [h] at h2; simp at h2
  have hdeg : q.natDegree ≤ 2 := by
    show (Polynomial.X ^ 2 - Polynomial.C (2 * aF) * Polynomial.X
      + Polynomial.C (aF ^ 2 - eF)).natDegree ≤ 2
    compute_degree
  exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd ↥(fixSub c) x hroot) hne).trans hdeg





section Cone

variable {c : Ω ≃+* Ω} [IsAlgClosed Ω] [CharZero Ω]

@[simp] lemma coe_addF (x y : ↥(fixSub c)) :
    ((x + y : ↥(fixSub c)) : Ω) = (x : Ω) + (y : Ω) := rfl
@[simp] lemma coe_mulF (x y : ↥(fixSub c)) :
    ((x * y : ↥(fixSub c)) : Ω) = (x : Ω) * (y : Ω) := rfl
@[simp] lemma coe_negF (x : ↥(fixSub c)) : ((-x : ↥(fixSub c)) : Ω) = -(x : Ω) := rfl
@[simp] lemma coe_subF (x y : ↥(fixSub c)) :
    ((x - y : ↥(fixSub c)) : Ω) = (x : Ω) - (y : Ω) := rfl
@[simp] lemma coe_zeroF : ((0 : ↥(fixSub c)) : Ω) = 0 := rfl
@[simp] lemma coe_oneF : ((1 : ↥(fixSub c)) : Ω) = 1 := rfl

lemma coe_eq_zero {x : ↥(fixSub c)} : x = 0 ↔ (x : Ω) = 0 := by
  rw [Subtype.ext_iff, coe_zeroF]

lemma notMem_normSet_neg (hc : c * c = 1) (hneg : (-1 : Ω) ∉ normSet c)
    {x : Ω} (hx : x ∈ normSet c) : -x ∉ normSet c := by
  intro h
  obtain ⟨m, hm, hm0, hxm⟩ := exists_fixed_sq_of_mem_normSet hc hx
  obtain ⟨m', hm', hm'0, hxm'⟩ := exists_fixed_sq_of_mem_normSet hc h
  have hmm : m ^ 2 + m' ^ 2 = 0 := by
    have h1 : m ^ 2 = x := hxm.symm
    have h2 : m' ^ 2 = -x := hxm'.symm
    rw [h1, h2]; ring
  have h3 : m ^ 2 = -(m' ^ 2) := add_eq_zero_iff_eq_neg.mp hmm
  have hmi : (m * m'⁻¹) ^ 2 = -1 := by
    rw [mul_pow, h3, inv_pow, neg_mul, mul_inv_cancel₀ (pow_ne_zero 2 hm'0)]
  apply hneg
  have hfix : c (m * m'⁻¹) = m * m'⁻¹ := by rw [map_mul, map_inv₀, hm, hm']
  refine ⟨m * m'⁻¹, mul_ne_zero hm0 (inv_ne_zero hm'0), ?_⟩
  rw [hfix, ← pow_two, hmi]

/-- The "positivity cone" on the fixed field of `c`. -/
def cone (x : ↥(fixSub c)) : Prop := (x : Ω) = 0 ∨ (x : Ω) ∈ normSet c

lemma cone_zero : cone (0 : ↥(fixSub c)) := by rw [cone]; exact Or.inl (by simp)

lemma cone_one (hc : c * c = 1) : cone (1 : ↥(fixSub c)) :=
  Or.inr (by simpa using one_mem_normSet c)

lemma cone_add (hc : c * c = 1) (hneg : (-1 : Ω) ∉ normSet c)
    {x y : ↥(fixSub c)} (hx : cone x) (hy : cone y) : cone (x + y) := by
  rw [cone] at hx hy ⊢
  simp only [coe_addF]
  rcases hx with hx | hx
  · rw [hx, zero_add]; exact hy
  rcases hy with hy | hy
  · rw [hy, add_zero]; exact Or.inr hx
  · exact Or.inr (add_mem_normSet c hc hneg hx hy)

lemma cone_mul {x y : ↥(fixSub c)} (hx : cone x) (hy : cone y) : cone (x * y) := by
  rw [cone] at hx hy ⊢
  simp only [coe_mulF]
  rcases hx with hx | hx
  · rw [hx, zero_mul]; exact Or.inl rfl
  rcases hy with hy | hy
  · rw [hy, mul_zero]; exact Or.inl rfl
  · exact Or.inr (normSet.mul_mem hx hy)

lemma cone_or_neg {x : ↥(fixSub c)} : cone x ∨ cone (-x) := by
  rcases eq_or_ne x 0 with h | h
  · left; rw [h]; exact cone_zero
  · have hx0 : (x : Ω) ≠ 0 := fun hx => h (coe_eq_zero.mpr hx)
    rw [cone, cone]
    rcases mem_or_neg_mem_normSet (c := c) (a := (x : Ω)) x.2 hx0 with h' | h'
    · exact Or.inl (Or.inr h')
    · exact Or.inr (Or.inr (by simpa using h'))

lemma cone_antisymm (hc : c * c = 1) (hneg : (-1 : Ω) ∉ normSet c)
    {x : ↥(fixSub c)} (hx : cone x) (hx' : cone (-x)) : x = 0 := by
  rw [cone] at hx hx'
  simp only [coe_negF] at hx'
  rcases hx with hx | hx
  · exact coe_eq_zero.mpr hx
  rcases hx' with hx' | hx'
  · exact coe_eq_zero.mpr (neg_eq_zero.mp hx')
  · exact absurd hx' (notMem_normSet_neg hc hneg hx)

end Cone

section Order

variable {c : Ω ≃+* Ω} [IsAlgClosed Ω] [CharZero Ω]

lemma cone_ne_zero_of_cone {x : ↥(fixSub c)} (hx : cone x) (hx' : ¬ cone (-x)) : x ≠ 0 :=
  fun h => hx' (by rw [h, neg_zero]; exact cone_zero)

lemma cone_of_cone_mul (hc : c * c = 1) {a z : ↥(fixSub c)} (ha : cone a) (ha0 : a ≠ 0)
    (h : cone (a * z)) : cone z := by
  rw [cone] at ha h ⊢
  simp only [coe_mulF] at h
  rcases ha with ha | ha
  · exact absurd (coe_eq_zero.mpr ha) ha0
  rcases h with h | h
  · left
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (coe_eq_zero.mpr h1) ha0
    · exact h1
  · obtain ⟨u, hu, hu0, hau⟩ := exists_fixed_sq_of_mem_normSet hc ha
    obtain ⟨m, hm, hm0, hzm⟩ := exists_fixed_sq_of_mem_normSet hc h
    have h1 : (u : Ω) ^ 2 * (z : Ω) = (m : Ω) ^ 2 := by rw [← hau]; exact hzm
    have hu2 : (u : Ω) ^ 2 ≠ 0 := pow_ne_zero 2 hu0
    have h2 : (z : Ω) = ((u : Ω) ^ 2)⁻¹ * (m : Ω) ^ 2 := by
      rw [← h1, ← mul_assoc, inv_mul_cancel₀ hu2, one_mul]
    right
    refine ⟨m * u⁻¹, mul_ne_zero hm0 (inv_ne_zero hu0), ?_⟩
    have hfix : c (m * u⁻¹) = m * u⁻¹ := by rw [map_mul, map_inv₀, hm, hu]
    rw [hfix, h2, ← inv_pow]
    ring

noncomputable instance instFixLinearOrder [Fact (c * c = 1)] [Fact (c ≠ 1)] :
    LinearOrder ↥(fixSub c) where
  le x y := cone (y - x)
  le_refl x := by
    show cone (x - x)
    rw [sub_self]; exact cone_zero
  le_trans x y z hxy hyz := by
    show cone (z - x)
    rw [show z - x = (z - y) + (y - x) from by ring]
    exact cone_add (Fact.out : c * c = 1)
      (neg_one_notMem_normSet c (Fact.out : c * c = 1) (Fact.out : c ≠ 1)) hyz hxy
  le_antisymm x y hxy hyx := by
    have h2 : cone (-(y - x)) := by
      rw [show -(y - x) = x - y from by ring]; exact hyx
    exact (sub_eq_zero.mp (cone_antisymm (Fact.out : c * c = 1)
      (neg_one_notMem_normSet c (Fact.out : c * c = 1) (Fact.out : c ≠ 1)) hxy h2)).symm
  le_total x y := by
    rcases cone_or_neg (c := c) (x := y - x) with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [show x - y = -(y - x) from by ring]; exact h)
  toDecidableLE x y := Classical.dec _
  toDecidableEq := Classical.decEq _
  toDecidableLT x y := Classical.dec _

lemma lt_iff_cone [Fact (c * c = 1)] [Fact (c ≠ 1)] (x y : ↥(fixSub c)) : x < y ↔ cone (y - x) ∧ ¬ cone (x - y) := by
  rw [lt_iff_le_not_ge]; rfl

noncomputable instance instFixIsStrictOrderedRing [Fact (c * c = 1)] [Fact (c ≠ 1)] :
    IsStrictOrderedRing ↥(fixSub c) where
  add_le_add_left a b hab d := by
    show cone ((b + d) - (a + d))
    rw [show (b + d) - (a + d) = b - a from by ring]; exact hab
  le_of_add_le_add_left a b d h := by
    show cone (d - b)
    rw [show d - b = (a + d) - (a + b) from by ring]; exact h
  zero_le_one := by
    show cone ((1 : ↥(fixSub c)) - 0)
    rw [sub_zero]; exact cone_one (Fact.out : c * c = 1)
  mul_lt_mul_of_pos_left := fun {a} ha {b} {d} hbd => by
    rw [lt_iff_cone] at ha hbd ⊢
    simp only [sub_zero, zero_sub] at ha
    have ha1 : cone a := ha.1
    have ha0 : a ≠ 0 := cone_ne_zero_of_cone ha1 ha.2
    refine ⟨?_, ?_⟩
    · rw [show a * d - a * b = a * (d - b) from by ring]
      exact cone_mul ha1 hbd.1
    · rw [show a * b - a * d = a * (b - d) from by ring]
      intro hb
      exact hbd.2 (cone_of_cone_mul (Fact.out : c * c = 1) ha1 ha0 hb)
  mul_lt_mul_of_pos_right := fun {d} hd {a} {b} hab => by
    rw [lt_iff_cone] at hd hab ⊢
    simp only [sub_zero, zero_sub] at hd
    have hd1 : cone d := hd.1
    have hd0 : d ≠ 0 := cone_ne_zero_of_cone hd1 hd.2
    refine ⟨?_, ?_⟩
    · rw [show b * d - a * d = (b - a) * d from by ring]
      exact cone_mul hab.1 hd1
    · intro hb
      refine hab.2 ?_
      have hb' : cone (d * (a - b)) := by
        rw [show d * (a - b) = a * d - b * d from by ring]; exact hb
      exact cone_of_cone_mul (Fact.out : c * c = 1) hd1 hd0 hb'

end Order


end Minpoly

end InvAux
end Work.SSGRoute
