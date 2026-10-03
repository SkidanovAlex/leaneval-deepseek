/-
# `Submission.Work.FITop4.Red5.primary_setup`

Vocabulary and elementary Gaussian arithmetic underlying the **primary reduction** of
Friedlander–Iwaniec (5.2): the identity
`Σ_{|w|²=m} Σ_{|z|²=n} Z(Re wz) = 4 · Σ_{|w|²=m} Σ_{z primary, |z|²=n} Z(Re wz)`
for `m ≥ 1` and `n` odd — the factor `4` "accounting for the four units `1, i, i², i³`" of
`ℤ[i]` (paper, p. 967).

The reduction has two independent halves, separated here:

* the **sphere** `|z|² = n` is invariant under multiplication by a unit, and its summands are
  unit-invariant because multiplication by a unit permutes the sphere `|w|² = m` (this file:
  `mul_unit_mem_sph`, `image_mul_unit_sph`, `sum_sph_mul_unit`);
* the sphere splits into `4`-element orbits, each containing exactly one primary element
  (`sphere_decomposition` in `Submission.Work.FITop4.Red5.sphere_decomposition`), so that
  `Σ_{|z|²=n} g z = 4 Σ_{z primary} g z` for any unit-invariant `g`.

Everything is stated in terms of the frozen vocabulary of `Submission.Work.FIPlan.Interface`.
-/
import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The sphere and the four units -/

/-- The **sphere** `|z|² = m` of Gaussian integers, cut out of the box `gBox m` so that the
summation is finite. -/
def sph (m : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m)

/-- The **primary** part of the sphere `|z|² = n`. -/
def sphPrim (n : ℕ) : Finset GaussianInt :=
  (sph n).filter (fun z => Work.FIPlan.IsPrimary z)

/-- The four units `1, -1, i, -i` of `ℤ[i]`, as a finset. -/
def units4 : Finset GaussianInt :=
  {1, -1, (⟨0, 1⟩ : GaussianInt), (⟨0, -1⟩ : GaussianInt)}

/-! ## 1. Elementary facts about the Gaussian norm -/

/-- `|zw|² = |z|² |w|²`. -/
lemma gnorm_mul (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  rw [Work.FIPlan.gnorm, Work.FIPlan.gnorm, Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `|z|² = (re z)² + (im z)²` as integers. -/
lemma gnorm_int (z : GaussianInt) : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  rw [Work.FIPlan.gnorm, Zsqrtd.norm_def]
  have h : z.re * z.re - -1 * z.im * z.im = z.re ^ 2 + z.im ^ 2 := by ring
  rw [h]
  exact Int.natAbs_of_nonneg (by positivity)

/-- A unit has norm one. -/
lemma gnorm_unit {u : GaussianInt} (hu : IsUnit u) : Work.FIPlan.gnorm u = 1 :=
  Zsqrtd.norm_eq_one_iff.mpr hu

/-- `|0|² = 0`. -/
lemma gnorm_zero : Work.FIPlan.gnorm (0 : GaussianInt) = 0 := by
  rw [Work.FIPlan.gnorm]
  simp

/-! ## 2. Membership in the box -/

/-- Membership in `gBox R`, in coordinates. -/
lemma mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    exact hp
  · rintro ⟨h1, h2⟩
    refine ⟨(z.re, z.im), ?_, ?_⟩
    · rw [Finset.product_eq_sprod]
      exact Finset.mem_product.mpr ⟨h1, h2⟩
    · ext <;> rfl

/-- **The sphere sits in the box**: `|z|² = R` implies `z ∈ gBox R`. -/
lemma mem_gBox_of_gnorm_eq {R : ℕ} {z : GaussianInt} (h : Work.FIPlan.gnorm z = R) :
    z ∈ Work.FIPlan.gBox ((R : ℕ) : ℤ) := by
  rw [mem_gBox_iff, Finset.mem_Icc, Finset.mem_Icc]
  have hz : (Work.FIPlan.gnorm z : ℤ) = (R : ℤ) := by rw [h]
  have hsq : ∀ a : ℤ, a = z.re ∨ a = z.im → a * a ≤ (R : ℤ) := by
    intro a ha
    have h1 := gnorm_int z
    rw [hz] at h1
    rcases ha with rfl | rfl <;> nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]
  have hRR : (R : ℤ) ≤ (R : ℤ) * (R : ℤ) := by
    rcases Nat.eq_zero_or_pos R with h0 | h1
    · subst h0; norm_num
    · have h2 : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast h1
      nlinarith
  have key : ∀ a : ℤ, a * a ≤ (R : ℤ) → -((R : ℤ)) ≤ a ∧ a ≤ (R : ℤ) := by
    intro a ha
    have h2 : a ^ 2 ≤ (R : ℤ) ^ 2 := by
      simpa only [sq] using le_trans ha hRR
    have h3 : |a| ≤ |((R : ℤ))| := sq_le_sq.mp h2
    have h4 : |((R : ℤ))| = ((R : ℤ)) := abs_of_nonneg (Nat.cast_nonneg R)
    rw [h4] at h3
    exact abs_le.mp h3
  exact ⟨key z.re (hsq z.re (Or.inl rfl)), key z.im (hsq z.im (Or.inr rfl))⟩

/-! ## 3. The four units -/

/-- Every element of `units4` is a unit of `ℤ[i]`. -/
lemma isUnit_of_mem_units4 {u : GaussianInt} (hu : u ∈ units4) : IsUnit u := by
  simp only [units4, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact isUnit_one
  · exact isUnit_neg_one
  · exact (Commons.NumberTheory.GaussianInt.units_classification _).mpr
      (Or.inr (Or.inr (Or.inl rfl)))
  · exact (Commons.NumberTheory.GaussianInt.units_classification _).mpr
      (Or.inr (Or.inr (Or.inr rfl)))

/-- The four units are four distinct elements. -/
lemma units4_card : units4.card = 4 := by decide

/-! ## 4. The sphere is stable under multiplication by a unit, and the `w`-sum is
unit-invariant -/

/-- `|w|² = m` and `u` a unit imply `|wu|² = m`; and `wu` stays in the box. -/
lemma mul_unit_mem_sph {m : ℕ} {w : GaussianInt} (hw : w ∈ sph m)
    {u : GaussianInt} (hu : IsUnit u) : w * u ∈ sph m := by
  have hwn : Work.FIPlan.gnorm w = m := (Finset.mem_filter.mp hw).2
  have hgn : Work.FIPlan.gnorm (w * u) = m := by
    rw [gnorm_mul, hwn, gnorm_unit hu, mul_one]
  rw [sph, Finset.mem_filter]
  exact ⟨mem_gBox_of_gnorm_eq hgn, hgn⟩

/-- Multiplication by a unit permutes the sphere `|w|² = m`. -/
lemma image_mul_unit_sph (m : ℕ) {u : GaussianInt} (hu : IsUnit u) :
    (sph m).image (fun w => w * u) = sph m := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact mul_unit_mem_sph hw hu
  · intro x hx
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : v * u = 1 := by rw [mul_comm, hv]
    have hvunit : IsUnit v := ⟨⟨v, u, hv', hv⟩, rfl⟩
    refine Finset.mem_image.mpr ⟨x * v, mul_unit_mem_sph hx hvunit, ?_⟩
    rw [mul_assoc, hv', mul_one]

/-- **The `w`-sum is invariant under `z ↦ zu`** (`u` a unit): substituting `w ↦ wu` and using
that multiplication by `u` permutes the sphere `|w|² = m`.  This is the only place where the outer
summation enters the primary reduction. -/
lemma sum_sph_mul_unit (m : ℕ) (F : ℕ → ℝ) {z u : GaussianInt} (hu : IsUnit u) :
    (∑ w ∈ sph m, F (Work.FIPlan.gnorm (z * u)) *
        (Work.FIPlan.Zint (Work.FIPlan.cForm w (z * u)) : ℝ))
      = ∑ w ∈ sph m, F (Work.FIPlan.gnorm z) *
          (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
  have hgu : Work.FIPlan.gnorm u = 1 := gnorm_unit hu
  have hzn : Work.FIPlan.gnorm (z * u) = Work.FIPlan.gnorm z := by
    rw [gnorm_mul, hgu, mul_one]
  have hc : ∀ w : GaussianInt,
      Work.FIPlan.cForm w (z * u) = Work.FIPlan.cForm (w * u) z := by
    intro w
    show (w * (z * u)).re = ((w * u) * z).re
    congr 1
    ring
  have hinj : Set.InjOn (fun w : GaussianInt => w * u) ↑(sph m) := by
    intro a _ b _ hab
    exact mul_right_cancel₀ (IsUnit.ne_zero hu) hab
  calc ∑ w ∈ sph m, F (Work.FIPlan.gnorm (z * u)) *
          (Work.FIPlan.Zint (Work.FIPlan.cForm w (z * u)) : ℝ)
      = ∑ w ∈ sph m, F (Work.FIPlan.gnorm z) *
          (Work.FIPlan.Zint (Work.FIPlan.cForm (w * u) z) : ℝ) := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [hzn, hc w]
    _ = ∑ x ∈ (sph m).image (fun w => w * u),
          F (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm x z) : ℝ) :=
        (Finset.sum_image (s := sph m) (g := fun w : GaussianInt => w * u)
          (f := fun x : GaussianInt => F (Work.FIPlan.gnorm z) *
            (Work.FIPlan.Zint (Work.FIPlan.cForm x z) : ℝ)) hinj).symm
    _ = ∑ x ∈ sph m, F (Work.FIPlan.gnorm z) *
          (Work.FIPlan.Zint (Work.FIPlan.cForm x z) : ℝ) := by
        rw [image_mul_unit_sph m hu]

/-! ## 5. The primary condition and the uniqueness of the primary associate -/

/-- The primary condition `z ≡ 1 (mod 2(1+i))` (paper (5.3)–(5.5)) in coordinates modulo `4`. -/
lemma isPrimary_iff_zmod (w : GaussianInt) :
    Work.FIPlan.IsPrimary w ↔
      Odd w.re ∧ Even w.im ∧ (w.im : ZMod 4) = ((w.re : ZMod 4) - 1) := by
  unfold Work.FIPlan.IsPrimary
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have hcast : ((w.im : ℤ) : ZMod 4) = (((w.re - 1 : ℤ)) : ZMod 4) :=
      (ZMod.intCast_eq_intCast_iff _ _ 4).mpr h3
    rw [hcast]
    push_cast
    ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have hcast : ((w.im : ℤ) : ZMod 4) = (((w.re - 1 : ℤ)) : ZMod 4) := by
      rw [h3]
      push_cast
      ring
    exact (ZMod.intCast_eq_intCast_iff _ _ 4).mp hcast

/-- **Uniqueness of the primary associate**: two primary elements associated to the same nonzero
`z` of odd norm coincide (immediate from `primary_associate_exists_unique`). -/
lemma eq_of_primary_associated {y z : GaussianInt} (hz : z ≠ 0)
    (hodd : Odd (Work.FIPlan.gnorm z)) (hy : Work.FIPlan.IsPrimary y)
    (hyassoc : Associated y z) {w : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hwassoc : Associated w z) : y = w := by
  obtain ⟨-, huniq⟩ := Classical.choose_spec
    (Commons.NumberTheory.GaussianInt.primary_associate_exists_unique (z := z) hz hodd)
  exact (huniq y ⟨hyassoc, (isPrimary_iff_zmod y).mp hy⟩).trans
    (huniq w ⟨hwassoc, (isPrimary_iff_zmod w).mp hw⟩).symm

/-! ## 6. Two consequences of the membership description of the sphere -/

/-- The norm on the sphere is `m`. -/
lemma sph_gnorm {m : ℕ} {w : GaussianInt} (hw : w ∈ sph m) : Work.FIPlan.gnorm w = m :=
  (Finset.mem_filter.mp hw).2

/-- A nonzero element of the sphere of odd norm: the primary decomposition applies to it. -/
lemma sph_ne_zero {n : ℕ} (hn : Odd n) {z : GaussianInt} (hz : z ∈ sph n) : z ≠ 0 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hn
    omega
  have hzn := sph_gnorm hz
  rintro rfl
  rw [gnorm_zero] at hzn
  exact hn0 hzn.symm

end

end Work.FITop4.Red5
