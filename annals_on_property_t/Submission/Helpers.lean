import ChallengeDeps
import Mathlib.Algebra.MonoidAlgebra.Defs

open OnPropertyT
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Helpers

noncomputable section

variable {G : Type*} [Group G]

lemma star_def (x : MonoidAlgebra ℝ G) :
    star x = MonoidAlgebra.mapDomain (fun g : G => g⁻¹) x := rfl

-- star of a monoid-algebra element is mapDomain by inversion
lemma star_coeff (x : MonoidAlgebra ℝ G) (g : G) :
    (star x).coeff g = x.coeff g⁻¹ := by
  rw [star_def]
  simpa using
    (Finsupp.mapDomain_apply_of_injective (f := fun h : G => h⁻¹) inv_injective x.coeff (g⁻¹))

lemma star_single (g : G) (r : ℝ) : star (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r := by
  classical
  ext h
  rw [star_coeff]
  change (Finsupp.single g r) h⁻¹ = (Finsupp.single g⁻¹ r) h
  rw [Finsupp.single_apply, Finsupp.single_apply]
  by_cases hg : g = h⁻¹
  · have hg2 : g⁻¹ = h := by simpa using congrArg (fun t : G => t⁻¹) hg
    simp [hg, hg2]
  · have hg2 : g⁻¹ ≠ h := by
      intro hh
      exact hg (by simpa using congrArg (fun t : G => t⁻¹) hh)
    simp [hg, hg2]

lemma star_of (g : G) : star (MonoidAlgebra.of ℝ G g) = MonoidAlgebra.of ℝ G g⁻¹ := by
  simp [MonoidAlgebra.of, star_single]

lemma star_one : star (1 : MonoidAlgebra ℝ G) = 1 := by
  classical
  ext g
  rw [star_coeff]
  change (Finsupp.single (1 : G) (1 : ℝ)) g⁻¹ = (Finsupp.single (1 : G) (1 : ℝ)) g
  rw [Finsupp.single_apply, Finsupp.single_apply]
  by_cases hg : g = 1
  · subst g
    simp
  · have hsym : (1 : G) ≠ g := fun h => hg h.symm
    simp [hg, hsym]

lemma star_star (x : MonoidAlgebra ℝ G) : star (star x) = x := by
  ext g
  rw [star_coeff, star_coeff, inv_inv]

lemma star_add (x y : MonoidAlgebra ℝ G) : star (x + y) = star x + star y := by
  rw [star_def, star_def, star_def]
  exact MonoidAlgebra.mapDomain_add (fun g : G => g⁻¹) x y

lemma star_neg (x : MonoidAlgebra ℝ G) : star (-x) = -star x := by
  ext g
  rw [star_coeff]
  simp [star_coeff, Finsupp.neg_apply]

lemma star_sub (x y : MonoidAlgebra ℝ G) : star (x - y) = star x - star y := by
  ext g
  rw [star_coeff]
  simp [star_coeff, Finsupp.sub_apply]


lemma star_zero : star (0 : MonoidAlgebra ℝ G) = 0 := by
  ext g; simp [star_coeff]

lemma star_sum {ι : Type*} (s : Finset ι) (f : ι → MonoidAlgebra ℝ G) :
    star (∑ i ∈ s, f i) = ∑ i ∈ s, star (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [star_zero]
  | insert a s ha ih =>
      simp [ha, Finset.sum_insert, star_add, ih]

lemma sum_star_support {β : Type*} [AddCommMonoid β] (z : MonoidAlgebra ℝ G) (f : G → β) :
    (∑ a ∈ (star z).coeff.support, f a) = ∑ a ∈ z.coeff.support, f a⁻¹ := by
  classical
  change (∑ a ∈ (Finsupp.mapDomain (fun a : G => a⁻¹) z.coeff).support, f a) = ∑ a ∈ z.coeff.support, f a⁻¹
  rw [Finsupp.mapDomain_support_of_injective (f := fun a : G => a⁻¹) inv_injective z.coeff]
  rw [Finset.sum_image]
  exact fun x hx y hy hxy => inv_injective hxy

private lemma inv_mul_inv_eq_iff (w u g : G) : (w⁻¹ * u⁻¹ = g) ↔ (u * w = g⁻¹) := by
  constructor
  · intro h
    have h' := congrArg (fun t : G => t⁻¹) h
    simpa [mul_inv_rev] using h'
  · intro h
    have h' := congrArg (fun t : G => t⁻¹) h
    simpa [mul_inv_rev] using h'

/-- `star` is an anti-homomorphism for the group ring: `star (x*y) = star y * star x`. -/
lemma star_mul (x y : MonoidAlgebra ℝ G) : star (x * y) = star y * star x := by
  classical
  ext g
  rw [star_coeff]
  rw [MonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  simp_rw [star_coeff]
  rw [show (∑ a ∈ (star y).coeff.support, ∑ b ∈ (star x).coeff.support,
              if a * b = g then y.coeff a⁻¹ * x.coeff b⁻¹ else 0)
        = ∑ w ∈ y.coeff.support, ∑ b ∈ (star x).coeff.support,
              if w⁻¹ * b = g then y.coeff w * x.coeff b⁻¹ else 0 by
    rw [sum_star_support y (fun a => ∑ b ∈ (star x).coeff.support,
              if a * b = g then y.coeff a⁻¹ * x.coeff b⁻¹ else 0)]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [inv_inv]]
  conv =>
    lhs
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [show (∑ b ∈ (star x).coeff.support, if w⁻¹ * b = g then y.coeff w * x.coeff b⁻¹ else 0)
        = ∑ u ∈ x.coeff.support, if u * w = g⁻¹ then x.coeff u * y.coeff w else 0 by
    rw [sum_star_support x (fun b => if w⁻¹ * b = g then y.coeff w * x.coeff b⁻¹ else 0)]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [inv_inv]
    rw [inv_mul_inv_eq_iff, mul_comm]]

lemma star_pow (x : MonoidAlgebra ℝ G) (n : ℕ) : star (x ^ n) = (star x) ^ n := by
  classical
  induction n with
  | zero => simp [star_one]
  | succ n ih =>
      rw [pow_succ']
      rw [star_mul, ih]
      rw [pow_succ]


lemma star_smul (r : ℝ) (x : MonoidAlgebra ℝ G) : star (r • x) = r • star x := by
  ext g
  rw [star_coeff]
  change (r • x.coeff) g⁻¹ = (r • (star x).coeff) g
  rw [Finsupp.smul_apply, Finsupp.smul_apply, star_coeff]

lemma star_natCast (n : ℕ) : star (n : MonoidAlgebra ℝ G) = (n : MonoidAlgebra ℝ G) := by
  classical
  ext g
  by_cases hg : g = 1
  · subst g; simp [star_coeff, Finsupp.single_apply]
  · have hg' : g⁻¹ ≠ 1 := fun h => hg (by simpa using congrArg (fun t : G => t⁻¹) h)
    simp [star_coeff, Finsupp.single_apply, hg, hg']


section HomMap

variable {H : Type*} [Group H]

lemma mapDomain_mapDomain {H' : Type*} (f : G → H) (g : H → H')
    (x : MonoidAlgebra ℝ G) :
    MonoidAlgebra.mapDomain g (MonoidAlgebra.mapDomain f x) = MonoidAlgebra.mapDomain (g ∘ f) x := by
  classical
  ext c
  simp [MonoidAlgebra.mapDomain, ← Finsupp.mapDomain_comp]

lemma mapDomain_hom_one (f : G →* H) :
    MonoidAlgebra.mapDomain f (1 : MonoidAlgebra ℝ G) = (1 : MonoidAlgebra ℝ H) := by
  simpa using (MonoidAlgebra.mapDomain_one (R := ℝ) f)

lemma mapDomain_hom_mul (f : G →* H) (x y : MonoidAlgebra ℝ G) :
    MonoidAlgebra.mapDomain f (x * y) = MonoidAlgebra.mapDomain f x * MonoidAlgebra.mapDomain f y := by
  simpa using (MonoidAlgebra.mapDomain_mul (R := ℝ) f x y)

lemma mapDomain_hom_star (f : G →* H) (x : MonoidAlgebra ℝ G) :
    star (MonoidAlgebra.mapDomain f x) = MonoidAlgebra.mapDomain f (star x) := by
  classical
  calc
    star (MonoidAlgebra.mapDomain f x)
        = MonoidAlgebra.mapDomain (fun h : H => h⁻¹) (MonoidAlgebra.mapDomain f x) := star_def _
    _ = MonoidAlgebra.mapDomain ((fun h : H => h⁻¹) ∘ f) x := by
          rw [mapDomain_mapDomain]
    _ = MonoidAlgebra.mapDomain (f ∘ (fun g : G => g⁻¹)) x := by
          congr 1
          funext g
          exact (f.map_inv g).symm
    _ = MonoidAlgebra.mapDomain f (MonoidAlgebra.mapDomain (fun g : G => g⁻¹) x) := by
          rw [mapDomain_mapDomain]
    _ = MonoidAlgebra.mapDomain f (star x) := by
          rw [star_def]

lemma mapDomain_hom_pow (f : G →* H) (x : MonoidAlgebra ℝ G) (n : ℕ) :
    MonoidAlgebra.mapDomain f (x ^ n) = (MonoidAlgebra.mapDomain f x) ^ n := by
  classical
  induction n with
  | zero => simp [mapDomain_hom_one]
  | succ n ih =>
      rw [pow_succ, pow_succ, mapDomain_hom_mul, ih]

lemma mapDomain_hom_add (f : G →* H) (x y : MonoidAlgebra ℝ G) :
    MonoidAlgebra.mapDomain f (x + y) = MonoidAlgebra.mapDomain f x + MonoidAlgebra.mapDomain f y := by
  simpa using (MonoidAlgebra.mapDomain_add (R := ℝ) f x y)

lemma mapDomain_hom_neg (f : G →* H) (x : MonoidAlgebra ℝ G) :
    MonoidAlgebra.mapDomain f (-x) = -MonoidAlgebra.mapDomain f x := by
  classical
  refine (eq_neg_iff_add_eq_zero).2 ?_
  rw [← MonoidAlgebra.mapDomain_add]
  rw [neg_add_cancel, MonoidAlgebra.mapDomain_zero]

lemma mapDomain_hom_sub (f : G →* H) (x y : MonoidAlgebra ℝ G) :
    MonoidAlgebra.mapDomain f (x - y) = MonoidAlgebra.mapDomain f x - MonoidAlgebra.mapDomain f y := by
  classical
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [mapDomain_hom_add, mapDomain_hom_neg]

lemma mapDomain_hom_natCast (f : G →* H) (n : ℕ) :
    MonoidAlgebra.mapDomain f (n : MonoidAlgebra ℝ G) = (n : MonoidAlgebra ℝ H) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, mapDomain_hom_add, ih]
      simp [mapDomain_hom_one]

end HomMap


lemma mapDomain_sum_finset {H : Type*} (f : G → H) (S : Finset G) (v : G → MonoidAlgebra ℝ G) :
    MonoidAlgebra.mapDomain f (∑ s ∈ S, v s) = ∑ s ∈ S, MonoidAlgebra.mapDomain f (v s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [MonoidAlgebra.mapDomain_add, ih]

lemma mapDomain_of_apply (f : G → G) (g : G) :
    MonoidAlgebra.mapDomain f (MonoidAlgebra.of ℝ G g) = MonoidAlgebra.of ℝ G (f g) := by
  simp [MonoidAlgebra.of, MonoidAlgebra.mapDomain_single]

end

end Submission.Helpers
