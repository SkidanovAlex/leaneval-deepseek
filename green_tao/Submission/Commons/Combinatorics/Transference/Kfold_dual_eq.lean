import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Combinatorics.Additive.AP.sum_translate_tuple

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Linearity of the cube embedding `ω ↦ ∑ i, (if ω i then h i else 0)`: shifting the
`d`-tuple `h` by the `d`-tuple `H` shifts each cube vertex by the corresponding value. -/
lemma Kfold_cube_add {G : Type*} [AddCommGroup G] (d : ℕ) (h H : Fin d → G)
    (ω : Fin d → Bool) :
    (∑ i, (if ω i then (h + H) i else 0))
      = (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H i else 0)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hc : ω i <;> simp [hc, Pi.add_apply]

/-- The multiple-binder sum notation `∑ (a) (b) (c), g a b c` is a sum over the product
finset `univ ×ˢ univ ×ˢ univ`; this lemma rewrites it as an iterated (nested) sum. -/
lemma Kfold_sum_binder3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (g : A → B → C → ℝ) :
    (∑ (a : A) (b : B) (c : C), g a b c) = ∑ (a : A), ∑ (b : B), ∑ (c : C), g a b c := by
  classical
  simp only [Finset.univ_product_univ]
  have key : (∑ x : A × (B × C), g x.1 x.2.1 x.2.2) = ∑ a, ∑ y : B × C, g a y.1 y.2 :=
    Fintype.sum_prod_type _
  rw [key]
  apply Finset.sum_congr rfl
  intro a _
  have key2 : (∑ y : B × C, g a y.1 y.2) = ∑ b, ∑ c, g a b c := Fintype.sum_prod_type _
  rw [key2]

/-- Change of variables `H ↦ h + H` on a `K`-tuple of `d`-tuples of an additive group:
the average over the common shift `h` turns the pairing into a product of independent sums. -/
lemma Kfold_pi_shift {G : Type*} [AddCommGroup G] [Fintype G] (d K : ℕ)
    (h : Fin d → G) (ψ : Fin K → (Fin d → G) → ℝ) :
    (∑ H : Fin K → Fin d → G, ∏ j : Fin K, ψ j (h + H j))
      = ∏ j : Fin K, ∑ k : Fin d → G, ψ j k := by
  classical
  let sh : (Fin d → G) ≃ (Fin d → G) := Equiv.addLeft h
  let e : (Fin K → Fin d → G) ≃ (Fin K → Fin d → G) := Equiv.piCongrRight (fun _ : Fin K => sh)
  have he : ∀ H : Fin K → Fin d → G, e H = fun j => h + H j := by
    intro H; funext j
    simp [e, sh, Equiv.piCongrRight, Equiv.addLeft]
  have key := Fintype.sum_equiv e (fun H : Fin K → Fin d → G => ∏ j : Fin K, ψ j (h + H j))
        (fun X : Fin K → Fin d → G => ∏ j : Fin K, ψ j (X j)) (fun H => by rw [he H])
  rw [key]
  rw [Finset.prod_univ_sum (fun _ : Fin K => (Finset.univ : Finset (Fin d → G))) ψ]
  rw [Fintype.piFinset_univ]

/-- Expansion of the `K`-fold pairing with dual functions, combined with the change of
variables `h_j ↦ h + H_j` (averaged over the common shift `h`). -/
theorem Kfold_dual_eq {G : Type*} [AddCommGroup G] [Fintype G] (d K : ℕ) (f : G → ℝ)
    (F : Fin K → G → ℝ) :
    ∑ x : G, f x * ∏ j : Fin K, (∑ h : Fin d → G,
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F j (x + ∑ i, (if ω i then h i else 0)))
      = ((Fintype.card G : ℝ) ^ d)⁻¹ *
        ∑ (H : Fin K → Fin d → G) (h : Fin d → G) (x : G),
          f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0))) := by
  classical
  rw [Kfold_sum_binder3 (fun (H : Fin K → Fin d → G) (h : Fin d → G) (x : G) =>
        f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
          F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))]
  have hBig :
      (∑ H : Fin K → Fin d → G, ∑ h : Fin d → G, ∑ x : G,
          f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
      = ∑ h : Fin d → G, ∑ x : G, f x * ∏ j : Fin K,
          ∑ k : Fin d → G, ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
            F j (x + ∑ i, (if ω i then k i else 0)) := by
    have h1 : (∑ H : Fin K → Fin d → G, ∑ h : Fin d → G,
          (∑ x : G, f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))))
        = ∑ h : Fin d → G, ∑ H : Fin K → Fin d → G,
          (∑ x : G, f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))) :=
      Finset.sum_comm
    rw [h1]
    apply Finset.sum_congr rfl
    intro h _
    have h2 : (∑ H : Fin K → Fin d → G,
          (∑ x : G, f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0)))))
        = ∑ x : G, ∑ H : Fin K → Fin d → G,
          f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0))) :=
      Finset.sum_comm
    rw [h2]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum]
    congr 1
    have hstep1 : (∑ H : Fin K → Fin d → G,
          ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0))))
        = ∑ H : Fin K → Fin d → G,
          ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then (h + H j) i else 0))) := by
      apply Finset.sum_congr rfl
      intro H _
      apply Finset.prod_congr rfl
      intro ω _
      apply Finset.prod_congr rfl
      intro j _
      rw [show x + (∑ i, (if ω i then h i else 0)) + (∑ i, (if ω i then H j i else 0))
            = x + (∑ i, (if ω i then (h + H j) i else 0)) by
          rw [Kfold_cube_add d h (H j) ω, add_assoc]]
    rw [hstep1]
    have hstep2 : (∑ H : Fin K → Fin d → G,
          ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), ∏ j : Fin K,
            F j (x + (∑ i, (if ω i then (h + H j) i else 0))))
        = ∑ H : Fin K → Fin d → G, ∏ j : Fin K,
          ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
            F j (x + (∑ i, (if ω i then (h + H j) i else 0))) :=
      Finset.sum_congr rfl (fun H _ => Finset.prod_comm)
    rw [hstep2]
    exact Kfold_pi_shift d K h
      (fun j k => ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
        F j (x + ∑ i, (if ω i then k i else 0)))
  rw [hBig]
  have hG : (Fintype.card G : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card G := by
      rw [← Finset.card_univ]
      exact Finset.card_pos.mpr ⟨0, Finset.mem_univ 0⟩
    exact_mod_cast (ne_of_gt hpos)
  have hcard : (Fintype.card (Fin d → G) : ℝ) = (Fintype.card G : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hG), one_mul]

end Commons.Combinatorics.Transference