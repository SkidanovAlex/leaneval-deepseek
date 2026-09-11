import Submission.Iso
import Mathlib.Algebra.MonoidAlgebra.Basic

open UnitConjecture

set_option autoImplicit false

noncomputable section

namespace Submission

open scoped Classical

abbrev F2 := ZMod 2
abbrev RG := MonoidAlgebra F2 HW
open MonoidAlgebra
open Finset

lemma coeff_sum {ι : Type*} (S : Finset ι) (f : ι → RG) (m : HW) :
    (∑ s ∈ S, f s).coeff m = ∑ s ∈ S, (f s).coeff m := by
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a s has ih
    simp [ih, has]

lemma coeff_single' (g m : HW) : (single g (1 : F2)).coeff m = if g = m then (1 : F2) else 0 := by
  by_cases h : g = m
  · subst m; simp
  · simp [h, Finsupp.single_eq_of_ne]

lemma coeff_sum_single {ι : Type*} (S : Finset ι) (f : ι → HW) (m : HW) :
    (∑ s ∈ S, single (f s) (1 : F2)).coeff m = ∑ s ∈ S, (if f s = m then (1 : F2) else 0) := by
  rw [coeff_sum]
  refine Finset.sum_congr rfl ?_
  intro s hs
  exact coeff_single' (f s) m

lemma sum_single_map_eq_single {ι : Type*} (P : Finset ι) (f : ι → HW) (g : HW)
    (hcount : (∑ p ∈ P, if f p = g then (1 : F2) else 0) = 1)
    (hz : ∀ p ∈ P, f p ≠ g →
      (∑ p' ∈ P, if f p' = f p then (1 : F2) else 0) = 0) :
    (∑ p ∈ P, single (f p) (1 : F2)) = single g (1 : F2) := by
  rw [MonoidAlgebra.ext_iff]
  apply Finsupp.ext
  intro m
  by_cases hmg : m = g
  · subst m
    rw [coeff_sum_single]
    rw [hcount]
    simp
  · by_cases hmem : ∃ p ∈ P, f p = m
    · rcases hmem with ⟨p0, hp0P, rfl⟩
      have hz0 := hz p0 hp0P hmg
      rw [coeff_sum_single]
      rw [coeff_single']
      rw [hz0]
      rw [if_neg (by intro h; exact hmg h.symm)]
    · rw [coeff_sum_single]
      rw [coeff_single']
      rw [if_neg (by intro h; exact hmg h.symm)]
      refine Finset.sum_eq_zero ?_
      intro p hp
      have hpm : f p ≠ m := by intro h; exact hmem ⟨p, hp, h⟩
      rw [if_neg hpm]

lemma prod_sum_single (S T : Finset HW) :
    (∑ s ∈ S, single s (1:F2)) * (∑ t ∈ T, single t (1:F2))
      = ∑ p ∈ S.product T, single (p.1 * p.2) (1:F2) := by
  calc
    (∑ s ∈ S, single s (1:F2)) * (∑ t ∈ T, single t (1:F2))
        = ∑ s ∈ S, single s (1:F2) * (∑ t ∈ T, single t (1:F2)) := by rw [Finset.sum_mul]
    _ = ∑ s ∈ S, ∑ t ∈ T, single (s * t) (1:F2) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [single_mul_single]
        simp
    _ = ∑ p ∈ S.product T, single (p.1 * p.2) (1:F2) := by
        rw [← Finset.sum_product (s := S) (t := T)
          (f := fun p : HW × HW => single (p.1 * p.2) (1 : F2))]
        rfl

/-- collapse a sum-of-images to a sum over a set -/
lemma sum_single_map_eq_sum_single {ι : Type*} (P : Finset ι) (f : ι → HW) (Q : Finset HW)
    (hcover : ∀ p ∈ P, f p ∈ Q)
    (huniq : ∀ q ∈ Q, (∑ p ∈ P, if f p = q then (1 : F2) else 0) = 1) :
    (∑ p ∈ P, single (f p) (1 : F2)) = ∑ q ∈ Q, single q (1 : F2) := by
  rw [MonoidAlgebra.ext_iff]
  apply Finsupp.ext
  intro m
  by_cases hmQ : m ∈ Q
  · have hL : ((∑ p ∈ P, single (f p) (1 : F2)).coeff m) = (1 : F2) := by
      rw [coeff_sum_single]
      exact huniq m hmQ
    have hR : ((∑ q ∈ Q, single q (1 : F2)).coeff m) = (1 : F2) := by
      rw [coeff_sum]
      rw [Finset.sum_eq_single (f := fun q : HW => (single q (1 : F2)).coeff m) m]
      · simp
      · intro b hb hbm
        rw [coeff_single']
        rw [if_neg hbm]
      · intro hmnot; exact False.elim (hmnot hmQ)
    rw [hL, hR]
  · have hL : ((∑ p ∈ P, single (f p) (1 : F2)).coeff m) = 0 := by
      rw [coeff_sum_single]
      refine Finset.sum_eq_zero ?_
      intro p hp
      have hfp : f p ∈ Q := hcover p hp
      have hne : f p ≠ m := by intro h; exact hmQ (by simpa [h] using hfp)
      rw [if_neg hne]
    have hR : ((∑ q ∈ Q, single q (1 : F2)).coeff m) = 0 := by
      rw [coeff_sum]
      refine Finset.sum_eq_zero ?_
      intro q hq
      rw [coeff_single']
      have hne : q ≠ m := by intro h; exact hmQ (by simpa [h] using hq)
      rw [if_neg hne]
    rw [hL, hR]

-- multiply a sum of singles on the right by a single
lemma sum_mul_single_right (S : Finset HW) (t : HW) :
    (∑ s ∈ S, single s (1 : F2)) * single t (1 : F2)
      = ∑ s ∈ S, single (s * t) (1 : F2) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [single_mul_single]
  simp

lemma sum_sum_union {S T : Finset HW} (h : Disjoint S T) :
    (∑ s ∈ S, single s (1 : F2)) + (∑ t ∈ T, single t (1 : F2))
      = ∑ u ∈ S ∪ T, single u (1 : F2) := by
  rw [← Finset.sum_union h]

lemma prod_sum_map_single {ι : Type*} (P : Finset ι) (f : ι → HW) (T : Finset HW) :
    (∑ p ∈ P, single (f p) (1 : F2)) * (∑ t ∈ T, single t (1 : F2))
      = ∑ q ∈ P.product T, single (f q.1 * q.2) (1 : F2) := by
  calc
    (∑ p ∈ P, single (f p) (1 : F2)) * (∑ t ∈ T, single t (1 : F2))
        = ∑ p ∈ P, single (f p) (1 : F2) * (∑ t ∈ T, single t (1 : F2)) := by
          rw [Finset.sum_mul]
    _ = ∑ p ∈ P, ∑ t ∈ T, single (f p * t) (1 : F2) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          rw [single_mul_single]
          simp
    _ = ∑ q ∈ P.product T, single (f q.1 * q.2) (1 : F2) := by
          rw [← Finset.sum_product (s := P) (t := T)
            (f := fun q : ι × HW => single (f q.1 * q.2) (1 : F2))]
          rfl

lemma sum_pair {β : Type*} [AddCommMonoid β] {a b : HW} (h : a ≠ b) (f : HW → β) :
    (∑ x ∈ ({a, b} : Finset HW), f x) = f a + f b := by
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
  · simp [h]

-- ============================================================
-- Definitions for the transported element
-- ============================================================

abbrev RR := MonoidAlgebra (ZMod 2) P

/-- transport ring isomorphism -/
def Phi : RR ≃ₐ[ZMod 2] MonoidAlgebra (ZMod 2) HW :=
  MonoidAlgebra.domCongr (R := ZMod 2) (A := ZMod 2) (M := P) (N := HW) iso

/-- the monomial constructor -/
def m (i j k : ℤ) (q : Q) : HW := { e := (i, j, k), q := q }

lemma iso_w (e : E) : iso (w e) = { e := e, q := q0 } := by
  change phi (w e) = { e := e, q := q0 }
  exact phi_w e

lemma iso_sig (q : Q) : iso (sig q) = { e := (0, 0, 0), q := q } := by
  change phi (sig q) = { e := (0, 0, 0), q := q }
  exact phi_sig q

lemma iso_wsig (e : E) (q : Q) : iso (w e * sig q) = { e := e, q := q } := by
  rw [map_mul]
  rw [iso_w]
  rw [iso_sig]
  exact q0_mul_q e q

/-- Phi of a single monomial -/
lemma Phi_mono (e : E) (q : Q) :
    Phi (single (w e * sig q) (1 : ZMod 2)) = single { e := e, q := q } (1 : ZMod 2) := by
  rw [Phi]
  rw [MonoidAlgebra.domCongr_single]
  congr 1
  exact iso_wsig e q

-- monomial elements in R (with sigma factors)
def monoR (e : E) (q : Q) : RR := single (w e * sig q) (1 : ZMod 2)

lemma iso_x : iso (x : P) = m 1 0 0 q0 := by
  rw [x_eq_a2]
  rw [map_pow]
  change phi (UnitConjecture.a : P) ^ 2 = HW.Tx
  rw [phi_a]
  exact HW.A_sq

lemma iso_y : iso (y : P) = m 0 1 0 q0 := by
  rw [y_eq_b2]
  rw [map_pow]
  change phi (UnitConjecture.b : P) ^ 2 = HW.Ty
  rw [phi_b]
  exact HW.B_sq

lemma iso_z : iso (z : P) = m 0 0 1 q0 := by
  rw [z_eq_ab2]
  rw [map_pow]
  rw [map_mul]
  change (HW.A * HW.B) ^ 2 = HW.Tz
  rw [pow_two]
  exact HW.AB_sq

lemma iso_z_inv : iso (z⁻¹ : P) = m 0 0 (-1) q0 := by
  rw [map_inv]
  rw [iso_z]
  change ({e := (0, 0, 1), q := q0} : HW)⁻¹ = m 0 0 (-1) q0
  rw [inv_trans]
  rfl

lemma iso_a : iso (UnitConjecture.a : P) = HW.A := by
  change phi (UnitConjecture.a : P) = HW.A
  exact phi_a

lemma iso_b : iso (UnitConjecture.b : P) = HW.B := by
  change phi (UnitConjecture.b : P) = HW.B
  exact phi_b

/-- Phi of the coerced generator x -/
lemma Phi_coe_x : Phi (((x : P) : RR)) = single (m 1 0 0 q0) (1 : ZMod 2) := by
  change Phi (single (x : P) (1 : ZMod 2)) = single (m 1 0 0 q0) (1 : ZMod 2)
  simp [Phi, iso_x]

lemma Phi_coe_y : Phi (((y : P) : RR)) = single (m 0 1 0 q0) (1 : ZMod 2) := by
  change Phi (single (y : P) (1 : ZMod 2)) = single (m 0 1 0 q0) (1 : ZMod 2)
  simp [Phi, iso_y]

lemma Phi_coe_z_inv : Phi (((z⁻¹ : P) : RR)) = single (m 0 0 (-1) q0) (1 : ZMod 2) := by
  change Phi (single (z⁻¹ : P) (1 : ZMod 2)) = single (m 0 0 (-1) q0) (1 : ZMod 2)
  simp [Phi, iso_z_inv]

lemma Phi_coe_a : Phi (((UnitConjecture.a : P) : RR)) = single (m 0 0 0 qA) (1 : ZMod 2) := by
  change Phi (single (UnitConjecture.a : P) (1 : ZMod 2)) = single (m 0 0 0 qA) (1 : ZMod 2)
  simp [Phi, iso_a]
  rw [show m 0 0 0 qA = HW.A by decide]

lemma Phi_coe_b : Phi (((UnitConjecture.b : P) : RR)) = single (m 0 0 0 qB) (1 : ZMod 2) := by
  change Phi (single (UnitConjecture.b : P) (1 : ZMod 2)) = single (m 0 0 0 qB) (1 : ZMod 2)
  simp [Phi, iso_b]
  rw [show m 0 0 0 qB = HW.B by decide]

/-- Phi on the image of a P element -/
lemma Phi_of_coe (g : P) : Phi ((g : RR)) = single (iso g) (1 : ZMod 2) := by
  change Phi (single g (1 : ZMod 2)) = single (iso g) (1 : ZMod 2)
  rw [Phi]
  rw [MonoidAlgebra.domCongr_single]

/-- Phi on a single of a P element -/
lemma Phi_single_coe (g : P) : Phi (single g (1 : ZMod 2)) = single (iso g) (1 : ZMod 2) := by
  rw [Phi]
  rw [MonoidAlgebra.domCongr_single]

lemma iso_a_m : iso (UnitConjecture.a : P) = m 0 0 0 qA := by
  rw [iso_a]
  rw [show HW.A = m 0 0 0 qA by decide]

lemma iso_b_m : iso (UnitConjecture.b : P) = m 0 0 0 qB := by
  rw [iso_b]
  rw [show HW.B = m 0 0 0 qB by decide]

/-- product = double sum (no product-finset) -/
lemma prod_sum_single_double (S T : Finset HW) :
    (∑ s ∈ S, single s (1:F2)) * (∑ t ∈ T, single t (1:F2))
      = ∑ s ∈ S, ∑ t ∈ T, single (s * t) (1:F2) := by
  calc
    (∑ s ∈ S, single s (1:F2)) * (∑ t ∈ T, single t (1:F2))
        = ∑ s ∈ S, single s (1:F2) * (∑ t ∈ T, single t (1:F2)) := by rw [Finset.sum_mul]
    _ = ∑ s ∈ S, ∑ t ∈ T, single (s * t) (1:F2) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [single_mul_single]
        simp

lemma coeff_sum_single_double (S T : Finset HW) (m : HW) :
    (∑ s ∈ S, ∑ t ∈ T, single (s * t) (1 : F2)).coeff m
      = ∑ s ∈ S, ∑ t ∈ T, (if s * t = m then (1 : F2) else 0) := by
  rw [coeff_sum]
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [coeff_sum]
  refine Finset.sum_congr rfl ?_
  intro t ht
  exact coeff_single' (s * t) m

/-- double sum of singles equals a single -/
lemma dbl_sum_single_eq_single (S T : Finset HW) (g : HW)
    (hcount : (∑ s ∈ S, ∑ t ∈ T, if s * t = g then (1 : F2) else 0) = 1)
    (hz : ∀ s ∈ S, ∀ t ∈ T, s * t ≠ g →
      (∑ s' ∈ S, ∑ t' ∈ T, if s' * t' = s * t then (1 : F2) else 0) = 0) :
    (∑ s ∈ S, ∑ t ∈ T, single (s * t) (1 : F2)) = single g (1 : F2) := by
  rw [MonoidAlgebra.ext_iff]
  apply Finsupp.ext
  intro m
  by_cases hmg : m = g
  · subst m
    rw [coeff_sum_single_double]
    rw [hcount]
    simp
  · by_cases hmem : ∃ s ∈ S, ∃ t ∈ T, s * t = m
    · rcases hmem with ⟨s0, hs0, t0, ht0, rfl⟩
      have hz0 := hz s0 hs0 t0 ht0 hmg
      rw [coeff_sum_single_double]
      rw [coeff_single']
      rw [hz0]
      rw [if_neg (by intro h; exact hmg h.symm)]
    · rw [coeff_sum_single_double]
      rw [coeff_single']
      rw [if_neg (by intro h; exact hmg h.symm)]
      refine Finset.sum_eq_zero ?_
      intro s hs
      refine Finset.sum_eq_zero ?_
      intro t ht
      have hne : s * t ≠ m := by
        intro h
        exact hmem ⟨s, hs, t, ht, h⟩
      rw [if_neg hne]

/-- coefficient of a double sum with generic op -/
lemma coeff_sum_single_double_op (S T : Finset HW) (op : HW → HW → HW) (m : HW) :
    (∑ s ∈ S, ∑ t ∈ T, single (op s t) (1 : F2)).coeff m
      = ∑ s ∈ S, ∑ t ∈ T, (if op s t = m then (1 : F2) else 0) := by
  rw [coeff_sum]
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [coeff_sum]
  refine Finset.sum_congr rfl ?_
  intro t ht
  exact coeff_single' (op s t) m

lemma dbl_sum_single_eq_single_op (S T : Finset HW) (op : HW → HW → HW) (g : HW)
    (hcount : (∑ s ∈ S, ∑ t ∈ T, if op s t = g then (1 : F2) else 0) = 1)
    (hz : ∀ s ∈ S, ∀ t ∈ T, op s t ≠ g →
      (∑ s' ∈ S, ∑ t' ∈ T, if op s' t' = op s t then (1 : F2) else 0) = 0) :
    (∑ s ∈ S, ∑ t ∈ T, single (op s t) (1 : F2)) = single g (1 : F2) := by
  rw [MonoidAlgebra.ext_iff]
  apply Finsupp.ext
  intro m
  by_cases hmg : m = g
  · subst m
    rw [coeff_sum_single_double_op]
    rw [hcount]
    simp
  · by_cases hmem : ∃ s ∈ S, ∃ t ∈ T, op s t = m
    · rcases hmem with ⟨s0, hs0, t0, ht0, rfl⟩
      have hz0 := hz s0 hs0 t0 ht0 hmg
      rw [coeff_sum_single_double_op]
      rw [coeff_single']
      rw [hz0]
      rw [if_neg (by intro h; exact hmg h.symm)]
    · rw [coeff_sum_single_double_op]
      rw [coeff_single']
      rw [if_neg (by intro h; exact hmg h.symm)]
      refine Finset.sum_eq_zero ?_
      intro s hs
      refine Finset.sum_eq_zero ?_
      intro t ht
      have hne : op s t ≠ m := by
        intro h
        exact hmem ⟨s, hs, t, ht, h⟩
      rw [if_neg hne]



/-- double sum of singles (generic op) equals a sum over a set -/
lemma dbl_sum_single_eq_sum_set_op (S T : Finset HW) (op : HW → HW → HW) (R : Finset HW)
    (hone : ∀ r ∈ R, (∑ s ∈ S, ∑ t ∈ T, if op s t = r then (1 : F2) else 0) = 1)
    (hz : ∀ s ∈ S, ∀ t ∈ T, op s t ∉ R →
      (∑ s' ∈ S, ∑ t' ∈ T, if op s' t' = op s t then (1 : F2) else 0) = 0) :
    (∑ s ∈ S, ∑ t ∈ T, single (op s t) (1 : F2)) = ∑ r ∈ R, single r (1 : F2) := by
  rw [MonoidAlgebra.ext_iff]
  apply Finsupp.ext
  intro m
  by_cases hmR : m ∈ R
  · -- coefficient left at m = 1, right = 1
    have hL : ((∑ s ∈ S, ∑ t ∈ T, single (op s t) (1 : F2)).coeff m) = (1 : F2) := by
      rw [coeff_sum_single_double_op]
      exact hone m hmR
    have hR : ((∑ r ∈ R, single r (1 : F2)).coeff m) = (1 : F2) := by
      rw [coeff_sum]
      rw [Finset.sum_eq_single (f := fun q : HW => (single q (1 : F2)).coeff m) m]
      · simp
      · intro b hb hbm
        rw [coeff_single']
        rw [if_neg hbm]
      · intro hmnot; exact False.elim (hmnot hmR)
    rw [hL, hR]
  · -- m not in R: right coefficient 0; left coefficient 0
    have hR : ((∑ r ∈ R, single r (1 : F2)).coeff m) = 0 := by
      rw [coeff_sum]
      refine Finset.sum_eq_zero ?_
      intro q hq
      rw [coeff_single']
      have hne : q ≠ m := by intro h; exact hmR (by simpa [h] using hq)
      rw [if_neg hne]
    have hL : ((∑ s ∈ S, ∑ t ∈ T, single (op s t) (1 : F2)).coeff m) = 0 := by
      rw [coeff_sum_single_double_op]
      by_cases hmem : ∃ s ∈ S, ∃ t ∈ T, op s t = m
      · rcases hmem with ⟨s0, hs0, t0, ht0, rfl⟩
        have hz0 := hz s0 hs0 t0 ht0 hmR
        rw [hz0]
      · refine Finset.sum_eq_zero ?_
        intro s hs
        refine Finset.sum_eq_zero ?_
        intro t ht
        have hne : op s t ≠ m := by intro h; exact hmem ⟨s, hs, t, ht, h⟩
        rw [if_neg hne]
    rw [hL, hR]

end Submission
