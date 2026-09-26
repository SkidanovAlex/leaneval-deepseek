import Mathlib
import Submission.Work.PTCert.OrderUnit

/-!
# Telescoping identity for products of the letters `b1 r k`

For a list of letters `ks`, the element `1 - ∏_{k ∈ ks} b1 r k` of the group ring
`ℝ[MulAut (F_r)]` telescopes as

  `1 - of (lprod r ks) = ∑_{i < ks.length} of (lprod r (ks.take i)) * (1 - of (b1 r (ks[i])))`.

The mathematical content is the elementary telescoping identity
`1 - p_n = ∑_{i<n} (p_i - p_{i+1})` with `p_i` the prefix product; it is proved here for an
arbitrary monoid `M`, ring `R` and monoid hom `φ : M →* R` (no commutativity is used).
-/

open scoped BigOperators

namespace Work.PTCert

/-- Telescoping identity for prefix products.

For a monoid `M`, a ring `R`, a monoid homomorphism `φ : M →* R`, a sequence
`g : ℕ → M` and a list `ks : List ℕ`, with `p i = φ ((ks.take i)).prod` the `i`-th prefix
product, we have `1 - φ ((ks.map g).prod) = ∑_{i < ks.length} p i * (1 - φ (g (ks[i])))`. -/
lemma telescope_general {M : Type*} [Monoid M] {R : Type*} [Ring R] (φ : M →* R) (g : ℕ → M) :
    ∀ ks : List ℕ,
    1 - φ ((ks.map g).prod) =
      ∑ i : Fin ks.length, φ ((ks.take i.val).map g).prod * (1 - φ (g (ks.get i))) := by
  intro ks
  induction ks with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons, MonoidHom.map_mul]
    show 1 - φ (g a) * φ ((t.map g).prod) =
      ∑ i : Fin (t.length + 1),
        φ ((List.take (i : ℕ) (a :: t)).map g).prod * (1 - φ (g ((a :: t).get i)))
    rw [Fin.sum_univ_succ]
    have key : (∑ i : Fin t.length,
          φ ((List.take (↑i.succ) (a :: t)).map g).prod * (1 - φ (g ((a :: t).get i.succ)))) =
        φ (g a) * (∑ i : Fin t.length,
          φ ((t.take i.val).map g).prod * (1 - φ (g (t.get i)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [List.get_eq_getElem]
      simp only [Fin.val_succ, List.take_succ_cons, List.map_cons, List.prod_cons,
        MonoidHom.map_mul, List.getElem_cons_succ]
      rw [List.get_eq_getElem, mul_assoc]
    rw [key, ← ih]
    simp only [Fin.val_zero, List.take_zero, List.map_nil, List.prod_nil, MonoidHom.map_one,
      List.get_cons_zero, one_mul]
    noncomm_ring

theorem lprodTelescope (r : ℕ) (ks : List ℕ) : (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r)))) - MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.lprod r ks) = Finset.univ.sum (fun i : Fin ks.length => MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.lprod r (ks.take i.val)) * (1 - MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r (ks.get i)))) := by
  have h := telescope_general
    (φ := MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r)))) (g := Submission.PTCert.b1 r) ks
  simpa [Submission.PTCert.lprod] using h

end Work.PTCert
