/-
  `Work.WilE9G.Lagrange.eaD_pad`

  Zero-padding a chain (and its polynomials) to `K ≥ k` coordinates commutes with the symbolic
  derivation `eaD`.  This is the algebraic backbone of the statements in the Lagrange area that
  transfer a computation from the intrinsic `k` coordinates to the padded ambient `K` coordinates.

  The proof rests on the observation that `EAPoly.pad hm` is the *variable renaming*
  `MvPolynomial.rename (Sum.map (Fin.castLE hm) id)`: padding acts on the `k` polynomial
  coordinates but leaves the `r` exponential variables alone.  Since `Fin.castLE hm` is injective,
  `MvPolynomial.pderiv_rename` applies, the renaming is multiplicative, and the only remaining
  point is that the padded chain has the same coefficients as the original one at padded indices.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.Stratum

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Lagrange

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The `EA`-polynomial variable renaming underlying padding: it acts on the coordinate part
`Fin k → Fin K` and is the identity on the `r` exponential variables. -/
def padVar {k K r : ℕ} (hm : k ≤ K) : Fin k ⊕ Fin r → Fin K ⊕ Fin r :=
  Sum.map (Fin.castLE hm) id

@[simp] theorem padVar_inl {k K r : ℕ} (hm : k ≤ K) (i : Fin k) :
    padVar (r := r) hm (Sum.inl i) = Sum.inl (Fin.castLE hm i) := rfl

@[simp] theorem padVar_inr {k K r : ℕ} (hm : k ≤ K) (j : Fin r) :
    padVar (r := r) hm (Sum.inr j) = Sum.inr j := rfl

theorem injective_padVar {k K r : ℕ} (hm : k ≤ K) : Function.Injective (padVar (r := r) hm) := by
  rw [padVar, Sum.map_injective]
  exact ⟨Fin.castLE_injective hm, fun _ _ h => h⟩

/-- `EAPoly.pad` is the variable renaming along `padVar` (definitionally). -/
theorem EAPoly.pad_eq_rename {k K r : ℕ} (hm : k ≤ K) (Q : EAPoly k r) :
    Work.WilE7.EAPoly.pad hm Q = MvPolynomial.rename (padVar (r := r) hm) Q := rfl

/-- The coefficient of the padded chain at a padded index is the coefficient of the original
chain at the original index. -/
theorem EAChain.pad_a {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (j : Fin r) (i : Fin k) :
    (Work.WilE7.EAChain.pad hm c).a j (Fin.castLE hm i) = c.a j i := by
  show (if h : (Fin.castLE hm i).val < k then c.a j ⟨(Fin.castLE hm i).val, h⟩ else 0) = c.a j i
  rw [dite_eq_left (by rw [Fin.val_castLE]; exact i.isLt)]
  congr 1

/-- **Padding commutes with the symbolic derivation.** -/
theorem eaD_pad {k K r : ℕ} (hm : k ≤ K) (c : WilkiesDesign.E.EAChain k r) (i : Fin k)
    (Q : WilkiesDesign.E.EAPoly k r) :
    WilkiesDesign.E.eaD (Work.WilE7.EAChain.pad hm c) (Fin.castLE hm i)
        (Work.WilE7.EAPoly.pad hm Q)
      = Work.WilE7.EAPoly.pad hm (WilkiesDesign.E.eaD c i Q) := by
  -- `EAPoly.pad hm` unfolds to `rename (Sum.map (Fin.castLE hm) id)`, so we work with that
  -- explicit renaming; `injective_padVar` supplies its injectivity.
  have hinj : Function.Injective (Sum.map (Fin.castLE hm) (id : Fin r → Fin r)) :=
    injective_padVar (r := r) hm
  have hcoe : ∀ j : Fin r, (Work.WilE7.EAChain.pad hm c).a j (Fin.castLE hm i) = c.a j i :=
    fun j => EAChain.pad_a hm c j i
  simp only [WilkiesDesign.E.eaD, Work.WilE7.EAPoly.pad]
  rw [map_add, map_sum]
  congr 1
  · rw [← MvPolynomial.pderiv_rename hinj (Sum.inl i) Q]
    simp only [Sum.map_inl]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]
    simp only [Sum.map_inr, id_eq]
    rw [← MvPolynomial.pderiv_rename hinj (Sum.inr j) Q, hcoe j]
    simp only [Sum.map_inr, id_eq]

end Work.WilE9G.Lagrange
