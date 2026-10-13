/-
  `Work.WilE7.PadAux.eaD_extend`

  Extending an EA chain (and its polynomials) along an injection `e : Fin k → Fin k'` of the
  variables commutes with the symbolic derivation `eaD`.  This is the algebraic backbone of the
  statements in the padding area that transfer a computation from the intrinsic `k` coordinates
  to the extended `k'` coordinates.

  The proof rests on the observation that `EAPoly.extend e` is the *variable renaming*
  `MvPolynomial.rename (Sum.map e id)`: the extension acts on the `k` polynomial coordinates but
  leaves the `r` exponential variables alone.  Since `Sum.map e id` is injective when `e` is,
  `MvPolynomial.pderiv_rename` applies, the renaming is additive and multiplicative, and the only
  remaining point is that the extended chain has, at an index `e i` in the image of `e`, the same
  coefficients as the original chain at `i` (here injectivity of `e` is essential: it identifies
  the `choose`-witness used by `EAChain.extend`).
-/
import Mathlib
import Submission.Work.WilE8.Extend

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.PadAux

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The coefficient of the extended chain at an index `e i` is the coefficient of the original
chain at `i`.  Injectivity of `e` makes the `choose`-witness of `EAChain.extend` at `e i`
unambiguous. -/
theorem EAChain.extend_a {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (c : EAChain k r) (j : Fin r) (i : Fin k) :
    (Work.WilE8.EAChain.extend e c).a j (e i) = c.a j i := by
  show (if h : ∃ i' : Fin k, e i' = e i then c.a j h.choose else 0) = c.a j i
  rw [dite_eq_left (⟨i, rfl⟩ : ∃ i' : Fin k, e i' = e i)]
  exact congrArg (c.a j) (he (Exists.choose_spec (⟨i, rfl⟩ : ∃ i' : Fin k, e i' = e i)))

/-- The variable renaming underlying `EAPoly.extend` is injective for injective `e`. -/
theorem injective_sumMap_extend {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e) :
    Function.Injective (Sum.map e (id : Fin r → Fin r)) := by
  rw [Sum.map_injective]
  exact ⟨he, fun _ _ h => h⟩

/-- **Extension commutes with the symbolic derivation.** -/
theorem eaD_extend {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (c : WilkiesDesign.E.EAChain k r) (i : Fin k) (Q : WilkiesDesign.E.EAPoly k r) :
    WilkiesDesign.E.eaD (Work.WilE8.EAChain.extend e c) (e i) (Work.WilE8.EAPoly.extend e Q)
      = Work.WilE8.EAPoly.extend e (WilkiesDesign.E.eaD c i Q) := by
  have hinj : Function.Injective (Sum.map e (id : Fin r → Fin r)) := injective_sumMap_extend he
  have hcoe : ∀ j : Fin r, (Work.WilE8.EAChain.extend e c).a j (e i) = c.a j i :=
    fun j => EAChain.extend_a he c j i
  simp only [WilkiesDesign.E.eaD, Work.WilE8.EAPoly.extend]
  rw [map_add, map_sum]
  congr 1
  · rw [← MvPolynomial.pderiv_rename hinj (Sum.inl i) Q]
    simp only [Sum.map_inl]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]
    simp only [Sum.map_inr, id_eq]
    rw [← MvPolynomial.pderiv_rename hinj (Sum.inr j) Q, hcoe j]
    simp only [Sum.map_inr, id_eq]

end Work.WilE7.PadAux
