/-
  `Work.WilE7.CoreStep.eaD_reindex`

  Reindexing the coordinates of a chain along an equivalence `e : Fin k ≃ Fin K` and
  correspondingly reindexing the `EA`-polynomial commutes with the symbolic derivation
  `eaD`: the derivation with respect to the new coordinate `e i` of the reindexed polynomial
  is the reindexed derivation with respect to `i`.

  The proof is the same as that of `Work.WilE7.PadAux.eaD_extend`: `EAPoly.reindex e` is the
  variable renaming `MvPolynomial.rename (Sum.map e id)` along the *injective* (indeed
  bijective) map `Sum.map e id`, so `MvPolynomial.pderiv_rename` applies, the renaming is
  additive and multiplicative, and the only remaining point is that the reindexed chain has,
  at an index `e i`, the same coefficients as the original chain at `i`.
-/
import Mathlib
import Submission.Work.WilE7.reindex_component

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.CoreStep

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The variable renaming underlying `EAPoly.reindex` is injective. -/
theorem injective_sumMap_reindex {k K r : ℕ} (e : Fin k ≃ Fin K) :
    Function.Injective (Sum.map e (id : Fin r → Fin r)) := by
  rw [Sum.map_injective]
  exact ⟨e.injective, fun _ _ h => h⟩

/-- The coefficient of the reindexed chain at `e i` is the coefficient of the original chain
at `i`. -/
theorem EAChain.reindex_a {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r) (j : Fin r)
    (i : Fin k) : (Work.WilE7.EAChain.reindex e c).a j (e i) = c.a j i := by
  simp [Work.WilE7.EAChain.reindex]

theorem eaD_reindex {k K r : ℕ} (e : Fin k ≃ Fin K) (c : WilkiesDesign.E.EAChain k r)
    (i : Fin k) (Q : WilkiesDesign.E.EAPoly k r) :
    WilkiesDesign.E.eaD (Work.WilE7.EAChain.reindex e c) (e i) (Work.WilE7.EAPoly.reindex e Q) =
      Work.WilE7.EAPoly.reindex e (WilkiesDesign.E.eaD c i Q) := by
  have hinj : Function.Injective (Sum.map e (id : Fin r → Fin r)) := injective_sumMap_reindex e
  have hcoe : ∀ j : Fin r, (Work.WilE7.EAChain.reindex e c).a j (e i) = c.a j i :=
    fun j => EAChain.reindex_a e c j i
  simp only [WilkiesDesign.E.eaD, Work.WilE7.EAPoly.reindex]
  rw [map_add, map_sum]
  congr 1
  · rw [← MvPolynomial.pderiv_rename hinj (Sum.inl i) Q]
    simp only [Sum.map_inl]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]
    simp only [Sum.map_inr, id_eq]
    rw [← MvPolynomial.pderiv_rename hinj (Sum.inr j) Q]
    simp only [Sum.map_inr, id_eq]
    rw [hcoe j]

end Work.WilE7.CoreStep
