import Mathlib
import Submission.NK.HassePrinciple.Norm
import Submission.NK.GlobalCFT.GlobalCFT

namespace NK.HassePrinciple

/-!
# `Ĥ¹(Gal(L/K), C_L) = 0` for cyclic `L/K`

The classical second inequality of global class field theory, in its cohomological form: for a
cyclic extension `L / K` of number fields the first Tate cohomology of the idèle class group
vanishes, `Ĥ¹(Gal(L/K), C_L) = 0`.

The proof is the index/Herbrand-quotient computation, and it does *not* use any further arithmetic
input beyond the two named ones:

* the **Hasse norm theorem** (`NK.HassePrinciple.HasseNormTheorem`), in its index form
  `[C_K : N_{L/K} C_L] = [L : K]`;
* the **Herbrand quotient** of the idèle class group
  (`NK.GlobalCFT.HerbrandQuotient`), `h(Gal(L/K), C_L) = [L : K]`, i.e.
  `|Ĥ⁰| = [L : K] · |Ĥ¹|`.

The missing link is supplied unconditionally by the on-disk `H⁰`-computation
(`NK.GlobalCFT.globalCFT_H0Computation`, Milne, *CFT*, Lemma 4.1):
`C_K ⧸ N_{L/K} C_L ≅ Ĥ⁰(Gal(L/K), C_L)`, so that `|Ĥ⁰| = [C_K : N_{L/K} C_L] = [L : K]`.  Together
with `|Ĥ⁰| = [L : K] · |Ĥ¹|` and `[L : K] > 0` this forces `|Ĥ¹| = 1`.

This is the input that turns the two inequalities of class field theory into the field axiom
`NK.GlobalCFT.fieldAxiom_of_herbrandQuotient`.
-/

set_option maxHeartbeats 1600000 in
/-- **The vanishing of `Ĥ¹` of the idèle class group of a cyclic extension.**  For a cyclic
extension `L / K` of number fields, the Hasse norm theorem (index form) and the Herbrand quotient
computation `h(Gal(L/K), C_L) = [L : K]` together with the `H⁰`-computation give
`Ĥ¹(Gal(L/K), C_L) = 0`. -/
theorem subsingleton_tateCohomology_one_of_cyclic (h : NK.HassePrinciple.HasseNormTheorem.{0}) {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (hh : NK.GlobalCFT.HerbrandQuotient K L) : Subsingleton (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 1) := by
  -- the `H⁰`-computation, *proved* on disk: `[C_K : N_{L/K} C_L] = |Ĥ⁰(Gal(L/K), C_L)|`
  have h0 : NK.GlobalCFT.H0Computation K L := NK.GlobalCFT.globalCFT_H0Computation
  have hA := NK.GlobalCFT.H0Computation.index_eq_natCard h0
  -- the Hasse norm theorem in index form: `[C_K : N_{L/K} C_L] = [L : K]`
  have hB := h.index_eq (K := K) (L := L) (inferInstance : IsCyclic (L ≃ₐ[K] L))
  -- hence `[L : K] = |Ĥ⁰| = [L : K] · |Ĥ¹|`
  have hmul : Module.finrank K L *
      Nat.card (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 1) =
        Module.finrank K L * 1 := by
    rw [← hh.herbrand, ← hA, hB, mul_one]
  -- and `[L : K] > 0`, so `|Ĥ¹| = 1`
  have hB1 : Nat.card (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 1) = 1 :=
    Nat.eq_of_mul_eq_mul_left Module.finrank_pos hmul
  exact (Nat.card_eq_one_iff_unique.mp hB1).1

end NK.HassePrinciple
