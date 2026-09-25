import Mathlib
import Submission.Work.Tower.Unramified.SplitsCompletelyNF

open NumberField

namespace Work.Tower.Unramified

theorem splitsCompletelyIn_of_NF {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] {𝔭 : Ideal (NumberField.RingOfIntegers F)}
    (h𝔭 : 𝔭.IsPrime) (h0 : 𝔭 ≠ ⊥)
    (h : Work.Tower.Unramified.SplitsCompletelyInNF F L 𝔭) :
    Work.Tower.SplitsCompletelyIn F L 𝔭 := by
  classical
  obtain ⟨hcard, hef⟩ := h
  haveI : 𝔭.IsMaximal := h𝔭.isMaximal h0
  haveI : Fintype (𝔭.primesOver (𝓞 L)) := (Algebra.QuasiFinite.finite_primesOver 𝔭).fintype
  have hcard' : Fintype.card (𝔭.primesOver (𝓞 L)) = Module.finrank F L := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  -- Enumerate the `[L : F]` primes of `𝓞 L` above `𝔭` by `Fin (Module.finrank F L)`.
  let e := Fintype.equivFinOfCardEq hcard'
  refine ⟨fun i => (e.symm i).1, fun i => (e.symm i).2.1, fun i => (e.symm i).2.2,
    Subtype.coe_injective.comp e.symm.injective, fun i => ?_⟩
  -- Each listed prime has inertia degree one, so its residue field is `𝓞 F ⧸ 𝔭`.
  haveI : ((e.symm i).1).IsPrime := (e.symm i).2.1
  haveI : ((e.symm i).1).LiesOver 𝔭 := (e.symm i).2.2
  have hP0 : (e.symm i).1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h0 _
  haveI : ((e.symm i).1).IsMaximal := ((e.symm i).2.1).isMaximal hP0
  exact nonempty_quot_equiv_of_inertiaDeg_eq_one (hef (e.symm i)).2

end Work.Tower.Unramified
