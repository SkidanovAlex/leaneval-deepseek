import Mathlib
import Submission.Work.Tower.Unramified.SplitsCompletelyNF

open NumberField

namespace Work.Tower.Unramified

/-- **A prime at which every overlying prime is unramified with trivial residue field
extension splits completely.**  If every prime `P` of `𝓞 L` above `𝔭` has ramification index
`1` and inertia degree `1` over `𝓞 F`, then `𝔭` splits completely in `L/F`: the fundamental
identity `∑ P, e P * f P = [L : F]` (here `Ideal.sum_ramification_inertia_eq_finrank`)
collapses to the count `Nat.card (𝔭.primesOver (𝓞 L)) = Module.finrank F L`. -/
theorem splitsCompletelyInNF_of_ramification_inertia {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L]
    {𝔭 : Ideal (NumberField.RingOfIntegers F)} (h𝔭 : 𝔭.IsPrime)
    (h : ∀ P : 𝔭.primesOver (NumberField.RingOfIntegers L),
      P.1.ramificationIdx (NumberField.RingOfIntegers F) = 1 ∧
        P.1.inertiaDeg (NumberField.RingOfIntegers F) = 1) :
    Work.Tower.Unramified.SplitsCompletelyInNF F L 𝔭 := by
  classical
  have : 𝔭.IsPrime := h𝔭
  have : Fintype (𝔭.primesOver (𝓞 L)) := (Algebra.QuasiFinite.finite_primesOver 𝔭).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank 𝔭 (𝓞 L)
  have hone : ∑ q : 𝔭.primesOver (𝓞 L),
      q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F)
        = Fintype.card (𝔭.primesOver (𝓞 L)) := by
    rw [← Finset.card_univ, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun q _ => by rw [(h q).1, (h q).2, mul_one]
  rw [hone] at hsum
  refine ⟨?_, h⟩
  rw [Nat.card_eq_fintype_card, hsum, IsFractionRing.finrank_eq (𝓞 F) F (𝓞 L) L]

end Work.Tower.Unramified
