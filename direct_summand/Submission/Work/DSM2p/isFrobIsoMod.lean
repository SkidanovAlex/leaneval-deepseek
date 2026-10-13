import Mathlib
import Submission.Work.DSM2p.Basic

namespace Work.DSM2p

/-- For `P : PerfectoidData p A` the ideals `(p)` and `(P.ϖ 0 ^ p)` agree: `P.unit` exhibits
`P.ϖ 0 ^ p = p * v` with `v` a unit, so the two principal ideals differ by a unit. -/
theorem span_p_eq_span_varpi_pow {p : ℕ} {A : Type*} [CommRing A]
    (P : DSMap.PerfectoidData p A) :
    Ideal.span {(p : A)} = Ideal.span {P.ϖ 0 ^ p} := by
  obtain ⟨v, hv⟩ := P.unit
  rw [hv]
  exact (Ideal.span_singleton_mul_right_unit v.isUnit (p : A)).symm

/-- **CS `p-oid-mod-pi`.**  The Frobenius `x ↦ x ^ p` induces an isomorphism `A/ϖ → A/ϖ ^ p`
for `ϖ = P.ϖ 0`.  These are exactly the conditions `frobSurj`/`frobInj` of `PerfectoidData`,
transported from `(p)` to `(ϖ 0 ^ p)` along `span_p_eq_span_varpi_pow`. -/
theorem isFrobIsoMod {p : ℕ} {A : Type*} [CommRing A] (P : DSMap.PerfectoidData p A) :
    IsFrobIsoMod p A (P.ϖ 0) := by
  have hspan := span_p_eq_span_varpi_pow P
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := P.frobSurj x
    exact ⟨y, by rw [← hspan]; exact hy⟩
  · exact P.frobInj x (hspan.symm ▸ hx)

end Work.DSM2p
