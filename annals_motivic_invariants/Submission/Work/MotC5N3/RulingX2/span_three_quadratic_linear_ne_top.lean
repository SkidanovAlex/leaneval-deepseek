import Mathlib
import Submission.Work.MotC5N3.RulingX2.span_quadratic_linear_ne_top

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotC5N3.RulingX2

/-- **The three-generator properness step of the `(P̂, Φ, Γ)` route to `ZiasSliceNeTop`.**

`Φ = X ^ 2 + C α * X + C β` is monic, `Γ = C D * X + C R`, and the norm
`R ^ 2 - α * R * D + β * D ^ 2` of `Γ` is divisible by `P`.  If `P` is **not a unit** (both reviews
of the earlier draft insisted on this instead of `P ≠ 0`, which is satisfiable by `P = 1`), then the
ideal `(P, Φ, Γ)` of `A[X]` is proper.

Proof: in `B := A ⧸ (P)` — nontrivial exactly because `P` is not a unit — the class of `Φ` is still
monic and the norm of the class of `Γ` vanishes, so `span_quadratic_linear_ne_top`
(`Submission/Work/MotC5N3/RulingX2/span_quadratic_linear_ne_top.lean`, PROVED) gives
`(Φ̄, Γ̄) ≠ ⊤` in `B[X]`; an inclusion `(C P, Φ, Γ) = ⊤` would map onto it.

This is the step that turns the CAS identity `P̂ ∣ R̂ ^ 2 - α R̂ D̂ + β D̂ ^ 2` (the norm of
`Γ = Gam`, with `Φ = Phisq`, `P = PhatPoly` of
`Submission/Work/MotC5N3/RulingX2/SlicePhi.lean`) into
`Work.MotC5N3.RulingX2.ZiasSliceGamNeTop`, the last-but-one input of the K5 leaf
`Work.MotC5N3.RulingX2.ZiasSliceNeTop` — see `RulingX2/NOTES_ZSST.md`.-/
theorem span_three_quadratic_linear_ne_top {A : Type*} [CommRing A]
    (P α β D R : A) (hP : ¬ IsUnit P)
    (h : P ∣ R ^ 2 - α * R * D + β * D ^ 2) :
    Ideal.span ({Polynomial.C P, Polynomial.X ^ 2 + Polynomial.C α * Polynomial.X + Polynomial.C β,
        Polynomial.C D * Polynomial.X + Polynomial.C R} : Set (Polynomial A)) ≠ ⊤ := by
  intro htop
  -- Quotient by `(P)`, which is proper because `P` is not a unit.
  set I : Ideal A := Ideal.span ({P} : Set A) with hI
  have hIne : I ≠ ⊤ := by
    rw [hI]
    exact fun hh => hP (Ideal.span_singleton_eq_top.mp hh)
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have hPmem : P ∈ I := by
    rw [hI]; exact Ideal.subset_span (by simp)
  have hPzero : (Ideal.Quotient.mk I) P = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hPmem
  -- The norm of `Γ` vanishes in the quotient.
  have hnorm : (Ideal.Quotient.mk I) (R ^ 2 - α * R * D + β * D ^ 2) = 0 := by
    obtain ⟨c, hc⟩ := h
    rw [hc, map_mul, hPzero, zero_mul]
  -- The two-generator statement in `(A ⧸ (P))[X]`.
  have hproper := span_quadratic_linear_ne_top
      ((Ideal.Quotient.mk I) α) ((Ideal.Quotient.mk I) β)
      ((Ideal.Quotient.mk I) D) ((Ideal.Quotient.mk I) R) hnorm
  apply hproper
  -- Map the three-generator ideal onto the two-generator ideal in the quotient.
  have hmap : Ideal.map (Polynomial.mapRingHom (Ideal.Quotient.mk I))
      (Ideal.span ({Polynomial.C P, Polynomial.X ^ 2 + Polynomial.C α * Polynomial.X + Polynomial.C β,
        Polynomial.C D * Polynomial.X + Polynomial.C R} : Set (Polynomial A))) = ⊤ := by
    rw [htop, Ideal.map_top]
  rw [Ideal.map_span] at hmap
  rw [← top_le_iff, ← hmap]
  apply Ideal.span_le.mpr
  rintro x ⟨y, hy, rfl⟩
  rcases hy with rfl | rfl | rfl
  · rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hPzero, Polynomial.C_0]
    exact Ideal.zero_mem _
  · rw [Polynomial.coe_mapRingHom]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    apply Ideal.subset_span
    simp
  · rw [Polynomial.coe_mapRingHom]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    apply Ideal.subset_span
    simp

end Work.MotC5N3.RulingX2
