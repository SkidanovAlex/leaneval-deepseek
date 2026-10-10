import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Flat descent of the pole-fibre local computation (ingredient (ii))

This file records the **algebraic heart of ingredient (ii)** of the pole-fibre chapter of the
characteristic-`5` Artin–Schreier branch (see `Submission/Work/MotV5/Nodes/GUIDE_PoleFibre.md`).

The geometric situation is this.  The twist surface `S = (C_L × E)/⟨σ'⟩` is the quotient of
`C_L × E` by a free action of `ℤ/5`, so the quotient map `π : C_L × E → S` is finite étale of
degree `5`; in particular, for a point `q ∈ S` and `x ∈ π^{-1}(q)` the ring map of local rings
`A := O_{S,q} → B := O_{C_L × E,x}` makes `B` a finite free (hence faithfully flat) `A`-algebra of
rank `5`, and `A` is a domain.

The fibre computation over the pole of `t` shows, in the local ring `B`,

  `t⁻¹ = s ^ 5 * (unit of B)`,   `s` a local equation of the pole fibre `E'`,

i.e. `(t⁻¹) · B = (s ^ 5) · B` as ideals.  Faithful flatness descends this to `A`: the *same*
relation holds with a unit of `A`.  That is the statement proved here; it is the step that turns a
computation on the (larger) quotient cover into a statement about the pole divisor on the twist
surface.

Mathlib already provides the flat-descent input in the form
`Ideal.map_injective_of_faithfullyFlat`; what the geometry needs on top of it is the conversion of
an equality of principal ideals into a *unit*, which is the content of `exists_unit_of_map_span_eq`
below. -/

namespace Work.MotV5

/-- **Flat descent of a principal-ideal equality to a unit.**  Let `A` be a domain and `B` a
faithfully flat `A`-algebra; let `f g : A` with `f ≠ 0`.  If `f` and `g` generate the same ideal
after extension to `B`, then `g = f * u` for a unit `u` of `A`.

This is the algebraic form of "`π^*(t⁻¹) = π^*(s) ^ 5 · (unit)` in `B` gives
`t⁻¹ = s ^ 5 · (unit)` in `A`": `f = t⁻¹`, `g = s ^ 5`.  The hypothesis `f ≠ 0` is automatic for
`f = t⁻¹` (the parameter `t` is transcendental in the function field); `A = O_{S,q}` is a domain
because `q` is a point of the regular surface `S`. -/
theorem exists_unit_of_map_span_eq {A B : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] {f g : A} (hf : f ≠ 0)
    (h : Ideal.map (algebraMap A B) (Ideal.span {f}) = Ideal.map (algebraMap A B) (Ideal.span {g})) :
    ∃ u : Aˣ, g = f * u := by
  have hfg : Ideal.span {f} = Ideal.span {g} := Ideal.map_injective_of_faithfullyFlat h
  have h1 : g ∈ Ideal.span ({f} : Set A) := hfg ▸ Ideal.subset_span (Set.mem_singleton g)
  have h2 : f ∈ Ideal.span ({g} : Set A) := hfg.symm ▸ Ideal.subset_span (Set.mem_singleton f)
  rw [Ideal.mem_span_singleton] at h1 h2
  obtain ⟨u, hu⟩ := h1
  obtain ⟨w, hw⟩ := h2
  refine ⟨Units.mkOfMulEqOne u w ?_, hu⟩
  have : f * (u * w) = f * 1 := by
    rw [mul_one, ← mul_assoc, ← hu, hw]
  exact mul_left_cancel₀ hf this

/-- **The same descent without the `f ≠ 0` hypothesis, in the form an equality of principal ideals
forces a unit multiple after extension.**  Version of `exists_unit_of_map_span_eq` where the
non-vanishing hypothesis is stated as `Ideal.span {f} ≠ ⊥` (equivalently `f ≠ 0` in a domain); it is
recorded separately because the geometric consumer frequently has the ideal-theoretic form. -/
theorem exists_unit_of_map_span_eq' {A B : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] {f g : A} (hf : Ideal.span {f} ≠ ⊥)
    (h : Ideal.map (algebraMap A B) (Ideal.span {f}) = Ideal.map (algebraMap A B) (Ideal.span {g})) :
    ∃ u : Aˣ, g = f * u := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (by simp)
  exact exists_unit_of_map_span_eq hf0 h

end Work.MotV5
