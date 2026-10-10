/-
Copyright (c) 2026 the annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.LineDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.BlowUp.isPrime_nilradical_lineRing`

The nilradical of the thickened chart ring `R 𝕜 = 𝕜[x,t,z,ε]/(ε², x·ε)` is a *prime* ideal.

The ring `lineRing 𝕜 = 𝕜[X₀,X₁,X₂,X₃]/(X₃², X₀X₃)` consists of the elements `a + b·ε`
(`ε = lineE 𝕜`, `ε² = 0`, `x·ε = 0`), so its only nilpotents are the multiples of `ε`.  Hence

`nilradical (R 𝕜) = Ideal.span {lineE 𝕜}`,

and this ideal is prime because it is the image of the prime ideal `(X₃)` of `𝕜[X₀,X₁,X₂,X₃]`
under the (surjective) quotient map.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MvPolynomial

namespace Work.CrauderKatz.BlowUp

theorem isPrime_nilradical_lineRing (𝕜 : Type) [Field 𝕜] :
    (nilradical (Work.CrauderKatz.BlowUp.lineRing 𝕜)).IsPrime := by
  -- `ε = lineE 𝕜` is nilpotent (`ε² = 0`), so it lies in the nilradical.
  have hE_nil : lineE 𝕜 ∈ nilradical (lineRing 𝕜) := by
    rw [mem_nilradical]
    exact ⟨2, lineE_sq 𝕜⟩
  have hle1 : Ideal.span {lineE 𝕜} ≤ nilradical (lineRing 𝕜) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hE_nil)
  -- `(ε)` is prime: it is the image of the prime ideal `(X₃)` of `𝕜[X₀,X₁,X₂,X₃]`.
  have hprime : (Ideal.span {lineE 𝕜}).IsPrime := by
    have hker : RingHom.ker (Ideal.Quotient.mk (lineI 𝕜)) ≤
        Ideal.span ({MvPolynomial.X 3} : Set (MvPolynomial (Fin 4) 𝕜)) := by
      rw [Ideal.mk_ker, lineI, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, ?_⟩
      · rw [sq]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
    haveI : (Ideal.span ({MvPolynomial.X 3} : Set (MvPolynomial (Fin 4) 𝕜))).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime (MvPolynomial.X_prime (σ := Fin 4) (R := 𝕜) (i := 3))
    have h := Ideal.map_isPrime_of_surjective (Ideal.Quotient.mk_surjective (I := lineI 𝕜)) hker
    rwa [Ideal.map_span, Set.image_singleton] at h
  -- Conversely the nilradical is contained in `(ε)`, since the latter is a prime containing `⊥`.
  have hle2 : nilradical (lineRing 𝕜) ≤ Ideal.span {lineE 𝕜} := by
    haveI := hprime
    exact nilradical_le_prime _
  rw [le_antisymm hle2 hle1]
  exact hprime

end Work.CrauderKatz.BlowUp
