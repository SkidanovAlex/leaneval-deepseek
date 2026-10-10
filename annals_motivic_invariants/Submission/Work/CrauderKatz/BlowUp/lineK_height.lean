/-
Copyright (c) 2026 the annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.LineDefs
import Submission.Work.CrauderKatz.BlowUp.height_thickK

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.BlowUp.lineK_height`

We prove `(lineK 𝕜).height = 1` for `lineK 𝕜 = (x, ε) ⊂ 𝕜[x,t,z,ε]/(ε², x·ε)`, the
three-dimensional analogue of `height_thickK`.

The ideal `(x, ε)` is the preimage of the principal prime `(X 0) ⊂ 𝕜[X,Y,Z]` under the surjection
`𝕜[x,t,z,ε]/(ε², x·ε) ↠ 𝕜[X,Y,Z]` killing `ε`.  Since that surjection has kernel inside the
nilradical, it induces an order isomorphism of prime spectra, preserving heights of primes.  The
general height-preservation lemma `height_comap_eq_of_surjective` is imported from
`Submission.Work.CrauderKatz.BlowUp.height_thickK`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.CrauderKatz.BlowUp

noncomputable section

open MvPolynomial
open Ideal

variable (𝕜 : Type) [Field 𝕜]

/-! ### The surjection `𝕜[x,t,z,ε] ↠ 𝕜[X,Y,Z]` killing `ε` -/

/-- The target ideal `(X) ⊂ 𝕜[X,Y,Z]` of the map sending `x ↦ X`. -/
def threeIdeal : Ideal (MvPolynomial (Fin 3) 𝕜) := Ideal.span {MvPolynomial.X 0}

/-- The `𝕜`-algebra map `𝕜[X,Y,Z] →+* 𝕜[X₀,X₁,X₂,X₃]` with `X ↦ X 0`, `Y ↦ X 1`, `Z ↦ X 2`. -/
def toFour : MvPolynomial (Fin 3) 𝕜 →+* MvPolynomial (Fin 4) 𝕜 :=
  (MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4)) :
    MvPolynomial (Fin 3) 𝕜 →ₐ[𝕜] MvPolynomial (Fin 4) 𝕜).toRingHom

/-- The ring hom `𝕜[X₀,X₁,X₂,X₃] →+* 𝕜[X,Y,Z]` with `X₀ ↦ X`, `X₁ ↦ Y`, `X₂ ↦ Z`, `X₃ ↦ 0`. -/
def killEZ : MvPolynomial (Fin 4) 𝕜 →+* MvPolynomial (Fin 3) 𝕜 :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
        (0 : MvPolynomial (Fin 3) 𝕜)] : Fin 4 → _)

@[simp] lemma killEZ_C (a : 𝕜) : killEZ 𝕜 (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ a

@[simp] lemma killEZ_X0 : killEZ 𝕜 (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [killEZ]

@[simp] lemma killEZ_X1 : killEZ 𝕜 (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  simp [killEZ]

@[simp] lemma killEZ_X2 : killEZ 𝕜 (MvPolynomial.X 2) = MvPolynomial.X 2 := by
  simp [killEZ]

@[simp] lemma killEZ_X3 : killEZ 𝕜 (MvPolynomial.X 3) = 0 := by
  simp [killEZ]

/-- `toFour` is a section of `killEZ`. -/
lemma killEZ_toFour : (killEZ 𝕜).comp (toFour 𝕜) = RingHom.id (MvPolynomial (Fin 3) 𝕜) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [toFour, killEZ]
  · intro i; fin_cases i <;> simp [toFour, killEZ]

lemma killEZ_surjective : Function.Surjective (killEZ 𝕜) := fun q =>
  ⟨toFour 𝕜 q, RingHom.congr_fun (killEZ_toFour 𝕜) q⟩

@[simp] lemma toFour_X0 : toFour 𝕜 (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [toFour]

@[simp] lemma toFour_X1 : toFour 𝕜 (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  simp [toFour]

@[simp] lemma toFour_X2 : toFour 𝕜 (MvPolynomial.X 2) = MvPolynomial.X 2 := by
  simp [toFour]

/-- A `𝕜[X₀,X₁,X₂,X₃]`-element differs from its `X₃ = 0` reduction by a multiple of `X₃`. -/
theorem killEZ_sub_toFour_mem (p : MvPolynomial (Fin 4) 𝕜) :
    p - toFour 𝕜 (killEZ 𝕜 p) ∈
      Ideal.span {(MvPolynomial.X 3 : MvPolynomial (Fin 4) 𝕜)} := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [toFour, killEZ]
  | add p q hp hq =>
      have h : (p + q) - toFour 𝕜 (killEZ 𝕜 (p + q)) =
          (p - toFour 𝕜 (killEZ 𝕜 p)) + (q - toFour 𝕜 (killEZ 𝕜 q)) := by
        simp only [map_add]; ring
      rw [h]; exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
      have hS : (MvPolynomial.X n - toFour 𝕜 (killEZ 𝕜 (MvPolynomial.X n))) ∈
          Ideal.span {(MvPolynomial.X 3 : MvPolynomial (Fin 4) 𝕜)} := by
        fin_cases n <;> simp [toFour, killEZ]
      have hrew : p * MvPolynomial.X n - toFour 𝕜 (killEZ 𝕜 (p * MvPolynomial.X n)) =
          toFour 𝕜 (killEZ 𝕜 p) *
              (MvPolynomial.X n - toFour 𝕜 (killEZ 𝕜 (MvPolynomial.X n)))
            + (p - toFour 𝕜 (killEZ 𝕜 p)) * MvPolynomial.X n := by
        simp only [map_mul]; ring
      rw [hrew]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hS) (Ideal.mul_mem_right _ _ hp)

/-! ### The induced surjection on the quotient `R = 𝕜[x,t,z,ε]/(ε², x·ε)` -/

lemma lineI_le_ker_killEZ : lineI 𝕜 ≤ RingHom.ker (killEZ 𝕜) := by
  rw [lineI, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · change killEZ 𝕜 (MvPolynomial.X 3 ^ 2) = 0
    rw [map_pow, killEZ_X3]; simp
  · change killEZ 𝕜 (MvPolynomial.X 0 * MvPolynomial.X 3) = 0
    rw [map_mul, killEZ_X0, killEZ_X3]; simp

/-- The surjection `R 𝕜 ↠ 𝕜[X,Y,Z]` killing `ε`. -/
def killEZBar : lineRing 𝕜 →+* MvPolynomial (Fin 3) 𝕜 :=
  Ideal.Quotient.lift (lineI 𝕜) (killEZ 𝕜) (fun a ha => lineI_le_ker_killEZ 𝕜 ha)

@[simp] lemma killEZBar_mk (p : MvPolynomial (Fin 4) 𝕜) :
    killEZBar 𝕜 (Ideal.Quotient.mk (lineI 𝕜) p) = killEZ 𝕜 p :=
  Ideal.Quotient.lift_mk (lineI 𝕜) (killEZ 𝕜)
    (fun a ha => lineI_le_ker_killEZ 𝕜 ha) (a := p)

@[simp] lemma killEZBar_lineX : killEZBar 𝕜 (lineX 𝕜) = MvPolynomial.X 0 := by
  simp [lineX]

@[simp] lemma killEZBar_lineE : killEZBar 𝕜 (lineE 𝕜) = 0 := by
  simp [lineE]

lemma killEZBar_surjective : Function.Surjective (killEZBar 𝕜) := fun q =>
  ⟨Ideal.Quotient.mk (lineI 𝕜) (toFour 𝕜 q), by
    rw [killEZBar_mk]; exact RingHom.congr_fun (killEZ_toFour 𝕜) q⟩

lemma lineE_mem_nilradical : lineE 𝕜 ∈ nilradical (lineRing 𝕜) := by
  rw [mem_nilradical]
  exact IsNilpotent.mk (lineE 𝕜) 2 (lineE_sq 𝕜)

lemma ker_killEZBar_le_nilradical :
    RingHom.ker (killEZBar 𝕜) ≤ nilradical (lineRing 𝕜) := by
  intro r hr
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  change killEZBar 𝕜 (Ideal.Quotient.mk (lineI 𝕜) p) = 0 at hr
  rw [killEZBar_mk] at hr
  have hp : p ∈ Ideal.span {(MvPolynomial.X 3 : MvPolynomial (Fin 4) 𝕜)} := by
    have h := killEZ_sub_toFour_mem 𝕜 p
    rw [hr, map_zero, sub_zero] at h
    exact h
  have hmem : (Ideal.Quotient.mk (lineI 𝕜) p) ∈ Ideal.span {lineE 𝕜} := by
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk (lineI 𝕜)) hp
    rw [Ideal.map_span, Set.image_singleton] at h
    simpa [lineE] using h
  refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (lineE_mem_nilradical 𝕜)) hmem

lemma lineK_eq_comap :
    lineK 𝕜 = (threeIdeal 𝕜).comap (killEZBar 𝕜) := by
  apply le_antisymm
  · rw [lineK, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · change killEZBar 𝕜 (lineX 𝕜) ∈ threeIdeal 𝕜
      rw [killEZBar_lineX]
      exact Ideal.subset_span (Set.mem_singleton _)
    · change killEZBar 𝕜 (lineE 𝕜) ∈ threeIdeal 𝕜
      rw [killEZBar_lineE]
      exact Ideal.zero_mem _
  · intro r hr
    rw [Ideal.mem_comap] at hr
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [killEZBar_mk] at hr
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hr
    have hsub := killEZ_sub_toFour_mem 𝕜 p
    rw [hq, map_mul, toFour_X0] at hsub
    have hsplit : p = (MvPolynomial.X 0 * toFour 𝕜 q)
        + (p - (MvPolynomial.X 0 * toFour 𝕜 q)) := by ring
    have hp : p ∈ Ideal.span
        ({(MvPolynomial.X 0), (MvPolynomial.X 3)} : Set (MvPolynomial (Fin 4) 𝕜)) := by
      rw [hsplit]
      refine Ideal.add_mem _ ?_ (Ideal.span_mono ?_ hsub)
      · exact Ideal.mul_mem_right (toFour 𝕜 q) _
          (Ideal.subset_span (Set.mem_insert _ _))
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk (lineI 𝕜)) hp
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at h
    simpa [lineK, lineX, lineE] using h

/-! ### The target height computation -/

lemma height_threeIdeal : (threeIdeal 𝕜).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (MvPolynomial.X_ne_zero (0 : Fin 3)))
    (fun h => by
      have h2 := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced
        (P := (MvPolynomial.X 0 : MvPolynomial (Fin 3) 𝕜))).mp h
      rw [MvPolynomial.totalDegree_X] at h2
      exact one_ne_zero h2.2)

lemma isPrime_threeIdeal : (threeIdeal 𝕜).IsPrime :=
  (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero (0 : Fin 3))).mpr MvPolynomial.X_prime

theorem lineK_height (𝕜 : Type) [Field 𝕜] :
    (Work.CrauderKatz.BlowUp.lineK 𝕜).height = 1 := by
  haveI := isPrime_threeIdeal 𝕜
  rw [lineK_eq_comap 𝕜]
  exact (height_comap_eq_of_surjective (killEZBar 𝕜) (killEZBar_surjective 𝕜)
      (ker_killEZBar_le_nilradical 𝕜) (threeIdeal 𝕜)).trans (height_threeIdeal 𝕜)

end

end Work.CrauderKatz.BlowUp
