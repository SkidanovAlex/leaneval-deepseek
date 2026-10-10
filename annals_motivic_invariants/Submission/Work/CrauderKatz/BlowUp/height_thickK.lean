/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.ThickDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `height_thickK` : the height of the ideal `(x, ε)` of the thickened chart ring

We prove `(thickK 𝕜).height = 1` for `thickK 𝕜 = (x, ε) ⊂ 𝕜[x,t,ε]/(ε², x·ε)`.

The ideal `(x, ε)` is the preimage of the principal prime `(X 0) ⊂ 𝕜[X,Y]` under the surjection
`𝕜[x,t,ε]/(ε², x·ε) ↠ 𝕜[X,Y]` killing `ε`.  Since that surjection has kernel inside the
nilradical, it induces an order isomorphism of prime spectra, preserving heights of primes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.CrauderKatz.BlowUp

noncomputable section

open MvPolynomial

open Ideal

/-! ### A general height-preservation lemma for surjections with nilpotent kernel -/

/-- A surjective ring homomorphism whose kernel is contained in the nilradical induces an order
isomorphism of prime spectra (on prime ideals, `comap f` is inverse to `map f`). -/
def primeSpectrumOrderIsoOfSurjective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical R) :
    PrimeSpectrum S ≃o PrimeSpectrum R where
  toFun p := PrimeSpectrum.comap f p
  invFun p := ⟨p.asIdeal.map f,
    Ideal.map_isPrime_of_surjective hf (hker.trans (nilradical_le_prime p.asIdeal))⟩
  left_inv p := by
    apply PrimeSpectrum.ext
    show Ideal.map f (Ideal.comap f p.asIdeal) = p.asIdeal
    exact Ideal.map_comap_of_surjective f hf p.asIdeal
  right_inv p := by
    apply PrimeSpectrum.ext
    show Ideal.comap f (Ideal.map f p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' f hf, sup_eq_left]
    exact hker.trans (nilradical_le_prime p.asIdeal)
  map_rel_iff' := by
    intro p q
    exact Ideal.comap_le_comap_iff_of_surjective f hf p.asIdeal q.asIdeal

/-- If `f : R →+* S` is a surjection whose kernel lies in the nilradical of `R`, then the
preimage of a prime ideal has the same height. -/
theorem height_comap_eq_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (hker : RingHom.ker f ≤ nilradical R)
    (P : Ideal S) [P.IsPrime] : (P.comap f).height = P.height := by
  have hmain : (primeSpectrumOrderIsoOfSurjective f hf hker ⟨P, ‹P.IsPrime›⟩).asIdeal.height
      = P.height :=
    calc (primeSpectrumOrderIsoOfSurjective f hf hker ⟨P, ‹P.IsPrime›⟩).asIdeal.height
        = Order.height (primeSpectrumOrderIsoOfSurjective f hf hker ⟨P, ‹P.IsPrime›⟩) :=
            PrimeSpectrum.height_eq_orderHeight _
      _ = Order.height (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum S) := Order.height_orderIso _ _
      _ = P.height := (PrimeSpectrum.height_eq_orderHeight _).symm
  rwa [show (primeSpectrumOrderIsoOfSurjective f hf hker ⟨P, ‹P.IsPrime›⟩).asIdeal
      = (P.comap f) from rfl] at hmain

/-! ### The surjection `𝕜[x,t,ε] ↠ 𝕜[X,Y]` killing `ε` -/

variable (𝕜 : Type) [Field 𝕜]

/-- The target ideal `(X) ⊂ 𝕜[X,Y]` of the map sending `x ↦ X`. -/
def twoIdeal : Ideal (MvPolynomial (Fin 2) 𝕜) := Ideal.span {MvPolynomial.X 0}

/-- The `𝕜`-algebra map `𝕜[X,Y] →+* 𝕜[X₀,X₁,X₂]` with `X ↦ X 0`, `Y ↦ X 1`. -/
def toThree : MvPolynomial (Fin 2) 𝕜 →+* MvPolynomial (Fin 3) 𝕜 :=
  (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 3)) :
    MvPolynomial (Fin 2) 𝕜 →ₐ[𝕜] MvPolynomial (Fin 3) 𝕜).toRingHom

/-- The ring hom `𝕜[X₀,X₁,X₂] →+* 𝕜[X,Y]` with `X₀ ↦ X`, `X₁ ↦ Y`, `X₂ ↦ 0`. -/
def killE : MvPolynomial (Fin 3) 𝕜 →+* MvPolynomial (Fin 2) 𝕜 :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) 𝕜)] : Fin 3 → _)

@[simp] lemma killE_C (a : 𝕜) : killE 𝕜 (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ a

@[simp] lemma killE_X0 : killE 𝕜 (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [killE]

@[simp] lemma killE_X1 : killE 𝕜 (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  simp [killE]

@[simp] lemma killE_X2 : killE 𝕜 (MvPolynomial.X 2) = 0 := by
  simp [killE]

/-- `toThree` is a section of `killE`. -/
lemma killE_toThree : (killE 𝕜).comp (toThree 𝕜) = RingHom.id (MvPolynomial (Fin 2) 𝕜) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [toThree, killE]
  · intro i; fin_cases i <;> simp [toThree, killE]

lemma killE_surjective : Function.Surjective (killE 𝕜) := fun q =>
  ⟨toThree 𝕜 q, RingHom.congr_fun (killE_toThree 𝕜) q⟩

@[simp] lemma toThree_X0 : toThree 𝕜 (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [toThree]

@[simp] lemma toThree_X1 : toThree 𝕜 (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  simp [toThree]

/-- A `𝕜[X₀,X₁,X₂]`-element differs from its `X₂ = 0` reduction by a multiple of `X₂`. -/
theorem killE_sub_toThree_mem (p : MvPolynomial (Fin 3) 𝕜) :
    p - toThree 𝕜 (killE 𝕜 p) ∈
      Ideal.span {(MvPolynomial.X 2 : MvPolynomial (Fin 3) 𝕜)} := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [toThree, killE]
  | add p q hp hq =>
      have h : (p + q) - toThree 𝕜 (killE 𝕜 (p + q)) =
          (p - toThree 𝕜 (killE 𝕜 p)) + (q - toThree 𝕜 (killE 𝕜 q)) := by
        simp only [map_add]; ring
      rw [h]; exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
      have hS : (MvPolynomial.X n - toThree 𝕜 (killE 𝕜 (MvPolynomial.X n))) ∈
          Ideal.span {(MvPolynomial.X 2 : MvPolynomial (Fin 3) 𝕜)} := by
        fin_cases n <;> simp [toThree, killE]
      have hrew : p * MvPolynomial.X n - toThree 𝕜 (killE 𝕜 (p * MvPolynomial.X n)) =
          toThree 𝕜 (killE 𝕜 p) *
              (MvPolynomial.X n - toThree 𝕜 (killE 𝕜 (MvPolynomial.X n)))
            + (p - toThree 𝕜 (killE 𝕜 p)) * MvPolynomial.X n := by
        simp only [map_mul]; ring
      rw [hrew]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hS) (Ideal.mul_mem_right _ _ hp)

/-! ### The induced surjection on the quotient `R = 𝕜[x,t,ε]/(ε², x·ε)` -/

lemma thickI_le_ker_killE : thickI 𝕜 ≤ RingHom.ker (killE 𝕜) := by
  rw [thickI, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · change killE 𝕜 (MvPolynomial.X 2 ^ 2) = 0
    rw [map_pow, killE_X2]; simp
  · change killE 𝕜 (MvPolynomial.X 0 * MvPolynomial.X 2) = 0
    rw [map_mul, killE_X0, killE_X2]; simp

/-- The surjection `R 𝕜 ↠ 𝕜[X,Y]` killing `ε`. -/
def killEBar : thickRing 𝕜 →+* MvPolynomial (Fin 2) 𝕜 :=
  Ideal.Quotient.lift (thickI 𝕜) (killE 𝕜) (fun a ha => thickI_le_ker_killE 𝕜 ha)

@[simp] lemma killEBar_mk (p : MvPolynomial (Fin 3) 𝕜) :
    killEBar 𝕜 (Ideal.Quotient.mk (thickI 𝕜) p) = killE 𝕜 p :=
  Ideal.Quotient.lift_mk (thickI 𝕜) (killE 𝕜)
    (fun a ha => thickI_le_ker_killE 𝕜 ha) (a := p)

@[simp] lemma killEBar_thickX : killEBar 𝕜 (thickX 𝕜) = MvPolynomial.X 0 := by
  simp [thickX]

@[simp] lemma killEBar_thickE : killEBar 𝕜 (thickE 𝕜) = 0 := by
  simp [thickE]

lemma killEBar_surjective : Function.Surjective (killEBar 𝕜) := fun q =>
  ⟨Ideal.Quotient.mk (thickI 𝕜) (toThree 𝕜 q), by
    rw [killEBar_mk]; exact RingHom.congr_fun (killE_toThree 𝕜) q⟩

lemma thickE_mem_nilradical : thickE 𝕜 ∈ nilradical (thickRing 𝕜) := by
  rw [mem_nilradical]
  exact IsNilpotent.mk (thickE 𝕜) 2 (thickE_sq 𝕜)

lemma ker_killEBar_le_nilradical :
    RingHom.ker (killEBar 𝕜) ≤ nilradical (thickRing 𝕜) := by
  intro r hr
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  change killEBar 𝕜 (Ideal.Quotient.mk (thickI 𝕜) p) = 0 at hr
  rw [killEBar_mk] at hr
  have hp : p ∈ Ideal.span {(MvPolynomial.X 2 : MvPolynomial (Fin 3) 𝕜)} := by
    have h := killE_sub_toThree_mem 𝕜 p
    rw [hr, map_zero, sub_zero] at h
    exact h
  have hmem : (Ideal.Quotient.mk (thickI 𝕜) p) ∈ Ideal.span {thickE 𝕜} := by
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk (thickI 𝕜)) hp
    rw [Ideal.map_span, Set.image_singleton] at h
    simpa [thickE] using h
  refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (thickE_mem_nilradical 𝕜)) hmem

lemma thickK_eq_comap :
    thickK 𝕜 = (twoIdeal 𝕜).comap (killEBar 𝕜) := by
  apply le_antisymm
  · rw [thickK, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨?_, ?_⟩
    · change killEBar 𝕜 (thickX 𝕜) ∈ twoIdeal 𝕜
      rw [killEBar_thickX]
      exact Ideal.subset_span (Set.mem_singleton _)
    · change killEBar 𝕜 (thickE 𝕜) ∈ twoIdeal 𝕜
      rw [killEBar_thickE]
      exact Ideal.zero_mem _
  · intro r hr
    rw [Ideal.mem_comap] at hr
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [killEBar_mk] at hr
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hr
    have hsub := killE_sub_toThree_mem 𝕜 p
    rw [hq, map_mul, toThree_X0] at hsub
    have hsplit : p = (MvPolynomial.X 0 * toThree 𝕜 q)
        + (p - (MvPolynomial.X 0 * toThree 𝕜 q)) := by ring
    have hp : p ∈ Ideal.span
        ({(MvPolynomial.X 0), (MvPolynomial.X 2)} : Set (MvPolynomial (Fin 3) 𝕜)) := by
      rw [hsplit]
      refine Ideal.add_mem _ ?_ (Ideal.span_mono ?_ hsub)
      · exact Ideal.mul_mem_right (toThree 𝕜 q) _
          (Ideal.subset_span (Set.mem_insert _ _))
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk (thickI 𝕜)) hp
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at h
    simpa [thickK, thickX, thickE] using h

/-! ### The target height computation -/

lemma height_twoIdeal : (twoIdeal 𝕜).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (MvPolynomial.X_ne_zero (0 : Fin 2)))
    (fun h => by
      have h2 := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced
        (P := (MvPolynomial.X 0 : MvPolynomial (Fin 2) 𝕜))).mp h
      rw [MvPolynomial.totalDegree_X] at h2
      exact one_ne_zero h2.2)

lemma isPrime_twoIdeal : (twoIdeal 𝕜).IsPrime :=
  (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero (0 : Fin 2))).mpr MvPolynomial.X_prime

theorem height_thickK (𝕜 : Type) [Field 𝕜] : (Work.CrauderKatz.BlowUp.thickK 𝕜).height = 1 := by
  haveI := isPrime_twoIdeal 𝕜
  rw [thickK_eq_comap 𝕜]
  exact (height_comap_eq_of_surjective (killEBar 𝕜) (killEBar_surjective 𝕜)
      (ker_killEBar_le_nilradical 𝕜) (twoIdeal 𝕜)).trans (height_twoIdeal 𝕜)

end

end Work.CrauderKatz.BlowUp
