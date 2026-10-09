/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Detecting irreducibility by reduction modulo the maximal ideal

Let `R` be a local domain with fraction field `K` (for instance the ring of integers `𝒪[k]`
of a non-archimedean local field `k`, which is a discrete valuation ring).  A monic polynomial
`f ∈ R[X]` whose reduction mod the maximal ideal is irreducible is itself irreducible: if
`f = a * b` is a nontrivial factorisation of a monic polynomial, then the leading coefficients
of `a` and `b` are units, so `a` and `b` remain of positive degree after reduction, and hence
reduce to non-units of `κ[X]` — contradicting the irreducibility of the reduction.

Combining this with Gauss's lemma for integrally closed domains
(`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`) gives the main result of this
file: irreducibility of the reduction of a monic polynomial over `𝒪[k]` implies irreducibility
of the polynomial over the local field `k` itself.

## Main results

* `Work.LocalFields.monic_irreducible_of_irreducible_map_residue`
* `Work.LocalFields.irreducible_map_of_irreducible_reduction`
-/
import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.LocalFieldAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open Polynomial

/-- **Irreducibility is detected by reduction modulo the maximal ideal.**  If `R` is a local
domain and `f ∈ R[X]` is monic with irreducible reduction `f mod 𝔪` in the residue field, then
`f` is irreducible.

(Note that `R` is assumed to be a domain: otherwise a non-unit constant polynomial could occur
as a factor, and the statement fails, e.g. for `R = ℤ/4`.) -/
theorem monic_irreducible_of_irreducible_map_residue {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] {f : R[X]} (hf : f.Monic)
    (h : Irreducible (f.map (IsLocalRing.residue R))) : Irreducible f := by
  rw [irreducible_iff] at h ⊢
  refine ⟨fun hunit => h.1 (hunit.map (Polynomial.mapRingHom (IsLocalRing.residue R))),
    fun a b hab => ?_⟩
  by_contra hc
  rw [not_or] at hc
  obtain ⟨ha, hb⟩ := hc
  -- The leading coefficients of `a` and `b` multiply to `1`, hence are units.
  have h1 : a.leadingCoeff * b.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hab, Monic.leadingCoeff hf]
  have hua : IsUnit a.leadingCoeff := isUnit_iff_exists_inv.mpr ⟨b.leadingCoeff, h1⟩
  have hub : IsUnit b.leadingCoeff :=
    isUnit_iff_exists_inv.mpr ⟨a.leadingCoeff, by rw [mul_comm]; exact h1⟩
  -- So a non-unit factor has positive degree.
  have hda : 1 ≤ a.natDegree := by
    by_contra hlt
    rw [not_le, Nat.lt_one_iff] at hlt
    refine ha ?_
    have hlc : a.leadingCoeff = a.coeff 0 := by rw [leadingCoeff, hlt]
    rw [isUnit_iff]
    exact ⟨a.coeff 0, hlc ▸ hua, (eq_C_of_natDegree_eq_zero hlt).symm⟩
  have hdb : 1 ≤ b.natDegree := by
    by_contra hlt
    rw [not_le, Nat.lt_one_iff] at hlt
    refine hb ?_
    have hlc : b.leadingCoeff = b.coeff 0 := by rw [leadingCoeff, hlt]
    rw [isUnit_iff]
    exact ⟨b.coeff 0, hlc ▸ hub, (eq_C_of_natDegree_eq_zero hlt).symm⟩
  -- Reduction does not change the degree, since the leading coefficients are units.
  have hna : (a.map (IsLocalRing.residue R)).natDegree = a.natDegree :=
    natDegree_map_eq_of_isUnit_leadingCoeff _ hua
  have hnb : (b.map (IsLocalRing.residue R)).natDegree = b.natDegree :=
    natDegree_map_eq_of_isUnit_leadingCoeff _ hub
  -- Hence the reductions of `a` and `b` are not units in `κ[X]`: units there are constants.
  have hnu : ¬ IsUnit (a.map (IsLocalRing.residue R)) := by
    intro hunit
    rw [isUnit_iff] at hunit
    obtain ⟨r, -, hrC⟩ := hunit
    rw [← hna, ← hrC, natDegree_C] at hda
    omega
  have hnu' : ¬ IsUnit (b.map (IsLocalRing.residue R)) := by
    intro hunit
    rw [isUnit_iff] at hunit
    obtain ⟨r, -, hrC⟩ := hunit
    rw [← hnb, ← hrC, natDegree_C] at hdb
    omega
  -- But the reduction of `f` is the product of these two non-units, contradiction.
  have hprod : f.map (IsLocalRing.residue R) =
      (a.map (IsLocalRing.residue R)) * (b.map (IsLocalRing.residue R)) := by
    rw [hab, Polynomial.map_mul]
  rcases h.2 hprod with h' | h'
  · exact hnu h'
  · exact hnu' h'

/-- **Irreducibility over a local field is detected by reduction.**  If `f` is a monic polynomial
with coefficients in the ring of integers `𝒪[k]` of a non-archimedean local field `k`, and the
reduction of `f` modulo the maximal ideal of `𝒪[k]` is irreducible over the residue field, then
`f`, viewed as a polynomial over `k`, is irreducible.

This is the "easy" direction of Hensel's lemma for factorisations of monic polynomials: the
converse direction (lifting a factorisation of the reduction) is what requires Hensel's lemma,
whereas irreducibility of the reduction propagates upwards by Gauss's lemma alone. -/
theorem irreducible_map_of_irreducible_reduction {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [Work.LocalFields.IsLocalField k]
    {f : Polynomial (Valued.integer k)} (hf : f.Monic)
    (h : Irreducible (f.map (IsLocalRing.residue (Valued.integer k)))) :
    Irreducible (f.map (algebraMap (Valued.integer k) k)) :=
  -- Gauss's lemma for the integrally closed domain `𝒪[k]`, whose fraction field is `k`,
  -- reduces the claim over `k` to the claim over `𝒪[k]`.
  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hf).mp
    (monic_irreducible_of_irreducible_map_residue hf h)

end Work.LocalFields
