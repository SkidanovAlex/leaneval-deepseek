/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The unramified extension of prescribed degree, at an arbitrary universe

`Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg` is stated
for a number field `L : Type` (universe `0`) and produces `L' : Type`.  The Neukirch–Uchida
development needs the same construction for `L : Type u` and `L' : Type u`, so that the local
extension `L'_{q'} / L_q` can be embedded into a separable closure of `L_q` (`L_q : Type u`).
The proof is the proof of the original lemma, verbatim.
-/
import Mathlib
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg
import Submission.Commons.FieldTheory.Polynomial.exists_monic_irreducible_of_natDegree
import Submission.Commons.RingTheory.Polynomial.exists_monic_lift_of_surjective

open scoped NumberField IntermediateField
open Polynomial
open IsDedekindDomain.HeightOneSpectrum
open Commons.NumberTheory.NumberField
open Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option autoImplicit false

universe u v

namespace NK.TameStructureDeep.Degree

/-- **Gap A at an arbitrary universe.**  For a number field `L : Type u`, a finite place `q` and
`n ≥ 1`, there is `L' : Type u`, a finite extension endowed with a place `q'` over `q`, such that
the local extension `L'_{q'} / L_q` is unramified of degree `n`: `e(q'|q) = 1`, `f(q'|q) = n` and
in fact `[L' : L] = n`. -/
theorem exists_unramified_extension_of_inertiaDeg' {L : Type u} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (n : ℕ) (hn : 0 < n) :
    ∃ (L' : Type u) (_ : Field L') (_ : NumberField L') (_ : Algebra L L')
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L')),
      q'.asIdeal.LiesOver q.asIdeal ∧
      q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1 ∧
      q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) = n ∧
      Module.finrank L L' = n := by
  let R := 𝓞 L
  haveI hfinq : Finite (R ⧸ q.asIdeal) := finite_quotient_heightOneSpectrum q
  letI : Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  haveI : Fintype (R ⧸ q.asIdeal) := Fintype.ofFinite _
  obtain ⟨g, hgmonic, hgirr, hgdeg⟩ :=
    Commons.FieldTheory.Polynomial.exists_monic_irreducible_of_natDegree (F := R ⧸ q.asIdeal) n hn
  obtain ⟨f, hfmonic, hfdeg, hfmap⟩ :=
    Commons.RingTheory.Polynomial.exists_monic_lift_of_surjective
      (Ideal.Quotient.mk q.asIdeal) Ideal.Quotient.mk_surjective g hgmonic
  have hfndeg : f.natDegree = n := hfdeg.trans hgdeg
  let Ω := AlgebraicClosure L
  let φ : R →+* Ω := algebraMap R Ω
  have hφlead : φ f.leadingCoeff ≠ 0 := by
    rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero
  have hfdeg' : (f.map φ).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hfmonic.map φ).ne_zero,
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hφlead, hfndeg]
    exact_mod_cast hn.ne'
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root (f.map φ) hfdeg'
  have hθ0 : f.eval₂ φ θ = 0 := by rw [← Polynomial.eval_map φ θ]; exact hθ
  have hintR : IsIntegral R θ :=
    ⟨f, hfmonic, by simpa only [Polynomial.aeval_def, φ] using hθ0⟩
  let Lst : IntermediateField L Ω := L⟮θ⟯
  have hmem : θ ∈ Lst := IntermediateField.mem_adjoin_simple_self L θ
  have hcompRL : (algebraMap L Ω).comp (algebraMap R L) = algebraMap R Ω := by
    ext x; exact IsScalarTower.algebraMap_apply R L Ω x
  have hL0 : Polynomial.aeval θ (f.map (algebraMap R L)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcompRL]
    simpa only [φ] using hθ0
  have hintL : IsIntegral L θ := ⟨f.map (algebraMap R L), hfmonic.map _, hL0⟩
  haveI hfd : FiniteDimensional L Lst := IntermediateField.adjoin.finiteDimensional hintL
  haveI hnum : NumberField Lst := numberField_of_intermediateField (K := L) (K' := Ω) Lst
  obtain ⟨q', hq'⟩ := exists_heightOneSpectrum_liesOver (K := L) (L := Lst) q
  haveI hfinq' : Finite (𝓞 ↥Lst ⧸ q'.asIdeal) := finite_quotient_heightOneSpectrum q'
  have hcast : (algebraMap ↥Lst Ω) (⟨θ, hmem⟩ : ↥Lst) = θ := rfl
  -- ## the polynomial relation for `θ`
  have hA : Polynomial.aeval (⟨θ, hmem⟩ : ↥Lst) (f.map (algebraMap R L)) = 0 := by
    have h1 := Polynomial.map_aeval_eq_aeval_map (R := L) (S := ↥Lst) (T := Ω) (U := Ω)
      (φ := algebraMap L Ω) (ψ := algebraMap ↥Lst Ω) (by ext x; rfl)
      (f.map (algebraMap R L)) ⟨θ, hmem⟩
    have h2 : (algebraMap ↥Lst Ω)
        (Polynomial.aeval (⟨θ, hmem⟩ : ↥Lst) (f.map (algebraMap R L))) = 0 := by
      rw [h1, hcast]
      have h3 : (f.map (algebraMap R L)).map (algebraMap L Ω) = f.map (algebraMap R Ω) := by
        rw [Polynomial.map_map, hcompRL]
      rw [h3, Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
      exact hθ
    exact (algebraMap ↥Lst Ω).injective (by rw [h2, map_zero])
  have hA1 : Polynomial.aeval (⟨θ, hmem⟩ : ↥Lst) f = 0 := by
    rw [Polynomial.aeval_def,
      show algebraMap R ↥Lst = (algebraMap L ↥Lst).comp (algebraMap R L) from rfl,
      ← Polynomial.eval₂_map]
    exact hA
  have hIntA : IsIntegral (𝓞 L) (⟨θ, hmem⟩ : ↥Lst) := ⟨f, hfmonic, hA1⟩
  have hintZΩ : IsIntegral ℤ θ := isIntegral_trans (R := ℤ) (A := 𝓞 L) θ hintR
  have hintZ : IsIntegral ℤ (⟨θ, hmem⟩ : ↥Lst) :=
    IsIntegral.tower_bot (R := ℤ) (A := ↥Lst) (B := Ω) (algebraMap ↥Lst Ω).injective
      (by rw [hcast]; exact hintZΩ)
  let θ' : 𝓞 ↥Lst := ⟨⟨θ, hmem⟩, hintZ⟩
  have hθ'map : algebraMap (𝓞 ↥Lst) ↥Lst θ' = ⟨θ, hmem⟩ := rfl
  have hθ'aeval : Polynomial.aeval θ' f = 0 := by
    apply NumberField.RingOfIntegers.coe_injective (K := ↥Lst)
    rw [map_zero]
    have h5 := Polynomial.map_aeval_eq_aeval_map (R := R) (S := 𝓞 ↥Lst) (T := ↥Lst) (U := ↥Lst)
      (φ := algebraMap R ↥Lst) (ψ := algebraMap (𝓞 ↥Lst) ↥Lst)
      (by ext x; rfl) f θ'
    rw [h5, hθ'map]
    have h6 : f.map (algebraMap R ↥Lst) = (f.map (algebraMap R L)).map (algebraMap L ↥Lst) := by
      rw [Polynomial.map_map]
      congr 1
    rw [h6, ← Polynomial.aeval_eq_aeval_map (R := L) (S := ↥Lst) (T := ↥Lst)
      (φ := algebraMap L ↥Lst) (by ext x; rfl) (f.map (algebraMap R L)) ⟨θ, hmem⟩]
    exact hA
  -- ## the residue-field bound `n ≤ f`
  have hres : n ≤ q'.asIdeal.inertiaDeg R := by
    rw [← hgdeg]
    exact Commons.NumberTheory.NumberField.Completion.natDegree_le_inertiaDeg_of_aeval_eq_zero (R := R) (S := 𝓞 ↥Lst)
      q.asIdeal q'.asIdeal f g hgmonic hgirr hfmap θ' hθ'aeval
  -- ## the upper bound `[L' : L] ≤ n`
  have hLst_le : Module.finrank L ↥Lst ≤ n := by
    have hmin_dvd : minpoly L θ ∣ f.map (algebraMap R L) := minpoly.dvd L θ hL0
    have hne : f.map (algebraMap R L) ≠ 0 := (hfmonic.map _).ne_zero
    have h1 : (minpoly L θ).natDegree ≤ (f.map (algebraMap R L)).natDegree :=
      Polynomial.natDegree_le_of_dvd hmin_dvd hne
    have h2 : (f.map (algebraMap R L)).natDegree = n := by
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
      · exact hfndeg
      · rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero
    rw [IntermediateField.adjoin.finrank (K := L) hintL]
    omega
  -- ## the numerical conclusion
  letI : Algebra (q.adicCompletion L) (q'.adicCompletion ↥Lst) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q' hq')
  have hcompl_le : Module.finrank (q.adicCompletion L) (q'.adicCompletion ↥Lst) ≤
      Module.finrank L ↥Lst :=
    finrank_adicCompletion_le_finrank (K := L) (L := ↥Lst) q q' hq'
  have hfin_le : Module.finrank (q.adicCompletion L) (q'.adicCompletion ↥Lst) ≤ n :=
    hcompl_le.trans hLst_le
  have hmul := finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg (K := L) (L := ↥Lst) q q' hq'
  have hepos : 0 < q'.asIdeal.ramificationIdx R := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx q.asIdeal q'.asIdeal q.ne_bot]
    exact Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q'.asIdeal q.ne_bot)
  have hfqpos : 0 < q'.asIdeal.inertiaDeg R := lt_of_lt_of_le hn hres
  have h1 : q'.asIdeal.ramificationIdx R * q'.asIdeal.inertiaDeg R ≤ n := by
    rw [hmul]; exact hfin_le
  have he1 : q'.asIdeal.ramificationIdx R = 1 := by
    have hle : q'.asIdeal.ramificationIdx R ≤ 1 :=
      Nat.le_of_mul_le_mul_right (le_trans h1 (by rw [one_mul]; exact hres)) hfqpos
    omega
  have hfq : q'.asIdeal.inertiaDeg R = n := by
    have := h1
    rw [he1, one_mul] at this
    omega
  have hfrank : Module.finrank L ↥Lst = n := by
    have h2 : Module.finrank (q.adicCompletion L) (q'.adicCompletion ↥Lst) = n := by
      rw [← hmul, he1, one_mul, hfq]
    omega
  exact ⟨Lst, inferInstance, inferInstance, inferInstance, q', hq', he1, hfq, hfrank⟩



end NK.TameStructureDeep.Degree
