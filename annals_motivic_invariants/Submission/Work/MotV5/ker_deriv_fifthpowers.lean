/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV5

# The kernel of a derivation of `L(E)` in characteristic 5 consists of fifth powers

Target of this file: `Work.MotV5.ker_deriv_fifthpowers`: for a Weierstrass curve `E` over an
algebraically closed field `N` of characteristic `5`, and any `N`-derivation `D` of the function
field `Func E = N(E)` with `D (genX E) ≠ 0`, every element of `ker D` is a fifth power.

The proof is by the following route (see `MotV5/KerDefs.lean` for the definition of the subfield
`fifthPowers E = {s ^ 5 | s : Func E}`):

* `ker_deriv_eq_fifthpowers_of_generator` — the general mechanism: if `F` is a subfield of a field
  `K` of characteristic `5` which *is* the set of fifth powers, if a derivation `D` of `K` kills
  `F`, if `D x ≠ 0` and `K = F(x)`, then `ker D ⊆ F`.  (`F ⊆ ker D` and `ker D` is a subfield, so
  `F ≤ ker D ≤ K = F(x)` with `[K : F] | 5`; hence `ker D = F`.)
* `adjoin_genX_genY_eq_top` — `Func E` is generated over `N` by `genX E` and `genY E`;
* `genY_mem_fifthPowers_adjoin_genX` (sibling file) — `genY E ∈ (fifthPowers E)⟮genX E⟯`,
  so `Func E = (fifthPowers E)⟮genX E⟯`;
* instantiate the general mechanism with `F = fifthPowers E`, `x = genX E`.

## Tags

elliptic curve, function field, derivation, inseparable extension
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.MotV5.KerDefs
import Submission.Work.MotV5.HurwitzLeaves.genY_mem_fifthPowers_adjoin_genX

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial
open scoped IntermediateField

namespace Work.MotV5

open Work.MotV5.HurwitzLeaves

/-! ## The general mechanism -/

/-- **The kernel of a derivation is the field of fifth powers**, when the whole field is generated
by a single element `x` over the field `F` of fifth powers.

Hypotheses: `K` has characteristic `5`; `F ≤ K` is a subfield which is exactly the image of the
Frobenius endomorphism `z ↦ z ^ 5` (both inclusions); the derivation `D` of `K` kills `F`; `x ∈ K`
with `D x ≠ 0`; and `K = F(x)`.

Conclusion: every `h` with `D h = 0` is a fifth power (indeed lies in `F`). -/
theorem ker_deriv_eq_fifthpowers_of_generator {N K : Type*} [Field N] [Field K] [Algebra N K]
    [CharP K 5] (F : IntermediateField N K) [CharP F 5]
    (D : Derivation N K K) (hkillF : ∀ c : F, D (c : K) = 0)
    (hF : ∀ z : K, z ∈ F ↔ ∃ s : K, s ^ 5 = z)
    (x : K) (hx : D x ≠ 0) (hgen : F⟮x⟯ = ⊤) :
    ∀ h : K, D h = 0 → ∃ s : K, h = s ^ 5 := by
  -- `K` is purely inseparable over `F`
  haveI hpi : IsPurelyInseparable F K := by
    rw [isPurelyInseparable_iff_pow_mem F 5]
    intro z
    exact ⟨1, ⟨⟨z ^ 5, (hF (z ^ 5)).mpr ⟨z, rfl⟩⟩, rfl⟩⟩
  -- `x` is integral over `F`, and `x ∉ F`
  have hx5 : x ^ 5 ∈ F := (hF (x ^ 5)).mpr ⟨x, rfl⟩
  have hxint : IsIntegral F x := by
    refine IsIntegral.of_pow (n := 5) (by norm_num) ?_
    have hcast : (x ^ 5 : K) = algebraMap F K (⟨x ^ 5, hx5⟩ : F) := rfl
    rw [hcast]
    exact isIntegral_algebraMap
  -- the minimal polynomial of `x` over `F` is `X ^ (5 ^ n) - C c`
  obtain ⟨n, c, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F 5 x
  have hdeg : (minpoly F x).natDegree = 5 ^ n := by
    rw [hmin, Polynomial.natDegree_X_pow_sub_C]
  have hdiv : minpoly F x ∣ Polynomial.X ^ 5 - Polynomial.C (⟨x ^ 5, hx5⟩ : F) := by
    refine minpoly.dvd F x ?_
    rw [map_sub, map_pow, aeval_X, aeval_C]
    exact sub_eq_zero.mpr rfl
  have hq : (Polynomial.X ^ 5 - Polynomial.C (⟨x ^ 5, hx5⟩ : F)) ≠ 0 := by
    intro h0
    have hnd := Polynomial.natDegree_X_pow_sub_C (R := F) (n := 5) (r := (⟨x ^ 5, hx5⟩ : F))
    rw [h0, Polynomial.natDegree_zero] at hnd
    exact absurd hnd (by norm_num)
  have hle : 5 ^ n ≤ 5 := by
    have hd := Polynomial.natDegree_le_of_dvd hdiv hq
    rw [Polynomial.natDegree_X_pow_sub_C] at hd
    simpa [hdeg] using hd
  have hnle : n ≤ 1 := by
    by_contra hn
    push_neg at hn
    have h2 : 5 ^ 2 ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h25 : 25 ≤ 5 ^ n := by simpa using h2
    omega
  have hn0 : n ≠ 0 := by
    intro hn0
    have h1 : (minpoly F x).natDegree = 1 := by rw [hdeg, hn0]; norm_num
    obtain ⟨c', hc'⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact hx (by rw [← hc']; exact hkillF c')
  have hn : n = 1 := by omega
  have hdeg5 : (minpoly F x).natDegree = 5 := by rw [hdeg, hn, pow_one]
  have hfin : Module.finrank ↥F ↥(F⟮x⟯) = 5 := by
    rw [IntermediateField.adjoin.finrank hxint, hdeg5]
  have hfinK : Module.finrank ↥F K = 5 := by
    rw [← IntermediateField.finrank_top', ← hgen]
    exact hfin
  -- the kernel of `D` as an intermediate field
  let KD : IntermediateField ↥F K :=
    { carrier := {z : K | D z = 0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb
        change D (a * b) = 0
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, ha, hb, mul_zero, mul_zero, add_zero]
      one_mem' := Derivation.map_one_eq_zero D
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb
        change D (a + b) = 0
        rw [Derivation.map_add, ha, hb, add_zero]
      zero_mem' := Derivation.map_zero D
      algebraMap_mem' := by
        intro cc
        exact hkillF cc
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha
        change D a⁻¹ = 0
        rw [Derivation.leibniz_inv, ha, smul_zero] }
  have hprod : Module.finrank ↥F ↥KD * Module.finrank ↥KD K = 5 := by
    rw [Module.finrank_mul_finrank, hfinK]
  have hKDne : Module.finrank ↥KD K ≠ 1 := by
    intro h1
    have h2 : Module.finrank ↥KD ↥(⊤ : IntermediateField ↥KD K) = 1 := by
      rw [IntermediateField.finrank_top', h1]
    have h3 : (⊤ : IntermediateField ↥KD K) = ⊥ := IntermediateField.finrank_eq_one_iff.mp h2
    have hxmem : x ∈ (⊥ : IntermediateField ↥KD K) := by rw [← h3]; trivial
    rw [IntermediateField.mem_bot] at hxmem
    obtain ⟨c', hc'⟩ := hxmem
    exact hx (by rw [← hc']; exact c'.2)
  have hb_dvd : Module.finrank ↥KD K ∣ 5 :=
    ⟨Module.finrank ↥F ↥KD, by rw [mul_comm]; exact hprod.symm⟩
  have hb : Module.finrank ↥KD K = 5 := by
    rcases (show Nat.Prime 5 by norm_num).eq_one_or_self_of_dvd (Module.finrank ↥KD K)
      hb_dvd with h | h
    · exact absurd h hKDne
    · exact h
  have ha : Module.finrank ↥F ↥KD = 1 := by
    have := hprod
    rw [hb] at this
    omega
  have hKDbot : KD = ⊥ := IntermediateField.finrank_eq_one_iff.mp ha
  intro h hh
  have hmem : h ∈ KD := hh
  rw [hKDbot, IntermediateField.mem_bot] at hmem
  obtain ⟨c', hc'⟩ := hmem
  have hcF : h ∈ F := by
    rw [← hc']
    exact c'.2
  obtain ⟨s, hs⟩ := (hF h).mp hcF
  exact ⟨s, hs.symm⟩

/-! ## `Func E` is generated by the coordinates over `N` -/

/-- The function field of a Weierstrass curve is generated, as a field over `N`, by the two
coordinates `genX E` and `genY E`.  (Universe-polymorphic version of `Work.MotV5.adjoin_genX_genY`
in `MotV5/adjoin_genX_genY.lean`.) -/
theorem adjoin_genX_genY_eq_top {L : Type*} [Field L] (E : WeierstrassCurve L) :
    IntermediateField.adjoin L
      ({Work.MotC2.genX E, Work.MotC2.genY E} : Set (Work.MotC2.Func E)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [IntermediateField.mem_adjoin_iff_div]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Work.MotC2.Coord E) f
  have key : ∀ a : Work.MotC2.Coord E,
      algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) a ∈
        Algebra.adjoin L ({Work.MotC2.genX E, Work.MotC2.genY E} :
          Set (Work.MotC2.Func E)) := by
    intro a
    have h1 : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) a ∈ Work.MotC2.affRing E :=
      Algebra.subset_adjoin ⟨a, rfl⟩
    rwa [Work.MotC2.affRing_eq_adjoin L E] at h1
  exact ⟨algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) a, key a,
    algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) b, key b, hab.symm⟩

/-! ## The function field is generated over the fifth powers by `genX` -/

/-- **`Func E` is generated over the subfield of fifth powers by the coordinate `genX E`.**
Indeed `genX E` and `genY E` generate `Func E` over `N ⊆ fifthPowers E`, and
`genY E ∈ (fifthPowers E)⟮genX E⟯`. -/
theorem fifthPowers_adjoin_genX_eq_top {N : Type*} [Field N] [IsAlgClosed N] [CharP N 5]
    (E : WeierstrassCurve N) : (fifthPowers E)⟮Work.MotC2.genX E⟯ = ⊤ := by
  have hle : IntermediateField.adjoin N
        ({Work.MotC2.genX E, Work.MotC2.genY E} : Set (Work.MotC2.Func E)) ≤
      ((fifthPowers E)⟮Work.MotC2.genX E⟯).restrictScalars N := by
    rw [IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self (↥(fifthPowers E)) (Work.MotC2.genX E)
    · exact genY_mem_fifthPowers_adjoin_genX E
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ IntermediateField.adjoin N
      ({Work.MotC2.genX E, Work.MotC2.genY E} : Set (Work.MotC2.Func E)) := by
    rw [adjoin_genX_genY_eq_top E]; trivial
  exact hle hz

/-! ## The target lemma -/

theorem ker_deriv_fifthpowers {N : Type*} [Field N] [IsAlgClosed N] [CharP N 5]
    (E : WeierstrassCurve N)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hx : D (Work.MotC2.genX E) ≠ 0) (h : Work.MotC2.Func E) (hh : D h = 0) :
    ∃ s : Work.MotC2.Func E, h = s ^ 5 :=
  ker_deriv_eq_fifthpowers_of_generator (fifthPowers E) D
    (fun c => deriv_fifthPowers_eq_zero E D c)
    (fun _ => mem_fifthPowers E) (Work.MotC2.genX E) hx
    (fifthPowers_adjoin_genX_eq_top E) h hh

end Work.MotV5
