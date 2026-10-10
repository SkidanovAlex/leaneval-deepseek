/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# The kernel of a derivation of a field of characteristic `p` consists of `p`-th powers

If `K` is a field of characteristic `p` (a prime) and `D` is a derivation of `K` with `D γ ≠ 0`,
and if `K` is generated over the subfield `K^p = PthPow K p` of `p`-th powers by the single element
`γ`, then every element killed by `D` is a `p`-th power.

The mathematical content is the following.  Let `F = K^p` and let `m` be the degree of `γ` over
`F`.  Since `γ^p ∈ F` and `γ ∉ F` (a derivation kills `p`-th powers), `m ∈ {1, p}`, and `m ≠ 1`,
so `m = p`.  Hence `[K : F] = p`, and the field `ker D` of constants satisfies
`F ≤ ker D ≤ K` with `[K : ker D] ≠ 1` (as `D γ ≠ 0`), so both degrees are `p` and `ker D = F`.

* `ker_le_of_generator` — the general mechanism, for an abstract base field `F` which is exactly
  the set of `p`-th powers: if `D` kills `F`, `D x ≠ 0` and `K = F(x)`, then `ker D ⊆ F`.
* `ker_deriv_eq_pthPow` — the target, obtained by applying the mechanism with `F = PthPow K p`.

## Tags

derivation, kernel, p-th powers, purely inseparable extension
-/

import Mathlib
import Submission.Work.MotV.PthPowDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial
open scoped IntermediateField

namespace Work.MotV

/-! ## The general mechanism -/

/-- **The kernel of a derivation consists of `p`-th powers**, when the whole field `K` is generated
by a single element `x` over the field `F` of `p`-th powers.

Hypotheses: `K` has characteristic `p`; `F ≤ K` is a field of characteristic `p` which is exactly
the set of `p`-th powers of elements of `K`; the derivation `D` of `K` kills the image of `F`;
`x ∈ K` with `D x ≠ 0`; and `K = F(x)`.

Conclusion: every `h` with `D h = 0` is a `p`-th power. -/
theorem ker_le_of_generator {R F K : Type*} [CommSemiring R] [Field F] [Field K]
    [Algebra R K] [Algebra F K] {p : ℕ} [Fact p.Prime] [CharP K p] [CharP F p]
    (D : Derivation R K K) (hkillF : ∀ c : F, D (algebraMap F K c) = 0)
    (hF : ∀ z : K, z ∈ (algebraMap F K).range ↔ ∃ s : K, s ^ p = z)
    (x : K) (hx : D x ≠ 0) (hgen : F⟮x⟯ = ⊤) :
    ∀ h : K, D h = 0 → ∃ s : K, s ^ p = h := by
  -- `K` is purely inseparable over `F` (every element is a `p`-th power of an element of `K`)
  have hpi : IsPurelyInseparable F K := by
    rw [isPurelyInseparable_iff_pow_mem F p]
    intro z
    exact ⟨1, by rw [pow_one]; exact (hF (z ^ p)).mpr ⟨z, rfl⟩⟩
  -- `x` is integral over `F`, and `x ∉ F`
  have hx5mem : x ^ p ∈ (algebraMap F K).range := (hF (x ^ p)).mpr ⟨x, rfl⟩
  obtain ⟨a, ha⟩ := hx5mem
  have hxint : IsIntegral F x := by
    refine IsIntegral.of_pow (n := p) (Fact.out : p.Prime).pos ?_
    rw [← ha]
    exact isIntegral_algebraMap
  -- the minimal polynomial of `x` over `F` is `X ^ (p ^ n) - C c`
  obtain ⟨n, c, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p x
  have hdeg : (minpoly F x).natDegree = p ^ n := by
    rw [hmin, Polynomial.natDegree_X_pow_sub_C]
  have hdiv : minpoly F x ∣ Polynomial.X ^ p - Polynomial.C a := by
    refine minpoly.dvd F x ?_
    rw [map_sub, map_pow, aeval_X, aeval_C, ha, sub_self]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq : (Polynomial.X ^ p - Polynomial.C a) ≠ 0 := by
    intro h0
    have hnd : (Polynomial.X ^ p - Polynomial.C a).natDegree = p :=
      Polynomial.natDegree_X_pow_sub_C
    rw [h0, Polynomial.natDegree_zero] at hnd
    omega
  have hle : p ^ n ≤ p := by
    have hd := Polynomial.natDegree_le_of_dvd hdiv hq
    rw [Polynomial.natDegree_X_pow_sub_C] at hd
    simpa [hdeg] using hd
  have hnle : n ≤ 1 := by
    by_contra hn
    have hn2 : 2 ≤ n := by omega
    have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp0 hn2
    have hpp : p * p ≤ p ^ n := by simpa [pow_two] using h2
    have h1 : p ≤ 1 := Nat.le_of_mul_le_mul_left
      (show p * p ≤ p * 1 by simpa using hpp.trans hle) hp0
    omega
  have hn0 : n ≠ 0 := by
    intro hn0
    have h1 : (minpoly F x).natDegree = 1 := by rw [hdeg, hn0]; norm_num
    obtain ⟨c', hc'⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact hx (by rw [← hc']; exact hkillF c')
  have hn : n = 1 := by omega
  have hdegp : (minpoly F x).natDegree = p := by rw [hdeg, hn, pow_one]
  have hfin : Module.finrank F ↥(F⟮x⟯) = p := by
    rw [IntermediateField.adjoin.finrank hxint, hdegp]
  have hfinK : Module.finrank F K = p := by
    rw [← IntermediateField.finrank_top', ← hgen]
    exact hfin
  -- the field of constants of `D`, as an intermediate field
  let KD : IntermediateField F K :=
    { carrier := {z : K | D z = 0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb
        change D (a * b) = 0
        rw [Derivation.leibniz, ha, hb, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, add_zero]
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
        by_cases ha0 : a = 0
        · subst ha0
          simp
        · have h := Derivation.leibniz D a a⁻¹
          rw [mul_inv_cancel₀ ha0, Derivation.map_one_eq_zero, ha] at h
          simp only [smul_zero, add_zero] at h
          rw [smul_eq_mul] at h
          rcases mul_eq_zero.mp h.symm with h1 | h1
          · exact absurd h1 ha0
          · exact h1 }
  have hprod : Module.finrank F ↥KD * Module.finrank ↥KD K = p := by
    rw [Module.finrank_mul_finrank, hfinK]
  -- `x ∉ KD ⊆ K`, so `[K : KD] ≠ 1`
  have hKDne : Module.finrank ↥KD K ≠ 1 := by
    intro h1
    have h2 : Module.finrank ↥KD ↥(⊤ : IntermediateField ↥KD K) = 1 := by
      rw [IntermediateField.finrank_top', h1]
    have h3 : (⊤ : IntermediateField ↥KD K) = ⊥ := IntermediateField.finrank_eq_one_iff.mp h2
    have hxmem : x ∈ (⊥ : IntermediateField ↥KD K) := by rw [← h3]; trivial
    rw [IntermediateField.mem_bot] at hxmem
    obtain ⟨c', hc'⟩ := hxmem
    exact hx (by rw [← hc']; exact c'.2)
  have hb_dvd : Module.finrank ↥KD K ∣ p :=
    ⟨Module.finrank F ↥KD, by rw [mul_comm]; exact hprod.symm⟩
  have hb : Module.finrank ↥KD K = p := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (Module.finrank ↥KD K) hb_dvd with h | h
    · exact absurd h hKDne
    · exact h
  have ha1 : Module.finrank F ↥KD = 1 := by
    have h := hprod
    rw [hb] at h
    refine Nat.eq_of_mul_eq_mul_right hp0 ?_
    rw [h, one_mul]
  have hKDbot : KD = ⊥ := IntermediateField.finrank_eq_one_iff.mp ha1
  intro h hh
  have hmem : h ∈ KD := hh
  rw [hKDbot, IntermediateField.mem_bot] at hmem
  obtain ⟨c', hc'⟩ := hmem
  exact (hF h).mp (Set.mem_range.mpr ⟨c', hc'⟩)

/-! ## The target -/

theorem ker_deriv_eq_pthPow {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]
    {p : ℕ} [Fact p.Prime] [CharP K p] (γ : K) (D : Derivation R K K) (hDγ : D γ ≠ 0)
    (hgen : Algebra.adjoin (Work.MotV.PthPow K p) {γ} = ⊤) :
    ∀ f : K, D f = 0 → ∃ s : K, s ^ p = f := by
  -- the `Subalgebra`-generation hypothesis upgrades to `IntermediateField`-generation
  have hgen' : IntermediateField.adjoin ↥(Work.MotV.PthPow K p) {γ} = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [IntermediateField.mem_adjoin_iff_div]
    exact ⟨z, by rw [hgen]; trivial, 1,
      (Algebra.adjoin ↥(Work.MotV.PthPow K p) {γ}).one_mem, by simp⟩
  refine ker_le_of_generator (F := ↥(Work.MotV.PthPow K p)) (p := p) D ?_ ?_ γ hDγ hgen'
  · intro c
    exact Work.MotV.deriv_eq_zero_of_mem_PthPow D c.2
  · intro z
    constructor
    · intro hz
      obtain ⟨c, hc⟩ := Set.mem_range.mp hz
      rw [← hc]
      exact Work.MotV.mem_PthPow.mp c.2
    · rintro ⟨s, rfl⟩
      exact Set.mem_range.mpr ⟨⟨s ^ p, Work.MotV.mem_PthPow.mpr ⟨s, rfl⟩⟩, rfl⟩

end Work.MotV
