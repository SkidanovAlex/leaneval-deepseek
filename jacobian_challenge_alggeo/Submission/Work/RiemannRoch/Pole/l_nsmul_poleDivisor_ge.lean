/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The lower bound `card ι * (m + 1 - r) ≤ l (m · (x)_∞)`

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k`, let `x ∈ K(C)` be
transcendental over `k`, and let `b` be a `k(x)`-basis of `K(C)` all of whose elements lie in the
Riemann–Roch space `L(r · (x)_∞)` of a multiple of the pole divisor of `x`.  Then, for every
`m ≥ r`, the `card ι * (m + 1 - r)` elements `x^j · b i` (`0 ≤ j ≤ m - r`) lie in
`L(m · (x)_∞)` and are `k`-linearly independent, whence the stated lower bound on
`l(m · (x)_∞) = dim_k L(m · (x)_∞)`.

The linear independence is the substantive point: a `k`-linear relation
`Σ_{j,i} c_{ji} x^j b_i = 0` groups as `Σ_i (Σ_j c_{ji} x^j) b_i = 0`, so by the `k(x)`-linear
independence of `b` each `p_i(x) = Σ_j c_{ji} x^j` vanishes; as `x` is transcendental, each
polynomial `p_i` vanishes and hence so does each `c_{ji}`.
-/
import Mathlib
import Submission.Work.RiemannRoch.Pole
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch.Pole

open Work.CurveBasics

noncomputable section

/-! ## Linear independence of the family `x ^ j * b i`

Let `k ⊆ K ⊆ L` be fields, `x ∈ K` transcendental over `k` (tested through the injectivity of
`Polynomial.aeval x`), and `b` a `K`-basis of `L`.  Then the products `x^j * b i` with `j < n`
are `k`-linearly independent. -/
lemma linearIndependent_pow_mul_basis {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (x : K) (hx : Function.Injective (Polynomial.aeval x : Polynomial k → K))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K L) (n : ℕ) :
    LinearIndependent k (fun p : Fin n × ι => (algebraMap K L x) ^ (p.1 : ℕ) * (b p.2 : L)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  obtain ⟨j, i⟩ := p
  -- rewrite the relation in the form `Σ_i (Σ_j c_{ji} x^j) • b_i = 0`, with coefficients in `K`
  have hE : (∑ i' : ι, (∑ j' : Fin n, c (j', i') • x ^ (j' : ℕ)) • b i')
      = ∑ p : Fin n × ι, c p • ((algebraMap K L x) ^ (p.1 : ℕ) * (b p.2 : L)) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    congr 1 with i'
    rw [Finset.sum_smul]
    congr 1 with j'
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply k K L, Algebra.smul_def]
    ring
  have hsum : (∑ i' : ι, (∑ j' : Fin n, c (j', i') • x ^ (j' : ℕ)) • b i') = 0 := by
    rw [hE, hc]
  -- the coefficients of the basis `b` vanish
  have hgi := (Fintype.linearIndependent_iff.mp b.linearIndependent)
    (fun i' => ∑ j' : Fin n, c (j', i') • x ^ (j' : ℕ)) hsum
  -- each `Σ_j c_{ji} x^j` is the value at `x` of a polynomial with coefficients `c_{ji}`
  have hP : Polynomial.aeval x
      (∑ j' : Fin n, Polynomial.C (c (j', i)) * Polynomial.X ^ (j' : ℕ)) = 0 := by
    rw [← hgi i]
    simp only [map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.smul_def]
  have hP0 : (∑ j' : Fin n, Polynomial.C (c (j', i)) * Polynomial.X ^ (j' : ℕ)) = 0 :=
    hx (by rw [hP, map_zero])
  -- read off the coefficient of `X ^ j`
  have hcoeff := congrArg (fun P : Polynomial k => P.coeff (j : ℕ)) hP0
  simp only [Polynomial.coeff_zero, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    at hcoeff
  rw [Finset.sum_eq_single j] at hcoeff
  · simpa using hcoeff
  · intro b' _ hb'
    rw [if_neg]
    intro h
    exact hb' (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ j) h

/-! ## Products of elements of Riemann–Roch spaces -/

/-- The product of an element of `L D` and an element of `L E` lies in `L (D + E)`. -/
theorem mul_mem_L {k : Type*} [Field k] (C : Curve k) {D E : C.Div} {f g : C.functionField}
    (hf : f ∈ C.L D) (hg : g ∈ C.L E) : f * g ∈ C.L (D + E) := by
  rw [Curve.mem_L_iff] at hf hg ⊢
  by_cases hf0 : f = 0
  · subst hf0
    simpa using Curve.zero_mem_L C (D + E)
  by_cases hg0 : g = 0
  · subst hg0
    simp
  rcases hf with hf | hf
  · exact absurd hf hf0
  rcases hg with hg | hg
  · exact absurd hg hg0
  refine Or.inr fun Q => ?_
  have hfQ : 0 ≤ (C.div f + D) Q := hf Q
  have hgQ : 0 ≤ (C.div g + E) Q := hg Q
  have hfg : f * g ≠ 0 := mul_ne_zero hf0 hg0
  simp only [Finsupp.add_apply, Curve.div_apply] at hfQ hgQ ⊢
  rw [Scheme.ord_mul hf0 hg0]
  linarith

/-- The function `x` lies in the Riemann–Roch space of its own pole divisor. -/
theorem self_mem_L_poleDivisor {k : Type*} [Field k] (C : Curve k) (x : C.functionField) :
    x ∈ C.L (1 • Curve.poleDivisor C x) := by
  rw [one_smul, Curve.mem_L_iff]
  exact Or.inr (Curve.div_add_poleDivisor_isEffective C x)

/-- Powers of `x` lie in the Riemann–Roch spaces of the multiples of its pole divisor. -/
theorem pow_mem_L_poleDivisor {k : Type*} [Field k] (C : Curve k) (x : C.functionField)
    (j : ℕ) : x ^ j ∈ C.L (j • Curve.poleDivisor C x) := by
  induction j with
  | zero =>
    rw [pow_zero, zero_smul]
    -- `1 ∈ C.L 0`, proved directly from `div 1 = 0` (avoids relying on the normal form of
    -- `algebraMap` at `1`).
    have hdiv : C.div (1 : C.functionField) = 0 := by
      have h := C.div_mul (one_ne_zero : (1 : C.functionField) ≠ 0)
        (one_ne_zero : (1 : C.functionField) ≠ 0)
      rw [mul_one] at h
      have h' : C.div (1 : C.functionField) + 0 = C.div (1 : C.functionField) + C.div 1 := by
        rw [add_zero]; exact h
      exact (add_left_cancel h').symm
    rw [Curve.mem_L_iff]
    exact Or.inr (by rw [hdiv]; simpa using Curve.Div.isEffective_zero (C := C))
  | succ j ih =>
    have h := mul_mem_L C ih (self_mem_L_poleDivisor C x)
    simpa [pow_succ, add_smul, one_smul] using h

/-! ## The lower bound -/

theorem l_nsmul_poleDivisor_ge {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (x : C.functionField) (hx : Transcendental k x) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField)
    (r : ℕ) (hr : ∀ i, (b i : C.functionField) ∈ C.L (r • Work.RiemannRoch.Curve.poleDivisor C x))
    (m : ℕ) (hm : r ≤ m) :
    Fintype.card ι * (m + 1 - r) ≤ C.l (m • Work.RiemannRoch.Curve.poleDivisor C x) := by
  classical
  set D : C.Div := Work.RiemannRoch.Curve.poleDivisor C x with hD
  have hDeff : D.IsEffective := by
    rw [hD]
    exact Work.RiemannRoch.Curve.isEffective_poleDivisor C x
  haveI hfin : FiniteDimensional k ↥(C.L (m • D)) :=
    Work.CurveBasics.Linear.finiteDimensional_L C (m • D)
  -- `x` as an element of `k(x)`
  let xK : IntermediateField.adjoin k ({x} : Set C.functionField) :=
    ⟨x, IntermediateField.subset_adjoin k {x} (Set.mem_singleton x)⟩
  have hxK : Function.Injective (Polynomial.aeval xK :
      Polynomial k → IntermediateField.adjoin k ({x} : Set C.functionField)) := by
    intro P Q hPQ
    have h := congrArg (algebraMap (IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField) hPQ
    rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_algebraMap_apply] at h
    have hcast : algebraMap (IntermediateField.adjoin k ({x} : Set C.functionField))
        C.functionField xK = x := rfl
    rw [hcast] at h
    exact (transcendental_iff_injective.mp hx) h
  -- linear independence of the family `x^j * b i`
  have hli : LinearIndependent k (fun p : Fin (m + 1 - r) × ι =>
      x ^ (p.1 : ℕ) * (b p.2 : C.functionField)) := by
    have h := linearIndependent_pow_mul_basis (k := k)
      (K := IntermediateField.adjoin k ({x} : Set C.functionField)) xK hxK b (m + 1 - r)
    simpa [xK, IntermediateField.algebraMap_apply] using h
  -- each of them lies in `L (m · D)`
  have hmem : ∀ p : Fin (m + 1 - r) × ι,
      x ^ (p.1 : ℕ) * (b p.2 : C.functionField) ∈ C.L (m • D) := by
    intro p
    have h1 : x ^ (p.1 : ℕ) ∈ C.L ((p.1 : ℕ) • D) := by
      simpa [← hD] using pow_mem_L_poleDivisor C x (p.1 : ℕ)
    have h2 : (b p.2 : C.functionField) ∈ C.L (r • D) := hr p.2
    have h3 : x ^ (p.1 : ℕ) * (b p.2 : C.functionField) ∈ C.L ((p.1 : ℕ) • D + r • D) :=
      mul_mem_L C h1 h2
    refine (C.L_mono ?_) h3
    rw [Curve.Div.le_iff]
    intro Q
    rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.smul_apply,
      nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    have hle : ((p.1 : ℕ) + r : ℕ) ≤ m := by
      have := p.1.isLt
      omega
    have hcast : (((p.1 : ℕ) : ℤ) + (r : ℤ)) ≤ (m : ℤ) := by exact_mod_cast hle
    nlinarith [hDeff Q]
  -- conclude with the dimension count
  have hspan : Submodule.span k (Set.range (fun p : Fin (m + 1 - r) × ι =>
      x ^ (p.1 : ℕ) * (b p.2 : C.functionField))) ≤ C.L (m • D) := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hmono := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_prod, Fintype.card_fin] at hmono
  have hfin' : Fintype.card ι * (m + 1 - r) ≤ Module.finrank k ↥(C.L (m • D)) := by
    calc Fintype.card ι * (m + 1 - r) = (m + 1 - r) * Fintype.card ι := Nat.mul_comm _ _
      _ ≤ Module.finrank k ↥(C.L (m • D)) := hmono
  exact hfin'

end

end Work.RiemannRoch.Pole
