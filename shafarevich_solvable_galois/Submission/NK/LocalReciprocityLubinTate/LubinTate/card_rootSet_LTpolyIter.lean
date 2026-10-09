import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Division
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree
import Submission.NK.LocalReciprocityLubinTate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The roots of the iterates `f^{(n)}` of the standard Lubin–Tate polynomial

For the standard Lubin–Tate polynomial `f(T) = πT + T^q` over a nonarchimedean local field `F`
of characteristic zero, the `n`-fold iterate `f^{(n)} = LTpolyIter (π : F) q n` is a monic
polynomial of degree `q^n` (`LTpolyIter_monic_degree`), and its roots in the algebraic closure of
`F` are exactly the `π^n`-division points `Λ_n` of the associated Lubin–Tate group (Milne, *CFT*,
§I.3).  In particular there are exactly `q^n` of them:

`card_rootSet_LTpolyIter : #{x ∈ F̄ | f^{(n)}(x) = 0} = q^n`.

The mathematical content is that `f^{(n)}` is *separable*, i.e. has no repeated roots.  This is
proved here by a purely polynomial induction using the factorisation

`f^{(n+1)} = f ∘ f^{(n)} = f^{(n)} · ((f^{(n)})^{q-1} + π)`,

in which the second factor `(f^{(n)})^{q-1} + π` is Eisenstein at `π`, hence irreducible over `F`
(and therefore separable, `F` having characteristic zero), while the two factors are coprime
because their difference is the nonzero constant `π`.

## Main results

* `separable_LTpolyIter` — the iterate `f^{(n)}` is separable;
* `card_rootSet_LTpolyIter` — the number of roots of `f^{(n)}` in the algebraic closure is `q^n`.
-/

open Polynomial

set_option maxHeartbeats 1000000

namespace NK.LocalReciprocityLubinTate

universe u

/-! ### The iterate in the other composition order -/

/-- The iterate of a polynomial can also be written with the composition on the left:
`f^{(n+1)} = f ∘ f^{(n)}`.  (`polyIter` is defined with `f^{(n+1)} = f^{(n)} ∘ f`; the two
agree because composition of a fixed polynomial with itself is associative.) -/
theorem polyIter_succ' {A : Type u} [CommRing A] (f : Polynomial A) (n : ℕ) :
    polyIter f (n + 1) = f.comp (polyIter f n) := by
  induction n with
  | zero => rw [polyIter_succ, polyIter_zero, X_comp, comp_X]
  | succ n ih =>
    have h1 : polyIter f (n + 1 + 1) = (polyIter f (n + 1)).comp f := polyIter_succ f (n + 1)
    rw [h1, ih, comp_assoc, ← polyIter_succ, ih]

/-- The iterate `f^{(n+1)}` of the Lubin–Tate polynomial as `f` composed with `f^{(n)}`. -/
theorem LTpolyIter_succ'' {A : Type u} [CommRing A] (π : A) (q n : ℕ) :
    LTpolyIter π q (n + 1) = (LTpoly π q).comp (LTpolyIter π q n) :=
  polyIter_succ' (LTpoly π q) n

/-! ### Compatibility with ring homomorphisms and reduction mod `π` -/

/-- The standard Lubin–Tate polynomial is compatible with ring homomorphisms. -/
theorem LTpoly_map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (π : A) (q : ℕ) :
    (LTpoly π q).map φ = LTpoly (φ π) q := by
  simp [LTpoly]

/-- The iterates of the Lubin–Tate polynomial are compatible with ring homomorphisms. -/
theorem LTpolyIter_map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (π : A)
    (q n : ℕ) : (LTpolyIter π q n).map φ = LTpolyIter (φ π) q n := by
  induction n with
  | zero => rw [LTpolyIter_zero, map_X, LTpolyIter_zero]
  | succ n ih => rw [LTpolyIter_succ, map_comp, ih, LTpoly_map, LTpolyIter_succ]

/-- Reduction modulo `π`: since `f(X) ≡ X^q (mod π)`, the `n`-th iterate satisfies
`f^{(n)}(X) ≡ X^{q^n} (mod π)`.  Equivalently, every non-leading coefficient of `f^{(n)}` is
divisible by `π`. -/
theorem LTpolyIter_map_quotient {R : Type u} [CommRing R] (π : R) (q n : ℕ) (_hq : 2 ≤ q) :
    (LTpolyIter π q n).map (Ideal.Quotient.mk (Ideal.span ({π} : Set R))) = X ^ (q ^ n) := by
  induction n with
  | zero => rw [LTpolyIter_zero, map_X, pow_zero, pow_one]
  | succ n ih =>
    rw [LTpolyIter_succ'', map_comp, ih, LTpoly_map]
    have hπ0 : Ideal.Quotient.mk (Ideal.span ({π} : Set R)) π = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
    have hlt : LTpoly (Ideal.Quotient.mk (Ideal.span ({π} : Set R)) π) q = X ^ q := by
      simp [LTpoly, hπ0]
    rw [hlt, pow_comp, X_comp, ← pow_mul, ← pow_succ]

/-! ### The Eisenstein factor `(f^{(n)})^{q-1} + π` is irreducible -/

/-- **The factor `(f^{(n)})^{q-1} + π` is Eisenstein at `π`, hence irreducible.**  Over a discrete
valuation ring `R` with fraction field `K`, for an irreducible `π ∈ R` and `q ≥ 2`, the polynomial
`(LTpolyIter π q n)^{q-1} + π` is Eisenstein at the maximal ideal `(π)` (it is monic, all its
lower coefficients are divisible by `π` by `LTpolyIter_map_quotient`, and its constant term is
exactly `π`, which is not divisible by `π^2`); Gauss's lemma then descends irreducibility from
`R[X]` to `K[X]`. -/
theorem irreducible_LTpolyIter_shift {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsIntegrallyClosed R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    Irreducible (((LTpolyIter π q n) ^ (q - 1) + C π).map (algebraMap R K)) := by
  set G : Polynomial R := LTpolyIter π q n with hGdef
  obtain ⟨hGmonic, hGnat, -, hGc0⟩ :=
    NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree π q n hq
  rw [← hGdef] at hGmonic hGnat hGc0
  have hdegpos : 0 < (q - 1) * q ^ n := Nat.mul_pos (by omega) (pow_pos (by omega) n)
  have hpowmonic : (G ^ (q - 1)).Monic := hGmonic.pow _
  have hGpow_deg : (G ^ (q - 1)).natDegree = (q - 1) * q ^ n := by
    rw [natDegree_pow, hGnat]
  have hlt : (C π).degree < (G ^ (q - 1)).degree := by
    rw [degree_C hπ.ne_zero, degree_eq_natDegree hpowmonic.ne_zero, hGpow_deg]
    exact_mod_cast hdegpos
  have hHmonic : (G ^ (q - 1) + C π).Monic := hpowmonic.add_of_left hlt
  have hHnat : (G ^ (q - 1) + C π).natDegree = (q - 1) * q ^ n := by
    rw [natDegree_add_eq_left_of_degree_lt hlt, hGpow_deg]
  have hHdegpos : 0 < (G ^ (q - 1) + C π).natDegree := by rw [hHnat]; exact hdegpos
  have hHmap : (G ^ (q - 1) + C π).map (Ideal.Quotient.mk (Ideal.span ({π} : Set R)))
      = X ^ ((q - 1) * q ^ n) := by
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C,
      LTpolyIter_map_quotient π q n hq]
    have hπ0 : Ideal.Quotient.mk (Ideal.span ({π} : Set R)) π = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
    rw [hπ0, Polynomial.C_0, add_zero, ← pow_mul, mul_comm]
  have hmem : ∀ {m : ℕ}, m < (G ^ (q - 1) + C π).natDegree →
      (G ^ (q - 1) + C π).coeff m ∈ Ideal.span ({π} : Set R) := by
    intro m hm
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, hHmap]
    rw [coeff_X_pow, if_neg]
    rw [hHnat] at hm
    omega
  have hc0 : (G ^ (q - 1) + C π).coeff 0 = π := by
    rw [coeff_add, coeff_C_zero]
    have hgz : (G ^ (q - 1)).coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, hGc0,
        zero_pow (by omega)]
    rw [hgz, zero_add]
  have hnotmem2 : (G ^ (q - 1) + C π).coeff 0 ∉ (Ideal.span ({π} : Set R)) ^ 2 := by
    rw [hc0]
    intro hcon
    rw [pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] at hcon
    obtain ⟨a, ha⟩ := hcon
    have h2 : π * a = 1 := by
      refine mul_left_cancel₀ hπ.ne_zero ?_
      calc π * (π * a) = (π * π) * a := by ring
        _ = π := ha.symm
        _ = π * 1 := by ring
    exact hπ.not_isUnit (IsUnit.of_mul_eq_one a h2)
  have hspan_ne_top : Ideal.span ({π} : Set R) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hπ.not_isUnit
  have hEis : (G ^ (q - 1) + C π).IsEisensteinAt (Ideal.span ({π} : Set R)) :=
    hHmonic.isEisensteinAt_of_mem_of_notMem hspan_ne_top hmem hnotmem2
  have hprime : (Ideal.span ({π} : Set R) : Ideal R).IsPrime := by
    rw [← hπ.maximalIdeal_eq]
    exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  have hirr : Irreducible (G ^ (q - 1) + C π) :=
    hEis.irreducible hprime hHmonic.isPrimitive hHdegpos
  exact (hHmonic.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hirr

/-! ### The factorisation `f^{(n+1)} = f^{(n)} · ((f^{(n)})^{q-1} + π)` -/

/-- Composing the Lubin–Tate polynomial with a polynomial `p` factors it as
`f(p) = p · (p^{q-1} + π)`, because `f(T) = πT + T^q = T(T^{q-1} + π)`. -/
theorem LTpoly_comp_eq {A : Type u} [CommRing A] (π : A) (q : ℕ) (hq : 1 ≤ q)
    (p : Polynomial A) :
    (LTpoly π q).comp p = p * (p ^ (q - 1) + C π) := by
  rw [LTpoly, add_comp, C_mul_comp, X_comp, pow_comp, X_comp]
  have hp : p ^ q = p * p ^ (q - 1) := by
    conv_lhs => rw [show q = (q - 1) + 1 by omega]
    rw [pow_succ']
  rw [hp]
  ring

/-- `p` and `p^m + c` are coprime for `c ≠ 0` and `m > 0`: their difference is the nonzero
constant `c`, so Bézout is witnessed by `-(c⁻¹)p^{m-1}` and `c⁻¹`. -/
theorem isCoprime_self_pow_add_C {F : Type u} [Field F] (p : Polynomial F) {c : F} (hc : c ≠ 0)
    (m : ℕ) (hm : 0 < m) : IsCoprime p (p ^ m + C c) := by
  refine ⟨-(C c⁻¹) * p ^ (m - 1), C c⁻¹, ?_⟩
  have hCc : C c⁻¹ * C c = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have hp : p ^ m = p * p ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ']
  rw [hp]
  linear_combination hCc

/-- **The iterate `f^{(n)}` is separable.**  Induction on `n`: `f^{(n+1)}` is the product of the
separable `f^{(n)}` with the Eisenstein (hence irreducible, hence separable, `F` of characteristic
zero) factor `(f^{(n)})^{q-1} + π`, and the two factors are coprime. -/
theorem separable_LTpolyIter (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    (LTpolyIter (π : F) q n).Separable := by
  have hπF : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.coe_injective (by simpa using h))
  induction n with
  | zero => rw [LTpolyIter_zero]; exact separable_X
  | succ n ih =>
    rw [LTpolyIter_succ'', LTpoly_comp_eq (π : F) q (by omega)]
    have hh : ((LTpolyIter (π : F) q n) ^ (q - 1) + C (π : F)).Separable := by
      refine Irreducible.separable ?_
      have h := irreducible_LTpolyIter_shift (R := ↥(ValuativeRel.valuation F).integer) (K := F)
        π hπ q n hq
      rwa [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C, LTpolyIter_map] at h
    exact Separable.mul ih hh (isCoprime_self_pow_add_C _ hπF (q - 1) (by omega))

end NK.LocalReciprocityLubinTate

namespace NK.LocalReciprocityLubinTate.LubinTate

open Polynomial

universe u

/-- **The number of roots of the `n`-th iterate of the standard Lubin–Tate polynomial is `q^n`**
(Milne, *CFT*, §I.3: the roots of `f^{(n)}` are the `π^n`-division points of the Lubin–Tate
group, of which there are `q^n`).

`f^{(n)}` is monic of degree `q^n` and separable, so over the algebraic closure it splits into
`q^n` distinct linear factors. -/
theorem card_rootSet_LTpolyIter (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q) :
    {x : AlgebraicClosure F | ((NK.LocalReciprocityLubinTate.LTpolyIter (π : F) q n).map
        (algebraMap F (AlgebraicClosure F))).IsRoot x}.ncard = q ^ n := by
  classical
  set p : Polynomial F := LTpolyIter (π : F) q n with hp
  obtain ⟨hmonic', hnat', -, -⟩ :=
    NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree (π : F) q n hq
  rw [← hp] at hmonic' hnat'
  have hmonic : p.Monic := hmonic'
  have hnat : p.natDegree = q ^ n := hnat'
  have hsep : p.Separable := by rw [hp]; exact separable_LTpolyIter F π hπ q n hq
  have hnzK : p.map (algebraMap F (AlgebraicClosure F)) ≠ 0 :=
    (hmonic.map (algebraMap F (AlgebraicClosure F))).ne_zero
  have hsepK : (p.map (algebraMap F (AlgebraicClosure F))).Separable := hsep.map
  have hsplit : (p.map (algebraMap F (AlgebraicClosure F))).Splits := IsAlgClosed.splits _
  have hnodup : (p.map (algebraMap F (AlgebraicClosure F))).roots.Nodup :=
    Polynomial.nodup_roots hsepK
  have hcard : ((p.map (algebraMap F (AlgebraicClosure F))).roots.toFinset).card = q ^ n := by
    rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots,
      hmonic.natDegree_map, hnat]
  have hset : {x : AlgebraicClosure F | (p.map (algebraMap F (AlgebraicClosure F))).IsRoot x}
      = ↑((p.map (algebraMap F (AlgebraicClosure F))).roots.toFinset) := by
    ext x
    rw [Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hnzK]
  rw [hset, Set.ncard_coe_finset, hcard]

end NK.LocalReciprocityLubinTate.LubinTate
