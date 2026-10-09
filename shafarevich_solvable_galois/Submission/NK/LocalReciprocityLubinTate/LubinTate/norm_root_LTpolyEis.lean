import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.DivisionPoints
import Submission.NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm of a root of the Eisenstein factor `f^{[n]}`

Let `F` be a nonarchimedean local field with ring of integers `𝒪` and let `π ∈ 𝒪` be a uniformizer
of residue degree `q` (i.e. `f(T) = πT + T^q` is the standard Lubin–Tate polynomial).  The
`n`-th Eisenstein factor

`f^{[n]}(T) = f^{(n-1)}(T)^{q-1} + π`

is monic of degree `d = (q-1)q^n` with constant coefficient `π`, hence is the minimal polynomial of
a primitive `π^{n+1}`-division point `π_n` and

`Nm_{K_n/F}(π_n) = (-1)^d · π = (-1)^{(q-1)q^n} · π`

(Milne, *CFT*, §I.3; the norm computation used in the proof of the local reciprocity law, cf.
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, §V.4).

The content is the general fact that for a **monic** polynomial `p` over a field `K` the norm of
the class of `X` in `K[X]/(p)` is `(-1)^{deg p} · p(0)`: the multiplication-by-`X` operator on
`K[X]/(p)` is the companion matrix of `p`.

## Main results

* `norm_root_of_monic` — the general norm formula for a root of a monic polynomial;
* `LTpolyEis_monic_natDegree_coeff_zero` — the shape of `f^{[n]}`: monic, of degree `(q-1)q^n`,
  with constant coefficient `π`;
* `norm_root_LTpolyEis` — `Nm(π_n) = (-1)^{(q-1)q^n} · π`.
-/

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

open Polynomial

/-- **The norm of the root of a monic polynomial.**  For a monic polynomial `p` over a field `K`,
the norm over `K` of the class of `X` in `K[X]/(p) = AdjoinRoot p` is `(-1)^{deg p}` times the
constant coefficient of `p`.

Indeed `1, X, …, X^{deg p - 1}` is a `K`-basis of `AdjoinRoot p` in which multiplication by `X`
is the companion matrix of `p`, whose determinant is `(-1)^{deg p} p(0)`; this is the power basis
`AdjoinRoot.powerBasis` together with
`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`. -/
theorem norm_root_of_monic {K : Type u} [Field K] (p : Polynomial K) (hp : p.Monic) :
    Algebra.norm K (AdjoinRoot.root p : AdjoinRoot p) =
      (-1) ^ p.natDegree * p.coeff 0 := by
  have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (AdjoinRoot.powerBasis hp.ne_zero)
  rwa [AdjoinRoot.minpoly_powerBasis_gen_of_monic hp, AdjoinRoot.powerBasis_gen,
    AdjoinRoot.powerBasis_dim] at h

/-- **The shape of the Eisenstein factor `f^{[n]}`**:  for `q ≥ 2` the polynomial
`f^{[n]}(T) = f^{(n-1)}(T)^{q-1} + π` is monic of degree `(q-1)q^n` with constant coefficient `π`
(so that, when `A` is a field, it is the minimal polynomial of a primitive division point). -/
theorem LTpolyEis_monic_natDegree_coeff_zero {A : Type u} [CommRing A] [Nontrivial A]
    (π : A) (q n : ℕ) (hq : 2 ≤ q) :
    (NK.LocalReciprocityLubinTate.LTpolyEis π q n).Monic ∧
      (NK.LocalReciprocityLubinTate.LTpolyEis π q n).natDegree = (q - 1) * q ^ n ∧
      (NK.LocalReciprocityLubinTate.LTpolyEis π q n).coeff 0 = π := by
  obtain ⟨hmon, hnat, -, hc0⟩ :=
    NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree π q n hq
  have hpowmon : ((LTpolyIter π q n) ^ (q - 1)).Monic := hmon.pow _
  have hpowdeg : ((LTpolyIter π q n) ^ (q - 1)).natDegree = (q - 1) * q ^ n := by
    rw [hmon.natDegree_pow, hnat]
  have hdegpos : 0 < (q - 1) * q ^ n := Nat.mul_pos (by omega) (pow_pos (by omega) n)
  -- the constant term of the power `f^{(n-1),q-1}` is `0`, so it does not interfere
  have hlt : (Polynomial.C π).degree < ((LTpolyIter π q n) ^ (q - 1)).degree := by
    refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [degree_eq_natDegree hpowmon.ne_zero, hpowdeg]
    exact_mod_cast hdegpos
  have hzero : ((LTpolyIter π q n) ^ (q - 1)).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_pow,
      show (LTpolyIter π q n).eval 0 = 0 by rw [← coeff_zero_eq_eval_zero, hc0],
      zero_pow (by omega : q - 1 ≠ 0)]
  refine ⟨hpowmon.add_of_left hlt, ?_, ?_⟩
  · rw [NK.LocalReciprocityLubinTate.LTpolyEis, natDegree_add_eq_left_of_degree_lt hlt, hpowdeg]
  · rw [NK.LocalReciprocityLubinTate.LTpolyEis, coeff_add, hzero, Polynomial.coeff_C_zero,
      zero_add]

/-- **The norm of a primitive `π^{n+1}`-division point is `±π`**:  with `f^{[n]}` the `n`-th
Eisenstein factor of the standard Lubin–Tate polynomial `f(T) = πT + T^q` (`q ≥ 2`),

`Nm_{K_n/F}(π_n) = (-1)^{(q-1)q^n} · π`

where `π_n` is the class of `X` in `F[X]/(f^{[n]})`, i.e. a root of `f^{[n]}` (Milne, *CFT*,
§I.3). -/
theorem norm_root_LTpolyEis (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : (↥(ValuativeRel.valuation F).integer)) (hπ : Irreducible π)
    (q n : ℕ) (hq : 2 ≤ q) :
    Algebra.norm F (AdjoinRoot.root (NK.LocalReciprocityLubinTate.LTpolyEis (π : F) q n) :
        AdjoinRoot (NK.LocalReciprocityLubinTate.LTpolyEis (π : F) q n)) =
      (-1) ^ ((q - 1) * q ^ n) * (π : F) := by
  obtain ⟨hmon, hnat, hc0⟩ :=
    LTpolyEis_monic_natDegree_coeff_zero (π : F) q n hq
  rw [norm_root_of_monic _ hmon, hnat, hc0]

end NK.LocalReciprocityLubinTate.LubinTate

