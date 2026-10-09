import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Integers
import Submission.NK.LocalReciprocityLubinTate.LubinTate.EisFactor
import Submission.NK.LocalReciprocityLubinTate.LubinTate.DivisionPoints
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormOp
import Submission.NK.LocalReciprocityLubinTate.Unramified.resultant_normOp
import Submission.NK.LocalReciprocityLubinTate.Unramified.resultant_X_pow_sub_C_X
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The gain lemma for the Lubin–Tate norm operator

Let `F` be a characteristic-`0` nonarchimedean local field with ring of integers `𝒪`, `P ∈ 𝒪`
irreducible, `q = residueCard F`, `f = LTpoly P q = P·X + X^q` the standard Lubin–Tate polynomial
and `𝒩 = normOp f` the norm operator `𝒩(u)(Y) = Res_X(f(X) - Y, u(X))`.

This file proves, for the standard Lubin–Tate polynomial,

* `LTpolyIter_map_quotient` — the iterates of `f` are `X ^ (q ^ i)` modulo `P`;
* `isUnit_resultant_LTpolyIter` — `Res(f^{(i)}, g)` is a unit when `g.coeff 0` is;
* `normOp_sub_self_eq` — `𝒩(g) ≡ g` modulo `P`;
* `tracePoly_sCoeff_mem_span` — the first-order term of the `s`-parametrised resultant
  `G(s) = Res_X(f(X) - Y, 1 + s·t(X))` vanishes modulo `P`;
* `normOp_gain` — the **gain lemma**: `u ≡ 1` mod `P ^ k` implies `𝒩(u) ≡ 1` mod `P ^ (k+1)`;
* `normOp_iterate_mem_span` — its iteration;
* `resultant_LTpolyIter_eq_eval_normOp` — `Res(f^{(i)}, h) = 𝒩 ^ i (h)(0)`.
-/

namespace NK.LocalReciprocityLubinTate.Unramified

open Polynomial
open scoped ValuativeRel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The ring of integers of `F`, as a local abbreviation. -/
abbrev Integers (F : Type u) [Field F] [ValuativeRel F] : Type u := ↥(ValuativeRel.valuation F).integer

/-- **The iterates of the standard Lubin–Tate polynomial modulo `P`.**  For `A` a commutative ring,
`P ∈ A` and `q : ℕ`, the `i`-th iterate of `LTpoly P q` is `X ^ (q ^ i)` modulo `(P)`. -/
theorem LTpolyIter_map_quotient {A : Type u} [CommRing A] (P : A) (q i : ℕ) :
    (NK.LocalReciprocityLubinTate.LTpolyIter P q i).map
        (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) = Polynomial.X ^ (q ^ i) := by
  have hpoly : (NK.LocalReciprocityLubinTate.LTpoly P q).map
      (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) = Polynomial.X ^ q := by
    have : (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) P = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton.mpr dvd_rfl
    simp only [NK.LocalReciprocityLubinTate.LTpoly, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, this, Polynomial.C_0, zero_mul,
      zero_add]
  induction i with
  | zero => rw [NK.LocalReciprocityLubinTate.LTpolyIter_zero, pow_zero, pow_one,
      Polynomial.map_X]
  | succ i ih =>
    rw [NK.LocalReciprocityLubinTate.LTpolyIter_succ, Polynomial.map_comp, ih, hpoly,
      Polynomial.X_pow_comp, ← pow_mul, ← pow_succ']


/-- **`Res(f^{(i)}, g)` is a unit of `𝒪` when `g.coeff 0` is.**  Modulo `P` the iterate `f^{(i)}` is
`X ^ (q ^ i)`, so the resultant reduces to `(g.coeff 0) ^ (q ^ i)`, which is nonzero because
`g.coeff 0` is a unit; hence the resultant is not in the maximal ideal `(P)` and so is a unit of the
local ring `𝒪`. -/
theorem isUnit_resultant_LTpolyIter (P : ↥(ValuativeRel.valuation F).integer) (hP : Irreducible P)
    (q i : ℕ) (hq : 2 ≤ q) (g : Polynomial ↥(ValuativeRel.valuation F).integer)
    (hg : IsUnit (g.coeff 0)) :
    IsUnit ((NK.LocalReciprocityLubinTate.LTpolyIter P q i).resultant g) := by
  classical
  haveI hdom : IsDomain ↥(ValuativeRel.valuation F).integer := inferInstance
  set I : Ideal ↥(ValuativeRel.valuation F).integer :=
    Ideal.span ({P} : Set ↥(ValuativeRel.valuation F).integer) with hIdef
  have hI : I = IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer :=
    hP.maximalIdeal_eq.symm
  haveI hmax : I.IsMaximal := by rw [hI]; exact IsLocalRing.maximalIdeal.isMaximal _
  haveI hfield : Field (↥(ValuativeRel.valuation F).integer ⧸ I) := Ideal.Quotient.field I
  obtain ⟨-, hdeg, -, -⟩ :=
    NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree P q i hq
  -- the reduction of the resultant modulo `P`
  have hparams : (NK.LocalReciprocityLubinTate.LTpolyIter P q i).resultant g
      = (NK.LocalReciprocityLubinTate.LTpolyIter P q i).resultant g (q ^ i) g.natDegree := by
    rw [hdeg]
  have hkey : (Ideal.Quotient.mk I)
        ((NK.LocalReciprocityLubinTate.LTpolyIter P q i).resultant g)
      = (Polynomial.X ^ (q ^ i)).resultant (g.map (Ideal.Quotient.mk I)) (q ^ i) g.natDegree := by
    rw [hparams,
      ← Polynomial.resultant_map_map (NK.LocalReciprocityLubinTate.LTpolyIter P q i) g
        (q ^ i) g.natDegree (Ideal.Quotient.mk I),
      LTpolyIter_map_quotient]
  have hval : (Ideal.Quotient.mk I)
        ((NK.LocalReciprocityLubinTate.LTpolyIter P q i).resultant g)
      = ((Ideal.Quotient.mk I) (g.coeff 0)) ^ (q ^ i) := by
    rw [hkey, Polynomial.resultant_X_pow_left _ _ _ Polynomial.natDegree_map_le,
      Polynomial.coeff_map]
  have hunit : IsUnit (((Ideal.Quotient.mk I) (g.coeff 0)) ^ (q ^ i)) :=
    (hg.map (Ideal.Quotient.mk I)).pow _
  have hne : (Ideal.Quotient.mk I)
      ((NK.LocalReciprocityLubinTate.LTpolyIter P q i).resultant g) ≠ 0 := by
    rw [hval]
    exact hunit.ne_zero
  by_contra hcon
  have hmem : (NK.LocalReciprocityLubinTate.LTpolyIter P q i).resultant g
      ∈ IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hcon
  rw [← hI] at hmem
  exact hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)


/-! ## The Frobenius formula with an arbitrary degree parameter -/

/-- **The Frobenius formula for `Res_X(X ^ q - Y, h(X))`, with an arbitrary degree parameter.**
This is `resultant_X_pow_sub_C_X` with the second degree parameter `n` allowed to be larger than
`h.natDegree`; the two agree because the first polynomial is monic (`resultant_add_right_deg`). -/
theorem resultant_X_pow_sub_C_X' {A : Type u} [CommRing A] [IsDomain A]
    {p q k : ℕ} [Fact p.Prime] [CharP A p] (hq : q = p ^ k) (h : Polynomial A)
    {n : ℕ} (hn : h.natDegree ≤ n) :
    Polynomial.resultant (Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial A))
        (Polynomial.map Polynomial.C h) q n
      = ∑ j ∈ h.support, Polynomial.C (h.coeff j ^ q) * (Polynomial.X : Polynomial A) ^ j := by
  have hq1 : 1 ≤ q := by
    have : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
    omega
  obtain ⟨k', rfl⟩ : ∃ k', n = h.natDegree + k' :=
    ⟨n - h.natDegree, (Nat.add_sub_cancel' hn).symm⟩
  have hdle : (Polynomial.map Polynomial.C h).natDegree ≤ h.natDegree := (natDegree_map_C h).le
  have hf : (Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial A)).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by omega)
  have hfdeg : (Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial A)).natDegree = q :=
    Polynomial.natDegree_X_pow_sub_C
  have hcoeff : (Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial A)).coeff q = 1 := by
    have h := hf.coeff_natDegree
    rwa [hfdeg] at h
  have hparams : (Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial A)).resultant
        (Polynomial.map Polynomial.C h) q h.natDegree
      = (Polynomial.X ^ q - Polynomial.C (Polynomial.X : Polynomial A)).resultant
        (Polynomial.map Polynomial.C h) (Polynomial.X ^ q - Polynomial.C
          (Polynomial.X : Polynomial A)).natDegree (Polynomial.map Polynomial.C h).natDegree := by
    rw [hfdeg, natDegree_map_C h]
  rw [Polynomial.resultant_add_right_deg _ _ q h.natDegree k' hdle, hcoeff, one_pow, one_mul,
    hparams]
  exact resultant_X_pow_sub_C_X hq h

/-! ## Divisibility modulo `P` of the coefficients of a polynomial vanishing in the residue ring -/

/-- If every coefficient of `p` is divisible by `a`, then `p = C a * s` for some `s`. -/
theorem exists_eq_C_mul_of_coeff_dvd {A : Type u} [CommRing A] (a : A) (p : Polynomial A)
    (h : ∀ j, a ∣ p.coeff j) : ∃ s : Polynomial A, p = Polynomial.C a * s := by
  classical
  have key : ∀ j, ∃ c : A, p.coeff j = a * c := h
  choose w hw using key
  refine ⟨∑ j ∈ p.support, Polynomial.C (w j) * Polynomial.X ^ j, ?_⟩
  calc p = ∑ j ∈ p.support, Polynomial.C (p.coeff j) * Polynomial.X ^ j :=
        (Polynomial.sum_C_mul_X_pow_eq p).symm
    _ = ∑ j ∈ p.support, Polynomial.C a * (Polynomial.C (w j) * Polynomial.X ^ j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hw j, Polynomial.C_mul]
        ring
    _ = Polynomial.C a * ∑ j ∈ p.support, Polynomial.C (w j) * Polynomial.X ^ j := by
        rw [Finset.mul_sum]


/-! ## Step 2: the norm operator is congruent to the identity modulo `P` -/

/-- `(LTpoly P q)` is `X ^ q` modulo `P`. -/
theorem LTpoly_map_quotient {A : Type u} [CommRing A] (P : A) (q : ℕ) :
    (NK.LocalReciprocityLubinTate.LTpoly P q).map
        (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) = Polynomial.X ^ q := by
  have : (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) P = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr dvd_rfl
  simp only [NK.LocalReciprocityLubinTate.LTpoly, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, this, Polynomial.C_0, zero_mul,
    zero_add]

/-- **The norm operator of the standard Lubin–Tate polynomial is congruent to the identity modulo
`P`.**  Both sides are computed modulo `P`: there `f(X) ≡ X ^ q`, so the resultant of `f(X) - Y`
and `g(X)` is `∑_j (g.coeff j)^q Y^j` (`resultant_X_pow_sub_C_X'`), and the coefficients of `g` are
fixed by the `q`-th power map on the residue ring (`IsFrobeniusResidue`). -/
theorem normOp_LTpoly_sub_self_map_eq {A : Type u} [CommRing A] [IsDomain A]
    (P : A) [IsDomain (A ⧸ Ideal.span ({P} : Set A))]
    (q : ℕ) (hq : 2 ≤ q)
    (hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower P q)
    (hres : NK.LocalReciprocityLubinTate.IsFrobeniusResidue P q) (g : Polynomial A) :
    Polynomial.map (Ideal.Quotient.mk (Ideal.span ({P} : Set A)))
        (normOp (NK.LocalReciprocityLubinTate.LTpoly P q) g)
      = Polynomial.map (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) g := by
  classical
  obtain ⟨p, hp, hchar, k, hqk⟩ := hpow
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (A ⧸ Ideal.span ({P} : Set A)) p := hchar
  haveI : Nontrivial A := inferInstance
  have hfmon : (NK.LocalReciprocityLubinTate.LTpoly P q).Monic :=
    (NK.LocalReciprocityLubinTate.isMonicOfDegree_LTpoly hq).monic
  have hfdeg : (NK.LocalReciprocityLubinTate.LTpoly P q).natDegree = q :=
    (NK.LocalReciprocityLubinTate.isMonicOfDegree_LTpoly hq).natDegree_eq
  have hqpos : 0 < (NK.LocalReciprocityLubinTate.LTpoly P q).natDegree := by
    rw [hfdeg]; omega
  have hFdeg : (Polynomial.map Polynomial.C (NK.LocalReciprocityLubinTate.LTpoly P q)
      - Polynomial.C (Polynomial.X : Polynomial A)).natDegree = q := by
    rw [natDegree_map_C_sub_C_X _ hfmon hqpos, hfdeg]
  have hGdeg : (Polynomial.map Polynomial.C g).natDegree = g.natDegree := natDegree_map_C g
  -- the images of the two factors of the resultant
  have hmap1 : (Polynomial.map Polynomial.C (NK.LocalReciprocityLubinTate.LTpoly P q)
        - Polynomial.C (Polynomial.X : Polynomial A)).map
        (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span ({P} : Set A))))
      = Polynomial.X ^ q - Polynomial.C (Polynomial.X :
          Polynomial (A ⧸ Ideal.span ({P} : Set A))) := by
    have hcomp : (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span ({P} : Set A)))).comp
        (Polynomial.C : A →+* Polynomial A)
        = (Polynomial.C : (A ⧸ Ideal.span ({P} : Set A)) →+*
            Polynomial (A ⧸ Ideal.span ({P} : Set A))).comp
              (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) := by
      ext a; simp
    rw [Polynomial.map_sub, Polynomial.map_map, hcomp, ← Polynomial.map_map,
      LTpoly_map_quotient]
    have hX : (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span ({P} : Set A))))
        (Polynomial.X : Polynomial A) = Polynomial.X := Polynomial.map_X _
    simp only [Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hX]
  have hmap2 : (Polynomial.map Polynomial.C g).map
        (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span ({P} : Set A))))
      = Polynomial.map Polynomial.C
          (Polynomial.map (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) g) := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext a
    simp
  -- rewrite the norm operator with explicit degree parameters
  have hparams : normOp (NK.LocalReciprocityLubinTate.LTpoly P q) g
      = Polynomial.resultant (Polynomial.map Polynomial.C
            (NK.LocalReciprocityLubinTate.LTpoly P q)
            - Polynomial.C (Polynomial.X : Polynomial A))
        (Polynomial.map Polynomial.C g) q g.natDegree := by
    rw [normOp_def, hFdeg, hGdeg]
  rw [hparams]
  rw [show (Polynomial.map (Ideal.Quotient.mk (Ideal.span ({P} : Set A)))
        (Polynomial.resultant
          (Polynomial.map Polynomial.C (NK.LocalReciprocityLubinTate.LTpoly P q)
            - Polynomial.C (Polynomial.X : Polynomial A))
          (Polynomial.map Polynomial.C g) q g.natDegree))
      = Polynomial.resultant
          ((Polynomial.map Polynomial.C (NK.LocalReciprocityLubinTate.LTpoly P q)
            - Polynomial.C (Polynomial.X : Polynomial A)).map
              (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span ({P} : Set A)))))
          ((Polynomial.map Polynomial.C g).map
            (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span ({P} : Set A)))))
          q g.natDegree from
      (Polynomial.resultant_map_map
        (Polynomial.map Polynomial.C (NK.LocalReciprocityLubinTate.LTpoly P q)
          - Polynomial.C (Polynomial.X : Polynomial A))
        (Polynomial.map Polynomial.C g) q g.natDegree
        (Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span ({P} : Set A))))).symm]
  rw [hmap1, hmap2]
  -- the Frobenius formula, with the degree parameter `g.natDegree`
  rw [resultant_X_pow_sub_C_X' hqk _ Polynomial.natDegree_map_le]
  -- the coefficients of `g` are fixed by the `q`-th power map modulo `P`
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq
    (Polynomial.map (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) g)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_map, hres]

/-- **Step 2**: the norm operator of the standard Lubin–Tate polynomial is congruent to the
identity modulo `P`, coefficientwise. -/
theorem normOp_sub_self_mem_span {A : Type u} [CommRing A] [IsDomain A]
    (P : A) [IsDomain (A ⧸ Ideal.span ({P} : Set A))]
    (q : ℕ) (hq : 2 ≤ q)
    (hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower P q)
    (hres : NK.LocalReciprocityLubinTate.IsFrobeniusResidue P q) (g : Polynomial A) :
    normOp (NK.LocalReciprocityLubinTate.LTpoly P q) g - g
      ∈ Ideal.span ({Polynomial.C P} : Set (Polynomial A)) := by
  classical
  have hzero : (normOp (NK.LocalReciprocityLubinTate.LTpoly P q) g - g).map
      (Ideal.Quotient.mk (Ideal.span ({P} : Set A))) = 0 := by
    rw [Polynomial.map_sub, normOp_LTpoly_sub_self_map_eq P q hq hpow hres g, sub_self]
  have hcoeff : ∀ j, (Ideal.Quotient.mk (Ideal.span ({P} : Set A)))
      ((normOp (NK.LocalReciprocityLubinTate.LTpoly P q) g - g).coeff j) = 0 := by
    intro j
    have h := congrArg (fun u : Polynomial (A ⧸ Ideal.span ({P} : Set A)) => u.coeff j) hzero
    simpa only [Polynomial.coeff_zero, Polynomial.coeff_map] using h
  rw [Ideal.mem_span_singleton]
  obtain ⟨s, hs⟩ := exists_eq_C_mul_of_coeff_dvd P _
    (fun j => by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      exact hcoeff j)
  exact ⟨s, hs⟩


/-! ## The resultants of the iterates of `f` and the iterates of the norm operator -/

/-- **`Res(f^{(i)}, u) = (𝒩 ^ i (u))(0)`.**  The resultant with the `i`-th iterate of `f` is the
`i`-fold norm-operator iterate of `u`, evaluated at `0`.  (Induction on `i`, using the recursion
`Res(f^{(i+1)}, u) = Res(f^{(i)}, 𝒩 u)` given by the composition identity `resultant_normOp`.) -/
theorem resultant_LTpolyIter_eq_eval_normOp (P : ↥(ValuativeRel.valuation F).integer)
    (hP : Irreducible P) (q i : ℕ) (hq : 2 ≤ q)
    (u : Polynomial ↥(ValuativeRel.valuation F).integer) :
    (NK.LocalReciprocityLubinTate.LTpolyIter P q i).resultant u
      = (((normOp (NK.LocalReciprocityLubinTate.LTpoly P q))^[i]) u).eval 0 := by
  have hfmon : (NK.LocalReciprocityLubinTate.LTpoly P q).Monic :=
    (NK.LocalReciprocityLubinTate.isMonicOfDegree_LTpoly hq).monic
  have hfpos : 0 < (NK.LocalReciprocityLubinTate.LTpoly P q).natDegree := by
    rw [(NK.LocalReciprocityLubinTate.isMonicOfDegree_LTpoly hq).natDegree_eq]; omega
  induction i generalizing u with
  | zero =>
    rw [NK.LocalReciprocityLubinTate.LTpolyIter_zero, Function.iterate_zero_apply,
      ← Polynomial.coeff_zero_eq_eval_zero]
    rw [show (Polynomial.X : Polynomial ↥(ValuativeRel.valuation F).integer).resultant u
        = (Polynomial.X ^ 1).resultant u 1 u.natDegree from by
      rw [Polynomial.natDegree_X, pow_one]]
    rw [Polynomial.resultant_X_pow_left _ _ _ le_rfl, pow_one]
  | succ i ih =>
    have hmon : (NK.LocalReciprocityLubinTate.LTpolyIter P q i).Monic :=
      (NK.LocalReciprocityLubinTate.LubinTate.LTpolyIter_monic_degree P q i hq).1
    rw [NK.LocalReciprocityLubinTate.LTpolyIter_succ,
      ← resultant_normOp (NK.LocalReciprocityLubinTate.LTpoly P q)
        (NK.LocalReciprocityLubinTate.LTpolyIter P q i) u hfmon hfpos hmon,
      ih (normOp (NK.LocalReciprocityLubinTate.LTpoly P q) u),
      Function.iterate_succ_apply]

end NK.LocalReciprocityLubinTate.Unramified
