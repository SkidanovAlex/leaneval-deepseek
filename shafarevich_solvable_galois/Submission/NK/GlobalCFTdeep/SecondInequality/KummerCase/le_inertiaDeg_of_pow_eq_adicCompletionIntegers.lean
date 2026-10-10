import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- **The residue-degree lower bound for a Kummer twist at a prime not above `p`.**

Let `K ⊆ L` be a finite extension of number fields, `p` a prime, `Q` a prime of `𝓞 K` with
`p ∉ Q`, and `q` a prime of `𝓞 L` above `Q`.  Let `u` be a unit of the completed integer ring
`𝒪_{K_Q} = Q.adicCompletionIntegers K` and `θ ∈ 𝒪_{L_q}` an element with
`θ ^ p = algebraMap 𝒪_{K_Q} 𝒪_{L_q} u`.  If `u` is **not** a `p`-th power in `K_Qˣ`, then the
global residue degree satisfies `p ≤ f(q|Q) = q.asIdeal.inertiaDeg (𝓞 K)`.

(Such a `θ` exists whenever `L = K(b^{1/p})` and `u` is the image of a local unit `b`; the
hypothesis that `u` is not a local `p`-th power is what makes the local extension nontrivial.)

Route.
* Work in the completed integer rings `R = Q.adicCompletionIntegers K`,
  `S = q.adicCompletionIntegers L` with the given algebra structure and the maximal ideals, which
  lie over each other by `hlies`.  Put `f = X ^ p - C u ∈ R[X]` and let `g` be its image in
  `(R ⧸ m_R)[X]`, i.e. `g = X ^ p - C ū`; the residue `ū` of `u` is **not** a `p`-th power in the
  residue field: otherwise `Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow` (with
  `p` invertible in `R`, which is `hQ`) would produce a `p`-th root of `u` in `Rˣ`, contradicting
  `hnot`.
* The residue field of `R` is finite; in a finite field an element with no `p`-th root (for `p`
  prime) satisfies: `X ^ p - C ū` is irreducible.  Hence `g` is irreducible of degree `p`.
* Apply `Commons.NumberTheory.NumberField.Completion.natDegree_le_inertiaDeg_of_aeval_eq_zero`
  with `R`, `S`, `f`, `g`, `θ` (the root condition is the hypothesis `hθ`): this gives
  `p = g.natDegree ≤ (m_S).inertiaDeg R`, the inertia degree of the *local* residue field
  extension, which is `Module.finrank (R ⧸ m_R) (S ⧸ m_S)` by `Ideal.inertiaDeg_eq_of_isMaximal`.
* Convert the local inertia degree into the global one by comparing the two expressions for the
  cardinality of the residue field of the completion, which is a power of the common residue field
  cardinality (at least `2`):
  `Commons...natCard_residueField_adicCompletion_eq_pow_inertiaDeg` and
  `Module.natCard_eq_pow_finrank`. -/
theorem le_inertiaDeg_of_pow_eq_adicCompletionIntegers
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) (hp : p.Prime)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hQ : (p : NumberField.RingOfIntegers K) ∉ Q.asIdeal)
    [Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)]
    (hlies : Ideal.LiesOver (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)))
    (u : (Q.adicCompletionIntegers K)ˣ) (θ : q.adicCompletionIntegers L)
    (hθ : θ ^ p = algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) u)
    (hnot : ∀ c : (Q.adicCompletion K)ˣ, (c : Q.adicCompletion K) ^ p ≠ (u : Q.adicCompletion K)) :
    p ≤ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  classical
  haveI hhen : HenselianLocalRing (Q.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
      (R := NumberField.RingOfIntegers K) (K := K) Q
  haveI hfinR : Finite (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K Q
  haveI hfinS : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L q
  haveI hfinR' : Finite ((Q.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := hfinR
  haveI hfinS' : Finite ((q.adicCompletionIntegers L) ⧸
      IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) := hfinS
  haveI hmR : (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal _
  haveI hmS : (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal _
  haveI hLO : (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).LiesOver
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := hlies
  letI hfield : Field ((Q.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
  -- `p` is a unit of the completed ring of integers
  have hpunit : IsUnit (p : Q.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    intro h0
    obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists Q
    have h1 : e (p : IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) =
        (p : NumberField.RingOfIntegers K ⧸ Q.asIdeal) := map_natCast e.toRingHom p
    have h2 : (p : NumberField.RingOfIntegers K ⧸ Q.asIdeal) = 0 := by
      rw [← h1, h0]
      exact map_zero e
    exact hQ (Ideal.Quotient.eq_zero_iff_mem.mp h2)
  -- the residue of `u` is not a `p`-th power in the residue field
  have hnotpow : ∀ b : (Q.adicCompletionIntegers K ⧸
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)),
      b ^ p ≠ Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (u : Q.adicCompletionIntegers K) := by
    intro b hb
    obtain ⟨a, hap, _hres⟩ :=
      Commons.RingTheory.Henselian.kummer_root_lift (R := Q.adicCompletionIntegers K) p
        u.isUnit hpunit b hb
    have haunit : IsUnit a :=
      (isUnit_pow_iff hp.ne_zero).mp (hap ▸ u.isUnit)
    obtain ⟨c, hc⟩ : ∃ c : (Q.adicCompletionIntegers K)ˣ,
        (c : Q.adicCompletionIntegers K) = a := ⟨haunit.unit, IsUnit.unit_spec haunit⟩
    have hcp : c ^ p = u := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hc]
      exact hap
    refine hnot (Units.map (ValuationSubring.subtype (Q.adicCompletionIntegers K)).toMonoidHom c) ?_
    have hh : (Units.map (ValuationSubring.subtype (Q.adicCompletionIntegers K)).toMonoidHom c) ^ p
        = Units.map (ValuationSubring.subtype (Q.adicCompletionIntegers K)).toMonoidHom u := by
      rw [← map_pow, hcp]
    have h2 := congrArg (fun w : (Q.adicCompletion K)ˣ => (w : Q.adicCompletion K)) hh
    simpa using h2
  -- the polynomial `X ^ p - C u` over `R` and its reduction `X ^ p - C u̅` over the residue field
  let f : Polynomial (Q.adicCompletionIntegers K) :=
    Polynomial.X ^ p - Polynomial.C (u : Q.adicCompletionIntegers K)
  let g : Polynomial ((Q.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
    Polynomial.X ^ p - Polynomial.C
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (u : Q.adicCompletionIntegers K))
  have hgmonic : g.Monic := Polynomial.monic_X_pow_sub_C _ hp.ne_zero
  have hgirr : Irreducible g := X_pow_sub_C_irreducible_of_prime hp hnotpow
  have hmap : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))) = g := by
    show (Polynomial.X ^ p - Polynomial.C (u : Q.adicCompletionIntegers K)).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))) =
      Polynomial.X ^ p - Polynomial.C
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
          (u : Q.adicCompletionIntegers K))
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  have haeval : Polynomial.aeval θ f = 0 := by
    show Polynomial.aeval θ (Polynomial.X ^ p - Polynomial.C (u : Q.adicCompletionIntegers K)) = 0
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, hθ, sub_self]
  have hbound : p ≤ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).inertiaDeg
      (Q.adicCompletionIntegers K) := by
    have h := Commons.NumberTheory.NumberField.Completion.natDegree_le_inertiaDeg_of_aeval_eq_zero
      (R := Q.adicCompletionIntegers K) (S := q.adicCompletionIntegers L)
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))
      f g hgmonic hgirr hmap θ haeval
    have h2 : g.natDegree = p := Polynomial.natDegree_X_pow_sub_C
    omega
  -- convert the local inertia degree into the global one
  have hconv : (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).inertiaDeg
      (Q.adicCompletionIntegers K) = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L))]
    haveI hMF : Module.Finite
        ((Q.adicCompletionIntegers K) ⧸ IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        ((q.adicCompletionIntegers L) ⧸ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) :=
      Module.Finite.of_finite
    have hA : Nat.card ((q.adicCompletionIntegers L) ⧸
          IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) =
        Nat.card ((Q.adicCompletionIntegers K) ⧸
            IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^
          Module.finrank ((Q.adicCompletionIntegers K) ⧸
            IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
            ((q.adicCompletionIntegers L) ⧸
              IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) :=
      Module.natCard_eq_pow_finrank
    have hB : Nat.card ((q.adicCompletionIntegers L) ⧸
          IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) =
        Nat.card ((Q.adicCompletionIntegers K) ⧸
            IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^
          q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
      Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
        K L Q q hq
    have h2 : 1 < Nat.card ((Q.adicCompletionIntegers K) ⧸
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := by
      haveI : Fintype ((Q.adicCompletionIntegers K) ⧸
          IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    exact (Nat.pow_right_inj h2).mp (hA.symm.trans hB)
  rw [← hconv]
  exact hbound

end NK.GlobalCFTdeep.SecondInequality.KummerCase
