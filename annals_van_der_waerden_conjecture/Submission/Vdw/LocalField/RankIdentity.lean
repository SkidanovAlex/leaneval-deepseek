import Mathlib
import Submission.Vdw.LocalField.QpIntFinite
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.LinearAlgebra.Dimension.Localization

open scoped NumberField WithZero Valued
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# Local-field chapter (G2(b)): the rank identity at the completed tower

With `Module.Finite (QpInt p) (kpInt p P)` (`QpIntFinite`, step (a3)+(a4))
this module closes the algebraic core of G2(b):

* `kpInt_torsionFree` — `kpInt p P` is torsion-free as a `QpInt p`-module
  (both rings embed into the field `kpAdic p P`; a nonzero scalar annihilating
  an element would annihilate it in the field);
* `flat_kpInt_QpInt` — with `QpInt p` a Dedekind domain (a DVR), torsion-free
  makes `kpInt p P` a flat `QpInt p`-module (Mathlib
  `[IsDedekindDomain R] [IsTorsionFree R M] : Module.Flat R M`);
* `primesOver_maximalIdeal_eq` — the primes of `kpInt` over the maximal ideal
  of `QpInt` are exactly the (single) maximal ideal of `kpInt`
  (`IsLocalRing.primesOver_eq`: `kpInt` is a local Dedekind domain, finite
  and faithful over the local `QpInt`);
* **`kpInt_fundamental`** — the fundamental identity at the completed tower:
  `e·f = Module.finrank (QpInt p) (kpInt p P)` where
  `e := mS.ramificationIdx (QpInt p)`, `f := mS.inertiaDeg (QpInt p)`,
  `mS := maximalIdeal (kpInt p P)` (instantiate
  `Ideal.sum_ramification_inertia_eq_finrank` at the tower
  `QpInt p → kpInt p P` over the maximal ideal of the base, then collapse the
  single prime via `primesOver_maximalIdeal_eq`);
* **`finrank_field_eq_finrank_int`** — the fraction-field bridge:
  `Module.finrank (QpAdic p) (kpAdic p P) = Module.finrank (QpInt p) (kpInt p P)`
  (`IsFractionRing.finrank_eq`; the towers are rfl-level, see below);
* **`finrank_kpAdic_eq_ramIdx_mul_inertiaDeg`** — the rank identity:
  `[K_P : ℚ_p] = e·f` for the completion `K_P` of the number field `K` at the
  prime `P | (p)`, with `e,f` the ramification index and inertia degree of the
  *completed* tower (the maximal ideal of `kpInt` over the maximal ideal of
  `ℤ_[p]`).

Remaining translation stones (recorded in Roadmap Session-70):
(a) identifying `e = P.ramificationIdx ℤ` and `f = P.inertiaDeg ℤ` (the
global tower ℤ → 𝓞 K): `f` via the residue fields
(`completion_residueField_equiv` + `ResidueInstances.kpIntResidue_card` show
the completed residue field has `p^{P.inertiaDeg ℤ}` elements, and the base
residue field is `𝔽_p`), `e` via the length/valuation definitions
(`ramificationIdx_def` + the valuation compatibility
`valuation_rat_pow_ramificationIdx` — `v_{K_P}(p) = e_P`); and
(b) re-spelling scalars as `Padic p` (`qpPadicEquiv`).
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- `kpInt p P` is torsion-free as a `QpInt p`-module: both rings embed into
the field `kpAdic p P` (the scalar action is the `QpInt`-algebra one, and a
nonzero scalar has nonzero image in the field, so it cannot annihilate a
nonzero element). -/
lemma kpInt_torsionFree (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.IsTorsionFree (QpInt p) (kpInt p P) := by
  refine Module.IsTorsionFree.of_smul_eq_zero ?_
  intro r m hm
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    have hcoef : ((r • m : kpInt p P) : kpAdic p P) = (0 : kpAdic p P) := by
      exact congrArg (fun x : kpInt p P => (x : kpAdic p P)) hm
    rw [Algebra.smul_def] at hcoef
    have hprod : ((qpIntToKpInt p P r : kpAdic p P) * (m : kpAdic p P)) = 0 := by
      change ((qpIntToKpInt p P r * m : kpInt p P) : kpAdic p P) = (0 : kpAdic p P)
      exact hcoef
    have hrQ : (r : QpAdic p) ≠ 0 := by
      intro hz
      apply hr
      apply Subtype.ext
      exact hz
    have hIm : algebraMap (QpAdic p) (kpAdic p P) (r : QpAdic p) ≠ 0 := by
      intro h0
      have hinj : Function.Injective (algebraMap (QpAdic p) (kpAdic p P)) := by
        exact RingHom.injective (algebraMap (QpAdic p) (kpAdic p P))
      exact hrQ (hinj (by simpa using h0))
    have hval : (qpIntToKpInt p P r : kpAdic p P) =
        algebraMap (QpAdic p) (kpAdic p P) (r : QpAdic p) := by
      rfl
    rw [hval] at hprod
    have hmK : (m : kpAdic p P) = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_left hIm
    apply Subtype.ext
    exact hmK

/-- `kpInt p P` is flat as a `QpInt p`-module: `QpInt p` is a Dedekind domain
(a DVR) and `kpInt` is torsion-free. -/
instance flat_kpInt_QpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.Flat (QpInt p) (kpInt p P) := by
  haveI : Module.IsTorsionFree (QpInt p) (kpInt p P) := kpInt_torsionFree p P
  infer_instance

/-- The primes of `kpInt p P` lying over the maximal ideal of `QpInt p` are
exactly the maximal ideal of `kpInt p P` (the tower is a finite extension of
local Dedekind domains, so the single prime of the top lies over the maximal
ideal of the bottom). -/
lemma primesOver_maximalIdeal_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Ideal.primesOver (IsLocalRing.maximalIdeal (QpInt p)) (kpInt p P) =
      ({IsLocalRing.maximalIdeal (kpInt p P)} : Set (Ideal (kpInt p P))) := by
  classical
  haveI : Module.IsTorsionFree (QpInt p) (kpInt p P) := kpInt_torsionFree p P
  haveI : FaithfulSMul (QpInt p) (kpInt p P) := by
    haveI : IsCancelMulZero (QpInt p) := inferInstance
    infer_instance
  have hp0 : IsLocalRing.maximalIdeal (QpInt p) ≠ (⊥ : Ideal (QpInt p)) :=
    IsDiscreteValuationRing.not_a_field (QpInt p)
  simpa using (IsLocalRing.primesOver_eq (A := kpInt p P) hp0)

/-- **The fundamental identity at the completed tower**: the ramification
index times the inertia degree of the maximal ideal of `kpInt p P` over the
maximal ideal of `QpInt p` equals the rank of `kpInt p P` as a
`QpInt p`-module (a single prime lies over the maximal ideal of the base, so
the sum over primes collapses). -/
theorem kpInt_fundamental (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (IsLocalRing.maximalIdeal (kpInt p P)).ramificationIdx (QpInt p) *
      (IsLocalRing.maximalIdeal (kpInt p P)).inertiaDeg (QpInt p) =
    Module.finrank (QpInt p) (kpInt p P) := by
  classical
  let mR : Ideal (QpInt p) := IsLocalRing.maximalIdeal (QpInt p)
  let mS : Ideal (kpInt p P) := IsLocalRing.maximalIdeal (kpInt p P)
  haveI : Module.IsTorsionFree (QpInt p) (kpInt p P) := kpInt_torsionFree p P
  haveI : mR.IsPrime := by
    simpa [mR] using (IsLocalRing.maximalIdeal.isMaximal (QpInt p)).isPrime
  have heq : mR.primesOver (kpInt p P) = ({mS} : Set (Ideal (kpInt p P))) := by
    simpa [mR, mS] using primesOver_maximalIdeal_eq p P
  have hFin : (mR.primesOver (kpInt p P)).Finite := by
    rw [heq]
    exact Set.finite_singleton mS
  haveI : Fintype (mR.primesOver (kpInt p P)) := Set.Finite.fintype hFin
  have hsum := Ideal.sum_ramification_inertia_eq_finrank
    (R := QpInt p) (p := mR) (S := kpInt p P)
  have hmemS : mS ∈ mR.primesOver (kpInt p P) := by
    rw [heq]
    simp
  let T := mR.primesOver (kpInt p P)
  let mS' : T := ⟨mS, hmemS⟩
  have huniq : ∀ q : T, q = mS' := by
    intro q
    apply Subtype.ext
    have hq : (q : Ideal (kpInt p P)) ∈ mR.primesOver (kpInt p P) := q.2
    rw [heq] at hq
    simpa using hq
  have huniv : (Finset.univ : Finset T) = {mS'} := by
    ext q
    simp [huniq q]
  have hcollapse :
      (∑ q : T, q.1.ramificationIdx (QpInt p) * q.1.inertiaDeg (QpInt p))
        = mS.ramificationIdx (QpInt p) * mS.inertiaDeg (QpInt p) := by
    rw [huniv, Finset.sum_singleton]
  change (∑ q : T, q.1.ramificationIdx (QpInt p) * q.1.inertiaDeg (QpInt p))
      = Module.finrank (QpInt p) (kpInt p P) at hsum
  rw [hcollapse] at hsum
  simpa [mR, mS] using hsum

/-- **Fraction-field bridge**: the rank of the finite module
`kpInt p P` over `QpInt p` equals the degree of the extension of fraction
fields `kpAdic p P / QpAdic p` (both `QpInt` and `kpInt` are the rings of
integers of their fraction fields, which are the ℚ_p-completion and the
K_P-completion). -/
theorem finrank_field_eq_finrank_int (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.finrank (QpAdic p) (kpAdic p P) = Module.finrank (QpInt p) (kpInt p P) := by
  letI : IsScalarTower (QpInt p) (kpInt p P) (kpAdic p P) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rfl
  letI : IsScalarTower (QpInt p) (QpAdic p) (kpAdic p P) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rfl
  exact (IsFractionRing.finrank_eq (A := QpInt p) (K := QpAdic p) (B := kpInt p P) (L := kpAdic p P))

/-- **The rank identity**: the degree `[K_P : ℚ_p]` of the completion of the
number field at `P | (p)` equals `e·f`, the product of the ramification index
and the inertia degree of the completed tower (maximal ideal of `kpInt p P`
over the maximal ideal of `QpInt p`). -/
theorem finrank_kpAdic_eq_ramIdx_mul_inertiaDeg (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.finrank (QpAdic p) (kpAdic p P) =
      (IsLocalRing.maximalIdeal (kpInt p P)).ramificationIdx (QpInt p) *
        (IsLocalRing.maximalIdeal (kpInt p P)).inertiaDeg (QpInt p) := by
  rw [finrank_field_eq_finrank_int p P]
  exact (kpInt_fundamental p P).symm

end
end Submission.Vdw.LocalField
