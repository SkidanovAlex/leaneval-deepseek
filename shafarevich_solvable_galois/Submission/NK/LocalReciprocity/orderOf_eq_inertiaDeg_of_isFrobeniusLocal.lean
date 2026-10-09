import Mathlib
import Submission.NK.LocalReciprocity.LocalSetup
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx
import Submission.Commons.NumberTheory.NumberField.Completion.algEquiv_mem_adicCompletionIntegers_iff
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The order of the local Frobenius is the inertia degree

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K`, and `q` a
place of `L` above `Q` which is unramified over `Q` (`e(q|Q) = 1`).  The local field `L_q` is a
finite Galois extension of `K_Q` with Galois group `Gal(L_q / K_Q)` of order `e(q|Q) · f(q|Q)`,
and the canonical Frobenius of this unramified local extension — the unique `K_Q`-automorphism of
`L_q` acting on the residue field by the `#k_Q`-power map
(`NK.LocalReciprocity.IsFrobeniusLocal`) — has order the inertia degree `f(q|Q)`.

This is the local counterpart of
`Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg`, and the proof follows the same
two steps:

* `orderOf σ ∣ f`, because `orderOf σ` divides the order `Nat.card Gal(L_q / K_Q) = e · f = f` of
  the local Galois group (`Commons...natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`);
* `f ≤ orderOf σ`, because the Frobenius condition says that `σ` acts on the residue field `k_q` of
  `L_q` by `y ↦ y ^ #k_Q`, hence `σ ^ orderOf σ = 1` acts trivially, so `y ^ (#k_Q ^ orderOf σ) = y`
  for every `y ∈ k_q`; as `#k_q = (#k_Q) ^ f` and `#k_Q ≥ 2`, the counting lemma
  `Commons.NumberTheory.NumberField.le_of_forall_pow_eq_self` gives `f ≤ orderOf σ`.
-/

set_option linter.style.haveILetI false

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalReciprocity

/-- The residue field `k_Q = 𝓞 K / Q` of a finite place of a number field has at least two
elements; equivalently `residueCard K Q ≥ 2`. -/
theorem two_le_residueCard (K : Type*) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 2 ≤ residueCard K Q := by
  haveI : Field (𝓞 K ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  haveI : Finite (𝓞 K ⧸ Q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
  haveI : Fintype (𝓞 K ⧸ Q.asIdeal) := Fintype.ofFinite _
  rw [residueCard,
    Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletionIntegers_eq_natCard_quotient
      K Q,
    Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- **The order of the local Frobenius is the inertia degree.**

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` and `q` a
place of `L` above `Q`, unramified over `Q` (`e(q|Q) = 1`).  Then a `K_Q`-algebra automorphism `σ`
of the local field `L_q = q.adicCompletion L` satisfying the Frobenius congruence
`σ x ≡ x ^ #k_Q (mod 𝔪)` on the ring of integers has order the inertia degree `f(q|Q)`.

Since the extension is unramified, `Gal(L_q / K_Q)` has order `e·f = f`, so `orderOf σ ∣ f`; and
the Frobenius congruence forces `σ` to act on the residue field `k_q` by the `#k_Q`-power map,
whose powers are trivial exactly on multiples of `f` because `[k_q : k_Q] = f`. -/
theorem orderOf_eq_inertiaDeg_of_isFrobeniusLocal {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
    (h : NK.LocalReciprocity.IsFrobeniusLocal Q q σ) :
    orderOf σ = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  classical
  -- the local Galois group is finite, being the automorphism group of a finite-dimensional
  -- algebra
  haveI hModFin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hFinGal : Finite (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    inferInstance
  -- ### First half: `orderOf σ ∣ f`, hence `orderOf σ ≤ f`
  have hcardG : Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    rw [Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q hq, hunr, one_mul]
  have hle : orderOf σ ≤ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    Nat.le_of_dvd (Ideal.inertiaDeg_pos q.asIdeal (NumberField.RingOfIntegers K))
      (hcardG ▸ orderOf_dvd_natCard σ)
  -- ### The residue action
  -- the induced ring automorphism of the ring of integers of the local field
  have hpres : ∀ x : q.adicCompletion L,
      σ x ∈ q.adicCompletionIntegers L ↔ x ∈ q.adicCompletionIntegers L :=
    Commons.NumberTheory.NumberField.Completion.algEquiv_mem_adicCompletionIntegers_iff_adicCompletion
      Q q hq σ
  let σB : q.adicCompletionIntegers L ≃+* q.adicCompletionIntegers L :=
    { toFun := fun x => ⟨σ (x : q.adicCompletion L), (hpres (x : q.adicCompletion L)).mpr x.2⟩
      invFun := fun y =>
        ⟨σ.symm (y : q.adicCompletion L), (hpres (σ.symm (y : q.adicCompletion L))).mp (by simp)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      map_mul' := fun x y => by ext; simp
      map_add' := fun x y => by ext; simp }
  have hcoe : ∀ x : q.adicCompletionIntegers L,
      ((σB x : q.adicCompletionIntegers L) : q.adicCompletion L) = σ (x : q.adicCompletion L) :=
    fun x => rfl
  -- the Frobenius congruence, as a statement about the residue field
  have hkey : ∀ x : q.adicCompletionIntegers L,
      IsLocalRing.residue (q.adicCompletionIntegers L) (σB x)
        = (IsLocalRing.residue (q.adicCompletionIntegers L) x) ^ residueCard K Q := by
    intro x
    have hid : (((σB x - x ^ residueCard K Q : q.adicCompletionIntegers L)) :
          q.adicCompletion L)
        = σ (x : q.adicCompletion L) - (x : q.adicCompletion L) ^ residueCard K Q := by
      simp [hcoe]
    have hmem : σB x - x ^ residueCard K Q ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) :=
      (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
        q _).mpr (by rw [hid]; exact h x)
    have hz := (IsLocalRing.residue_eq_zero_iff (R := q.adicCompletionIntegers L) _).mpr hmem
    rw [map_sub, map_pow] at hz
    exact sub_eq_zero.mp hz
  -- the action of the powers of `σB` on the ring of integers
  have hpowB : ∀ (m : ℕ) (x : q.adicCompletionIntegers L),
      (((σB ^ m) x : q.adicCompletionIntegers L) : q.adicCompletion L)
        = (σ ^ m) (x : q.adicCompletion L) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ,
        show (((σB ^ m * σB) x : q.adicCompletionIntegers L)) = (σB ^ m) (σB x) from rfl,
        ih (σB x), hcoe x]
      rfl
  -- the residue action of the powers of `σB`: `x ↦ x ^ (#k_Q ^ m)`
  have hresB : ∀ (m : ℕ) (x : q.adicCompletionIntegers L),
      IsLocalRing.residue (q.adicCompletionIntegers L) ((σB ^ m) x)
        = (IsLocalRing.residue (q.adicCompletionIntegers L) x) ^ (residueCard K Q ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ,
        show (((σB ^ m * σB) x : q.adicCompletionIntegers L)) = (σB ^ m) (σB x) from rfl,
        ih (σB x), hkey x, ← pow_mul, pow_succ, Nat.mul_comm]
  -- ### Second half: `f ≤ orderOf σ`
  have hfinal : ∀ y : IsLocalRing.ResidueField (q.adicCompletionIntegers L),
      y ^ (residueCard K Q ^ orderOf σ) = y := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have hfix : ((σB ^ orderOf σ) x : q.adicCompletionIntegers L) = x := by
      apply Subtype.ext
      rw [hpowB, pow_orderOf_eq_one]
      rfl
    rw [← hresB (orderOf σ) x, hfix]
  have hge : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤ orderOf σ := by
    haveI hfin : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
      Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L q
    haveI : Fintype (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) := Fintype.ofFinite _
    have hcardR : Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L))
        = residueCard K Q ^ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
      Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
        K L Q q hq
    exact Commons.NumberTheory.NumberField.le_of_forall_pow_eq_self hcardR
      (two_le_residueCard K Q) (orderOf_pos σ) hfinal
  exact le_antisymm hle hge

end NK.LocalReciprocity
