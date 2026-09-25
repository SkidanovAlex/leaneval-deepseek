import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.exists_orderOf_eq_inertiaDeg_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion

/-!
# The unramified local Artin map

For a finite Galois extension `L / K` of number fields, a height one prime `Q` of `𝓞 K` and a
height one prime `q` of `𝓞 L` lying over `Q` with ramification index one, we construct a
surjective group homomorphism

`Φ : (K_Q)ˣ →* Gal(L_q / K_Q)`

whose kernel is the group of norms of units of `L_q`.  Since `L_q / K_Q` is unramified, it is the
cyclic extension cut out by the Frobenius; `Φ` is the local Artin (reciprocity) map.

The proof is elementary.  Choose an element `σ` of the local Galois group with
`orderOf σ = f`, where `f = q.asIdeal.inertiaDeg (𝓞 K)` is the inertia degree (such an element
exists because the local Galois group is cyclic of order `f`).  For a unit `x` of `K_Q` let

`n x = - log v x`,

where `v` is the (additive) `Q`-adic valuation, normalised so that a uniformiser has valuation
`-1`.  Then `x ↦ σ ^ (n x)` is a group homomorphism `(K_Q)ˣ →* Gal(L_q / K_Q)`.

* It is surjective because `σ` generates the local Galois group (as `orderOf σ` equals its
  cardinality) and `n` is surjective onto `ℤ` (a uniformiser of `K_Q` has `n = 1`).
* Its kernel consists of the `x` with `f ∣ n x`, and `f ∣ n x` holds if and only if `x` is the
  norm of an element of `L_q`: the valuation of a norm is the inertia degree times the valuation
  (`v (N z) = (v z) ^ f`), and conversely every `x` whose valuation is divisible by `f` differs
  from `N (π_L ^ m)` (for a suitable uniformiser `π_L` of `L_q`) by a unit, which is a norm by
  `norm_units_surjective_of_ramificationIdx_eq_one`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- If the ramification index is one, the map of adic completions preserves the valuation. -/
lemma val_adicCompletionMap_eq_self_of_ramificationIdx_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) (z : Q.adicCompletion K) :
    Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq z) =
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) z := by
  rw [val_adicCompletionMap_eq_pow Q q hq z, hunr, pow_one]

/-- If the ramification index is one, the algebra map of adic completions preserves the
valuation. -/
lemma val_algebraMap_eq_self_of_ramificationIdx_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ z : Q.adicCompletion K,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) =
        Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) z := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro z
  rw [RingHom.algebraMap_toAlgebra]
  exact val_adicCompletionMap_eq_self_of_ramificationIdx_eq_one Q q hq hunr z

/-- The valuation of the norm of a nonzero element of `L_q` is the inertia degree times its
valuation. -/
lemma log_val_norm_eq_of_ramificationIdx_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ z : q.adicCompletion L,
      WithZero.log (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (Algebra.norm (Q.adicCompletion K) z)) =
        (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          WithZero.log (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            z) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro z
  have hpow := val_norm_adicCompletion_eq_pow Q q hq z
  have hvK : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (Algebra.norm (Q.adicCompletion K) z) =
      (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) z) ^
        (Module.finrank (Q.adicCompletion K) (q.adicCompletion L)) := by
    rw [← val_algebraMap_eq_self_of_ramificationIdx_eq_one Q q hq hunr
      (Algebra.norm (Q.adicCompletion K) z), hpow]
  have hfin : ((Module.finrank (Q.adicCompletion K) (q.adicCompletion L) : ℕ) : ℤ) =
      (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) := by
    have h := finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq
    rw [hunr, one_mul] at h
    exact_mod_cast h.symm
  calc WithZero.log (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (Algebra.norm (Q.adicCompletion K) z))
      = WithZero.log ((Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          z) ^ (Module.finrank (Q.adicCompletion K) (q.adicCompletion L))) := by rw [hvK]
    _ = WithZero.log ((Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          z) ^ ((Module.finrank (Q.adicCompletion K) (q.adicCompletion L) : ℕ) : ℤ)) := by
        rw [zpow_natCast]
    _ = ((Module.finrank (Q.adicCompletion K) (q.adicCompletion L) : ℕ) : ℤ) •
          WithZero.log (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            z) := WithZero.log_zpow _ _
    _ = (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          WithZero.log (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            z) := by rw [hfin, smul_eq_mul]

/-- The valuation of the uniformiser of a `v`-adic completion is `exp (-1)`, so its logarithm
is `-1`. -/
lemma log_val_uniformizer_eq_neg_one
    (V : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    WithZero.log (Valued.v (R := V.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) V :
          V.adicCompletionIntegers K) : V.adicCompletion K)) = -1 := by
  rw [Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one V, WithZero.log_exp]

/-- The logarithm of the valuation of the norm of a power of the uniformiser of `L_q` is
`- f * m`, where `f` is the inertia degree. -/
lemma log_val_norm_uniformizer_zpow_eq
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ m : ℤ,
      WithZero.log (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          (Algebra.norm (Q.adicCompletion K)
            (((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q :
              q.adicCompletionIntegers L) : q.adicCompletion L) ^ m))) =
        -((q.asIdeal.inertiaDeg (𝓞 K) : ℤ) * m) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro m
  rw [log_val_norm_eq_of_ramificationIdx_eq_one Q q hq hunr, map_zpow₀, WithZero.log_zpow,
    log_val_uniformizer_eq_neg_one q]
  ring

/-- The valuation (or rather its logarithm) of an element of `K_Q` is divisible by the inertia
degree if and only if the element is the norm of an element of `L_q`. -/
lemma dvd_inertiaDeg_log_val_iff_exists_norm_of_ramificationIdx_eq_one
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ x : Q.adicCompletion K, x ≠ 0 →
      ((q.asIdeal.inertiaDeg (𝓞 K) : ℤ) ∣
          WithZero.log (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) x) ↔
        ∃ y : q.adicCompletion L, Algebra.norm (Q.adicCompletion K) y = x) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hfree : Module.Free (Q.adicCompletion K) (q.adicCompletion L) :=
    Module.Free.of_divisionRing _ _
  intro x hx
  constructor
  · intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    set m : ℤ := -k with hmdef
    have hπne : ((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q :
        q.adicCompletionIntegers L) : q.adicCompletion L) ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v (R := q.adicCompletion L)
        (Γ₀ := WithZero (Multiplicative ℤ)))).mp (by
          simpa using Commons.RingTheory.Henselian.uniformizer_val_ne_zero (R := 𝓞 L) (K := L) q)
    have hNne : Algebra.norm (Q.adicCompletion K)
        (((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q :
            q.adicCompletionIntegers L) : q.adicCompletion L) ^ m) ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]
      exact zpow_ne_zero m hπne
    have hlogx : WithZero.log (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)) x) = -((q.asIdeal.inertiaDeg (𝓞 K) : ℤ) * m) := by
      rw [hk, hmdef]
      ring
    have hlogq : WithZero.log (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ))
          (x / Algebra.norm (Q.adicCompletion K)
            (((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q :
                q.adicCompletionIntegers L) : q.adicCompletion L) ^ m))) = 0 := by
      rw [map_div₀, WithZero.log_div ((Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
            (Γ₀ := WithZero (Multiplicative ℤ)))).mpr hx)
          ((Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
            (Γ₀ := WithZero (Multiplicative ℤ)))).mpr hNne),
        hlogx, log_val_norm_uniformizer_zpow_eq Q q hq hunr m]
      ring
    have hquotne : x / Algebra.norm (Q.adicCompletion K)
        (((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q :
            q.adicCompletionIntegers L) : q.adicCompletion L) ^ m) ≠ 0 :=
      div_ne_zero hx hNne
    have hval1 : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (x / Algebra.norm (Q.adicCompletion K)
          (((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q :
              q.adicCompletionIntegers L) : q.adicCompletion L) ^ m)) = 1 := by
      rw [← WithZero.exp_log ((Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)))).mpr hquotne), hlogq, WithZero.exp_zero]
    obtain ⟨y₀, hy₀⟩ := norm_units_surjective_of_ramificationIdx_eq_one Q q hq hunr
      (x / Algebra.norm (Q.adicCompletion K)
        (((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q :
            q.adicCompletionIntegers L) : q.adicCompletion L) ^ m)) hval1
    refine ⟨(((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 L) (K := L) q :
        q.adicCompletionIntegers L) : q.adicCompletion L) ^ m) * y₀, ?_⟩
    rw [map_mul, hy₀, mul_div_cancel₀ x hNne]
  · rintro ⟨y, hy⟩
    refine ⟨WithZero.log (Valued.v (R := q.adicCompletion L)
      (Γ₀ := WithZero (Multiplicative ℤ)) y), ?_⟩
    rw [← hy]
    exact log_val_norm_eq_of_ramificationIdx_eq_one Q q hq hunr y

/-- **The local Artin map of an unramified extension.**

If the prime `q` of `𝓞 L` lying over `Q` has ramification index one, there is a surjective group
homomorphism from the units of the `Q`-adic completion of `K` onto the Galois group of the local
extension `L_q / K_Q`, whose kernel is exactly the group of norms of units of `L_q`.  This is the
local Artin reciprocity map for the (cyclic) unramified local extension `L_q / K_Q`. -/
theorem exists_mulEquiv_artinMap_of_ramificationIdx_eq_one {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ Φ : (Q.adicCompletion K)ˣ →* (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      Function.Surjective Φ ∧
      (∀ x : (Q.adicCompletion K)ˣ, Φ x = 1 ↔
        ∃ y : (q.adicCompletion L)ˣ,
          Algebra.norm (Q.adicCompletion K) (y : q.adicCompletion L) =
            (x : Q.adicCompletion K)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hfree : Module.Free (Q.adicCompletion K) (q.adicCompletion L) :=
    Module.Free.of_divisionRing _ _
  haveI : Finite (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := inferInstance
  obtain ⟨σ, hσ⟩ := exists_orderOf_eq_inertiaDeg_of_ramificationIdx_eq_one Q q hq hunr
  have hcard : Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) =
      q.asIdeal.inertiaDeg (𝓞 K) :=
    natCard_algEquiv_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one Q q hq hunr
  let n : (Q.adicCompletion K)ˣ → ℤ := fun x =>
    - WithZero.log (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (x : Q.adicCompletion K))
  have hn : ∀ x : (Q.adicCompletion K)ˣ,
      n x = - WithZero.log (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)) (x : Q.adicCompletion K)) := fun x => rfl
  have hn_mul : ∀ x y : (Q.adicCompletion K)ˣ, n (x * y) = n x + n y := by
    intro x y
    rw [hn, hn, hn, Units.val_mul, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
          (Γ₀ := WithZero (Multiplicative ℤ)))).mpr x.ne_zero)
        ((Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
          (Γ₀ := WithZero (Multiplicative ℤ)))).mpr y.ne_zero)]
    ring
  let Φ : (Q.adicCompletion K)ˣ →*
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    { toFun := fun x => σ ^ (n x)
      map_one' := by rw [hn, Units.val_one, map_one, WithZero.log_one, neg_zero, zpow_zero]
      map_mul' := fun x y => by rw [hn_mul, zpow_add] }
  have hΦ : ∀ x : (Q.adicCompletion K)ˣ, Φ x = σ ^ (n x) := fun x => rfl
  refine ⟨Φ, ?_, ?_⟩
  · intro g
    have htop : Subgroup.zpowers σ = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hσ, hcard]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top g)
    have hπKne : ((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q :
        Q.adicCompletionIntegers K) : Q.adicCompletion K) ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)))).mp (by
          simpa using Commons.RingTheory.Henselian.uniformizer_val_ne_zero (R := 𝓞 K) (K := K) Q)
    let πK : (Q.adicCompletion K)ˣ :=
      Units.mk0 ((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q :
        Q.adicCompletionIntegers K) : Q.adicCompletion K) hπKne
    have hπKlog : WithZero.log (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)) ((πK : (Q.adicCompletion K)ˣ) : Q.adicCompletion K)) = -1 := by
      have : WithZero.log (Valued.v (R := Q.adicCompletion K)
          (Γ₀ := WithZero (Multiplicative ℤ))
          ((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q :
            Q.adicCompletionIntegers K) : Q.adicCompletion K)) = -1 :=
        log_val_uniformizer_eq_neg_one Q
      simpa [πK] using this
    have hnj : n (πK ^ j) = j := by
      rw [hn, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, hπKlog]
      simp
    refine ⟨πK ^ j, ?_⟩
    rw [hΦ, hnj, hj]
  · intro x
    have hx0 : (x : Q.adicCompletion K) ≠ 0 := x.ne_zero
    have hker : σ ^ (n x) = 1 ↔ (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) ∣ n x := by
      rw [zpow_eq_one_iff_modEq, Int.modEq_iff_dvd, zero_sub, dvd_neg, hσ]
    rw [hΦ, hker, hn, dvd_neg,
      dvd_inertiaDeg_log_val_iff_exists_norm_of_ramificationIdx_eq_one Q q hq hunr x hx0]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Units.mk0 y ?_, ?_⟩
      · intro h0
        have hxzero : (x : Q.adicCompletion K) = 0 := by rw [← hy, h0, Algebra.norm_zero]
        exact hx0 hxzero
      · simpa using hy
    · rintro ⟨y, hy⟩
      exact ⟨(y : q.adicCompletion L), hy⟩

end Commons.NumberTheory.NumberField.Completion
