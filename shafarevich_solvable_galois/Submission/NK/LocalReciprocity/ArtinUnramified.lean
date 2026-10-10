import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalReciprocity.Frobenius
import Submission.NK.LocalReciprocity.NormGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical local Artin map of an unramified extension

Let `L / K` be a finite Galois extension of number fields, `Q` a place of `K` and `q` a place of
`L` above `Q` with ramification index one, so that the local extension `L_q / K_Q` is unramified
(hence cyclic).  In `NK.LocalReciprocity.Frobenius` we defined the canonical Frobenius
`frobeniusLocal Q q hunr`; here we define the **canonical (Frobenius-normalised) local Artin map**

`artinUnramified : K_Qˣ →* Gal(L_q/K_Q)`,   `x ↦ Frob ^ (n x)`,  `n x = - log v(x)`,

prove that it is surjective with kernel the norm group, that it sends the canonical uniformiser to
the Frobenius, and that it is the *unique* such map (`eq_artinUnramified_of`).  The last statement
turns the existential Artin map of
`Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_ramificationIdx_eq_one`
into a *canonical* one, and is what makes the Artin maps of the finite levels of a local field a
compatible system.
-/

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalReciprocity

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- **The exponent of a unit**: `n x = - log v x`, where `v` is the `Q`-adic valuation normalised
so that a uniformiser has valuation `exp (-1)`.  Hence `n (π) = 1` for a uniformiser and
`n (u) = 0` for a unit of the ring of integers. -/
def valExponent (K : Type*) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : (Q.adicCompletion K)ˣ) : ℤ :=
  - WithZero.log (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (x : Q.adicCompletion K))

/-- **The canonical uniformiser** of the local field `K_Q`, as a unit. -/
def uniformizerUnit (K : Type*) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : (Q.adicCompletion K)ˣ :=
  Units.mk0 ((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q :
      Q.adicCompletionIntegers K) : Q.adicCompletion K)
    ((Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ)))).mp
      (by simpa using Commons.RingTheory.Henselian.uniformizer_val_ne_zero (R := 𝓞 K) (K := K) Q))

theorem valExponent_apply (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (Q.adicCompletion K)ˣ) :
    valExponent K Q x = - WithZero.log (Valued.v (R := Q.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ)) (x : Q.adicCompletion K)) := rfl

theorem valExponent_mul (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x y : (Q.adicCompletion K)ˣ) :
    valExponent K Q (x * y) = valExponent K Q x + valExponent K Q y := by
  rw [valExponent_apply, valExponent_apply, valExponent_apply, Units.val_mul, map_mul,
    WithZero.log_mul ((Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)))).mpr x.ne_zero)
      ((Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)))).mpr y.ne_zero)]
  ring

theorem valExponent_one (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    valExponent K Q 1 = 0 := by
  rw [valExponent_apply, Units.val_one, map_one, WithZero.log_one, neg_zero]

theorem valExponent_zpow (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (Q.adicCompletion K)ˣ) (m : ℤ) :
    valExponent K Q (x ^ m) = m * valExponent K Q x := by
  rw [valExponent_apply, valExponent_apply, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow]
  ring

theorem valExponent_eq_zero_iff (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (Q.adicCompletion K)ˣ) :
    valExponent K Q x = 0 ↔
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (x : Q.adicCompletion K) = 1 := by
  have hx : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (x : Q.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v (R := Q.adicCompletion K)
      (Γ₀ := WithZero (Multiplicative ℤ)))).mpr x.ne_zero
  rw [valExponent_apply, neg_eq_zero]
  refine ⟨fun h => le_antisymm ?_ ?_, fun h => by rw [h, WithZero.log_one]⟩
  · have h1 : WithZero.log (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)) (x : Q.adicCompletion K)) ≤ WithZero.log 1 :=
      le_of_eq h
    exact (WithZero.log_le_log hx (by simp)).mp h1
  · have h1 : WithZero.log 1 ≤ WithZero.log (Valued.v (R := Q.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ)) (x : Q.adicCompletion K)) := le_of_eq h.symm
    exact (WithZero.log_le_log (by simp) hx).mp h1

theorem valExponent_uniformizerUnit (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    valExponent K Q (uniformizerUnit K Q) = 1 := by
  have h := Commons.NumberTheory.NumberField.Completion.log_val_uniformizer_eq_neg_one
    (K := K) Q
  rw [valExponent_apply]
  rw [show ((uniformizerUnit K Q : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) =
      ((Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q :
        Q.adicCompletionIntegers K) : Q.adicCompletion K) from rfl, h]
  ring

variable {L : Type*} [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The canonical (Frobenius-normalised) local Artin map of an unramified extension.** -/
def artinUnramified (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (Q.adicCompletion K)ˣ →* (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) where
  toFun x := frobeniusLocal Q q hunr ^ (valExponent K Q x)
  map_one' := by rw [valExponent_one, zpow_zero]
  map_mul' x y := by rw [valExponent_mul, zpow_add]

@[simp]
theorem artinUnramified_apply (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) (x : (Q.adicCompletion K)ˣ) :
    artinUnramified Q q hunr x = frobeniusLocal Q q hunr ^ (valExponent K Q x) := rfl

/-- The Artin map sends the canonical uniformiser to the Frobenius. -/
theorem artinUnramified_uniformizer (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    artinUnramified Q q hunr (uniformizerUnit K Q) = frobeniusLocal Q q hunr := by
  rw [artinUnramified_apply, valExponent_uniformizerUnit, zpow_one]

/-- **The unramified local Artin map is surjective**: the Frobenius generates the Galois group. -/
theorem artinUnramified_surjective (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Function.Surjective (artinUnramified Q q hunr) := by
  intro g
  have htop := frobeniusLocal_generates Q q hunr
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top g)
  refine ⟨uniformizerUnit K Q ^ m, ?_⟩
  rw [map_zpow, artinUnramified_uniformizer, hm]

/-- **The kernel of the unramified local Artin map is the group of norms.** -/
theorem ker_artinUnramified (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    MonoidHom.ker (artinUnramified Q q hunr) =
      normGroup (Q.adicCompletion K) (q.adicCompletion L) := by
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hfree : Module.Free (Q.adicCompletion K) (q.adicCompletion L) :=
    Module.Free.of_divisionRing _ _
  ext x
  have hx0 : (x : Q.adicCompletion K) ≠ 0 := x.ne_zero
  rw [MonoidHom.mem_ker, artinUnramified_apply, mem_normGroup_iff]
  have hker : frobeniusLocal Q q hunr ^ (valExponent K Q x) = 1 ↔
      ((q.asIdeal.inertiaDeg (𝓞 K) : ℤ) ∣ valExponent K Q x) := by
    rw [zpow_eq_one_iff_modEq, Int.modEq_iff_dvd, zero_sub, dvd_neg,
      orderOf_eq_inertiaDeg_of_isFrobeniusLocal Q q hunr _
        (frobeniusLocal_spec Q q hunr)]
  rw [hker, valExponent_apply, dvd_neg,
    Commons.NumberTheory.NumberField.Completion.dvd_inertiaDeg_log_val_iff_exists_norm_of_ramificationIdx_eq_one
      Q q hq hunr (x : Q.adicCompletion K) hx0]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.mk0 y ?_, ?_⟩
    · intro h0
      have hxzero : (x : Q.adicCompletion K) = 0 := by rw [← hy, h0, Algebra.norm_zero]
      exact hx0 hxzero
    · simpa using hy
  · rintro ⟨y, hy⟩
    exact ⟨(y : q.adicCompletion L), hy⟩

/-- **The canonical unramified local Artin isomorphism** `K_Qˣ ⧸ N(L_qˣ) ≃* Gal(L_q/K_Q)`,
Frobenius-normalised. -/
def artinUnramifiedEquiv (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ((Q.adicCompletion K)ˣ ⧸ normGroup (Q.adicCompletion K) (q.adicCompletion L)) ≃*
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_artinUnramified Q q hunr).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (artinUnramified_surjective Q q hunr))

/-- **Canonicity of the unramified local Artin map.**  A group homomorphism
`K_Qˣ →* Gal(L_q/K_Q)` with kernel the norm group which sends the canonical uniformiser to the
Frobenius is the canonical Artin map: since `x` and `π ^ n x` differ by an element of the norm
group (which is the kernel of both maps), both maps take the same value at `x`. -/
theorem eq_artinUnramified_of (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (Φ : (Q.adicCompletion K)ˣ →* (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L))
    (hker : MonoidHom.ker Φ = normGroup (Q.adicCompletion K) (q.adicCompletion L))
    (hπ : Φ (uniformizerUnit K Q) = frobeniusLocal Q q hunr) :
    Φ = artinUnramified Q q hunr := by
  ext x
  have hπmem : x * ((uniformizerUnit K Q) ^ (valExponent K Q x))⁻¹ ∈
      MonoidHom.ker (artinUnramified Q q hunr) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, artinUnramified_uniformizer,
      artinUnramified_apply]
    exact mul_inv_cancel _
  rw [ker_artinUnramified Q q hunr] at hπmem
  have hΦmem : Φ (x * ((uniformizerUnit K Q) ^ (valExponent K Q x))⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hπmem
  rw [map_mul, map_inv, map_zpow, hπ] at hΦmem
  rw [mul_inv_eq_one.mp hΦmem, artinUnramified_apply]

end

end NK.LocalReciprocity
