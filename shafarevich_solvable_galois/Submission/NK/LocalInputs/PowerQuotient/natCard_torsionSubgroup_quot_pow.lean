import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Basic
import Submission.NK.LocalInputs.PowerQuotient.Setup
import Submission.NK.LocalInputs.PowerQuotient.exists_powTorsion_exponent
import Submission.NK.LocalInputs.PowerQuotient.natCard_powTorsion_quot_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p`-power quotient of the `p`-power torsion of the units of `𝒪_{K_𝔭}`

For a number field `K`, a finite prime `𝔭` of `K` and a prime `p`, let

  `H = torsionSubgroup 𝔭 p ≤ (𝔭.adicCompletionIntegers K)ˣ`

be the subgroup of elements `u` of the units of the ring of integers of the `𝔭`-adic completion
`κ = K_𝔭` such that `(coeUnit 𝔭 u) ^ (p ^ m) = 1` for some `m` — i.e. the `p`-power torsion of
`𝒪_κˣ`, viewed inside `κˣ`.

This file computes the order of the `p`-power quotient of `H`:

  `#(H / Hᵖ) = p ^ zetaIndicator p κ`,

that is `p` if `κ` contains a primitive `p`-th root of unity and `1` otherwise.

The route is to identify `H` with the `p`-power torsion subgroup of `κˣ`, which is the closure
`G` of the set of `p`-power torsion units of `κˣ`: indeed

* every `p`-power torsion unit of `κˣ` has valuation `1`, hence is a unit of `𝒪_κ` and therefore
  lies in the image of `coeUnit 𝔭` (`exists_unit_coeUnit_eq_of_val_eq_one`);
* this proves `H.map (coeUnit 𝔭) = G` (`map_torsionSubgroup_eq_closure`), since `G` is generated
  by those elements.

An isomorphism of groups transports the `p`-power quotient
(`natCard_quot_powMonoidHom_eq_of_mulEquiv`), and the cardinality of `G / Gᵖ` is the field-level
computation `natCard_powTorsion_quot_pow`, whose hypothesis (a uniform exponent bound for the
`p`-power torsion) is supplied by `exists_powTorsion_exponent`.
-/

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero
open IsDedekindDomain

namespace NK.LocalInputs.PowerQuotient

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The unit of `𝒪_κ` mapping to a unit of `κ` through `coeUnit` is unique: `coeUnit` is
injective. -/
lemma coeUnit_injective (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Injective (coeUnit 𝔭) :=
  Units.map_injective (fun a b h => Subtype.ext (by simpa using h))

/-- **A `p`-power torsion unit of the completion has valuation `1`.** -/
lemma val_eq_one_of_pow_eq_one {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {p : ℕ} (hp : p.Prime) {ζ : (𝔭.adicCompletion K)ˣ} (hζ : ∃ m : ℕ, ζ ^ p ^ m = 1) :
    (Valued.v : Valuation (𝔭.adicCompletion K) Zstar) (ζ : 𝔭.adicCompletion K) = 1 := by
  obtain ⟨m, hm⟩ := hζ
  have hm' : ((ζ : 𝔭.adicCompletion K)) ^ p ^ m = 1 := by
    simpa using congrArg (fun u : (𝔭.adicCompletion K)ˣ => (u : 𝔭.adicCompletion K)) hm
  have hle : (Valued.v : Valuation (𝔭.adicCompletion K) Zstar)
      (ζ : 𝔭.adicCompletion K) ≤ 1 :=
    val_le_one_of_pow_eq_one (𝔭 := 𝔭) (pow_ne_zero m hp.ne_zero) hm'
  have hvne : (Valued.v : Valuation (𝔭.adicCompletion K) Zstar)
      (ζ : 𝔭.adicCompletion K) ≠ 0 := by
    intro h
    exact Units.ne_zero ζ ((Valuation.zero_iff _).mp h)
  have hge : (1 : Zstar) ≤ (Valued.v : Valuation (𝔭.adicCompletion K) Zstar)
      (ζ : 𝔭.adicCompletion K) := by
    have hinv : (((ζ : 𝔭.adicCompletion K))⁻¹) ^ p ^ m = 1 := by
      rw [inv_pow, hm', inv_one]
    have h2 : ((Valued.v : Valuation (𝔭.adicCompletion K) Zstar)
        (ζ : 𝔭.adicCompletion K))⁻¹ ≤ 1 := by
      have h := val_le_one_of_pow_eq_one (𝔭 := 𝔭) (x := ((ζ : 𝔭.adicCompletion K))⁻¹)
        (pow_ne_zero m hp.ne_zero) hinv
      simpa using h
    have h3 := mul_le_mul_left h2 ((Valued.v : Valuation (𝔭.adicCompletion K) Zstar)
      (ζ : 𝔭.adicCompletion K))
    rw [inv_mul_cancel₀ hvne, one_mul] at h3
    exact h3
  exact le_antisymm hle hge

/-- **A unit of the completion of valuation `1` is a unit of the ring of integers.** -/
lemma exists_unit_coeUnit_eq_of_val_eq_one
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {ζ : (𝔭.adicCompletion K)ˣ}
    (hval : (Valued.v : Valuation (𝔭.adicCompletion K) Zstar) (ζ : 𝔭.adicCompletion K) = 1) :
    ∃ u : (𝔭.adicCompletionIntegers K)ˣ, coeUnit 𝔭 u = ζ := by
  have hζO : (ζ : 𝔭.adicCompletion K) ∈ 𝔭.adicCompletionIntegers K :=
    (mem_adicCompletionIntegers (R := NumberField.RingOfIntegers K) (K := K) (v := 𝔭)).mpr
      (le_of_eq hval)
  have hinvO : ((ζ : 𝔭.adicCompletion K))⁻¹ ∈ 𝔭.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, Valuation.map_inv, hval, inv_one]
  have h1 : (⟨(ζ : 𝔭.adicCompletion K), hζO⟩ : 𝔭.adicCompletionIntegers K) *
      ⟨((ζ : 𝔭.adicCompletion K))⁻¹, hinvO⟩ = 1 := by
    refine Subtype.ext ?_
    rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk,
      mul_inv_cancel₀ (Units.ne_zero ζ)]
  have h2 : (⟨((ζ : 𝔭.adicCompletion K))⁻¹, hinvO⟩ : 𝔭.adicCompletionIntegers K) *
      ⟨(ζ : 𝔭.adicCompletion K), hζO⟩ = 1 := by
    refine Subtype.ext ?_
    rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk,
      inv_mul_cancel₀ (Units.ne_zero ζ)]
  refine ⟨Units.mk ⟨(ζ : 𝔭.adicCompletion K), hζO⟩
    ⟨((ζ : 𝔭.adicCompletion K))⁻¹, hinvO⟩ h1 h2, ?_⟩
  refine Units.ext ?_
  simp only [coeUnit, Units.coe_map]
  rfl

/-- **Every `p`-power torsion unit of the completion is a unit of the ring of integers.** -/
lemma exists_unit_coeUnit_eq_of_pow_eq_one
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p : ℕ}
    (hp : p.Prime) {ζ : (𝔭.adicCompletion K)ˣ} (hζ : ∃ m : ℕ, ζ ^ p ^ m = 1) :
    ∃ u : (𝔭.adicCompletionIntegers K)ˣ, coeUnit 𝔭 u = ζ :=
  exists_unit_coeUnit_eq_of_val_eq_one (val_eq_one_of_pow_eq_one (𝔭 := 𝔭) hp hζ)

/-- **The `p`-power torsion of `𝒪_κˣ` has the `p`-power torsion of `κˣ` as its image.** -/
lemma map_torsionSubgroup_eq_closure
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p : ℕ}
    (hp : p.Prime) :
    (torsionSubgroup 𝔭 p).map (coeUnit 𝔭) =
      Subgroup.closure {ζ : (𝔭.adicCompletion K)ˣ | ∃ m : ℕ, ζ ^ p ^ m = 1} := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨u, hu, rfl⟩
    exact Subgroup.subset_closure ((mem_torsionSubgroup_iff).mp hu)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro ζ ⟨m, hm⟩
    obtain ⟨u, rfl⟩ := exists_unit_coeUnit_eq_of_pow_eq_one (𝔭 := 𝔭) hp ⟨m, hm⟩
    exact ⟨u, mem_torsionSubgroup_iff.mpr ⟨m, hm⟩, rfl⟩

/-- **An isomorphism of commutative groups induces an isomorphism of the `p`-power quotients**,
hence an equality of their cardinalities. -/
lemma natCard_quot_powMonoidHom_eq_of_mulEquiv {A B : Type*} [CommGroup A] [CommGroup B]
    (p : ℕ) (e : A ≃* B) :
    Nat.card (A ⧸ (powMonoidHom p : A →* A).range) =
      Nat.card (B ⧸ (powMonoidHom p : B →* B).range) := by
  have h : Subgroup.map (e : A →* B) (powMonoidHom p : A →* A).range =
      (powMonoidHom p : B →* B).range := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      simp only [SetLike.mem_coe, MonoidHom.mem_range] at hy ⊢
      obtain ⟨a, ha⟩ := hy
      refine ⟨e a, ?_⟩
      rw [← hyx, ← ha, powMonoidHom_apply, powMonoidHom_apply]
      exact (map_pow (e : A →* B) a p).symm
    · intro hx
      simp only [MonoidHom.mem_range] at hx
      obtain ⟨b, hb⟩ := hx
      refine ⟨e.symm (b ^ p), ⟨e.symm b, ?_⟩, ?_⟩
      · rw [powMonoidHom_apply]
        exact (map_pow (e.symm : B →* A) b p).symm
      · show e (e.symm (b ^ p)) = x
        rw [MulEquiv.apply_symm_apply, ← hb, powMonoidHom_apply]
  rw [← h]
  exact (Subgroup.index_map_equiv _ e).symm

end

theorem natCard_torsionSubgroup_quot_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    Nat.card (↥(NK.LocalInputs.PowerQuotient.torsionSubgroup 𝔭 p) ⧸
      (powMonoidHom p : ↥(NK.LocalInputs.PowerQuotient.torsionSubgroup 𝔭 p) →*
        ↥(NK.LocalInputs.PowerQuotient.torsionSubgroup 𝔭 p)).range) =
      p ^ NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) := by
  obtain ⟨N, hN⟩ := exists_powTorsion_exponent 𝔭 hp hres
  have hfield := natCard_powTorsion_quot_pow 𝔭 hp hres hN
  have hmap := map_torsionSubgroup_eq_closure (K := K) (𝔭 := 𝔭) hp
  have hiso := natCard_quot_powMonoidHom_eq_of_mulEquiv p
    (Subgroup.equivMapOfInjective (torsionSubgroup 𝔭 p) (coeUnit 𝔭) (coeUnit_injective 𝔭))
  rw [hiso, hmap]
  exact hfield

end NK.LocalInputs.PowerQuotient
