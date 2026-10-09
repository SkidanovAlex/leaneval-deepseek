import Mathlib
import Submission.Work.SSGRoute.local_lifting_setup
import Submission.Work.SSGRoute.finite_card_residueField_comap_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The residue field of a finite place of an algebraic closure over a number field

Let `k` be a number field and `Ω` an algebraic closure of `k`.  For a finite place `A` of `Ω` over
`k` (a valuation subring whose restriction to `k` is proper) the residue field `κ` of `A` is an
algebraic closure of the residue field `𝔽_p` of the prime of `k` below `A`, so every element of `κ`
is either `0` or a root of unity of order prime to `p = char κ`:

`Work.SSGRoute.residueField_residue_pow_eq_one_gen`.

The proof follows the same scheme as in the case `k = ℚ`
(`Work.SSGRoute.residueField_residue_pow_eq_one`): for `a : ↥A` put `L = k⟮a⟯`, a finite extension
of `k`, and `B = A ∩ L`; the residue class of `a` in `κ_B = κ(B)` is the image of the residue
class of `a` in `κ`, and by linear independence of lifts
(`NK.RamificationAudit.exists_monic_aeval_eq_zero_natDegree_le`) it is integral over the residue
field `F₀` of `B ∩ k`, which is the finite field `𝓞 k ⧸ 𝔭` (`𝔭 = primeOf A hA`).  Any nonzero
element of a field extension integral over a finite field is a root of unity of order prime to the
characteristic (`Work.SSGRoute.pow_exists_eq_one_of_isIntegral_finiteField_base`).

The only point where the present development is more general than the `ℚ`-case is that the base
field `F₀` is now *any* finite field (of cardinality `p ^ f`), whence the auxiliary lemma
`pow_exists_eq_one_of_isIntegral_finiteField_base` is stated with the characteristic `p` of the
ambient field rather than with the cardinality of the base field.
-/

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-- **A nonzero element of a field extension integral over a finite field is a root of unity whose
order is prime to the characteristic.**

Let `F ⊆ K` be fields with `F` finite and `K` of characteristic `p`, and let `x ∈ K` be nonzero and
integral over `F`.  Then `x ^ N = 1` for some `N > 0` not divisible by `p`.

Indeed, `F` is a finite field, hence has `p ^ n` elements with `n ≥ 1`; the subfield `F⟮x⟯` is a
finite extension of `F` of cardinality `p ^ (n · [F⟮x⟯ : F])`, so `x` is killed by the order
`p ^ (n · [F⟮x⟯ : F]) - 1` of the multiplicative group of `F⟮x⟯`, a number prime to `p`. -/
theorem pow_exists_eq_one_of_isIntegral_finiteField_base
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F]
    (p : ℕ) [CharP K p] {x : K} (hx : x ≠ 0) (hint : IsIntegral F x) :
    ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ x ^ N = 1 := by
  haveI : Fintype F := Fintype.ofFinite F
  -- The characteristic of the subfield `F` is `p` as well.
  have hcharF : CharP F p := RingHom.charP (algebraMap F K) (algebraMap F K).injective p
  haveI := hcharF
  -- `F` is a finite field with `p ^ n` elements, `p` prime.
  obtain ⟨n, hpprime, hcardF⟩ := FiniteField.card F p
  have hcardFn : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcardF]
  -- The subextension `E = F⟮x⟯` is finite over `F`, hence finite.
  set E : IntermediateField F K := IntermediateField.adjoin F ({x} : Set K) with hE
  have hxmem : x ∈ E := by
    rw [hE]; exact IntermediateField.subset_adjoin F {x} (Set.mem_singleton x)
  have hfd : FiniteDimensional F E := by
    rw [hE]
    exact IntermediateField.finiteDimensional_adjoin (S := {x})
      (fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hint)
  haveI : Module.Finite F E := hfd
  haveI : Finite E := Module.finite_of_finite F
  haveI : Fintype E := Fintype.ofFinite E
  -- Its cardinality is `p ^ (n · [E : F])`.
  have hcardE : Nat.card E = p ^ ((n : ℕ) * Module.finrank F E) := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := E), hcardFn, ← pow_mul]
  have hcardE2 : 2 ≤ Nat.card E := by
    have : 1 < Fintype.card E := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]; omega
  have hexp : 1 ≤ (n : ℕ) * Module.finrank F E := by
    rcases Nat.eq_zero_or_pos ((n : ℕ) * Module.finrank F E) with h | h
    · exfalso; rw [h, pow_zero] at hcardE; omega
    · exact h
  refine ⟨Nat.card E - 1, ?_, ?_, ?_⟩
  · omega
  · -- `p ∤ p ^ (n · [E : F]) - 1`.
    rw [hcardE]
    intro hdvd
    have hdvd' : p ∣ p ^ ((n : ℕ) * Module.finrank F E) := dvd_pow_self p (by omega)
    have h1 : p ∣ 1 := by
      have := Nat.dvd_sub hdvd' hdvd
      rwa [Nat.sub_sub_self
        (Nat.one_le_pow ((n : ℕ) * Module.finrank F E) p hpprime.pos)] at this
    exact hpprime.not_dvd_one h1
  · -- Lagrange in `Eˣ`.
    have hN : Nat.card Eˣ = Nat.card E - 1 := Nat.card_units E
    rw [← hN]
    have hxe : (⟨x, hxmem⟩ : E) ≠ 0 := by intro h; exact hx (congrArg Subtype.val h)
    let ye : Eˣ := Units.mk0 (⟨x, hxmem⟩ : E) hxe
    have hpow : ye ^ Nat.card Eˣ = 1 := pow_card_eq_one'
    have hE' : ((ye : E) ^ Nat.card Eˣ : E) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
    have hye : (ye : E) = ⟨x, hxmem⟩ := Units.val_mk0 hxe
    rw [hye] at hE'
    have := congrArg (fun z : E => (z : K)) hE'
    rw [IntermediateField.coe_pow, IntermediateField.coe_one] at this
    rwa [show ((⟨x, hxmem⟩ : E) : K) = x from rfl] at this

/-- **The residue field of the prime of `k` below a place, pulled back to the bottom subfield of a
finite level, is finite and of the residue cardinality `#(𝓞 k ⧸ 𝔭)`.**

General form of `Work.SSGRoute.finite_card_residueField_comap_bot` from `ℚ` to an arbitrary number
field `k`: for a place `A` of `Ω` over the finite prime `𝔭 = primeOf A hA` of `k` and a finite
intermediate field `L/k`, the residue field of `(A ∩ L) ∩ k ⊆ L` is finite, with `Nat.card` equal
to `#(𝓞 k ⧸ 𝔭)`; in particular it is the finite field `𝔽_p` when `p` is the residue
characteristic. -/
theorem finite_card_residueField_comap_bot_gen
    {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : A.comap (algebraMap k Ω) ≠ ⊤)
    (L : IntermediateField k Ω) [FiniteDimensional k L] :
    Finite (IsLocalRing.ResidueField
      ↥((A.comap (algebraMap ↥L Ω)).comap (algebraMap ↥(⊥ : IntermediateField k ↥L) ↥L))) ∧
    Nat.card (IsLocalRing.ResidueField
      ↥((A.comap (algebraMap ↥L Ω)).comap (algebraMap ↥(⊥ : IntermediateField k ↥L) ↥L)))
      = Nat.card (NumberField.RingOfIntegers k ⧸
          (Submission.NeukirchUchida.primeOf A hA).asIdeal) := by
  classical
  -- `primeOf` is stated for a separable closure; over a number field `k` (perfect, being of
  -- characteristic `0`) an algebraic closure is a separable closure.
  haveI : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  -- Pulling back to `⊥ ⊆ ↥L` (a copy of `k`) does not change the residue field.
  obtain ⟨e1⟩ := residueField_comap_bot_ringEquiv (F := k) (E := ↥L)
    (V := A.comap (algebraMap ↥L Ω))
  have hcomap : (A.comap (algebraMap ↥L Ω)).comap (algebraMap k ↥L)
      = A.comap (algebraMap k Ω) := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq k ↥L Ω]
  -- The place of `k` below `A` is a localisation at a height one prime.
  have hprime : A.comap (algebraMap k Ω)
      = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
          (Submission.NeukirchUchida.primeOf A hA) :=
    Submission.NeukirchUchida.primeOf_spec A hA
  obtain ⟨e2⟩ := residueField_valuationSubringAtPrime_ringEquiv (K := k)
    (Submission.NeukirchUchida.primeOf A hA)
  have e : IsLocalRing.ResidueField
        ↥((A.comap (algebraMap ↥L Ω)).comap
          (algebraMap ↥(⊥ : IntermediateField k ↥L) ↥L))
      ≃+* (NumberField.RingOfIntegers k ⧸
        (Submission.NeukirchUchida.primeOf A hA).asIdeal) :=
    ((hcomap.trans hprime) ▸ e1).trans e2
  refine ⟨?_, ?_⟩
  · haveI : Finite (NumberField.RingOfIntegers k ⧸
        (Submission.NeukirchUchida.primeOf A hA).asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum _
    exact Finite.of_equiv (NumberField.RingOfIntegers k ⧸
        (Submission.NeukirchUchida.primeOf A hA).asIdeal) e.symm
  · rw [Nat.card_congr e.toEquiv]

theorem residueField_residue_pow_eq_one_gen
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (p : ℕ)
    (hchar : CharP (IsLocalRing.ResidueField ↥A) p) (a : ↥A) :
    IsLocalRing.residue ↥A a = 0 ∨
      ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (IsLocalRing.residue ↥A a) ^ N = 1 := by
  by_cases hx : IsLocalRing.residue ↥A a = 0
  · exact Or.inl hx
  · right
    -- The finite level `L = k⟮a⟯` generated by `a`.
    let L : IntermediateField k Ω :=
      IntermediateField.adjoin k ({(a : Ω)} : Set Ω)
    haveI hLfd : FiniteDimensional k L :=
      IntermediateField.adjoin.finiteDimensional
        ((Algebra.IsAlgebraic.isAlgebraic (a : Ω)).isIntegral)
    -- The valuation ring `B = A ∩ L` of `L` and `a` as an element of it.
    let B : ValuationSubring ↥L := A.comap (algebraMap ↥L Ω)
    have haL : (a : Ω) ∈ L :=
      IntermediateField.mem_adjoin_simple_self k (a : Ω)
    let y : ↥B := ⟨⟨(a : Ω), haL⟩, by
      show algebraMap ↥L Ω ⟨(a : Ω), haL⟩ ∈ A
      simpa using a.2⟩
    have hcomapy : NK.RamificationAudit.comapToA A L y = a := by
      ext
      simp [y, NK.RamificationAudit.comapToA]
    -- `a` is a root of a monic polynomial over the residue field of `B ∩ k`.
    obtain ⟨f, hfmonic, _hfdeg, hf⟩ :=
      NK.RamificationAudit.exists_monic_aeval_eq_zero_natDegree_le (K := k) (L := ↥L)
        B (⊥ : IntermediateField k ↥L) (IsLocalRing.residue ↥B y)
    -- The map on residue fields induced by `B ⊆ A`, and the base field `F₀ = κ(B ∩ k)`.
    let ψ : IsLocalRing.ResidueField ↥B →+* IsLocalRing.ResidueField ↥A :=
      IsLocalRing.ResidueField.map (NK.RamificationAudit.comapToA A L)
    let F0 := IsLocalRing.ResidueField ↥(B.comap (algebraMap ↥(⊥ : IntermediateField k ↥L) ↥L))
    -- The residue class of `a` is the image of the residue class of `y`.
    have hxψ : ψ (IsLocalRing.residue ↥B y) = IsLocalRing.residue ↥A a := by
      rw [IsLocalRing.ResidueField.map_residue, hcomapy]
    have hzint : IsIntegral F0 (IsLocalRing.residue ↥B y) := ⟨f, hfmonic, hf⟩
    -- Give `κ` the `F₀`-algebra structure induced by `ψ`; the residue class of `a` is integral.
    letI : Algebra F0 (IsLocalRing.ResidueField ↥A) :=
      (ψ.comp (algebraMap F0 (IsLocalRing.ResidueField ↥B))).toAlgebra
    have hcompat : (algebraMap F0 (IsLocalRing.ResidueField ↥A)).comp (RingHom.id F0) =
        ψ.comp (algebraMap F0 (IsLocalRing.ResidueField ↥B)) := by
      ext z
      rfl
    have hint : IsIntegral F0 (IsLocalRing.residue ↥A a) := by
      rw [← hxψ]
      exact IsIntegral.map_of_comp_eq (RingHom.id F0) ψ hcompat hzint
    -- `F₀` is the finite field `𝓞 k ⧸ 𝔭`, and `κ` has characteristic `p`.
    obtain ⟨hFin, _hcard⟩ := finite_card_residueField_comap_bot_gen A hA L
    haveI : Finite F0 := hFin
    haveI : CharP (IsLocalRing.ResidueField ↥A) p := hchar
    exact pow_exists_eq_one_of_isIntegral_finiteField_base (F := F0) p hx hint

end Work.SSGRoute
