import Mathlib
import Submission.Work.SSGRoute.N2v2.kummerSplit_of_hsplit
import Submission.Work.SSGRoute.step4_y_escape_v2.localFactor_productFormula_clean
import Submission.Work.SSG8Escape.localField_not_real_of_no_involutions
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.N2v2

open NK.GlobalCFT

/-! ### Divisibility of the units of an archimedean local field

At an archimedean place the local field is either `ℝ` or `ℂ`, and the prime-`2` correction of
Shafarevich's theorem rules out the real case; what is left is `ℂ`, whose unit group is divisible.
The two small facts recorded here make this usable: `ℂˣ` is rootable by `ℕ`, hence so is the unit
group of any field ring-isomorphic to `ℂ`, and any monoid homomorphism from a `ℕ`-rootable monoid
to a *finite* group is trivial. -/

/-- Every nonzero complex number has an `n`-th root for every `n > 0`; equivalently `ℂˣ` is
rootable by `ℕ`. -/
noncomputable def rootableBy_units_complex : RootableBy ℂˣ ℕ :=
  rootableByOfPowLeftSurj ℂˣ ℕ fun {n} hn x => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact Units.ne_zero x hz.symm
    exact ⟨Units.mk0 z hz0, by ext; simpa using hz⟩

/-- A field ring-isomorphic to `ℂ` has rootable unit group. -/
noncomputable def rootableBy_units_of_ringEquiv_complex {R : Type*} [Field R] (e : R ≃+* ℂ) :
    RootableBy Rˣ ℕ := by
  haveI : RootableBy ℂˣ ℕ := rootableBy_units_complex
  exact Function.Surjective.rootableBy
    ((Units.mapEquiv e.toMulEquiv).symm : ℂˣ →* Rˣ)
    (Units.mapEquiv e.toMulEquiv).symm.surjective
    (fun a n => map_pow _ a n)

/-- A monoid homomorphism from an `ℕ`-rootable monoid to a finite group is trivial: if `a = z ^ n`
with `n` the order of the finite group, then `f a = f z ^ n = 1`. -/
theorem MonoidHom.eq_one_of_rootableBy_finite {A : Type*} [Monoid A] [RootableBy A ℕ]
    {G : Type*} [Group G] [Fintype G] (f : A →* G) (a : A) : f a = 1 := by
  obtain ⟨z, hz⟩ := RootableBy.surjective_pow A ℕ (n := Fintype.card G)
    Fintype.card_ne_zero a
  rw [← hz, map_pow, pow_card_eq_one]

/-- **The archimedean local factors of the Artin family are killed by a Kummer character.**

Let `χ` be the descent to `Gal(M/↥K)` of the Kummer character `χ_c` of an element `c ∈ Kˣ` whose
Kummer field lies in `M` (`Work.SSGRoute.N2v2.exists_kummerChar_level`, proved), let `v` be an
*archimedean* place of `↥K` (`hv` says `v` is not a finite place), and let `θ_v : K_vˣ →* Gal(M/↥K)`
be any local Artin factor of `M/↥K` with kernel the local norm subgroup (`hker`, as supplied by
`localFactor_productFormula_clean`).  Then `(χ (θ_v u)).toAdd = 0` for every `u ∈ K_vˣ`.

This is the archimedean hypothesis `hχarch` of `N2v2/char_eq_neg_localSum`.  The *short* proof uses
the already-proved `Work.SSG8Escape.localField_not_real_of_no_involutions`: for every archimedean
place `v`, `K_v` has no ring homomorphism to `ℝ` (for odd `p` because `K` contains a primitive odd
`p`-th root of unity; for `p = 2` because a real place of `K` would give a nontrivial involution of
`Gal(Ω/↥K)` with square `1`, contradicting `hKimag`).  Hence `K_v ≃ ℂ`, so `K_vˣ` is a divisible
group, and any homomorphism from a divisible group to the *finite* group `Gal(M/↥K)` is trivial:
`θ_v u = θ_v (zⁿ) = 1` for `zⁿ = u`.  Therefore `χ (θ_v u) = 1` and the `toAdd` is `0`.

(Equivalently, by the case analysis: at a complex `v` the local norm is onto so `localNormSubgroup
v = ⊤` and `θ_v u = 1` by `hker`; at a real `v` the norm is `z ↦ |z|²`, whose range contains `u²`,
so `(θ_v u)² = 1` and then `2 · χ_c σ = χ_c (σ²) = 0` for a lift `σ` of `θ_v u` -- `σ²` lying in
`M.fixingSubgroup` -- giving `χ_c σ = 0` for odd `p`.  The archimedean machinery is in
`Submission/NK/CFTLib/IdeleHasse/localGlobalArtinMap_exists.lean`.) -/
theorem kummerChar_archimedean (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    (c : (↥K)ˣ) (hc : NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ M)
    (χ : (↥M ≃ₐ[↥K] ↥M) →* Multiplicative (ZMod p))
    (hχ : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ) =
        Multiplicative.ofAdd
          (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ))
    (v : NK.GlobalCFT.Place ↥K) (hv : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      v ≠ NK.GlobalCFT.Place.ofFinite 𝔮)
    (θv : (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥M ≃ₐ[↥K] ↥M))
    (hker : θv.ker = NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥M) v)
    (u : (NK.GlobalCFT.Place.localField ↥K v)ˣ) :
    (χ (θv u)).toAdd = 0 := by
  -- `v` is archimedean: it is not a finite place.
  have hvinf : ¬ v.IsFinite := by
    intro h
    obtain ⟨q, hq⟩ := NK.GlobalCFT.Place.isFinite_iff.mp h
    exact hv q hq
  -- at such a place the local field has no ring homomorphism to `ℝ`
  have hnotreal := Work.SSG8Escape.localField_not_real_of_no_involutions
    p K ζ hζ hKimag v hvinf
  cases v with
  | inr q =>
    -- impossible: `v` would be a finite place, contradicting `hv`
    exact absurd (NK.GlobalCFT.Place.isFinite_ofFinite q) hvinf
  | inl w =>
    -- so the local field is `ℂ`, hence its unit group is rootable by `ℕ`
    have hC : NumberField.InfinitePlace.IsComplex w := by
      rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
      intro hR
      exact hnotreal
        ⟨(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hR).toRingHom, trivial⟩
    haveI : RootableBy (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofInfinite w))ˣ ℕ :=
      rootableBy_units_of_ringEquiv_complex
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC)
    -- `Gal(M/K)` is finite, so `θv` is trivial
    have h1 : θv u = 1 := MonoidHom.eq_one_of_rootableBy_finite θv u
    rw [h1, map_one]
    simp

end Work.SSGRoute.N2v2
