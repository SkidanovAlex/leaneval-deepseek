import Mathlib
import Submission.Work.SSGRoute.PT.decompK_linked
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **At a place of `K` with trivial decomposition group the prime must be `2`.**

Hypotheses: `ζ` is a primitive `p`-th root of unity lying in `K` (this is the `hζK` of the whole
`pt_selmer_relaxed` cone), `c` is a nontrivial involution of `Gal(Ω/k)`, `φ : Ω →+* ℂ` is the seam
(`φ (c x) = conj (φ x)`), `w = mk (φ|_K)`, and `decompK w = ⊥` (the place is real / split).

Conclusion: `p = 2`.

Proof: `decompK_linked` turns `decompK w = ⊥` into `(zpowers c).map (res k K) = ⊥`, whence
`res k K c = 1`, i.e. `c` fixes `K` pointwise; so `c ζ = ζ`.  The seam then gives
`φ ζ = conj (φ ζ)`, i.e. `φ ζ ∈ ℝ`.  But `φ ζ` is a primitive `p`-th root of unity in `ℂ` (a field
homomorphism is injective, and `ℂ` has characteristic zero), and the only primitive `p`-th root of
unity that is real is `-1`, which is primitive exactly for `p = 2`.

Useful inputs already on disk: `Work.SSGRoute.ArchDictionary.res_eq_one_of_decompK_eq_bot`
(`ArchDictionary/archimedeanDictSplitPlace.lean:20`, proved, with no admitted steps) is exactly the
first step,
and `phi_mem_real_of_fixed` in the same file gives `(φ z).im = 0` when `c z = z`; only the
root-of-unity classification is genuinely new (`IsPrimitiveRoot.map_of_injective`,
`Complex.ext_iff`, `IsPrimitiveRoot.eq_orderOf`, `orderOf_neg_one`).

Consequence (the intended use): for odd `p` the split-place hypotheses
(`ArchDictionary.archimedeanDictSplitPlace`, i.e. `archimedeanDictionaryCanon` with
`decompK w = ⊥`) are *inconsistent*, so the split case of the archimedean dictionary only has
content at `p = 2`; there one may assume `2 • e = 0` on the coefficient module `E`. -/
theorem prime_eq_two_of_decompK_eq_bot
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥) :
    p = 2 := by
  -- Step 1: the decomposition group of the linked place is `⟨res c⟩`, so `c` acts trivially on `K`.
  have hlinked := decompK_linked k Ω K c hc2 hc1 φ hlink
  rw [hw] at hbot
  rw [hlinked] at hbot
  have hres : SSGRoute.res k K c = 1 := by
    have hmem : SSGRoute.res k K c ∈ (Subgroup.zpowers c).map (SSGRoute.res k K) :=
      ⟨c, Subgroup.mem_zpowers c, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  -- Step 2: `c` fixes `ζ`.
  have hfix : c ζ = ζ := by
    have h2 : (SSGRoute.res k K c) (⟨ζ, hζK⟩ : K) = ⟨ζ, hζK⟩ := by
      rw [hres]; rfl
    have h3 : ((SSGRoute.res k K c) (⟨ζ, hζK⟩ : K) : Ω) = c ζ :=
      AlgEquiv.restrictNormalHom_apply K c ⟨ζ, hζK⟩
    rw [h2] at h3
    simpa using h3.symm
  -- Step 3: the seam makes `φ ζ` real.
  have hζim : (φ ζ).im = 0 := by
    have h : starRingEnd ℂ (φ ζ) = φ ζ := by rw [← hlink ζ, hfix]
    have h2 : -(φ ζ).im = (φ ζ).im := by
      simpa [Complex.conj_im] using congrArg Complex.im h
    linarith
  have hzreal : φ ζ = ((φ ζ).re : ℂ) := by
    refine Complex.ext ?_ ?_
    · simp
    · simpa using hζim
  -- Step 4: `φ ζ` is a primitive `p`-th root of unity, and it is a real number.
  have hprim : IsPrimitiveRoot (φ ζ) p := hζ.map_of_injective (f := φ) (RingHom.injective φ)
  have hpne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hzp : ((φ ζ).re) ^ p = 1 := by
    apply Complex.ofReal_injective
    have hpow : ((φ ζ).re : ℂ) ^ p = 1 := by
      rw [← hzreal]; exact hprim.pow_eq_one
    calc ((↑(((φ ζ).re) ^ p)) : ℂ) = ((φ ζ).re : ℂ) ^ p := Complex.ofReal_pow _ _
      _ = 1 := hpow
      _ = ((1 : ℝ) : ℂ) := Complex.ofReal_one.symm
  -- Step 5: a real number whose `p`-th power is `1` (with `p` prime) is `±1`; `1` is excluded by
  -- primitivity, and `-1` forces `p = 2`.
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  rcases (pow_eq_one_iff_of_ne_zero (a := (φ ζ).re) (n := p) hpne).mp hzp with h1 | ⟨h1, heven⟩
  · exact absurd (by rw [hzreal, h1]; simp) (hprim.ne_one hp1)
  · exact (Nat.Prime.even_iff (Fact.out : p.Prime)).mp heven

end Work.SSGRoute.PT
