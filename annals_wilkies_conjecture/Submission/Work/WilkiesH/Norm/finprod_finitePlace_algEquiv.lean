import Mathlib
import Submission.Work.WilkiesH.Norm.absNorm_map_ringEquiv
import Submission.Work.WilkiesH.Norm.finprod_finitePlace_self
import Submission.Work.WilkiesH.Norm.finprod_finitePlace_max
import Submission.Work.WilkiesH.Norm.finprod_finitePlace_max_div

/-!
# The finite part of the height is invariant under `ℚ`-algebra isomorphisms

For a number field `K` and `x : K`, the product `∏ᶠ v, max (v x) 1` over the finite places of `K`
equals `absNorm (span {b}) / absNorm (span {a, b})` for any presentation `x = a / b` with
`a b : 𝓞 K`, `b ≠ 0`: the family of finite places is recovered from `v a` and `v b`, whereas the
absolute norms of the ideals `(a, b)` and `(b)` are transported by any ring isomorphism of rings of
integers.  Consequently the product is invariant under `ℚ`-algebra isomorphisms of number fields,
which is the statement proved here.
-/

open scoped NumberField

namespace Work.WilkiesH.Norm

open NumberField

/-- For `x = a / b` with `a b : 𝓞 K`, `b ≠ 0`, the product over the finite places of
`max (v x) 1`, multiplied by the norm of the ideal `(a, b)`, is the norm of the ideal `(b)`.
Equivalently `∏ᶠ v, max (v x) 1 = absNorm (b) / absNorm (a, b)`. -/
private theorem finprod_finitePlace_max_mul_absNorm {K : Type*} [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) {a b : 𝓞 K} (hb : b ≠ 0) (hab : (a : K) = (b : K) * x) :
    (∏ᶠ v : FinitePlace K, max (v x) 1)
      * (Ideal.absNorm (Ideal.span ({a, b} : Set (𝓞 K))) : ℝ)
      = (Ideal.absNorm (Ideal.span ({b} : Set (𝓞 K))) : ℝ) := by
  have hdiv := finprod_finitePlace_max_div hx hb hab
  have hself := finprod_finitePlace_self (K := K) hb
  have hmax := finprod_finitePlace_max (K := K) (a := a) (b := b) hb
  have hPb : (∏ᶠ v : FinitePlace K, v (b : K)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hself
    exact one_ne_zero hself.symm
  have hY : (∏ᶠ v : FinitePlace K, max (v x) 1) * (∏ᶠ v : FinitePlace K, v (b : K))
      = ∏ᶠ v : FinitePlace K, max (v (a : K)) (v (b : K)) := by
    rw [hdiv]
    exact div_mul_cancel₀ _ hPb
  have h1 : ((∏ᶠ v : FinitePlace K, max (v x) 1)
        * (Ideal.absNorm (Ideal.span ({a, b} : Set (𝓞 K))) : ℝ))
      * (∏ᶠ v : FinitePlace K, v (b : K)) = 1 := by
    rw [mul_assoc, mul_comm (Ideal.absNorm (Ideal.span ({a, b} : Set (𝓞 K))) : ℝ)
        (∏ᶠ v : FinitePlace K, v (b : K)), ← mul_assoc, hY, hmax]
  have h2 : (Ideal.absNorm (Ideal.span ({b} : Set (𝓞 K))) : ℝ)
      * (∏ᶠ v : FinitePlace K, v (b : K)) = 1 := by
    rw [mul_comm]
    exact hself
  exact mul_right_cancel₀ hPb (h1.trans h2.symm)

theorem finprod_finitePlace_algEquiv {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃ₐ[ℚ] L) (x : K) :
    (∏ᶠ v : NumberField.FinitePlace L, max (v (e x)) 1)
      = ∏ᶠ v : NumberField.FinitePlace K, max (v x) 1 := by
  by_cases hx : x = 0
  · rw [hx]
    simp
  obtain ⟨a, b, hb_mem, hdiv⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_mem
  have hbK : (b : K) ≠ 0 := fun h =>
    hb (IsFractionRing.injective (𝓞 K) K (by simpa using h))
  have hab : (a : K) = (b : K) * x := by rw [← hdiv, mul_comm, div_mul_cancel₀ _ hbK]
  have hK := finprod_finitePlace_max_mul_absNorm hx hb hab
  -- transfer to `L` along the induced isomorphism of rings of integers
  let f : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e.toRingEquiv
  have hfa : ((f a : 𝓞 L) : L) = e (a : K) :=
    RingOfIntegers.mapRingEquiv_apply e.toRingEquiv a
  have hfb : ((f b : 𝓞 L) : L) = e (b : K) :=
    RingOfIntegers.mapRingEquiv_apply e.toRingEquiv b
  have hfb_ne : f b ≠ 0 := fun h => hb (f.injective (by simpa using h))
  have hex : e x ≠ 0 := fun h => hx (e.injective (by simpa using h))
  have hfab : ((f a : 𝓞 L) : L) = ((f b : 𝓞 L) : L) * e x := by
    rw [hfa, hfb, hab, map_mul]
  have hL := finprod_finitePlace_max_mul_absNorm hex hfb_ne hfab
  -- the sets of images of the pairs of generators
  have hsetA : ({f a, f b} : Set (𝓞 L)) = (f : 𝓞 K →+* 𝓞 L) '' ({a, b} : Set (𝓞 K)) := by
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro (h | h)
      · exact ⟨a, Or.inl rfl, h.symm⟩
      · exact ⟨b, Or.inr rfl, h.symm⟩
    · rintro ⟨z, (rfl | rfl), hz⟩
      · exact Or.inl hz.symm
      · exact Or.inr hz.symm
  have hsetB : ({f b} : Set (𝓞 L)) = (f : 𝓞 K →+* 𝓞 L) '' ({b} : Set (𝓞 K)) := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro rfl
      exact ⟨b, rfl, rfl⟩
    · rintro ⟨z, rfl, hz⟩
      exact hz.symm
  -- the absolute norms of the two ideals agree with those on the `K` side
  have hmapA : Ideal.span ({f a, f b} : Set (𝓞 L))
      = (Ideal.span ({a, b} : Set (𝓞 K))).map (f : 𝓞 K →+* 𝓞 L) := by
    rw [Ideal.map_span, hsetA]
  have hmapB : Ideal.span ({f b} : Set (𝓞 L))
      = (Ideal.span ({b} : Set (𝓞 K))).map (f : 𝓞 K →+* 𝓞 L) := by
    rw [Ideal.map_span, hsetB]
  have hA : (Ideal.absNorm (Ideal.span ({f a, f b} : Set (𝓞 L))) : ℝ)
      = (Ideal.absNorm (Ideal.span ({a, b} : Set (𝓞 K))) : ℝ) := by
    rw [hmapA, absNorm_map_ringEquiv f (Ideal.span ({a, b} : Set (𝓞 K)))]
  have hB : (Ideal.absNorm (Ideal.span ({f b} : Set (𝓞 L))) : ℝ)
      = (Ideal.absNorm (Ideal.span ({b} : Set (𝓞 K))) : ℝ) := by
    rw [hmapB, absNorm_map_ringEquiv f (Ideal.span ({b} : Set (𝓞 K)))]
  have hA0 : (Ideal.absNorm (Ideal.span ({a, b} : Set (𝓞 K))) : ℝ) ≠ 0 := by
    have hne : Ideal.span ({a, b} : Set (𝓞 K)) ≠ ⊥ := by
      intro h
      have hmem : b ∈ Ideal.span ({a, b} : Set (𝓞 K)) := Ideal.subset_span (by simp)
      rw [h] at hmem
      exact hb (by simpa using hmem)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hne)
  rw [hA, hB] at hL
  rw [← hL] at hK
  exact (mul_right_cancel₀ hA0 hK).symm

end Work.WilkiesH.Norm
