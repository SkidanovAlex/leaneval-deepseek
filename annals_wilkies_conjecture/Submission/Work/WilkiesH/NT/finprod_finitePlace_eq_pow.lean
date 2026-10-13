import Mathlib
import Submission.Work.WilkiesH.Norm.finprod_finitePlace_algEquiv
import Submission.Work.WilkiesH.Norm.finprod_finitePlace_max
import Submission.Work.WilkiesH.Norm.finprod_finitePlace_max_div
import Submission.Work.WilkiesH.Norm.finprod_finitePlace_self

/-!
# The finite part of the height is multiplicative in the extension degree

For a number field `K`, a subfield `F ≤ K` (as an `IntermediateField ℚ K`) and `z : F`, the
product over the finite places of `K` of `max (w z) 1` is the `[K : F]`-th power of the same
product over the finite places of `F`:

`∏ᶠ w : FinitePlace K, max (w (z : K)) 1 = (∏ᶠ v : FinitePlace F, max (v z) 1) ^ [K : F]`.

The proof is by the ideal-norm description of the finite part of the height (the lemmas
`Work.WilkiesH.Norm.finprod_finitePlace_max_div`, `finprod_finitePlace_self` and
`finprod_finitePlace_max`): writing `z = a / b` with `a b : 𝓞 F`,

`(∏ᶠ v, max (v z) 1) * absNorm_F (a, b) = absNorm_F (b)`   and
`(∏ᶠ w, max (w (z : K)) 1) * absNorm_K (a, b) = absNorm_K (b)`,

and the ideal `(a, b) 𝓞 K` of `𝓞 K` obtained by extending the ideal `(a, b)` of `𝓞 F` has
`absNorm_K = absNorm_F ^ [K : F]`
(`absNorm_map_algebraMap_pow_finrank`, from `Ideal.absNorm_relNorm` and
`Ideal.relNorm_algebraMap` together with `IsFractionRing.finrank_eq`). Cancelling the common
non-zero factor `absNorm_F (a, b) ^ [K : F]` gives the claim.
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilkiesH.NT

open NumberField

/-- For `x = a / b` with `a b : 𝓞 K`, `b ≠ 0`, the product over the finite places of
`max (v x) 1`, multiplied by the norm of the ideal `(a, b)`, is the norm of the ideal `(b)`.
Equivalently `∏ᶠ v, max (v x) 1 = absNorm (b) / absNorm (a, b)`.

This is the public form of the private helper of the same name used in
`Submission/Work/WilkiesH/Norm/finprod_finitePlace_algEquiv.lean`; it is restated here so that
the present file does not depend on the privacy of that declaration. -/
theorem finprod_finitePlace_max_mul_absNorm {K : Type*} [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) {a b : 𝓞 K} (hb : b ≠ 0) (hab : (a : K) = (b : K) * x) :
    (∏ᶠ v : FinitePlace K, max (v x) 1)
      * (Ideal.absNorm (Ideal.span ({a, b} : Set (𝓞 K))) : ℝ)
      = (Ideal.absNorm (Ideal.span ({b} : Set (𝓞 K))) : ℝ) := by
  have hdiv := Work.WilkiesH.Norm.finprod_finitePlace_max_div hx hb hab
  have hself := Work.WilkiesH.Norm.finprod_finitePlace_self (K := K) hb
  have hmax := Work.WilkiesH.Norm.finprod_finitePlace_max (K := K) (a := a) (b := b) hb
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

/-- The absolute norm of an ideal extended along `𝓞 F → 𝓞 K` is the `[K : F]`-th power of the
absolute norm: for `F ≤ K` a subfield of the number field `K` and `I : Ideal (𝓞 F)`,

`absNorm_K (I · 𝓞 K) = absNorm_F I ^ [K : F]`.

This is the relative-norm computation `absNorm (relNorm I) = absNorm I` combined with
`relNorm (I · 𝓞 K) = I ^ [𝓞 K : 𝓞 F]` and `Module.finrank (𝓞 F) (𝓞 K) = [K : F]`. -/
theorem absNorm_map_algebraMap_pow_finrank {K : Type*} [Field K] [NumberField K]
    (F : IntermediateField ℚ K) (I : Ideal (𝓞 ↥F)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 ↥F) (𝓞 K))) = (Ideal.absNorm I) ^ Module.finrank ↥F K := by
  rw [IsFractionRing.finrank_eq (𝓞 ↥F) ↥F (𝓞 K) K,
    ← Ideal.absNorm_relNorm (𝓞 ↥F) (𝓞 K), Ideal.relNorm_algebraMap (𝓞 K) I]
  simp only [Ideal.absNorm_apply]
  induction Module.finrank (𝓞 ↥F) (𝓞 K) with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', cardQuot_mul, ih]

theorem finprod_finitePlace_eq_pow {K : Type*} [Field K] [NumberField K]
    (F : IntermediateField ℚ K) (z : ↥F) :
    (∏ᶠ w : NumberField.FinitePlace K, max (w (z : K)) 1)
      = (∏ᶠ v : NumberField.FinitePlace ↥F, max (v z) 1) ^ Module.finrank ↥F K := by
  classical
  by_cases hz0 : z = 0
  · subst hz0
    simp
  obtain ⟨a, b, hb_mem, hdiv⟩ := IsFractionRing.div_surjective (𝓞 ↥F) z
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_mem
  have hbF : (b : ↥F) ≠ 0 := fun h => hb (Subtype.ext h)
  have hab : (a : ↥F) = (b : ↥F) * z := by
    rw [← hdiv, mul_comm, div_mul_cancel₀ _ hbF]
  have hzK : (z : K) ≠ 0 := fun h => hz0 (Subtype.ext (by simpa using h))
  -- the identity over the subfield `F`
  have hF := finprod_finitePlace_max_mul_absNorm (K := ↥F) hz0 hb hab
  -- its counterpart over `K`, for the extended pair `(a, b)`
  have hbK : algebraMap (𝓞 ↥F) (𝓞 K) b ≠ 0 := fun h =>
    hb (RingOfIntegers.algebraMap.injective ↥F K (by simpa using h))
  have habK : (algebraMap (𝓞 ↥F) (𝓞 K) a : K)
      = (algebraMap (𝓞 ↥F) (𝓞 K) b : K) * (z : K) := by
    have h1 : ((algebraMap (𝓞 ↥F) (𝓞 K) a : 𝓞 K) : K) = algebraMap ↥F K (a : ↥F) :=
      RingOfIntegers.mapRingHom_apply (algebraMap ↥F K) a
    have h2 : ((algebraMap (𝓞 ↥F) (𝓞 K) b : 𝓞 K) : K) = algebraMap ↥F K (b : ↥F) :=
      RingOfIntegers.mapRingHom_apply (algebraMap ↥F K) b
    have h3 : (z : K) = algebraMap ↥F K z := rfl
    rw [h1, h2, h3, ← map_mul, hab]
  have hK := finprod_finitePlace_max_mul_absNorm (K := K) hzK hbK habK
  -- the ideals `(a, b)` and `(b)` of `𝓞 K` are the extensions of those of `𝓞 F`
  have hspan2 : Ideal.span ({algebraMap (𝓞 ↥F) (𝓞 K) a, algebraMap (𝓞 ↥F) (𝓞 K) b} : Set (𝓞 K))
      = (Ideal.span ({a, b} : Set (𝓞 ↥F))).map (algebraMap (𝓞 ↥F) (𝓞 K)) := by
    rw [Ideal.map_span]
    congr 1
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro (h | h)
      · exact ⟨a, Or.inl rfl, h.symm⟩
      · exact ⟨b, Or.inr rfl, h.symm⟩
    · rintro ⟨c, (rfl | rfl), hc⟩
      · exact Or.inl hc.symm
      · exact Or.inr hc.symm
  have hspanb : Ideal.span ({algebraMap (𝓞 ↥F) (𝓞 K) b} : Set (𝓞 K))
      = (Ideal.span ({b} : Set (𝓞 ↥F))).map (algebraMap (𝓞 ↥F) (𝓞 K)) := by
    rw [Ideal.map_span]
    congr 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro rfl
      exact ⟨b, rfl, rfl⟩
    · rintro ⟨c, rfl, hc⟩
      exact hc.symm
  -- the common factor `absNorm_F (a, b) ^ [K : F]` is non-zero
  have hX0 : (Ideal.absNorm (Ideal.span ({a, b} : Set (𝓞 ↥F))) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h
    rw [Ideal.absNorm_eq_zero_iff] at h
    have hmem : b ∈ Ideal.span ({a, b} : Set (𝓞 ↥F)) := Ideal.subset_span (by simp)
    rw [h] at hmem
    exact hb (by simpa using hmem)
  -- rewrite the `K`-identity in terms of the `F`-quantities
  have hKn : (∏ᶠ w : FinitePlace K, max (w (z : K)) 1)
      * (Ideal.absNorm (Ideal.span ({a, b} : Set (𝓞 ↥F))) : ℝ) ^ Module.finrank ↥F K
      = (Ideal.absNorm (Ideal.span ({b} : Set (𝓞 ↥F))) : ℝ) ^ Module.finrank ↥F K := by
    have h := hK
    rw [hspan2, absNorm_map_algebraMap_pow_finrank (K := K) F, Nat.cast_pow] at h
    rw [hspanb, absNorm_map_algebraMap_pow_finrank (K := K) F, Nat.cast_pow] at h
    exact h
  rw [← hF, mul_pow] at hKn
  exact mul_right_cancel₀ (pow_ne_zero _ hX0) hKn

end Work.WilkiesH.NT
