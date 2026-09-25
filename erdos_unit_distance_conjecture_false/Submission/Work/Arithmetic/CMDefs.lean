import Mathlib

/-!
# Setup for the class-group pigeonhole in a CM field

Vocabulary for the arithmetic step (`Proposition 2.2` of the paper): given a CM field `K`
with complex conjugation `c`, a family of prime ideals `P i` no two of which are conjugate,
and signs `ε : Fin m → Bool`, we form

* `ASet m P ε  = ∏ i, (if ε i then P i else conjI (P i))`,
* `ASet' m P ε = ∏ i, (if ε i then conjI (P i) else P i)  = conjI (ASet m P ε)`.

For a pair `x y : 𝓞 K` with `(x) * ASet ε = (y) * ASet η` we put
`uOf x y = (y * c x) / (x * c y) ∈ K`.
-/

namespace Work.Arithmetic

open scoped nonZeroDivisors
open NumberField

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsCMField K]

/-- Complex conjugation on the ring of integers `𝓞 K` of a CM field, as a ring homomorphism. -/
noncomputable abbrev conjR (K : Type*) [Field K] [NumberField K] [NumberField.IsCMField K] :
    𝓞 K →+* 𝓞 K :=
  (IsCMField.ringOfIntegersComplexConj K).toRingHom

/-- The image of an ideal of `𝓞 K` under complex conjugation. -/
noncomputable def conjI (I : Ideal (𝓞 K)) : Ideal (𝓞 K) := Ideal.map (conjR K) I

/-- `Ideal.map` of a finite product of ideals, for `RingHom`s. -/
lemma Ideal.map_prod' {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {ι : Type*} (s : Finset ι) (g : ι → Ideal R) :
    Ideal.map f (∏ i ∈ s, g i) = ∏ i ∈ s, Ideal.map f (g i) := by
  simp only [← Ideal.mapHom_apply]
  exact map_prod (Ideal.mapHom f) g s

lemma conjR_conjR (x : 𝓞 K) : conjR K (conjR K x) = x := by
  ext
  change IsCMField.complexConj K (IsCMField.complexConj K (x : K)) = (x : K)
  exact IsCMField.complexConj_apply_apply K _

lemma conjR_injective : Function.Injective (conjR K) := by
  intro x y hxy
  have := congrArg (conjR K) hxy
  simpa only [conjR_conjR] using this

lemma conjR_surjective : Function.Surjective (conjR K) := fun y => ⟨conjR K y, conjR_conjR y⟩

lemma conjR_natCast (n : ℕ) : conjR K (n : 𝓞 K) = (n : 𝓞 K) := map_natCast _ n

lemma conjR_comp_self : (conjR K).comp (conjR K) = RingHom.id (𝓞 K) := by
  ext x
  simp only [RingHom.comp_apply, RingHom.id_apply]
  exact congrArg Subtype.val (conjR_conjR x)

@[simp] lemma conjI_conjI (I : Ideal (𝓞 K)) : conjI (conjI I) = I := by
  rw [conjI, conjI, Ideal.map_map, conjR_comp_self, Ideal.map_id]

lemma conjI_mono : Monotone (conjI (K := K)) := fun _ _ h => Ideal.map_mono h

lemma conjI_prime {I : Ideal (𝓞 K)} (h : I.IsPrime) : (conjI I).IsPrime := by
  haveI := h
  rw [conjI]
  exact Ideal.map_isPrime_of_equiv (IsCMField.ringOfIntegersComplexConj K)

@[simp] lemma conjI_span_nat (p : ℕ) : conjI (Ideal.span {(p : 𝓞 K)}) = Ideal.span {(p : 𝓞 K)} := by
  rw [conjI, Ideal.map_span, Set.image_singleton, conjR_natCast]

lemma conjI_ne_bot {I : Ideal (𝓞 K)} (h : I ≠ ⊥) : conjI I ≠ ⊥ := by
  rw [conjI]
  intro hmap
  exact h ((Ideal.map_eq_bot_iff_of_injective conjR_injective).mp hmap)

@[simp] lemma conjI_mul (I J : Ideal (𝓞 K)) : conjI (I * J) = conjI I * conjI J := by
  rw [conjI, conjI, conjI, Ideal.map_mul]

lemma conjI_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Ideal (𝓞 K)) :
    conjI (∏ i ∈ s, f i) = ∏ i ∈ s, conjI (f i) := by
  rw [conjI, Ideal.map_prod']
  exact Finset.prod_congr rfl fun i _ => rfl

/-- `ASet m P ε = ∏ i, (if ε i then P i else conjI (P i))`. -/
noncomputable def ASet (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (ε : Fin m → Bool) : Ideal (𝓞 K) :=
  ∏ i, if ε i then P i else conjI (P i)

/-- `ASet' m P ε = ∏ i, (if ε i then conjI (P i) else P i)`. -/
noncomputable def ASet' (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (ε : Fin m → Bool) : Ideal (𝓞 K) :=
  ∏ i, if ε i then conjI (P i) else P i

lemma ASet_eq_prod (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (ε : Fin m → Bool) :
    ASet m P ε = ∏ i, if ε i then P i else conjI (P i) := rfl

lemma ASet'_eq_prod (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (ε : Fin m → Bool) :
    ASet' m P ε = ∏ i, if ε i then conjI (P i) else P i := rfl

lemma conjI_ASet (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (ε : Fin m → Bool) :
    conjI (ASet m P ε) = ASet' m P ε := by
  rw [ASet_eq_prod, ASet'_eq_prod, conjI, Ideal.map_prod']
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · simp only [conjI]; exact conjI_conjI (P i)

lemma ASet_mul_ASet' (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (ε : Fin m → Bool) :
    ASet m P ε * ASet' m P ε = ∏ i, (P i * conjI (P i)) := by
  rw [ASet_eq_prod, ASet'_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

lemma ASet_mul_ASet'_swap (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (ε η : Fin m → Bool) :
    ASet m P ε * ASet' m P η
      = ∏ i, ((if ε i then P i else conjI (P i)) * (if η i then conjI (P i) else P i)) := by
  rw [ASet_eq_prod, ASet'_eq_prod, ← Finset.prod_mul_distrib]

lemma ASet_ne_bot (m : ℕ) (P : Fin m → Ideal (𝓞 K)) (hPnb : ∀ i, P i ≠ ⊥)
    (ε : Fin m → Bool) : ASet m P ε ≠ ⊥ := by
  rw [ASet_eq_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  split_ifs with h
  · exact hPnb i
  · exact conjI_ne_bot (hPnb i)

/-- The element `u = (y * c x) / (x * c y) ∈ K` attached to a pair `x y : 𝓞 K`. -/
noncomputable def uOf (x y : 𝓞 K) : K :=
  (y : K) * IsCMField.complexConj K (x : K) / ((x : K) * IsCMField.complexConj K (y : K))

@[simp] lemma uOf_def (x y : 𝓞 K) :
    uOf x y
      = (y : K) * IsCMField.complexConj K (x : K) / ((x : K) * IsCMField.complexConj K (y : K)) :=
  rfl

end Work.Arithmetic
