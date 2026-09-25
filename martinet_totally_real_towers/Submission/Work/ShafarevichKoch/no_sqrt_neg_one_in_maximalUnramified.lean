import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.RelationBound
import Submission.Work.ClassFieldTower.int_coords_and_norm
import Submission.Work.ShafarevichKoch.exists_coords_even_of_sq_add_sq_mem_four
import Submission.Work.ShafarevichKoch.exists_two_mul_eq_of_mem_ringOfIntegers
import Submission.Work.ShafarevichKoch.minpoly_ringOfIntegers_adjoin_sq_eq_neg_one

/-!
# `-1` is not a square in the maximal unramified pro-`2` extension of `Kc`

For `Kc = ℚ(√-30030)` (`Work.ClassFieldTower.Kc`) and `M.K` the maximal unramified pro-`2`
extension of `Kc`, the element `-1` is not a square in `M.K`.

The mathematical content is that the quadratic extension `Kc(√-1)/Kc` is **ramified** at the prime
of `Kc` above `2`: `Kc(√-1) = ℚ(i, √-30030)` is a biquadratic field whose completion at `2` is
`ℚ₂(ζ₈)`, totally ramified of degree `4` over `ℚ₂`, while `Kc` is only ramified of degree `2`.

The proof given here is elementary and avoids local fields, discriminants of quartic fields and
ramification theory.  Put `x = √-1` and `L = Kc(x)`, so that `L ⊆ M.K` and `M.unramified` gives
`differentIdeal (𝓞 Kc) (𝓞 L) = ⊤`.  Then:

* for `b ∈ 𝓞 L` one has `2b = a + a' x` with `a a' ∈ 𝓞 Kc` and `a² + a'² = 4c` for an integral
  `c` (the trace/norm argument for a quadratic extension);
* writing `a = u + v√-30030`, `a' = u' + v'√-30030` with integers and applying the parity lemma
  (`4 ∣ u² + u'² - 30030(v² + v'²)`, `2 ∣ uv + u'v'`) shows that `u, u'` are even, whence
  `√-30030 · b ∈ 𝓞 Kc + 𝓞 Kc · x`: the element `√-30030` lies in the conductor
  `(𝓞 Kc[x] : 𝓞 L)`;
* the classical identity `(conductor) · (different) = (f'(x)) = (2x)` then forces
  `conductor = (2x)` if the different were trivial, i.e. `√-30030 ∈ (2x)`;
* but `√-30030 ∉ (2x)`: otherwise `((√-30030)/(2x))² = 30030/4 ∉ 𝓞 L`.
-/

namespace Work.ShafarevichKoch

open Work.ClassFieldTower
open scoped NumberField
open scoped IntermediateField
open NumberField Polynomial

noncomputable section

/-- **`-1` is not a square in `Kc = ℚ(√-30030)`.**

Since `{1, √-30030}` is a `ℚ`-basis of `Kc` with `(√-30030)² = -30030`, expanding
`(x + y√-30030)² = -1` gives `x² - 30030 y² = -1` and `2xy = 0`; the first branch is impossible
over `ℚ` and the second would make `30030` a rational square. -/
theorem neg_one_not_isSquare_Kc : ¬ ∃ w : Kc, w * w = -1 := by
  rintro ⟨w, hw⟩
  obtain ⟨x, y, hxy⟩ := exists_coords w
  rw [hxy] at hw
  have key : (algebraMap ℚ Kc x + algebraMap ℚ Kc y * sc)
        * (algebraMap ℚ Kc x + algebraMap ℚ Kc y * sc)
      = algebraMap ℚ Kc x * algebraMap ℚ Kc x + (algebraMap ℚ Kc x * algebraMap ℚ Kc y) * sc
        + (algebraMap ℚ Kc y * algebraMap ℚ Kc x) * sc
        + algebraMap ℚ Kc y * algebraMap ℚ Kc y * (sc * sc) := by ring
  have key2 : (algebraMap ℚ Kc x + algebraMap ℚ Kc y * sc)
        * (algebraMap ℚ Kc x + algebraMap ℚ Kc y * sc) + 1
      = algebraMap ℚ Kc (x ^ 2 - 30030 * y ^ 2 + 1) + algebraMap ℚ Kc (2 * x * y) * sc := by
    rw [key, sc_sq]
    push_cast
    simp only [map_ofNat]
    ring
  have h0 : algebraMap ℚ Kc (x ^ 2 - 30030 * y ^ 2 + 1)
      + algebraMap ℚ Kc (2 * x * y) * sc = 0 := by
    rw [← key2, hw]; ring
  have hz : (x ^ 2 - 30030 * y ^ 2 + 1 : ℚ) • (1 : Kc) + (2 * x * y : ℚ) • sc = 0 := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]; exact h0
  obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp linearIndependent_pair_one_sc)
      (x ^ 2 - 30030 * y ^ 2 + 1) (2 * x * y) hz
  have h1' : x ^ 2 - 30030 * y ^ 2 + 1 = 0 := h1
  have h2' : 2 * x * y = 0 := h2
  have hx_or_hy : x = 0 ∨ y = 0 := by
    rcases mul_eq_zero.mp h2' with h | h
    · left; exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact Or.inr h
  rcases hx_or_hy with hx0 | hy0
  · subst hx0
    have hyne : y ≠ 0 := by intro hy; rw [hy] at h1'; norm_num at h1'
    refine absurd (show IsSquare (30030 : ℚ) from ⟨y⁻¹, ?_⟩) (by norm_num)
    field_simp at h1' ⊢
    linarith
  · subst hy0
    nlinarith [sq_nonneg x]

/-- `z` with `z * z = -1` is integral over `Kc`. -/
theorem isIntegral_Kc_of_sq_eq_neg_one {M : MaximalUnramifiedProP.{0} Kc 2} {z : M.K}
    (hz : z * z = algebraMap Kc M.K (-1 : Kc)) : IsIntegral Kc z :=
  IsIntegral.of_pow (n := 2) (by norm_num) (by rw [pow_two, hz]; exact isIntegral_algebraMap)

/-- `z` with `z * z = -1` is integral over `ℤ`. -/
theorem isIntegral_int_of_sq_eq_neg_one {M : MaximalUnramifiedProP.{0} Kc 2} {z : M.K}
    (hz : z * z = algebraMap Kc M.K (-1 : Kc)) : IsIntegral ℤ z :=
  IsIntegral.of_pow (n := 2) (by norm_num) (by
    rw [pow_two, hz]
    have h1 : algebraMap Kc M.K (-1 : Kc) = algebraMap ℤ M.K (-1 : ℤ) := by
      rw [show (-1 : Kc) = algebraMap ℤ Kc (-1 : ℤ) by simp]
      rw [← IsScalarTower.algebraMap_apply ℤ Kc M.K]
    rw [h1]
    exact isIntegral_algebraMap)

/-- The minimal polynomial of `z` over `Kc` is `X² + 1`. -/
theorem minpoly_Kc_of_sq_eq_neg_one {M : MaximalUnramifiedProP.{0} Kc 2} {z : M.K}
    (hz : z * z = algebraMap Kc M.K (-1 : Kc)) : minpoly Kc z = X ^ 2 + 1 := by
  have hirr : Irreducible (X ^ 2 + 1 : Kc[X]) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [show (X ^ 2 + 1 : Kc[X]).natDegree = 2 by compute_degree!]
      decide
    · intro w hw
      rw [Polynomial.IsRoot.def] at hw
      have h1 : w ^ 2 + 1 = 0 := by simpa using hw
      have h2 : w * w = -1 := by rw [pow_two] at h1; linear_combination h1
      exact neg_one_not_isSquare_Kc ⟨w, h2⟩
  have hroot : (Polynomial.aeval z) (X ^ 2 + 1 : Kc[X]) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    simp only [Polynomial.eval₂_one]
    have h1 : (1 : M.K) = -(algebraMap Kc M.K (-1 : Kc)) := by rw [map_neg, map_one]; ring
    rw [pow_two, hz, h1]; ring
  have hmonic : (X ^ 2 + 1 : Kc[X]).Monic := by
    have h := monic_X_pow_add_C (n := 2) (a := (1 : Kc)) (by norm_num)
    simpa using h
  exact (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm

/-- The adjoin `Kc⟮z⟯` is two-dimensional over `Kc`. -/
theorem finrank_adjoin_of_sq_eq_neg_one {M : MaximalUnramifiedProP.{0} Kc 2} {z : M.K}
    (hz : z * z = algebraMap Kc M.K (-1 : Kc)) :
    Module.finrank Kc (Kc⟮z⟯ : IntermediateField Kc M.K) = 2 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_Kc_of_sq_eq_neg_one hz),
    minpoly_Kc_of_sq_eq_neg_one hz]
  compute_degree!

/-- `Kc⟮z⟯` is Galois over `Kc`. -/
theorem isGalois_adjoin_of_sq_eq_neg_one {M : MaximalUnramifiedProP.{0} Kc 2} {z : M.K}
    (hz : z * z = algebraMap Kc M.K (-1 : Kc)) :
    IsGalois Kc (Kc⟮z⟯ : IntermediateField Kc M.K) := by
  haveI : Algebra.IsQuadraticExtension Kc (Kc⟮z⟯ : IntermediateField Kc M.K) :=
    ⟨finrank_adjoin_of_sq_eq_neg_one hz⟩
  haveI : Algebra.IsSeparable Kc (Kc⟮z⟯ : IntermediateField Kc M.K) :=
    Algebra.IsSeparable.of_integral Kc _
  exact Algebra.IsQuadraticExtension.isGalois Kc _

/-- The generator of `Kc⟮z⟯` generates it as an algebra over `Kc`. -/
theorem adjoin_gen_eq_top {M : MaximalUnramifiedProP.{0} Kc 2} (z : M.K) :
    Algebra.adjoin Kc ({(⟨z, IntermediateField.subset_adjoin Kc ({z} : Set M.K)
      (Set.mem_singleton z)⟩ : (Kc⟮z⟯ : IntermediateField Kc M.K))} :
      Set (Kc⟮z⟯ : IntermediateField Kc M.K)) = ⊤ := by
  rw [← IntermediateField.adjoin_eq_top_iff]
  have hmap : (IntermediateField.adjoin Kc ({(⟨z, IntermediateField.subset_adjoin Kc ({z} : Set M.K)
      (Set.mem_singleton z)⟩ : (Kc⟮z⟯ : IntermediateField Kc M.K))} :
      Set (Kc⟮z⟯ : IntermediateField Kc M.K))).map (Kc⟮z⟯ : IntermediateField Kc M.K).val
      = (Kc⟮z⟯ : IntermediateField Kc M.K) := by
    refine le_antisymm ?_ ?_
    · rintro w ⟨v, -, rfl⟩; exact v.2
    · rw [IntermediateField.adjoin_le_iff]
      rintro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨_, IntermediateField.subset_adjoin Kc _ (Set.mem_singleton _), rfl⟩
  have htop : (⊤ : IntermediateField Kc (Kc⟮z⟯ : IntermediateField Kc M.K)).map
      (Kc⟮z⟯ : IntermediateField Kc M.K).val = (Kc⟮z⟯ : IntermediateField Kc M.K) := by
    rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  exact IntermediateField.map_injective _ (hmap.trans htop.symm)

section Glue

variable {L : Type*} [Field L] [NumberField L] [Algebra Kc L] [FiniteDimensional Kc L]

/-- **Divisibility by `2` of `√-30030 · a` when the `1`-coordinate of `a` is even.**

If `a : 𝓞 Kc` has coordinates `a = u + v·√-30030` with `u` even, then `√-30030 · a` is twice an
integral element: with `u = 2u₁` one has `√-30030·a = 2(u₁√-30030 - 15015 v)`. -/
theorem exists_two_mul_scR_mul {a : 𝓞 Kc} {u v : ℤ}
    (hco : (a : Kc) = (u : Kc) + (v : Kc) * sc) (hu : Even u) :
    ∃ c : 𝓞 Kc, scR * a = 2 * c := by
  obtain ⟨u₁, rfl⟩ := hu
  refine ⟨(u₁ : 𝓞 Kc) * scR - (15015 * v : 𝓞 Kc), ?_⟩
  apply RingOfIntegers.coe_injective (K := Kc)
  simp only [map_mul, map_sub, map_ofNat, map_intCast, RingOfIntegers.coe_eq_algebraMap]
  have hscR : (algebraMap (𝓞 Kc) Kc) scR = sc := scR_coe
  have ha : (algebraMap (𝓞 Kc) Kc) a = (u₁ : Kc) + (u₁ : Kc) + (v : Kc) * sc := by
    rw [← RingOfIntegers.coe_eq_algebraMap, hco]
    push_cast
    ring
  rw [hscR, ha]
  push_cast
  rw [show sc * ((u₁ : Kc) + (u₁ : Kc) + (v : Kc) * sc)
      = sc * (u₁ : Kc) + sc * (u₁ : Kc) + (v : Kc) * (sc * sc) by ring]
  rw [show sc * sc = -(30030 : Kc) by rw [sc_sq_num]]
  ring

/-- **The trace datum implies that `√-30030` lies in the conductor.**

Assume that for every `b` in the ring of integers of `L` there are `a a' c : 𝓞 Kc` with
`2b = a + a'·x` and `a² + a'² = 4c` (the trace/norm decomposition for a quadratic extension).
Then `√-30030` lies in the conductor of `𝓞 Kc[x]` in `𝓞 L`: for every `b : 𝓞 L` the product
`√-30030 · b` is an `𝓞 Kc`-linear combination of `1` and `x`. -/
theorem scR_mem_conductor (x : 𝓞 L)
    (htrace : ∀ b : 𝓞 L, ∃ a a' c : 𝓞 Kc,
      (2 : 𝓞 L) * b
        = algebraMap (𝓞 Kc) (𝓞 L) a + algebraMap (𝓞 Kc) (𝓞 L) a' * x
      ∧ a ^ 2 + a' ^ 2 = 4 * c) :
    algebraMap (𝓞 Kc) (𝓞 L) scR ∈ conductor (𝓞 Kc) x := by
  rw [mem_conductor_iff]
  intro b
  obtain ⟨a, a', c, heq, hsq⟩ := htrace b
  obtain ⟨u, v, u', v', hco, hco', hu, hu', -, -⟩ :=
    exists_coords_even_of_sq_add_sq_mem_four a a' ⟨c, hsq⟩
  obtain ⟨c₀, hc₀⟩ := exists_two_mul_scR_mul hco hu
  obtain ⟨c₁, hc₁⟩ := exists_two_mul_scR_mul hco' hu'
  have key : algebraMap (𝓞 Kc) (𝓞 L) scR * b
      = algebraMap (𝓞 Kc) (𝓞 L) c₀ + algebraMap (𝓞 Kc) (𝓞 L) c₁ * x := by
    apply RingOfIntegers.coe_injective (K := L)
    have h2 : (2 : L) ≠ 0 := by norm_num
    have h4 : algebraMap (𝓞 Kc) (𝓞 L) scR * (algebraMap (𝓞 Kc) (𝓞 L) a
          + algebraMap (𝓞 Kc) (𝓞 L) a' * x)
        = 2 * (algebraMap (𝓞 Kc) (𝓞 L) c₀ + algebraMap (𝓞 Kc) (𝓞 L) c₁ * x) := by
      have h5 : algebraMap (𝓞 Kc) (𝓞 L) scR * algebraMap (𝓞 Kc) (𝓞 L) a
          = algebraMap (𝓞 Kc) (𝓞 L) (2 * c₀) := by rw [← map_mul, hc₀]
      have h6 : algebraMap (𝓞 Kc) (𝓞 L) scR * algebraMap (𝓞 Kc) (𝓞 L) a'
          = algebraMap (𝓞 Kc) (𝓞 L) (2 * c₁) := by rw [← map_mul, hc₁]
      rw [mul_add, ← mul_assoc, h5, h6]
      simp only [map_mul, map_ofNat]
      try ring
    have heqL : (2 : L) * (b : L)
        = ((algebraMap (𝓞 Kc) (𝓞 L) a + algebraMap (𝓞 Kc) (𝓞 L) a' * x) : 𝓞 L) := by
      rw [← heq]; push_cast; try simp only [map_ofNat]; try ring
    have hmul : (2 : L) * ((algebraMap (𝓞 Kc) (𝓞 L) scR * b) : 𝓞 L)
        = (2 : L) * ((algebraMap (𝓞 Kc) (𝓞 L) c₀
            + algebraMap (𝓞 Kc) (𝓞 L) c₁ * x) : 𝓞 L) := by
      calc (2 : L) * ((algebraMap (𝓞 Kc) (𝓞 L) scR * b) : 𝓞 L)
          = (algebraMap (𝓞 Kc) (𝓞 L) scR : L) * ((2 : L) * (b : L)) := by push_cast; ring
        _ = (algebraMap (𝓞 Kc) (𝓞 L) scR : L) * ((algebraMap (𝓞 Kc) (𝓞 L) a
              + algebraMap (𝓞 Kc) (𝓞 L) a' * x) : 𝓞 L) := by rw [heqL]
        _ = ((algebraMap (𝓞 Kc) (𝓞 L) scR * (algebraMap (𝓞 Kc) (𝓞 L) a
              + algebraMap (𝓞 Kc) (𝓞 L) a' * x)) : 𝓞 L) := by push_cast; try simp only [map_ofNat]; try ring
        _ = ((2 * (algebraMap (𝓞 Kc) (𝓞 L) c₀
              + algebraMap (𝓞 Kc) (𝓞 L) c₁ * x)) : 𝓞 L) := by rw [h4]
        _ = (2 : L) * ((algebraMap (𝓞 Kc) (𝓞 L) c₀
              + algebraMap (𝓞 Kc) (𝓞 L) c₁ * x) : 𝓞 L) := by push_cast; try simp only [map_ofNat]; try ring
    exact mul_left_cancel₀ h2 hmul
  rw [key]
  exact add_mem (Subalgebra.algebraMap_mem _ c₀) (mul_mem (Subalgebra.algebraMap_mem _ c₁)
    (Algebra.subset_adjoin (Set.mem_singleton x)))

/-- **The algebraic contradiction.**  Let `L` be a finite extension field of `Kc`, let `x ∈ 𝓞 L`
square to `-1` and generate `L` over `Kc`, suppose `minpoly (𝓞 Kc) x = X² + 1`, and suppose the
relative different of `𝓞 L / 𝓞 Kc` is trivial.  Then we get a contradiction.

Indeed, the trace form of the quadratic extension gives `2b = a + a'x` with `a² + a'² = 4c` for
every `b ∈ 𝓞 L`; the parity lemma then puts `√-30030` in the conductor of `𝓞 Kc[x]`, so that
`conductor = (√-30030) · different = (√-30030)`, while the classical identity
`conductor · different = (f'(x)) = (2x)` gives `conductor = (2x)`.  Hence `√-30030 = 2x·d` for
some `d ∈ 𝓞 L`, and squaring yields `30030/4 = d² ∈ 𝓞 L`, contradicting `𝓞 L ∩ ℚ = ℤ`. -/
theorem false_of_unramified_of_sq_eq_neg_one (x : 𝓞 L)
    (hgen : Algebra.adjoin Kc ({algebraMap (𝓞 L) L x} : Set L) = ⊤)
    (hx : (algebraMap (𝓞 L) L x) * (algebraMap (𝓞 L) L x) = -1)
    (hminR : minpoly (𝓞 Kc) x = Polynomial.X ^ 2 + 1)
    (hunr : differentIdeal (𝓞 Kc) (𝓞 L) = ⊤) : False := by
  -- the trace datum
  have htrace : ∀ b : 𝓞 L, ∃ a a' c : 𝓞 Kc,
      (2 : 𝓞 L) * b = algebraMap (𝓞 Kc) (𝓞 L) a + algebraMap (𝓞 Kc) (𝓞 L) a' * x
      ∧ a ^ 2 + a' ^ 2 = 4 * c :=
    fun b => exists_two_mul_eq_of_mem_ringOfIntegers x hgen hx b
  have hcond : algebraMap (𝓞 Kc) (𝓞 L) scR ∈ conductor (𝓞 Kc) x := scR_mem_conductor x htrace
  -- the conductor-different identity
  have hrel : conductor (𝓞 Kc) x * differentIdeal (𝓞 Kc) (𝓞 L)
      = Ideal.span {Polynomial.aeval x (Polynomial.derivative (minpoly (𝓞 Kc) x))} :=
    conductor_mul_differentIdeal (𝓞 Kc) Kc L x hgen
  have hderiv : Polynomial.aeval x (Polynomial.derivative (minpoly (𝓞 Kc) x)) = 2 * x := by
    rw [hminR]
    rw [show Polynomial.derivative ((Polynomial.X : (𝓞 Kc)[X]) ^ 2 + 1)
        = Polynomial.C (2 : 𝓞 Kc) * Polynomial.X by
      rw [Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_one,
        add_zero]
      ring_nf]
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_ofNat]
  have hcond2 : conductor (𝓞 Kc) x = Ideal.span {(2 : 𝓞 L) * x} := by
    rw [← hderiv, ← hrel, hunr, Ideal.mul_top]
  have hmem : algebraMap (𝓞 Kc) (𝓞 L) scR ∈ Ideal.span {(2 : 𝓞 L) * x} := by
    rw [← hcond2]; exact hcond
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hmem
  -- push the identity into `L`
  have hscR : (algebraMap (𝓞 Kc) Kc) scR = sc := scR_coe
  have hdL : algebraMap Kc L sc = (2 : L) * (algebraMap (𝓞 L) L x) * ((d : 𝓞 L) : L) := by
    have h := congrArg (fun t : 𝓞 L => algebraMap (𝓞 L) L t) hd
    simp only [map_mul, map_ofNat] at h
    rw [← h, ← IsScalarTower.algebraMap_apply (𝓞 Kc) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 Kc) Kc L, hscR]
  have hsq : (algebraMap Kc L sc) * (algebraMap Kc L sc) = -(30030 : L) := by
    rw [← map_mul, sc_sq_num, map_neg, map_ofNat (algebraMap Kc L) 30030]
  have h1 : (algebraMap Kc L sc) * (algebraMap Kc L sc)
      = 4 * ((algebraMap (𝓞 L) L x) * (algebraMap (𝓞 L) L x))
        * (((d : 𝓞 L) : L) * ((d : 𝓞 L) : L)) := by
    rw [hdL]; ring
  have hq : (4 : L) * (((d : 𝓞 L) : L) * ((d : 𝓞 L) : L)) = 30030 := by
    have h := h1
    rw [hsq, hx] at h
    linear_combination h
  have hd2 : ((d : 𝓞 L) : L) * ((d : 𝓞 L) : L) = algebraMap ℚ L (30030 / 4) := by
    refine mul_left_cancel₀ (show (4 : L) ≠ 0 by norm_num) ?_
    rw [hq, ← map_ofNat (algebraMap ℚ L) 4, ← map_mul,
      show (4 : ℚ) * (30030 / 4) = 30030 by norm_num, map_ofNat (algebraMap ℚ L) 30030]
  -- `30030/4` would be an algebraic integer
  have hint : IsIntegral ℤ (algebraMap ℚ L (30030 / 4)) := by
    rw [← hd2]
    exact (RingOfIntegers.isIntegral_coe d).mul (RingOfIntegers.isIntegral_coe d)
  have hint2 : IsIntegral ℤ (30030 / 4 : ℚ) :=
    (isIntegral_algebraMap_iff (x := (30030 / 4 : ℚ))).mp hint
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hint2
  have hm' : (m : ℚ) = 30030 / 4 := hm
  have hmZ : (4 * m : ℤ) = 30030 := by
    have hcast : ((4 * m : ℤ) : ℚ) = 30030 := by
      push_cast
      rw [hm']
      norm_num
    exact_mod_cast hcast
  omega

end Glue

/-- **The main theorem.** -/
theorem no_sqrt_neg_one_in_maximalUnramified
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2) :
    ¬ ∃ z : M.K, z * z = algebraMap Work.ClassFieldTower.Kc M.K (-1 : Work.ClassFieldTower.Kc) := by
  rintro ⟨z, hz⟩
  have hzKc : IsIntegral Kc z := isIntegral_Kc_of_sq_eq_neg_one hz
  have hzmem : z ∈ (Kc⟮z⟯ : IntermediateField Kc M.K) :=
    IntermediateField.subset_adjoin Kc ({z} : Set M.K) (Set.mem_singleton z)
  have hfd : FiniteDimensional Kc (Kc⟮z⟯ : IntermediateField Kc M.K) :=
    IntermediateField.adjoin.finiteDimensional hzKc
  haveI : NumberField (Kc⟮z⟯ : IntermediateField Kc M.K) := NumberField.of_module_finite Kc _
  have hgal : IsGalois Kc (Kc⟮z⟯ : IntermediateField Kc M.K) := isGalois_adjoin_of_sq_eq_neg_one hz
  have hunr : differentIdeal (𝓞 Kc) (𝓞 (Kc⟮z⟯ : IntermediateField Kc M.K)) = ⊤ :=
    M.unramified _ hfd hgal
  -- the element `z` in `L = Kc⟮z⟯` and its integrality
  have hzL : (⟨z, hzmem⟩ : (Kc⟮z⟯ : IntermediateField Kc M.K))
      * ⟨z, hzmem⟩ = -1 := by
    apply Subtype.ext
    push_cast
    rw [hz, map_neg, map_one]
  have hzL_int : IsIntegral ℤ (⟨z, hzmem⟩ : (Kc⟮z⟯ : IntermediateField Kc M.K)) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hzL]
    rw [show (-1 : (Kc⟮z⟯ : IntermediateField Kc M.K))
        = algebraMap ℤ (Kc⟮z⟯ : IntermediateField Kc M.K) (-1) by simp]
    exact isIntegral_algebraMap
  let x : 𝓞 (Kc⟮z⟯ : IntermediateField Kc M.K) := ⟨⟨z, hzmem⟩, hzL_int⟩
  have hxcoe : ((x : 𝓞 (Kc⟮z⟯ : IntermediateField Kc M.K)) :
      (Kc⟮z⟯ : IntermediateField Kc M.K)) = ⟨z, hzmem⟩ := rfl
  have hgenR : Algebra.adjoin Kc ({(algebraMap (𝓞 (Kc⟮z⟯ : IntermediateField Kc M.K))
      (Kc⟮z⟯ : IntermediateField Kc M.K) x)} :
      Set (Kc⟮z⟯ : IntermediateField Kc M.K)) = ⊤ := by
    rw [show algebraMap (𝓞 (Kc⟮z⟯ : IntermediateField Kc M.K))
        (Kc⟮z⟯ : IntermediateField Kc M.K) x = ⟨z, hzmem⟩ from rfl]
    exact adjoin_gen_eq_top z
  have hxL : (algebraMap (𝓞 (Kc⟮z⟯ : IntermediateField Kc M.K))
      (Kc⟮z⟯ : IntermediateField Kc M.K) x) * algebraMap (𝓞 (Kc⟮z⟯ : IntermediateField Kc M.K))
      (Kc⟮z⟯ : IntermediateField Kc M.K) x = -1 := hzL
  have hminR : minpoly (𝓞 Kc) x = Polynomial.X ^ 2 + 1 :=
    minpoly_ringOfIntegers_adjoin_sq_eq_neg_one hz neg_one_not_isSquare_Kc x hxL
  exact false_of_unramified_of_sq_eq_neg_one
    (L := ↥(Kc⟮z⟯ : IntermediateField Kc M.K)) x hgenR hxL hminR hunr

end

end Work.ShafarevichKoch
