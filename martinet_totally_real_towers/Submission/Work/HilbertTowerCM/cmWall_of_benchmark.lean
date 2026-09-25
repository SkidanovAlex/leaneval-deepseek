import Mathlib
import Submission.Work.CMRealSubfield.Defs
import Submission.Work.CMRealSubfield.Walls

/-!
# `Benchmark ⟹ CMWall`: adjoining `i` to a totally real family

This file proves `Work.HilbertTowerCM.cmWall_of_benchmark`: the **converse** of the classical
real-subfield reduction `Work.CMRealSubfield.benchmark_of_cmWall`.

Given a family of *totally real* number fields `K` of degree `d` with `|disc K| ≤ C ^ d`
(the statement `Work.CMRealSubfield.Benchmark`, the content of the challenge), one obtains a
family of *CM* fields of degree `2d` with the same bounded root discriminant (constant `4 * C`)
by adjoining a square root of `-1`:

* `L := K(i) = K[X]/(X² + 1)` is a quadratic extension of the totally real field `K`, and it is
  totally complex (`i ↦ ±i` under every complex embedding), hence a **CM** extension
  (`Work.CMRealSubfield.cmWall_of_cmExtensionWall`, `NumberField.IsCMField.ofCMExtension`);
* the relative different of `𝓞 L / 𝓞 K` contains `f'(i) = 2i` (the classical conductor–different
  relation applied to the generator `i` of `L` over `K`), hence also `(4) = -(2i)²`; since
  `Ideal.absNorm` is monotone decreasing with respect to inclusion, its norm divides
  `4 ^ [L : ℚ]`;
* the tower formula `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`
  gives `|disc L| ≤ 4 ^ [L : ℚ] · |disc K| ^ 2 ≤ (4 C) ^ [L : ℚ]`.

The route through `Work.CMRealSubfield.cmWall_of_cmExtensionWall` is taken so that the
`IsCMField` instance is produced where the CM-extension data is available.
-/

namespace Work.HilbertTowerCM

open Polynomial NumberField

open scoped NumberField

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace AdjoinI

noncomputable section

/-- **`K(i) = K[X]/(X² + 1)`**, the quadratic extension of `K` obtained by adjoining a square
root of `-1`. -/
abbrev QI (K : Type*) [Field K] : Type _ := AdjoinRoot (X ^ 2 + 1 : K[X])

/-- The class of `X` in `K[X]/(X² + 1)`, i.e. a square root of `-1`. -/
abbrev qiRoot (K : Type*) [Field K] : QI K := AdjoinRoot.root (X ^ 2 + 1 : K[X])

/-! ## `-1` is not a square in a totally real field -/

/-- In a totally real number field, `-1` is not a square: a real embedding would send a square
root of `-1` to a real square root of `-1`. -/
theorem not_isSquare_neg_one_of_isTotallyReal (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] : ¬ IsSquare (-1 : K) := by
  rintro ⟨y, hy⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hφ : ComplexEmbedding.IsReal (InfinitePlace.embedding w) :=
    InfinitePlace.isReal_iff.mp (NumberField.IsTotallyReal.isReal w)
  set f : K →+* ℝ := ComplexEmbedding.IsReal.embedding hφ with hfdef
  have hcoe : ((f y * f y : ℝ) : ℂ) = -1 := by
    rw [Complex.ofReal_mul, hfdef, ComplexEmbedding.IsReal.coe_embedding_apply hφ,
      ← map_mul, ← hy, map_neg, map_one]
  have h1 : f y * f y = -1 := by
    apply Complex.ofReal_injective
    simpa using hcoe
  nlinarith [sq_nonneg (f y), h1]

/-- `X² + 1` is irreducible over a field in which `-1` is not a square. -/
theorem irreducible_X2_add_one (K : Type*) [Field K] (hne : ¬ IsSquare (-1 : K)) :
    Irreducible (X ^ 2 + 1 : K[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [show (X ^ 2 + 1 : K[X]).natDegree = 2 by compute_degree!]
    decide
  · intro w hw
    rw [Polynomial.IsRoot.def] at hw
    have h1 : w ^ 2 + 1 = 0 := by simpa using hw
    refine hne ⟨w, ?_⟩
    rw [pow_two] at h1
    exact (eq_neg_of_add_eq_zero_left h1).symm

/-- For `n : ℤ`, the cast to `ℝ` of `n.natAbs` is `|n|`. -/
theorem natAbs_cast_eq_abs (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  rcases Int.natAbs_eq n with h | h
  · rw [h]; simp
  · rw [h]; simp

/-! ## The minimal polynomial of a square root of `-1` over a ring of integers -/

/-- **`minpoly` over `𝓞 K` of a square root of `-1` in `𝓞 L`.**

Let `L/K` be a finite extension of number fields and let `x ∈ 𝓞 L` satisfy `x² = -1`.  If `-1` is
not a square in `K`, then the minimal polynomial of `x` over the ring `𝓞 K` is `X² + 1`.

The argument is the one of `Work.ShafarevichKoch.minpoly_ringOfIntegers_adjoin_sq_eq_neg_one`:
`X² + 1` is irreducible over `K` (since `-1` is not a square), so it is the minimal polynomial of
the image of `x` in `L`; `minpoly.isIntegrallyClosed_eq_field_fractions` transports this to
`minpoly (𝓞 K) x`, and the map `𝓞 K → K` is injective. -/
theorem minpoly_ringOfIntegers_X2_add_one {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsScalarTower (𝓞 K) (𝓞 L) L]
    (hne : ¬ IsSquare (-1 : K)) (x : 𝓞 L) (hx : (x : L) * (x : L) = -1) :
    minpoly (𝓞 K) x = X ^ 2 + 1 := by
  have hint : IsIntegral (𝓞 K) x := Algebra.IsIntegral.isIntegral x
  have hirr : Irreducible (X ^ 2 + 1 : K[X]) := irreducible_X2_add_one K hne
  have hroot : aeval (x : L) (X ^ 2 + 1 : K[X]) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    simp only [Polynomial.eval₂_one]
    rw [pow_two, hx]
    ring
  have hmonic : (X ^ 2 + 1 : K[X]).Monic := by
    simpa using monic_X_pow_add_C (n := 2) (a := (1 : K)) (by norm_num)
  have hfield : minpoly K (x : L) = X ^ 2 + 1 :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
  have hfr := minpoly.isIntegrallyClosed_eq_field_fractions (R := 𝓞 K) (S := 𝓞 L) K L hint
  have hmap : ((minpoly (𝓞 K) x).map (algebraMap (𝓞 K) K)) = X ^ 2 + 1 := by
    rw [← hfr, hfield]
  have hmap2 : ((X ^ 2 + 1 : (𝓞 K)[X]).map (algebraMap (𝓞 K) K)) = X ^ 2 + 1 := by simp
  exact Polynomial.map_injective (algebraMap (𝓞 K) K) (RingOfIntegers.coe_injective)
    (by rw [hmap, hmap2])

/-- **The relative different of a quadratic extension generated by a square root of `-1` is
bounded.**  For `L/K` a finite extension of number fields and `x ∈ 𝓞 L` with `x² = -1` generating
`L` over `K`, the norm of the relative different ideal divides `4 ^ [L : ℚ]`.

Indeed `f'(x) = 2x ∈ 𝔡_{L/K}` (`aeval_derivative_mem_differentIdeal`), so
`(4) = -(2x)² ⊆ 𝔡_{L/K}`, and `Ideal.absNorm` is monotone decreasing with respect to inclusion. -/
theorem absNorm_differentIdeal_dvd_four {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsScalarTower (𝓞 K) (𝓞 L) L]
    [Algebra.IsSeparable K L]
    (hne : ¬ IsSquare (-1 : K)) (x : 𝓞 L) (hx : (x : L) * (x : L) = -1)
    (hgen : Algebra.adjoin K ({(x : L)} : Set L) = ⊤) :
    Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ 4 ^ Module.finrank ℚ L := by
  have hmin : minpoly (𝓞 K) x = X ^ 2 + 1 := minpoly_ringOfIntegers_X2_add_one hne x hx
  have hderiv : Polynomial.aeval x (Polynomial.derivative (minpoly (𝓞 K) x)) = 2 * x := by
    rw [hmin]
    rw [show Polynomial.derivative ((Polynomial.X : (𝓞 K)[X]) ^ 2 + 1)
        = Polynomial.C (2 : 𝓞 K) * Polynomial.X by
      rw [Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_one,
        add_zero]
      ring_nf]
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_ofNat]
  have hmem : (2 : 𝓞 L) * x ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    rw [← hderiv]
    exact aeval_derivative_mem_differentIdeal (𝓞 K) K L x hgen
  have hx' : x * x = -(1 : 𝓞 L) := by
    apply RingOfIntegers.coe_injective (K := L)
    rw [map_mul, map_neg, map_one]
    exact hx
  have hsq : ((2 : 𝓞 L) * x) * ((2 : 𝓞 L) * x) = -(4 : 𝓞 L) := by
    rw [show (2 : 𝓞 L) * x * (2 * x) = 4 * (x * x) by ring, hx']
    ring
  have hfour : (4 : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    have h1 := (differentIdeal (𝓞 K) (𝓞 L)).mul_mem_left ((2 : 𝓞 L) * x) hmem
    rw [hsq] at h1
    exact neg_mem_iff.mp h1
  have hle : Ideal.span {(4 : 𝓞 L)} ≤ differentIdeal (𝓞 K) (𝓞 L) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfour)
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have h4 : Ideal.absNorm (Ideal.span {(4 : 𝓞 L)}) = 4 ^ Module.finrank ℚ L := by
    have := Ideal.absNorm_span_natCast (S := 𝓞 L) 4
    rw [RingOfIntegers.rank] at this
    exact this
  rwa [h4] at hdvd

/-! ## The field `K(i)` -/

/-- The class of `X` in `K[X]/(X² + 1)` squares to `-1`. -/
theorem qiRoot_sq (K : Type*) [Field K] : qiRoot K ^ 2 = (-1 : QI K) := by
  have h0 : aeval (qiRoot K) (X ^ 2 + 1 : K[X]) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [map_add, map_pow, map_one, aeval_def, Polynomial.eval₂_X] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-- The square root of `-1` in `K(i)` is integral over `ℤ`. -/
theorem qiRoot_isIntegral (K : Type*) [Field K] : IsIntegral ℤ (qiRoot K) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [qiRoot_sq K]
  rw [show (-1 : QI K) = algebraMap ℤ (QI K) (-1) by simp]
  exact isIntegral_algebraMap

/-- `K(i)` is a finite extension of `K`. -/
instance instModuleFiniteQI (K : Type*) [Field K] [Fact (Irreducible (X ^ 2 + 1 : K[X]))] :
    Module.Finite K (QI K) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible (X ^ 2 + 1 : K[X])).ne_zero).finite

/-- `K(i)` is a number field when `K` is. -/
instance instNumberFieldQI (K : Type*) [Field K] [NumberField K]
    [Fact (Irreducible (X ^ 2 + 1 : K[X]))] : NumberField (QI K) := by
  haveI := instModuleFiniteQI K
  exact NumberField.of_module_finite K (QI K)

/-- The scalar-tower `𝓞 K → 𝓞 (K(i)) → K(i)`.  (It has to be provided explicitly: the
`AdjoinRoot` algebra structure on `K(i)` is not definitionally the one used by
`RingOfIntegers.inst_isScalarTower`.) -/
instance instIsScalarTowerQI (K : Type*) [Field K] [NumberField K]
    [Fact (Irreducible (X ^ 2 + 1 : K[X]))] :
    IsScalarTower (𝓞 K) (𝓞 (QI K)) (QI K) := by
  haveI := instModuleFiniteQI K
  haveI := instNumberFieldQI K
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- `K(i)/K` is a quadratic extension. -/
instance instIsQuadraticExtensionQI (K : Type*) [Field K]
    [Fact (Irreducible (X ^ 2 + 1 : K[X]))] : Algebra.IsQuadraticExtension K (QI K) :=
  ⟨by
    have hf : (X ^ 2 + 1 : K[X]) ≠ 0 := (Fact.out : Irreducible (X ^ 2 + 1 : K[X])).ne_zero
    rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim]
    compute_degree!⟩

/-- `K(i)` is totally complex: every complex embedding sends `i` to `±i`. -/
instance instIsTotallyComplexQI (K : Type*) [Field K]
    [Fact (Irreducible (X ^ 2 + 1 : K[X]))] : IsTotallyComplex (QI K) := ⟨fun w => by
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have hφ : ComplexEmbedding.IsReal (InfinitePlace.embedding w) := InfinitePlace.isReal_iff.mp hw
  set f : QI K →+* ℝ := ComplexEmbedding.IsReal.embedding hφ with hfdef
  have hcoe : ((f (qiRoot K) * f (qiRoot K) : ℝ) : ℂ) = -1 := by
    rw [Complex.ofReal_mul, hfdef, ComplexEmbedding.IsReal.coe_embedding_apply hφ,
      ← map_mul, ← pow_two, qiRoot_sq K, map_neg, map_one]
  have h1 : f (qiRoot K) * f (qiRoot K) = -1 := by
    apply Complex.ofReal_injective
    simpa using hcoe
  nlinarith [sq_nonneg (f (qiRoot K)), h1]⟩

/-- `[K(i) : ℚ] = 2 * [K : ℚ]`. -/
theorem finrank_rat_QI (K : Type*) [Field K] [NumberField K]
    [Fact (Irreducible (X ^ 2 + 1 : K[X]))] :
    Module.finrank ℚ (QI K) = 2 * Module.finrank ℚ K := by
  have h2 : Module.finrank K (QI K) = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K (QI K)
  rw [← Module.finrank_mul_finrank ℚ K (QI K), h2, mul_comm]

/-! ## The discriminant bound for `K(i)` -/

/-- The relative different of `𝓞 (K(i)) / 𝓞 K` has norm dividing `4 ^ [K(i) : ℚ]`. -/
theorem absNorm_differentIdeal_QI_dvd (K : Type*) [Field K] [NumberField K]
    [Fact (Irreducible (X ^ 2 + 1 : K[X]))] (hne : ¬ IsSquare (-1 : K)) :
    Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 (QI K))) ∣ 4 ^ Module.finrank ℚ (QI K) := by
  haveI : Algebra.IsSeparable K (QI K) := inferInstance
  let x : 𝓞 (QI K) := ⟨qiRoot K, qiRoot_isIntegral K⟩
  have hx : (x : QI K) = qiRoot K := rfl
  have hx2 : (x : QI K) * (x : QI K) = -1 := by
    rw [hx, ← pow_two, qiRoot_sq K]
  have hgen : Algebra.adjoin K ({(x : QI K)} : Set (QI K)) = ⊤ := by
    rw [hx]
    exact AdjoinRoot.adjoinRoot_eq_top
  exact absNorm_differentIdeal_dvd_four hne x hx2 hgen

/-- **The discriminant bound for `K(i)`.**  If `K` is totally real then
`|disc K(i)| ≤ 16 ^ [K : ℚ] · |disc K| ^ 2`, i.e. the root discriminant of `K(i)` is at most
`4 · √|disc K|^(1/[K:ℚ])`.

This is the tower formula together with `absNorm_differentIdeal_QI_dvd`. -/
theorem natAbs_discr_QI_le (K : Type*) [Field K] [NumberField K]
    [Fact (Irreducible (X ^ 2 + 1 : K[X]))] (hne : ¬ IsSquare (-1 : K)) :
    (NumberField.discr (QI K)).natAbs ≤
      16 ^ Module.finrank ℚ K * (NumberField.discr K).natAbs ^ 2 := by
  have hformula := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    K (𝓞 K) (QI K) (𝓞 (QI K))
  have h2 : Module.finrank K (QI K) = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K (QI K)
  have hformula2 : (NumberField.discr (QI K)).natAbs =
      Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 (QI K))) * (NumberField.discr K).natAbs ^ 2 := by
    rw [hformula, h2]
  have hdvd := absNorm_differentIdeal_QI_dvd K hne
  have hle : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 (QI K))) ≤
      4 ^ Module.finrank ℚ (QI K) :=
    Nat.le_of_dvd (by positivity) hdvd
  have h4 : 4 ^ Module.finrank ℚ (QI K) = 16 ^ Module.finrank ℚ K := by
    rw [finrank_rat_QI K, pow_mul]
    norm_num
  calc (NumberField.discr (QI K)).natAbs
      = Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 (QI K))) * (NumberField.discr K).natAbs ^ 2 :=
        hformula2
    _ ≤ 4 ^ Module.finrank ℚ (QI K) * (NumberField.discr K).natAbs ^ 2 :=
        Nat.mul_le_mul_right _ hle
    _ = 16 ^ Module.finrank ℚ K * (NumberField.discr K).natAbs ^ 2 := by rw [h4]

end

end AdjoinI

/-- **The benchmark implies the CM wall**: adjoining `i` to a totally real family of number
fields produces a CM family of twice the degree with the constant `4 * C`. -/
theorem cmExtensionWall_of_benchmark (h : Work.CMRealSubfield.Benchmark) :
    Work.CMRealSubfield.CMExtensionWall := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨4 * C, by positivity, fun N => ?_⟩
  obtain ⟨d, hNd, K, hKf, hKnf, hKtr, hKfin, hKdisc⟩ := hfam N
  letI := hKf
  letI := hKnf
  letI := hKtr
  have hne : ¬ IsSquare (-1 : K) := AdjoinI.not_isSquare_neg_one_of_isTotallyReal K
  haveI hirr : Fact (Irreducible (X ^ 2 + 1 : K[X])) :=
    ⟨AdjoinI.irreducible_X2_add_one K hne⟩
  refine ⟨K, hKf, hKnf, hKtr, AdjoinI.QI K, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · rw [AdjoinI.finrank_rat_QI K, hKfin]
    omega
  · have hnat := AdjoinI.natAbs_discr_QI_le K hne
    have hnatR : ((NumberField.discr (AdjoinI.QI K)).natAbs : ℝ) ≤
        (16 : ℝ) ^ d * (C ^ d) ^ 2 := by
      have hcast : ((NumberField.discr (AdjoinI.QI K)).natAbs : ℝ) ≤
          ((16 ^ Module.finrank ℚ K * (NumberField.discr K).natAbs ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hpush : ((16 ^ Module.finrank ℚ K * (NumberField.discr K).natAbs ^ 2 : ℕ) : ℝ) =
          (16 : ℝ) ^ Module.finrank ℚ K * ((NumberField.discr K).natAbs : ℝ) ^ 2 := by
        push_cast
        ring
      rw [hpush, hKfin] at hcast
      have hKabs : ((NumberField.discr K).natAbs : ℝ) ≤ C ^ d := by
        rw [AdjoinI.natAbs_cast_eq_abs (NumberField.discr K)]
        exact hKdisc
      have hsq : ((NumberField.discr K).natAbs : ℝ) ^ 2 ≤ (C ^ d) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hKabs 2
      exact le_trans hcast (mul_le_mul_of_nonneg_left hsq (by positivity))
    have hconst : (16 : ℝ) ^ d * (C ^ d) ^ 2 = (4 * C) ^ (2 * d) := by
      have hL : (16 : ℝ) ^ d * (C ^ d) ^ 2 = (16 * C ^ 2) ^ d := by
        rw [pow_two, ← pow_add, show d + d = 2 * d by ring, pow_mul, ← mul_pow]
      have hR : (4 * C) ^ (2 * d) = (16 * C ^ 2) ^ d := by
        rw [pow_mul]
        congr 1
        ring
      rw [hL, hR]
    calc |(NumberField.discr (AdjoinI.QI K) : ℝ)|
        = ((NumberField.discr (AdjoinI.QI K)).natAbs : ℝ) :=
          (AdjoinI.natAbs_cast_eq_abs (NumberField.discr (AdjoinI.QI K))).symm
      _ ≤ (16 : ℝ) ^ d * (C ^ d) ^ 2 := hnatR
      _ = (4 * C) ^ (2 * d) := hconst
      _ = (4 * C) ^ Module.finrank ℚ (AdjoinI.QI K) := by
          rw [AdjoinI.finrank_rat_QI K, hKfin]

/-- **`Benchmark ⟹ CMWall`** (the converse of `Work.CMRealSubfield.benchmark_of_cmWall`). -/
theorem cmWall_of_benchmark (h : Work.CMRealSubfield.Benchmark) : Work.CMRealSubfield.CMWall :=
  Work.CMRealSubfield.cmWall_of_cmExtensionWall (cmExtensionWall_of_benchmark h)

end Work.HilbertTowerCM
