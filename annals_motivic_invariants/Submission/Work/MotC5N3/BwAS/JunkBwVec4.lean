import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.BwASDefs
import Submission.Work.MotC5N3.BwAS.BwASpolyFracRing
import Submission.Work.MotK.TGen.JunkClassBwVec4
import Submission.Work.MotK.JunkClassPrimePointX
import Submission.Work.MotK.JunkClassLinearThree
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth


/-!
# `Work.MotV5.ASLocal.JunkBwVec4` — local fork of `MotAS.censusAS2_junk_bwVec4`

**Why this file exists.**  Byte-for-byte copy of the sibling census clause, with the single import of
`MotAS.bwASpoly_fractionRing` re-pointed at the local fork `MotV5.ASLocal.BwASpolyFracRing` (which
renames the two declarations `asR2`, `asV` that clash with `SdualAS2Defs`/`ASMinv` inside the import
closure of `censusAS2_class_sdual`).  See `BwASpolyFracRing.lean` and `JunkFwVec0.lean` for the
duplicate-declaration conflicts this works around.  It is a *replacement* for
`Submission.Work.MotAS.censusAS2_junk_bwVec4`: do **not** import both.
-/
/-!
# `Work.MotAS.censusAS2_junk_bwVec4` — the target chart denominator of the corrected AS chart

`bwVecAS2 a b g 4 = (R^AS(tchart))₄` is the explicit cubic `bwASpoly a b g` of
`Submission/Work/MotAS/BwASDefs.lean` (`bwVecAS2_four_eq_bwASpoly`).  For the census data
`a = aK D`, `b = bK D` (with `a² − ab − b² ≠ 0` from `ASGood D`) and `g = fAS 𝕜 = t³ + t ≠ 0`,

* `bwASpoly a b g` is **prime** (`bwASpoly_prime` below): transported to the variable `X₂` (via
  `Work.MotK.TGen.bwTau`) it becomes the cubic `bwQT a b g = C κ X³ + C α X² + C β X + C δ` with
  `κ = −g·d²`, `α = γX₁ − 2ed`, `β = −ed X₀X₁ − d²X₀`, `δ = γX₁² + γX₀²X₁ − 2ed X₁³`; its leading
  coefficient `κ` is a unit of `K[X₀,X₁]`, it has **no root** in `K[X₀,X₁]` (the `X₀`-degree
  argument: `deg(κ·r³) = 3·deg r` dominates `deg(α r²) = 2·deg r`, `deg(β r) ≤ 1 + deg r` and
  `deg δ = 2`), and it is therefore irreducible by
  `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`;
* hence the only height-one prime containing it is the principal prime it generates
  (`Work.MotK.CensusPrime.eq_span_of_height_one`);
* the residue field of that prime is the rational function field `RatFunc (RatFunc (RatFunc 𝕜))`
  (`Work.MotAS.bwASpoly_fractionRing`), because the projective closure
  `{W·bwASQ + bwASR = 0} ⊆ ℙ³` is linear in `W` and hence birational to `ℙ²`.

The single-prime residue field is a junk class by `Work.MotK.junkClass_of_resF_ratFunc_ratFunc`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MotC5N3.BwAS

open Work.MotAS

open MvPolynomial

/-! ## §1.  `X₀`-degree bookkeeping in `K[X₀,X₁]` -/

/-- The `X₀`-degree of a non-zero product in `K[X₀,X₁]` is the sum of the `X₀`-degrees. -/
theorem degreeOf_zero_mul_fin2 {K : Type*} [CommRing K] [IsDomain K]
    (f g : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).degreeOf 0 = f.degreeOf 0 + g.degreeOf 0 := by
  have hf' : MvPolynomial.finSuccEquiv K 1 f ≠ 0 := fun h =>
    hf ((MvPolynomial.finSuccEquiv K 1).injective (by rw [h, map_zero]))
  have hg' : MvPolynomial.finSuccEquiv K 1 g ≠ 0 := fun h =>
    hg ((MvPolynomial.finSuccEquiv K 1).injective (by rw [h, map_zero]))
  rw [← MvPolynomial.natDegree_finSuccEquiv (R := K) (n := 1) (f * g), map_mul,
    Polynomial.natDegree_mul'
      (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf')
        (Polynomial.leadingCoeff_ne_zero.mpr hg')),
    MvPolynomial.natDegree_finSuccEquiv (R := K) (n := 1) f,
    MvPolynomial.natDegree_finSuccEquiv (R := K) (n := 1) g]

/-- The `X₀`-degree of a power of a non-zero polynomial. -/
theorem degreeOf_zero_pow_fin2 {K : Type*} [CommRing K] [IsDomain K]
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (n : ℕ) :
    (f ^ n).degreeOf 0 = n * f.degreeOf 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, degreeOf_zero_mul_fin2 _ _ (pow_ne_zero k hf) hf, ih]
      first | refl_ring1 | ring

/-- `degreeOf 0` of a difference is at most the maximum of the two degrees. -/
theorem degreeOf_zero_sub_le {K : Type*} [CommRing K] (f g : MvPolynomial (Fin 2) K) :
    (f - g).degreeOf 0 ≤ max (f.degreeOf 0) (g.degreeOf 0) := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  by_cases hf : m ∈ f.support
  · exact (MvPolynomial.monomial_le_degreeOf 0 hf).trans (le_max_left _ _)
  · by_cases hg : m ∈ g.support
    · exact (MvPolynomial.monomial_le_degreeOf 0 hg).trans (le_max_right _ _)
    · exfalso
      rw [MvPolynomial.mem_support_iff] at hm
      rw [MvPolynomial.coeff_sub, MvPolynomial.notMem_support_iff.mp hf,
        MvPolynomial.notMem_support_iff.mp hg, sub_zero] at hm
      exact hm rfl

/-- Multiplying by a constant does not increase the `X₀`-degree. -/
theorem degreeOf_zero_C_mul_le {K : Type*} [CommRing K] (c : K) (f : MvPolynomial (Fin 2) K) :
    (C c * f).degreeOf 0 ≤ f.degreeOf 0 := by
  refine (MvPolynomial.degreeOf_mul_le 0 (C c) f).trans ?_
  rw [MvPolynomial.degreeOf_C, zero_add]

/-- `(X₁ : K[X₀,X₁]).degreeOf 0 = 0`. -/
theorem degreeOf_zero_X_one {K : Type*} [CommRing K] [Nontrivial K] :
    (X 1 : MvPolynomial (Fin 2) K).degreeOf 0 = 0 := by
  rw [MvPolynomial.degreeOf_X]
  simp

/-- `(X₁ ^ n : K[X₀,X₁]).degreeOf 0 = 0`. -/
theorem degreeOf_zero_X_one_pow {K : Type*} [CommRing K] [Nontrivial K] (n : ℕ) :
    (X 1 ^ n : MvPolynomial (Fin 2) K).degreeOf 0 = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine (MvPolynomial.degreeOf_pow_le 0 (X 1) n).trans ?_
  rw [degreeOf_zero_X_one, mul_zero]

/-! ## §2.  The four coefficients of `bwASpoly` in the variable `X₂` -/

/-- The leading coefficient `κ = −g·d²` of the cubic in `X₂`. -/
noncomputable def nrK (K : Type*) [CommRing K] (a b g : K) : K := -(g * asDel a b ^ 2)

/-- The `X₂²`-coefficient `α = γX₁ − 2ed`. -/
noncomputable def nrA (K : Type*) [CommRing K] (a b : K) : MvPolynomial (Fin 2) K :=
  C (asGam a b) * X 1 - C (2 * asEps a b * asDel a b)

/-- The `X₂`-coefficient `β = −ed X₀X₁ − d²X₀`. -/
noncomputable def nrB (K : Type*) [CommRing K] (a b : K) : MvPolynomial (Fin 2) K :=
  (0 : MvPolynomial (Fin 2) K) - C (asEps a b * asDel a b) * X 0 * X 1
    - C (asDel a b ^ 2) * X 0

/-- The constant coefficient `δ = γX₁² + γX₀²X₁ − 2ed X₁³`. -/
noncomputable def nrD (K : Type*) [CommRing K] (a b : K) : MvPolynomial (Fin 2) K :=
  X 0 ^ 2 * (C (asGam a b) * X 1)
    + (C (asGam a b) * (X 1) ^ 2 - C (2 * asEps a b * asDel a b) * (X 1) ^ 3)

variable {K : Type} [Field K] [CharP K 5]

/-- `deg_{X₀} α ≤ 0`. -/
theorem degreeOf_zero_nrA_le (a b : K) : (nrA K a b).degreeOf 0 ≤ 0 := by
  have h1 : (C (asGam a b) * X 1 : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 0 := by
    refine (MvPolynomial.degreeOf_mul_le 0 (C (asGam a b)) (X 1)).trans ?_
    rw [MvPolynomial.degreeOf_C, zero_add, degreeOf_zero_X_one]
  have h2 : (C (2 * asEps a b * asDel a b) : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 0 := by
    rw [MvPolynomial.degreeOf_C]
  rw [nrA]
  exact (degreeOf_zero_sub_le (C (asGam a b) * X 1)
    (C (2 * asEps a b * asDel a b))).trans (max_le h1 h2)

/-- `deg_{X₀} β ≤ 1`. -/
theorem degreeOf_zero_nrB_le (a b : K) : (nrB K a b).degreeOf 0 ≤ 1 := by
  have h0 : (0 : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 1 := by
    rw [MvPolynomial.degreeOf_zero]; norm_num
  have hX0 : (X 0 : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 1 := by
    rw [MvPolynomial.degreeOf_X_self]
  have hE : (C (asEps a b * asDel a b) * X 0 : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 1 := by
    refine (MvPolynomial.degreeOf_mul_le 0 (C (asEps a b * asDel a b)) (X 0)).trans ?_
    rw [MvPolynomial.degreeOf_C, zero_add]
    exact hX0
  have hE1 : (C (asEps a b * asDel a b) * X 0 * X 1 : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 1 := by
    refine (MvPolynomial.degreeOf_mul_le 0 (C (asEps a b * asDel a b) * X 0) (X 1)).trans ?_
    rw [degreeOf_zero_X_one, add_zero]
    exact hE
  have hD : (C (asDel a b ^ 2) * X 0 : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 1 := by
    refine (MvPolynomial.degreeOf_mul_le 0 (C (asDel a b ^ 2)) (X 0)).trans ?_
    rw [MvPolynomial.degreeOf_C, zero_add]
    exact hX0
  have hsub : ((0 : MvPolynomial (Fin 2) K)
      - C (asEps a b * asDel a b) * X 0 * X 1).degreeOf 0 ≤ 1 :=
    (degreeOf_zero_sub_le (0 : MvPolynomial (Fin 2) K)
      (C (asEps a b * asDel a b) * X 0 * X 1)).trans (max_le h0 hE1)
  rw [nrB]
  exact (degreeOf_zero_sub_le ((0 : MvPolynomial (Fin 2) K)
    - C (asEps a b * asDel a b) * X 0 * X 1)
    (C (asDel a b ^ 2) * X 0)).trans (max_le hsub hD)

/-- `deg_{X₀} δ = 2` when `γ ≠ 0`. -/
theorem degreeOf_zero_nrD (a b : K) (hγ : asGam a b ≠ 0) : (nrD K a b).degreeOf 0 = 2 := by
  rw [nrD]
  have h1 : (X 0 ^ 2 * (C (asGam a b) * X 1) : MvPolynomial (Fin 2) K).degreeOf 0 = 2 := by
    rw [degreeOf_zero_mul_fin2 _ _ (pow_ne_zero 2 (MvPolynomial.X_ne_zero 0))
      (mul_ne_zero (by simpa using hγ) (MvPolynomial.X_ne_zero 1))]
    rw [MvPolynomial.degreeOf_X_self_pow,
      degreeOf_zero_mul_fin2 _ _ (by simpa using hγ) (MvPolynomial.X_ne_zero 1),
      MvPolynomial.degreeOf_C, degreeOf_zero_X_one, add_zero]
  have h2 : (C (asGam a b) * (X 1) ^ 2 - C (2 * asEps a b * asDel a b) * (X 1) ^ 3 :
      MvPolynomial (Fin 2) K).degreeOf 0 ≤ 0 := by
    refine (degreeOf_zero_sub_le _ _).trans ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · refine (degreeOf_zero_C_mul_le (asGam a b) ((X 1) ^ 2)).trans ?_
      rw [degreeOf_zero_X_one_pow]
    · refine (degreeOf_zero_C_mul_le (2 * asEps a b * asDel a b) ((X 1) ^ 3)).trans ?_
      rw [degreeOf_zero_X_one_pow]
  rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt
    (by rw [h1]; exact lt_of_le_of_lt h2 (by norm_num)), h1]

/-! ## §3.  The cubic has no root in `K[X₀,X₁]` -/

/-- `MvPolynomial.C x ≠ 0` when `x ≠ 0` (two variables). -/
theorem C_ne_zero_two {x : K} (hx : x ≠ 0) : (C x : MvPolynomial (Fin 2) K) ≠ 0 :=
  fun h => hx (MvPolynomial.C_injective (Fin 2) K
    (show C x = C (0 : K) from by rw [h, MvPolynomial.C_0]))

/-- **The `X₀`-degree argument.**  `κ·r³ + α·r² + β·r + δ ≠ 0` for every `r ∈ K[X₀,X₁]`: the
leading term `κr³` has `X₀`-degree `3·deg r` (`κ ≠ 0` a constant), which strictly dominates
`2·deg r` (from `α`), `1 + deg r` (from `β`) and `2` (from `δ`). -/
theorem nrK_mul_pow_add (a b g : K) (hd : asDel a b ≠ 0) (hg : g ≠ 0)
    (r : MvPolynomial (Fin 2) K) :
    C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2 + nrB K a b * r + nrD K a b ≠ 0 := by
  have hγ : asGam a b ≠ 0 := asGam_ne_zero a b hd
  have hκ : nrK K a b g ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hg (asDel_sq_ne_zero a b hd))
  have hD : (nrD K a b).degreeOf 0 = 2 := degreeOf_zero_nrD a b hγ
  intro hcon
  rcases eq_or_ne r 0 with hr | hr
  · have hz : nrD K a b = 0 := by
      have h := hcon
      rw [hr] at h
      simpa only [zero_pow (show (3 : ℕ) ≠ 0 by norm_num),
        zero_pow (show (2 : ℕ) ≠ 0 by norm_num), mul_zero, add_zero, zero_add] using h
    rw [hz, MvPolynomial.degreeOf_zero] at hD
    exact absurd hD (by norm_num)
  · have hA : (C (nrK K a b g) * r ^ 3 : MvPolynomial (Fin 2) K).degreeOf 0
        = 3 * r.degreeOf 0 := by
      rw [degreeOf_zero_mul_fin2 (C (nrK K a b g)) (r ^ 3)
        (C_ne_zero_two hκ) (pow_ne_zero 3 hr)]
      rw [MvPolynomial.degreeOf_C, zero_add, degreeOf_zero_pow_fin2 r hr 3]
    have hB : (nrA K a b * r ^ 2 : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 2 * r.degreeOf 0 := by
      refine (MvPolynomial.degreeOf_mul_le 0 (nrA K a b) (r ^ 2)).trans ?_
      rw [degreeOf_zero_pow_fin2 r hr 2]
      have h := degreeOf_zero_nrA_le (K := K) a b
      omega
    have hC : (nrB K a b * r : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 1 + r.degreeOf 0 :=
      (MvPolynomial.degreeOf_mul_le 0 (nrB K a b) r).trans
        (add_le_add (degreeOf_zero_nrB_le (K := K) a b) le_rfl)
    rcases Nat.eq_zero_or_pos (r.degreeOf 0) with hn | hn
    · have hA0 : (C (nrK K a b g) * r ^ 3 : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 0 := by
        rw [hA, hn]
      have hB0 : (nrA K a b * r ^ 2 : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 0 := by
        rw [hn] at hB
        simpa using hB
      have hC0 : (nrB K a b * r : MvPolynomial (Fin 2) K).degreeOf 0 ≤ 1 := by
        rw [hn] at hC
        simpa using hC
      have hAB : ((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2) :
          MvPolynomial (Fin 2) K).degreeOf 0 ≤ 0 :=
        (MvPolynomial.degreeOf_add_le 0 (C (nrK K a b g) * r ^ 3)
          (nrA K a b * r ^ 2)).trans (max_le hA0 hB0)
      have hABC : (((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2) + nrB K a b * r) :
          MvPolynomial (Fin 2) K).degreeOf 0 ≤ 1 :=
        (MvPolynomial.degreeOf_add_le 0 (C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2)
          (nrB K a b * r)).trans (max_le (hAB.trans (by norm_num : (0 : ℕ) ≤ 1)) hC0)
      have hlt : (((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2) + nrB K a b * r) :
          MvPolynomial (Fin 2) K).degreeOf 0 < (nrD K a b).degreeOf 0 := by
        rw [hD]; exact lt_of_le_of_lt hABC (by norm_num)
      have hdeg : (nrD K a b + ((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2)
          + nrB K a b * r) : MvPolynomial (Fin 2) K).degreeOf 0 = 2 :=
        (MvPolynomial.degreeOf_add_eq_of_degreeOf_lt hlt).trans hD
      have hdeg' : (((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2) + nrB K a b * r
          + nrD K a b) : MvPolynomial (Fin 2) K).degreeOf 0 = 2 := by
        rw [show (((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2) + nrB K a b * r)
            + nrD K a b) = nrD K a b + ((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2)
            + nrB K a b * r) from add_comm _ _]
        exact hdeg
      rw [hcon, MvPolynomial.degreeOf_zero] at hdeg'
      exact absurd hdeg' (by norm_num)
    · have hAB : ((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2) :
          MvPolynomial (Fin 2) K).degreeOf 0 = 3 * r.degreeOf 0 :=
        (MvPolynomial.degreeOf_add_eq_of_degreeOf_lt
          (show (nrA K a b * r ^ 2 : MvPolynomial (Fin 2) K).degreeOf 0
              < (C (nrK K a b g) * r ^ 3).degreeOf 0 from by
            rw [hA]; exact lt_of_le_of_lt hB (by omega))).trans hA
      have hABC : (((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2) + nrB K a b * r) :
          MvPolynomial (Fin 2) K).degreeOf 0 = 3 * r.degreeOf 0 :=
        (MvPolynomial.degreeOf_add_eq_of_degreeOf_lt
          (show (nrB K a b * r : MvPolynomial (Fin 2) K).degreeOf 0
              < (C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2).degreeOf 0 from by
            rw [hAB]; exact lt_of_le_of_lt hC (by omega))).trans hAB
      have hltD : (nrD K a b : MvPolynomial (Fin 2) K).degreeOf 0
          < (C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2 + nrB K a b * r :
              MvPolynomial (Fin 2) K).degreeOf 0 := by
        rw [hABC, hD]; omega
      have hdeg : (((C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2) + nrB K a b * r
          + nrD K a b) : MvPolynomial (Fin 2) K).degreeOf 0 = 3 * r.degreeOf 0 :=
        (MvPolynomial.degreeOf_add_eq_of_degreeOf_lt hltD).trans hABC
      rw [hcon, MvPolynomial.degreeOf_zero] at hdeg
      exact absurd hdeg (by omega)

/-! ## §4.  The transported cubic and its irreducibility -/

/-- The cubic `bwASpoly a b g` rewritten in the polynomial variable `X₂`:
`C (C κ) X³ + C α X² + C β X + C δ`. -/
noncomputable def bwQT (K : Type*) [CommRing K] (a b g : K) :
    Polynomial (MvPolynomial (Fin 2) K) :=
  Polynomial.C (MvPolynomial.C (nrK K a b g)) * Polynomial.X ^ 3
    + Polynomial.C (nrA K a b) * Polynomial.X ^ 2
    + Polynomial.C (nrB K a b) * Polynomial.X + Polynomial.C (nrD K a b)

/-- **The transport**: `bwTau` sends `bwASpoly` to the cubic `bwQT`. -/
theorem bwTau_bwASpoly (a b g : K) :
    Work.MotK.TGen.bwTau K (bwASpoly a b g) = bwQT K a b g := by
  rw [bwASpoly_decomp]
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, Work.MotK.TGen.bwTau_X_zero,
    Work.MotK.TGen.bwTau_X_one, Work.MotK.TGen.bwTau_X_two, Work.MotK.TGen.bwTau_C,
    bwQT, nrK, nrA, nrB, nrD, Polynomial.C_neg, Polynomial.C_add,
    Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_0, MvPolynomial.C_0]
  first | refl_ring1 | ring

/-- The `X³`-coefficient of the transported cubic is `C κ`. -/
theorem bwQT_coeff_three (a b g : K) : (bwQT K a b g).coeff 3 = MvPolynomial.C (nrK K a b g) := by
  have h3 : (Polynomial.C (MvPolynomial.C (nrK K a b g)) * Polynomial.X ^ 3 :
      Polynomial (MvPolynomial (Fin 2) K)).coeff 3 = MvPolynomial.C (nrK K a b g) := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  have h2 : (Polynomial.C (nrA K a b) * Polynomial.X ^ 2 :
      Polynomial (MvPolynomial (Fin 2) K)).coeff 3 = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  have h1 : (Polynomial.C (nrB K a b) * Polynomial.X :
      Polynomial (MvPolynomial (Fin 2) K)).coeff 3 = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X]
    simp
  have h0 : (Polynomial.C (nrD K a b) :
      Polynomial (MvPolynomial (Fin 2) K)).coeff 3 = 0 := by
    rw [Polynomial.coeff_C]
    simp
  rw [bwQT, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add, h3, h2, h1, h0]
  simp

/-- The transported cubic has degree at most `3`. -/
theorem bwQT_natDegree_le (a b g : K) : (bwQT K a b g).natDegree ≤ 3 := by
  have h1 : (Polynomial.C (MvPolynomial.C (nrK K a b g)) * Polynomial.X ^ 3 :
      Polynomial (MvPolynomial (Fin 2) K)).natDegree ≤ 3 := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
  have h2 : (Polynomial.C (nrA K a b) * Polynomial.X ^ 2 :
      Polynomial (MvPolynomial (Fin 2) K)).natDegree ≤ 3 := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    norm_num
  have h3 : (Polynomial.C (nrB K a b) * Polynomial.X :
      Polynomial (MvPolynomial (Fin 2) K)).natDegree ≤ 3 := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
    norm_num
  have h4 : (Polynomial.C (nrD K a b) :
      Polynomial (MvPolynomial (Fin 2) K)).natDegree ≤ 3 := by
    rw [Polynomial.natDegree_C]
    norm_num
  rw [bwQT]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ h4)
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ h3)
  exact (Polynomial.natDegree_add_le _ _).trans (max_le h1 h2)

/-- The transported cubic has no root in `K[X₀,X₁]`. -/
theorem bwQT_no_root (a b g : K) (hd : asDel a b ≠ 0) (hg : g ≠ 0) :
    ∀ r : MvPolynomial (Fin 2) K, ¬ (bwQT K a b g).IsRoot r := by
  intro r hr
  have h0 : MvPolynomial.C (nrK K a b g) * r ^ 3 + nrA K a b * r ^ 2 + nrB K a b * r
      + nrD K a b = 0 := by
    simpa only [bwQT, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow] using hr
  exact nrK_mul_pow_add a b g hd hg r h0

/-- **The transported cubic is prime** (hence so is `bwASpoly a b g`). -/
theorem bwQT_prime (a b g : K) (hd : asDel a b ≠ 0) (hg : g ≠ 0) :
    Prime (bwQT K a b g) := by
  have hκ : nrK K a b g ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hg (asDel_sq_ne_zero a b hd))
  have hu : (MvPolynomial.C (nrK K a b g) : MvPolynomial (Fin 2) K) ≠ 0 :=
    C_ne_zero_two (K := K) hκ
  have hu' : (MvPolynomial.C ((nrK K a b g)⁻¹) : MvPolynomial (Fin 2) K) ≠ 0 :=
    C_ne_zero_two (K := K) (inv_ne_zero hκ)
  -- the monic rescaling
  have hc : (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g).coeff 3 = 1 := by
    rw [Polynomial.coeff_C_mul, bwQT_coeff_three, ← MvPolynomial.C_mul, inv_mul_cancel₀ hκ,
      MvPolynomial.C_1]
  have hnd : (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g).natDegree ≤ 3 := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_C, zero_add]
    exact bwQT_natDegree_le a b g
  have hmonic : (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one 3 hnd hc
  have hne : (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g) ≠ 0 :=
    hmonic.ne_zero
  have hdeg2 : 2 ≤ (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g).natDegree := by
    have h3 : 3 ≤ (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g).natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero)
    omega
  have hroot : ∀ r : MvPolynomial (Fin 2) K,
      ¬ (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g).IsRoot r := by
    intro r hr
    simp only [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_C] at hr
    rcases mul_eq_zero.mp hr with h | h
    · exact hu' h
    · exact bwQT_no_root a b g hd hg r h
  have hroots : (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g).roots = 0 :=
    Multiset.eq_zero_of_forall_notMem
      (fun r hr => hroot r ((Polynomial.mem_roots hne).mp hr))
  have hirr : Irreducible (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g) :=
    (Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic hdeg2 hnd).mpr hroots
  have hprimeScaled : Prime (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g) :=
    irreducible_iff_prime.mp hirr
  have huPC : IsUnit (Polynomial.C (MvPolynomial.C (nrK K a b g)) :
      Polynomial (MvPolynomial (Fin 2) K)) :=
    ⟨⟨Polynomial.C (MvPolynomial.C (nrK K a b g)),
      Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)),
      by rw [← Polynomial.C_mul, ← MvPolynomial.C_mul, mul_inv_cancel₀ hκ, MvPolynomial.C_1,
        Polynomial.C_1],
      by rw [← Polynomial.C_mul, ← MvPolynomial.C_mul, inv_mul_cancel₀ hκ, MvPolynomial.C_1,
        Polynomial.C_1]⟩, rfl⟩
  have hfac : bwQT K a b g
      = Polynomial.C (MvPolynomial.C (nrK K a b g))
        * (Polynomial.C (MvPolynomial.C ((nrK K a b g)⁻¹)) * bwQT K a b g) := by
    rw [← mul_assoc, ← Polynomial.C_mul, ← MvPolynomial.C_mul, mul_inv_cancel₀ hκ,
      MvPolynomial.C_1, Polynomial.C_1, one_mul]
  rw [hfac]
  exact (prime_isUnit_mul huPC).mpr hprimeScaled

/-- **`bwASpoly a b g` is prime.** -/
theorem bwASpoly_prime (a b g : K) (hd : asDel a b ≠ 0) (hg : g ≠ 0) :
    Prime (bwASpoly a b g) := by
  have h1 : Prime (bwQT K a b g) := bwQT_prime a b g hd hg
  rw [← bwTau_bwASpoly a b g] at h1
  exact (MulEquiv.prime_iff (Work.MotK.TGen.bwTau K)).mp h1

/-- **`bwASpoly a b g` is not a unit**: it vanishes at the origin, so it lies in the proper ideal
`ker (aeval 0)`. -/
theorem bwASpoly_not_isUnit (a b g : K) : ¬ IsUnit (bwASpoly a b g) := by
  intro hu
  have hmem : bwASpoly a b g
      ∈ RingHom.ker (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))) := by
    rw [RingHom.mem_ker, bwASpoly_decomp]
    simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    simp
  have htop := Ideal.eq_top_of_isUnit_mem _ hmem hu
  have h1 : (1 : MvPolynomial (Fin 3) K)
      ∈ RingHom.ker (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))) := by
    rw [htop]
    trivial
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

/-! ## §5.  The assembly -/

/-- **Every codimension-one point above the target chart denominator `bwVecAS2 · 4` is junk.** -/
theorem censusAS2_junk_bwVec4 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    ∀ x : Work.MotA.polySpec (RatFunc 𝕜) 3, Order.coheight x = 1 →
      bwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) 4 ∈ x.asIdeal →
        Work.MotV.JunkClass (RatFunc 𝕜) x := by
  intro x hcoh hmem
  have hd : (aK D) ^ 2 - (aK D) * (bK D) - (bK D) ^ 2 ≠ 0 := aK_sq_sub_ne D hD
  have hg : Work.MotV.fAS 𝕜 ≠ 0 := fAS_ne_zero
  have hprime : Prime (bwASpoly (aK D) (bK D) (Work.MotV.fAS 𝕜)) :=
    bwASpoly_prime _ _ _ hd hg
  have hspan : (Ideal.span {bwASpoly (aK D) (bK D) (Work.MotV.fAS 𝕜)} :
      Ideal (MvPolynomial (Fin 3) (RatFunc 𝕜))).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hheight : Ideal.height (Ideal.span {bwASpoly (aK D) (bK D) (Work.MotV.fAS 𝕜)} :
      Ideal (MvPolynomial (Fin 3) (RatFunc 𝕜))) = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hprime.ne_zero) hprime.not_isUnit
  have hmem' : bwASpoly (aK D) (bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal := by
    rw [← bwVecAS2_four_eq_bwASpoly (aK D) (bK D) (Work.MotV.fAS 𝕜)]
    exact hmem
  have hx : x.asIdeal = Ideal.span {bwASpoly (aK D) (bK D) (Work.MotV.fAS 𝕜)} := by
    haveI : x.asIdeal.IsPrime := x.isPrime
    exact Work.MotK.CensusPrime.eq_span_of_height_one _ hspan hheight x.asIdeal
      (by rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hcoh) hmem'
  have hxe : x = ⟨Ideal.span {bwASpoly (aK D) (bK D) (Work.MotV.fAS 𝕜)}, hspan⟩ :=
    PrimeSpectrum.ext hx
  rw [hxe]
  exact Work.MotK.junkClass_of_resF_ratFunc_ratFunc (RatFunc 𝕜) _
    (bwASpoly_fractionRing (aK D) (bK D) (Work.MotV.fAS 𝕜) hd hg hspan)

end Work.MotC5N3.BwAS
