import Mathlib
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.int_coords_and_norm

/-!
# `2b = a + a'x` and `a² + a'² = 4c` for `b` integral, `x² = -1`

Let `Kc = ℚ(√-30030)` (`Work.ClassFieldTower.Kc`), let `L` be a number field with a
`Kc`-algebra structure, and let `x ∈ 𝓞 L` satisfy `x * x = -1` and generate `L` over `Kc`
(`Algebra.adjoin Kc {x} = ⊤`).  Since `-1` is not a square in `Kc` (an elementary computation
with the `ℚ`-basis `{1, √-30030}`, done below), `x ∉ Kc`, so `L/Kc` is the quadratic extension
`Kc(x)` with `minpoly Kc x = X² + 1`, and `{1, x}` is a `Kc`-basis of `L`.

For every `b ∈ 𝓞 L` the trace/norm argument for a quadratic extension gives

`2b = a + a'x`   with   `a = Tr_{L/Kc}(b)`,   `a' = -Tr_{L/Kc}(b x)`,

and `a² + a'² = 4 N_{L/Kc}(b)`.  Since the trace and the norm of an integral element are
integral, `a`, `a'` and `c = N_{L/Kc}(b)` all lie in `𝓞 Kc` — which is the statement proved
here.  The traces and the norm are computed in the basis `{1, x}` (left multiplication by
`b = c₀ + c₁x` has matrix `[[c₀, -c₁], [c₁, c₀]]`, of trace `2c₀` and determinant `c₀² + c₁²`).

This is the linear step in `Work.ShafarevichKoch.no_sqrt_neg_one_in_maximalUnramified`: combined
with the parity lemma (`4 ∣ u² + u'² - 30030(v² + v'²)`, `2 ∣ uv + u'v'`) it shows that
`√-30030 · 𝓞 L ⊆ 𝓞 Kc + 𝓞 Kc·x`, i.e. that `√-30030` lies in the conductor of `𝓞 Kc[x]`.
-/

set_option linter.unusedVariables false

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower
open NumberField Polynomial
open scoped NumberField

/-! ## `-1` is not a square in `Kc = ℚ(√-30030)` -/

/-- **`-1` is not a square in `Kc = ℚ(√-30030)`.**

Since `{1, √-30030}` is a `ℚ`-basis of `Kc` with `(√-30030)² = -30030`, expanding
`(x + y√-30030)² = -1` gives `x² - 30030 y² = -1` and `2xy = 0`; the first branch is impossible
over `ℚ` and the second would make `30030` a rational square. -/
private theorem neg_one_not_isSquare_Kc_aux : ¬ ∃ w : Kc, w * w = -1 := by
  rintro ⟨w, hw⟩
  obtain ⟨x, y, hxy⟩ := Work.ClassFieldTower.exists_coords w
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

/-! ## The main statement -/

theorem exists_two_mul_eq_of_mem_ringOfIntegers
    {L : Type*} [Field L] [NumberField L] [Algebra Work.ClassFieldTower.Kc L]
    [FiniteDimensional Work.ClassFieldTower.Kc L]
    (x : NumberField.RingOfIntegers L)
    (hgen : Algebra.adjoin Work.ClassFieldTower.Kc
      ({algebraMap (NumberField.RingOfIntegers L) L x} : Set L) = ⊤)
    (hx : (algebraMap (NumberField.RingOfIntegers L) L x) * (algebraMap (NumberField.RingOfIntegers L) L x) = -1)
    (b : NumberField.RingOfIntegers L) :
    ∃ a a' c : NumberField.RingOfIntegers Work.ClassFieldTower.Kc,
      (2 : NumberField.RingOfIntegers L) * b
        = algebraMap (NumberField.RingOfIntegers Work.ClassFieldTower.Kc) (NumberField.RingOfIntegers L) a
          + algebraMap (NumberField.RingOfIntegers Work.ClassFieldTower.Kc) (NumberField.RingOfIntegers L) a' * x
      ∧ a ^ 2 + a' ^ 2 = 4 * c := by
  have hxL : (x : L) * (x : L) = -1 := hx
  have hgen' : Algebra.adjoin Kc ({(x : L)} : Set L) = ⊤ := hgen
  -- ### `x` is not in the image of `Kc`
  have hxKi : ¬ ∃ w : Kc, algebraMap Kc L w = (x : L) := by
    rintro ⟨w, hw⟩
    refine neg_one_not_isSquare_Kc_aux ⟨w, ?_⟩
    have h : algebraMap Kc L (w * w) = algebraMap Kc L (-1 : Kc) := by
      rw [map_mul, map_neg, map_one, hw, hxL]
    exact (algebraMap Kc L).injective h
  -- ### `x` is integral over `Kc`
  have hxK : IsIntegral Kc (x : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hxL]
    simpa using isIntegral_algebraMap (R := Kc) (A := L) (x := (-1 : Kc))
  -- ### the minimal polynomial of `x` is `X² + 1`
  have hmin : minpoly Kc (x : L) = (X : Kc[X]) ^ 2 + 1 := by
    have hirr : Irreducible ((X : Kc[X]) ^ 2 + 1) := by
      refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
      · have hdeg : ((X : Kc[X]) ^ 2 + 1).natDegree = 2 := by compute_degree!
        rw [hdeg]
        decide
      · intro w hw
        rw [Polynomial.IsRoot.def] at hw
        have h1 : w ^ 2 + 1 = 0 := by simpa using hw
        have h2 : w * w = -1 := by rw [pow_two] at h1; linear_combination h1
        exact neg_one_not_isSquare_Kc_aux ⟨w, h2⟩
    have hroot : (Polynomial.aeval (x : L)) ((X : Kc[X]) ^ 2 + 1) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      simp only [Polynomial.eval₂_one]
      rw [pow_two, hxL]
      ring
    have hmonic : ((X : Kc[X]) ^ 2 + 1).Monic := by
      have h := monic_X_pow_add_C (n := 2) (a := (1 : Kc)) (by norm_num)
      simpa using h
    exact (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
  -- ### `[L : Kc] = 2`
  have htop : IntermediateField.adjoin Kc ({(x : L)} : Set L) = (⊤ : IntermediateField Kc L) :=
    (IntermediateField.adjoin_eq_top_iff).mpr hgen'
  have hfr : Module.finrank Kc L = 2 := by
    have h1 : Module.finrank Kc ↥(IntermediateField.adjoin Kc ({(x : L)} : Set L)) = 2 := by
      rw [IntermediateField.adjoin.finrank hxK, hmin]
      compute_degree!
    rw [← IntermediateField.finrank_top' (F := Kc) (E := L), ← htop]
    exact h1
  -- ### `{1, x}` is a `Kc`-basis of `L`
  have hlin : LinearIndependent Kc ![(1 : L), (x : L)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have ht : t = 0 := by
      by_contra ht
      have h1 : algebraMap Kc L t * (x : L) = -(algebraMap Kc L s) := by
        have h2 : algebraMap Kc L s + algebraMap Kc L t * (x : L) = 0 := by
          simpa [Algebra.smul_def] using h
        linear_combination h2
      have htne : algebraMap Kc L t ≠ 0 :=
        fun hz => ht ((algebraMap Kc L).injective (by rw [hz, map_zero]))
      have h4 : (x : L) = -(algebraMap Kc L s) / (algebraMap Kc L t) := by
        rw [eq_div_iff htne, mul_comm]; exact h1
      exact hxKi ⟨-(s / t), by rw [h4, map_neg, map_div₀, neg_div]⟩
    subst ht
    constructor
    · have h2 : algebraMap Kc L s = 0 := by simpa [Algebra.smul_def] using h
      exact (algebraMap Kc L).injective (by rw [h2, map_zero])
    · rfl
  have hcard : Fintype.card (Fin 2) = Module.finrank Kc L := by rw [hfr]; simp
  set B : Module.Basis (Fin 2) Kc L :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hBdef
  have hB0 : B 0 = (1 : L) := by
    rw [hBdef, coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  have hB1 : B 1 = (x : L) := by
    rw [hBdef, coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  -- ### coordinates in the basis `{1, x}`
  have hrepr_pair (a c : Kc) : B.repr (a • (1 : L) + c • (x : L)) = ![a, c] := by
    have h : a • (1 : L) + c • (x : L) = ∑ i, ![a, c] i • B i := by
      rw [Fin.sum_univ_two, hB0, hB1]
      simp
    rw [h, Module.Basis.repr_sum_self]
  have hsum (y : L) : y = B.repr y 0 • (1 : L) + B.repr y 1 • (x : L) := by
    conv_lhs => rw [← B.sum_repr y]
    rw [Fin.sum_univ_two, hB0, hB1]
  have hmulx (a c : Kc) :
      (a • (1 : L) + c • (x : L)) * (x : L) = (-c) • (1 : L) + a • (x : L) := by
    simp only [add_mul, one_mul, Algebra.smul_mul_assoc, hxL]
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, RingHom.map_neg]
    ring
  have hrepr_mul_x (y : L) : B.repr (y * (x : L)) = ![-(B.repr y 1), B.repr y 0] := by
    have h1 : y * (x : L) = (-(B.repr y 1)) • (1 : L) + (B.repr y 0) • (x : L) := by
      conv_lhs => rw [hsum y]
      rw [hmulx]
    rw [h1, hrepr_pair]
  have h00 (y : L) : Algebra.leftMulMatrix B y 0 0 = B.repr y 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one]
  have h01 (y : L) : Algebra.leftMulMatrix B y 0 1 = -(B.repr y 1) := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hrepr_mul_x]
    simp
  have h10 (y : L) : Algebra.leftMulMatrix B y 1 0 = B.repr y 1 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hB0, mul_one]
  have h11 (y : L) : Algebra.leftMulMatrix B y 1 1 = B.repr y 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hB1, hrepr_mul_x]
    simp
  have hlm (y : L) :
      Algebra.leftMulMatrix B y = !![B.repr y 0, -(B.repr y 1); B.repr y 1, B.repr y 0] := by
    rw [Matrix.eta_fin_two (Algebra.leftMulMatrix B y), h00 y, h01 y, h10 y, h11 y]
  -- ### trace and norm in the basis `{1, x}`
  have htrace (y : L) : Algebra.trace Kc L y = 2 * B.repr y 0 := by
    rw [Algebra.trace_eq_matrix_trace B, hlm y, Matrix.trace_fin_two_of]
    ring
  have htrace_x (y : L) : Algebra.trace Kc L (y * (x : L)) = -(2 * B.repr y 1) := by
    rw [Algebra.trace_eq_matrix_trace B, hlm (y * (x : L)), Matrix.trace_fin_two_of, hrepr_mul_x]
    simp
    ring
  have hnorm (y : L) : Algebra.norm Kc y = (B.repr y 0) ^ 2 + (B.repr y 1) ^ 2 := by
    rw [Algebra.norm_eq_matrix_det B, hlm y, Matrix.det_fin_two_of]
    ring
  -- ### integrality of `b`, `x`, `b x` and of the trace and the norm
  have hIntb : IsIntegral ℤ (b : L) := RingOfIntegers.isIntegral_coe b
  have hxZ : IsIntegral ℤ (x : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hxL]
    simpa using isIntegral_algebraMap (R := ℤ) (A := L) (x := (-1 : ℤ))
  have hIntbx : IsIntegral ℤ ((b : L) * (x : L)) := hIntb.mul hxZ
  have htr : IsIntegral ℤ (Algebra.trace Kc L (b : L)) :=
    Algebra.isIntegral_trace (R := ℤ) (L := Kc) (F := L) hIntb
  have htr' : IsIntegral ℤ (Algebra.trace Kc L ((b : L) * (x : L))) :=
    Algebra.isIntegral_trace (R := ℤ) (L := Kc) (F := L) hIntbx
  have hnrm : IsIntegral ℤ (Algebra.norm Kc (b : L)) :=
    Algebra.isIntegral_norm (R := ℤ) (L := L) Kc hIntb
  obtain ⟨A, hA⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 Kc) (R := ℤ) (B := Kc)).mp htr
  obtain ⟨A', hA'⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 Kc) (R := ℤ) (B := Kc)).mp
    htr'.neg
  obtain ⟨C, hC⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 Kc) (R := ℤ) (B := Kc)).mp hnrm
  have key1L : (2 : L) * (b : L)
      = algebraMap Kc L (algebraMap (𝓞 Kc) Kc A)
        + algebraMap Kc L (algebraMap (𝓞 Kc) Kc A') * (x : L) := by
    rw [hA, hA', htrace, htrace_x]
    conv_lhs => rw [hsum (b : L)]
    simp only [Algebra.smul_def, mul_one, map_mul, map_ofNat, map_neg]
    ring
  refine ⟨A, A', C, ?_, ?_⟩
  · -- `2b = a + a'x`
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_ofNat, map_add, map_mul]
    rw [← IsScalarTower.algebraMap_apply (𝓞 Kc) (𝓞 L) L]
    rw [IsScalarTower.algebraMap_apply (𝓞 Kc) Kc L]
    exact key1L
  · -- `a² + a'² = 4c`
    apply RingOfIntegers.ext
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap (4 * C)]
    rw [map_add, map_pow, map_pow, map_mul, map_ofNat]
    rw [hA, hA', hC, htrace, htrace_x, hnorm]
    ring

end Work.ShafarevichKoch
