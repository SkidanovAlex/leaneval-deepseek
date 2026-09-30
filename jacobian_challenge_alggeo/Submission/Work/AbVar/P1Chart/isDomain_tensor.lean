/-
Area AV: the chart `D₊(Xᵢ)` of `P¹` is affine space.

`Work.AbVar.P1Chart.AX k i` is the degree-zero part of `k[X₀,X₁]` localised at `Xᵢ`.  We show
here that `AX k i` is the polynomial ring `↥(gr k 0)[T]` on the element
`t k i = X_{other i}/Xᵢ`, and deduce that for every field extension `K` of the degree-zero
part `↥(gr k 0)` the base change `AX k i ⊗ K` is a domain (indeed `≅ K[T]`), i.e. that the
chart is geometrically integral.
-/
import Mathlib
import Submission.Work.AbVar.P1Chart.Basic
import Submission.Work.AbVar.ProjectiveLine.chart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open HomogeneousLocalization MvPolynomial

set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

namespace Work.AbVar.P1Chart

noncomputable section

variable (k : Type*) [Field k]

/-- The coordinate ring `k[X₀,X₁]` of `P¹`. -/
abbrev K2 : Type _ := MvPolynomial (Fin 2) k

/-- `Xᵢⁿ` is homogeneous of degree `n` (for the standard grading by total degree). -/
lemma X_pow_mem_gr (i : Fin 2) (n : ℕ) :
    (MvPolynomial.X i : K2 k) ^ n ∈ gr k (n • 1) :=
  SetLike.pow_mem_graded n (X_mem k i)

/-- Two `Away.mk`'s with the same numerator and denominator degree are equal. -/
lemma awayMk_congr {i : Fin 2} {n m : ℕ} {x y : K2 k}
    (hx : x ∈ gr k (n • 1)) (hy : y ∈ gr k (m • 1)) (hn : n = m) (hxy : x = y) :
    Away.mk (gr k) (X_mem k i) n x hx = Away.mk (gr k) (X_mem k i) m y hy := by
  apply HomogeneousLocalization.val_injective (𝒜 := gr k)
    (x := Submonoid.powers (MvPolynomial.X i))
  rw [Away.val_mk, Away.val_mk, hn, hxy]

/-- `Xᵢⁿ / Xᵢⁿ = 1` in the chart ring. -/
lemma away_mk_pow_self (i : Fin 2) (n : ℕ) :
    Away.mk (gr k) (X_mem k i) n (((MvPolynomial.X i : K2 k)) ^ n) (X_pow_mem_gr k i n) = 1 := by
  apply HomogeneousLocalization.val_injective (𝒜 := gr k)
    (x := Submonoid.powers (MvPolynomial.X i))
  rw [Away.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self
    (⟨((MvPolynomial.X i : K2 k)) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (MvPolynomial.X i))

/-- `t k i = X_{other i} / Xᵢ` is `awayU i (other i)`. -/
lemma t_eq_awayU (i : Fin 2) :
    t k i = Work.AbVar.ProjectiveLine.awayU (R := k) i (other i) := rfl

/-- `Xᵢⁿ · X_j / Xᵢ^{n+1} = X_j/Xᵢ` in the chart ring, `j = other i`. -/
lemma away_mk_pow_mul_other (i : Fin 2) (n : ℕ) :
    Away.mk (gr k) (X_mem k i) (n + 1)
        (((MvPolynomial.X i : K2 k)) ^ n * (MvPolynomial.X (other i) : K2 k))
        (by
          have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded n (X_mem k i))
            (X_mem k (other i))
          simpa [nsmul_eq_mul] using h) = t k i := by
  apply HomogeneousLocalization.val_injective (𝒜 := gr k)
    (x := Submonoid.powers (MvPolynomial.X i))
  rw [Away.val_mk, t_eq_awayU, Work.AbVar.ProjectiveLine.awayU_val,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq']
  simp [pow_succ, mul_comm, mul_assoc]

/-- The four generators `Xᵢⁿ X_j^m / Xᵢ^{n+m}` with `n,m ≤ 1` are `1` or `t`. -/
lemma away_case (i : Fin 2) {n m : ℕ} (hn : n ≤ 1) (hm : m ≤ 1)
    (hx : ((MvPolynomial.X i : K2 k)) ^ n * (MvPolynomial.X (other i) : K2 k) ^ m
      ∈ gr k ((n + m) • 1)) :
    (Away.mk (gr k) (X_mem k i) (n + m)
        (((MvPolynomial.X i : K2 k)) ^ n * (MvPolynomial.X (other i) : K2 k) ^ m) hx = 1) ∨
      (Away.mk (gr k) (X_mem k i) (n + m)
        (((MvPolynomial.X i : K2 k)) ^ n * (MvPolynomial.X (other i) : K2 k) ^ m) hx = t k i) := by
  obtain (rfl | rfl) : n = 0 ∨ n = 1 := by omega
  · obtain (rfl | rfl) : m = 0 ∨ m = 1 := by omega
    · -- (0,0)
      left
      have hy := X_pow_mem_gr k i 0
      have hc : Away.mk (gr k) (X_mem k i) (0 + 0)
            (((MvPolynomial.X i : K2 k)) ^ 0 * (MvPolynomial.X (other i) : K2 k) ^ 0) hx
          = Away.mk (gr k) (X_mem k i) 0 ((MvPolynomial.X i : K2 k) ^ 0) hy := by
        apply awayMk_congr (hx := hx) (hy := hy) (hn := rfl)
        show ((MvPolynomial.X i : K2 k)) ^ 0 * (MvPolynomial.X (other i) : K2 k) ^ 0
          = ((MvPolynomial.X i : K2 k)) ^ 0
        simp only [pow_zero, mul_one]
      rw [hc]
      exact away_mk_pow_self k i 0
    · -- (0,1)
      right
      have hy : ((MvPolynomial.X i : K2 k)) ^ 0 * (MvPolynomial.X (other i) : K2 k)
          ∈ gr k ((0 + 1) • 1) := by
        have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded 0 (X_mem k i))
          (X_mem k (other i))
        have hidx : (0 : ℕ) • 1 + 1 = (0 + 1) • 1 := by norm_num
        rwa [hidx] at h
      have hc : Away.mk (gr k) (X_mem k i) (0 + 1)
            (((MvPolynomial.X i : K2 k)) ^ 0 * (MvPolynomial.X (other i) : K2 k) ^ 1) hx
          = Away.mk (gr k) (X_mem k i) (0 + 1)
            (((MvPolynomial.X i : K2 k)) ^ 0 * (MvPolynomial.X (other i) : K2 k)) hy := by
        apply awayMk_congr (hx := hx) (hy := hy) (hn := rfl)
        show ((MvPolynomial.X i : K2 k)) ^ 0 * (MvPolynomial.X (other i) : K2 k) ^ 1
          = ((MvPolynomial.X i : K2 k)) ^ 0 * (MvPolynomial.X (other i) : K2 k)
        simp only [pow_zero, pow_one, one_mul]
      rw [hc]
      exact away_mk_pow_mul_other k i 0
  · obtain (rfl | rfl) : m = 0 ∨ m = 1 := by omega
    · -- (1,0)
      left
      have hy := X_pow_mem_gr k i 1
      have hc : Away.mk (gr k) (X_mem k i) (1 + 0)
            (((MvPolynomial.X i : K2 k)) ^ 1 * (MvPolynomial.X (other i) : K2 k) ^ 0) hx
          = Away.mk (gr k) (X_mem k i) 1 ((MvPolynomial.X i : K2 k) ^ 1) hy := by
        apply awayMk_congr (hx := hx) (hy := hy) (hn := rfl)
        show ((MvPolynomial.X i : K2 k)) ^ 1 * (MvPolynomial.X (other i) : K2 k) ^ 0
          = ((MvPolynomial.X i : K2 k)) ^ 1
        simp only [pow_zero, pow_one, mul_one]
      rw [hc]
      exact away_mk_pow_self k i 1
    · -- (1,1)
      right
      have hy : ((MvPolynomial.X i : K2 k)) ^ 1 * (MvPolynomial.X (other i) : K2 k)
          ∈ gr k ((1 + 1) • 1) := by
        have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded 1 (X_mem k i))
          (X_mem k (other i))
        have hidx : (1 : ℕ) • 1 + 1 = (1 + 1) • 1 := by norm_num
        rwa [hidx] at h
      have hc : Away.mk (gr k) (X_mem k i) (1 + 1)
            (((MvPolynomial.X i : K2 k)) ^ 1 * (MvPolynomial.X (other i) : K2 k) ^ 1) hx
          = Away.mk (gr k) (X_mem k i) (1 + 1)
            (((MvPolynomial.X i : K2 k)) ^ 1 * (MvPolynomial.X (other i) : K2 k)) hy := by
        apply awayMk_congr (hx := hx) (hy := hy) (hn := rfl)
        show ((MvPolynomial.X i : K2 k)) ^ 1 * (MvPolynomial.X (other i) : K2 k) ^ 1
          = ((MvPolynomial.X i : K2 k)) ^ 1 * (MvPolynomial.X (other i) : K2 k)
        simp only [pow_one]
      rw [hc]
      exact away_mk_pow_mul_other k i 1

/-- In `k[X₀,X₁]`, the degree-zero part of `constToZeroEquiv` is `C`. -/
lemma algebraMap_constToZero (a : k) :
    algebraMap ↥(gr k 0) (K2 k) (Work.AbVar.ProjectiveLine.constToZeroEquiv a)
      = MvPolynomial.C a := by
  rw [Work.AbVar.ProjectiveLine.constToZeroEquiv_apply]
  rfl

/-- The generators `X₀, X₁` generate `k[X₀,X₁]` over the degree-zero part. -/
lemma adjoin_range_X_gr :
    Algebra.adjoin ↥(gr k 0) (Set.range (fun j : Fin 2 => (MvPolynomial.X j : K2 k))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine MvPolynomial.induction_on (p := x) ?_ ?_ ?_
  · intro a
    rw [show MvPolynomial.C a = algebraMap ↥(gr k 0) (K2 k)
        (Work.AbVar.ProjectiveLine.constToZeroEquiv a) from (algebraMap_constToZero k a).symm]
    exact Subalgebra.algebraMap_mem _ _
  · intro p q hp hq
    exact add_mem hp hq
  · intro p n hp
    exact mul_mem hp (Algebra.subset_adjoin ⟨n, rfl⟩)

/-- Every generator `(∏ X_j^{a_j}) / Xᵢ^a` lies in the range of `aeval (t k i)`. -/
lemma mk_prod_mem_range (i : Fin 2) {a : ℕ} {ai : Fin 2 → ℕ}
    (hai : ∑ j, ai j • (1 : ℕ) = a • (1 : ℕ)) (h : ∀ j, ai j ≤ 1)
    (hx : (∏ j : Fin 2, (MvPolynomial.X j : K2 k) ^ ai j) ∈ gr k (a • 1)) :
    Away.mk (gr k) (X_mem k i) a (∏ j : Fin 2, (MvPolynomial.X j : K2 k) ^ ai j) hx ∈
      (Polynomial.aeval (t k i) : Polynomial ↥(gr k 0) →ₐ[↥(gr k 0)] AX k i).range := by
  have hsum2 : ai 0 + ai 1 = a := by
    have hh := hai
    simp only [Fin.sum_univ_two, nsmul_eq_mul, mul_one] at hh
    exact hh
  have hsum : a = ai i + ai (other i) := by
    rw [← hsum2]
    fin_cases i <;> simp [other] <;> omega
  have hprod : (∏ j : Fin 2, (MvPolynomial.X j : K2 k) ^ ai j)
      = (MvPolynomial.X i : K2 k) ^ (ai i) * (MvPolynomial.X (other i) : K2 k) ^ (ai (other i)) := by
    rw [Fin.prod_univ_two]
    fin_cases i <;> simp [other, mul_comm]
  have hy : (MvPolynomial.X i : K2 k) ^ (ai i) * (MvPolynomial.X (other i) : K2 k) ^ (ai (other i))
      ∈ gr k ((ai i + ai (other i)) • 1) := by
    have hh := SetLike.mul_mem_graded (SetLike.pow_mem_graded (ai i) (X_mem k i))
      (SetLike.pow_mem_graded (ai (other i)) (X_mem k (other i)))
    have hidx : (ai i) • 1 + (ai (other i)) • 1 = (ai i + ai (other i)) • 1 :=
      (add_smul _ _ (1 : ℕ)).symm
    rwa [hidx] at hh
  have hcongr : Away.mk (gr k) (X_mem k i) a
        (∏ j : Fin 2, (MvPolynomial.X j : K2 k) ^ ai j) hx
      = Away.mk (gr k) (X_mem k i) (ai i + ai (other i))
        ((MvPolynomial.X i : K2 k) ^ (ai i) * (MvPolynomial.X (other i) : K2 k) ^ (ai (other i))) hy :=
    awayMk_congr (i := i) (n := a) (m := ai i + ai (other i))
      (x := ∏ j : Fin 2, (MvPolynomial.X j : K2 k) ^ ai j)
      (y := (MvPolynomial.X i : K2 k) ^ (ai i) * (MvPolynomial.X (other i) : K2 k) ^ (ai (other i)))
      (hx := hx) (hy := hy) (hn := hsum) (hxy := hprod)
  rw [hcongr]
  rcases away_case k i (h i) (h (other i)) hy with h1 | h1
  · rw [h1]
    exact ⟨1, map_one _⟩
  · rw [h1]
    exact ⟨Polynomial.X, Polynomial.aeval_X _⟩

/-- The chart ring `AX k i` is generated as a `↥(gr k 0)`-algebra by `t k i`. -/
theorem aeval_t_surj (i : Fin 2) :
    Function.Surjective (Polynomial.aeval (t k i) :
      Polynomial ↥(gr k 0) →ₐ[↥(gr k 0)] AX k i) := by
  have hkey := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top (𝒜 := gr k)
    (X_mem k i) (Fin 2) (fun j : Fin 2 => (MvPolynomial.X j : K2 k)) (adjoin_range_X_gr k)
    (fun _ => 1) (fun j => X_mem k j)
  have htop : (⊤ : Subalgebra ↥(gr k 0) (AX k i))
      ≤ (Polynomial.aeval (t k i) : Polynomial ↥(gr k 0) →ₐ[↥(gr k 0)] AX k i).range := by
    rw [← hkey, Algebra.adjoin_le_iff]
    rintro z ⟨a, ai, hai, hai', rfl⟩
    exact mk_prod_mem_range k i hai hai' _
  intro y
  exact htop trivial

/-- The two algebra structures agree on the constants of the chart ring. -/
lemma algmap_agree (i : Fin 2) (a : ↥(gr k 0)) :
    algebraMap ↥(gr k 0) (AX k i) a
      = algebraMap k (Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i))
          (Work.AbVar.ProjectiveLine.constToZeroEquiv.symm a) := by
  rw [HomogeneousLocalization.algebraMap_eq, Work.AbVar.ProjectiveLine.algebraMap_awayAlg,
    Work.AbVar.ProjectiveLine.awayAlg, RingHom.comp_apply,
    ← Work.AbVar.ProjectiveLine.constToZeroEquiv_apply, RingEquiv.apply_symm_apply]

/-- The comparison of `aeval t` with the explicit retraction `polyToAway` on monomials. -/
lemma aeval_t_monomial (i : Fin 2) (n : ℕ) (a : ↥(gr k 0)) :
    (Polynomial.aeval (t k i) : Polynomial ↥(gr k 0) →ₐ[↥(gr k 0)] AX k i)
        (Polynomial.monomial n a)
      = (Work.AbVar.ProjectiveLine.polyToAway (R := k) i (other i))
          (Polynomial.map ((Work.AbVar.ProjectiveLine.constToZeroEquiv (R := k)).symm :
            ↥(gr k 0) →+* k) (Polynomial.monomial n a)) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  rw [map_mul, map_pow, Polynomial.map_mul, Polynomial.map_pow, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.map_C, Polynomial.map_X,
    Work.AbVar.ProjectiveLine.polyToAway_C, Work.AbVar.ProjectiveLine.polyToAway_X,
    algmap_agree]
  rfl

/-- `aeval (t k i)` factors through the polynomial ring over `k` via the transpose of
`constToZeroEquiv`. -/
lemma aeval_t_apply (i : Fin 2) (p : Polynomial ↥(gr k 0)) :
    (Polynomial.aeval (t k i) : Polynomial ↥(gr k 0) →ₐ[↥(gr k 0)] AX k i) p
      = (Work.AbVar.ProjectiveLine.polyToAway (R := k) i (other i))
          (Polynomial.map ((Work.AbVar.ProjectiveLine.constToZeroEquiv (R := k)).symm :
            ↥(gr k 0) →+* k) p) := by
  induction p using Polynomial.induction_on' with
  | monomial n a => exact aeval_t_monomial k i n a
  | add p q hp hq => rw [map_add, Polynomial.map_add, map_add, hp, hq]

/-- `t k i` is transcendental over `↥(gr k 0)`. -/
theorem aeval_t_inj (i : Fin 2) :
    Function.Injective (Polynomial.aeval (t k i) :
      Polynomial ↥(gr k 0) →ₐ[↥(gr k 0)] AX k i) := by
  intro p q hpq
  rw [aeval_t_apply k i p, aeval_t_apply k i q] at hpq
  exact Polynomial.map_injective
    ((Work.AbVar.ProjectiveLine.constToZeroEquiv (R := k)).symm : ↥(gr k 0) →+* k)
    (RingEquiv.injective _)
    (Work.AbVar.ProjectiveLine.polyToAway_injective (i := i) (j := other i) (other_ne i) hpq)

/-- The chart ring is a polynomial ring over the degree-zero part. -/
theorem nonempty_algEquiv (i : Fin 2) :
    Nonempty (AX k i ≃ₐ[↥(gr k 0)] Polynomial ↥(gr k 0)) :=
  ⟨(AlgEquiv.ofBijective _ ⟨aeval_t_inj k i, aeval_t_surj k i⟩).symm⟩

/-- `Polynomial R ⊗[R] K` is the polynomial ring `K[T]`, hence a domain. -/
theorem isDomain_polynomial_tensor (K : Type*) [Field K] [Algebra ↥(gr k 0) K] :
    IsDomain (TensorProduct ↥(gr k 0) (Polynomial ↥(gr k 0)) K) := by
  have e : TensorProduct ↥(gr k 0) (Polynomial ↥(gr k 0)) K
      ≃ₐ[↥(gr k 0)] Polynomial K :=
    (Algebra.TensorProduct.comm ↥(gr k 0) (Polynomial ↥(gr k 0)) K).trans
      (polyEquivTensor ↥(gr k 0) K).symm
  exact e.toMulEquiv.isDomain (Polynomial K)

theorem isDomain_tensor (k : Type*) [Field k] (i : Fin 2) (K : Type*) [Field K]
    [Algebra ↥(Work.AbVar.P1Chart.gr k 0) K] :
    IsDomain (TensorProduct ↥(Work.AbVar.P1Chart.gr k 0) (Work.AbVar.P1Chart.AX k i) K) := by
  obtain ⟨e⟩ := nonempty_algEquiv k i
  haveI : IsDomain (TensorProduct ↥(Work.AbVar.P1Chart.gr k 0)
      (Polynomial ↥(Work.AbVar.P1Chart.gr k 0)) K) := isDomain_polynomial_tensor k K
  exact (Algebra.TensorProduct.congr (S := ↥(Work.AbVar.P1Chart.gr k 0)) e
    (AlgEquiv.refl (R := ↥(Work.AbVar.P1Chart.gr k 0)) (A₁ := K))).toMulEquiv.isDomain
    (TensorProduct ↥(Work.AbVar.P1Chart.gr k 0)
      (Polynomial ↥(Work.AbVar.P1Chart.gr k 0)) K)

end

end Work.AbVar.P1Chart
