import Mathlib

set_option linter.style.haveILetI false

namespace Commons.Algebra.Lie.Casimir

open scoped TensorProduct BigOperators

/-- If `b` is a basis of `L` and `b'` is a family with `B (b i) (b' j) = δᵢⱼ`, then
every `v : L` is the sum `∑ j, B v (b' j) • b j`. -/
lemma repr_dual {K L ι : Type*} [Field K] [AddCommGroup L] [Module K L]
    [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (b : Module.Basis ι K L) (b' : ι → L)
    (hb : ∀ i j, B (b i) (b' j) = if i = j then 1 else 0) (v : L) :
    v = ∑ j, B v (b' j) • b j := by
  set w := v - ∑ j, B v (b' j) • b j with hwdef
  have hwB : ∀ k, B w (b' k) = 0 := by
    intro k
    rw [hwdef]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, hb, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hrepr : w = ∑ j, (b.repr w) j • b j := (b.sum_repr w).symm
  have hzero : ∀ k, (b.repr w) k = 0 := by
    intro k
    have h1 : B w (b' k) = (b.repr w) k := by
      rw [hrepr]
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, hb, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    rw [← h1]
    exact hwB k
  have hw0 : w = 0 := by rw [hrepr]; simp [hzero]
  rw [hwdef] at hw0
  exact sub_eq_zero.mp hw0

/-- If `b` is a basis of `L` and `b'` is a family with `B (b' i) (b j) = δᵢⱼ` (and
`B (b i) (b' j) = δᵢⱼ`), then every `v : L` is the sum `∑ j, B v (b j) • b' j`. -/
lemma repr_dual' {K L ι : Type*} [Field K] [AddCommGroup L] [Module K L]
    [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (b : Module.Basis ι K L) (b' : ι → L)
    (hb : ∀ i j, B (b i) (b' j) = if i = j then 1 else 0)
    (hb' : ∀ i j, B (b' i) (b j) = if i = j then 1 else 0) (v : L) :
    v = ∑ j, B v (b j) • b' j := by
  set w := v - ∑ j, B v (b j) • b' j with hwdef
  have hwB : ∀ k, B w (b k) = 0 := by
    intro k
    rw [hwdef]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    rw [map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, hb', smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hwB' : ∀ k, B w (b' k) = 0 := by
    intro k
    rw [show b' k = ∑ j, (b.repr (b' k)) j • b j from (b.sum_repr (b' k)).symm]
    rw [map_sum]
    simp only [map_smul, hwB, smul_eq_mul, mul_zero, Finset.sum_const_zero]
  have hrepr : w = ∑ j, (b.repr w) j • b j := (b.sum_repr w).symm
  have hzero : ∀ k, (b.repr w) k = 0 := by
    intro k
    have h1 : B w (b' k) = (b.repr w) k := by
      rw [hrepr]
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, hb, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    rw [← h1]
    exact hwB' k
  have hw0 : w = 0 := by rw [hrepr]; simp [hzero]
  rw [hwdef] at hw0
  exact sub_eq_zero.mp hw0

theorem lie_commute {K L ι : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K L) (hBsym : B.IsSymm) (hBinv : B.lieInvariant L)
    (b : Module.Basis ι K L) (b' : ι → L)
    (hb : ∀ i j, B (b i) (b' j) = if i = j then 1 else 0)
    (hb' : ∀ i j, B (b' i) (b j) = if i = j then 1 else 0)
    (x : L) :
    (UniversalEnvelopingAlgebra.ι K x)
        * (∑ i, (UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K (b' i)))
      = (∑ i, (UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K (b' i)))
        * (UniversalEnvelopingAlgebra.ι K x) := by
  letI : LieRing (UniversalEnvelopingAlgebra K L) := LieRing.ofAssociativeRing
  set C := ∑ i, (UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K (b' i))
    with hCdef
  -- per-term commutator identity
  have hterm : ∀ i, (UniversalEnvelopingAlgebra.ι K x)
        * ((UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K (b' i)))
      - ((UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K (b' i)))
        * (UniversalEnvelopingAlgebra.ι K x)
      = (UniversalEnvelopingAlgebra.ι K ⁅x, b i⁆) * (UniversalEnvelopingAlgebra.ι K (b' i))
        + (UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K ⁅x, b' i⁆) := by
    intro i
    have h1 : UniversalEnvelopingAlgebra.ι K ⁅x, b i⁆
        = (UniversalEnvelopingAlgebra.ι K x) * (UniversalEnvelopingAlgebra.ι K (b i))
          - (UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K x) := by
      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
    have h2 : UniversalEnvelopingAlgebra.ι K ⁅x, b' i⁆
        = (UniversalEnvelopingAlgebra.ι K x) * (UniversalEnvelopingAlgebra.ι K (b' i))
          - (UniversalEnvelopingAlgebra.ι K (b' i)) * (UniversalEnvelopingAlgebra.ι K x) := by
      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
    rw [h1, h2]
    noncomm_ring
  -- Step 1
  have hstep1 : (UniversalEnvelopingAlgebra.ι K x) * C - C * (UniversalEnvelopingAlgebra.ι K x)
      = ∑ i, ((UniversalEnvelopingAlgebra.ι K ⁅x, b i⁆) * (UniversalEnvelopingAlgebra.ι K (b' i))
          + (UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K ⁅x, b' i⁆)) := by
    rw [hCdef, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hterm i
  -- expansions
  have hS1 : (∑ i, (UniversalEnvelopingAlgebra.ι K ⁅x, b i⁆) * (UniversalEnvelopingAlgebra.ι K (b' i)))
      = ∑ i, ∑ j, B ⁅x, b i⁆ (b' j)
          • ((UniversalEnvelopingAlgebra.ι K (b j)) * (UniversalEnvelopingAlgebra.ι K (b' i))) := by
    apply Finset.sum_congr rfl
    intro i _
    have hexp : UniversalEnvelopingAlgebra.ι K ⁅x, b i⁆
        = ∑ j, B ⁅x, b i⁆ (b' j) • UniversalEnvelopingAlgebra.ι K (b j) := by
      conv_lhs => rw [repr_dual B b b' hb ⁅x, b i⁆]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
    rw [hexp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_mul_assoc]
  have hS2 : (∑ i, (UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K ⁅x, b' i⁆))
      = ∑ i, ∑ j, B ⁅x, b' j⁆ (b i)
          • ((UniversalEnvelopingAlgebra.ι K (b j)) * (UniversalEnvelopingAlgebra.ι K (b' i))) := by
    have h2a : (∑ i, (UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K ⁅x, b' i⁆))
        = ∑ i, ∑ j, B ⁅x, b' i⁆ (b j)
            • ((UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K (b' j))) := by
      apply Finset.sum_congr rfl
      intro i _
      have hexp : UniversalEnvelopingAlgebra.ι K ⁅x, b' i⁆
          = ∑ j, B ⁅x, b' i⁆ (b j) • UniversalEnvelopingAlgebra.ι K (b' j) := by
        conv_lhs => rw [repr_dual' B b b' hb hb' ⁅x, b' i⁆]
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
      rw [hexp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_smul_comm]
    rw [h2a, Finset.sum_comm]
  -- cancellation of coefficients
  have hcancel : ∀ i j, B ⁅x, b i⁆ (b' j) + B ⁅x, b' j⁆ (b i) = 0 := by
    intro i j
    rw [hBinv x (b i) (b' j), hBsym.eq (b i) ⁅x, b' j⁆]
    ring
  have hstep2 : (∑ i, ((UniversalEnvelopingAlgebra.ι K ⁅x, b i⁆) * (UniversalEnvelopingAlgebra.ι K (b' i))
          + (UniversalEnvelopingAlgebra.ι K (b i)) * (UniversalEnvelopingAlgebra.ι K ⁅x, b' i⁆))) = 0 := by
    rw [Finset.sum_add_distrib, hS1, hS2, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    rw [← add_smul, hcancel i j, zero_smul]
  have : (UniversalEnvelopingAlgebra.ι K x) * C - C * (UniversalEnvelopingAlgebra.ι K x) = 0 := by
    rw [hstep1, hstep2]
  exact sub_eq_zero.mp this

end Commons.Algebra.Lie.Casimir
