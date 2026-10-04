import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

/-- **Double sum of an antisymmetric matrix vanishes.**

For a finite index type `ι` and `g : ι → ι → ℝ` with `g i j + g j i = 0` for all `i j`,
the total double sum `∑ i, ∑ j, g i j` is zero: reindex `ι × ι` by the swap involution
`(i,j) ↦ (j,i)`, under which every term becomes its own negative. -/
private lemma sum_antisymm_zero' {ι : Type*} [Fintype ι] (g : ι → ι → ℝ)
    (hg : ∀ i j, g i j + g j i = 0) : ∑ i, ∑ j, g i j = 0 := by
  have h1 : (∑ i, ∑ j, g i j) = ∑ p : ι × ι, g p.1 p.2 := by
    rw [Fintype.sum_prod_type]
  have h2 : (∑ p : ι × ι, g p.1 p.2) = ∑ p : ι × ι, g p.2 p.1 := by
    symm
    exact Equiv.sum_comp (Equiv.prodComm ι ι) (fun p : ι × ι => g p.1 p.2)
  have h3 : (∑ p : ι × ι, g p.2 p.1) = - ∑ p : ι × ι, g p.1 p.2 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    linarith [hg p.1 p.2]
  linarith [h1, h2, h3]

/-- **Antisymmetric matrix paired against a symmetric one sums to zero.**

If `ω i j + ω j i = 0` and `H i j = H j i` for all `i j`, then `∑ i, ∑ j, ω i j * H i j = 0`.
Indeed the summand `g i j = ω i j * H i j` is antisymmetric, so `sum_antisymm_zero'` applies. -/
private lemma double_sum_antisymm_mul_symm {ι : Type*} [Fintype ι]
    (ω H : ι → ι → ℝ) (hω : ∀ i j, ω i j + ω j i = 0)
    (hH : ∀ i j, H i j = H j i) : ∑ i, ∑ j, ω i j * H i j = 0 := by
  refine sum_antisymm_zero' (fun i j => ω i j * H i j) ?_
  intro i j
  have hω' : ω j i = - ω i j := by linarith [hω i j]
  rw [hω', hH j i]
  ring

theorem curvForm_pair_sum_zero {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (T : V → V → V → V → ℝ)
    (h1 : ∀ (r s : ℝ) (a₁ a₂ b c d : V),
      T (r • a₁ + s • a₂) b c d = r * T a₁ b c d + s * T a₂ b c d)
    (h2 : ∀ (r s : ℝ) (a b₁ b₂ c d : V),
      T a (r • b₁ + s • b₂) c d = r * T a b₁ c d + s * T a b₂ c d)
    (h3 : ∀ (r s : ℝ) (a b c₁ c₂ d : V),
      T a b (r • c₁ + s • c₂) d = r * T a b c₁ d + s * T a b c₂ d)
    (h4 : ∀ (r s : ℝ) (a b c d₁ d₂ : V),
      T a b c (r • d₁ + s • d₂) = r * T a b c d₁ + s * T a b c d₂)
    (h12 : ∀ a b c d : V, T a b c d + T b a c d = 0)
    (h34 : ∀ a b c d : V, T a b c d + T a b d c = 0)
    (hpe : ∀ a b c d : V, T a b c d = T c d a b)
    (e : Fin n → V) (X : Fin n → V) (ω : Fin n → Fin n → ℝ)
    (hX : ∀ i, X i = ∑ p, ω i p • e p) (hanti : ∀ i p, ω i p + ω p i = 0) :
    ∑ i, ∑ j, (T (X i) (e j) (e i) (e j) + T (e i) (X j) (e i) (e j)
        + T (e i) (e j) (X i) (e j) + T (e i) (e j) (e i) (X j)) = 0 := by
  -- Slotwise additivity / homogeneity, extracted from `h1`–`h4`.
  have hAdd1 : ∀ a₁ a₂ b c d : V, T (a₁ + a₂) b c d = T a₁ b c d + T a₂ b c d := by
    intro a₁ a₂ b c d; simpa using h1 1 1 a₁ a₂ b c d
  have hSmul1 : ∀ (r : ℝ) (a b c d : V), T (r • a) b c d = r * T a b c d := by
    intro r a b c d; simpa using h1 r 0 a a b c d
  have hAdd2 : ∀ a b₁ b₂ c d : V, T a (b₁ + b₂) c d = T a b₁ c d + T a b₂ c d := by
    intro a b₁ b₂ c d; simpa using h2 1 1 a b₁ b₂ c d
  have hSmul2 : ∀ (r : ℝ) (a b c d : V), T a (r • b) c d = r * T a b c d := by
    intro r a b c d; simpa using h2 r 0 a b b c d
  have hAdd3 : ∀ a b c₁ c₂ d : V, T a b (c₁ + c₂) d = T a b c₁ d + T a b c₂ d := by
    intro a b c₁ c₂ d; simpa using h3 1 1 a b c₁ c₂ d
  have hSmul3 : ∀ (r : ℝ) (a b c d : V), T a b (r • c) d = r * T a b c d := by
    intro r a b c d; simpa using h3 r 0 a b c c d
  have hAdd4 : ∀ a b c d₁ d₂ : V, T a b c (d₁ + d₂) = T a b c d₁ + T a b c d₂ := by
    intro a b c d₁ d₂; simpa using h4 1 1 a b c d₁ d₂
  have hSmul4 : ∀ (r : ℝ) (a b c d : V), T a b c (r • d) = r * T a b c d := by
    intro r a b c d; simpa using h4 r 0 a b c d d
  -- Expansion of a finite linear combination in each of the four slots.
  have hexp1 : ∀ (f : Fin n → ℝ) (b c d : V),
      T (∑ p, f p • e p) b c d = ∑ p, f p * T (e p) b c d := by
    intro f b c d
    let φ : V →ₗ[ℝ] ℝ :=
      { toFun := fun a => T a b c d
        map_add' := fun x y => hAdd1 x y b c d
        map_smul' := fun r x => by
          simp only [hSmul1, smul_eq_mul, RingHom.id_apply] }
    have h := map_sum φ (fun p => f p • e p) Finset.univ
    simp only [map_smul, smul_eq_mul] at h
    exact h
  have hexp2 : ∀ (f : Fin n → ℝ) (a c d : V),
      T a (∑ p, f p • e p) c d = ∑ p, f p * T a (e p) c d := by
    intro f a c d
    let φ : V →ₗ[ℝ] ℝ :=
      { toFun := fun b => T a b c d
        map_add' := fun x y => hAdd2 a x y c d
        map_smul' := fun r x => by
          simp only [hSmul2, smul_eq_mul, RingHom.id_apply] }
    have h := map_sum φ (fun p => f p • e p) Finset.univ
    simp only [map_smul, smul_eq_mul] at h
    exact h
  have hexp3 : ∀ (f : Fin n → ℝ) (a b d : V),
      T a b (∑ p, f p • e p) d = ∑ p, f p * T a b (e p) d := by
    intro f a b d
    let φ : V →ₗ[ℝ] ℝ :=
      { toFun := fun c => T a b c d
        map_add' := fun x y => hAdd3 a b x y d
        map_smul' := fun r x => by
          simp only [hSmul3, smul_eq_mul, RingHom.id_apply] }
    have h := map_sum φ (fun p => f p • e p) Finset.univ
    simp only [map_smul, smul_eq_mul] at h
    exact h
  have hexp4 : ∀ (f : Fin n → ℝ) (a b c : V),
      T a b c (∑ p, f p • e p) = ∑ p, f p * T a b c (e p) := by
    intro f a b c
    let φ : V →ₗ[ℝ] ℝ :=
      { toFun := fun d => T a b c d
        map_add' := fun x y => hAdd4 a b c x y
        map_smul' := fun r x => by
          simp only [hSmul4, smul_eq_mul, RingHom.id_apply] }
    have h := map_sum φ (fun p => f p • e p) Finset.univ
    simp only [map_smul, smul_eq_mul] at h
    exact h
  -- `X i` written as the finite combination `∑ p, ω i p • e p` in each slot.
  have hX1 : ∀ (i : Fin n) (b c d : V), T (X i) b c d = ∑ p, ω i p * T (e p) b c d := by
    intro i b c d; rw [hX i]; exact hexp1 (fun p => ω i p) b c d
  have hX2 : ∀ (i : Fin n) (a c d : V), T a (X i) c d = ∑ p, ω i p * T a (e p) c d := by
    intro i a c d; rw [hX i]; exact hexp2 (fun p => ω i p) a c d
  have hX3 : ∀ (i : Fin n) (a b d : V), T a b (X i) d = ∑ p, ω i p * T a b (e p) d := by
    intro i a b d; rw [hX i]; exact hexp3 (fun p => ω i p) a b d
  have hX4 : ∀ (i : Fin n) (a b c : V), T a b c (X i) = ∑ p, ω i p * T a b c (e p) := by
    intro i a b c; rw [hX i]; exact hexp4 (fun p => ω i p) a b c
  -- Each of the four double sums vanishes.
  -- Third sum: `∑ i ∑ j T (e i)(e j)(X i)(e j) = ∑ i ∑ p ω i p · H i p` with
  -- `H i p = ∑ j T (e i)(e j)(e p)(e j)` symmetric (by `hpe`).
  have hA3 : (∑ i, ∑ j, T (e i) (e j) (X i) (e j)) = 0 := by
    have key : ∀ (i : Fin n), (∑ j, T (e i) (e j) (X i) (e j))
        = ∑ p, ω i p * (∑ j, T (e i) (e j) (e p) (e j)) := by
      intro i
      have h : (∑ j, T (e i) (e j) (X i) (e j))
          = ∑ j, ∑ p, ω i p * T (e i) (e j) (e p) (e j) := by
        apply Finset.sum_congr rfl; intro j _
        rw [hX3 i (e i) (e j) (e j)]
      rw [h, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    exact double_sum_antisymm_mul_symm ω (fun i p => ∑ j, T (e i) (e j) (e p) (e j)) hanti
      (fun i p => by
        apply Finset.sum_congr rfl; intro j _
        exact hpe (e i) (e j) (e p) (e j))
  -- First sum: pointwise equal to the third by `hpe`.
  have hA1 : (∑ i, ∑ j, T (X i) (e j) (e i) (e j)) = 0 := by
    rw [show (∑ i, ∑ j, T (X i) (e j) (e i) (e j))
        = (∑ i, ∑ j, T (e i) (e j) (X i) (e j)) from by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact hpe (X i) (e j) (e i) (e j)]
    exact hA3
  -- Second sum: `∑ i ∑ j T (e i)(X j)(e i)(e j) = ∑ j ∑ p ω j p · H' j p` with
  -- `H' j p = ∑ i T (e i)(e p)(e i)(e j)` symmetric (by `hpe`).
  have hA2 : (∑ i, ∑ j, T (e i) (X j) (e i) (e j)) = 0 := by
    have key : ∀ (i : Fin n), (∑ j, T (e i) (X j) (e i) (e j))
        = ∑ j, ∑ p, ω j p * T (e i) (e p) (e i) (e j) := by
      intro i
      apply Finset.sum_congr rfl; intro j _
      rw [hX2 j (e i) (e i) (e j)]
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    rw [Finset.sum_comm]
    rw [show (∑ j, ∑ i, ∑ p, ω j p * T (e i) (e p) (e i) (e j))
        = ∑ j, ∑ p, ω j p * (∑ i, T (e i) (e p) (e i) (e j)) from by
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.mul_sum]]
    exact double_sum_antisymm_mul_symm ω (fun j p => ∑ i, T (e i) (e p) (e i) (e j)) hanti
      (fun j p => by
        apply Finset.sum_congr rfl; intro i _
        exact hpe (e i) (e p) (e i) (e j))
  -- Fourth sum: pointwise equal to the second by `hpe`.
  have hA4 : (∑ i, ∑ j, T (e i) (e j) (e i) (X j)) = 0 := by
    rw [show (∑ i, ∑ j, T (e i) (e j) (e i) (X j))
        = (∑ i, ∑ j, T (e i) (X j) (e i) (e j)) from by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact (hpe (e i) (X j) (e i) (e j)).symm]
    exact hA2
  -- Split the four-term sum and use the four vanishing identities.
  have hsplit : (∑ i, ∑ j, (T (X i) (e j) (e i) (e j) + T (e i) (X j) (e i) (e j)
      + T (e i) (e j) (X i) (e j) + T (e i) (e j) (e i) (X j)))
      = ((∑ i, ∑ j, T (X i) (e j) (e i) (e j)) + (∑ i, ∑ j, T (e i) (X j) (e i) (e j))
        + (∑ i, ∑ j, T (e i) (e j) (X i) (e j)) + (∑ i, ∑ j, T (e i) (e j) (e i) (X j))) := by
    simp only [Finset.sum_add_distrib]
  rw [hsplit, hA1, hA2, hA3, hA4]
  norm_num

end Work.Diff.GE
