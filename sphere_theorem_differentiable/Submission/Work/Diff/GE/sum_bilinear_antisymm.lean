import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

/-- **Double sum of an antisymmetric matrix vanishes.**

For a finite index type `ι` and `g : ι → ι → ℝ` with `g i j + g j i = 0` for all `i j`,
the total double sum `∑ i, ∑ j, g i j` is zero.  This is the reindexing by the
swap involution `(i,j) ↦ (j,i)` of `ι × ι`, where each term becomes its negative. -/
private lemma sum_antisymm_zero {ι : Type*} [Fintype ι] (g : ι → ι → ℝ)
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

/-- **The antisymmetrisation of a bilinear form against an antisymmetric matrix vanishes.**

Let `B : V → V → ℝ` be additive and `ℝ`-homogeneous in each argument (hypotheses `hB₁`, `hB₂`),
let `e : Fin n → V`, and let `A m = ∑ j, ω m j • e j` with `ω m j + ω j m = 0`.  Then
`∑ m, (B (A m) (e m) + B (e m) (A m)) = 0`.

Proof: expand `A m` in each entry as a finite linear combination, giving the two double sums
`∑_m ∑_j ω m j · B (e j) (e m)` and `∑_m ∑_j ω m j · B (e m) (e j)`; their summand is the
antisymmetric matrix `(m,j) ↦ ω m j · (B (e j) (e m) + B (e m) (e j))`, whose total double sum
is `0` (`sum_antisymm_zero`), because `ω m j + ω j m = 0`. -/
theorem sum_bilinear_antisymm
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ)
    (hB₁ : ∀ (r s : ℝ) (u₁ u₂ w : V), B (r • u₁ + s • u₂) w = r * B u₁ w + s * B u₂ w)
    (hB₂ : ∀ (r s : ℝ) (u w₁ w₂ : V), B u (r • w₁ + s • w₂) = r * B u w₁ + s * B u w₂)
    {n : ℕ} (e : Fin n → V) (A : Fin n → V) (ω : Fin n → Fin n → ℝ)
    (hA : ∀ m, A m = ∑ j, ω m j • e j)
    (hanti : ∀ m j, ω m j + ω j m = 0) :
    ∑ m, (B (A m) (e m) + B (e m) (A m)) = 0 := by
  -- Linearity of `B` in each argument, extracted from the two hypotheses.
  have hadd₁ : ∀ u v w : V, B (u + v) w = B u w + B v w := by
    intro u v w; simpa using hB₁ 1 1 u v w
  have hsmul₁ : ∀ (r : ℝ) (u w : V), B (r • u) w = r * B u w := by
    intro r u w; simpa using hB₁ r 0 u u w
  have hadd₂ : ∀ u v w : V, B u (v + w) = B u v + B u w := by
    intro u v w; simpa using hB₂ 1 1 u v w
  have hsmul₂ : ∀ (r : ℝ) (u w : V), B u (r • w) = r * B u w := by
    intro r u w; simpa using hB₂ r 0 u w w
  -- Expansion of `B` applied to a finite linear combination, in each argument.
  have hsum₁ : ∀ (f : Fin n → ℝ) (w : V),
      B (∑ j, f j • e j) w = ∑ j, f j * B (e j) w := by
    intro f w
    let φ : V →ₗ[ℝ] ℝ :=
      { toFun := fun u => B u w
        map_add' := fun u v => hadd₁ u v w
        map_smul' := fun c u => by simp only [hsmul₁, smul_eq_mul, RingHom.id_apply] }
    have h := map_sum φ (fun j => f j • e j) Finset.univ
    simp only [map_smul, smul_eq_mul] at h
    exact h
  have hsum₂ : ∀ (f : Fin n → ℝ) (u : V),
      B u (∑ j, f j • e j) = ∑ j, f j * B u (e j) := by
    intro f u
    let ψ : V →ₗ[ℝ] ℝ :=
      { toFun := fun w => B u w
        map_add' := fun v w => hadd₂ u v w
        map_smul' := fun c w => by simp only [hsmul₂, smul_eq_mul, RingHom.id_apply] }
    have h := map_sum ψ (fun j => f j • e j) Finset.univ
    simp only [map_smul, smul_eq_mul] at h
    exact h
  -- Substitute `A m` in both entries.
  have hterm₁ : ∀ m, B (A m) (e m) = ∑ j, ω m j * B (e j) (e m) := by
    intro m; rw [hA m]; exact hsum₁ (fun j => ω m j) (e m)
  have hterm₂ : ∀ m, B (e m) (A m) = ∑ j, ω m j * B (e m) (e j) := by
    intro m; rw [hA m]; exact hsum₂ (fun j => ω m j) (e m)
  rw [Finset.sum_add_distrib]
  have e1 : (∑ m, B (A m) (e m)) = ∑ m, ∑ j, ω m j * B (e j) (e m) :=
    Finset.sum_congr rfl (fun m _ => hterm₁ m)
  have e2 : (∑ m, B (e m) (A m)) = ∑ m, ∑ j, ω m j * B (e m) (e j) :=
    Finset.sum_congr rfl (fun m _ => hterm₂ m)
  rw [e1, e2]
  -- Combine the two double sums into one double sum of the antisymmetric matrix.
  have hcomb : (∑ m, ∑ j, ω m j * B (e j) (e m)) + (∑ m, ∑ j, ω m j * B (e m) (e j))
      = ∑ m, ∑ j, (ω m j * B (e j) (e m) + ω m j * B (e m) (e j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.sum_add_distrib]
  rw [hcomb]
  apply sum_antisymm_zero
  intro m j
  have h' : ω j m = - ω m j := by linarith [hanti m j]
  rw [h']; ring

end Work.Diff.GE
