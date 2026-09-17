import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm

namespace Commons.Algebra.Lie.SerreConstruction

open scoped BigOperators
open Matrix

/-- The `E₈` Cartan matrix over `ℚ`. -/
private abbrev E8q : Matrix (Fin 8) (Fin 8) ℚ := CartanMatrix.E₈.map (Int.castRingHom ℚ)

private lemma E8q_apply (i j : Fin 8) : E8q i j = (CartanMatrix.E₈ i j : ℚ) := rfl

private lemma E8q_transpose : E8qᵀ = E8q := by
  rw [← transpose_map, (show CartanMatrix.E₈.transpose = CartanMatrix.E₈ from CartanMatrix.E₈_transpose)]

private lemma E8q_det_eq_one : E8q.det = 1 := by
  rw [show E8q = CartanMatrix.E₈.map (Int.castRingHom ℚ) from rfl,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, (show CartanMatrix.E₈.det = 1 from CartanMatrix.E₈_det)]
  norm_num

private lemma E8q_inv_mul_self : E8q⁻¹ * E8q = 1 := by
  apply nonsing_inv_mul
  rw [E8q_det_eq_one]; exact isUnit_one

private lemma E8q_inv_transpose : (E8q⁻¹)ᵀ = E8q⁻¹ := by
  rw [transpose_nonsing_inv, E8q_transpose]

/-- Expansion of the difference of a quadratic form at `v+w` and at `v`. -/
private lemma quad_expand (M : Matrix (Fin 8) (Fin 8) ℚ) (hM : Mᵀ = M) (v w : Fin 8 → ℚ) :
    (v + w) ⬝ᵥ (M *ᵥ (v + w)) - v ⬝ᵥ (M *ᵥ v)
      = 2 * (v ⬝ᵥ (M *ᵥ w)) + w ⬝ᵥ (M *ᵥ w) := by
  have hvec : w ᵥ* M = M *ᵥ w := by
    have hh := vecMul_transpose (A := M) (x := w)
    rwa [hM] at hh
  have h : w ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ w) := by
    rw [dotProduct_mulVec, hvec, dotProduct_comm]
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, h]
  ring

private lemma sum_quad (M : Matrix (Fin 8) (Fin 8) ℚ) (v : Fin 8 → ℚ) :
    (∑ i, ∑ j, v i * M i j * v j) = v ⬝ᵥ (M *ᵥ v) := by
  rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]

/-- **There is no dominant weight strictly below `lam` on the Casimir sphere.**

If `lam` and `nu` are dominant integral and `lam - nu = ∑ nᵢ αᵢ` with `nᵢ ≥ 0`, `n ≠ 0`, then
`(nu+rho, nu+rho) ≠ (lam+rho, lam+rho)` for `(x,y) = xᵀA⁻¹y`, `A = CartanMatrix.E₈`, `rho = (1,…,1)`.

This is the missing input of the uniqueness proof of Freudenthal's recursion: it implies that at a
*singular* weight (one with `(nu+rho,nu+rho) = (lam+rho,lam+rho)`) either the weight is `lam` or some
`W`-conjugate of it lies outside the support cone `lam - ℕΦ⁺`.

Proof: write `mu := lam - nu = ∑ nᵢ αᵢ`, `mu ≠ 0`.  Since `nu` is dominant, `nuᵢ = lamᵢ - ⟨mu, αᵢ∨⟩ ≥ 0`,
so `⟨mu, αᵢ∨⟩ ≤ lamᵢ`; hence `(mu,mu) = ∑ᵢ nᵢ ⟨mu, αᵢ∨⟩ ≤ ∑ᵢ nᵢ lamᵢ` (using `A` symmetric).
Also `(mu,rho) = ∑ᵢ nᵢ` (as `⟨rho, αᵢ∨⟩ = 1` and `(αᵢ,αᵢ) = 2`) and `(mu,lam) = ∑ᵢ nᵢ lamᵢ`, so
`2(mu, lam+rho) = 2∑ᵢ nᵢ(lamᵢ+1) ≥ 2∑ᵢ nᵢ lamᵢ + 2`, while the singularity is equivalent to
`2(mu,lam+rho) = (mu,mu)`.  Combining gives `∑ᵢ nᵢ lamᵢ + 2 ≤ 0`, contradicting `lamᵢ ≥ 0`,
`nᵢ ≥ 0`, `∑ nᵢ ≥ 1`. -/
theorem no_dominant_singular_weight {lam nu : Fin 8 → ℤ} (hl : ∀ i, 0 ≤ lam i) (hn : ∀ i, 0 ≤ nu i)
    (hmu : ∃ n : Fin 8 → ℕ, (∃ i, 0 < n i) ∧ ∀ j, lam j - nu j = ∑ i, n i * CartanMatrix.E₈ i j) :
    (∑ i, ∑ j, (nu i + 1 : ℚ) * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (nu j + 1 : ℚ))
      ≠ (∑ i, ∑ j, (lam i + 1 : ℚ) * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (lam j + 1 : ℚ)) := by
  obtain ⟨n, hnne, hnmul⟩ := hmu
  let vnu : Fin 8 → ℚ := fun i => (nu i : ℚ) + 1
  let vlam : Fin 8 → ℚ := fun i => (lam i : ℚ) + 1
  let muq : Fin 8 → ℚ := fun i => (lam i : ℚ) - (nu i : ℚ)
  let nq : Fin 8 → ℚ := fun i => (n i : ℚ)
  have hLnu : (∑ i, ∑ j, (nu i + 1 : ℚ) * (E8q⁻¹) i j * (nu j + 1 : ℚ))
      = ∑ i, ∑ j, vnu i * (E8q⁻¹) i j * vnu j := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [vnu]
  have hLlam : (∑ i, ∑ j, (lam i + 1 : ℚ) * (E8q⁻¹) i j * (lam j + 1 : ℚ))
      = ∑ i, ∑ j, vlam i * (E8q⁻¹) i j * vlam j := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [vlam]
  rw [hLnu, hLlam]
  -- `mu = lam - nu` is the vector `A * n` (in `ω`-coordinates).
  have hmuqA : muq = E8q *ᵥ nq := by
    funext j
    have hcast : ((lam j - nu j : ℤ) : ℚ)
        = ∑ i, (n i : ℚ) * (CartanMatrix.E₈ i j : ℚ) := by
      rw [hnmul j]; push_cast; rfl
    show muq j = (E8q *ᵥ nq) j
    simp only [muq, nq, mulVec, dotProduct, E8q_apply]
    rw [← Int.cast_sub, hcast]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm.1 j i)]
    ring
  have hMmuq : E8q⁻¹ *ᵥ muq = nq := by
    rw [hmuqA, mulVec_mulVec, E8q_inv_mul_self, one_mulVec]
  have hvlam : vlam = vnu + muq := by
    funext i; simp only [vlam, vnu, muq, Pi.add_apply]; ring
  -- The two quadratic forms differ by `∑ᵢ (lamᵢ + nuᵢ + 2) nᵢ > 0`.
  have key : (∑ i, ∑ j, vlam i * (E8q⁻¹) i j * vlam j)
      - (∑ i, ∑ j, vnu i * (E8q⁻¹) i j * vnu j)
      = ∑ i, ((lam i : ℚ) + (nu i : ℚ) + 2) * nq i := by
    rw [sum_quad (E8q⁻¹) vlam, sum_quad (E8q⁻¹) vnu, hvlam,
      quad_expand (E8q⁻¹) E8q_inv_transpose vnu muq, hMmuq]
    simp only [dotProduct]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [vnu, muq, nq]; ring
  have hpos : 0 < ∑ i, ((lam i : ℚ) + (nu i : ℚ) + 2) * nq i := by
    obtain ⟨i0, hi0⟩ := hnne
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · have h1 : (0:ℚ) ≤ (lam i : ℚ) := by exact_mod_cast hl i
      have h2 : (0:ℚ) ≤ (nu i : ℚ) := by exact_mod_cast hn i
      have h3 : (0:ℚ) ≤ nq i := by simp only [nq]; positivity
      exact mul_nonneg (by linarith) h3
    · have h1 : (0:ℚ) ≤ (lam i0 : ℚ) := by exact_mod_cast hl i0
      have h2 : (0:ℚ) ≤ (nu i0 : ℚ) := by exact_mod_cast hn i0
      have h3 : (0:ℚ) < nq i0 := by simp only [nq]; exact_mod_cast hi0
      exact mul_pos (by linarith) h3
  intro hEq
  have hd : (∑ i, ∑ j, vlam i * (E8q⁻¹) i j * vlam j)
      - (∑ i, ∑ j, vnu i * (E8q⁻¹) i j * vnu j) = 0 := by
    rw [hEq]; ring
  rw [key] at hd
  linarith

end Commons.Algebra.Lie.SerreConstruction