import Mathlib
import Submission.Work.Hering.HardCore.abelian_setup
import Submission.Work.Hering.HardCore.phi_mul
import Submission.Work.Hering.HardCore.phi_smul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-!
# Conjugation acts on `Φ` by the matrix acting on the coordinates

Setting: `C ≤ G` is an abelian subgroup, `c : Fin 3 → G` is a triple of elements of `C` of
exponent dividing `2 ^ m` (so that `Φ c x = c₀^x₀ · c₁^x₁ · c₂^x₂` only depends on `x` modulo
`2 ^ m`), and `g ∈ G` conjugates the `cᵢ` into the images under `Φ c` of the three **columns** of
a matrix `M` over `ℤ/2 ^ m`:

`g * cᵢ * g⁻¹ = Φ c (fun j => M j i)`.

The lemma says that conjugation by `g` then acts on the whole image of `Φ c` by the *matrix*
action on the coordinates: `g * Φ c x * g⁻¹ = Φ c (M *ᵥ x)`.

The proof has three ingredients, all of them already available in the workspace:

* `Φ c x = c₀^x₀ · c₁^x₁ · c₂^x₂` is a product of three powers, so conjugating it just conjugates
  each factor (`map_mul`, `map_pow` for the automorphism `MulAut.conj g`), and the hypothesis
  replaces `conj g (cᵢ)` by the `i`-th column;
* `Phi_smul` (`phi_smul`) turns `(Φ c v) ^ a.val` into `Φ c (a • v)`, and `Phi_mul` (`phi_mul`)
  multiplies the three resulting factors into `Φ c` of their sum;
* `M *ᵥ x = ∑ i, xᵢ • (column i)` is the matrix–vector product written as a linear combination
  of the columns (`Matrix.mulVec_apply_eq_sum`), which identifies that sum with `M *ᵥ x`.
-/

theorem phi_of_cols {G : Type*} [Group G] {C : Subgroup G} (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    {m : ℕ} {c : Fin 3 → G} (hc : ∀ i, c i ∈ C) (hpow : ∀ i, (c i) ^ (2 ^ m) = 1)
    {g : G} {M : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ m))}
    (hcol : ∀ i, g * c i * g⁻¹ = Phi c (fun j => M j i)) (x : Fin 3 → ZMod (2 ^ m)) :
    g * Phi c x * g⁻¹ = Phi c (Matrix.mulVec M x) := by
  -- Conjugation by `g` as an automorphism, and the hypothesis rephrased with it.
  have hcol' : ∀ i : Fin 3, MulAut.conj g (c i) = Phi c (fun j => M j i) := by
    intro i
    rw [MulAut.conj_apply]
    exact hcol i
  -- Step 1: `conj g` distributes over the product defining `Φ c x`, and the hypothesis rewrites
  -- each `conj g (cᵢ)` as the `i`-th column, while `phi_smul` re-absorbs the exponents.
  have key : MulAut.conj g (Phi c x)
      = Phi c ((x 0) • (fun j : Fin 3 => M j 0)) * Phi c ((x 1) • (fun j : Fin 3 => M j 1))
        * Phi c ((x 2) • (fun j : Fin 3 => M j 2)) := by
    have h1 : MulAut.conj g (Phi c x)
        = (MulAut.conj g (c 0)) ^ (x 0).val * (MulAut.conj g (c 1)) ^ (x 1).val
          * (MulAut.conj g (c 2)) ^ (x 2).val := by
      simp only [Phi, map_mul, map_pow]
    rw [h1, hcol' 0, hcol' 1, hcol' 2, ← phi_smul hCab hc hpow (x 0) (fun j : Fin 3 => M j 0),
      ← phi_smul hCab hc hpow (x 1) (fun j : Fin 3 => M j 1),
      ← phi_smul hCab hc hpow (x 2) (fun j : Fin 3 => M j 2)]
  -- `M *ᵥ x` is the linear combination of the columns of `M` with coefficients `x`.
  have hmv : (∑ i : Fin 3, (x i) • (fun j : Fin 3 => M j i)) = Matrix.mulVec M x := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum,
      Fin.sum_univ_three, mul_comm]
  -- Step 2: `phi_mul` merges the three factors into `Φ c` of the sum of the three columns.
  have hsum : Phi c ((x 0) • (fun j : Fin 3 => M j 0)) * Phi c ((x 1) • (fun j : Fin 3 => M j 1))
        * Phi c ((x 2) • (fun j : Fin 3 => M j 2)) = Phi c (Matrix.mulVec M x) := by
    rw [phi_mul hCab hc hpow ((x 0) • (fun j : Fin 3 => M j 0)) ((x 1) • (fun j : Fin 3 => M j 1)),
        phi_mul hCab hc hpow (((x 0) • (fun j : Fin 3 => M j 0)) + ((x 1) • (fun j : Fin 3 => M j 1)))
          ((x 2) • (fun j : Fin 3 => M j 2))]
    rw [← hmv, Fin.sum_univ_three]
  rw [← MulAut.conj_apply g (Phi c x), key, hsum]

end Work.Hering.HardCore
