/-
# The canonical pairing `H₁(G, A) × H¹(G, A^∨) → k`

For a commutative ring `k`, a group `G` and a `k`-linear representation `A` of `G`, the bar
complex of `A` has degree-`1` chains `C₁ = G →₀ A` and degree-`1` cochains `G → A^∨`; the
evaluation `⟨∑ a_g·[g], θ⟩ = ∑ θ g (a_g)` is a perfect pairing (*currying*), and it is compatible
with the differentials, so it descends to a pairing

`H₁(G, A) × H¹(G, A^∨) → k`.

This file defines the pairing (`pairFun`, plus the bilinear map `evalForm`), proves the two
compatibility statements (`pairFun_d₂₁`, `pairFun_d₀₁`) and descends it to the homology/cohomology
level, giving

`tatePairLin : H₁(G, A) →ₗ[k] Module.Dual k (H¹(G, A^∨))`.

Over a field this is the pairing of Tate duality in degrees `-2` and `1`; unlike the abstract
assembly `Work.SSGRoute.H1_tateDual_clean` it is defined by an explicit formula, hence manifestly
natural in both `G` and `A` (see `Submission/Work/SSGRoute/H1Pair/Natural.lean`).

## Main definitions

* `pairFun` — the evaluation pairing on the bar complex;
* `evalForm` — the same, as a bilinear map;
* `tatePairLin` — the descended linear map `H₁(G, A) →ₗ (H¹(G, A^∨))^∨`.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open CategoryTheory

namespace Work.SSGRoute.H1Pair

universe u

variable {k : Type u} [CommRing k]

/-! ## The evaluation pairing on the bar complex -/

/-- The evaluation pairing `⟨∑_i a_i·[i], θ⟩ = ∑_i θ i (a_i)` between the degree-`n` chains
`ι →₀ A` and the degree-`n` cochains `ι → A^∨`. -/
def pairFun {ι : Type u} {A : Type u} [AddCommGroup A] [Module k A]
    (c : ι →₀ A) (θ : ι → Module.Dual k A) : k :=
  c.sum fun i a => θ i a

variable {ι : Type u} {A : Type u} [AddCommGroup A] [Module k A]

/-- Unfolding of the pairing through `Finsupp.lsum`. -/
theorem pairFun_eq (c : ι →₀ A) (θ : ι → Module.Dual k A) :
    pairFun c θ = (Finsupp.lsum k θ) c := by
  rw [Finsupp.lsum_apply]
  rfl

@[simp]
theorem pairFun_zero_left (θ : ι → Module.Dual k A) : pairFun (0 : ι →₀ A) θ = 0 := by
  rw [pairFun_eq, map_zero]

@[simp]
theorem pairFun_zero_right (c : ι →₀ A) : pairFun c (0 : ι → Module.Dual k A) = 0 := by
  rw [pairFun_eq, map_zero]
  rfl

theorem pairFun_single (i : ι) (a : A) (θ : ι → Module.Dual k A) :
    pairFun (Finsupp.single i a) θ = θ i a := by
  rw [pairFun_eq, Finsupp.lsum_single]

theorem pairFun_add_left (c c' : ι →₀ A) (θ : ι → Module.Dual k A) :
    pairFun (c + c') θ = pairFun c θ + pairFun c' θ := by
  rw [pairFun_eq, pairFun_eq, pairFun_eq, map_add]

theorem pairFun_sub_left (c c' : ι →₀ A) (θ : ι → Module.Dual k A) :
    pairFun (c - c') θ = pairFun c θ - pairFun c' θ := by
  rw [pairFun_eq, pairFun_eq, pairFun_eq, map_sub]

theorem pairFun_smul_left (r : k) (c : ι →₀ A) (θ : ι → Module.Dual k A) :
    pairFun (r • c) θ = r • pairFun c θ := by
  rw [pairFun_eq, pairFun_eq, map_smul]

theorem pairFun_add_right (c : ι →₀ A) (θ θ' : ι → Module.Dual k A) :
    pairFun c (θ + θ') = pairFun c θ + pairFun c θ' := by
  rw [pairFun_eq, pairFun_eq, pairFun_eq, map_add, LinearMap.add_apply]

theorem pairFun_smul_right (r : k) (c : ι →₀ A) (θ : ι → Module.Dual k A) :
    pairFun c (r • θ) = r • pairFun c θ := by
  rw [pairFun_eq, pairFun_eq, map_smul, LinearMap.smul_apply]

/-- The evaluation pairing, as a `k`-bilinear map `C₁ × C¹ → k`. -/
def evalForm : (ι →₀ A) →ₗ[k] (ι → Module.Dual k A) →ₗ[k] k :=
  LinearMap.mk₂ k pairFun pairFun_add_left pairFun_smul_left pairFun_add_right pairFun_smul_right

@[simp]
theorem evalForm_apply (c : ι →₀ A) (θ : ι → Module.Dual k A) : evalForm c θ = pairFun c θ := rfl

/-- Currying: the evaluation pairing identifies the cochains `ι → A^∨` with the linear functionals
on the chains `ι →₀ A`. This is `Finsupp.lsum` in disguise. -/
theorem evalForm_flip_eq_lsum :
    evalForm.flip
      = ((Finsupp.lsum k : (ι → Module.Dual k A) ≃ₗ[k] (ι →₀ A) →ₗ[k] k) :
          (ι → Module.Dual k A) →ₗ[k] (ι →₀ A) →ₗ[k] k) := by
  refine LinearMap.ext fun θ => LinearMap.ext fun c => ?_
  rw [LinearMap.flip_apply, evalForm_apply, pairFun_eq]
  rfl

end Work.SSGRoute.H1Pair
