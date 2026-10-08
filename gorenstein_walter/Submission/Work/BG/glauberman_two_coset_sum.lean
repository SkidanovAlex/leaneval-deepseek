import Mathlib
import Submission.Work.BG.glauberman_two_setup
import Submission.Work.BG.Defs
import Submission.Work.BG.CharBridge
import Submission.Work.BG.glauberman_two_coset_count

/-!
# Glauberman's two-coset sum

This module proves `Work.BG.glauberman_two_coset_sum`, the coset-sum identity behind
Glauberman's correspondence in the case `|A| = 2` (Glauberman, *Correspondences of characters
for relatively prime operator groups*, Canad. J. Math. **20** (1968)).

## Statement

Let `U` be a finite group of **odd** order, `σ` an involutive automorphism of `U` and
`Γ = U ⋊ ⟨σ⟩` the semidirect product (`Work.BG.Gam σ`), with `a = gInv σ` the involution
corresponding to `σ`, `U` embedded as `iot σ`, and `B = C_U(σ) = fixedSubgroup σ`.  For every
class function `μ` on `Γ`,

`|B| * ∑_{u ∈ U} μ (a * iot u) = |U| * ∑_{b ∈ B} μ (a * iot b)`.

## Proof

Write `f u := μ (a * iot u)`.  Since `μ` is a class function and `iot v * (a * iot u) * (iot v)⁻¹
= a * iot (σ v * u * v⁻¹)` (`gam_conj_iot`), the function `f` is invariant under the twisted
conjugation `u ↦ σ v * u * v⁻¹`:

`f (σ v * u * v⁻¹) = f u`.   `(h1)`

Consider the double sum

`T = ∑_{u ∈ U} ∑_{v ∈ U} [σ v * u * v⁻¹ ∈ B] • f (σ v * u * v⁻¹)`, with `[·] ∈ {0,1}`.

* Computing the inner sum first with `(h1)`: the summand is `[σ v * u * v⁻¹ ∈ B] • f u`, so the
  inner sum is `#{v | σ v * u * v⁻¹ ∈ B} • f u = |B| • f u` by `glauberman_two_coset_count`;
  hence `T = |B| • ∑_u f u`.
* Computing the outer sum first: for fixed `v` the map `u ↦ σ v * u * v⁻¹` is a bijection of `U`,
  so the inner sum is `∑_{w ∈ B} f w`; hence `T = |U| • ∑_{b ∈ B} f b`.

Comparing the two evaluations gives the identity.  Note that no hypothesis on `μ` beyond class
function is needed, and that oddness of `|U|` is used exactly once, in the counting lemma
`glauberman_two_coset_count`.
-/

open scoped BigOperators

namespace Work.BG

/-! ## 1. Conjugation formulas in the semidirect product `U ⋊ ⟨σ⟩` -/

section Conjugation

variable {U : Type} [Group U]

/-- Left multiplication rule: `a * iot u = iot (σ u) * a` where `a = gInv σ`. -/
theorem gInv_mul_iot_eq (σ : MulAut U) (hσ : σ * σ = 1) (u : U) :
    Gam.gInv σ * Gam.iot σ u = Gam.iot σ (σ u) * Gam.gInv σ := by
  have h := Gam.gInv_mul_iot (σ := σ) u
  rw [Gam.gInv_inv σ hσ] at h
  calc Gam.gInv σ * Gam.iot σ u
      = Gam.gInv σ * Gam.iot σ u * (Gam.gInv σ * Gam.gInv σ) := by
          rw [Gam.gInv_mul_self σ hσ, mul_one]
    _ = (Gam.gInv σ * Gam.iot σ u * Gam.gInv σ) * Gam.gInv σ := by group
    _ = Gam.iot σ (σ u) * Gam.gInv σ := by rw [h]

/-- Right multiplication rule: `iot u * a = a * iot (σ u)` where `a = gInv σ`. -/
theorem iot_mul_gInv_eq_coset_coset (σ : MulAut U) (hσ : σ * σ = 1) (u : U) :
    Gam.iot σ u * Gam.gInv σ = Gam.gInv σ * Gam.iot σ (σ u) := by
  have h := Gam.gInv_mul_iot (σ := σ) u
  rw [Gam.gInv_inv σ hσ] at h
  calc Gam.iot σ u * Gam.gInv σ
      = (Gam.gInv σ * Gam.gInv σ) * (Gam.iot σ u * Gam.gInv σ) := by
          rw [Gam.gInv_mul_self σ hσ, one_mul]
    _ = Gam.gInv σ * (Gam.gInv σ * Gam.iot σ u * Gam.gInv σ) := by group
    _ = Gam.gInv σ * Gam.iot σ (σ u) := by rw [h]

/-- Conjugation in `Gam σ`: conjugating `a * iot u` by `iot v` produces
`a * iot (σ v * u * v⁻¹)`. -/
theorem gam_conj_iot (σ : MulAut U) (hσ : σ * σ = 1) (u v : U) :
    Gam.iot σ v * (Gam.gInv σ * Gam.iot σ u) * (Gam.iot σ v)⁻¹
      = Gam.gInv σ * Gam.iot σ (σ v * u * v⁻¹) := by
  have hσ2 : ∀ x : U, σ (σ x) = x := by
    intro x
    have h := DFunLike.congr_fun hσ x
    simpa [MulAut.mul_apply] using h
  have harg : σ (v * σ u * σ (v⁻¹)) = σ v * u * v⁻¹ := by
    rw [map_mul, map_mul, hσ2 u, hσ2 (v⁻¹)]
  calc Gam.iot σ v * (Gam.gInv σ * Gam.iot σ u) * (Gam.iot σ v)⁻¹
      = Gam.iot σ v * (Gam.iot σ (σ u) * Gam.gInv σ) * (Gam.iot σ v)⁻¹ := by
          rw [gInv_mul_iot_eq σ hσ u]
    _ = Gam.iot σ (v * σ u) * (Gam.gInv σ * Gam.iot σ (v⁻¹)) := by
          rw [← map_inv, ← mul_assoc, ← map_mul]
          group
    _ = Gam.iot σ (v * σ u) * (Gam.iot σ (σ (v⁻¹)) * Gam.gInv σ) := by
          rw [gInv_mul_iot_eq σ hσ (v⁻¹)]
    _ = Gam.iot σ (v * σ u * σ (v⁻¹)) * Gam.gInv σ := by
          rw [← mul_assoc, ← map_mul]
    _ = Gam.gInv σ * Gam.iot σ (σ (v * σ u * σ (v⁻¹))) :=
          iot_mul_gInv_eq_coset_coset σ hσ (v * σ u * σ (v⁻¹))
    _ = Gam.gInv σ * Gam.iot σ (σ v * u * v⁻¹) := by rw [harg]

end Conjugation

/-! ## 2. The averaging argument -/

/-- **Glauberman's two-coset sum**, in the `U`-language.

For `|U|` odd, `σ² = 1`, and any function `f` on `U` which is invariant under the twisted
conjugation `u ↦ σ v * u * v⁻¹` (`h1` — the case of `f u = μ (a * iot u)` for a class
function `μ` of `Gam σ`), one has
`|C_U(σ)| * ∑_u f u = |U| * ∑_{b ∈ C_U(σ)} f b`. -/
theorem coset_sum_aux {U : Type} [Group U] [Fintype U]
    (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1) [Fintype ↥(fixedSubgroup σ)]
    (f : U → ℂ)
    (h1 : ∀ u v, f (σ v * u * v⁻¹) = f u) :
    (Nat.card ↥(fixedSubgroup σ) : ℂ) * (∑ u : U, f u)
      = (Nat.card U : ℂ) * ∑ b : ↥(fixedSubgroup σ), f (b : U) := by
  classical
  -- the counting lemma, transported to a statement about the `ℂ`-valued indicator
  have hcount : ∀ u : U,
      (((Finset.univ.filter (fun v : U => σ v * u * v⁻¹ ∈ fixedSubgroup σ)).card : ℕ) : ℂ)
        = (Nat.card ↥(fixedSubgroup σ) : ℂ) := by
    intro u
    have h2 : Nat.card {v : U // σ v * u * v⁻¹ ∈ fixedSubgroup σ}
        = Nat.card ↥(fixedSubgroup σ) := glauberman_two_coset_count hU σ hσ u
    have h3 : (Finset.univ.filter (fun v : U => σ v * u * v⁻¹ ∈ fixedSubgroup σ)).card
        = Nat.card ↥(fixedSubgroup σ) := by
      rw [← Fintype.card_subtype (p := fun v : U => σ v * u * v⁻¹ ∈ fixedSubgroup σ),
        ← Nat.card_eq_fintype_card, h2]
    exact_mod_cast h3
  -- the inner sum over `v` for fixed `u`
  have hinner : ∀ u : U,
      (∑ v : U, (if σ v * u * v⁻¹ ∈ fixedSubgroup σ then f u else 0))
        = (Nat.card ↥(fixedSubgroup σ) : ℂ) * f u := by
    intro u
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcount u]
  -- first evaluation of the double sum
  have hT1 : (∑ u : U, ∑ v : U,
        (if σ v * u * v⁻¹ ∈ fixedSubgroup σ then f (σ v * u * v⁻¹) else 0))
      = (Nat.card ↥(fixedSubgroup σ) : ℂ) * ∑ u : U, f u := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_congr rfl (fun v _ => by rw [h1 u v])]
    exact hinner u
  -- the inner sum over `u` is a sum over the whole group, reindexed by the bijection
  -- `u ↦ σ v * u * v⁻¹`
  have hreindex : ∀ v : U, (∑ u : U,
        (if σ v * u * v⁻¹ ∈ fixedSubgroup σ then f (σ v * u * v⁻¹) else 0))
      = ∑ w : U, (if w ∈ fixedSubgroup σ then f w else 0) := by
    intro v
    let e : U ≃ U := (Equiv.mulRight (v⁻¹)).trans (Equiv.mulLeft (σ v))
    have he : ∀ u : U, e u = σ v * (u * v⁻¹) := fun _ => rfl
    have := Equiv.sum_comp e (fun w : U => if w ∈ fixedSubgroup σ then f w else 0)
    simpa only [he, mul_assoc] using this
  have hsub : (∑ w : U, (if w ∈ fixedSubgroup σ then f w else 0))
      = ∑ b : ↥(fixedSubgroup σ), f (b : U) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (s := Finset.univ.filter (fun w : U => w ∈ fixedSubgroup σ))
      (p := fun w : U => w ∈ fixedSubgroup σ) (fun w => by simp) f
  -- second evaluation of the double sum
  have hswap : (∑ u : U, ∑ v : U,
        (if σ v * u * v⁻¹ ∈ fixedSubgroup σ then f (σ v * u * v⁻¹) else 0))
      = (Nat.card U : ℂ) * ∑ b : ↥(fixedSubgroup σ), f (b : U) := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (fun v _ => (hreindex v).trans hsub),
      Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]
  exact hT1.symm.trans hswap

/-! ## 3. The coset-sum identity for class functions -/

/-- **Glauberman's two-coset sum** (`|A| = 2` case).  For a finite group `U` of odd order, an
involutive automorphism `σ` of `U`, the semidirect product `Γ = U ⋊ ⟨σ⟩` with involution
`a = gInv σ`, `B = C_U(σ) = fixedSubgroup σ`, and every class function `μ` on `Γ`:
`|B| * ∑_{u ∈ U} μ (a * iot u) = |U| * ∑_{b ∈ B} μ (a * iot b)`. -/
theorem glauberman_two_coset_sum {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    [Fintype ↥(Work.BG.fixedSubgroup σ)]
    (μ : OddOrder.RepresentationTheory.ClassFunction (Work.BG.Gam σ) ℂ) :
    (Nat.card ↥(Work.BG.fixedSubgroup σ) : ℂ) *
        (∑ u : U, μ (Work.BG.Gam.gInv σ * Work.BG.Gam.iot σ u))
      = (Nat.card U : ℂ) *
        ∑ b : ↥(Work.BG.fixedSubgroup σ),
          μ (Work.BG.Gam.gInv σ * Work.BG.Gam.iot σ (b : U)) := by
  refine coset_sum_aux hU σ hσ (fun u => μ (Gam.gInv σ * Gam.iot σ u)) ?_
  intro u v
  rw [← gam_conj_iot (σ := σ) hσ u v]
  exact OddOrder.RepresentationTheory.ClassFunction.conj_eq μ _ _

end Work.BG
