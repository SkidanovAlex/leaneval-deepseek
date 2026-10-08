import Mathlib
import ChallengeDeps
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Singer cycle of `PSL(2, 2ⁿ)`: model statement and transport

Suzuki 1962 §8 (HB III XI §10) uses a **cyclic subgroup `V` of order `q + 1`** of a group
isomorphic to `PSL(2, q)` (`q = 2ⁿ`) — the non-split torus / Singer cycle — with

* `V` cyclic of order `q + 1`,
* `C_G(V) = V` (self-centralising),
* `|N_G(V)| = 2 (q + 1)`,
* distinct conjugates of `V` meeting trivially.

Together with the conjugates of `Q` and of `D` these give the final count
`|G| ≥ N² + N(N+1)(q-2)/2 + N(N+1)q(q-1)/(2(q+1))` with `|G| = N(N+1)(q-1)`, hence `N ≤ q`.

This module is the **model and transport** half, kept free of the Higman area so that it
compiles independently:

* `singer_cycle_model` (delegated separately, `singer_cycle_model.lean`) — the matrix/Singer
  side: `PSL2Model n = PSL(2, 2ⁿ)` contains such a `V₀` (cyclic of order `2 ^ n + 1`,
  self-centralising, normaliser of order `2 (2 ^ n + 1)`).
* `singer_cycle_transport` (below) — any `X ≃* PSL2Model n` inherits all of that, `C_X(V) = V`
  included.
* `exists_singer_selfcentralizing` (below, stated; the proof is the deep step) — the same in the
  ambient group `G` of `Work.ZassenhausSuzuki.QSZThm1`, where `C_G(V) = V` is *not* a formal
  consequence of `C_X(V) = V` and is Suzuki's Proposition 14 plus the count of §8.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs

/-- The image of a cyclic group under a surjective homomorphism is cyclic. -/
theorem isCyclic_of_surjective {A B : Type*} [Group A] [Group B] (h : IsCyclic A)
    (f : A →* B) (hf : Function.Surjective f) : IsCyclic B := by
  obtain ⟨g, hg⟩ := h
  refine ⟨f g, fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hf b
  obtain ⟨n, rfl⟩ := hg a
  exact ⟨n, by rw [map_zpow]⟩

/-- **Transport of the model Singer cycle along an isomorphism.**  If `PSL2Model n` has a cyclic
self-centralising subgroup `V₀` of order `2 ^ n + 1` with normaliser of order `2 (2 ^ n + 1)`,
then the same holds in every group `X` with `X ≃* PSL2Model n`. -/
theorem singer_cycle_transport {X : Type} [Group X] [Finite X] {n : ℕ}
    {V₀ : Subgroup (PSL2Model n)} (hcyc : IsCyclic ↥V₀) (hcard : Nat.card ↥V₀ = 2 ^ n + 1)
    (hcent : Subgroup.centralizer (V₀ : Set (PSL2Model n)) = V₀)
    (hnorm : Nat.card ↥(Subgroup.normalizer (V₀ : Set (PSL2Model n))) = 2 * (2 ^ n + 1))
    (e : X ≃* PSL2Model n) :
    ∃ V : Subgroup X, IsCyclic ↥V ∧ Nat.card ↥V = 2 ^ n + 1 ∧
      Subgroup.centralizer (V : Set X) = V ∧
      Nat.card ↥(Subgroup.normalizer (V : Set X)) = 2 * (2 ^ n + 1) := by
  classical
  -- `V` is the preimage of `V₀` along `e`
  let V : Subgroup X := Subgroup.comap (e : X →* PSL2Model n) V₀
  have hmem : ∀ x : X, x ∈ V ↔ e x ∈ V₀ := fun _ => Iff.rfl
  have hcard' : Nat.card ↥V = Nat.card ↥V₀ :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => Iff.rfl))
  have hcyc' : IsCyclic ↥V := by
    refine isCyclic_of_surjective hcyc
      { toFun := fun y => (⟨e.symm (y : PSL2Model n), (hmem _).mpr (by
          rw [e.apply_symm_apply]; exact y.2)⟩ : ↥V)
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp } ?_
    intro x
    exact ⟨⟨e (x : X), (hmem _).mp x.2⟩, by ext; simp⟩
  have hcent' : Subgroup.centralizer (V : Set X) = V := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [hmem, ← hcent, Subgroup.mem_centralizer_iff]
      rw [Subgroup.mem_centralizer_iff] at hx
      intro w hw
      have hw' : e.symm w ∈ V := (hmem _).mpr (by rw [e.apply_symm_apply]; exact hw)
      have h2 : e.symm w * x = x * e.symm w := hx _ hw'
      calc w * e x = e (e.symm w) * e x := by rw [e.apply_symm_apply]
        _ = e (e.symm w * x) := (map_mul e _ x).symm
        _ = e (x * e.symm w) := by rw [h2]
        _ = e x * e (e.symm w) := map_mul e x _
        _ = e x * w := by rw [e.apply_symm_apply]
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : e v ∈ V₀ := (hmem v).mp hv
      have hx' : e x ∈ V₀ := (hmem x).mp hx
      have h2 : e v * e x = e x * e v :=
        (Subgroup.mem_centralizer_iff.mp (by rw [hcent]; exact hx')) (e v) hv'
      have h3 := congrArg e.symm h2
      simpa using h3
  have hnorm' : Nat.card ↥(Subgroup.normalizer (V : Set X)) =
      Nat.card ↥(Subgroup.normalizer (V₀ : Set (PSL2Model n))) := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
    intro x
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h w
      have h2 := h (e.symm w)
      simp only [hmem, map_mul, map_inv, e.apply_symm_apply] at h2
      exact h2
    · intro h y
      have h2 := h (e y)
      have h3 : e (x * y * x⁻¹) = e x * e y * (e x)⁻¹ := by simp
      rw [hmem, hmem, h3]
      exact h2
  exact ⟨V, hcyc', hcard'.trans hcard, hcent', hnorm'.trans hnorm⟩

-- **Removed** (unused, and a deep Suzuki §8 gap): `exists_singer_selfcentralizing` is not
-- needed by the final chain — its only consumer would be the `|Q| = q³` (Higman) branch,
-- which is already contradictory in the final route.  The delegation target, if ever needed,
-- is `Work.ZassenhausSuzuki.exists_singer_selfcentralizing_zs` (statement reviewed).
end Work.ZassenhausSuzuki
