import Mathlib
import Submission.Work.ZassenhausSuzuki.SingerCycle
import ChallengeDeps

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Transport of the full Singer-cycle package

`SingerCycle.singer_cycle_transport` transports the four cardinality/centraliser clauses of a
Singer cycle along an isomorphism `X ≃* PSL2Model n`.  This file adds the two clauses that
Suzuki 1962 §8 uses on the elements of `V`:

* `V` admits an involution inverting it (the reflection of the dihedral normaliser `N(V)`);
* every element of `V` is strongly real (a product of two involutions) — because a reflection `τ`
  inverting `V` gives `v = τ · (τ v)` with `τ v` an involution.

Here `V` is the *preimage* of `V₀` under `e`, so that all six clauses are proved at once.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs

/-- **Transport of the Singer-cycle package** along `e : X ≃* PSL2Model n`, including the
inverting involution and strong reality of the elements of the cycle. -/
theorem singer_cycle_transport_full {X : Type} [Group X] [Finite X] {n : ℕ}
    {V₀ : Subgroup (PSL2Model n)} (hcyc : IsCyclic ↥V₀) (hcard : Nat.card ↥V₀ = 2 ^ n + 1)
    (hcent : Subgroup.centralizer (V₀ : Set (PSL2Model n)) = V₀)
    (hnorm : Nat.card ↥(Subgroup.normalizer (V₀ : Set (PSL2Model n))) = 2 * (2 ^ n + 1))
    (hinv : ∃ τ : PSL2Model n, τ * τ = 1 ∧ ∀ v ∈ V₀, τ * v * τ = v⁻¹)
    (hsr : ∀ s ∈ V₀, ∃ a b : PSL2Model n, a * a = 1 ∧ b * b = 1 ∧ a * b = s)
    (e : X ≃* PSL2Model n) :
    ∃ V : Subgroup X, IsCyclic ↥V ∧ Nat.card ↥V = 2 ^ n + 1 ∧
      Subgroup.centralizer (V : Set X) = V ∧
      Nat.card ↥(Subgroup.normalizer (V : Set X)) = 2 * (2 ^ n + 1) ∧
      (∃ τ : X, τ * τ = 1 ∧ ∀ v ∈ V, τ * v * τ = v⁻¹) ∧
      (∀ s ∈ V, ∃ a b : X, a * a = 1 ∧ b * b = 1 ∧ a * b = s) := by
  classical
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
  refine ⟨V, hcyc', hcard'.trans hcard, hcent', hnorm'.trans hnorm, ?_, ?_⟩
  · obtain ⟨τ₀, hτ₀2, hτ₀inv⟩ := hinv
    refine ⟨e.symm τ₀, ?_, ?_⟩
    · apply e.injective
      rw [map_mul, map_one, e.apply_symm_apply, hτ₀2]
    · intro v hv
      have hv' : e v ∈ V₀ := (hmem v).mp hv
      apply e.injective
      rw [map_mul, map_mul, map_inv]
      simp only [e.apply_symm_apply]
      exact hτ₀inv (e v) hv'
  · intro s hs
    obtain ⟨a, b, ha, hb, hab⟩ := hsr (e s) ((hmem s).mp hs)
    refine ⟨e.symm a, e.symm b, ?_, ?_, ?_⟩
    · apply e.injective
      rw [map_mul, map_one, e.apply_symm_apply, ha]
    · apply e.injective
      rw [map_mul, map_one, e.apply_symm_apply, hb]
    · apply e.injective
      rw [map_mul]
      simp only [e.apply_symm_apply]
      exact hab

end Work.ZassenhausSuzuki
