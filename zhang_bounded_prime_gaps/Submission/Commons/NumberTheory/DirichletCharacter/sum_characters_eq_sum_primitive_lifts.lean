import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.BombieriVinogradov.mean_value_large_range

namespace Commons.NumberTheory.DirichletCharacter

open scoped Classical
open _root_.DirichletCharacter

/-- `changeLevel` does not depend on the particular proof of divisibility of the levels. -/
lemma changeLevel_congr_arg {R : Type*} [CommMonoidWithZero R] {n m : ℕ} (h₁ h₂ : n ∣ m)
    (χ : DirichletCharacter R n) : changeLevel h₁ χ = changeLevel h₂ χ := by
  rw [Subsingleton.elim h₁ h₂]

/-- The map sending a primitive character of level `c` with `c ∣ q` to the corresponding
Dirichlet character of level `q`, obtained by lifting the level. -/
noncomputable def primitiveLiftMap (R : Type*) [CommMonoidWithZero R] (q : ℕ) [NeZero q]
    (x : (Σ c : {d : ℕ // d ∈ q.divisors}, {ψ : DirichletCharacter R c.1 // ψ.IsPrimitive})) :
    DirichletCharacter R q :=
  changeLevel (Nat.mem_divisors.mp x.1.2).1 x.2.1

lemma primitiveLiftMap_injective (R : Type*) [CommMonoidWithZero R] (q : ℕ) [NeZero q] :
    Function.Injective (primitiveLiftMap R q) := by
  intro x y h
  obtain ⟨c₁, ψ₁, h1⟩ := x
  obtain ⟨c₂, ψ₂, h2⟩ := y
  have hx : (primitiveLiftMap R q ⟨c₁, ⟨ψ₁, h1⟩⟩).conductor = c₁.1 := by
    rw [primitiveLiftMap, conductor_changeLevel]
    exact (isPrimitive_def ψ₁).mp h1
  have hy : (primitiveLiftMap R q ⟨c₂, ⟨ψ₂, h2⟩⟩).conductor = c₂.1 := by
    rw [primitiveLiftMap, conductor_changeLevel]
    exact (isPrimitive_def ψ₂).mp h2
  have hc : c₁.1 = c₂.1 := by rw [← hx, ← hy, h]
  have hc' : c₁ = c₂ := Subtype.ext hc
  subst hc'
  have hval : changeLevel (Nat.mem_divisors.mp c₁.2).1 ψ₁
      = changeLevel (Nat.mem_divisors.mp c₁.2).1 ψ₂ := h
  have hpsi : ψ₁ = ψ₂ := changeLevel_injective _ hval
  subst hpsi
  rfl

lemma primitiveLiftMap_surjective (R : Type*) [CommMonoidWithZero R] (q : ℕ) [NeZero q] :
    Function.Surjective (primitiveLiftMap R q) := by
  intro χ
  refine ⟨⟨⟨χ.conductor, Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne q⟩⟩,
      ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩⟩, ?_⟩
  rw [primitiveLiftMap]
  simp only
  rw [changeLevel_congr_arg _ χ.conductor_dvd_level]
  exact changeLevel_primitiveCharacter χ

theorem sum_characters_eq_sum_primitive_lifts (q : ℕ) [NeZero q]
    (g : DirichletCharacter ℂ q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, g χ)
    = ∑ c ∈ q.divisors.attach,
        ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
          g (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1) := by
  have hbij : Function.Bijective (primitiveLiftMap ℂ q) :=
    ⟨primitiveLiftMap_injective ℂ q, primitiveLiftMap_surjective ℂ q⟩
  have hsigma : (∑ c : {d : ℕ // d ∈ q.divisors},
        ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
          g (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1))
      = ∑ x : (Σ c : {d : ℕ // d ∈ q.divisors},
          {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive}),
          g (primitiveLiftMap ℂ q x) :=
    (Fintype.sum_sigma (f := fun x => g (primitiveLiftMap ℂ q x))).symm
  rw [← Finset.sum_coe_sort_eq_attach, hsigma]
  exact (hbij.sum_comp g).symm

end Commons.NumberTheory.DirichletCharacter