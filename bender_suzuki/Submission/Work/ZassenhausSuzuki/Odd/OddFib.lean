import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.OddCore
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_conj_of_prime_dvd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The fibre decomposition of `ℱ` by order

Second block of helpers for `Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki`: two members
of `ℱ` of the same order are conjugate, so the finite set `FinsetCZ` of `ℱ`-subgroups is the
disjoint union of its fibres over the order map; every fibre is a single conjugacy class.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

theorem mem_FinsetCZ {A : Subgroup G} : A ∈ FinsetCZ (G := G) ↔ IsCZ A := by
  classical
  simp [FinsetCZ]

theorem mem_FinsetCZ' {A : Subgroup G} :
    A ∈ FinsetCZ' (G := G) H t ↔
      IsCZ A ∧ ¬ ∃ g : G, A = conj g (twoPoint H t) := by
  classical
  simp [FinsetCZ', FinsetCZ]

/-- The conjugates of `A` have the same order as `A`. -/
theorem card_conj_eq (A : Subgroup G) (g : G) : Nat.card ↥(conj g A) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (K := A)
    (MulAut.conj g).injective

/-- Two members of `ℱ` of the same order are conjugate. -/
theorem isCZ_conj_of_card_eq (h : SzOddHyp H Q t) {A B : Subgroup G} (hA : IsCZ A) (hB : IsCZ B)
    (hcard : Nat.card ↥A = Nat.card ↥B) : ∃ g : G, B = conj g A := by
  have h5 : 5 ≤ Nat.card ↥A := isCZ_card_ge_five h hA
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥A) (by omega)
  exact isCZ_conj_of_prime_dvd h hA hB hp hpd (hcard ▸ hpd)

/-- The set of orders occurring in `ℱ`. -/
noncomputable def Vals (G : Type) [Group G] [Finite G] : Finset ℕ :=
  (FinsetCZ (G := G)).image (fun A : Subgroup G => Nat.card ↥A)

/-- The fibre over `a` of the order map on `FinsetCZ`. -/
noncomputable def Fib (G : Type) [Group G] [Finite G] (a : ℕ) : Finset (Subgroup G) :=
  (FinsetCZ (G := G)).filter (fun A : Subgroup G => Nat.card ↥A = a)

theorem mem_Vals {a : ℕ} : a ∈ Vals G ↔ ∃ A ∈ FinsetCZ (G := G), Nat.card ↥A = a := by
  classical
  simp [Vals]

theorem mem_Fib {a : ℕ} {A : Subgroup G} :
    A ∈ Fib G a ↔ IsCZ A ∧ Nat.card ↥A = a := by
  classical
  simp only [Fib, Finset.mem_filter, mem_FinsetCZ]

theorem Fib_eq_filter (a : ℕ) :
    Fib G a = (FinsetCZ (G := G)).filter (fun A : Subgroup G => Nat.card ↥A = a) := rfl

/-- The fibre over `a` is the conjugacy class of any of its members. -/
theorem card_Fib_eq_card_conj (h : SzOddHyp H Q t) {A : Subgroup G} (hA : IsCZ A) :
    Nat.card {B : Subgroup G // IsCZ B ∧ ∃ g : G, B = conj g A}
      = (Fib G (Nat.card ↥A)).card := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  have hP : ∀ B : Subgroup G,
      (IsCZ B ∧ ∃ g : G, B = conj g A) ↔ B ∈ Fib G (Nat.card ↥A) := by
    intro B
    rw [mem_Fib]
    constructor
    · rintro ⟨hB, g, rfl⟩
      exact ⟨hB, card_conj_eq A g⟩
    · rintro ⟨hB, hcard⟩
      exact ⟨hB, isCZ_conj_of_card_eq h hA hB hcard.symm⟩
  have h1 : Nat.card {B : Subgroup G // IsCZ B ∧ ∃ g : G, B = conj g A}
      = (Finset.univ.filter (fun B : Subgroup G => IsCZ B ∧ ∃ g : G, B = conj g A)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1]
  congr 1
  ext B
  rw [Finset.mem_filter, hP B]
  simp

/-- The element count summed over `FinsetCZ` is the sum over the fibres of the order map. -/
theorem sum_card_sub_one_eq_sum_Fib :
    (∑ A ∈ FinsetCZ (G := G), (Nat.card ↥A - 1))
      = ∑ a ∈ Vals G, (Fib G a).card * (a - 1) := by
  classical
  have hmaps : ∀ A ∈ FinsetCZ (G := G), Nat.card ↥A ∈ Vals G :=
    fun A hA => Finset.mem_image_of_mem (fun A : Subgroup G => Nat.card ↥A) hA
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun A : Subgroup G => Nat.card ↥A - 1)]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [Fib_eq_filter]
  have : ∀ A ∈ (FinsetCZ (G := G)).filter (fun A : Subgroup G => Nat.card ↥A = a),
      Nat.card ↥A - 1 = a - 1 := by
    intro A hA
    rw [(Finset.mem_filter.mp hA).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The class count summed over `FinsetCZ` is the sum over the fibres of the order map. -/
theorem sum_card_mul_card_sub_one_eq_sum_Fib :
    (∑ A ∈ FinsetCZ (G := G), Nat.card ↥A * (Nat.card ↥A - 1))
      = ∑ a ∈ Vals G, (Fib G a).card * (a * (a - 1)) := by
  classical
  have hmaps : ∀ A ∈ FinsetCZ (G := G), Nat.card ↥A ∈ Vals G :=
    fun A hA => Finset.mem_image_of_mem (fun A : Subgroup G => Nat.card ↥A) hA
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun A : Subgroup G => Nat.card ↥A * (Nat.card ↥A - 1))]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [Fib_eq_filter]
  have : ∀ A ∈ (FinsetCZ (G := G)).filter (fun A : Subgroup G => Nat.card ↥A = a),
      Nat.card ↥A * (Nat.card ↥A - 1) = a * (a - 1) := by
    intro A hA
    rw [(Finset.mem_filter.mp hA).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]

end Work.ZassenhausSuzuki.Odd
