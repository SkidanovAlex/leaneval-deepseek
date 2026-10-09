import Mathlib
import Submission.Commons.Algebra.Order.pow_mul_right_injective_of_lt_one
import Submission.Commons.RingTheory.Valuation.exists_mem_fixedField_stabilizer_val_eq_one_val_lt_one
import Submission.Commons.RingTheory.Valuation.exists_val_eq_algebraMap_of_conj_val_ne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open scoped Pointwise

/-- **Finite Galois case: the value of an element of the decomposition field lies in the base
value group.**

Let `L/K` be a finite Galois extension, `A` a valuation subring of `L` and `x` an element of the
decomposition field `Z = L^d` where `d = MulAction.stabilizer (L ≃ₐ[K] L) A` is the decomposition
group.  Then the `A`-value of `x` is the `A`-value of an element of `K`.

This is the finite-level form of the statement that the decomposition field is an *immediate*
extension of `K`.

Suggested route (Marker, *Algebra of Henselian Fields*, Lemma 5.5): let `d` be the decomposition
group.  Use
`Commons.RingTheory.Valuation.exists_unit_of_stabilizer_valuationSubring`
to find `u : L` with `A.valuation u = 1` and `A.valuation (σ u) < 1` for `σ ∉ d`, set
`a = ∏ σ ∈ d, σ u` (so `a` lies in the decomposition field, `A.valuation a = 1` and
`A.valuation (σ a) < 1` for `σ ∉ d`), pick `N` such that `A.valuation (σ (a^N * x))` differs from
`A.valuation (a^N * x)` for every `σ` with `σ (a^N * x) ≠ a^N * x` (for `σ ∉ d` the map
`N ↦ A.valuation (σ a)^N` is strictly decreasing, so each `σ` forbids at most one `N`), and then
apply `Commons.RingTheory.Valuation.exists_val_eq_algebraMap_of_conj_val_ne` to
`β = a^N * x`. -/
theorem exists_val_eq_algebraMap_of_mem_fixedField_stabilizer {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (A : ValuationSubring L)
    (x : IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) A)) :
    ∃ y : K, A.valuation (x : L) = A.valuation (algebraMap K L y) := by
  classical
  by_cases hx0 : (x : L) = 0
  · exact ⟨0, by simp [hx0]⟩
  -- Marker's approximation element: fixed by the decomposition group, value `1` there and
  -- value `< 1` at every other conjugate place.
  obtain ⟨a, ha_mem, ha_val, ha_lt⟩ :=
    exists_mem_fixedField_stabilizer_val_eq_one_val_lt_one (K := K) A
  have ha_ne : a ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at ha_val; exact one_ne_zero ha_val.symm
  have ha_mem_fix : ∀ σ : L ≃ₐ[K] L,
      σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) A → σ a = a := by
    intro σ hσ
    exact (IntermediateField.mem_fixedField_iff (MulAction.stabilizer (L ≃ₐ[K] L) A) a).mp
      ha_mem σ hσ
  have hxmem : ∀ σ : L ≃ₐ[K] L,
      σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) A → σ (x : L) = (x : L) := by
    intro σ hσ
    exact (IntermediateField.mem_fixedField_iff (MulAction.stabilizer (L ≃ₐ[K] L) A) (x : L)).mp
      x.2 σ hσ
  -- `P σ N` says that the conjugate `σ (a^N * x)` has the same value as `x`.
  let P : (L ≃ₐ[K] L) → ℕ → Prop := fun σ n =>
    A.valuation (σ (a ^ n * (x : L))) = A.valuation (x : L)
  -- For `σ ∉ d`, the map `N ↦ A.valuation (σ a)^N * A.valuation (σ x)` is strictly decreasing,
  -- so `σ` forbids at most one value of `N`.
  have huniq : ∀ σ : L ≃ₐ[K] L, σ ∉ MulAction.stabilizer (L ≃ₐ[K] L) A →
      ∀ m n, P σ m → P σ n → m = n := by
    intro σ hσd m n hm hn
    have hr1 : A.valuation (σ a) < 1 := ha_lt σ hσd
    have hr0 : A.valuation (σ a) ≠ 0 := by
      intro h
      rw [Valuation.zero_iff] at h
      exact ha_ne (σ.injective (by rw [h, map_zero]))
    have hc : A.valuation (σ (x : L)) ≠ 0 := by
      intro h
      rw [Valuation.zero_iff] at h
      exact hx0 (σ.injective (by rw [h, map_zero]))
    have hform : ∀ k : ℕ, A.valuation (σ (a ^ k * (x : L)))
        = (A.valuation (σ a)) ^ k * A.valuation (σ (x : L)) := by
      intro k
      rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
    refine Commons.Algebra.Order.pow_mul_right_injective_of_lt_one hr1 hr0 hc ?_
    show (A.valuation (σ a)) ^ m * A.valuation (σ (x : L))
        = (A.valuation (σ a)) ^ n * A.valuation (σ (x : L))
    rw [← hform m, ← hform n, hm, hn]
  -- `bad σ` is the (at most one) `N` that `σ` forbids; `B` collects all of them.
  let bad : (L ≃ₐ[K] L) → ℕ := fun σ => if h : ∃ n, P σ n then Nat.find h else 0
  let B : Finset ℕ := Finset.univ.image bad
  have hnotP : ∀ σ : L ≃ₐ[K] L, σ ∉ MulAction.stabilizer (L ≃ₐ[K] L) A →
      ¬ P σ (B.sup id + 1) := by
    intro σ hσd hPN
    have hbad : bad σ = B.sup id + 1 := by
      dsimp only [bad]
      rw [dif_pos ⟨B.sup id + 1, hPN⟩]
      exact (Nat.find_eq_iff ⟨B.sup id + 1, hPN⟩).mpr ⟨hPN, fun n hn hPn => by
        have h := huniq σ hσd n (B.sup id + 1) hPn hPN
        omega⟩
    have hmem : bad σ ∈ B := by
      dsimp only [B]
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ σ, rfl⟩
    have hle : bad σ ≤ B.sup id := Finset.le_sup (s := B) (f := id) hmem
    omega
  -- The element `β = a^N * x` has isolated value.
  let β : L := a ^ (B.sup id + 1) * (x : L)
  have hβval : A.valuation β = A.valuation (x : L) := by
    dsimp only [β]
    rw [map_mul, map_pow, ha_val, one_pow, one_mul]
  have hβ : ∀ σ : L ≃ₐ[K] L, σ β ≠ β → A.valuation (σ β) ≠ A.valuation β := by
    intro σ hne hval
    have hσd : σ ∉ MulAction.stabilizer (L ≃ₐ[K] L) A := by
      intro hσ
      exact hne (by dsimp only [β]; rw [map_mul, map_pow, ha_mem_fix σ hσ, hxmem σ hσ])
    apply hnotP σ hσd
    dsimp only [P]
    dsimp only [β] at hval hβval
    rw [hval, hβval]
  obtain ⟨y, hy⟩ := exists_val_eq_algebraMap_of_conj_val_ne (β := β) A hβ
  exact ⟨y, hβval.symm.trans hy⟩

end Commons.RingTheory.Valuation
